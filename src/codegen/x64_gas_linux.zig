const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const Ast = @import("../ast.zig");
const TypeCheck = @import("../type_check.zig");
const StringBuilder = @import("../string_builder.zig");
const common = @import("./common.zig");
const CompiledExpression = common.CompiledExpression;
const CompiledExprStack = CompiledExpression.CompiledExprStack;
const CompiledExprLiteral = CompiledExpression.CompiledExprLiteral;
const CompiledExpCommon = CompiledExpression.CompiledExpCommon;
const CompiledExprField = CompiledExpression.CompiledExprField;

allocator: Allocator,
program_builder: StringBuilder,
scratch_buffer: StringBuilder,
string_arena: StringBuilder,

const Self = @This();
pub const Storage = struct {
    pub const Type = enum { Stack, CallArg };
    storage_type: Type,
    offset: u64,
    pub fn init(storage_type: Type, offset: u64) Storage {
        return .{ .storage_type = storage_type, .offset = offset };
    }
    pub fn mark(self: Storage) struct { Type, u64 } {
        return .{ self.storage_type, self.offset };
    }
    pub fn get_next(self: *Storage, scratch_buffer: *StringBuilder, size: u8) ![]const u8 {
        assert(1 <= size and size <= 8);
        switch (self.storage_type) {
            .Stack => {
                const prev_offset = self.offset;
                self.offset -= size;
                return try scratch_buffer.append_fmt("-{}(%rbp)", .{prev_offset});
            },
            .CallArg => {
                unreachable;
            },
        }
    }
};

pub fn init(allocator: Allocator) Self {
    var arena = std.heap.ArenaAllocator.init(allocator);
    return .{ .allocator = allocator, .program_builder = .init(allocator), .scratch_buffer = .init(allocator), .string_arena = .init(arena.allocator()) };
}
pub inline fn get_generated_assembly(self: *const Self) []const u8 {
    return self.program_builder.string.items;
}
fn _get_size_of_register(reg: []const u8) u16 {
    return switch (reg.len) {
        1 => unreachable,
        2 => if (reg[0] != 'r') return 8 else return 2,
        3 => if (reg[0] == 'r') return 8 else return 4,
        else => unreachable,
    };
}
const LinuxCallingConvRegisters = [_][]const u8{
    "edi", "rdi",
    "esi", "rsi",
    "edx", "rdx",
    "ecx", "rcx",
    "r8d", "r8",
    "r9d", "r9",
};

pub fn get_callcov_arg_register(self: *Self, idx: usize, size: u32) []const u8 {
    _ = self;
    if (idx < LinuxCallingConvRegisters.len) {
        return LinuxCallingConvRegisters[(idx * 2) + (size / 8)];
    }
    unreachable;
}

//register should be a,b,c,d
fn get_register_based_on_size(self: *Self, register: []const u8, size: usize) []const u8 {
    switch (register[0]) {
        'a', 'b', 'c', 'd' => {},
        else => std.debug.panic("idk if register {s} exists or not", .{register}),
    }
    return switch (size) {
        1 => self.scratch_buffer.append_fmt("{s}l", .{register}) catch unreachable,
        2 => self.scratch_buffer.append_fmt("{s}x", .{register}) catch unreachable,
        4 => self.scratch_buffer.append_fmt("e{s}x", .{register}) catch unreachable,
        8 => self.scratch_buffer.append_fmt("r{s}x", .{register}) catch unreachable,
        else => {
            std.debug.print("size is this {}\n", .{size});
            unreachable;
        },
    };
}

fn _clear_register(self: *Self, register: []const u8) !void {
    _ = try self.program_builder.append_fmt("   xor %{s}, %{s}\n", .{ register, register });
}

pub fn get_size_of_int_literal(int_literal: u64) u32 {
    if (int_literal == 0) return 1;
    const n_bits: u16 = 64 - @clz(int_literal);
    const n_bytes: u16 = std.math.divCeil(u16, @intCast(n_bits), 8) catch unreachable;
    return n_bytes;
}
pub fn get_int_mnemonic_based_on_size(size: u8) []const u8 {
    return switch (size) {
        1 => "b",
        2 => "w",
        4 => "l",
        8 => "q",
        else => unreachable,
    };
}
pub fn compile_field_access(
    self: *Self,
    module: *Ast.Module,
    block: *Ast.Block,
    field: CompiledExprField,
    storage: ?*Storage,
    register: []const u8,
    register_size: ?u32,
) !struct { CompiledExpression, []const u8 } {
    var ret = try self.compile_expr(module, block, field.access.expr, storage);
    var expr_compiled: []const u8 = undefined;
    if (ret == .PlexLiteral) assert(ret.PlexLiteral.storage_type == .Stack); // we don't support calls at all

    var field_it = field.access.field;
    var fld_offset: u32 = 0;
    var fld_size: u32 = 0;
    // man this is the worst code I've ever written
    var is_last_fld_deref: bool = false;
    while (field_it) |fld| {
        defer field_it = fld.next;
        is_last_fld_deref = fld.kind == .Deref;

        switch (fld.kind) {
            .Member => {
                fld_offset += fld.field_offset;
                fld_size = fld.field_size;
            },
            .Deref => |deref| {
                var original_type = deref;
                original_type.info.ptr_depth -= 1;
                const original_size = (try TypeCheck.get_type_size_if_exists2(module, &original_type)).?;

                ret, expr_compiled = try self.compiled_expr_to_asm(module, block, storage, ret, register, register_size);
                // TODO(shahzad): @bug @priority we don't support dereferencing plex
                switch (ret) {
                    .Register => |*compiled_expr_as_reg| {
                        const pointer_reg = self.get_register_based_on_size(compiled_expr_as_reg.expr, 8);
                        expr_compiled = self.get_register_based_on_size(compiled_expr_as_reg.expr, original_size);
                        // TODO(shahzad): @fixme @priority we completely ignoring any non integer dereference :sob:
                        const mnemonic = get_int_mnemonic_based_on_size(@intCast(original_size));
                        _ = try self.program_builder.append_fmt("   mov{s} (%{s}), %{s}\n", .{ mnemonic, pointer_reg, expr_compiled });
                        expr_compiled = try self.scratch_buffer.append_fmt("%{s}", .{expr_compiled});
                        compiled_expr_as_reg.size = @intCast(original_size);
                        // TODO(shahzad)!!!!!: @bug @priority what about variable that holds a plex????_
                    },

                    else => std.debug.panic("deref for {} is not implemented!\n", .{ret}),
                }
            },
        }
    }

    if (!is_last_fld_deref) {
        switch (ret) {
            .Var => |*expr_as_var| {
                expr_as_var.offset -= fld_offset;
                expr_as_var.size = fld_size;
            },
            .Register => {
                // TODO(shahzad)!!!!!!: @bug @priority we assume that every dereferenced type is 64 bit
            },
            else => {
                std.log.err("man ts is ass {}\n", .{ret});
                unreachable;
            },
        }
        ret, expr_compiled = try self.compiled_expr_to_asm(module, block, storage, ret, register, register_size);
    }
    return .{ ret, expr_compiled };
}
pub fn compile_reference(self: *Self, module: *Ast.Module, block: *Ast.Block, compiled_expr: CompiledExpression, register: []const u8) anyerror!CompiledExpression {
    _ = module;
    _ = block;
    const reg = self.get_register_based_on_size(register, 8);
    switch (compiled_expr) {
        .Var => |compiled_expr_as_var| {
            _ = try self.program_builder.append_fmt("   leaq -{}(%rbp), %{s}\n", .{ compiled_expr_as_var.offset, reg });
            return .{ .Register = .{ .expr = register, .size = 8 } };
        },
        .Field => {
            unreachable;
        },
        .LitStr, .LitInt, .Call, .PlexLiteral, .Register => {
            // TODO(shahzad): @feat need to create temp variable for this, in type check add
            // code to create temp variables when reference to r values
            @panic("unimplemented");
        },
        .Reference => unreachable,
    }
}
pub fn compile_plex(self: *Self, module: *Ast.Module, block: *Ast.Block, plex: *const Ast.Expression.PlexDef, storage: *Storage) anyerror!void {
    if (storage.storage_type == .CallArg) @panic("we are cooked");
    const plex_decl = module.get_plex_decl(plex.name);
    for (plex.members.items, 0..) |*member, i| {
        const compiled_expr = try self.compile_expr(module, block, member, storage);
        // TODO(shahzad): @bug @priority recursive plex compilation
        const field_size: u8 = @intCast(plex_decl.?.fields.items[i].size);
        const byte_storage = try storage.get_next(&self.scratch_buffer, field_size);
        const postfix = get_int_mnemonic_based_on_size(field_size);
        var lhs_compiled: []const u8 = undefined;
        switch (compiled_expr) {
            .Var => |expr| {
                var register = try self.load_variable_to_register(expr, "d");
                if (field_size < expr.size) {
                    const smol_register = try self.load_variable_to_register(expr, "d");
                    _ = try self.program_builder.append_fmt("   movz{s}l %{s}, %{s}\n", .{ postfix, smol_register, register });
                    register = smol_register;
                }
                lhs_compiled = try self.scratch_buffer.append_fmt("%{s}", .{register});
            },
            .LitInt => |expr| {
                lhs_compiled = try self.scratch_buffer.append_fmt("${}", .{expr.literal});
            },
            .Register, .Call => |expr| {
                lhs_compiled = try self.scratch_buffer.append_fmt("%{s}", .{expr.expr});
            },
            .LitStr => |expr| {
                std.log.err("field_size {}\n", .{field_size});
                assert(field_size == 8);
                const register = self.get_register_based_on_size("d", 8);
                _ = try self.program_builder.append_fmt("   leaq {s}(%rip), %{s}\n", .{ expr.expr, register });
                lhs_compiled = try self.scratch_buffer.append_fmt("%{s}", .{register});
            },
            .Reference => |expr| {
                _ = try self.compile_reference(module, block, expr.*, "d");
                const register = self.get_register_based_on_size("d", 8);
                lhs_compiled = try self.scratch_buffer.append_fmt("%{s}", .{register});
            },

            .Field => @panic("unhandled"),
            // TODO(shahzad): @bug @priority this should be that hard but i am tired as shit
            .PlexLiteral => @panic("recursive plex literals are not supported as of now"),
        }
        _ = try self.program_builder.append_fmt("   mov{s} {s}, {s}\n", .{ postfix, lhs_compiled, byte_storage });
    }
}

pub fn compile_expr(self: *Self, module: *Ast.Module, block: *Ast.Block, expr: *const Ast.Expression, storage: ?*Storage) anyerror!CompiledExpression {
    switch (expr.*) {
        .LiteralInt => |expr_as_int_lit| {
            const int_lit_size: u32 = if (get_size_of_int_literal(expr_as_int_lit) <= 4) 4 else 8;
            return .{ .LitInt = .{ .literal = expr_as_int_lit, .size = int_lit_size } };
        },
        .LiteralString => |lit| {
            const str_lit = module.find_string_literal(lit);
            return .{ .LitStr = .{ .expr = str_lit.label, .size = 8 } };
        },
        .NoOp => {},
        .Var => |expr_as_var| {
            const var_type, const stack_var = block.find_variable(expr_as_var).?;
            _ = var_type;
            const stack_offset = stack_var.offset;

            return .{ .Var = .{ .offset = stack_offset, .size = stack_var.meta.size } };
        },
        .FieldAccess => |*field_access| {
            // TODO(shahzad): @fixme @priority we don't support pointers to plex :sob:
            return .{ .Field = .{ .access = field_access.* } };
        },
        .Reference => |*ref| {
            const ref_expr_duped = try self.allocator.create(CompiledExpression);
            ref_expr_duped.* = try self.compile_expr(module, block, ref.*, storage);
            return .{ .Reference = ref_expr_duped };
        },
        .Plex => |plex| {
            assert(storage != null);
            const storage_type, const offset = storage.?.mark();
            try self.compile_plex(module, block, &plex, storage.?);
            return .{ .PlexLiteral = .{ .storage_type = storage_type, .start = offset } };
        },
        .Call => |call_expr| {
            for (call_expr.params.items, 0..) |param_expr, idx| {
                var local_storage: Storage = .init(.CallArg, 0);
                const expr_compiled_to_reg = try self.compile_expr(module, block, &param_expr, storage orelse &local_storage);

                // TODO(shahzad): @bug @needContext we can't use %rdx for binOp because if we do
                // that after the 3th argument rdx will get overrided
                switch (expr_compiled_to_reg) {
                    .LitInt => |compiled_expr| {
                        const register = self.get_callcov_arg_register(idx, compiled_expr.size);
                        _ = try self.program_builder.append_fmt("   mov ${}, %{s}\n", .{ compiled_expr.literal, register });
                    },

                    .Var => |compiled_expr| {
                        const register = self.get_callcov_arg_register(idx, compiled_expr.size);
                        _ = try self.program_builder.append_fmt("   mov -{}(%rbp), %{s}\n", .{ compiled_expr.offset, register });
                    },
                    .Register, .Call => |compiled_expr| {
                        const callconv_register = self.get_callcov_arg_register(idx, compiled_expr.size);
                        const compiled_register = self.get_register_based_on_size(compiled_expr.expr, compiled_expr.size);
                        _ = try self.program_builder.append_fmt("   mov %{s}, %{s}\n", .{ compiled_register, callconv_register });
                    },
                    .LitStr => |compiled_expr| {
                        const register = self.get_callcov_arg_register(idx, compiled_expr.size);
                        if (idx * 2 < LinuxCallingConvRegisters.len) {
                            _ = try self.program_builder.append_fmt("   leaq {s}(%rip), %{s}\n", .{ compiled_expr.expr, register });
                        } else {
                            unreachable; // unimplemented
                            // _ = try self.program_builder.append_fmt("   mov %{s}, %{s}\n", .{ compiled_expr.expr, register });
                        }
                    },
                    .Reference => @panic("unimplemented!"),
                    .PlexLiteral => {
                        unreachable;
                    },
                    .Field => @panic("todo!"),
                }
            }
            var proc_decl = module.get_proc_decl(call_expr.name);

            // NOTE(shahzad): @hack cause we can also define our own put char
            if (proc_decl != null) {
                // c abi expect number of vector register used in rax if a function with
                // va args is called, we don't support that anyways to just zeroing out rax
                _ = try self.program_builder.append_fmt("   xor %rax, %rax\n", .{});
                _ = try self.program_builder.append_fmt("   call {s}@PLT\n", .{call_expr.name});
            } else {
                // @NOTE(shahzad): if the proc is not in decl_array that means it is not extern, which means
                // that it can only be a defined proc, calling undeclared proc is handled by the parser
                proc_decl = module.get_proc_def(call_expr.name).?.decl;

                _ = try self.program_builder.append_fmt("   xor %rax, %rax\n", .{});
                _ = try self.program_builder.append_fmt("   call {s}\n", .{call_expr.name});
            }
            const return_size = switch (proc_decl.?.return_size) {
                1...4 => 4,
                5...8 => 8,
                else => proc_decl.?.return_size,
            };
            // TODO(shahzad): @bug @priority add code to handle returning shit that's bigger than 8 bytes
            return .{ .Call = .{ .expr = "a", .size = @intCast(return_size) } };
        },
        .Block => |blk| {
            try self.compile_block(module, blk);
            return .{ .Register = .{ .expr = "assignment from compiled block is not implemented!", .size = 8 } };
        },
        .IfCondition => |if_condition| {
            module.total_branches += 1;

            var if_skip_label: [32]u8 = undefined;
            const if_skip_fmt = try std.fmt.bufPrint(&if_skip_label, "LB{d:0>2}", .{module.total_branches});

            module.total_branches += 1;
            var else_skip_label: [32]u8 = undefined;
            const else_skip_fmt = try std.fmt.bufPrint(&else_skip_label, "LB{d:0>2}", .{module.total_branches});

            const compiled_expr = try self.compile_expr(module, block, if_condition.if_.condition, null);
            switch (compiled_expr) {
                .Register => |reg| {
                    const register = self.get_register_based_on_size(reg.expr, reg.size);

                    _ = try self.program_builder.append_fmt("   test %{s}, %{s}\n", .{ register, register });
                    _ = try self.program_builder.append_fmt("   jz {s}\n", .{if_skip_fmt});
                },
                .Call => {
                    _ = try self.program_builder.append_fmt("   test %rax, %rax\n", .{});
                    _ = try self.program_builder.append_fmt("   jz {s}\n", .{if_skip_fmt});
                },

                else => {
                    std.log.err("{} is not supported while compiling if conditions\n", .{compiled_expr});
                    unreachable;
                },
            }
            _ = try self.compile_expr(module, block, if_condition.if_.expression, null);
            _ = try self.program_builder.append_fmt("   jmp {s}\n", .{else_skip_fmt});
            _ = try self.program_builder.append_fmt("{s}:\n", .{if_skip_fmt});
            if (if_condition.else_expr) |else_expr| {
                _ = try self.compile_expr(module, block, else_expr, null);
            }
            // TODO(shahzad): @pretty @perf? don't generate unnecessary  labels
            _ = try self.program_builder.append_fmt("{s}:\n", .{else_skip_fmt});
            return .{ .Register = .{ .expr = "assignment from if conditions is not implemented!", .size = 8 } };
        },
        .WhileLoop => |while_loop| {
            module.total_branches += 1;
            const n_branch = module.total_branches;

            var label: [32]u8 = undefined;
            const label_fmt = try std.fmt.bufPrint(&label, "LB{d:0>2}", .{n_branch});
            _ = try self.program_builder.append_fmt("{s}:\n", .{label_fmt});

            _ = try self.compile_expr(module, block, while_loop.expression, null);
            const compiled_expr = try self.compile_expr(module, block, while_loop.condition, null);

            switch (compiled_expr) {
                .Register => |reg| {
                    const register = self.get_register_based_on_size(reg.expr, reg.size);
                    _ = try self.program_builder.append_fmt("   test %{s}, %{s}\n", .{ register, register });
                    _ = try self.program_builder.append_fmt("   jnz {s}\n", .{label_fmt});
                },
                .Call => {
                    _ = try self.program_builder.append_fmt("   test %rax, %rax\n", .{});
                    _ = try self.program_builder.append_fmt("   jnz {s}\n", .{label_fmt});
                },
                else => unreachable,
            }

            return .{ .Register = .{ .expr = "assignment from if conditions is not implemented!", .size = 8 } };
        },
        // @TODO(shahzad): @needContext figure out what to do with this shit
        .Tuple => {},
        .BinOp => |*expr_as_bin_op| {
            return try self.compile_expr_bin_op(module, block, expr_as_bin_op, storage);
        },
    }
    unreachable;
}

//      =
//      /\
//     x  +
//        /\
//      34  35
//
//
//      2 int literals = lea rax + intlit, 2nd intlit
//      1var 1int literals = load variable in rax and add rax, int lit
//      2var = load variable in rax, load variable in rdx add
fn load_int_literal_to_register(self: *Self, expr: CompiledExprLiteral, register: []const u8) ![]const u8 {
    const reg = self.get_register_based_on_size(register, expr.size);
    _ = try self.program_builder.append_fmt("   mov ${}, %{s}\n", .{ expr.literal, reg });
    return reg;
}
fn compile_mov_reg_inst(self: *Self, src: CompiledExpCommon, dest: []const u8) ![]const u8 {
    const rhs = self.get_register_based_on_size(src.expr, src.size);
    const lhs = self.get_register_based_on_size(dest, src.size);
    _ = try self.program_builder.append_fmt("   mov %{s}, %{s} #why is this getting called\n", .{ rhs, lhs });
    return lhs;
}

pub fn load_variable_to_register(self: *Self, expr: CompiledExprStack, register: []const u8) ![]const u8 {
    // const register_size: u32 = if (expr.size <= 4) 4 else 8;
    const register_size: u32 = expr.size;
    const reg = self.get_register_based_on_size(register, register_size);
    _ = try self.program_builder.append_fmt("   mov -{}(%rbp), %{s}\n", .{ expr.offset, reg });
    return reg;
}

fn get_compare_store_inst_based_on_op(bin_op: *const Ast.BinaryOperation) []const u8 {
    switch (bin_op.op) {
        .Eq => return "sete",
        .Lt => return "setl",
        else => @panic("unimplemented!"),
    }
}
pub fn compiled_expr_to_asm(
    self: *Self,
    module: *Ast.Module,
    block: *Ast.Block,
    storage: ?*Storage,
    compiled_expr: CompiledExpression,
    register: []const u8,
    register_size: ?u32,
) anyerror!struct { CompiledExpression, []const u8 } {
    var expr_compiled: []const u8 = undefined;

    const ret: CompiledExpression = blk: switch (compiled_expr) {
        .LitInt => |expr| {
            const reg = try self.load_int_literal_to_register(expr, register);
            expr_compiled = try self.scratch_buffer.append_fmt("%{s}", .{reg});
            break :blk .{ .Register = .{ .expr = register, .size = expr.size } };
        },
        .Var => |expr| {
            var reg = try self.load_variable_to_register(expr, register);
            var ret_size = expr.size;
            if (ret_size < 4) {
                ret_size = 4;
                const extended_reg = self.get_register_based_on_size(register, ret_size);
                const lhs_mnemonic = get_int_mnemonic_based_on_size(@intCast(expr.size));
                _ = try self.program_builder.append_fmt("   movz{s} %{s}, %{s} # extending\n", .{ lhs_mnemonic, reg, extended_reg });
                reg = extended_reg;
            }
            expr_compiled = try self.scratch_buffer.append_fmt("%{s}", .{reg});
            break :blk .{ .Register = .{ .expr = register, .size = ret_size } };
        },
        .Register, .Call => |expr| {
            const moved_to = try self.compile_mov_reg_inst(
                .{ .expr = expr.expr, .size = expr.size },
                register,
            );
            expr_compiled = try self.scratch_buffer.append_fmt("%{s}", .{moved_to});
            break :blk .{ .Register = .{ .expr = register, .size = register_size orelse expr.size } };
        },
        .LitStr => |expr| {
            const reg = self.get_register_based_on_size(register, 8);
            _ = try self.program_builder.append_fmt("   leaq {s}(%rip), %{s}\n", .{ expr.expr, reg });
            expr_compiled = try self.scratch_buffer.append_fmt("%{s}", .{reg});
            break :blk .{ .Register = .{ .expr = "unreachable you cannot assign to strlit", .size = 8 } };
        },
        .PlexLiteral => |plex_lit| {
            // _ = try self.program_builder.append_fmt("   xor %rax,%rax # fix this hack\n", .{});
            self.scratch_buffer.reset();
            break :blk .{ .PlexLiteral = plex_lit };
        },
        .Field => |field| {
            const ret, expr_compiled = try self.compile_field_access(module, block, field, storage, register, register_size);
            break :blk ret;
        },
        .Reference => |inner_expr| {
            const ref_compiled = try self.compile_reference(module, block, inner_expr.*, register);
            expr_compiled = try self.scratch_buffer.append_fmt("%{s}", .{self.get_register_based_on_size(register, 8)});
            break :blk ref_compiled;
        },
    };
    return .{ ret, expr_compiled };
}
pub fn compile_expr_bin_op(self: *Self, module: *Ast.Module, block: *Ast.Block, bin_op: *const Ast.BinaryOperation, storage: ?*Storage) anyerror!CompiledExpression {
    // TODO(shahzad): @bug @priority 64 bits bin ops are fucked :sob:
    const lhs = try self.compile_expr(module, block, bin_op.lhs, storage);
    const rhs = try self.compile_expr(module, block, bin_op.rhs, storage);
    // TODO(shahzad): @hack this is a hack when we don't know which register rhs will return
    // if lhs also returns the same register ie .Call op .Call which will be op %rax %rax
    // so if rhs is register then we change the lhs register to "b"
    const lhs_register = switch (rhs) {
        .Register, .Call => "b",
        else => "a",
    };

    const lhs_compiled_expr, const lhs_compiled = blk: switch (bin_op.op) {
        .Ass => {
            switch (lhs) {
                .Var => |expr| {
                    const lhs_compiled = try self.scratch_buffer.append_fmt("-{}(%rbp)", .{expr.offset});
                    const ret: CompiledExpression = .{ .Var = .{ .offset = expr.offset, .size = expr.size } };
                    break :blk .{ ret, lhs_compiled };
                },
                else => unreachable, // we don't give a shit as of now
            }
        },
        else => break :blk try self.compiled_expr_to_asm(module, block, storage, lhs, lhs_register, null),
    };
    const rhs_compiled_expr, const rhs_compiled = blk: switch (bin_op.op) {
        .Ass => {
            return switch (rhs) {
                .Register, .Call => |expr| {
                    const lhs_size: u32 = if (lhs.get_size() <= 4) 4 else 8;
                    const register = self.get_register_based_on_size(expr.expr, lhs_size);
                    if (lhs == .Var and lhs_size == 4) {
                        const lhs_mnemonic = get_int_mnemonic_based_on_size(@intCast(lhs_size));
                        _ = try self.program_builder.append_fmt("   mov{s} %{s}, %{s} # extending\n", .{ lhs_mnemonic, register, register });
                    }
                    const rhs_compiled = try self.scratch_buffer.append_fmt("%{s}", .{register});
                    const ret: CompiledExpression = .{ .Register = .{ .expr = "unreachable this shit #assignment", .size = expr.size } };
                    break :blk .{ ret, rhs_compiled };
                },
                .Field => {
                    var ret, const compiled_expr = try self.compiled_expr_to_asm(module, block, storage, rhs, "d", null);
                    assert(ret == .Register);
                    const ret_size = ret.get_size();
                    const lhs_size: u32 = if (lhs.get_size() <= 4) 4 else 8;
                    // a register whose size matches with with lhs
                    const lhs_size_reg = self.get_register_based_on_size("d", lhs_size);
                    std.log.debug("ret size is this {}\n", .{ret_size});
                    // zero extend
                    if (ret_size < 4) {
                        const mnemonic = get_int_mnemonic_based_on_size(@intCast(ret_size));
                        _ = try self.program_builder.append_fmt("   movz{s}l {s}, %{s} # extending\n", .{ mnemonic, compiled_expr, lhs_size_reg });
                    } else if (ret_size == 4) {
                        // _ = try self.program_builder.append_fmt("   movl %{s}, %{s} # extending bruh\n", .{ lhs_size_reg, lhs_size_reg });
                    }
                    const rhs_compiled = try self.scratch_buffer.append_fmt("%{s}", .{lhs_size_reg});
                    ret = .{ .Register = .{ .expr = "unreachable this shit #assignment", .size = ret.Register.size } };
                    break :blk .{ ret, rhs_compiled };
                },
                else => break :blk try self.compiled_expr_to_asm(module, block, storage, rhs, "d", null),
            };
        },

        .LtEq, .GtEq, .Lt, .Gt, .Eq => {
            const lhs_size: u32 = if (lhs_compiled_expr.get_size() <= 4) 4 else 8;
            break :blk try self.compiled_expr_to_asm(module, block, storage, rhs, "d", lhs_size);
        },
        else => break :blk try self.compiled_expr_to_asm(module, block, storage, rhs, "d", null),
    };
    switch (bin_op.op) {
        .Add, .Sub, .Mul, .Div, .Eq, .Lt => {
            switch (lhs) {
                .LitStr, .PlexLiteral => unreachable,
                else => {},
            }
            switch (rhs) {
                .LitStr, .PlexLiteral => unreachable,
                else => {},
            }
        },
        else => {},
    }
    var ret: CompiledExpression = rhs_compiled_expr;
    switch (bin_op.op) {
        .Add => {
            _ = try self.program_builder.append_fmt("   add {s}, {s}\n", .{ lhs_compiled, rhs_compiled });
        },
        .Sub => {
            _ = try self.program_builder.append_fmt("   sub {s}, {s}\n", .{ lhs_compiled, rhs_compiled });
        },
        .Mul => {
            _ = try self.program_builder.append_fmt("   imul {s}, {s}\n", .{ lhs_compiled, rhs_compiled });
        },
        .Div => {
            // TODO(shahzad): support floating point divides
            const mnemonic = get_int_mnemonic_based_on_size(@intCast(rhs_compiled_expr.get_size()));
            const b_reg = self.get_register_based_on_size("b", rhs_compiled_expr.get_size());
            _ = try self.program_builder.append_fmt("   #-----divide------\n", .{});
            _ = try self.program_builder.append_fmt("   mov{s} {s}, %{s}\n", .{ mnemonic, rhs_compiled, b_reg });
            _ = try self.program_builder.append_fmt("   xor {s}, {s}\n", .{ rhs_compiled, rhs_compiled });
            _ = try self.program_builder.append_fmt("   idiv %{s}\n", .{b_reg});
            _ = try self.program_builder.append_fmt("   mov{s} {s}, {s}\n", .{ mnemonic, lhs_compiled, rhs_compiled });
        },

        .Ass => {
            // if it's a plex literal meaning we will handle it with storage
            // TODO(shahzad): @refactor ^
            if (rhs != .PlexLiteral) {
                ret = lhs_compiled_expr;
                const lhs_size: u32 = if (lhs.get_size() <= 4) 4 else 8;
                const lhs_mnemonic = get_int_mnemonic_based_on_size(@intCast(lhs_size));
                _ = try self.program_builder.append_fmt("   mov{s} {s}, {s} # is this the culprit\n", .{ lhs_mnemonic, rhs_compiled, lhs_compiled });
            }
        },
        .Eq, .Lt => {
            switch (rhs) {
                // .Register, .Call => |expr| {
                //     // NOTE(shahzad): we are using the lhs size here is this alright chat?
                //     const register = self.get_register_based_on_size(expr.expr, lhs_size);
                //     rhs_compiled = try self.scratch_buffer.append_fmt("%{s}", .{register});
                // },
                .LitStr, .PlexLiteral => unreachable,
                else => {},
            }

            _ = try self.program_builder.append_fmt("   cmpl {s}, {s}\n", .{ rhs_compiled, lhs_compiled });
            const cmp_inst = get_compare_store_inst_based_on_op(bin_op);
            _ = try self.program_builder.append_fmt("   {s} %dl\n", .{cmp_inst});

            // NOTE(shahzad): @bug we expect that any op with respect to a comparison has to be
            // 32 bits wide is not always the case
            _ = try self.program_builder.append_fmt("   movzbl %dl, %edx\n", .{});
            self.scratch_buffer.reset();
            ret = .{ .Register = .{ .expr = "d", .size = 4 } };
        },

        else => std.debug.panic("compile_expr_bin_op for {} is not implemented!", .{bin_op}),
    }
    self.scratch_buffer.reset();
    return ret;
}
pub fn compile_stmt(self: *Self, module: *Ast.Module, block: *Ast.Block, statement: *Ast.Statement) !void {
    switch (statement.*) {
        .VarDefStack, .VarDefStackMut => |stmt| {
            if (!std.meta.eql(stmt.expr, .NoOp)) {
                var var_as_expr: Ast.Expression = .{ .Var = stmt.name };
                var rhs_as_expr = stmt.expr;
                const bin_op_expr: Ast.BinaryOperation = .{
                    .op = .Ass,
                    .lhs = &var_as_expr,
                    .rhs = &rhs_as_expr,
                };

                const var_type, const stack_var = block.find_variable(stmt.name).?;
                assert(var_type == .Stack);
                var storage: Storage = .init(.Stack, stack_var.offset);
                _ = try self.compile_expr_bin_op(module, block, &bin_op_expr, &storage);
            }
        },
        .Expr => |*stmt_as_expr| {
            _ = try self.compile_expr(module, block, stmt_as_expr, null);
        },
        else => {},
    }
}
fn compile_proc_prologue(self: *Self, procedure: *Ast.ProcDef) !void {
    _ = try self.program_builder.append_fmt("{s}:\n", .{procedure.decl.name});
    _ = try self.program_builder.append_fmt("   mov %rsp, %rbp\n", .{});
    _ = try self.program_builder.append_fmt("   sub ${}, %rsp\n", .{procedure.total_stack_var_offset});
    for (procedure.decl.args_list.items, 0..) |arg, i| {
        const register = self.get_callcov_arg_register( i, arg.meta.size);
        _ = try self.program_builder.append_fmt("   mov %{s}, -{}(%rbp)\n", .{  register, arg.offset });
    }

    //for (procedure.decl.args_list.items) |arguments| {
    //}
}
fn compile_block(self: *Self, module: *Ast.Module, block: *Ast.Block) anyerror!void {
    for (block.stmts.items) |*statement| {
        try self.compile_stmt(module, block, statement);
    }
}
pub fn compile_proc(self: *Self, module: *Ast.Module, procedure: *Ast.ProcDef) !void {
    try self.compile_proc_prologue(procedure);
    try self.compile_block(module, procedure.block);
    try self.compile_proc_epilogue(procedure);
}
fn compile_proc_epilogue(self: *Self, procedure: *Ast.ProcDef) !void {
    _ = try self.program_builder.append_fmt("   add ${}, %rsp\n", .{procedure.total_stack_var_offset});
    std.log.debug("@TODO(shahzad): add return value :sob:", .{});
    _ = try self.program_builder.append_fmt("   xor %rax, %rax\n", .{});
    _ = try self.program_builder.append_fmt("   ret\n", .{});
}
pub fn compile_data_section(self: *Self, module: *Ast.Module) !void {
    var label_no: usize = 0;
    _ = try self.program_builder.append_fmt(".section .rodata\n", .{});
    for (module.string_literals.items) |*str_lit| {
        str_lit.label = try self.string_arena.append_fmt("LD{d:0>2}", .{label_no});
        _ = try self.program_builder.append_fmt("{s}:\n", .{str_lit.label});
        _ = try self.program_builder.append_fmt(".string \"{s}\"\n", .{str_lit.string});
        label_no += 1;
    }
}

pub fn compile_mod(self: *Self, module: *Ast.Module) !void {
    try self.compile_data_section(module);
    _ = try self.program_builder.append_fmt(".section .text\n", .{});
    if (module.has_main_proc) {
        _ = try self.program_builder.append_fmt(".global main\n", .{});
        // @NOTE(shahzad): we linking with crt so we don't care much about anything for now
    }
    var proc_decl_iter = module.proc_decls.iterator(0);
    while (proc_decl_iter.next()) |proc_decl| {
        _ = try self.program_builder.append_fmt(".extern {s}\n", .{proc_decl.name});
    }
    var proc_def_iter = module.proc_defs.iterator(0);
    while (proc_def_iter.next()) |proc_def| {
        try self.compile_proc(module, proc_def);
    }
}
