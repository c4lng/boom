const std = @import("std");
const Allocator = std.mem.Allocator;
const ArrayListManaged = std.array_list.Managed;
const StringHashMap = std.hash_map.StringHashMap;
const assert = std.debug.assert;

const Ast = @import("../ast.zig");
const Ir = @import("../ir.zig");
const StringBuilder = @import("../string_builder.zig");
const Self = @This();

allocator: Allocator,
program_builder: StringBuilder,
scratch_buffer: StringBuilder,
strings: StringBuilder,
computed_values: ArrayListManaged(Operand),
values: ArrayListManaged(Ir.Value),
used_strings: StringHashMap([]const u8),
registers: u9 = 0b000000000,

// TODO(shahzad): @scope duplication put this in utils or smth
const get_value = Ir.get_value;

const LinuxCallingConvRegisters = [_]Register{
    .{ .id = .DI, .width = 8 },
    .{ .id = .SI, .width = 8 },
    .{ .id = .D, .width = 8 },
    .{ .id = .C, .width = 8 },
    .{ .id = .r8, .width = 8 },
    .{ .id = .r9, .width = 8 },
};

pub const Register = struct {
    pub const Id = enum(u8) {
        // we only give a shit about callee saved register
        // that's why the order is like that
        // zig fmt: off
        NULL  =  0,   A    =  1,   C    =  2,   D    =  3,   SI   =  4,
        DI    =  5,   r8   =  6,   r9   =  7,   r10  =  8,   r11  =  9,
        B     =  10,  r12  =  11,  r13  =  12,  r14  =  13,  r15  =  14,
        // zig fmt: on
        pub inline fn to_int(id: Id) u8 {
            return @intFromEnum(id);
        }
        pub inline fn from_int(id: u8) Id {
            return @enumFromInt(id);
        }
    };

    id: Id,
    width: u8,
    pub fn make(id: Id, width: u8) Register {
        return .{ .id = id, .width = width };
    }
    pub fn _null() Register {
        return .{ .id = .NULL, .width = 8 };
    }
    // i stole this from ChatGPT and i am not proud of it :sob::sob:
    pub fn to_string(self: @This()) []const u8 {
        const w = self.width;
        return switch (self.id) {
            .NULL => "null",
            .A => reg_name(w, "al", "ax", "eax", "rax"),
            .B => reg_name(w, "bl", "bx", "ebx", "rbx"),
            .C => reg_name(w, "cl", "cx", "ecx", "rcx"),
            .D => reg_name(w, "dl", "dx", "edx", "rdx"),
            .SI => reg_name(w, "sil", "si", "esi", "rsi"),
            .DI => reg_name(w, "dil", "di", "edi", "rdi"),

            inline else => |reg_tag| reg_name(w, @tagName(reg_tag) ++ "b", @tagName(reg_tag) ++ "w", @tagName(reg_tag) ++ "d", @tagName(reg_tag)),
        };
    }
    pub fn change_width(reg: Register, new_width: u8) Register {
        return .{ .id = reg.id, .width = new_width };
    }
    pub fn upcast(reg: Register, new_width: u8) Register {
        if (reg.width > new_width) @panic("invalid upcast");
        return reg.change_width(new_width);
    }
    pub fn downcast(reg: Register, new_width: u8) Register {
        if (reg.width < new_width) @panic("invalid downcast");
        return reg.change_width(new_width);
    }

    inline fn reg_name(
        width: u8,
        r8: []const u8,
        r16: []const u8,
        r32: []const u8,
        r64: []const u8,
    ) []const u8 {
        return switch (width) {
            1 => r8,
            2 => r16,
            4 => r32,
            8 => r64,
            else => std.debug.panic("invalid register width {}\n", .{width}),
        };
    }
};

pub const Operand = struct {
    pub const Memory = struct {
        start: union(enum) { Register: Register, Label: []const u8 },
        offset: usize,
        len: usize,
    };
    kind: union(enum) {
        Immediate: u64,
        Register: Register,
        Memory: Memory,
        Void: void,
    },
    pub fn as_compiled_string(self: *const Operand, sb: *StringBuilder) ![]const u8 {
        const compiled = blk: switch (self.kind) {
            .Register => |reg| {
                break :blk try sb.append_fmt("%{s}", .{reg.to_string()});
            },
            .Immediate => |imm_value| {
                break :blk try sb.append_fmt("${}", .{imm_value});
            },
            .Memory => unreachable,
            .Void => unreachable,
        };
        return compiled;
    }
};

const RegAllocInfo = struct { requested: Register, to_spill: Register };

pub fn push_register(self: *Self, reg: Register) !void {
    assert(reg.width == 8);
    _ = try self.program_builder.append_fmt("   pushq %{s}\n", .{reg.to_string()});
}

pub fn pop_register(self: *Self, reg: Register) !void {
    assert(reg.width == 8);
    _ = try self.program_builder.append_fmt("   popq %{s}\n", .{reg.to_string()});
}

pub fn save_call_registers(self: *Self) !u9 {
    for (1..10) |i| {
        const as_reg = Register.make(.from_int(@intCast(i)), 8);
        if (!self.is_reg_available(as_reg)) try self.push_register(as_reg);
    }
    const mark = self.registers;
    self.registers = 0;
    return mark;
}
pub fn restore_call_registers(self: *Self, mark: u9) !void {
    self.registers = mark;

    var registers: [9]Register = undefined;
    var len: usize = 0;

    for (1..10) |i| {
        const as_reg = Register.make(.from_int(@intCast(i)), 8);
        if (!self.is_reg_available(as_reg)) {
            registers[len] = as_reg;
            len += 1;
        }
    }
    var it: isize = @as(isize, @intCast(len)) - 1;
    while (it >= 0) {
        const register = registers[@intCast(it)];
        std.debug.print("reg {s}\n", .{register.to_string()});
        try self.pop_register(register);
        it -= 1;
    }
}
pub fn ensure_reg(self: *Self, operand: Operand, to: Register) !RegAllocInfo {
    switch (operand.kind) {
        .Register => |as_reg| return .{ .requested = as_reg, .to_spill = ._null() },
        .Immediate => |imm_value| {
            // TODO(shahzad): hardcoded
            if (to.id != .NULL) {
                const alloc_info = self.reg_alloc2(to.id, to.width);
                if (alloc_info.to_spill.id != .NULL) {
                    try self.mov_reg_to_reg(alloc_info.requested, alloc_info.to_spill);
                }
                try self.load_imm_to_reg(imm_value, alloc_info.requested);
                return alloc_info;
            }
            const reg = self.reg_alloc(4);
            try self.load_imm_to_reg(imm_value, reg);
            return .{ .requested = reg, .to_spill = ._null() };
        },
        .Memory => unreachable,
        .Void => unreachable,
    }
}

pub fn make_register_mask(registers: []Register.Id) u9 {
    var mask: u9 = 0;
    for (registers) |id| {
        const bit_idx = @as(u9, @intCast(1)) << @intCast(id.to_int() - 1);
        mask ^= bit_idx;
    }
    return mask;
}
pub fn reg_alloc_except(self: *Self, width: u8, mask: u9) Register {
    const original = self.registers;

    self.registers = mask | self.registers;
    const register = self.reg_alloc(width);
    self.registers = original;
    return register;
}
pub fn reg_alloc2(self: *Self, id: Register.Id, width: u8) RegAllocInfo {
    const reg: Register = .make(id, width);
    if (!self.is_reg_available(reg)) {
        const spill_reg = self.reg_alloc(width);
        return .{ .requested = reg, .to_spill = spill_reg };
    }

    const bit_idx = @as(u9, @intCast(1)) << @intCast(id.to_int() - 1);
    self.registers ^= bit_idx;
    std.log.info("bit_idx: {x}", .{bit_idx});
    std.log.info("allocated register {} state :{b}", .{ id, self.registers });
    assert(!self.is_reg_available(reg));
    return .{ .requested = reg, .to_spill = ._null() };
}

pub fn reg_alloc(self: *Self, width: u8) Register {
    const lowest_unset_bit = ~self.registers & (self.registers + 1);
    if (lowest_unset_bit == 0) return ._null();

    const idx = 9 - @clz(lowest_unset_bit);
    assert(idx >= 0 and idx < 64);

    const reg_info = self.reg_alloc2(@enumFromInt(idx), width);
    assert(reg_info.to_spill.id == .NULL);
    return reg_info.requested;
}
pub fn is_reg_available(self: *Self, reg: Register) bool {
    const bit_idx: u4 = @as(u4, @intCast(reg.id.to_int())) - 1;
    return (self.registers >> (bit_idx)) & 1 == 0;
}
pub fn reg_free(self: *Self, reg: Register) void {
    std.debug.print("freeing register {}\n", .{reg.id});
    if (reg.id == .NULL) return;
    const mask: u9 = @as(u9, 1) << (@as(u4, @intCast(reg.id.to_int())) - 1);
    assert(!self.is_reg_available(reg));

    self.registers ^= mask;
    assert(self.is_reg_available(reg));
}

pub fn print_allocated_registers(self: *Self) void {
    std.debug.print("--------------------\n", .{});
    std.debug.print("register {b}\n", .{self.registers});
    for (1..10) |i| {
        const as_reg = Register.make(.from_int(@intCast(i)), 4);
        if (!self.is_reg_available(as_reg)) {
            std.debug.print("register {} is available!\n", .{as_reg.id});
        }
    }
    std.debug.print("--------------------\n", .{});
}

pub fn init(allocator: Allocator, values: ArrayListManaged(Ir.Value)) !Self {
    const self: Self = .{
        .allocator = allocator,
        .program_builder = .init(allocator),
        .scratch_buffer = .init(allocator),
        .strings = .init(allocator),
        .used_strings = .init(allocator),
        .computed_values = .init(allocator),
        .values = values,
    };
    return self;
}

// TODO(shahzad): @scope @priority register should be a structure
pub fn mov_reg_to_reg(self: *Self, src: Register, dst: Register) !void {
    var comment: []const u8 = "";

    var _src = src;
    if (src.id == dst.id) return;

    if (src.width > dst.width) {
        comment = "# loss of information";
        _src = src.downcast(dst.width);
    } else {
        _src = src.upcast(dst.width);
    }

    _ = try self.program_builder.append_fmt("   mov %{s}, %{s}\n", .{ _src.to_string(), dst.to_string() });
}
pub fn load_imm_to_reg(self: *Self, src: u64, dst: Register) !void {
    _ = try self.program_builder.append_fmt("   mov ${}, %{s}\n", .{ src, dst.to_string() });
}
pub fn load_mem_to_reg(self: *Self, src: Operand.Memory, dst: Register) !void {
    switch (src.start) {
        .Label => |as_lbl| {
            // TODO(shahzad): @fixme this is a hack
            const dst_fixed: Register = .{ .width = 8, .id = dst.id };
            _ = try self.program_builder.append_fmt("   leaq {s}(%rip), %{s}\n", .{ as_lbl, dst_fixed.to_string() });
        },
        .Register => |as_reg| {
            return self.mov_reg_to_reg(as_reg, dst);
        },
    }
}
// pub fn spill_reg(self: *Self, from: Register, to: Register) !void {}
pub fn mov_op_to_reg(self: *Self, src: Operand, dst: Register) !void {
    switch (src.kind) {
        .Register => |as_reg| {
            try self.mov_reg_to_reg(as_reg, dst);
        },
        .Immediate => |as_imm| {
            try self.load_imm_to_reg(as_imm, dst);
        },
        .Memory => |as_mem| {
            try self.load_mem_to_reg(as_mem, dst);
        },
        .Void => unreachable,
    }
}
pub fn compile_inst(self: *Self, mod: *Ir.Module, inst: *const Ir.Instruction, proc: *Ir.Procedure, bb_idx: usize) anyerror!Operand {
    const bb: *Ir.BasicBlock = &proc.block.basic_blocks.items[bb_idx];
    const mark = self.scratch_buffer.mark();
    defer self.scratch_buffer.reset(mark);
    // TODO(shahzad): @bug @priority free rhs register
    std.debug.print("this is the instruction we are compiling {}\n", .{inst});
    switch (inst.type) {
        .BinOp => |as_binop| {
            var lhs_ = try self.resolve_value(get_value(self.values, inst.operands.items[0]), bb);
            var rhs_ = try self.resolve_value(get_value(self.values, inst.operands.items[1]), bb);

            std.debug.print("lhs = {}, rhs = {}\n", .{ lhs_, rhs_ });

            if (as_binop.is_identity() and
                lhs_.kind == .Immediate and (rhs_.kind == .Register or rhs_.kind == .Memory))
            { // if one side is register make it lhs
                std.mem.swap(Operand, &lhs_, &rhs_);
            }

            const lhs = lhs_;
            const rhs = rhs_;

            if (as_binop == .Ass and lhs.kind != .Register) {
                // @note when doing assignment we are making sure that lhs is a register
                // so that's why we are moving whatever op we have as lhs to a register
                // but this does not matter as we do not care about the value of lhs as
                // we are going to replace it anyways
                _ = try self.program_builder.append_fmt("   # @Assignment extra mov that doesn't matter\n", .{});
            }
            const lhs_reg_info = try self.ensure_reg(lhs, if (as_binop == .Div) .make(.A, 4) else ._null());
            const lhs_compiled = try self.scratch_buffer.append_fmt("%{s}", .{lhs_reg_info.requested.to_string()});
            const rhs_compiled = try rhs.as_compiled_string(&self.scratch_buffer);

            var ret_reg: Register = ._null();
            if (lhs_reg_info.to_spill.id == .NULL) ret_reg = lhs_reg_info.requested else {
                ret_reg = self.reg_alloc_except(4, Register.Id.D.to_int());
                if (ret_reg.id == .NULL) unreachable; // we ran out of registers
            }

            switch (as_binop) {
                .Add => {
                    const lhs_value = get_value(self.values, inst.operands.items[0]);
                    if (lhs_value.type != .Temp) {
                        // this means that lhs register that is probably a variable
                        // and we should not modify it so we create a register to
                        // do the addition
                        // @todo hardcoded

                        const add_store_reg = self.reg_alloc(4);
                        try self.mov_reg_to_reg(lhs_reg_info.requested, add_store_reg);
                        _ = try self.program_builder.append_fmt("   add {s}, %{s}\n", .{ rhs_compiled, add_store_reg.to_string() });
                        ret_reg = add_store_reg;

                    } else _ = try self.program_builder.append_fmt("   add {s}, {s}\n", .{ rhs_compiled, lhs_compiled });
                },
                .Sub => {
                    _ = try self.program_builder.append_fmt("   sub {s}, {s}\n", .{ rhs_compiled, lhs_compiled });
                },
                .Mul => {
                    _ = try self.program_builder.append_fmt("   imul {s}, {s}\n", .{ rhs_compiled, lhs_compiled });
                },
                .Div => {
                    _ = try self.program_builder.append_fmt("   #-----divide------\n", .{});

                    const dx_reg_info = try self.ensure_reg(.{
                        .kind = .{ .Immediate = 0 },
                    }, .make(.D, 4));
                    const rhs_reg_info = try self.ensure_reg(rhs, ._null());

                    _ = try self.program_builder.append_fmt("   idiv %{s}\n", .{rhs_reg_info.requested.to_string()});
                    self.reg_free(rhs_reg_info.requested);

                    if (dx_reg_info.to_spill.id != .NULL) {
                        try self.mov_reg_to_reg(dx_reg_info.to_spill, dx_reg_info.requested);
                        self.reg_free(dx_reg_info.to_spill);
                    } else self.reg_free(dx_reg_info.requested);

                    try self.mov_reg_to_reg(lhs_reg_info.requested, ret_reg);

                    if (ret_reg.id != lhs_reg_info.requested.id) self.reg_free(lhs_reg_info.requested);
                    _ = try self.program_builder.append_fmt("   #------------------\n", .{});
                },

                .Eq, .Lt, .Gt, .LtEq, .GtEq => |typ| {
                    const cmp_set_inst = switch (typ) {
                        .Eq => "sete",
                        .Lt => "setl",
                        else => unreachable,
                    };
                    const cmp_result_reg = self.reg_alloc(1);
                    _ = try self.program_builder.append_fmt("   cmp {s}, {s}\n", .{ rhs_compiled, lhs_compiled });
                    _ = try self.program_builder.append_fmt("   {s} %{s}\n", .{ cmp_set_inst, cmp_result_reg.to_string() });
                    _ = try self.program_builder.append_fmt("   movzbl %{s}, %{s}\n", .{ cmp_result_reg.to_string(), cmp_result_reg.upcast(4).to_string() });
                    ret_reg = cmp_result_reg;
                },

                .Ass => {
                    try self.mov_op_to_reg(rhs, ret_reg);
                },
                else => |typ| {
                    std.debug.panic("type {} is unimplemented!", .{typ});
                }, // unimplemented
            }

            if (lhs_reg_info.to_spill.id != .NULL) {
                try self.mov_reg_to_reg(lhs_reg_info.to_spill, lhs_reg_info.requested);
                self.reg_free(lhs_reg_info.to_spill);
            }

            var dst = get_value(self.values, inst.produces);
            _ = try self.computed_values.append(.{ .kind = .{ .Register = ret_reg } });
            dst.lowered_operand_idx = self.computed_values.items.len - 1;
            return .{ .kind = .{ .Register = ret_reg } };
        },
        .Return => {
            const value = get_value(self.values, inst.operands.items[0]);
            const operand = try self.resolve_value(value, bb);
            switch (operand.kind) {
                .Immediate => |imm_value| {
                    if (!self.is_reg_available(.make(.A, 4))) {
                        @panic("codegen violation: RAX is in use!");
                    }
                    const reg: Register = .make(.A, 8);
                    try self.load_imm_to_reg(imm_value, reg);
                    _ = try self.program_builder.append_fmt("   ret\n", .{});
                    return .{ .kind = .Void };
                },
                .Register => |reg| {
                    try self.mov_reg_to_reg(reg, .make(.A, 8));
                    _ = try self.program_builder.append_fmt("   ret\n", .{});
                    return .{ .kind = .Void };
                },
                .Memory => unreachable,
                .Void => unreachable,
            }
        },
        .ProcCall => |call_name| {
            std.debug.print("pushing the registers and shit\n", .{});
            self.print_allocated_registers();
            const register_mark = try self.save_call_registers();

            for (inst.operands.items, 0..) |param_expr_idx, idx| {
                const value = get_value(self.values, param_expr_idx);
                const operand = try self.resolve_value(value, bb);
                const call_reg = LinuxCallingConvRegisters[idx];
                try self.mov_op_to_reg(operand, call_reg);
            }

            var is_plt: []const u8 = "";
            for (mod.proc_decls.items) |proc_decl| {
                if (std.mem.eql(u8, proc_decl.name, call_name)) {
                    if (proc_decl.extrn == true) {
                        is_plt = "@PLT";
                    }
                }
            }

            _ = try self.program_builder.append_fmt("   xor %rax, %rax\n", .{});
            _ = try self.program_builder.append_fmt("   call {s}{s}\n", .{ call_name, is_plt });
            try self.restore_call_registers(register_mark);

            // we don't support arguments
            return .{ .kind = .Void };
        },
        .Block => |as_loop| {
            const blk_start_label = try self.t_make_label(as_loop.basic_block_idx, "BLK");
            _ = try self.program_builder.append_fmt("{s}:\n", .{blk_start_label});
            try self.compile_bb(mod, proc, as_loop.basic_block_idx, true);
            const blk_end_label = try self.t_make_label(as_loop.basic_block_idx, "BLK_E");
            _ = try self.program_builder.append_fmt("{s}:\n", .{blk_end_label});
            return .{ .kind = .Void };
        },
        .ConditionalJump => |where| {
            const value = get_value(self.values, inst.operands.items[0]);
            const operand = try self.resolve_value(value, bb);
            if (operand.kind != .Register) @panic("unreachable!");
            const reg = operand.kind.Register;
            _ = try self.program_builder.append_fmt("   test %{s}, %{s}\n", .{ reg.to_string(), reg.to_string() });

            if (where == -1) {
                const cur_block_id = proc.block.basic_blocks.items[bb_idx].id;
                const loop_start_label = try self.t_make_label(cur_block_id, "BLK_E");
                _ = try self.program_builder.append_fmt("   jz {s}\n", .{loop_start_label});
            } else {
                unreachable;
            }
            return .{ .kind = .Void };
        },
        .Goto => |as_goto| {
            const cur_block = proc.block.basic_blocks.items[bb_idx];
            if (as_goto != 0) {
                @panic("trying to use Goto which is not implemented!");
            }
            const loop_start_label = try self.scratch_buffer.append_fmt("BLK{d:0>2}", .{cur_block.id});
            _ = try self.program_builder.append_fmt("   jmp {s}\n", .{loop_start_label});
            return .{ .kind = .Void };
        },

        .Void => {
            return .{ .kind = .Void };
        },
        else => |unknown| {
            std.debug.print("unknown instruction {}\n", .{unknown});
            unreachable;
        },
    }
}
pub fn t_make_label(self: *Self, id: usize, fmt: ?[]const u8) ![]const u8 {
    if (fmt) |_fmt| {
        return self.scratch_buffer.append_fmt("{s}{d:0>2}", .{ _fmt, id });
    }
    return self.scratch_buffer.append_fmt("LD{d:0>2}", .{id});
}
pub fn make_label(self: *Self, id: usize) ![]const u8 {
    return self.strings.append_fmt("LD{d:0>2}", .{id});
}
pub fn resolve_value(self: *Self, value: *const Ir.Value, bb: *const Ir.BasicBlock) !Operand {
    _ = bb;
    switch (value.type) {
        .Const => |as_const| {
            switch (as_const) {
                .Int => return .{ .kind = .{ .Immediate = as_const.Int } },
                .LiteralString => |as_str| {
                    const label = try self.make_label(as_str.id);
                    try self.used_strings.put(label, as_str.inner);
                    return .{ .kind = .{ .Memory = .{ .start = .{ .Label = label }, .offset = as_str.id, .len = as_str.inner.len } } };
                },
            }
        },
        .ValueId => |idx| {
            const parent_value = self.values.items[idx];
            // this means we using a value that does not exist
            assert(parent_value.lowered_operand_idx != std.math.maxInt(usize));
            return self.computed_values.items[parent_value.lowered_operand_idx];
        },
        .Result => {
            return self.computed_values.items[value.lowered_operand_idx];
        },
        .Void => {
            unreachable;
        },
        .Temp => {
            return self.computed_values.items[value.lowered_operand_idx];
    },
    }
}

pub fn compile_bb(self: *Self, mod: *Ir.Module, proc: *Ir.Procedure, bb_idx: usize, force_compile: bool) !void {
    const bb = &proc.block.basic_blocks.items[bb_idx];
    if (!force_compile and !bb.should_compile) return;
    for (bb.insts.items) |*inst| {
        const operand = try self.compile_inst(mod, inst, proc, bb_idx);
        try self.computed_values.append(operand);
        const idx = self.computed_values.items.len - 1;
        // assert(inst.produces != std.math.maxInt(usize)); // NOTE(shahzad): idk
        if (inst.produces == std.math.maxInt(usize)) continue;
        const value = get_value(self.values, inst.produces);
        value.lowered_operand_idx = idx;
    }
}
fn compile_proc_prologue(self: *Self, proc: *Ir.Procedure) !void {
    _ = try self.program_builder.append_fmt("{s}:\n", .{proc.name});
    _ = try self.program_builder.append_fmt("   mov %rsp, %rbp\n", .{});
    // TODO(shahzd): @bug @priority pre allocate the required size for stack
    // _ = try self.program_builder.append_fmt("   sub ${}, %rsp\n", .{proc.total_stack_var_offset});
}
fn compile_proc_epilogue(self: *Self, proc: *Ir.Procedure) !void {
    _ = proc;
    // TODO(shahzd): @bug deallocate the stack (this requires pre computed stack size)
    // TODO(shahzad): @bug @priority add return value :sob:

    _ = try self.program_builder.append_fmt("   xor %rax, %rax\n", .{});
    _ = try self.program_builder.append_fmt("   ret\n", .{});
}

fn compile_block(self: *Self, mod: *Ir.Module, proc: *Ir.Procedure, block: *Ir.Block) anyerror!void {
    for (block.basic_blocks.items, 0..) |_, idx| {
        try self.compile_bb(mod, proc, idx, false);
    }
}

pub fn compile_proc_decl(self: *Self, proc_decl: *Ir.ProcedureDecl) !void {
    std.debug.print("compiling proc_decl {s}\n", .{proc_decl.name});
    _ = try self.program_builder.append_fmt(".extern {s}\n", .{proc_decl.name});
}

pub fn compile_proc(self: *Self, mod: *Ir.Module, proc: *Ir.Procedure) !void {
    std.debug.print("compiling proc {s}\n", .{proc.name});
    try self.compile_proc_prologue(proc);
    try self.compile_block(mod, proc, &proc.block);
    try self.compile_proc_epilogue(proc);
}

pub fn compile_data_section(self: *Self) !void {
    var it = self.used_strings.iterator();
    _ = try self.program_builder.append_fmt("\n.section .rodata\n", .{});
    while (it.next()) |ent| {
        _ = try self.program_builder.append_fmt("{s}:\n", .{ent.key_ptr.*});
        _ = try self.program_builder.append_fmt(".string \"{s}\"\n", .{ent.value_ptr.*});
    }
}

pub fn compile_mod(self: *Self, mod: *Ir.Module) !void {
    _ = try self.program_builder.append_fmt(".section .text\n", .{});
    // TODO(shahzad): @bug @priority only if we have main
    _ = try self.program_builder.append_fmt(".global main\n", .{});

    for (mod.proc_decls.items) |*proc| {
        try self.compile_proc_decl(proc);
    }
    for (mod.procs.items) |*proc| {
        try self.compile_proc(mod, proc);
    }

    try self.compile_data_section();

    self.print_allocated_registers();
}
pub fn get_generated_assembly(self: *const Self) []const u8 {
    return self.program_builder.string.items;
}
