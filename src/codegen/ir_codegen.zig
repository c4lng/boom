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
    pub fn as_compiled_string(self: *Operand, sb: *StringBuilder) ![]const u8 {
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
    std.log.info("allocated register {} state :{x}", .{ id, self.registers });
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
    if (src.id == dst.id) return;
    _ = try self.program_builder.append_fmt("   mov %{s}, %{s}\n", .{ src.to_string(), dst.to_string() });
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
pub fn compile_inst(self: *Self, mod: *Ir.Module, inst: *const Ir.Instruction, bb: *const Ir.BasicBlock) anyerror!Operand {
    const mark = self.scratch_buffer.mark();
    defer self.scratch_buffer.reset(mark);
    // TODO(shahzad): @bug @priority free rhs register
    switch (inst.type) {
        .BinOp => |as_binop| {
            var lhs = try self.resolve_value(get_value(self.values, inst.operands.items[0]), bb);
            var rhs = try self.resolve_value(get_value(self.values, inst.operands.items[1]), bb);

            std.debug.print("lhs = {}, rhs = {}\n", .{ lhs, rhs });
            if (as_binop != .Div and lhs.kind == .Immediate and (rhs.kind == .Register or rhs.kind == .Memory)) {
                // if one side is register make it lhs
                const temp = lhs;
                lhs = rhs;
                rhs = temp;
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
                    _ = try self.program_builder.append_fmt("   add {s}, {s}\n", .{ rhs_compiled, lhs_compiled });
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
                else => unreachable, // unimplemented
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
            for (inst.operands.items, 0..) |param_expr_idx, idx| {
                const value = get_value(self.values, param_expr_idx);
                const operand = try self.resolve_value(value, bb);

                // TODO(shahzad): @bug @priority support for args on stack
                var call_reg = LinuxCallingConvRegisters[idx];
                call_reg.width = 4; // TODO(shahzad)!!!!!: @bug are we really doing this bruh

                // TODO(shahzad): @bug @spill the registers if they are in use
                if (operand.kind != .Register or (operand.kind == .Register and operand.kind.Register.id != call_reg.id)) {
                    assert(self.is_reg_available(call_reg));
                }
                _ = self.reg_alloc2(call_reg.id, 4);

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
    }
}

pub fn compile_bb(self: *Self, mod: *Ir.Module, bb: *const Ir.BasicBlock) !void {
    for (bb.insts.items) |*inst| {
        const operand = try self.compile_inst(mod, inst, bb);
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

fn compile_block(self: *Self, mod: *Ir.Module, block: *Ir.Block) anyerror!void {
    for (block.basic_blocks.items) |*bb| {
        try self.compile_bb(mod, bb);
    }
}

pub fn compile_proc_decl(self: *Self, proc_decl: *Ir.ProcedureDecl) !void {
    std.debug.print("compiling proc_decl {s}\n", .{proc_decl.name});
    _ = try self.program_builder.append_fmt(".extern {s}\n", .{proc_decl.name});
}

pub fn compile_proc(self: *Self, mod: *Ir.Module, proc: *Ir.Procedure) !void {
    std.debug.print("compiling proc {s}\n", .{proc.name});
    try self.compile_proc_prologue(proc);
    try self.compile_block(mod, &proc.block);
    try self.compile_proc_epilogue(proc);
}

pub fn compile_data_secition(self: *Self) !void {
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

    try self.compile_data_secition();
}
pub fn get_generated_assembly(self: *const Self) []const u8 {
    return self.program_builder.string.items;
}
