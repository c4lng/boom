const std = @import("std");
const Allocator = std.mem.Allocator;
const ArrayListManaged = std.array_list.Managed;
const assert = std.debug.assert;

const Ast = @import("../ast.zig");
const Ir = @import("../ir.zig");
const StringBuilder = @import("../string_builder.zig");
const Self = @This();

allocator: Allocator,
program_builder: StringBuilder,
scratch_buffer: StringBuilder,
string_arena: StringBuilder,
computed_values: ArrayListManaged(Operand),
values: ArrayListManaged(Ir.Value),
registers: u16 = 0b1111111110000000,

// TODO(shahzad): @scope duplication put this in utils or smth
const get_value = Ir.get_value;

pub const Register = struct {
    pub const Id = enum(u8) {
        // we only give a shit about callee saved register
        // that's why the order is like that
        // zig fmt: off
        A    =  0,   C    =  1,   D    =  2,   SI   =  3,   DI  =  4,
        r8   =  5,   r9   =  6,   r10  =  7,   r11  =  8,   B   =  9,
        r12  =  10,  r13  =  11,  r14  =  12,  r15  =  13,
        // zig fmt: on
        pub inline fn to_int(id: Id) u8 {
            return @intFromEnum(id);
        }
    };
    id: Id,
    width: u8 = 69,
    pub fn to_string(self: @This()) [4]u8 {
        var buf = [4]u8{ 0, 0, 0, 0 };
        var builder = StringBuilder.Fixed.init(&buf);
        var prefix = switch (self.width) {
            inline 1, 2 => "",
            inline 4 => "e",
            inline 8 => "r",
            inline else => |value| {
                std.log.err("value is this {}\n", .{value});
                unreachable;
            },
        };
        var postfix = switch (self.width) {
            inline 0 => "", // just here to make zig compiler stfu and make it compile
            inline 1 => "l",
            inline 2, 4, 8 => "x",
            inline else => unreachable,
        };
        const middle = switch (self.id) {
            inline .A => "a",
            inline .B => "b",
            inline .C => "c",
            inline .D => "d",
            inline .DI => "di",
            inline .SI => "si",
            inline else => |value| blk: {
                prefix = "";
                postfix = "";
                break :blk @tagName(value);
            },
        };
        _ = builder.print_fmt("{s}{s}{s}", .{ prefix, middle, postfix }) catch unreachable;
        return buf;
    }
};

const LinuxCallingConvRegisters = [_][]const u8{
    "edi", "rdi",
    "esi", "rsi",
    "edx", "rdx",
    "ecx", "rcx",
    "r8d", "r8",
    "r9d", "r9",
};

pub const Operand = union(enum) {
    Immediate: u64,
    Register: Register,
    Memory: void,
    Void: void,
};

pub fn ensure_reg(self: *Self, operand: Operand) !Register {
    switch (operand) {
        .Register => |as_reg| return as_reg,
        .Immediate => |imm_value| {
            const reg = self.reg_alloc();
            try self.load_imm_to_reg(imm_value, &reg.to_string());
            return reg;
        },
        .Memory => unreachable,
        .Void => unreachable,
    }
}
pub fn reg_alloc(self: *Self) Register {
    const idx = @clz(self.registers);
    assert(idx <= 10); // we have allocated too much and went to callee Register's boundary
    self.registers ^= @as(u16, @intCast(1)) << @intCast(15 - idx);
    return .{ .id = @enumFromInt(idx) };
}
pub fn is_reg_available(self: *Self, reg: Register) bool {
    const bit_idx: u4 = 15 - @as(u4, @intCast(reg.id.to_int()));
    return (self.registers >> (bit_idx)) & 1 == 1;
}
pub fn reg_free(self: *Self, reg: Register) void {
    const idx: u8 = reg.id.to_int();
    const bit_idx: u4 = 15 - @as(u4, @intCast(idx));
    assert(!self.is_reg_available(reg));
    self.registers ^= @as(u16, @intCast(1)) << @intCast(bit_idx);
}

pub fn init(allocator: Allocator, values: ArrayListManaged(Ir.Value)) !Self {
    var arena = std.heap.ArenaAllocator.init(allocator);
    const self: Self = .{
        .allocator = allocator,
        .program_builder = .init(allocator),
        .scratch_buffer = .init(allocator),
        .string_arena = .init(arena.allocator()),
        .computed_values = .init(allocator),
        .values = values,
    };
    return self;
}

// TODO(shahzad): @scope @priority register should be a structure
pub fn load_imm_to_reg(self: *Self, imm_value: u64, reg: []const u8) !void {
    _ = try self.program_builder.append_fmt("   mov ${}, %{s}\n", .{ imm_value, reg });
}
pub fn mov_reg_to_reg(self: *Self, src: Register, dst: Register) !void {
    if (src.id == dst.id) return;
    _ = try self.program_builder.append_fmt("   mov %{s}, %{s}\n", .{ src.to_string(), dst.to_string() });
}
pub fn compile_inst(self: *Self, inst: *const Ir.Instruction, bb: *const Ir.BasicBlock) anyerror!Operand {
    // TODO(shahzad): @bug @priority free rhs register
    switch (inst.type) {
        .BinOp => |as_binop| {
            var lhs = try self.resolve_value(get_value(self.values, as_binop.lhs), bb);
            var rhs = try self.resolve_value(get_value(self.values, as_binop.rhs), bb);

            var lhs_reg: Register = undefined;

            std.debug.print("lhs = {}, rhs = {}\n", .{ lhs, rhs });
            if (lhs == .Immediate and (rhs == .Register or rhs == .Memory)) {
                // if one side is register make it lhs
                const temp = lhs;
                lhs = rhs;
                rhs = temp;
            }
            const lhs_compiled = blk: switch (lhs) {
                .Register => |reg| {
                    lhs_reg = reg;
                    // NOTE(shahzad): @bug @priority hardcoded
                    lhs_reg.width = 4;
                    break :blk try self.scratch_buffer.append_fmt("%{s}", .{lhs_reg.to_string()});
                },
                .Immediate => |imm_value| {
                    lhs_reg = self.reg_alloc();
                    // NOTE(shahzad): @bug @priority hardcoded
                    lhs_reg.width = 4;
                    const reg_as_str = lhs_reg.to_string();
                    try self.load_imm_to_reg(imm_value, &reg_as_str);
                    break :blk try self.scratch_buffer.append_fmt("%{s}", .{reg_as_str});
                },
                .Memory => unreachable,
                .Void => unreachable,
            };
            const rhs_compiled = blk: switch (rhs) {
                .Register => |reg| {
                    var rhs_reg = reg;
                    // NOTE(shahzad): @bug @priority hardcoded
                    rhs_reg.width = 4;
                    break :blk try self.scratch_buffer.append_fmt("%{s}", .{rhs_reg.to_string()});
                },
                .Immediate => |imm_value| {
                    break :blk try self.scratch_buffer.append_fmt("${}", .{imm_value});
                },
                .Memory => unreachable,
                .Void => unreachable,
            };
            switch (as_binop.Op) {
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

                    const a_reg: Register = .{ .width = 8, .id = .A };
                    var tmp_ax_hold_reg: ?Register = null;
                    const rhs_reg = try self.ensure_reg(rhs);
                    if (lhs.Register.id != .A) { // lhs will always be a register
                        if (self.is_reg_available(a_reg)) {
                            try self.mov_reg_to_reg(lhs.Register, .{ .width = 8, .id = .A });
                            self.reg_free(lhs_reg);
                            lhs_reg.id = .A;
                        } else {
                            tmp_ax_hold_reg = self.reg_alloc();

                            // register is not available so we shuffle
                            try self.mov_reg_to_reg(a_reg, tmp_ax_hold_reg.?);
                            try self.mov_reg_to_reg(lhs.Register, .{ .width = 8, .id = .A });
                        }
                    }

                    _ = try self.program_builder.append_fmt("   idiv %{s}\n", .{rhs_reg.to_string()});
                    try self.mov_reg_to_reg(a_reg, lhs_reg);

                    if (tmp_ax_hold_reg) |tmp_reg|{
                        try self.mov_reg_to_reg(tmp_reg, a_reg);
                        self.reg_free(tmp_reg);
                    }

                    self.reg_free(rhs_reg);
                },
                else => unreachable, // unimplemented
            }
            self.scratch_buffer.reset();

            var dst = get_value(self.values, inst.produces);
            _ = try self.computed_values.append(.{ .Register = lhs_reg });
            dst.lowered_operand_idx = self.computed_values.items.len - 1;
            return .{ .Register = lhs_reg };
        },
        .Return => |as_ret_idx| {
            const value = get_value(self.values, as_ret_idx);
            const operand = try self.resolve_value(value, bb);
            switch (operand) {
                .Immediate => |imm_value| {
                    if (!self.is_reg_available(.{ .id = .A })) {
                        @panic("codegen violation: RAX is in use!");
                    }
                    const reg: Register = .{ .id = .A, .width = 8 };
                    const reg_as_str = reg.to_string();
                    try self.load_imm_to_reg(imm_value, &reg_as_str);
                    _ = try self.program_builder.append_fmt("   ret\n", .{});
                    return .Void;
                },
                .Register => |reg| {
                    try self.mov_reg_to_reg(reg, .{ .id = .A, .width = 8 });
                    _ = try self.program_builder.append_fmt("   ret\n", .{});
                    return .Void;
                },
                .Memory => unreachable,
                .Void => unreachable,
            }
        },
        .Void => {
            return .Void;
        },
        else => |unknown| {
            std.debug.print("unknown instruction {}\n", .{unknown});
            unreachable;
        },
    }
}
pub fn resolve_value(self: *Self, value: *const Ir.Value, bb: *const Ir.BasicBlock) !Operand {
    _ = bb;
    switch (value.type) {
        .Const => |as_const| {
            assert(as_const == .Int);
            return .{ .Immediate = as_const.Int };
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
    }
}

pub fn compile_bb(self: *Self, bb: *const Ir.BasicBlock) !void {
    for (bb.insts.items) |*inst| {
        const operand = try self.compile_inst(inst, bb);
        try self.computed_values.append(operand);
        const idx = self.computed_values.items.len - 1;
        // assert(inst.produces != std.math.maxInt(usize)); // NOTE(shahzad): idk
        if (inst.produces == std.math.maxInt(usize)) continue;
        const value = get_value(self.values, inst.produces);
        value.lowered_operand_idx = idx;
    }
    std.debug.print("generated assembly", .{});
    std.debug.print("--------------------------------------------------\n", .{});
    std.debug.print("{s}\n", .{self.program_builder.string.items});
    std.debug.print("--------------------------------------------------\n", .{});
}
