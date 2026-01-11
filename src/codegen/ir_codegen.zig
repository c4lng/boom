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
registers: u16 = 0b1111111110000000,

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

pub fn resolve_value(self: *Self, value: *const Ir.Value) Operand {
    switch (value.*) {
        .Const => |val| {
            switch (val) {
                .Int => |as_int| {
                    return .{ .Immediate = as_int };
                },
            }
        },
        .instid => |idx| {
            return self.computed_values.items[idx];
        },
    }
}
pub fn init(allocator: Allocator) !Self {
    var arena = std.heap.ArenaAllocator.init(allocator);
    const self: Self = .{ .allocator = allocator, .program_builder = .init(allocator), .scratch_buffer = .init(allocator), .string_arena = .init(arena.allocator()), .computed_values = .init(allocator) };
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
pub fn compile_inst(self: *Self, inst: *const Ir.Instruction, bb: *const Ir.BasicBlock) !Operand {
    switch (inst.type) {
        .Add => |as_add| {
            const lhs = self.resolve_value(&as_add.lhs);
            const rhs = self.resolve_value(&as_add.rhs);

            var lhs_reg: Register = undefined;

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
                    self.reg_free(reg);
                    break :blk try self.scratch_buffer.append_fmt("%{s}", .{rhs_reg.to_string()});
                },
                .Immediate => |imm_value| {
                    break :blk try self.scratch_buffer.append_fmt("${}", .{imm_value});
                },
                .Memory => unreachable,
                .Void => unreachable,
            };
            self.scratch_buffer.reset();

            _ = try self.program_builder.append_fmt("   add {s}, {s}\n", .{ rhs_compiled, lhs_compiled });

            return .{ .Register = lhs_reg };
        },
        .Return => |as_ret| {
            const operand = try self.compile_value(&as_ret, bb);
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
        else => |unknown| {
            std.debug.print("unknown instruction {}\n", .{unknown});
            unreachable;
        },
    }
}
pub fn compile_value(self: *Self, value: *const Ir.Value, bb: *const Ir.BasicBlock) !Operand {
    switch (value.*) {
        .Const => |as_const| {
            assert(as_const == .Int);
            return .{ .Immediate = as_const.Int };
        },
        .instid => |idx| {
            const inst = bb.inst.items[idx];
            // this means we using a value that does not exist
            assert(inst.lowered_operand_idx != std.math.maxInt(usize));
            return self.computed_values.items[inst.lowered_operand_idx];
        },
    }
}

pub fn compile_bb(self: *Self, bb: *const Ir.BasicBlock) !void {
    for (bb.inst.items) |*inst| {
        const operand = try self.compile_inst(inst, bb);
        try self.computed_values.append(operand);
        const idx = self.computed_values.items.len - 1;
        inst.lowered_operand_idx = idx;
    }
    std.debug.print("generated assembly", .{});
    std.debug.print("--------------------------------------------------\n", .{});
    std.debug.print("{s}\n", .{self.program_builder.string.items});
    std.debug.print("--------------------------------------------------\n", .{});
}
