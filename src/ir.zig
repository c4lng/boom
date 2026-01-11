const std = @import("std");
const Allocator = std.mem.Allocator;
const ArrayListManaged = std.array_list.Managed;
const assert = std.debug.assert;

const Ast = @import("ast.zig");
const Self = @This();

allocator: Allocator,

const Data = union(enum) {
    Int: usize,
};
pub const Value = union(enum) {
    Const: Data,
    instid: usize,
};

// TODO(shahzad): @scope this should hold the type that ts resolves to
pub const Instruction = struct {
    type: union(enum) {
        FunctionDef: struct { label: []const u8 },
        Add: struct { lhs: Value, rhs: Value },
        DataNode: *Instruction,
        Return: Value,
    },
    lowered_operand_idx: usize = std.math.maxInt(usize), // filled in codegen phase
};
pub const BasicBlock = struct {
    inst: ArrayListManaged(Instruction),
    pub fn init(allocator: Allocator) BasicBlock {
        return .{ .inst = .init(allocator) };
    }
};
pub const Block = struct {
    basic_blocks: ArrayListManaged(BasicBlock),
    pub fn init(allocator: Allocator) Block {
        return .{ .basic_blocks = .init(allocator) };
    }
};

pub fn init(allocator: Allocator) Self {
    return .{ .allocator = allocator };
}

pub fn parse_binop(self: Self, bin_op: *const Ast.BinaryOperation, insts: *ArrayListManaged(Instruction)) !Value {
    _ = self;
    assert(bin_op.lhs.* == .LiteralInt);
    assert(bin_op.rhs.* == .LiteralInt); // we only support int literal for now
    const lhs_as_inst: Value = .{ .Const = .{ .Int = bin_op.lhs.LiteralInt } };
    const rhs_as_inst: Value = .{ .Const = .{ .Int = bin_op.rhs.LiteralInt } };
    try insts.append(.{ .type = .{ .Add = .{ .lhs = lhs_as_inst, .rhs = rhs_as_inst } } });
    return .{ .instid = insts.items.len - 1 };
}
pub fn parse_expr(self: Self, expr: *const Ast.Expression, insts: *ArrayListManaged(Instruction)) !Value {
    switch (expr.*) {
        .BinOp => |as_binop| {
            return try self.parse_binop(&as_binop, insts);
        },
        .LiteralInt => |as_literal| {
            return .{ .Const = .{ .Int = as_literal } };
        },
        else => unreachable,
    }
    return undefined;
}

pub fn parse_block(self: Self, block: *const Ast.Block) !BasicBlock {
    var basic_block: BasicBlock = .init(self.allocator);
    for (block.stmts.items) |stmt| {
        switch (stmt) {
            .Expr => {},
            .Return => |as_ret| {
                const ret_expr = try self.parse_expr(&as_ret, &basic_block.inst);
                try basic_block.inst.append(.{ .type = .{ .Return = ret_expr } });
            },
            else => unreachable,
        }
    }
    return basic_block;
}
pub fn from_proc(self: *Self, proc: *const Ast.ProcDef) !BasicBlock {
    return self.parse_block(proc.block);
}
