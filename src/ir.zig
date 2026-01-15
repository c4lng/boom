const std = @import("std");
const Allocator = std.mem.Allocator;
const ArrayListManaged = std.array_list.Managed;
const assert = std.debug.assert;

const Ast = @import("ast.zig");
const Lexer = @import("lexer.zig");
const Self = @This();

allocator: Allocator,
values: ArrayListManaged(Value),

const Data = union(enum) {
    Int: usize,
};
pub const Value = struct {
    // NOTE(shahzad):  ValueId means that this depends on some other value
    // so during codegen we should first go to that value and then take
    // the operand from there,
    // Result means that this produces a value so the lowered_operand_idx MUST
    // be set to some valid index in the computed value array
    type: union(enum) {
        Const: Data,
        ValueId: usize,
        Result: void,
    },
    lowered_operand_idx: usize = std.math.maxInt(usize), // filled in codegen phase

    pub fn peeophole(self: Value, ctx: *Self, bb: *BasicBlock) Value {
        _ = ctx;
        _ = bb;
        return self;
    }
};

pub fn get_value(values: ArrayListManaged(Value), idx: usize) *Value {
    return &values.items[idx];
}

// TODO(shahzad): @scope this should hold the type that ts resolves to
pub const Instruction = struct {
    type: union(enum) {
        FunctionDef: struct { label: []const u8 },
        // stores index in value array
        BinOp: struct { Op: Lexer.Operators, lhs: usize, rhs: usize },
        Value: usize,
        Return: usize,
        Void: void, // chat should we generate no op?
    },
    produces: usize = std.math.maxInt(usize),
    pub fn peephole(self: *Instruction, ctx: *Self, bb: *BasicBlock) !void {
        _ = bb;
        switch (self.type) {
            .BinOp => |as_binop| {
                const lhs = get_value(ctx.values, as_binop.lhs);
                const rhs = get_value(ctx.values, as_binop.rhs);

                if (lhs.type == .Const and rhs.type == .Const) {
                    self.type = .Void;

                    const lhs_as_const = lhs.type.Const.Int;
                    const rhs_as_const = rhs.type.Const.Int;

                    const result = switch (as_binop.Op) {
                        .Add => @addWithOverflow(lhs_as_const, rhs_as_const).@"0",
                        .Sub => @subWithOverflow(lhs_as_const, rhs_as_const).@"0",
                        .Mul => @mulWithOverflow(lhs_as_const, rhs_as_const).@"0",
                        .Div => @divTrunc(lhs_as_const, rhs_as_const),
                        else => unreachable, // unimplemented
                    };

                    const value = get_value(ctx.values, self.produces);
                    value.* = .{
                        .type = .{ .Const = .{ .Int = result } },
                    };

                    self.type = .Void;
                    return;
                }
                unreachable;
            },
            .Return => {}, // we can't peephole return bruh
            else => unreachable,
        }
    }
};

pub const BasicBlock = struct {
    inst: ArrayListManaged(Instruction),
    pub fn init(allocator: Allocator) BasicBlock {
        return .{ .inst = .init(allocator) };
    }
    pub fn optimize(bb: *BasicBlock, ctx: *Self) !void {
        for (bb.inst.items) |*inst| {
            try inst.peephole(ctx, bb);
        }
        // TODO(shahzad): @fixme remove all void instructions
    }
};
pub const Block = struct {
    basic_blocks: ArrayListManaged(BasicBlock),
    pub fn init(allocator: Allocator) Block {
        return .{ .basic_blocks = .init(allocator) };
    }
};

pub fn init(allocator: Allocator) Self {
    return .{ .allocator = allocator, .values = .init(allocator) };
}

pub fn parse_binop(self: *Self, bin_op: *const Ast.BinaryOperation, insts: *ArrayListManaged(Instruction)) anyerror!usize {
    const lhs = try self.parse_expr(bin_op.lhs, insts);
    const rhs = try self.parse_expr(bin_op.rhs, insts);

    try self.values.append(.{ .type = .Result });
    const dest = self.values.items.len - 1;
    try insts.append(.{ .type = .{ .BinOp = .{ .Op = bin_op.op, .lhs = lhs, .rhs = rhs } }, .produces = dest });
    return dest;
}
pub fn parse_expr(self: *Self, expr: *const Ast.Expression, insts: *ArrayListManaged(Instruction)) anyerror!usize {
    switch (expr.*) {
        .BinOp => |as_binop| {
            return try self.parse_binop(&as_binop, insts);
        },
        .LiteralInt => |as_literal| {
            try self.values.append(.{ .type = .{ .Const = .{ .Int = as_literal } } });
            return self.values.items.len - 1;
        },
        else => unreachable,
    }
    unreachable;
}

pub fn parse_block(self: *Self, block: *const Ast.Block) !BasicBlock {
    var basic_block: BasicBlock = .init(self.allocator);
    for (block.stmts.items) |stmt| {
        switch (stmt) {
            .Expr => {},
            .Return => |as_ret| {
                const value_id = try self.parse_expr(&as_ret, &basic_block.inst);
                try basic_block.inst.append(.{ .type = .{ .Return = value_id } });
            },
            .VarDefStack => {},
            else => unreachable,
        }
    }
    return basic_block;
}

pub fn from_proc(self: *Self, proc: *const Ast.ProcDef) !BasicBlock {
    var bb = try self.parse_block(proc.block);
    try bb.optimize(self);
    return bb;
}
