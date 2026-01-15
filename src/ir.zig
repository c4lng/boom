const std = @import("std");
const Allocator = std.mem.Allocator;
const ArrayListManaged = std.array_list.Managed;
const assert = std.debug.assert;

const Ast = @import("ast.zig");
const Lexer = @import("lexer.zig");
const Self = @This();

allocator: Allocator,
values: ArrayListManaged(Value),

symbol_table_stack: SymbolTableStack,
peephole_enabled: bool = true,

const SymbolTableStack = struct {
    allocator: Allocator,
    inner: ArrayListManaged(SymbolTable),
    pub fn init(allocator: Allocator) SymbolTableStack {
        return .{ .allocator = allocator, .inner = .init(allocator) };
    }

    pub fn print_sym_table_stack(
        self: *SymbolTableStack,
        ctx: Self,
    ) void {
        var last_idx: isize = @intCast(self.inner.items.len - 1);
        while (last_idx >= 0) : (last_idx -= 1) {
            std.log.debug("----------start---------------", .{});
            print_symbol_table(ctx, self.inner.items[@intCast(last_idx)]);
            std.log.debug("===========end================", .{});
            std.log.debug("", .{});
        }
    }
    pub fn get_sym_value_idx(self: *SymbolTableStack, sym_name: []const u8) ?usize {
        var last_idx: isize = @intCast(self.inner.items.len - 1);
        var value_idx: ?usize = null;
        while (last_idx >= 0) : (last_idx -= 1) {
            const sym_table = self.inner.items[@intCast(last_idx)];
            value_idx = sym_table.get(sym_name) orelse {
                continue;
            };
            break;
        }
        return value_idx;
    }
    pub fn append_sym(self: *SymbolTableStack, sym_name: []const u8, value_idx: usize) !void {
        var last = &self.inner.items[self.inner.items.len - 1];
        const entry = try last.getOrPut(sym_name);
        assert(entry.found_existing != true); // bug in type checking
        entry.value_ptr.* = value_idx;
    }
    pub fn set_sym(self: *SymbolTableStack, sym_name: []const u8, value_idx: usize) !void {
        var last_idx: isize = @intCast(self.inner.items.len - 1);
        while (last_idx >= 0) : (last_idx -= 1) {
            const sym_table = self.inner.items[@intCast(last_idx)];
            const prev_value_idx = sym_table.getPtr(sym_name) orelse {
                continue;
            };
            prev_value_idx.* = value_idx;
            return;
        }
        try self.append_sym(sym_name, value_idx);
    }

    pub fn new_frame(self: *SymbolTableStack) !void {
        try self.inner.append(.init(self.allocator));
    }
};

const SymbolTable = std.StringHashMap(usize);
pub fn print_symbol_table(ctx: Self, sym_table: SymbolTable) void {
    var iter = sym_table.iterator();
    while (iter.next()) |ent| {
        const value = get_value(ctx.values, ent.value_ptr.*);
        std.log.debug("sym_table entry : {s} -> {}\n", .{ ent.key_ptr.*, value });
    }
}

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
    insts: ArrayListManaged(Instruction),
    pub fn init(allocator: Allocator) BasicBlock {
        return .{ .insts = .init(allocator) };
    }
    pub fn optimize(bb: *BasicBlock, ctx: *Self) !void {
        for (bb.insts.items) |*inst| {
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
    return .{
        .allocator = allocator,
        .values = .init(allocator),
        .symbol_table_stack = .init(allocator),
    };
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
        .Var => |as_var| {
            const var_as_value = self.symbol_table_stack.get_sym_value_idx(as_var);
            if (var_as_value == null) {
                std.log.err("symbol '{s}' not present in symbol table", .{as_var});
                self.symbol_table_stack.print_sym_table_stack(self.*);
                @panic("symbol not present in the table!");
            }
            return var_as_value.?;
        },
        else => unreachable,
    }
    unreachable;
}

pub fn parse_block(self: *Self, block: *const Ast.Block) anyerror!BasicBlock {
    var basic_block: BasicBlock = .init(self.allocator);
    for (block.stmts.items) |stmt| {
        switch (stmt) {
            .Expr => {},
            .Return => |as_ret| {
                const value_id = try self.parse_expr(&as_ret, &basic_block.insts);
                try basic_block.insts.append(.{ .type = .{ .Return = value_id } });
            },
            .VarDefStack => |as_var_def| {
                const var_name = as_var_def.name;
                const value_id = if (as_var_def.expr != .NoOp)
                    try self.parse_expr(&as_var_def.expr, &basic_block.insts)
                else blk: {
                    try self.values.append(.{ .type = .Result });
                    break :blk self.values.items.len - 1;
                };
                try self.symbol_table_stack.set_sym(var_name, value_id);
            },
            else => unreachable,
        }
    }
    return basic_block;
}

pub fn from_proc(self: *Self, proc: *const Ast.ProcDef) !BasicBlock {
    try self.symbol_table_stack.new_frame();
    var bb = try self.parse_block(proc.block);
    if (self.peephole_enabled) try bb.optimize(self);
    return bb;
}
