const std = @import("std");
const Allocator = std.mem.Allocator;
const ArrayListManaged = std.array_list.Managed;
const assert = std.debug.assert;

const Ast = @import("ast.zig");
const Lexer = @import("lexer.zig");

pub const Module = @This();

values: ArrayListManaged(Value) = undefined,
procs: ArrayListManaged(Procedure) = undefined,
global_symbols: SymbolTable = undefined,
allocator: Allocator,

pub fn init(allocator: Allocator) Module {
    return .{
        .allocator = allocator,
        .values = .init(allocator),
        .procs = .init(allocator),
        .global_symbols = .init(allocator),
    };
}

pub const Options = struct {
    enable_peephole: bool = false,
};
pub const Procedure = struct {
    name: []const u8,
    symbol_table_stack: SymbolTableStack,
    block: Block,
    mod: *Module,
    pub fn init(module: *Module, name: []const u8) @This() {
        return .{
            .name = name,
            .symbol_table_stack = .init(module.allocator),
            .block = .init(module.allocator),
            .mod = module,
        };
    }
};

const SymbolTableStack = struct {
    allocator: Allocator,
    inner: ArrayListManaged(SymbolTable),
    pub fn init(allocator: Allocator) SymbolTableStack {
        return .{ .allocator = allocator, .inner = .init(allocator) };
    }

    pub fn print_sym_table_stack(
        self: *SymbolTableStack,
        module: Module,
    ) void {
        var last_idx: isize = @intCast(self.inner.items.len - 1);
        while (last_idx >= 0) : (last_idx -= 1) {
            std.log.debug("----------start---------------", .{});
            print_symbol_table(module, self.inner.items[@intCast(last_idx)]);
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
pub fn print_symbol_table(mod: Module, sym_table: SymbolTable) void {
    var iter = sym_table.iterator();
    while (iter.next()) |ent| {
        const value = get_value(mod.values, ent.value_ptr.*);
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

    pub fn peeophole(self: Value, mod: *Module, bb: *BasicBlock) Value {
        _ = mod;
        _ = bb;
        return self;
    }
};

pub fn get_value(values: ArrayListManaged(Value), idx: usize) *Value {
    return &values.items[idx];
}

// TODO(shahzad): @scope this should hold the type that ts resolves to
pub const Instruction = struct {
    pub const Type = union(enum) {
        BinOp: Lexer.Operators,
        Value,
        Return,
        Void, // chat should we generate no op?
    };
    type: Type,
    operands: ArrayListManaged(usize),
    produces: usize = std.math.maxInt(usize),

    pub fn init(allocator: Allocator, inst_type: Instruction.Type, produces: ?usize, operands: []const usize) !@This() {
        var ops: ArrayListManaged(usize) = .init(allocator);

        try ops.appendSlice(operands);
        return .{
            .type = inst_type,
            .operands = ops,
            .produces = produces orelse std.math.maxInt(usize),
        };
    }
    pub fn peephole(self: *Instruction, mod: *Module, bb: *BasicBlock) !void {
        _ = bb;
        switch (self.type) {
            .BinOp => |as_binop| {
                const lhs = get_value(mod.values, self.operands.items[0]);
                const rhs = get_value(mod.values, self.operands.items[1]);

                if (lhs.type == .Const and rhs.type == .Const) {
                    self.type = .Void;

                    const lhs_as_const = lhs.type.Const.Int;
                    const rhs_as_const = rhs.type.Const.Int;

                    const result = switch (as_binop) {
                        .Add => @addWithOverflow(lhs_as_const, rhs_as_const).@"0",
                        .Sub => @subWithOverflow(lhs_as_const, rhs_as_const).@"0",
                        .Mul => @mulWithOverflow(lhs_as_const, rhs_as_const).@"0",
                        .Div => @divTrunc(lhs_as_const, rhs_as_const),
                        else => unreachable, // unimplemented
                    };

                    const value = get_value(mod.values, self.produces);
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
    pub fn optimize(bb: *BasicBlock, mod: *Module) !void {
        for (bb.insts.items) |*inst| {
            try inst.peephole(mod, bb);
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
pub fn parse_expr(mod: *Module, proc: *Procedure, expr: *const Ast.Expression, insts: *ArrayListManaged(Instruction)) anyerror!usize {
    switch (expr.*) {
        .BinOp => |as_binop| {
            return try mod.parse_binop(proc, &as_binop, insts);
        },
        .LiteralInt => |as_literal| {
            try mod.values.append(.{ .type = .{ .Const = .{ .Int = as_literal } } });
            return mod.values.items.len - 1;
        },
        .Var => |as_var| {
            const var_as_value = proc.symbol_table_stack.get_sym_value_idx(as_var);
            if (var_as_value == null) {
                std.log.err("symbol '{s}' not present in symbol table", .{as_var});
                proc.symbol_table_stack.print_sym_table_stack(mod.*);
                @panic("symbol not present in the table!");
            }
            return var_as_value.?;
        },
        else => unreachable,
    }
    unreachable;
}
pub fn parse_binop(mod: *Module, proc: *Procedure, bin_op: *const Ast.BinaryOperation, insts: *ArrayListManaged(Instruction)) anyerror!usize {
    const lhs = try mod.parse_expr(proc, bin_op.lhs, insts);

    const rhs = try mod.parse_expr(proc, bin_op.rhs, insts);

    try mod.values.append(.{ .type = .Result });
    const dest = mod.values.items.len - 1;
    try insts.append(try .init(proc.mod.allocator, .{ .BinOp = bin_op.op }, dest, &[_]usize{ lhs, rhs }));
    return dest;
}
pub fn parse_block(mod: *Module, proc: *Procedure, ast_block: *const Ast.Block, ir_block: *Block) anyerror!void {
    var basic_block: *BasicBlock = try ir_block.basic_blocks.addOne();
    basic_block.* = .init(mod.allocator);
    for (ast_block.stmts.items) |stmt| {
        switch (stmt) {
            .Expr => {},
            .Return => |as_ret| {
                const value_id = try mod.parse_expr(proc, &as_ret, &basic_block.insts);

                try basic_block.insts.append(try .init(mod.allocator, .Return, null, &[_]usize{value_id}));
            },
            .VarDefStack => |as_var_def| {
                const var_name = as_var_def.name;
                const value_id = if (as_var_def.expr != .NoOp)
                    try mod.parse_expr(proc, &as_var_def.expr, &basic_block.insts)
                else blk: {
                    try mod.values.append(.{ .type = .Result });
                    break :blk mod.values.items.len - 1;
                };
                try proc.symbol_table_stack.set_sym(var_name, value_id);
            },
            else => unreachable,
        }
    }
}

pub fn compile_proc(mod: *Module, proc_def: *const Ast.ProcDef, opts: Options) !Procedure {
    var proc: Procedure = .init(mod, proc_def.decl.name);
    try proc.symbol_table_stack.new_frame();
    // TODO(shahzad): @bug @scope we have to have more than one basic block
    try mod.parse_block(&proc, proc_def.block, &proc.block);

    if (opts.enable_peephole) {
        for (proc.block.basic_blocks.items) |*bb| try bb.*.optimize(mod);
    }
    return proc;
}

pub fn compile_mod(allocator: Allocator, module: *Ast.Module, opts: Options) !Module {
    var mod: Module = .init(allocator);
    var iter = module.proc_defs.iterator(0);
    while (iter.next()) |it| {
        const proc = try mod.compile_proc(it, opts);
        try mod.procs.append(proc);
    }
    return mod;
}
