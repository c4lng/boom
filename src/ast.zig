const std = @import("std");

const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const ArrayListManaged = std.array_list.Managed;

const strings = @import("./strings.zig");
const BinOp = @import("lexer.zig").BinOp;
pub const Error = error{UnexpectedToken};

pub const StringLiteral = struct {
    string: []const u8,
    label: []const u8,
};
pub const Module = struct {
    allocator: Allocator,
    context: SourceContext,
    // i could use a hashmap but no
    string_literals: ArrayListManaged(StringLiteral),
    arena: std.heap.ArenaAllocator,
    blocks: std.mem.Allocator = undefined,
    proc_decls: std.SegmentedList(ProcDecl, 8),
    proc_defs: std.SegmentedList(ProcDef, 8),
    plex_decl: ArrayListManaged(PlexDecl),
    total_branches: usize, // for label generation
    has_main_proc: bool = false, // cries in alignment :sob:
    const Self = @This();
    pub fn init(self: *Self, allocator: Allocator, context: SourceContext) void {
        self.* = .{
            .allocator = allocator,
            .proc_defs = .{},
            .proc_decls = .{},
            .plex_decl = .init(allocator),
            .context = context,
            .string_literals = .init(allocator),
            .total_branches = 0,
            .arena = .init(allocator),
        };
        self.blocks = self.arena.allocator();
    }
    pub fn get_proc_decl(self: *Self, name: []const u8) ?ProcDecl {
        var proc_decl_iter = self.proc_decls.iterator(0);
        while (proc_decl_iter.next()) |proc_decl| {
            if (std.mem.eql(u8, proc_decl.name, name)) {
                return proc_decl.*;
            }
        }
        return null;
    }
    pub fn get_proc_def(self: *Self, name: []const u8) ?ProcDef {
        var proc_def_iter = self.proc_defs.iterator(0);
        while (proc_def_iter.next()) |proc_def| {
            if (std.mem.eql(u8, proc_def.decl.name, name)) {
                return proc_def.*;
            }
        }
        return null;
    }
    pub fn get_proc(self: *Self, name: []const u8) ?ProcDecl {
        var proc_decl = self.get_proc_decl(name);
        if (proc_decl == null) {
            const proc_def = self.get_proc_def(name);
            if (proc_def == null) {
                return null;
            }
            proc_decl = proc_def.?.decl;
        }
        return proc_decl;
    }
    pub fn get_plex_decl(self: *const Self, name: []const u8) ?PlexDecl {
        for (self.plex_decl.items) |plex_decl| {
            if (std.mem.eql(u8, plex_decl.name, name)) {
                return plex_decl;
            }
        }
        return null;
    }
    pub fn find_string_literal(self: *Self, literal: []const u8) StringLiteral {
        for (self.string_literals.items) |it| {
            if (it.string.ptr == literal.ptr) {
                return it;
            }
        }
        unreachable;
    }
};
// TODO(shahzad): make this generic over unary op
pub const FieldAccess = struct {
    pub const Field = struct {
        kind: union(enum) {
            Member: []const u8,
            Deref: ExprType,
        },
        field_offset: u32,
        field_size: u32,
        next: ?*@This(),
    };
    expr: *Expression,
    field: ?*Field,
    last_field_size: u32,
};
pub const BinaryOperation = struct {
    op: BinOp,
    lhs: *Expression,
    rhs: *Expression,
    const Self = @This();
    pub fn init(allocator: Allocator, op_type: BinOp, lhs_expr: Expression, rhs_expr: Expression) !Self {
        const lhs = try allocator.create(Expression);
        const rhs = try allocator.create(Expression);
        lhs.* = lhs_expr;
        rhs.* = rhs_expr;
        return .{ .op = op_type, .lhs = lhs, .rhs = rhs };
    }
};

pub const Block = struct {
    outer: ?*Block, // NOTE(shahzad): @question should this contain outer block?
    owner_proc: ?*ProcDecl = null,
    stmts: ArrayListManaged(Statement),
    stack_vars: ArrayListManaged(StackVar), // populated in type checking phase
    stack_var_offset: usize = 0,
    const Self = @This();
    const AccessedVarType = enum {
        Argument,
        Stack,
    };
    pub fn find_stack_variable(self: *Self, var_name: []const u8) ?Variable {
        for (self.stack_vars.items) |stack_var| {
            if (std.mem.eql(u8, stack_var.decl.name, var_name)) {
                return stack_var;
            }
        }
        if (self.outer) |outer| return outer.find_stack_variable(var_name);
        assert(self.owner_proc != null);
        return null;
    }
    pub fn find_scope_variable(self: *Self, var_name: []const u8) ?Variable {
        for (self.stack_vars.items) |stack_var| {
            if (std.mem.eql(u8, stack_var.decl.name, var_name)) {
                return stack_var;
            }
        }
        return null;
    }
    pub fn find_argument(self: *Self, arg_name: []const u8) ?Variable {
        if (self.owner_proc) |proc| {
            if (proc.get_argument(arg_name)) |arg| {
                return arg;
            }
        }

        // NOTE(shahzad): we don't support anything that's global
        // for now so this not being null is a bug
        assert(self.owner_proc != null);
        return null;
    }
    pub fn find_variable(self: *Self, var_name: []const u8) ?struct { AccessedVarType, Variable } {
        if (self.find_scope_variable(var_name)) |variable| return .{ .Stack, variable };
        if (self.find_argument(var_name)) |argument| return .{ .Argument, argument };
        if (self.outer) |outer| return .{ .Stack, outer.find_stack_variable(var_name) orelse return null };
        unreachable;
    }
};
pub const ConditionalExpression = struct {
    condition: *Expression,
    expression: *Expression,
};
// @TODO(shahzad): @priority add source here so we can do error reporting

pub const Expression = union(enum) {
    pub const ProcCall = struct { name: []const u8, params: ArrayListManaged(Expression) };
    // TODO(shahzad): @feat add reference on plex_defs as r values
    pub const PlexDef = struct { name: []const u8, members: ArrayListManaged(Expression) };
    NoOp: void,
    Var: []const u8,
    LiteralInt: u64, // this should go away
    LiteralString: []const u8,
    Call: ProcCall,
    Plex: PlexDef,
    Tuple: ArrayListManaged(Expression),
    IfCondition: struct {
        if_: ConditionalExpression,
        else_expr: ?*Expression, // block is an expression
    },
    WhileLoop: ConditionalExpression,
    Block: *Block,
    BinOp: BinaryOperation,
    FieldAccess: FieldAccess,
    Reference: *Expression,
};
pub const PlexField = struct {
    name: []const u8,
    type: ExprType,
    expr: Expression,
    size: u32,
    offset: u32,
};

pub const PlexDecl = struct {
    name: []const u8,
    size: ?usize, // this is set during the typechecking
    fields: ArrayListManaged(PlexField),
    const Self = @This();
    pub fn offset_of(field: []const u8) usize {
        _ = field;
        @panic("unimplemented!");
    }
    pub fn get_field(self: *const Self, field_name: []const u8) ?PlexField {
        for (self.fields.items) |value| {
            if (std.mem.eql(u8, field_name, value.name)) {
                return value;
            }
        }
        return null;
    }
};
// @TODO(shahzad): @bug @priority add source in every field here so we can do error reporting
pub const Statement = union(enum) {
    VarDefStack: VarDecl,
    VarDefStackMut: VarDecl,
    VarDefGlobal: []u8,
    VarDefGlobalMut: []u8,
    Expr: Expression,
    Return: Expression,
};

//TODO(shahzad): @bug add fmt here
pub const ExprType = struct {
    type: []const u8, // this should be in meta but fuck it
    info: union { ptr_depth: usize, int_lit: u64 }, // contains the depth or int literal
    const Self = @This();
    pub fn default() Self {
        return .{ .type = "unknown", .info = undefined };
    }
};
pub const VarDecl = struct {
    name: []const u8,
    type: ?ExprType,
    expr: Expression,

    pub fn init(name: []const u8, @"type": []const u8, ptr_depth: usize) @This() {
        return .{ .name = name, .type = .{ .type = @"type", .info = .{ .ptr_depth = ptr_depth } }, .expr = .NoOp };
    }
};
pub const VarMetaData = struct {
    size: u31,
    is_mut: u1,
    pub fn init(size: usize, is_mut: bool) @This() {
        return .{ .size = @intCast(size), .is_mut = @bitCast(is_mut) };
    }
};
pub const Variable = struct {
    decl: VarDecl,
    meta: VarMetaData,
    offset: u32,

    const Self = @This();
    pub fn init(self: *Self, name: []const u8, offset: u32, size: usize, @"type": ?ExprType, is_mutable: bool) void {
        self.* = .{ .decl = .{ .name = name, .type = @"type", .expr = undefined }, .meta = .init(size, is_mutable), .offset = offset };
    }
    pub fn default() Self {
        return .{ .decl = .init("default", "DEFAULT_VARIABLE_OR_ARGUMENT", 0), .meta = .init(0, true) };
    }
};
pub const StackVar = Variable;
pub const Argument = Variable;
// TODO(shahzad): @refactor @priority size should be the part of ExprType
pub const ProcDecl = struct {
    name: []const u8,
    args_list: ArrayListManaged(Argument),
    return_type: ExprType,
    return_size: usize,
    const Self = @This();
    pub fn init(name: []const u8, args: ArrayListManaged(Argument), return_type: []const u8, ptr_depth: usize) Self {
        return .{
            .name = name,
            .args_list = args,
            .return_type = .{
                .type = return_type,
                .info = .{ .ptr_depth = ptr_depth },
            },
            .return_size = 0,
        };
    }
    pub fn get_required_params(self: *const Self) ArrayListManaged(Argument) {
        // @TODO(shahzad): @bug @scope impl this function frfr
        return self.args_list;
    }
    pub fn get_argument(self: *const Self, arg_name: []const u8) ?Argument {
        // TODO(shahzad): @perf this is ass
        for (self.args_list.items) |it| {
            if (std.mem.eql(u8, it.decl.name, arg_name)) {
                return it;
            }
        }
        return null;
    }
};

pub const ProcDef = struct {
    decl: ProcDecl,
    total_stack_var_offset: usize = 0,
    block: *Block,
    const Self = @This();

    pub fn init(decl: ProcDecl, block: *Block) Self {
        return .{ .decl = decl, .block = block };
    }
    pub fn get_variable(self: *Self, var_name: []const u8) ?StackVar {
        return self.decl.get_argument(var_name) orelse self.block.find_scope_variable(var_name);
    }
};

pub const SourceContext = struct {
    filename: []const u8,
    file: []const u8,
    const Self = @This();
    pub fn init(filename: []const u8, file: []const u8) SourceContext {
        return .{
            .filename = filename,
            .file = file,
        };
    }
    pub fn count_lines_until_source_found(self: Self, source: []const u8) u32 {
        const start_ptr = self.file;

        assert(@intFromPtr(source.ptr) >= @intFromPtr(start_ptr.ptr) and source.len <= start_ptr.len);
        const buf = start_ptr[0 .. source.ptr - start_ptr.ptr];
        var count: u32 = 1;
        for (buf) |val| {
            switch (val) {
                '\r', '\n' => {
                    count += 1;
                },
                else => {},
            }
        }
        return count;
    }
    pub fn get_line_start_for_source(self: Self, source: []const u8) []const u8 {
        const start_ptr = self.file;
        assert(@intFromPtr(source.ptr) >= @intFromPtr(start_ptr.ptr) and source.len <= start_ptr.len);
        const buf = start_ptr[0 .. source.ptr - start_ptr.ptr];
        const line: []const u8 = blk: {
            var idx = buf.len - 1;
            while (idx >= 0) : (idx -= 1) {
                if (idx == 0) return strings.get_line(start_ptr[0..]);
                switch (buf[idx]) {
                    '\r', '\n' => {
                        const line_start_idx = if (idx + 1 < buf.len) idx + 1 else buf.len;
                        break :blk strings.get_line(start_ptr[line_start_idx..]);
                    },
                    else => {},
                }
            }

            break :blk strings.get_line(start_ptr[0..]);
        };

        return line;
    }
    pub fn get_loc(self: Self, source: []const u8) struct { u32, []const u8 } {
        const n_lines = self.count_lines_until_source_found(source);
        const line = self.get_line_start_for_source(source);
        return .{ n_lines, line };
    }

    // this function takes a pointer inside file buffer and prints the line (with
    // the source highlighted? i guess idk tho)
    pub fn print_loc(self: Self, source: []const u8) void {
        const n_lines: u32 = self.count_lines_until_source_found(source);
        const line = self.get_line_start_for_source(source);
        std.log.debug("{s}:{}: {s}", .{ self.filename, n_lines, line });
    }
};
