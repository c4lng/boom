const std = @import("std");
const Allocator = std.mem.Allocator;
const Ast = @import("ast.zig");
const assert = std.debug.assert;
const SourceContext = Ast.SourceContext;

allocator: Allocator,
context: SourceContext,
const Self = @This();

const Error = error{
    TypeNotFound,
    VariableRedefinition,
    VariableNotDefined,
    ProcedureNotDefined,
    PlexNotDefined,
    UndefinedPlexField,
    ProcedureCallArgsMismatch,
    TypeMisMatch,
    RecursiveDeclaration,
};

//TODO(shahzad): add a formatter here
// NOTE(shahzad): we use this as IntLiteralType ++ int_literal
const IntLiteralType = "\x00intlit";

const PrimitiveTypes = [_]struct { []const u8, u32 }{
    .{ "s8", 1 },
    .{ "x8", 1 },

    .{ "s16", 2 },
    .{ "x16", 2 },

    .{ "s32", 4 },
    .{ "x32", 4 },

    .{ "s64", 8 },
    .{ "x64", 8 },

    .{ "bool", 1 },
    .{ "void", 0 },
};

pub fn init(allocator: Allocator, context: SourceContext) Self {
    return .{ .context = context, .allocator = allocator };
}
pub fn get_size_for_user_defined_type(module: *const Ast.Module, @"type": Ast.ExprType) Self.Error!?usize {
    const plex_decl = module.get_plex_decl(@"type".type);
    if (plex_decl) |decl| {
        if (@"type".info.ptr_depth > 0) return 8 else return decl.size;
    }

    return Error.TypeNotFound;
}
pub fn get_size_for_primitive_type(@"type": Ast.ExprType) Self.Error!usize {
    if (std.mem.eql(u8, @"type".type, IntLiteralType)) {
        return @intCast(get_size_of_int_literal(@"type".info.int_lit));
    }
    for (PrimitiveTypes) |it| {
        if (std.mem.eql(u8, it[0], @"type".type)) {
            if (@"type".info.ptr_depth > 0) return 8;
            return it[1];
        }
    }
    return Error.TypeNotFound;
}
pub fn is_type_int_lit(@"type": Ast.ExprType) bool {
    return std.mem.eql(u8, @"type".type, IntLiteralType);
}
pub fn get_size_of_int_literal(int_literal: u64) u32 {
    if (int_literal == 0) return 1;
    const n_bits: u16 = 64 - @clz(int_literal);
    const n_bytes: u16 = std.math.divCeil(u16, @intCast(n_bits), 8) catch unreachable;
    assert(n_bytes <= 8);
    return if ((n_bytes & n_bytes - 1) == 0) n_bytes else @as(u16, @intCast(1)) << @intCast(std.math.log2(n_bytes) + 1);
}

fn get_unsigned_int_for_size(size: u16) []const u8 {
    for (PrimitiveTypes) |it| {
        if (it[0][0] == 'x' and it[1] == size) {
            return it[0];
        }
    }
    unreachable;
}

pub fn type_check_plex_def_block(self: *Self, module: *Ast.Module, caller_block: *Ast.Block, plex_def: *const Ast.Expression.PlexDef, plex_decl: *const Ast.PlexDecl) bool {
    const fields = plex_decl.fields;
    const n_lines, _ = self.context.get_loc(plex_def.name);
    if (fields.items.len > plex_def.members.items.len) {
        std.log.err("{s}:{}:{}: too few fields initialized to plex '{s}' expected {}, have {}", .{ self.context.filename, n_lines, 0, plex_def.name, fields.items.len, plex_def.members.items.len });
        return false;
    } else if (fields.items.len < plex_def.members.items.len) {
        std.log.err("@TODO(shahzad): {s}:{}:{}: plex definition '{s}' contains more fields than required!", .{ self.context.filename, n_lines, 0, plex_def.name });
        return false;
    }
    for (fields.items, 0..) |field, idx| {
        // TODO(shahzad): @feat add designated initialization of fields
        // easy we can check if expr is binop.Ass and if that's the case then take
        // the l value and lookup the field that has the same name then we don't
        // type check the l value and give the r value tree to the type_check_expr
        const resolved_type = self.type_check_expr(module, caller_block, &plex_def.members.items[idx]) catch {
            std.log.err("{s}:{}:{}: type of field in plex {s} on postion {} is '{s}', but given {s}", .{ self.context.filename, n_lines, 0, plex_def.name, idx, field.type.type, "unimplemented" });
            return false;
        };

        if (!can_type_resolve(field.type, resolved_type)) {
            std.log.err("{s}:{}:{}: type of field in plex {s} on postion {} is '{s}', but given {s}", .{ self.context.filename, n_lines, 0, plex_def.name, idx, field.type.type, resolved_type.type });
            return false;
        }
    }
    return true;
}

pub fn type_check_proc_args(self: *Self, module: *Ast.Module, caller_block: *Ast.Block, proc_call: *const Ast.Expression.ProcCall, proc_decl: *const Ast.ProcDecl) bool {
    // @TODO(shahzad): better error reporting
    const params = proc_decl.get_required_params();
    const n_lines, _ = self.context.get_loc(proc_call.name);
    if (params.items.len > proc_call.params.items.len) {
        std.log.err("{s}:{}:{}: too few arguments to procedure '{s}' expected {}, have {}", .{ self.context.filename, n_lines, 0, proc_call.name, params.items.len, proc_call.params.items.len });
        return false;
    } else if (params.items.len < proc_call.params.items.len) {
        std.log.debug("@TODO(shahzad): {s}:{}:{}: procedure call '{s}' contains more arguments than required! implement named args!!!!", .{ self.context.filename, n_lines, 0, proc_call.name });
    }
    for (params.items, 0..) |param, idx| {
        const resolved_type = self.type_check_expr(module, caller_block, &proc_call.params.items[idx]) catch |err| {
            std.log.err("{s}:{}:{}: type of argument in procedure {s} on postion {} is '{s}', but given {s}, {}", .{ self.context.filename, n_lines, 0, proc_call.name, idx, param.decl.type.?.type, "unimplemented!", err });
            return false;
        };

        if (!can_type_resolve(param.decl.type.?, resolved_type)) {
            std.log.err("{s}:{}:{}: type of argument in procedure {s} on postion {} is '{s}', but given {s}", .{ self.context.filename, n_lines, 0, proc_call.name, idx, param.decl.type.?.type, resolved_type.type });
            return false;
        }
    }
    return true;
}

pub fn can_type_resolve(concrete_: ?Ast.ExprType, abstract_: ?Ast.ExprType) bool {
    if (concrete_ == null and abstract_ == null) {
        return false;
    } else if (concrete_ == null or abstract_ == null) {
        return true;
    }

    const concrete = concrete_.?.type;
    var abstract = abstract_.?.type;

    const is_abstract_int_lit = std.mem.eql(u8, abstract_.?.type, IntLiteralType);
    const is_concrete_int_lit = std.mem.eql(u8, concrete_.?.type, IntLiteralType);

    if (is_abstract_int_lit and is_concrete_int_lit) {
        return true;
    } else if (is_concrete_int_lit) {
        return can_type_resolve(abstract_, concrete_);
    } else if (is_abstract_int_lit) {
        // this means that concrete is not a literal so check if it's a pointer
        if (concrete_.?.info.ptr_depth > 0) return false; // idk if this is right or nah
        const abstract_int_lit = abstract_.?.info.int_lit;
        const abstract_int_lit_size: u16 = @intCast(get_size_of_int_literal(abstract_int_lit));
        abstract = get_unsigned_int_for_size(abstract_int_lit_size);
    } else if (abstract_.?.info.ptr_depth != concrete_.?.info.ptr_depth) {
        return false;
    }

    if (std.mem.eql(u8, concrete, abstract)) {
        return true;
    }
    const concrete_size = get_size_for_primitive_type(concrete_.?) catch return false;
    const abstract_size = get_size_for_primitive_type(abstract_.?) catch return false;
    if (concrete_size >= abstract_size and concrete[0] == abstract[0]) return true; // don't break signed numbers and only cast to bigger size
    return false;
}
pub fn type_check_bin_op(self: *Self, module: *Ast.Module, block: *Ast.Block, bin_op_expr: Ast.BinaryOperation) anyerror!Ast.ExprType {
    const asignee_type = try self.type_check_expr(module, block, bin_op_expr.lhs);
    if (is_type_int_lit(asignee_type)) {
        const int_lit = asignee_type.info.int_lit;
        std.log.debug("asignee_type int_literal, literal: {}\n", .{int_lit});
    } else std.log.debug("asignee_type {}\n", .{asignee_type});

    const asigner_type = try self.type_check_expr(module, block, bin_op_expr.rhs);
    if (is_type_int_lit(asigner_type)) {
        const int_lit = asigner_type.info.int_lit;
        std.log.debug("asigner_type int_literal, literal: {}\n", .{int_lit});
    } else std.log.debug("asigner_type {}\n", .{asigner_type});

    if (!can_type_resolve(asignee_type, asigner_type)) {
        std.log.err("unable to resolve type {s} to {s}\n", .{ asigner_type.type, asignee_type.type });
        return error.TypeMisMatch;
    }
    const return_type =
        if ((try self.get_type_size_if_exists(module, &asignee_type)).? >
        (try self.get_type_size_if_exists(module, &asigner_type)).?)
            asignee_type
        else
            asigner_type;
    if (is_type_int_lit(return_type)) {
        const int_lit = return_type.info.int_lit;
        std.log.debug("BinOP returning int_literal literal: {}\n", .{int_lit});
    } else std.log.debug("BinOP returning {}\n", .{return_type});
    return return_type;
}

fn is_expr_valid_lhs(expr: *Ast.Expression) bool {
    switch (expr.*) {
        .Var, .FieldAccess => return true,
        .BinOp => @panic("can bin op be lhs??"),
        .Call,
        .Block,
        .IfCondition,
        .WhileLoop,
        .LiteralInt,
        .LiteralString,
        .NoOp,
        .Tuple,
        .Plex,
        .Reference,
        => {
            return false;
        },
    }
}

pub fn type_check_field_expr(
    self: *Self,
    module: *Ast.Module,
    plex_type: Ast.ExprType,
    field: *Ast.FieldAccess.Field,
) !Ast.ExprType { //offset and type
    var plex_type_it = plex_type;
    var field_it: ?*Ast.FieldAccess.Field = field;
    var prev_fld = field;
    while (field_it) |fld| {
        defer field_it = fld.next;
        if (fld.kind == .Deref) {
            fld.kind.Deref = plex_type_it;
            if (plex_type_it.info.ptr_depth < 1) {
                std.log.err("failed to dereference a non pointer type\n", .{});
                self.context.print_loc(plex_type_it.type);
                self.context.print_loc(prev_fld.kind.Member);
                // ^ force because we only update it when it's not deref
                std.log.err("{[value]s: >[width]}^\n", .{
                    .value = "",
                    .width = 20 + @intFromPtr(plex_type_it.type.ptr),
                });
            }
            plex_type_it.info.ptr_depth -= 1;
            continue;
        }
        const plex = module.get_plex_decl(plex_type_it.type) orelse {
            self.context.print_loc(plex_type.type);
            return Error.TypeNotFound;
        };
        prev_fld = field;
        const field_meta_data = plex.get_field(fld.kind.Member) orelse {
            self.context.print_loc(fld.kind.Member);
            return Error.UndefinedPlexField;
        };
        fld.field_offset = field_meta_data.offset;
        fld.field_size = field_meta_data.size;
        plex_type_it = field_meta_data.type;
    }
    return plex_type_it;
}
// check if the expr is correct with types and shit and also check if it can resolve to the given type
pub fn type_check_expr(self: *Self, module: *Ast.Module, block: *Ast.Block, expression: *Ast.Expression) !Ast.ExprType {
    //@TODO(shahzad): this is ass brother please fix it
    switch (expression.*) {
        .Var => |expr_as_var| {
            const variable = block.find_variable(expr_as_var);
            const n_lines, _ = self.context.get_loc(expr_as_var);
            if (variable == null) {
                std.log.err("{s}:{}:{}: use of undefined variable '{s}'", .{ self.context.filename, n_lines, 0, expr_as_var });
                self.context.print_loc(expr_as_var);
                return Error.VariableNotDefined;
            }

            return variable.?.decl.type.?;
        },
        .BinOp => |expr_as_bin_op| {
            // @NOTE(shahzad)!!: PRECEDENCE IS REQUIRED FOR TYPE CHECKING TO PROPERLY WORK!!!!
            switch (expr_as_bin_op.op) {
                .Add, .Sub, .Div, .Mul => {
                    return try self.type_check_bin_op(module, block, expr_as_bin_op);
                },
                .Lt, .LtEq, .Gt, .GtEq, .Eq => {
                    // TODO(shahzad): @bug we don't return bool for Eq variant
                    return try self.type_check_bin_op(module, block, expr_as_bin_op);
                },
                .Ass, .AddAss, .DivAss, .MulAss, .SubAss => {
                    if (!is_expr_valid_lhs(expr_as_bin_op.lhs)) {
                        std.log.err("{s}:{}:{}: type {} cannot be assigned to {}\n", .{ self.context.filename, 0, 0, expr_as_bin_op.lhs, expr_as_bin_op.rhs });
                        return Error.TypeMisMatch;
                    }
                    return try self.type_check_bin_op(module, block, expr_as_bin_op);
                },
            }
        },
        .LiteralString => |str_lit| {
            try module.string_literals.append(.{ .string = str_lit, .label = undefined });
            return .{ .type = "x8", .info = .{ .ptr_depth = 1 } }; // hack

        },
        .Block => |blk| {
            return try self.type_check_block(module, blk, block.stack_var_offset);
        },
        .Plex => |plex| {
            const plex_decl = module.get_plex_decl(plex.name);
            if (plex_decl == null) {
                const n_lines, _ = self.context.get_loc(plex.name);

                std.log.err("{s}:{}:{}: use of undefined plex '{s}'", .{ self.context.filename, n_lines, 0, plex.name });
                self.context.print_loc(plex.name);
                return Error.PlexNotDefined;
            }
            if (self.type_check_plex_def_block(module, block, &plex, &plex_decl.?) == false) return Error.TypeMisMatch;
            return .{ .type = plex.name, .info = .{ .ptr_depth = 0 } };
        },

        .Call => |*expr_as_call| {
            // @TODO(shahzad): check if the return statement matches with the proc_decl.return_type
            const proc_decl = module.get_proc(expr_as_call.name);
            if (proc_decl == null) {
                const n_lines, _ = self.context.get_loc(expr_as_call.name);

                std.log.err("{s}:{}:{}: use of undefined procedure '{s}'", .{ self.context.filename, n_lines, 0, expr_as_call.name });
                self.context.print_loc(expr_as_call.name);
                return Error.ProcedureNotDefined;
            }
            if (!self.type_check_proc_args(module, block, expr_as_call, &proc_decl.?)) {
                return Error.ProcedureCallArgsMismatch;
            }
            return proc_decl.?.return_type;
        },
        .NoOp, .Tuple => {
            // @TODO(shahzad)!!!!!: this smells bad
            // return "";
            unreachable;
        },
        .LiteralInt => |expr_as_int_lit| {
            // @TODO(shahzad): @fixme add something  in the literal int source to we can get the loc of it
            // @TODO(shahzad)!!: @feat add comptime overflow checks on maths ops
            // @TODO(shahzad)!: @feat add run time overflow checks on maths ops

            // @NOTE(shahzad)!: @fixme Literal int is by default unsigned

            return .{ .type = IntLiteralType, .info = .{ .int_lit = expr_as_int_lit } };
        },
        .IfCondition => |if_block| {
            // is the block.stack_var_offset set atp?? cause we will need it for initializing the
            // if block
            _ = try self.type_check_expr(module, block, if_block.if_.condition);
            const if_condition_expr_type = try self.type_check_expr(
                module,
                block,
                if_block.if_.expression,
            );
            if (if_block.else_expr) |else_expr| {
                const else_condition_expr_type = try self.type_check_expr(
                    module,
                    block,
                    else_expr,
                );
                _ = else_condition_expr_type;
            }
            // TODO(shahzad): @feat check if type can resolve into each other
            // shouldn't be that hard
            return if_condition_expr_type;
        },
        .WhileLoop => |while_loop| {
            _ = try self.type_check_expr(module, block, while_loop.condition);
            return try self.type_check_expr(
                module,
                block,
                while_loop.expression,
            );
        },
        .FieldAccess => |*field_access| {
            const field_access_expr_type = try self.type_check_expr(module, block, field_access.expr);
            const typ = try self.type_check_field_expr(module, field_access_expr_type, field_access.field.?);
            field_access.last_field_size = @intCast((try self.get_type_size_if_exists(module, &typ)).?);
            return typ;
        },
        .Reference => |ref| {
            var expr_type = try self.type_check_expr(module, block, ref);
            // TODO(shahzad): @feat should we support references to int literal?
            // TODO(shahzad): @feat @bug we don't support more than one reference i.e.
            // &&x or &&&x

            // TODO(shahzad): @feat figure out a way to create temp variables when
            // reference to r values
            expr_type.info.ptr_depth += 1;

            return expr_type;
        },
        // else => |unhandled| {
        //     std.log.err("type_check_expr is not implemented for {}\n", .{unhandled});
        //
        // },
    }
    unreachable;
}

//todo(shahzad): can we print the propagating error?
pub fn type_check_stmt(self: *Self, module: *Ast.Module, block: *Ast.Block, statement: *Ast.Statement) !void {
    // @TODO(shahzad)!!!!: check mutability on assignments
    switch (statement.*) {
        .VarDefStack, .VarDefStackMut => |stmt_var_def_stack| {
            const variable = block.find_local_variable(stmt_var_def_stack.name);
            if (variable != null) {
                const n_lines, const line = self.context.get_loc(variable.?.decl.name);

                std.log.err("{s}:{}:{}: redeclaration of variable '{s}'", .{ self.context.filename, n_lines, 0, variable.?.decl.name });
                std.log.debug("{s}:{}: {s}", .{ self.context.filename, n_lines, line });

                std.log.err("first declared here", .{});
                self.context.print_loc(stmt_var_def_stack.name);
                return Error.VariableRedefinition;
            }
            //@TODO(shahzad): after we add assignment at initialization we should check type of that shit here
        },
        .VarDefGlobal, .VarDefGlobalMut => {
            unreachable; // @NOTE(shahzad): this is ONLY for static variables inside proc def

        },
        .Expr => |*stmt_expr| {
            _ = try self.type_check_expr(module, block, stmt_expr);
        },
        .Return => |stmt_return| {
            _ = stmt_return;
            unreachable;
            // if (!std.mem.eql(u8, procedure.decl.return_type.type, "void")) {
            //     if (stmt_return.expr == null) {
            //         std.log.err("@TODO(shahzad): add something in return to get the location!!!", .{});
            //         std.log.err("{s}: caller expects '{s}' but procedure '{s}' returns void", .{
            //             self.context.filename,
            //             procedure.decl.return_type.type,
            //             procedure.decl.name,
            //         });
            //     }
            // }
            // if (stmt_return.expr != null) {
            //     _ = try self.type_check_expr(
            //         module,
            //         procedure,
            //         &stmt_return.expr.?,
            //     );
            // }
            //@TODO(shahzad): check all the variables in return value is defined or nah
        },
    }
}

// TODO(shahzad): return the type that the block resolves to
pub fn type_check_block(self: *Self, module: *Ast.Module, block: *Ast.Block, block_stack_base: usize) anyerror!Ast.ExprType {
    block.stack_var_offset = block_stack_base;
    for (block.stmts.items) |*statement| {
        try self.type_check_stmt(module, block, statement);

        if (statement.* == .VarDefStack or statement.* == .VarDefStackMut) {
            var var_def = if (statement.* == .VarDefStack) statement.VarDefStack else statement.VarDefStackMut;
            const size = (try self.get_type_size_if_exists(module, &var_def.type.?)).?;
            block.stack_var_offset += if (size <= 4) 4 else 8;
            var stack_var: Ast.StackVar = undefined;
            stack_var.init(var_def.name, @intCast(block.stack_var_offset), size, var_def.type, statement.* == .VarDefStackMut);
            if (!std.meta.eql(var_def.expr, .NoOp)) {
                const expr_type = try self.type_check_expr(module, block, &var_def.expr);
                if (!can_type_resolve(var_def.type.?, expr_type)) {
                    std.log.err("unable to resolve type {s} to {s}\n", .{ (var_def.type orelse Ast.ExprType.default()).type, expr_type.type });

                    return error.TypeMisMatch;
                }
            }

            try block.stack_vars.append(stack_var);
        }
        if (statement.* == .Expr and statement.Expr == .Block) {
            block.stack_var_offset += statement.Expr.Block.stack_var_offset;
        }
    }
    block.stack_var_offset -= block_stack_base;

    return .{ .type = "void", .info = .{ .ptr_depth = 0 } };
}
pub fn type_check_proc(self: *Self, module: *Ast.Module, procedure: *Ast.ProcDef) !void {
    const return_type = try self.type_check_block(module, procedure.block, 0);
    procedure.total_stack_var_offset = procedure.block.stack_var_offset;
    if (can_type_resolve(procedure.decl.return_type, return_type) != true) {
        const n_lines, _ = self.context.get_loc(procedure.decl.return_type.type);
        std.log.err("{s}:{}: caller expects '{s}' but procedure '{s}' returns '{s}'\n", .{
            self.context.filename,
            n_lines,
            procedure.decl.return_type.type,
            procedure.decl.name,
            return_type.type,
        });
    }
}
pub fn get_type_size_if_exists2(module: *const Ast.Module, expr_type: *const Ast.ExprType) Error!?usize {
    var size: ?usize = get_size_for_primitive_type(expr_type.*) catch null;
    if (size == null) {
        const userdefined_size: ?usize = try get_size_for_user_defined_type(module, expr_type.*);
        size = userdefined_size;
    }
    return size;
}

pub fn get_type_size_if_exists(self: *Self, module: *const Ast.Module, expr_type: *const Ast.ExprType) Error!?usize {
    var size: ?usize = get_size_for_primitive_type(expr_type.*) catch null;
    if (size == null) {
        const userdefined_size: ?usize = get_size_for_user_defined_type(module, expr_type.*) catch |err| {
            std.log.err("type '{s}' is not defined\n", .{expr_type.type});
            self.context.print_loc(expr_type.type);
            return err;
        };
        size = userdefined_size;
    }
    return size;
}
pub fn type_check_plex_decl(self: *Self, module: *const Ast.Module, plex_decl: *Ast.PlexDecl, outer_plex: ?*Ast.PlexDecl) !void {
    var total_field_size: usize = 0;
    for (plex_decl.fields.items) |*plex_field| {
        if (outer_plex != null and
            std.mem.eql(u8, plex_field.type.type, outer_plex.?.name) and
            plex_field.type.info.ptr_depth == 0)
        {
            std.log.err("plex '{s}' is used recursive\n", .{outer_plex.?.name});
            self.context.print_loc(plex_field.type.type);
            return Error.RecursiveDeclaration;
        }
        var plex_field_size = try self.get_type_size_if_exists(module, &plex_field.type);

        if (plex_field_size == null) {
            var untyped_plex = module.get_plex_decl(plex_field.type.type);
            try self.type_check_plex_decl(module, &untyped_plex.?, plex_decl);
            plex_field_size.? = untyped_plex.?.size.?;
        }
        plex_field.size = @intCast(plex_field_size.?);
        plex_field.offset = @intCast(total_field_size);
        total_field_size += plex_field.size;
    }
    plex_decl.size = total_field_size;
}
pub fn type_check_argument_list(self: *Self, proc_decl: *Ast.ProcDecl) bool {
    var err = false;
    // TODO(shahzad): @perf use hashmap or smth idk
    for (0..proc_decl.args_list.items.len) |idx| {
        for (idx..proc_decl.args_list.items.len) |idx2| {
            const arg = &proc_decl.args_list.items[idx];
            const arg2 = &proc_decl.args_list.items[idx2];
            if (arg != arg2 and std.mem.eql(u8, arg.*.decl.name, arg2.*.decl.name)) {
                const n_lines, const line = self.context.get_loc(arg.*.decl.name);
                std.log.err("{s}:{}:{}: redeclaration of argument '{s}'", .{ self.context.filename, n_lines, 0, arg.*.decl.name });
                std.log.debug("{s}:{}: {s}", .{ self.context.filename, n_lines, line });

                std.log.err("first declared here", .{});
                self.context.print_loc(arg2.*.decl.name);
                err = true;
            }
        }
    }
    return err;
}
pub fn type_check_proc_decl(self: *Self, module: *Ast.Module, proc_decl: *Ast.ProcDecl) !void {
    if (self.type_check_argument_list(proc_decl)) return Error.VariableRedefinition;
    const return_size = try self.get_type_size_if_exists(module, &proc_decl.return_type);
    // NOTE(shahzad): this will happen when extern plex is used
    if (return_size == null) @panic("size is defined but not typechecked!");
    proc_decl.return_size = return_size.?;
}
// @TODO(shahzad): typecheck proc calls
pub fn type_check_mod(self: *Self, module: *Ast.Module) !void {
    for (module.plex_decl.items) |*plex_decl| {
        try self.type_check_plex_decl(module, plex_decl, null);
    }
    // @TODO(shahzad): type check declarations only
    for (module.proc_decls.items) |*proc_decl| {
        try self.type_check_proc_decl(module, proc_decl);
    }
    for (module.proc_defs.items) |*proc| {
        try self.type_check_proc(module, proc);
    }
}
