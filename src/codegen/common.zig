const Ast = @import("../ast.zig");
// TODO(shahzad): @fixme change storage based on the current platform
const Storage = @import("./x64_gas_linux.zig").Storage;
pub const CompiledExpression = union(enum) {
    pub const CompiledExpCommon = struct {
        expr: []const u8,
        size: u32,
    };
    pub const CompiledExprStack = struct {
        offset: usize,
        size: u32,
    };
    pub const CompiledExprLiteral = struct {
        literal: u64,
        size: u32,
    };
    pub const CompiledExprField = struct {
        access: Ast.FieldAccess,
    };
    pub const CompiledExprPlex = struct {
        storage_type: Storage.Type,
        start: u64,
    };

    Var: CompiledExprStack,
    Reference: *CompiledExpression,
    Field: CompiledExprField,
    PlexLiteral: CompiledExprPlex, // compile_plex takes storage as argument so we don't need to pass shit
    LitInt: CompiledExprLiteral,
    LitStr: CompiledExpCommon,
    Register: CompiledExpCommon,
    Call: CompiledExpCommon,
    // TODO(shahzad): @refactor i've piled garbage onto garbage so much that i have to
    // do the oop :sob: we will have to refactor ts
    pub fn get_size(self: @This()) u32 {
        switch (self) {
            inline .Var => |compiled_expr| return compiled_expr.size,
            inline .LitInt => |compiled_expr| return compiled_expr.size,
            inline .LitStr, .Register, .Call => |compiled_expr| return compiled_expr.size,
            inline .Field => |compiled_expr| return compiled_expr.access.field_size,
            inline .PlexLiteral => unreachable,
            inline .Reference => return 8,
        }
    }
};
