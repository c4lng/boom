const std = @import("std");
const builtin = @import("builtin");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const io = @import("io/linux.zig");

const ArgParse = @import("arg_parse.zig");

const Lexer = @import("lexer.zig").Lexer;
const Parser = @import("parser.zig").Parser;
const SourceContext = @import("ast.zig").SourceContext;
const TypeCheck = @import("./type_check.zig");
const Ir = @import("ir.zig");
// const CodeGen = @import("./codegen/x64_gas_linux.zig");
const CodeGen = @import("./codegen/ir_codegen.zig");
const StringBuilder = @import("string_builder.zig");

const nob = @import("nob.zig");

pub const CompilerOptions = struct {
    input_filename: []const u8,
    output_filename: []const u8,
    link_object_filename: std.array_list.Managed([]const u8),
    object_only: bool,

    const Self = @This();
    pub fn from_args(args: ArgParse) Self {
        return .{
            .input_filename = args.input_filename,
            .output_filename = args.output_filename,
            .link_object_filename = args.link_object_filename,
            .object_only = args.object_only,
        };
    }
};
pub const Compiler = struct {
    allocator: Allocator,
    lexer: Lexer,
    source_ctx: SourceContext,
    parser: Parser,
    type_checker: TypeCheck,
    code_gen: CodeGen,
    opts: CompilerOptions,
    const Self = @This();
    pub fn default(allocator: Allocator, opts: CompilerOptions) Self {
        return .{
            .allocator = allocator,
            .lexer = undefined,
            .source_ctx = undefined,
            .parser = undefined,
            .type_checker = undefined,
            .code_gen = undefined,
            .opts = opts,
        };
    }

    pub fn compile(self: *Self) !void {
        const program = try io.read_entire_file(self.allocator, self.opts.input_filename);

        const source_ctx = SourceContext.init(self.opts.input_filename, program);

        self.lexer.init(self.allocator, source_ctx);

        try self.lexer.tokenize();

        self.parser = Parser.init(self.allocator, self.lexer.tokens.items);
        var module = try self.parser.parse(source_ctx);

        self.type_checker = TypeCheck.init(self.allocator, module.context);
        self.type_checker.type_check_mod(&module) catch |err| {
            std.log.debug("Error Occured {}", .{err});
            return err;
        };
        var ir = Ir.init(self.allocator);
        var ir_son = try ir.from_proc(module.proc_defs.at(0));
        self.code_gen = try CodeGen.init(self.allocator);
        try self.code_gen.compile_bb(&ir_son);
        // try self.code_gen.compile_son(&ir_son);
        
        // try self.code_gen.compile_son(&ir_son);
        // self.code_gen = CodeGen.init(self.allocator);
        // try self.code_gen.compile_mod(&module);
    }

    pub fn build_asm_file(self: Self, save_asm_file: bool) !void {
        // TODO(shahzad): @refactor
        const program = self.code_gen.get_generated_assembly();

        var cmd: nob.Cmd = .init(self.allocator);
        var temp_builder = StringBuilder.init(self.allocator);

        var ret: std.posix.WaitPidResult = undefined;
        var buff: [1024]u8 = undefined;
        const asm_filename = if (save_asm_file)
            try std.fmt.bufPrint(&buff, "{s}.s", .{self.opts.output_filename})
        else
            "-";

        if (save_asm_file) try io.write_entire_file(asm_filename, program);

        const obj_filename = try temp_builder.print_fmt("{s}.o", .{self.opts.output_filename});
        try cmd.append_many(&[_][]const u8{ "as", "-g", asm_filename, "-o", if (self.opts.object_only) self.opts.output_filename else obj_filename });

        ret = blk: {
            if (!save_asm_file) {
                // TODO(shahzad): @scope extend nob.zig to support this
                var child_proc = std.process.Child.init(cmd.arg_list.items, self.allocator);
                child_proc.stdin_behavior = .Pipe;
                try child_proc.spawn();
                const pid = child_proc.id;
                try child_proc.stdin.?.writeAll(program);
                child_proc.stdin.?.close();
                child_proc.stdin = null;
                const cp_ret = try child_proc.wait();
                break :blk .{ .pid = pid, .status = cp_ret.Exited };
            } else {
                break :blk try cmd.run(.{});
            }
        };

        if (ret.status != 0) {
            std.log.err("failed to run command \"{s}\"!\n", .{try std.mem.join(self.allocator, " ", cmd.arg_list.items)});
            return;
        }

        cmd.reset();
        if (self.opts.object_only) return;

        try cmd.append_many(&[_][]const u8{ "gcc", "-g", obj_filename });
        for (self.opts.link_object_filename.items) |object_file| {
            try cmd.append(object_file);
        }
        try cmd.append_many(&[_][]const u8{ "-o", self.opts.output_filename });
        ret = try cmd.run(.{});
        if (ret.status != 0) {
            std.log.err("failed to run command \"{s}\"!\n", .{try std.mem.join(self.allocator, " ", cmd.arg_list.items)});
            return;
        }
        cmd.reset();
    }
};
pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};

    const allocator = gpa.allocator();

    var args: ArgParse = .{};
    args.init();
    try args.populate();

    const opts = CompilerOptions.from_args(args);
    var compiler = Compiler.default(allocator, opts);
    try compiler.compile();

    // try compiler.build_asm_file(false);

    // std.debug.print("generated assembly", .{});
    // std.debug.print("--------------------------------------------------\n", .{});
    // std.debug.print("{s}\n", .{compiler.code_gen.program_builder.string.items});
    // std.debug.print("--------------------------------------------------\n", .{});
}
