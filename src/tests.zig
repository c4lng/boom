// @TODO(shahzad): @scope hacked together in an hour write something better
const std = @import("std");
const io = @import("io/linux.zig");
const root = @import("main.zig");
const nob = @import("nob.zig");

const TestFiles = struct {
    const TestOpts = struct { incremental: bool };
    const DEFAULT_TEST_DIR = "./tests";
    const DEFAULT_TEST_OUTPUT_DIR = "./.test_output";
    const MAX_OUTPUT_FILE_SIZE = 64 * 1024;
    const BUILD_FAIL_HARD = true;
    program_cwd: std.fs.Dir = std.fs.cwd(),
    dir: std.fs.Dir = undefined,
    output_dir: std.fs.Dir = undefined,
    filenames: std.array_list.Managed([]u8),
    allocator: std.mem.Allocator,
    const Self = @This();
    pub fn populate(allocator: std.mem.Allocator, test_dir_path: []const u8) !Self {
        var test_files: TestFiles = .{
            .allocator = allocator,
            .filenames = .init(allocator),
        };

        test_files.dir = try test_files.program_cwd.openDir(test_dir_path, .{ .iterate = true });
        var test_dir_it = test_files.dir.iterate();
        while (try test_dir_it.next()) |fileinfo| {
            if (!std.mem.startsWith(u8, fileinfo.name, "test_") or !std.mem.endsWith(u8, fileinfo.name, ".c4")) continue;
            const filename_without_ext = fileinfo.name[0..std.mem.indexOfScalar(u8, fileinfo.name, '.').?];

            const filename_duped = try allocator.dupe(u8, filename_without_ext);
            try test_files.filenames.append(filename_duped);
        }
        return test_files;
    }

    pub fn compile(self: *Self) !void {
        const input_dir_name = try get_dir_name(self.allocator, self.dir);
        // defer test_files.allocator.free(input_dir_name);
        const output_dir_name = try get_dir_name(self.allocator, self.output_dir);
        // defer test_files.allocator.free(output_dir_name);

        var test_file_idx: usize = 0;
        var path_buffer: [std.fs.max_path_bytes]u8 = undefined;
        while (test_file_idx < self.filenames.items.len) : (test_file_idx += 1) {
            const test_file = self.filenames.items[test_file_idx];
            var input_filename = std.fmt.bufPrint(&path_buffer, "./{s}/{s}.c4", .{ input_dir_name, test_file }) catch unreachable;
            input_filename = try self.allocator.dupe(u8, input_filename);
            defer self.allocator.free(input_filename);
            var output_filename = std.fmt.bufPrint(&path_buffer, "./{s}/{s}", .{ output_dir_name, test_file }) catch unreachable;
            output_filename = try self.allocator.dupe(u8, output_filename);
            defer self.allocator.free(output_filename);

            std.debug.print("input_path is {s}\n", .{input_filename});
            const opts = root.CompilerOptions{
                .object_only = false,
                .input_filename = input_filename,
                .output_filename = output_filename,
                .link_object_filename = .init(self.allocator),
            };
            var compiler = root.Compiler.default(self.allocator, opts);
            _ = compiler.compile() catch |err| {
                // TODO(shahzad): @scope this should be a hard fail
                std.log.err("failed to compile test {s} {}\n", .{ input_filename, err });
                _ = self.filenames.swapRemove(test_file_idx);
                test_file_idx -= 1;
                if (BUILD_FAIL_HARD) return err;
                continue;
            };
            try compiler.build_asm_file(false);
        }
    }
    pub fn delete(self: Self) !void {
        // TODO(shahzad): @refactor return error from here
        var path_buffer: [std.fs.max_path_bytes]u8 = undefined;
        for (self.filenames.items) |test_file| {
            const test_obj_file = std.fmt.bufPrint(&path_buffer, "{s}.o", .{test_file}) catch unreachable;
            const test_bin_file = test_file;
            self.output_dir.deleteFile(test_obj_file) catch |err| std.debug.print("failed to remove {s}: {}!\n", .{ test_obj_file, err });
            self.output_dir.deleteFile(test_bin_file) catch |err| std.debug.print("failed to remove {s}: {}!\n", .{ test_bin_file, err });
        }
    }
    fn run_tests_check(self: Self, opts: TestOpts) !void {
        var path_buffer: [std.fs.max_path_bytes]u8 = undefined;

        const output_dir_name = try get_dir_name(self.allocator, self.output_dir);
        // defer test_files.allocator.free(input_dir_name);
        // defer test_files.allocator.free(output_dir_name);

        for (self.filenames.items) |filename| {
            if (opts.incremental) {} // TODO(shahzad): @scope impl this
            const pipe = try std.posix.pipe();
            const to_read_file = std.fs.File{ .handle = pipe[0] };
            const to_write_file = std.fs.File{ .handle = pipe[1] };
            var cmd: nob.Cmd = .init(self.allocator);

            cmd.stdout = to_write_file;
            cmd.stderr = to_write_file;

            var run_cmd = std.fmt.bufPrint(&path_buffer, "./{s}/{s}", .{ output_dir_name, filename }) catch unreachable;
            run_cmd = try self.allocator.dupe(u8, run_cmd);
            defer self.allocator.free(run_cmd);
            try cmd.append(run_cmd);

            const test_output_filename = std.fmt.bufPrint(&path_buffer, "{s}.out", .{filename}) catch unreachable;
            const expected = try self.dir.readFileAlloc(self.allocator, test_output_filename, MAX_OUTPUT_FILE_SIZE);

            const proc_ret = try cmd.run(.{});
            if (proc_ret.status != 0) {
                std.log.err("failed to run test {s} exited with {}\n", .{ filename, proc_ret.status });
                continue; //TODO(shahzad): @scope ignoring failure is not a good thing
            }

            to_write_file.close();
            // TODO(shahzad): @bug only 64kib because typical linux pipe length is 64kib
            // this is a bug because we don't handle the case where the child process will
            // write more than which will cause it to block on further writes

            const output = try to_read_file.readToEndAlloc(self.allocator, 64 * 1024);

            if (!std.mem.eql(u8, expected, output)) {
                std.log.err("{s} failed!", .{filename});
                std.log.err("expected", .{});
                std.log.err("================================================================================", .{});
                std.log.err("{s}", .{expected});
                std.log.err("--------------------------------------------------------------------------------", .{});
                std.log.err("got", .{});
                std.log.err("--------------------------------------------------------------------------------", .{});
                std.log.err("{s}", .{expected});
                std.log.err("================================================================================", .{});
                return;
            } else {
                std.debug.print("{s} passed!\n", .{filename});
            }
            // we don't give a shit if the running proc fails
        }
    }

    fn record(self: Self, opts: TestOpts) !void {
        var path_buffer: [std.fs.max_path_bytes]u8 = undefined;

        const input_dir_name = try get_dir_name(self.allocator, self.dir);
        // defer test_files.allocator.free(input_dir_name);
        const output_dir_name = try get_dir_name(self.allocator, self.output_dir);
        // defer test_files.allocator.free(output_dir_name);

        for (self.filenames.items) |filename| {
            if (opts.incremental) {
                const test_output_filename = std.fmt.bufPrint(&path_buffer, "{s}.out", .{filename}) catch unreachable;
                if (self.dir.statFile(test_output_filename)) |_| {
                    std.debug.print("{s} record skipping!\n", .{filename});
                    continue;
                } else |_| {}
            }

            var cmd: nob.Cmd = .init(self.allocator);
            var run_cmd = std.fmt.bufPrint(&path_buffer, "./{s}/{s}", .{ output_dir_name, filename }) catch unreachable;
            std.debug.print("run cmd is {s}\n", .{run_cmd});

            run_cmd = try self.allocator.dupe(u8, run_cmd);
            defer self.allocator.free(run_cmd);

            try cmd.append(run_cmd);

            const test_output_filename = std.fmt.bufPrint(&path_buffer, "./{s}/{s}.out", .{ input_dir_name, filename }) catch unreachable;
            const proc_ret = try cmd.run(.{ .stdout_path = test_output_filename, .stderr_path = test_output_filename });
            // we don't give a shit if the running proc fails
            _ = proc_ret;
        }
    }
};

fn get_dir_name(allocator: std.mem.Allocator, dir: std.fs.Dir) ![]u8 {
    const dir_path_abs = try dir.realpathAlloc(allocator, ".");
    return dir_path_abs[std.mem.lastIndexOfScalar(u8, dir_path_abs, '/').? + 1 .. dir_path_abs.len];
}

test "check" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = gpa.allocator();
    var test_files = try TestFiles.populate(allocator, TestFiles.DEFAULT_TEST_DIR);
    test_files.output_dir = if (std.posix.getenv("C4_HOME")) |path|
        try io.create_dir_if_not_exists(path)
    else
        try io.create_dir_if_not_exists(TestFiles.DEFAULT_TEST_OUTPUT_DIR);

    try test_files.compile();
    try test_files.record(.{ .incremental = true });
    try test_files.run_tests_check(.{ .incremental = false });
    // try test_files.delete();
}

test "record" {}
