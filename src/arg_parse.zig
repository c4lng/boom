const std = @import("std");
const Allocator = std.mem.Allocator;

var fixed_buffer: [2048]u8 = undefined;
var fba = std.heap.FixedBufferAllocator.init(&fixed_buffer);
input_filename: []const u8 = undefined,
output_filename: []const u8 = undefined,
allocator: Allocator = fba.allocator(),
link_object_filename: std.array_list.Managed([]const u8) = undefined,
object_only: bool = false,
const Self = @This();
pub fn init(self: *Self) void {
    self.* = .{
        .link_object_filename = .init(fba.allocator()),
    };
}
pub fn help() void {
    std.log.debug("USAGE: boom -i file", .{});
}

pub fn populate(self: *Self) !void {
    var iter = std.process.ArgIterator.init();
    var flag = iter.next();
    var is_file_flag = false;
    var _output_filename: ?[]const u8 = null;
    while (flag != null) {
        if (std.mem.eql(u8, flag.?, "-i")) {
            const name = iter.next();
            self.input_filename = name.?;
            is_file_flag = true;
        } else if (std.mem.eql(u8, flag.?, "-o")) {
            const name = iter.next();
            _output_filename = name.?;
            is_file_flag = true;
        } else if (std.mem.eql(u8, flag.?, "-c")) {
            self.object_only = true;
        } else if (std.mem.eql(u8, flag.?, "-l")) {
            // TODO(shahzad): @bug only works with relative paths :sob:
            // this is ass :sob:
            while (true) {
                const name = iter.next();
                if (name == null) break;
                try self.link_object_filename.append(name.?);
            }
        }

        flag = iter.next();
    }
    if (is_file_flag == false) {
        help();
        std.process.exit(1);
    }
    self.output_filename = _output_filename orelse "a.out";
}
