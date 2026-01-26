const std = @import("std");
const ArrayListManaged = std.array_list.Managed;
const Allocator = std.mem.Allocator;

string: ArrayListManaged(u8),
const Self = @This();
pub fn init(allocator: Allocator) Self {
    return .{ .string = .init(allocator) };
}
pub fn append_fmt(self: *Self, comptime fmt: []const u8, args: anytype) ![]const u8 {
    const format_required_size = std.fmt.count(fmt, args);
    const fmt_buff: []u8 = try self.string.addManyAsSlice(format_required_size);
    return try std.fmt.bufPrint(fmt_buff, fmt, args);
}

pub fn print_fmt(self: *Self, comptime fmt: []const u8, args: anytype) ![]u8 {
    const format_required_size = std.fmt.count(fmt, args);
    try self.string.resize(format_required_size);
    return try std.fmt.bufPrint(self.string.items, fmt, args);
}

pub fn mark(self: *Self) usize {
    return self.string.items.len;
}
pub fn reset(self: *Self, mark_: usize) void {
    self.string.items.len = mark_;
}

pub const Fixed = struct {
    buf: []u8,
    pub fn init(buffer: []u8) Fixed {
        return .{ .buf = buffer };
    }
    pub fn print_fmt(self: *Fixed, comptime fmt: []const u8, args: anytype) ![]u8 {
        return try std.fmt.bufPrint(self.buf, fmt, args);
    }
};
