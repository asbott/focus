deinit_cursor_history :: () {
    array_reset(*edit_notifications);
    table_reset(*editor_history_table);
    table_reset(*forward_history_table);
    navigation_back_history = .{};
    navigation_forward_history = .{};

    last_seen_cursor.editor_id = -1;
    last_seen_cursor.buffer_id = -1;
    last_seen_cursor.cursor = .{};
    last_seen_cursor.moved_at = 0;
    last_seen_cursor.pending_save = false;
}

maybe_save_cursor_history :: () {
    defer apply_edit_notifications();

    // Go-to-line and bookmark dialogs move the editor as a live preview while
    // the user types (for example, "500" previews lines 5, 50, then 500).
    // Those transient positions are not real navigation history. Keeping the
    // last observed caret unchanged records the origin when a preview is
    // accepted, and records nothing when it is cancelled and restored.
    if active_global_widget == .go_to_line_dialog || active_global_widget == .bookmark_dialog return;

    editor_id := get_visible_editor_id(editors.active_pane);
    editor := ifx editor_id >= 0 then *open_editors[editor_id] else null;
    buffer := ifx editor then *open_buffers[editor.buffer_id] else null;
    buffer_id := ifx editor then editor.buffer_id else -1;
    cursor := ifx editor then get_main_cursor(editor) else NO_CURSOR;

    if !config.settings.c_caret_history {
        last_seen_cursor = .{ editor_id = editor_id, buffer_id = buffer_id, cursor = cursor, moved_at = seconds_since_init() };
        return;
    }

    location_changed := editor_id != last_seen_cursor.editor_id || buffer_id != last_seen_cursor.buffer_id;
    cursor_moved   := cursor.pos != last_seen_cursor.pos;
    now := seconds_since_init();

    saved := false;

    if location_changed {
        if last_seen_cursor.editor_id >= 0 && last_seen_cursor.buffer_id >= 0 {
            maybe_save_cursor_position(last_seen_cursor.editor_id, last_seen_cursor.buffer_id,
                                       last_seen_cursor.cursor, force = true);
        }
        last_seen_cursor = .{ editor_id = editor_id, buffer_id = buffer_id, cursor = cursor, moved_at = now, pending_save = true };
    } else if cursor_moved {
        // A large navigation records the position before the jump immediately.
        if editor && last_seen_cursor.editor_id >= 0 {
            old_line := offset_to_line(editor, buffer, last_seen_cursor.pos, safe = true);
            new_line := offset_to_line(editor, buffer, cursor.pos, safe = true);
            if abs(old_line-new_line) >= MIN_LINE_THRESHOLD {
                saved = maybe_save_cursor_position(editor_id, buffer_id, last_seen_cursor.cursor, force = true);
            }
        }
        last_seen_cursor = .{ editor_id = editor_id, buffer_id = buffer_id, cursor = cursor, moved_at = now, pending_save = true };
    } else if last_seen_cursor.pending_save && (now-last_seen_cursor.moved_at) >= IDLE_THRESHOLD_IN_SECONDS {
        saved = maybe_save_cursor_position(editor_id, buffer_id, cursor, force = true);
        last_seen_cursor.pending_save = false;
    }

    if saved {
        clear_forward_history(editor_id, buffer_id);
        navigation_forward_history = .{};
    }
}

move_back_in_cursor_history :: () -> moved: bool, editor_id: s64 = -1, buffer_id: s64 = -1, cursor := Cursor.{} {
    editor_id := get_visible_editor_id(editors.active_pane);
    if editor_id < 0 return false;
    editor, _ := get_editor_and_buffer(editor_id);
    buffer_id := editor.buffer_id;

    current_location := Navigation_History_Frame.{ editor_id = editor_id, buffer_id = buffer_id, cursor = get_main_cursor(editor) };
    navigation_moved:, destination := move_between_navigation_histories(*navigation_back_history, *navigation_forward_history, current_location);
    if navigation_moved return true, destination.editor_id, destination.buffer_id, destination.cursor;

    key := cursor_history_key(editor_id, buffer_id);
    editor_history := table_find_pointer(*editor_history_table, key);
    if !editor_history return false;

    current_cursor := get_main_cursor(editor);
    forward_history := find_or_add(*forward_history_table, key);
    ringbuffer_add(forward_history, .{ pos = current_cursor.pos, sel = current_cursor.sel });

    while true {
        has_editor_history:, frame := ringbuffer_pop(editor_history);
        if !has_editor_history break;
        if frame.pos != current_cursor.pos || frame.sel != current_cursor.sel return true, editor_id, buffer_id, Cursor.{ pos = frame.pos, sel = frame.sel };
    }
    ringbuffer_pop(forward_history); // no move: undo the speculative forward entry
    return false;
}

move_forward_in_cursor_history :: () -> moved: bool, editor_id: s64 = -1, buffer_id: s64 = -1, cursor := Cursor.{} {
    editor_id := get_visible_editor_id(editors.active_pane);
    if editor_id < 0 return false;
    editor, _ := get_editor_and_buffer(editor_id);
    buffer_id := editor.buffer_id;
    key := cursor_history_key(editor_id, buffer_id);
    forward_history := table_find_pointer(*forward_history_table, key);
    current_cursor := get_main_cursor(editor);
    if forward_history {
        editor_history := find_or_add(*editor_history_table, key);
        while true {
            has_forward:, frame := ringbuffer_pop(forward_history);
            if !has_forward break;
            if frame.pos == current_cursor.pos && frame.sel == current_cursor.sel continue;
            ringbuffer_add(editor_history, .{ pos = current_cursor.pos, sel = current_cursor.sel });
            return true, editor_id, buffer_id, Cursor.{ pos = frame.pos, sel = frame.sel };
        }
    }

    current_location := Navigation_History_Frame.{ editor_id = editor_id, buffer_id = buffer_id, cursor = current_cursor };
    navigation_moved:, destination := move_between_navigation_histories(*navigation_forward_history, *navigation_back_history, current_location);
    if navigation_moved return true, destination.editor_id, destination.buffer_id, destination.cursor;
    return false;
}


history_reopen_editor_and_set_cursor :: (editor_id: s64, new_cursor: Cursor, expected_buffer_id: s64 = -1) {
    editor: *Editor;
    buffer: *Buffer;
    if expected_buffer_id >= 0 && expected_buffer_id < open_buffers.count &&
       (editor_id < 0 || editor_id >= open_editors.count || open_editors[editor_id].buffer_id != expected_buffer_id) {
        editors_open_buffer(expected_buffer_id);
        editor_id = get_active_editor_id();
        editor, buffer = get_editor_and_buffer(editor_id);
    } else {
        editor, buffer = reopen_editor_by_id(editor_id);
    }

    make_editor_active(editor_id);

    cursor := leave_only_main_cursor(editor);
    cursor.* = new_cursor;
    put_cursor_in_valid_spot(cursor, buffer);

    last_seen_cursor = .{ editor_id = editor_id, buffer_id = editor.buffer_id, pos = cursor.pos, sel = cursor.sel };

    editor.scroll_to_cursor = .yes;
}

history_record_navigation_jump :: (destination_buffer_id: s64, destination_offset: s32) {
    if !config.settings.c_caret_history return;
    editor_id := get_visible_editor_id(editors.active_pane);
    if editor_id < 0 return;
    editor, _ := get_editor_and_buffer(editor_id);
    cursor := get_main_cursor(editor);
    if editor.buffer_id == destination_buffer_id && cursor.pos == destination_offset && cursor.sel == destination_offset return;

    source := Navigation_History_Frame.{ editor_id = editor_id, buffer_id = editor.buffer_id, cursor = cursor };
    navigation_history_add_if_distinct(*navigation_back_history, source);
    navigation_forward_history = .{};
    clear_forward_history(editor_id, editor.buffer_id);
}

navigation_history_add_if_distinct :: (history: *Navigation_History, frame: Navigation_History_Frame) {
    last := ringbuffer_peek_pointer(history);
    if last && navigation_history_frames_equal(last.*, frame) return;
    ringbuffer_add(history, frame);
}

navigation_history_frames_equal :: (a: Navigation_History_Frame, b: Navigation_History_Frame) -> bool {
    return a.editor_id == b.editor_id && a.buffer_id == b.buffer_id && a.pos == b.pos && a.sel == b.sel;
}

move_between_navigation_histories :: (from: *Navigation_History, to: *Navigation_History,
                                       current: Navigation_History_Frame) -> moved: bool, destination: Navigation_History_Frame {
    while true {
        found:, candidate := ringbuffer_pop(from);
        if !found return false, .{};
        if navigation_history_frames_equal(candidate, current) continue;
        navigation_history_add_if_distinct(to, current);
        return true, candidate;
    }
}

history_add_edit_notification_to_batch :: (notification: Buffer.Edit_Notification) {
    array_add(*edit_notifications, notification);
}

history_reset_last_seen_cursor :: () {
    // Occasionally we manually adjust cursor positions, e.g. after converting indentation to another type
    // or stripping whitespace. In this case the cursor position might change, but we don't want to
    // remember the previous one in that case because the perceived cursor position hasn't changed
    editor_id := get_visible_editor_id(editors.active_pane);
    if editor_id < 0 return;

    editor := *open_editors[editor_id];
    cursor := get_main_cursor(editor);

    last_seen_cursor = .{ editor_id = editor_id, buffer_id = editor.buffer_id, cursor = cursor };
}


#scope_file

cursor_history_key :: (editor_id: s64, buffer_id: s64) -> s64 {
    if editor_id < 0 || buffer_id < 0 return -1;
    return cast(s64) ((cast(u64)editor_id << 32) | (cast(u64)buffer_id & 0xffffffff));
}

clear_forward_history :: (editor_id: s64, buffer_id: s64) {
    history := table_find_pointer(*forward_history_table, cursor_history_key(editor_id, buffer_id));
    if history then history.* = .{};
}

maybe_save_cursor_position :: (editor_id: s64, buffer_id: s64, cursor: Cursor, force := false) -> saved: bool {
    if editor_id < 0 || buffer_id < 0 return false;

    editor, buffer := get_editor_and_buffer(editor_id);
    if editor.buffer_id != buffer_id return false;
    editor_history := find_or_add(*editor_history_table, cursor_history_key(editor_id, buffer_id));

    last_frame := ringbuffer_peek_pointer(editor_history);

    if !force && last_frame {
        last_line    := offset_to_line(editor, buffer, last_frame.pos, safe = true);
        current_line := offset_to_line(editor, buffer, cursor.pos, safe = true);
        if abs(last_line - current_line) < MIN_LINE_THRESHOLD return false;  // cursor hasn't moved far enough
    }

    history_debug_print(">> EDITOR %, FRAME %, pos = %\n", editor_id, editor_history.total, cursor.pos);
    ringbuffer_add(editor_history, .{ pos = cursor.pos, sel = cursor.sel });

    return true;
}

apply_edit_notifications :: () {
    // @speed: measure speed and maybe optimise later, if large edit groups end up being a problem
    while edit_notifications {
        buffer_id := edit_notifications[0].buffer_id;

        for edit_notifications {
            if buffer_id != it.buffer_id continue;
            apply_edit_to_navigation_history(*navigation_back_history, it);
            apply_edit_to_navigation_history(*navigation_forward_history, it);
        }

        for * editor, editor_id : open_editors {
            if editor.buffer_id != buffer_id continue;
            editor_history: *Editor_History;
            forward_history := table_find_pointer(*forward_history_table, cursor_history_key(editor_id, buffer_id));
            editor_history = table_find_pointer(*editor_history_table, cursor_history_key(editor_id, buffer_id));
            if !editor_history && !forward_history continue;

            for edit_notifications {
                if buffer_id != it.buffer_id continue;
                if editor_history then apply_edit_to_history(editor_history, it);
                if forward_history then apply_edit_to_history(forward_history, it);
            }
        }

        for edit_notifications { if buffer_id == it.buffer_id remove it; }
    }
}

apply_edit_to_navigation_history :: (history: *Navigation_History, edit: Buffer.Edit_Notification) {
    for *frame: history {
        if frame.buffer_id != edit.buffer_id continue;
        if frame.pos >= edit.offset then frame.pos = max(frame.pos + edit.delta, edit.offset);
        if frame.sel >= edit.offset then frame.sel = max(frame.sel + edit.delta, edit.offset);
    }
}

apply_edit_to_history :: (history: *Editor_History, edit: Buffer.Edit_Notification) {
    for * frame : history {
        if frame.pos >= edit.offset then frame.pos = max(frame.pos + edit.delta, edit.offset);
        if frame.sel >= edit.offset then frame.sel = max(frame.sel + edit.delta, edit.offset);
    }
}


IDLE_THRESHOLD_IN_SECONDS :: 0.2;   // record a stable caret promptly without filling history while a key is held
MIN_LINE_THRESHOLD :: 10;           // how many lines the cursor needs to move by to qualify for recording

NO_CURSOR :: Cursor.{ pos = -1, sel = -1 };

EDITOR_HISTORY_SIZE :: 64;  // per editor
NAVIGATION_HISTORY_SIZE :: 64;

Editor_History :: Ring_Buffer(Editor_History_Frame, EDITOR_HISTORY_SIZE);
Navigation_History :: Ring_Buffer(Navigation_History_Frame, NAVIGATION_HISTORY_SIZE);

editor_history_table: Table(s64, Editor_History);
forward_history_table: Table(s64, Editor_History);
navigation_back_history: Navigation_History;
navigation_forward_history: Navigation_History;

edit_notifications: [..] Buffer.Edit_Notification;

last_seen_cursor: struct {
    editor_id: s64 = -1;
    buffer_id: s64 = -1;
    using cursor: Cursor;
    moved_at: float64;
    pending_save: bool;
};


Editor_History_Frame :: struct {
    pos: s32;
    sel: s32;
}

Navigation_History_Frame :: struct {
    editor_id: s64;
    buffer_id: s64;
    using cursor: Cursor;
}

DEBUG_HISTORY :: false;

history_debug_print :: (format_string: string, args: .. Any) {
    #if DEBUG_HISTORY {
        history_debug_print(format_string, ..args);
    }
} @PrintLike

#scope_export

#if C_LANGUAGE_FEATURE_TESTS {
    c_test_caret_history_isolation :: () {
        key_a := cursor_history_key(9, 101);
        key_b := cursor_history_key(9, 202);
        assert(key_a != key_b);
        ringbuffer_add(find_or_add(*editor_history_table, key_a), .{ pos = 11, sel = 11 });
        ringbuffer_add(find_or_add(*editor_history_table, key_b), .{ pos = 22, sel = 22 });
        found_a:, frame_a := ringbuffer_pop(table_find_pointer(*editor_history_table, key_a));
        found_b:, frame_b := ringbuffer_pop(table_find_pointer(*editor_history_table, key_b));
        assert(found_a && frame_a.pos == 11 && found_b && frame_b.pos == 22,
               "Caret history storage must be isolated by editor and buffer");

        navigation_back: Navigation_History;
        navigation_forward: Navigation_History;
        source := Navigation_History_Frame.{ editor_id = 1, buffer_id = 101, cursor = .{ pos = 11, sel = 11 } };
        target := Navigation_History_Frame.{ editor_id = 2, buffer_id = 202, cursor = .{ pos = 22, sel = 22 } };
        navigation_history_add_if_distinct(*navigation_back, source);
        moved_back:, back_destination := move_between_navigation_histories(*navigation_back, *navigation_forward, target);
        assert(moved_back && navigation_history_frames_equal(back_destination, source),
               "Back must return to the source of a cross-buffer navigation jump");
        moved_forward:, forward_destination := move_between_navigation_histories(*navigation_forward, *navigation_back, source);
        assert(moved_forward && navigation_history_frames_equal(forward_destination, target),
               "Forward must return to the cross-buffer navigation target");
        apply_edit_to_navigation_history(*navigation_back, .{ buffer_id = 101, offset = 5, delta = 3 });
        edited_source := ringbuffer_peek_pointer(*navigation_back);
        assert(edited_source && edited_source.pos == 14 && edited_source.sel == 14,
               "Cross-buffer navigation locations must follow edits in their buffers");
        table_reset(*editor_history_table);
        table_reset(*forward_history_table);
    }
}
