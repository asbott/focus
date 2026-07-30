Bookmark :: struct {
    name: string;
    file_path: string; // Persistent identity. Buffer ids are only valid for one runtime.
    buffer_id: s64;
    offset: s32;
}

bookmarks: [..] Bookmark;
bookmarks_dirty := false;
bookmarks_last_change_time: Apollo_Time;

BOOKMARK_FILE_MAGIC   :: 0x314d425355434f46; // "FOCUSBM1"
BOOKMARK_FILE_VERSION :: 1;
BOOKMARK_SAVE_DELAY_MS :: 500;
MAX_PERSISTED_BOOKMARKS :: 100000;

Bookmark_File_Header :: struct {
    magic: u64;
    version: u32;
    count: u32;
}

Bookmark_File_Record :: struct {
    offset: s32;
    name_count: u32;
    path_count: u32;
}

Bookmark_Dialog :: struct {
    using #as generic_dialog: Generic_Choice_Dialog(Bookmark);
    generic_dialog.global_widget_id = .bookmark_dialog;
    generic_dialog.refresh_entries = bookmark_refresh_entries;
    generic_dialog.after_refresh = bookmark_after_refresh;
    generic_dialog.on_move = bookmark_preview_selected;
    generic_dialog.on_hide = bookmark_restore_origin;
    generic_dialog.open_entry = bookmark_accept;
    mode: Mode;
    origin_editor_id: s64 = -1;
    origin_cursor: Cursor;
    accepted: bool;

    Mode :: enum { create; go_to; }
}

bookmark_dialog: Bookmark_Dialog;

show_bookmark_dialog :: (mode: Bookmark_Dialog.Mode) {
    if !config.settings.c_bookmarks return;
    editor, buffer := get_active_editor_and_buffer();
    if !editor || !buffer return;
    bookmark_dialog.mode = mode;
    bookmark_dialog.origin_editor_id = get_active_editor_id();
    bookmark_dialog.origin_cursor = get_main_cursor(editor);
    bookmark_dialog.accepted = false;
    show_dialog(*bookmark_dialog);
}

bookmark_dialog_handle_event :: (event: Input.Event) -> bool {
    // Generic choice dialogs consume Escape, arrows, Backspace, text, and Enter.
    return dialog_handle_event(*bookmark_dialog, event);
}

bookmark_name_exists :: (name: string) -> bool {
    for bookmarks if it.name == name return true;
    return false;
}

bookmark_free :: (bookmark: *Bookmark) {
    free(bookmark.name,, allocator = focus_allocator);
    free(bookmark.file_path,, allocator = focus_allocator);
    bookmark.* = .{};
}

bookmarks_clear :: () {
    for *bookmark: bookmarks bookmark_free(bookmark);
    array_reset(*bookmarks);
}

bookmarks_mark_dirty :: () {
    bookmarks_dirty = true;
    bookmarks_last_change_time = current_time_monotonic();
}

bookmark_storage_path_tmp :: () -> string {
    return tprint("%/bookmarks.bin", data_dir);
}

bookmark_get_persistable_path :: (bookmark: *Bookmark) -> string {
    if bookmark.file_path return bookmark.file_path;

    // An untitled buffer may have been saved after its bookmark was created.
    // Adopt its path the next time bookmarks are persisted.
    if bookmark.buffer_id >= 0 && bookmark.buffer_id < open_buffers.count {
        buffer := *open_buffers[bookmark.buffer_id];
        if buffer.has_file && buffer.file.full_path {
            bookmark.file_path = copy_string(buffer.file.full_path,, allocator = focus_allocator);
            return bookmark.file_path;
        }
    }
    return "";
}

bookmarks_save_to_path :: (path: string) -> bool {
    persistent_count: u32;
    for *bookmark: bookmarks {
        file_path := bookmark_get_persistable_path(bookmark);
        if file_path && bookmark.name.count <= 0xffffffff && file_path.count <= 0xffffffff then persistent_count += 1;
    }

    builder: String_Builder;
    init_string_builder(*builder);

    header := Bookmark_File_Header.{
        magic = BOOKMARK_FILE_MAGIC,
        version = BOOKMARK_FILE_VERSION,
        count = persistent_count,
    };
    append(*builder, cast(*u8) *header, size_of(Bookmark_File_Header));

    for *bookmark: bookmarks {
        file_path := bookmark_get_persistable_path(bookmark);
        if !file_path continue;
        if bookmark.name.count > 0xffffffff || file_path.count > 0xffffffff continue;

        record := Bookmark_File_Record.{
            offset = max(bookmark.offset, 0),
            name_count = cast(u32) bookmark.name.count,
            path_count = cast(u32) file_path.count,
        };
        append(*builder, cast(*u8) *record, size_of(Bookmark_File_Record));
        append(*builder, bookmark.name);
        append(*builder, file_path);
    }

    hashable := builder_to_string(*builder, do_reset = false,, allocator = temp);
    hash := calculate_hash(to_bytes(hashable));
    append(*builder, cast(*u8) *hash, size_of(u64));

    success := write_entire_file(path, *builder, do_reset = true);
    if !success then log_error("Couldn't save bookmarks to '%'", path);
    return success;
}

bookmarks_load_from_path :: (path: string) -> bool {
    file_data, success := read_entire_file(path);
    if !success return false;
    defer free(file_data);

    minimum_size := size_of(Bookmark_File_Header) + size_of(u64);
    if file_data.count < minimum_size {
        log_error("Bookmark file '%' is truncated", path);
        return false;
    }

    payload_count := file_data.count - size_of(u64);
    stored_hash := <<cast(*u64) (file_data.data + payload_count);
    payload := string.{ data = file_data.data, count = payload_count };
    if stored_hash != calculate_hash(to_bytes(payload)) {
        log_error("Bookmark file '%' failed its integrity check", path);
        return false;
    }

    header: Bookmark_File_Header;
    memcpy(*header, file_data.data, size_of(Bookmark_File_Header));
    if header.magic != BOOKMARK_FILE_MAGIC || header.version != BOOKMARK_FILE_VERSION ||
       header.count > MAX_PERSISTED_BOOKMARKS {
        log_error("Bookmark file '%' has an unsupported format", path);
        return false;
    }

    // Validate every length before changing the live bookmark list. This way a
    // damaged file can never leave a partially loaded set behind.
    cursor: s64 = size_of(Bookmark_File_Header);
    for 1..header.count {
        if cursor + size_of(Bookmark_File_Record) > payload_count return false;
        record: Bookmark_File_Record;
        memcpy(*record, file_data.data + cursor, size_of(Bookmark_File_Record));
        cursor += size_of(Bookmark_File_Record);
        string_bytes := cast(s64) record.name_count + cast(s64) record.path_count;
        if record.name_count == 0 || record.path_count == 0 || cursor + string_bytes > payload_count return false;
        cursor += string_bytes;
    }
    if cursor != payload_count return false;

    bookmarks_clear();
    cursor = size_of(Bookmark_File_Header);
    for 1..header.count {
        record: Bookmark_File_Record;
        memcpy(*record, file_data.data + cursor, size_of(Bookmark_File_Record));
        cursor += size_of(Bookmark_File_Record);
        name := string.{ data = file_data.data + cursor, count = record.name_count };
        cursor += record.name_count;
        file_path := string.{ data = file_data.data + cursor, count = record.path_count };
        cursor += record.path_count;
        array_add(*bookmarks, .{
            name = copy_string(name,, allocator = focus_allocator),
            file_path = copy_string(file_path,, allocator = focus_allocator),
            buffer_id = -1,
            offset = record.offset,
        });
    }
    return true;
}

bookmarks_load :: () {
    path := bookmark_storage_path_tmp();
    if file_exists(path) then bookmarks_load_from_path(path);
    bookmarks_dirty = false;
}

bookmarks_save_if_needed :: (force := false) {
    if !bookmarks_dirty return;
    if !force && to_milliseconds(current_time_monotonic() - bookmarks_last_change_time) < BOOKMARK_SAVE_DELAY_MS return;
    if bookmarks_save_to_path(bookmark_storage_path_tmp()) then bookmarks_dirty = false;
}

bookmarks_deinit :: () {
    bookmarks_save_if_needed(force = true);
    bookmarks_clear();
}

bookmark_matches_buffer :: (bookmark: *Bookmark, buffer: *Buffer, buffer_id: s64) -> bool {
    if bookmark.buffer_id == buffer_id && buffer_id >= 0 {
        if !bookmark.file_path return true;
        if buffer.has_file && platform_path_equals(bookmark.file_path, buffer.file.full_path) return true;
    }
    if bookmark.file_path && buffer.has_file && platform_path_equals(bookmark.file_path, buffer.file.full_path) {
        bookmark.buffer_id = buffer_id;
        return true;
    }
    return false;
}

bookmark_line_fully_deleted :: (buffer: *Buffer, bookmark_offset: s32, edit_start: s32, old_count: s32) -> bool {
    if old_count <= 0 || !buffer.bytes return false;
    edit_end := edit_start + old_count;
    position := clamp(bookmark_offset, 0, buffer.bytes.count);
    if position < edit_start || position > edit_end return false;

    line_start := position;
    while line_start > 0 && buffer.bytes[line_start-1] != #char "\n" line_start -= 1;
    line_end := position;
    while line_end < buffer.bytes.count && buffer.bytes[line_end] != #char "\n" line_end += 1;
    if line_end < buffer.bytes.count then line_end += 1; // Include the line delimiter.

    // A zero-width final line still exists after deleting the preceding newline,
    // so it is not considered deleted.
    return line_end > line_start && edit_start <= line_start && edit_end >= line_end;
}

bookmarks_note_buffer_edit_for_id :: (buffer: *Buffer, buffer_id: s64, edit_start_: s64, old_count_: s64, new_count_: s64) {
    if !bookmarks return;
    edit_start := cast(s32) edit_start_;
    old_count := cast(s32) old_count_;
    new_count := cast(s32) new_count_;
    common_count := min(old_count, new_count);
    adjustment_start := edit_start + common_count;
    delta := new_count - old_count;
    changed := false;

    index := 0;
    while index < bookmarks.count {
        bookmark := *bookmarks[index];
        if !bookmark_matches_buffer(bookmark, buffer, buffer_id) {
            index += 1;
            continue;
        }

        if bookmark_line_fully_deleted(buffer, bookmark.offset, edit_start, old_count) {
            bookmark_free(bookmark);
            array_ordered_remove_by_index(*bookmarks, index);
            changed = true;
            continue;
        }

        if bookmark.offset >= adjustment_start {
            new_offset := max(bookmark.offset + delta, adjustment_start);
            if new_offset != bookmark.offset {
                bookmark.offset = new_offset;
                changed = true;
            }
        }
        index += 1;
    }
    if changed then bookmarks_mark_dirty();
}

bookmarks_note_buffer_edit :: (buffer: *Buffer, edit_start: s64, old_count: s64, new_count: s64) {
    if !bookmarks return;

    buffer_id: s64 = -1;
    if context.current_buffer_id >= 0 && context.current_buffer_id < open_buffers.count &&
       *open_buffers[context.current_buffer_id] == buffer {
        buffer_id = context.current_buffer_id;
    } else if context.current_editor_id >= 0 && context.current_editor_id < open_editors.count {
        candidate_id := open_editors[context.current_editor_id].buffer_id;
        if candidate_id >= 0 && candidate_id < open_buffers.count && *open_buffers[candidate_id] == buffer then buffer_id = candidate_id;
    }
    if buffer_id < 0 {
        for *candidate, candidate_id: open_buffers if candidate == buffer { buffer_id = candidate_id; break; }
    }

    bookmarks_note_buffer_edit_for_id(buffer, buffer_id, edit_start, old_count, new_count);
}

bookmarks_note_buffer_saved :: (buffer_id: s64, file_path: string) {
    changed := false;
    for *bookmark: bookmarks {
        if bookmark.buffer_id != buffer_id || bookmark.file_path continue;
        bookmark.file_path = copy_string(file_path,, allocator = focus_allocator);
        changed = true;
    }
    if changed then bookmarks_mark_dirty();
}

bookmark_refresh_entries :: (filter: Fuzzy_Filter) {
    using bookmark_dialog;
    if mode == .create return; // "New Bookmark" is an input, not a picker.
    for bookmark: bookmarks {
        score, highlights := fuzzy_match(bookmark.name, filter);
        if score <= 0 && filter.full_string continue;
        entry := array_add(*filtered);
        entry.details = bookmark;
        entry.highlights = highlights;
        entry.sort_key = cast(u64) max(score, 0);
    }
}

bookmark_after_refresh :: () {
    if bookmark_dialog.filtered.count > 5 then bookmark_dialog.filtered.count = 5;
    bookmark_dialog.per_page = 5;
    if bookmark_dialog.mode == .go_to then bookmark_preview_selected();
}

bookmark_jump_to :: (bookmark: Bookmark, placement := Editor_Placement.in_place) -> bool {
    buffer_id := bookmark.buffer_id;
    if bookmark.file_path {
        id_matches_path := buffer_id >= 0 && buffer_id < open_buffers.count && open_buffers[buffer_id].has_file &&
                           platform_path_equals(bookmark.file_path, open_buffers[buffer_id].file.full_path);
        if !id_matches_path {
            buffer_id = find_buffer_id_by_path(bookmark.file_path);
            if buffer_id < 0 && file_exists(bookmark.file_path) then buffer_id, _ = find_or_create_buffer(bookmark.file_path);
        }
    }
    if buffer_id < 0 || buffer_id >= open_buffers.count return false;
    editors_open_buffer(buffer_id, placement);
    editor, buffer := get_visible_editor_and_buffer();
    if !editor || !buffer || editor.buffer_id != buffer_id return false;
    for *stored: bookmarks if stored.name == bookmark.name then stored.buffer_id = buffer_id;
    cursor := leave_only_main_cursor(editor);
    cursor.pos = clamp(bookmark.offset, 0, xx buffer.bytes.count);
    cursor.sel = cursor.pos;
    cursor.col_wanted = -1;
    editor.cursor_moved = true;
    editor.scroll_to_cursor = .yes;
    return true;
}

bookmark_preview_selected :: () {
    using bookmark_dialog;
    if mode != .go_to || !filtered return;
    selected = clamp(selected, 0, filtered.count-1);
    if bookmark_jump_to(filtered[selected].details) {
        // Opening the preview buffer activates the editors. Keep the choice
        // dialog active until Enter accepts it or Escape restores the origin.
        active_global_widget = .bookmark_dialog;
    }
}

bookmark_restore_origin :: () {
    using bookmark_dialog;
    if mode != .go_to || accepted || origin_editor_id < 0 return;
    history_reopen_editor_and_set_cursor(origin_editor_id, origin_cursor);
}

bookmark_accept :: (placement: Editor_Placement) {
    using bookmark_dialog;
    typed_name := trim(to_string(input.text));

    if mode == .create {
        if !typed_name return;
        if bookmark_name_exists(typed_name) {
            add_user_warning("A bookmark named '%' already exists", typed_name, dismiss_in_seconds = 3);
            return;
        }
        if origin_editor_id < 0 || origin_editor_id >= open_editors.count return;
        buffer_id := open_editors[origin_editor_id].buffer_id;
        buffer := *open_buffers[buffer_id];
        array_add(*bookmarks, .{
            name = copy_string(typed_name,, allocator = focus_allocator),
            file_path = ifx buffer.has_file then copy_string(buffer.file.full_path,, allocator = focus_allocator) else "",
            buffer_id = buffer_id,
            offset = origin_cursor.pos,
        });
        bookmarks_mark_dirty();
        add_success_message("Bookmark '%' added", typed_name, dismiss_in_seconds = 2);
        hide_dialog(generic_dialog);
        return;
    }

    if !filtered return;
    selected = clamp(selected, 0, filtered.count-1);
    bookmark := filtered[selected].details;
    accepted = bookmark_jump_to(bookmark, placement);
    if !accepted {
        add_user_warning("Bookmark '%' points to a file that is no longer available", bookmark.name, dismiss_in_seconds = 4);
        return;
    }
    hide_dialog(generic_dialog);
}
