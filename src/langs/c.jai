C_Typedef_Candidate :: struct {
    word: string;
    start: s32;
    paren_depth: s32;
    follows_pointer: bool;
}

C_Typedef_Tracker :: struct {
    active: bool;
    base_brace_depth: s32;
    base_paren_depth: s32;
    base_bracket_depth: s32;
    segment_index: s32;
    saw_type_specifier: bool;
    expect_aggregate_tag: bool;
    attribute_pending: bool;
    attribute_paren_depth: s32 = -1;
    pointer_pending: bool;
    top_level_count: s32;
    last_top_level: C_Typedef_Candidate;
    first_nested: C_Typedef_Candidate;
    has_first_nested: bool;
    first_pointer: C_Typedef_Candidate;
    has_first_pointer: bool;
}

C_Enum_State :: struct {
    depth: s32 = -1;
    paren_depth: s32;
    bracket_depth: s32;
    expects_member: bool;
}

c_token_word :: inline (buffer: *Buffer, token: Token) -> string {
    return .{ count = token.len, data = buffer.bytes.data + token.start };
}

c_is_attribute_introducer :: inline (word: string) -> bool {
    return word == "__attribute__" || word == "__declspec";
}

c_is_pointer_declarator_modifier :: inline (word: string) -> bool {
    return word == "__cdecl" || word == "__stdcall" || word == "__fastcall" ||
           word == "__thiscall" || word == "__vectorcall" || word == "__ptr64" ||
           word == "__unaligned" || word == "_Nonnull" || word == "_Nullable" ||
           word == "restrict" || word == "__restrict" || word == "__restrict__" ||
           word == "WINAPI" || word == "CALLBACK" || word == "APIENTRY" ||
           word == "NTAPI" || word == "STDMETHODCALLTYPE";
}

c_is_identifier_token :: inline (token: Token) -> bool {
    return token.type == .identifier || token.type == .keyword || token.type == .type ||
           token.type == .value || token.type == .modifier;
}

begin_c_typedef :: (tracker: *C_Typedef_Tracker, brace_depth: s32, paren_depth: s32, bracket_depth: s32) {
    tracker.active = true;
    tracker.base_brace_depth = brace_depth;
    tracker.base_paren_depth = paren_depth;
    tracker.base_bracket_depth = bracket_depth;
    tracker.segment_index = 0;
    tracker.saw_type_specifier = false;
    tracker.expect_aggregate_tag = false;
    tracker.attribute_pending = false;
    tracker.attribute_paren_depth = -1;
    tracker.pointer_pending = false;
    tracker.top_level_count = 0;
    tracker.has_first_nested = false;
    tracker.has_first_pointer = false;
}

finish_c_typedef_segment :: (buffer: *Buffer, tracker: *C_Typedef_Tracker) {
    alias: C_Typedef_Candidate;
    has_alias := false;

    if tracker.top_level_count >= 2 {
        // The first identifier can be a user-defined declaration specifier:
        // typedef Existing_Type New_Type;
        alias = tracker.last_top_level;
        has_alias = true;
    } else if tracker.top_level_count == 1 {
        if tracker.saw_type_specifier || tracker.segment_index > 0 {
            alias = tracker.last_top_level;
            has_alias = true;
        } else if tracker.has_first_pointer {
            // typedef Existing_Type (*Callback)(int);
            alias = tracker.first_pointer;
            has_alias = true;
        } else if tracker.has_first_nested {
            alias = tracker.first_nested;
            has_alias = true;
        }
    } else if tracker.has_first_pointer {
        // typedef int (*Callback)(int);
        alias = tracker.first_pointer;
        has_alias = true;
    } else if tracker.has_first_nested {
        alias = tracker.first_nested;
        has_alias = true;
    }

    if has_alias {
        define_word(buffer, alias.word, .type);
        memset(buffer.tokens.data + alias.start, xx Token_Type.type, alias.word.count);
    }

    tracker.top_level_count = 0;
    tracker.has_first_nested = false;
    tracker.has_first_pointer = false;
    tracker.segment_index += 1;
    tracker.expect_aggregate_tag = false;
    tracker.attribute_pending = false;
    tracker.attribute_paren_depth = -1;
    tracker.pointer_pending = false;
}

record_c_include :: (buffer: *Buffer, include_token: Token, macro_sequence: u32) {
    if !buffer.has_file return;

    literal := c_token_word(buffer, include_token);
    if literal.count < 2 return;

    matched_delimiters :=
        literal[0] == #char "\"" && literal[literal.count - 1] == #char "\"" ||
        literal[0] == #char "<"  && literal[literal.count - 1] == #char ">";
    if !matched_delimiters return;

    relative_path := string.{ count = literal.count - 2, data = literal.data + 1 };
    if !relative_path return;
    // Backslash-newline pairs disappear before preprocessing tokens are
    // interpreted, including when they occur inside a header name.
    relative_path = replace(relative_path, "\\\r\n", "");
    relative_path = replace(relative_path, "\\\n", "");

    path_to_resolve := relative_path;
    if !is_absolute_path(path_to_resolve) {
        path_to_resolve = tprint("%1/%2", get_parent_dir_path(buffer.file.full_path), relative_path);
    }
    absolute_path, success := get_absolute_path(path_to_resolve,, temp);
    if !success return;

    path_overwrite_separators(absolute_path, #char "/");
    add_user_type_include(buffer, absolute_path, macro_sequence);
}

tokenize_c :: (using buffer: *Buffer, start_offset := -1, count := -1) -> [] Buffer_Region {
    auto_release_temp();
    buffer.uses_c_user_type_highlighting = true;
    tokenizer := get_tokenizer(buffer, start_offset, count);

    tokenizer.prev_tokens[0] = New(Token,, temp);
    prev_effective_type := Token_Type.invalid;
    prev_was_preprocessor_line := false;
    user_type_lookup: User_Type_Lookup_Context;
    user_type_lookup.buffers.allocator = temp;
    user_type_lookup.macro_states.allocator = temp;
    user_type_lookup.macro_status.allocator = temp;

    typedef_tracker: C_Typedef_Tracker;

    brace_depth: s32;
    paren_depth: s32;
    bracket_depth: s32;

    aggregate_pending := false;
    aggregate_kind := Keyword.kw_struct;
    aggregate_tag_seen := false;
    aggregate_attribute_pending := false;
    aggregate_attribute_paren_depth: s32 = -1;

    enum_depth: s32 = -1;
    enum_paren_depth: s32;
    enum_bracket_depth: s32;
    enum_expects_member := false;
    enum_stack: [16] C_Enum_State;
    enum_stack_count: s32;

    in_preprocessor_line := false;
    preprocessor_directive: Token;
    preprocessor_scan_offset: s32;
    preprocessor_operand_seen := false;

    in_rstr := false;
    rstr_depth: s32;

    vk_expects_type := false;

    while true {
        token := get_next_token(*tokenizer);
        if token.type == .eof break;

        using tokenizer;
        prev_token := cast(*Token) prev_tokens[0];

        if !in_rstr {
            if in_preprocessor_line {
                scan_offset := preprocessor_scan_offset;
                while scan_offset < token.start {
                    if buffer.bytes[scan_offset] == #char "\n" {
                        previous := scan_offset - 1;
                        if previous >= 0 && buffer.bytes[previous] == #char "\r" then previous -= 1;
                        if previous < 0 || buffer.bytes[previous] != #char "\\" {
                            in_preprocessor_line = false;
                            break;
                        }
                    }
                    scan_offset += 1;
                }
                if in_preprocessor_line then preprocessor_scan_offset = token.start;
            }

            // A '#' inside an existing replacement list is stringification or
            // token pasting, not a nested directive.
            starts_preprocessor_directive := !in_preprocessor_line &&
                (token.type == .directive ||
                 token.start < buffer.bytes.count && buffer.bytes[token.start] == #char "#");
            if starts_preprocessor_directive {
                in_preprocessor_line = true;
                preprocessor_directive = token;
                preprocessor_scan_offset = token.start + token.len;
                preprocessor_operand_seen = false;
            }
        }

        // RSTR(...) is deliberately opaque to the C semantic state machine.
        // Its outer parentheses remain punctuation; everything inside is string.
        if in_rstr {
            highlighted := token;
            highlighted.type = .string_literal;

            if token.type == .punctuation {
                if token.punctuation == .l_paren {
                    rstr_depth += 1;
                } else if token.punctuation == .r_paren {
                    if rstr_depth == 0 {
                        in_rstr = false;
                        highlighted.type = .punctuation;
                    } else {
                        rstr_depth -= 1;
                    }
                }
            }

            highlight_token(buffer, highlighted);
            prev_token.* = token;
            prev_effective_type = highlighted.type;
            prev_was_preprocessor_line = false;
            continue;
        }

        if !in_preprocessor_line &&
           !prev_was_preprocessor_line &&
           token.type == .punctuation && token.punctuation == .l_paren &&
           prev_token.type == .keyword && prev_token.keyword == .kw_RSTR {
            in_rstr = true;
            rstr_depth = 0;
            highlight_token(buffer, token);
            prev_token.* = token;
            prev_effective_type = token.type;
            prev_was_preprocessor_line = false;
            continue;
        }

        is_identifier_token := c_is_identifier_token(token);
        word: string;
        if is_identifier_token then word = c_token_word(buffer, token);
        force_type_context := false;
        force_enum_context := false;

        is_line_splice := false;
        if token.type == .punctuation && token.punctuation == .backslash {
            next_offset := token.start + token.len;
            if next_offset < buffer.bytes.count && buffer.bytes[next_offset] == #char "\r" then next_offset += 1;
            is_line_splice = next_offset < buffer.bytes.count && buffer.bytes[next_offset] == #char "\n";
        }
        is_directive_token := token.start == preprocessor_directive.start;
        if in_preprocessor_line && !is_directive_token && !preprocessor_operand_seen &&
           token.type != .comment && token.type != .multiline_comment && !is_line_splice {
            preprocessor_operand_seen = true;
            if preprocessor_directive.type == .directive {
                if is_identifier_token && preprocessor_directive.directive == .di_define {
                    sequence := next_c_preprocessor_sequence(buffer);
                    undefine_word(buffer, word, .macro_undefined);
                    define_word(buffer, word, .macro);
                    set_word_macro_sequence(buffer, word, sequence);
                } else if is_identifier_token && preprocessor_directive.directive == .di_undef {
                    sequence := next_c_preprocessor_sequence(buffer);
                    undefine_word(buffer, word, .macro);
                    define_word(buffer, word, .macro_undefined);
                    set_word_macro_sequence(buffer, word, sequence);
                } else if token.type == .string_literal && preprocessor_directive.directive == .di_include {
                    sequence := next_c_preprocessor_sequence(buffer);
                    record_c_include(buffer, token, sequence);
                }
            }
        }

        if enum_depth >= 0 &&
           !in_preprocessor_line &&
           brace_depth == enum_depth &&
           paren_depth == enum_paren_depth &&
           bracket_depth == enum_bracket_depth &&
           enum_expects_member && token.type == .identifier {
            define_word(buffer, word, .enum_constant);
            enum_expects_member = false;
            force_enum_context = true;
        }

        // Consume a pending struct/union/enum tag or body opener.
        starts_enum_body := false;
        if !in_preprocessor_line && aggregate_pending {
            ignoring_aggregate_attribute := aggregate_attribute_paren_depth >= 0;
            if aggregate_attribute_pending {
                if token.type == .punctuation && token.punctuation == .l_paren {
                    aggregate_attribute_pending = false;
                    aggregate_attribute_paren_depth = paren_depth + 1;
                    ignoring_aggregate_attribute = true;
                } else if token.type != .comment && token.type != .multiline_comment {
                    aggregate_attribute_pending = false;
                }
            }

            if ignoring_aggregate_attribute {
                if token.type == .punctuation && token.punctuation == .r_paren &&
                   paren_depth == aggregate_attribute_paren_depth {
                    aggregate_attribute_paren_depth = -1;
                }
            } else if token.type == .identifier && c_is_attribute_introducer(word) {
                aggregate_attribute_pending = true;
            } else if token.type == .identifier && !aggregate_tag_seen {
                define_word(buffer, word, .type);
                force_type_context = true;
                if aggregate_kind == .kw_enum {
                    aggregate_tag_seen = true;
                } else {
                    aggregate_pending = false;
                    aggregate_attribute_pending = false;
                    aggregate_attribute_paren_depth = -1;
                }
            } else if token.type == .punctuation && token.punctuation == .l_brace {
                starts_enum_body = aggregate_kind == .kw_enum;
                aggregate_pending = false;
                aggregate_attribute_pending = false;
                aggregate_attribute_paren_depth = -1;
            } else if token.type == .comment || token.type == .multiline_comment {
                // Comments do not interrupt "enum E { ... }".
            } else if aggregate_kind == .kw_enum && aggregate_tag_seen &&
                      (token.type == .type || token.type == .modifier ||
                       token.type == .operation && token.operation == .colon) {
                // C23 enum E : unsigned { ... }
            } else {
                aggregate_pending = false;
                aggregate_attribute_pending = false;
                aggregate_attribute_paren_depth = -1;
            }
        }

        if !in_preprocessor_line && aggregate_attribute_paren_depth < 0 &&
           token.type == .keyword &&
           (token.keyword == .kw_struct || token.keyword == .kw_union || token.keyword == .kw_enum) {
            aggregate_pending = true;
            aggregate_kind = token.keyword;
            aggregate_tag_seen = false;
            aggregate_attribute_pending = false;
            aggregate_attribute_paren_depth = -1;
        }

        // Track typedef declarators. Candidates inside aggregate bodies and array
        // suffixes are ignored; each top-level comma ends one declarator.
        if !in_preprocessor_line && typedef_tracker.active {
            at_base_brace := brace_depth == typedef_tracker.base_brace_depth;
            at_base_paren := paren_depth == typedef_tracker.base_paren_depth;
            at_base_bracket := bracket_depth == typedef_tracker.base_bracket_depth;

            ignoring_attribute := typedef_tracker.attribute_paren_depth >= 0;
            if typedef_tracker.attribute_pending {
                if token.type == .punctuation && token.punctuation == .l_paren {
                    typedef_tracker.attribute_pending = false;
                    typedef_tracker.attribute_paren_depth = paren_depth + 1;
                    ignoring_attribute = true;
                } else if token.type != .comment && token.type != .multiline_comment {
                    typedef_tracker.attribute_pending = false;
                }
            }

            ends_segment := token.type == .punctuation &&
                            (token.punctuation == .comma || token.punctuation == .semicolon) &&
                            at_base_brace && at_base_paren && at_base_bracket;

            if ends_segment {
                finish_c_typedef_segment(buffer, *typedef_tracker);
                if token.punctuation == .semicolon then typedef_tracker.active = false;
            } else {
                if at_base_brace && !ignoring_attribute {
                    if at_base_paren && at_base_bracket &&
                       (token.type == .type || token.type == .modifier) {
                        typedef_tracker.saw_type_specifier = true;
                    }
                    if token.type == .operation && token.operation == .asterisk && at_base_bracket {
                        typedef_tracker.pointer_pending = true;
                    }

                    if token.type == .keyword &&
                       (token.keyword == .kw_struct || token.keyword == .kw_union || token.keyword == .kw_enum) {
                        typedef_tracker.saw_type_specifier = true;
                        typedef_tracker.expect_aggregate_tag = true;
                    } else if token.type == .identifier && c_is_attribute_introducer(word) {
                        typedef_tracker.attribute_pending = true;
                    } else if typedef_tracker.expect_aggregate_tag {
                        if token.type == .identifier {
                            typedef_tracker.expect_aggregate_tag = false;
                        } else if token.type == .punctuation && token.punctuation == .l_brace {
                            typedef_tracker.expect_aggregate_tag = false;
                        }
                    } else if token.type == .identifier && bracket_depth == typedef_tracker.base_bracket_depth {
                        if typedef_tracker.pointer_pending && c_is_pointer_declarator_modifier(word) {
                            // Calling convention/nullability annotations can sit
                            // between '*' and the actual function-pointer name.
                        } else {
                            candidate := C_Typedef_Candidate.{
                                word = word,
                                start = token.start,
                                paren_depth = paren_depth - typedef_tracker.base_paren_depth,
                                follows_pointer = typedef_tracker.pointer_pending,
                            };
                            if candidate.paren_depth == 0 {
                                typedef_tracker.top_level_count += 1;
                                typedef_tracker.last_top_level = candidate;
                            } else if !typedef_tracker.has_first_nested {
                                typedef_tracker.first_nested = candidate;
                                typedef_tracker.has_first_nested = true;
                            }
                            if candidate.follows_pointer && !typedef_tracker.has_first_pointer {
                                typedef_tracker.first_pointer = candidate;
                                typedef_tracker.has_first_pointer = true;
                            }
                            typedef_tracker.pointer_pending = false;
                        }
                    }
                }
            }

            if typedef_tracker.attribute_paren_depth >= 0 &&
               token.type == .punctuation && token.punctuation == .r_paren &&
               paren_depth == typedef_tracker.attribute_paren_depth {
                typedef_tracker.attribute_paren_depth = -1;
            }
        }

        if !in_preprocessor_line && token.type == .keyword &&
           token.keyword == .kw_typedef && !typedef_tracker.active {
            begin_c_typedef(*typedef_tracker, brace_depth, paren_depth, bracket_depth);
        }

        // Vulkan's handle declaration macros name a type in their first argument.
        if !in_preprocessor_line && vk_expects_type {
            if token.type == .identifier {
                define_word(buffer, word, .type);
                force_type_context = true;
                vk_expects_type = false;
            } else if token.type == .punctuation && token.punctuation == .r_paren {
                vk_expects_type = false;
            }
        }
        if !in_preprocessor_line &&
           !prev_was_preprocessor_line &&
           token.type == .punctuation && token.punctuation == .l_paren &&
           prev_token.type == .keyword &&
           (prev_token.keyword == .kw_VK_DEFINE_HANDLE ||
            prev_token.keyword == .kw_VK_DEFINE_NON_DISPATCHABLE_HANDLE) {
            vk_expects_type = true;
        }

        effective_type := token.type;
        if is_identifier_token {
            if force_enum_context {
                effective_type = .enum_variant;
            } else if force_type_context {
                effective_type = .type;
            } else {
                definition := get_word_definition(buffer, word, *user_type_lookup);
                if definition & .macro {
                    effective_type = .macro;
                } else if token.type == .identifier && definition & .enum_constant {
                    effective_type = .enum_variant;
                } else if token.type == .identifier && definition & .type {
                    effective_type = .type;
                }
            }
        }

        highlighted := token;
        highlighted.type = effective_type;
        highlight_token(buffer, highlighted);

        // Restore the upstream function highlighting, but do not overwrite a
        // resolved type/macro/enum token used as a cast or macro invocation.
        c_settings := ifx buffer.settings then buffer.settings else *config.settings;
        if c_settings.c_parse_functions &&
           token.type == .punctuation && token.punctuation == .l_paren &&
           !prev_was_preprocessor_line &&
           prev_effective_type == .identifier {
            memset(tokens.data + prev_token.start, xx Token_Type.function, prev_token.len);
        }

        if enum_depth >= 0 &&
           !in_preprocessor_line &&
           token.type == .punctuation && token.punctuation == .comma &&
           brace_depth == enum_depth &&
           paren_depth == enum_paren_depth &&
           bracket_depth == enum_bracket_depth {
            enum_expects_member = true;
        }

        if !in_preprocessor_line && token.type == .punctuation {
            if token.punctuation == .l_brace {
                brace_depth += 1;
                if starts_enum_body {
                    if enum_depth < 0 || enum_stack_count < enum_stack.count {
                        if enum_depth >= 0 {
                            enum_stack[enum_stack_count] = .{
                                depth = enum_depth,
                                paren_depth = enum_paren_depth,
                                bracket_depth = enum_bracket_depth,
                                expects_member = enum_expects_member,
                            };
                            enum_stack_count += 1;
                        }
                        enum_depth = brace_depth;
                        enum_paren_depth = paren_depth;
                        enum_bracket_depth = bracket_depth;
                        enum_expects_member = true;
                    }
                }
            } else if token.punctuation == .r_brace {
                if enum_depth == brace_depth {
                    if enum_stack_count > 0 {
                        enum_stack_count -= 1;
                        previous_enum := enum_stack[enum_stack_count];
                        enum_depth = previous_enum.depth;
                        enum_paren_depth = previous_enum.paren_depth;
                        enum_bracket_depth = previous_enum.bracket_depth;
                        enum_expects_member = previous_enum.expects_member;
                    } else {
                        enum_depth = -1;
                        enum_expects_member = false;
                    }
                }
                brace_depth = max(brace_depth - 1, 0);
            } else if token.punctuation == .l_paren {
                paren_depth += 1;
            } else if token.punctuation == .r_paren {
                paren_depth = max(paren_depth - 1, 0);
            } else if token.punctuation == .l_bracket {
                bracket_depth += 1;
            } else if token.punctuation == .r_bracket {
                bracket_depth = max(bracket_depth - 1, 0);
            }
        }

        if token.type != .comment && token.type != .multiline_comment &&
           !(in_preprocessor_line && is_line_splice) {
            prev_token.* = token;
            prev_effective_type = effective_type;
            prev_was_preprocessor_line = in_preprocessor_line;
        }
    }

    c_schedule_semantic_index(buffer);

    return .[];
}

get_next_c_token :: get_next_token;  // export for indent tokenization

#scope_file

get_next_token :: (using tokenizer: *Tokenizer) -> Token {
    eat_white_space(tokenizer);

    token: Token;
    token.start = cast(s32) (t - buf.data);
    token.type  = .eof;
    if t >= max_t return token;

    start_t = t;

    // Look at the first char as if it's ASCII
    char := t.*;

    if ascii_is_alpha(char) || char == #char "_" {
        // Parse identifiers which start with an ASCII letter or _
        // We'll look at identifiers which start with UTF8 letters later when we've already checked for more probable possibilities
        parse_identifier(tokenizer, *token);
    } else if ascii_is_digit(char) {
        parse_number_c_like(tokenizer, *token);
    } else if char == {
        case #char ":";  parse_colon                 (tokenizer, *token);
        case #char "?";  parse_question              (tokenizer, *token);
        case #char "=";  parse_equal                 (tokenizer, *token);
        case #char "-";  parse_minus                 (tokenizer, *token);
        case #char "+";  parse_plus                  (tokenizer, *token);
        case #char "*";  parse_asterisk              (tokenizer, *token);
        case #char "<";  parse_less_than_or_include  (tokenizer, *token);
        case #char ">";  parse_greater_than          (tokenizer, *token);
        case #char "!";  parse_bang                  (tokenizer, *token);
        case #char "#";  parse_directive             (tokenizer, *token);
        case #char "\""; parse_string_literal        (tokenizer, *token);
        case #char "'";  parse_char_literal          (tokenizer, *token);
        case #char "/";  parse_slash_or_comment      (tokenizer, *token);
        case #char "&";  parse_ampersand             (tokenizer, *token);
        case #char "|";  parse_pipe                  (tokenizer, *token);
        case #char "%";  parse_percent               (tokenizer, *token);
        case #char "^";  parse_caret                 (tokenizer, *token);

        case #char ";";  token.type = .punctuation; token.punctuation = .semicolon; t += 1;
        case #char "\\"; token.type = .punctuation; token.punctuation = .backslash; t += 1;
        case #char ",";  token.type = .punctuation; token.punctuation = .comma;     t += 1;
        case #char ".";  token.type = .punctuation; token.punctuation = .period;    t += 1;
        case #char "{";  token.type = .punctuation; token.punctuation = .l_brace;   t += 1;
        case #char "}";  token.type = .punctuation; token.punctuation = .r_brace;   t += 1;
        case #char "(";  token.type = .punctuation; token.punctuation = .l_paren;   t += 1;
        case #char ")";  token.type = .punctuation; token.punctuation = .r_paren;   t += 1;
        case #char "[";  token.type = .punctuation; token.punctuation = .l_bracket; t += 1;
        case #char "]";  token.type = .punctuation; token.punctuation = .r_bracket; t += 1;

        case #char "~";  token.type = .operation;   token.operation   = .tilde;     t += 1;
        case #char "`";  token.type = .operation;   token.operation   = .backtick;  t += 1;

        case;
            // It could still be an identifier which starts with a UTF8 character
            utf32 := character_utf8_to_utf32(t, max_t - t);
            if is_utf32_letter(utf32) {
                parse_identifier(tokenizer, *token);
            } else {
                token.type = .invalid; t += 1;  // give up
            }
    }

    if t >= max_t then t = max_t;
    token.len = cast(s32) (t - start_t);

    return token;
}

parse_identifier :: (using tokenizer: *Tokenizer, token: *Token) {
    token.type = .identifier;

    identifier_str := read_utf8_identifier_string(tokenizer);

    // Maybe it's a keyword
    if identifier_str.count <= MAX_KEYWORD_LENGTH {
        ok, kw_token := table_find(*KEYWORD_MAP, identifier_str);
        if ok { token.type = kw_token.type; token.keyword = kw_token.keyword; return; }
    }
}

parse_colon :: (using tokenizer: *Tokenizer, token: *Token) {
    token.type = .operation;
    token.operation = .colon;
    t += 1;
}

parse_question :: (using tokenizer: *Tokenizer, token: *Token) {
    token.type = .operation;
    token.operation = .question;
    t += 1;
}

parse_equal :: (using tokenizer: *Tokenizer, token: *Token) {
    token.type = .operation;
    token.operation = .equal;

    t += 1;
    if t >= max_t return;

    if t.* == {
        case #char "=";  token.operation = .equal_equal; t += 1;
    }
}

parse_minus :: (using tokenizer: *Tokenizer, token: *Token) {
    token.type = .operation;
    token.operation = .minus;

    t += 1;
    if t >= max_t return;

    if t.* == {
        case #char "=";
            token.operation = .minus_equal;
            t += 1;
        case #char ">";
            token.operation = .arrow;
            t += 1;
        case #char "-";
            token.operation = .minus_minus;
            t += 1;
        case;
            if ascii_is_digit(t.*) parse_number_c_like(tokenizer, token);
    }
}

parse_plus :: (using tokenizer: *Tokenizer, token: *Token) {
    token.type = .operation;
    token.operation = .plus;

    t += 1;
    if t >= max_t return;

    if t.* == {
        case #char "=";
            token.operation = .plus_equal;
            t += 1;
        case #char "+";
            token.operation = .plus_plus;
            t += 1;
    }
}

parse_asterisk :: (using tokenizer: *Tokenizer, token: *Token) {
    token.type = .operation;
    token.operation = .asterisk;

    t += 1;
    if t >= max_t return;

    if t.* == {
        case #char "=";
            token.operation = .asterisk_equal;
            t += 1;
    }
}

parse_less_than_or_include :: (using tokenizer: *Tokenizer, token: *Token) {
    token.type = .operation;
    token.operation = .less_than;

    t += 1;
    if t >= max_t return;

    prev_token := cast(*Token) prev_tokens[0];
    include_is_on_logical_line := prev_token.type == .directive && prev_token.directive == .di_include;
    if include_is_on_logical_line {
        gap := buf.data + prev_token.start + prev_token.len;
        while gap < start_t {
            if gap.* == #char "\n" {
                previous := gap - 1;
                if previous >= buf.data && previous.* == #char "\r" then previous -= 1;
                if previous < buf.data || previous.* != #char "\\" {
                    include_is_on_logical_line = false;
                    break;
                }
            }
            gap += 1;
        }
    }
    if include_is_on_logical_line {
        // Parse an #include <...> statement
        token.type = .string_literal;
        while t < max_t && t.* != #char "\n" && t.* != #char ">" {
            if t.* == #char "\\" && t + 1 < max_t {
                if <<(t + 1) == #char "\n" {
                    t += 2;
                    continue;
                }
                if <<(t + 1) == #char "\r" && t + 2 < max_t && <<(t + 2) == #char "\n" {
                    t += 3;
                    continue;
                }
            }
            t += 1;
        }
        if t < max_t && t.* == #char ">" then t += 1;
        return;
    }

    if t.* == {
        case #char "=";
            token.operation = .less_than_equal;
            t += 1;
        case #char "<";
            token.operation = .double_less_than;
            t += 1;
    }
}

parse_greater_than :: (using tokenizer: *Tokenizer, token: *Token) {
    token.type = .operation;
    token.operation = .greater_than;

    t += 1;
    if t >= max_t return;

    if t.* == {
        case #char "=";
            token.operation = .greater_than_equal;
            t += 1;
    }
}

parse_bang :: (using tokenizer: *Tokenizer, token: *Token) {
    token.type = .operation;
    token.operation = .bang;

    t += 1;
    if t >= max_t return;

    if t.* == {
        case #char "=";
            token.operation = .bang_equal;
            t += 1;
    }
}

parse_directive :: (using tokenizer: *Tokenizer, token: *Token) {
    token.type = .identifier;

    t += 1;
    eat_white_space(tokenizer, only_until_newline = true);  // there may be spaces between the # and the name
    if t < max_t && !ascii_is_alpha(<<t) return;

    directive_str := read_identifier_string(tokenizer);

    while t < max_t && ascii_is_alnum(t.*) t += 1;

    // Check if it's one of the existing directives
    if directive_str.count > MAX_DIRECTIVE_LENGTH return;
    ok, directive := table_find(*DIRECTIVES_MAP, directive_str);
    if ok {
        token.type = .directive;
        token.directive = directive;
    }
}

parse_string_literal :: (using tokenizer: *Tokenizer, token: *Token) {
    token.type = .string_literal;

    escape_seen := false;

    t += 1;
    while t < max_t && t.* != #char "\n" {
        if t.* == #char "\\" && t + 1 < max_t {
            if <<(t + 1) == #char "\n" {
                t += 2;
                escape_seen = false;
                continue;
            }
            if <<(t + 1) == #char "\r" && t + 2 < max_t && <<(t + 2) == #char "\n" {
                t += 3;
                escape_seen = false;
                continue;
            }
        }
        if <<t == #char "\"" && !escape_seen break;
        escape_seen = !escape_seen && <<t == #char "\\";
        t += 1;
    }
    if t < max_t && <<t == #char "\"" then t += 1;
}

parse_char_literal :: (using tokenizer: *Tokenizer, token: *Token) {
    token.type = .char_literal;

    escape_seen := false;

    t += 1; //
    if t >= max_t || t.* == #char "\n" return;

    if t.* == #char "\\" {
      escape_seen = true;
      t += 1;
      if t >= max_t || t.* == #char "\n" return;
    }

    if t.* == #char "'" && !escape_seen {
      // not escaped single quote without a character
      token.type = .invalid;
      t += 1; // the invalid '
      return;
    }

    t += 1; // the char
    if t >= max_t || t.* == #char "\n" return;

    t += 1; // ending '
}

parse_slash_or_comment :: (using tokenizer: *Tokenizer, token: *Token) {
    token.type = .operation;
    token.operation = .slash;

    t += 1;
    if t >= max_t return;

    if t.* == {
        case #char "=";
            token.operation = .slash_equal;
            t += 1;
        case #char "/";
            token.type = .comment;
            t += 1;
            while t < max_t && t.* != #char "\n" t += 1;
        case #char "*";
            token.type = .multiline_comment;
            t += 1;
            while t + 1 < max_t {
                if t.* == #char "*" && << (t + 1) == #char "/" {
                  t += 2;
                  break;
                }
                t += 1;
            }
    }
}

parse_ampersand :: (using tokenizer: *Tokenizer, token: *Token) {
    token.type = .operation;
    token.operation = .ampersand;

    t += 1;
    if t >= max_t return;

    if t.* == {
        case #char "=";
            token.operation = .ampersand_equal;
            t += 1;
        case #char "&";
            token.operation = .double_ampersand;
            t += 1;
    }
}

parse_pipe :: (using tokenizer: *Tokenizer, token: *Token) {
    token.type = .operation;
    token.operation = .pipe;

    t += 1;
    if t >= max_t return;

    if t.* == {
        case #char "=";
            token.operation = .pipe_equal;
            t += 1;
        case #char "|";
            token.operation = .double_pipe;
            t += 1;
    }
}

parse_percent :: (using tokenizer: *Tokenizer, token: *Token) {
    token.type = .operation;
    token.operation = .percent;

    t += 1;
    if t >= max_t return;

    if t.* == {
        case #char "=";
            token.operation = .percent_equal;
            t += 1;
    }
}

parse_caret :: (using tokenizer: *Tokenizer, token: *Token) {
    token.type = .operation;
    token.operation = .caret;

    t += 1;
    if t >= max_t return;

    if t.* == {
        case #char "=";
            token.operation = .caret_equal;
            t += 1;
    }
}

Token :: struct {
    using #as base: Base_Token;

    union {
        keyword:        Keyword;
        punctuation:    Punctuation;
        operation:      Operation;
        directive:      Directive;
    }
}

PUNCTUATION :: string.[
    "semicolon", "backslash", "l_paren", "r_paren", "l_brace", "r_brace", "l_bracket", "r_bracket", "period", "comma",
];

OPERATIONS :: string.[
    "arrow", "bang", "backtick", "pipe", "double_pipe", "pipe_equal", "equal", "equal_equal", "bang_equal", "percent",
    "percent_equal", "less_than", "double_less_than", "less_than_equal", "greater_than", "greater_than_equal", "minus",
    "minus_equal", "minus_minus", "asterisk", "asterisk_equal", "colon", "slash", "plus", "plus_equal", "plus_plus",
    "slash_equal", "ampersand", "double_ampersand", "ampersand_equal", "tilde", "question", "unknown", "caret", "caret_equal",
];

KEYWORDS :: string.[
    "break", "case", "continue", "default", "do", "else", "enum", "for", "goto", "if", "return", "sizeof", "struct", "switch",
    "typedef", "union", "while","_Atomic", "_Generic", "_Noreturn", "_Static_assert", "__asm", "__asm__", "__except",
    "__finally", "__leave", "__try",
    "RSTR", "VK_DEFINE_HANDLE", "VK_DEFINE_NON_DISPATCHABLE_HANDLE"
];

TYPE_KEYWORDS :: string.[
    // built-in types
    "char", "double", "float", "int", "long", "short", "void", "_Bool", "_Complex", "_Imaginary",

    // stdint types
    "int8_t", "int16_t", "int32_t", "int64_t", "uint8_t", "uint16_t", "uint32_t", "uint64_t", "int_least8_t", "int_least16_t",
    "int_least32_t", "int_least64_t", "uint_least8_t", "uint_least16_t", "uint_least32_t", "uint_least64_t", "int_fast8_t",
    "int_fast16_t", "int_fast32_t", "int_fast64_t", "uint_fast8_t", "uint_fast16_t", "uint_fast32_t", "uint_fast64_t", "intptr_t",
    "uintptr_t", "intmax_t", "uintmax_t", "wint_t", "size_t", "ssize_t", "ptrdiff_t", "sig_atomic_t", "time_t", "clock_t", "bool", "u8", "s8", "u16", "s16", "u32", "s32", "u64", "s64", "sys_int", "sys_uint", "uint8", "int8", "uint16", "int16", "uint32", "int32", "uint64", "int64"
];

VALUE_KEYWORDS :: string.[
    "false", "true",
];

MODIFIER_KEYWORDS :: string.[
    "const", "constexpr", "extern", "register", "restrict", "signed", "static", "unsigned", "volatile", "thread_local", "_Thread_local",
];

DIRECTIVES :: string.[
    "define", "elif", "elifdef", "elifndef", "else", "end", "endif", "error", "if", "ifdef", "ifndef",
    "include", "line", "pragma", "undef", "warning",
];

#insert -> string {
    b: String_Builder;
    init_string_builder(*b);

    define_enum :: (b: *String_Builder, enum_name: string, prefix: string, value_lists: [][] string) {
        print_to_builder(b, "% :: enum u16 {\n", enum_name);
        for values : value_lists {
            for v : values print_to_builder(b, "    %0%;\n", prefix, v);
        }
        print_to_builder(b, "}\n");
    }

    define_enum(*b, "Punctuation",  "",    .[PUNCTUATION]);
    define_enum(*b, "Operation",    "",    .[OPERATIONS]);
    define_enum(*b, "Keyword",      "kw_", .[KEYWORDS, TYPE_KEYWORDS, VALUE_KEYWORDS, MODIFIER_KEYWORDS]);
    define_enum(*b, "Directive",    "di_", .[DIRECTIVES]);

    return builder_to_string(*b);
}

Keyword_Token :: struct {
    type: Token_Type;
    keyword: Keyword;
}

KEYWORD_MAP :: #run -> Table(string, Keyword_Token) {
    table: Table(string, Keyword_Token);
    size := 10 * (KEYWORDS.count + TYPE_KEYWORDS.count + VALUE_KEYWORDS.count);
    init(*table, size);

    #insert -> string {
        b: String_Builder;
        for KEYWORDS           append(*b, sprint("table_add(*table, \"%1\", Keyword_Token.{ type = .keyword,  keyword = .kw_%1 });\n", it));
        for TYPE_KEYWORDS      append(*b, sprint("table_add(*table, \"%1\", Keyword_Token.{ type = .type,     keyword = .kw_%1 });\n", it));
        for VALUE_KEYWORDS     append(*b, sprint("table_add(*table, \"%1\", Keyword_Token.{ type = .value,    keyword = .kw_%1 });\n", it));
        for MODIFIER_KEYWORDS  append(*b, sprint("table_add(*table, \"%1\", Keyword_Token.{ type = .modifier, keyword = .kw_%1 });\n", it));
        return builder_to_string(*b);
    }

    return table;
}

DIRECTIVES_MAP :: #run -> Table(string, Directive) {
    table: Table(string, Directive);
    size := 2 * DIRECTIVES.count;
    init(*table, size);

    #insert -> string {
        b: String_Builder;
        init_string_builder(*b);
        for DIRECTIVES {
            print_to_builder(*b, "table_add(*table, \"%1\", .di_%1);\n", it);
        }
        return builder_to_string(*b);
    }

    return table;
}

MAX_KEYWORD_LENGTH :: #run -> s32 {
    result: s64;
    for KEYWORDS          { if it.count > result then result = it.count; }
    for TYPE_KEYWORDS     { if it.count > result then result = it.count; }
    for VALUE_KEYWORDS    { if it.count > result then result = it.count; }
    for MODIFIER_KEYWORDS { if it.count > result then result = it.count; }
    return xx result;
}

MAX_DIRECTIVE_LENGTH :: #run -> s32 {
    result: s64;
    for DIRECTIVES { if it.count > result then result = it.count; }
    return xx result;
}
