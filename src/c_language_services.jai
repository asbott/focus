C_Symbol_Kind :: enum u8 {
    function;
    global_variable;
    local_variable;
    parameter;
    struct_member;
    type_definition;
    macro;
    enum_constant;
    count;
}

C_SYMBOL_BUCKET_COUNT :: 2048;

C_Symbol :: struct {
    name_hash: u64;
    type_hash: u64;       // declared aggregate type, or owning aggregate for members
    result_type_hash: u64; // member/variable value type (for chained dereferences)
    name_offset: s32;
    name_count: s32;
    definition_offset: s32;
    scope_start: s32;
    scope_end: s32;
    kind: C_Symbol_Kind;
    next_same_hash: s32 = -1;
}

C_Reference :: struct {
    offset: s32;
    count: s32;
    symbol_index: s32;
    token_type: Token_Type;
}

C_Diagnostic :: struct {
    offset: s32;
    count: s32 = 1;
    message: string;
    severity: enum u8 { error; warning; note; };
}

C_Completion_State :: struct {
    candidates: Array(C_Completion_Candidate);
    prefix_start: s32;
    selected: s32;
    active: bool;
}

C_Completion_Candidate :: struct {
    name: string;
    kind: C_Symbol_Kind;
    priority: u8;
}

C_Completion_Expectation :: enum u8 { any; variable; type; member; function; value; macro; }

C_Semantic_Token :: struct {
    start: s32 #align 1;
    count: s32 #align 1;
    pair: s32 = -1 #align 1;
    brace_depth: s16 #align 1;
    paren_depth: s16 #align 1;
    bracket_depth: s16 #align 1;
    kind: enum u8 { word; punctuation; } #align 1;
    first: u8 #align 1;
    second: u8 #align 1;
    lexical_type: Token_Type #align 1;
}

c_get_settings :: inline (buffer: *Buffer) -> *Settings {
    return ifx buffer.settings then buffer.settings else *config.settings;
}

c_symbol_token_type :: inline (kind: C_Symbol_Kind) -> Token_Type {
    if kind == {
        case .function;        return .function;
        case .global_variable; return .variable_global;
        case .local_variable;  return .variable_local;
        case .parameter;       return .parameter;
        case .struct_member;   return .struct_member;
        case .type_definition; return .type;
        case .macro;           return .macro;
        case .enum_constant;   return .enum_variant;
    }
    return .identifier;
}

c_symbol_matches_token :: inline (kind: C_Symbol_Kind, lexical_type: Token_Type, next_is_call: bool) -> bool {
    if lexical_type == .macro return kind == .macro;
    if lexical_type == .enum_variant return kind == .enum_constant;
    if lexical_type == .type return kind == .type_definition;
    if next_is_call return kind == .function;
    return kind == .global_variable || kind == .local_variable || kind == .parameter || kind == .function;
}

c_name_hash :: inline (name: string) -> u64 {
    return hash_user_type_name(name, 0xa0761d6478bd642f);
}

c_symbol_name :: inline (buffer: *Buffer, symbol: C_Symbol) -> string {
    if symbol.name_offset < 0 || symbol.name_offset + symbol.name_count > buffer.bytes.count return "";
    return .{ data = buffer.bytes.data + symbol.name_offset, count = symbol.name_count };
}

c_token_text :: inline (buffer: *Buffer, token: C_Semantic_Token) -> string {
    return .{ data = buffer.bytes.data + token.start, count = token.count };
}

c_token_is :: inline (token: C_Semantic_Token, first: u8, second: u8 = 0) -> bool {
    return token.kind == .punctuation && token.first == first && token.second == second;
}

c_is_word_start :: inline (c: u8) -> bool {
    return ascii_is_alpha(c) || c == #char "_" || c >= 128;
}

c_is_word_continue :: inline (c: u8) -> bool {
    return ascii_is_alpha(c) || ascii_is_digit(c) || c == #char "_" || c >= 128;
}

c_is_ignored_lexical_type :: inline (type: Token_Type) -> bool {
    return type == .comment || type == .multiline_comment || type == .string_literal ||
           type == .multiline_string || type == .raw_string || type == .char_literal;
}

c_analysis_cancelled :: inline (cancel_flag: *bool) -> bool {
    return cancel_flag && atomic_read(cancel_flag);
}

c_collect_semantic_tokens :: (buffer: *Buffer, cancel_flag: *bool = null) -> [] C_Semantic_Token /* temp */ {
    result: [..] C_Semantic_Token;
    result.allocator = temp;

    braces: [..] s32; braces.allocator = temp;
    parens: [..] s32; parens.allocator = temp;
    brackets: [..] s32; brackets.allocator = temp;
    brace_depth: s16;
    paren_depth: s16;
    bracket_depth: s16;

    i: s32;
    at_line_start := true;
    in_preprocessor := false;
    while i < buffer.bytes.count {
        if c_analysis_cancelled(cancel_flag) return .[];
        c := buffer.bytes[i];
        lexical_type := ifx i < buffer.tokens.count then buffer.tokens[i] else Token_Type.default;

        if c == #char "\n" {
            escaped := i > 0 && buffer.bytes[i-1] == #char "\\";
            if !escaped { at_line_start = true; in_preprocessor = false; }
            i += 1;
            continue;
        }
        if in_preprocessor { i += 1; continue; }
        if c == #char " " || c == #char "\t" || c == #char "\r" { i += 1; continue; }
        if at_line_start && c == #char "#" { in_preprocessor = true; i += 1; continue; }
        at_line_start = false;

        if c_is_ignored_lexical_type(lexical_type) {
            i += 1;
            while i < buffer.bytes.count && buffer.tokens[i] == lexical_type { i += 1; }
            continue;
        }

        if c_is_word_start(c) {
            start := i;
            i += 1;
            while i < buffer.bytes.count && c_is_word_continue(buffer.bytes[i]) { i += 1; }
            array_add(*result, C_Semantic_Token.{
                start = start, count = i-start, kind = .word, first = c,
                lexical_type = lexical_type,
                brace_depth = brace_depth, paren_depth = paren_depth, bracket_depth = bracket_depth,
            });
            continue;
        }

        second: u8;
        if i+1 < buffer.bytes.count {
            n := buffer.bytes[i+1];
            if (c == #char "-" && n == #char ">") ||
               (c == #char ":" && n == #char ":") ||
               (c == #char "." && n == #char ".") {
                second = n;
            }
        }
        token_index := cast(s32) result.count;
        token := C_Semantic_Token.{
            start = i, count = cast(s32) (ifx second then 2 else 1),
            kind = .punctuation, first = c, second = second, lexical_type = lexical_type,
            brace_depth = brace_depth, paren_depth = paren_depth, bracket_depth = bracket_depth,
        };
        array_add(*result, token);

        if c == #char "{" { array_add(*braces, token_index); brace_depth += 1; }
        else if c == #char "}" {
            brace_depth = max(brace_depth-1, 0);
            if braces { open := pop(*braces); result[open].pair = token_index; result[token_index].pair = open; }
        } else if c == #char "(" { array_add(*parens, token_index); paren_depth += 1; }
        else if c == #char ")" {
            paren_depth = max(paren_depth-1, 0);
            if parens { open := pop(*parens); result[open].pair = token_index; result[token_index].pair = open; }
        } else if c == #char "[" { array_add(*brackets, token_index); bracket_depth += 1; }
        else if c == #char "]" {
            bracket_depth = max(bracket_depth-1, 0);
            if brackets { open := pop(*brackets); result[open].pair = token_index; result[token_index].pair = open; }
        }
        i += token.count;
    }
    return result;
}

c_is_control_word :: inline (word: string) -> bool {
    return word == "if" || word == "for" || word == "while" || word == "switch" ||
           word == "return" || word == "sizeof" || word == "_Alignof" || word == "typeof" ||
           word == "case" || word == "do";
}

c_is_declaration_specifier :: inline (token: C_Semantic_Token, word: string) -> bool {
    return token.lexical_type == .type || token.lexical_type == .modifier ||
           word == "struct" || word == "union" || word == "enum" || word == "typedef" ||
           word == "_Atomic" || word == "inline" || word == "_Noreturn";
}

c_is_declarator_identifier :: inline (token: C_Semantic_Token, word: string) -> bool {
    if token.kind != .word return false;
    if token.lexical_type == .type || token.lexical_type == .modifier ||
       token.lexical_type == .keyword || token.lexical_type == .value || token.lexical_type == .macro ||
       token.lexical_type == .directive return false;
    return !c_is_control_word(word) && !c_is_attribute_introducer(word) && !c_is_pointer_declarator_modifier(word);
}

c_add_symbol :: (buffer: *Buffer, token: C_Semantic_Token, kind: C_Symbol_Kind, scope_start: s32, scope_end: s32, type_hash: u64 = 0, result_type_hash: u64 = 0) -> s32 {
    name := c_token_text(buffer, token);
    hash := c_name_hash(name);
    if buffer.c_symbol_bucket_heads.count == 0 {
        resize(*buffer.c_symbol_bucket_heads, C_SYMBOL_BUCKET_COUNT);
        memset(buffer.c_symbol_bucket_heads.data, 0xff, buffer.c_symbol_bucket_heads.count*size_of(s32));
    }
    bucket := cast(s32) (hash & (C_SYMBOL_BUCKET_COUNT-1));
    existing := buffer.c_symbol_bucket_heads[bucket];
    while existing >= 0 {
        symbol := buffer.c_symbols[existing];
        if symbol.name_hash == hash && symbol.definition_offset == token.start && symbol.kind == kind return existing;
        existing = symbol.next_same_hash;
    }
    symbol := C_Symbol.{
        name_hash = hash, name_offset = token.start, name_count = token.count,
        definition_offset = token.start, scope_start = scope_start, scope_end = scope_end,
        kind = kind, type_hash = type_hash, result_type_hash = result_type_hash,
        next_same_hash = buffer.c_symbol_bucket_heads[bucket],
    };
    add(*buffer.c_symbols, symbol);
    buffer.c_symbol_bucket_heads[bucket] = buffer.c_symbols.count-1;
    if kind == .function then define_word(buffer, name, .function);
    else if kind == .global_variable then define_word(buffer, name, .variable);
    return cast(s32) buffer.c_symbols.count-1;
}

c_register_macro_definitions :: (buffer: *Buffer, cancel_flag: *bool = null) -> [] C_Reference /* temp */ {
    references: [..] C_Reference;
    references.allocator = temp;
    i: s32;
    while i < buffer.bytes.count {
        if c_analysis_cancelled(cancel_flag) return .[];
        line_end := i;
        while line_end < buffer.bytes.count && buffer.bytes[line_end] != #char "\n" { line_end += 1; }
        p := i;
        while p < line_end && (buffer.bytes[p] == #char " " || buffer.bytes[p] == #char "\t") { p += 1; }
        if p < line_end && buffer.bytes[p] == #char "#" {
            p += 1;
            while p < line_end && (buffer.bytes[p] == #char " " || buffer.bytes[p] == #char "\t") { p += 1; }
            directive_start := p;
            while p < line_end && c_is_word_continue(buffer.bytes[p]) { p += 1; }
            directive := string.{ data = buffer.bytes.data+directive_start, count = p-directive_start };
            if directive == "define" {
                while p < line_end && (buffer.bytes[p] == #char " " || buffer.bytes[p] == #char "\t") { p += 1; }
                name_start := p;
                if p < line_end && c_is_word_start(buffer.bytes[p]) {
                    p += 1;
                    while p < line_end && c_is_word_continue(buffer.bytes[p]) { p += 1; }
                    symbol_index := c_add_symbol(buffer,
                        .{ start = name_start, count = p-name_start, kind = .word, lexical_type = .macro },
                        .macro, name_start, xx buffer.bytes.count);
                    array_add(*references, C_Reference.{
                        offset = name_start, count = p-name_start, symbol_index = symbol_index, token_type = .macro,
                    });
                }
            }
        }
        i = line_end+1;
    }
    return references;
}

c_type_hash_in_range :: (buffer: *Buffer, tokens: [] C_Semantic_Token, start: s32, end: s32) -> u64 {
    result: u64;
    saw_aggregate_keyword := false;
    for i: start..end {
        token := tokens[i];
        if token.kind != .word continue;
        word := c_token_text(buffer, token);
        if word == "struct" || word == "union" { saw_aggregate_keyword = true; continue; }
        if saw_aggregate_keyword || token.lexical_type == .type {
            // Builtin types cannot own members; user types can. Keeping their hash is harmless.
            result = c_name_hash(word);
            if !saw_aggregate_keyword && buffer.c_symbol_bucket_heads.count {
                candidate := buffer.c_symbol_bucket_heads[cast(s64)(result & (C_SYMBOL_BUCKET_COUNT-1))];
                while candidate >= 0 {
                    symbol := buffer.c_symbols[candidate];
                    if symbol.kind == .type_definition && symbol.name_hash == result &&
                       c_symbol_name(buffer, symbol) == word && symbol.result_type_hash {
                        result = symbol.result_type_hash;
                        break;
                    }
                    candidate = symbol.next_same_hash;
                }
            }
            if saw_aggregate_keyword return result;
        }
    }
    return result;
}

c_enclosing_scope :: (buffer: *Buffer, tokens: [] C_Semantic_Token, token_index: s32) -> start: s32, end: s32 {
    depth := tokens[token_index].brace_depth;
    if depth <= 0 return 0, xx buffer.bytes.count;
    for #v2 < i: 0..token_index {
        if c_token_is(tokens[i], #char "{") && tokens[i].brace_depth == depth-1 && tokens[i].pair >= 0 {
            return tokens[i].start+1, tokens[tokens[i].pair].start;
        }
    }
    return 0, xx buffer.bytes.count;
}

c_find_statement_start :: (tokens: [] C_Semantic_Token, end_index: s32) -> s32 {
    target_brace := tokens[end_index].brace_depth;
    target_paren := tokens[end_index].paren_depth;
    for #v2 < i: 0..end_index-1 {
        t := tokens[i];
        if c_token_is(t, #char "}") && t.brace_depth == target_brace+1 return i+1;
        if t.brace_depth > target_brace || t.paren_depth > target_paren continue;
        if c_token_is(t, #char ";") || c_token_is(t, #char "{") || c_token_is(t, #char "}") ||
           (target_paren > 0 && (c_token_is(t, #char "(") || c_token_is(t, #char ";"))) return i+1;
    }
    return 0;
}

c_register_declaration_segment :: (buffer: *Buffer, tokens: [] C_Semantic_Token, start: s32, end: s32, kind: C_Symbol_Kind, scope_start: s32, scope_end: s32, owner_hash: u64 = 0) {
    if start >= end return;
    saw_type := false;
    first_declarator := -1;
    type_hash := c_type_hash_in_range(buffer, tokens, start, end-1);
    base_paren := tokens[start].paren_depth;
    base_bracket := tokens[start].bracket_depth;
    aggregate_needs_tag := false;

    for i: start..end-1 {
        token := tokens[i];
        if token.kind != .word continue;
        word := c_token_text(buffer, token);
        if word == "struct" || word == "union" || word == "enum" { saw_type = true; aggregate_needs_tag = true; continue; }
        if aggregate_needs_tag { aggregate_needs_tag = false; continue; }
        // The lexical pass may already know a simple typedef name by the time
        // semantic indexing runs, so its declaration token can itself be .type.
        if kind == .type_definition && saw_type && i == end-1 {
            first_declarator = i;
            break;
        }
        if c_is_declaration_specifier(token, word) { saw_type = true; continue; }
        if saw_type && c_is_declarator_identifier(token, word) {
            first_declarator = i;
            break;
        }
    }
    if !saw_type || first_declarator < 0 return;

    segment_start: s64 = first_declarator;
    while segment_start < end {
        segment_end: s64 = end;
        for i: segment_start..cast(s64)end-1 {
            if c_token_is(tokens[i], #char ",") && tokens[i].paren_depth == base_paren && tokens[i].bracket_depth == base_bracket {
                segment_end = i;
                break;
            }
        }

        candidate: s64 = -1;
        for i: segment_start..segment_end-1 {
            token := tokens[i];
            if c_token_is(token, #char "=") && token.paren_depth == base_paren { break; }
            if token.kind == .word {
                word := c_token_text(buffer, token);
                if c_is_declarator_identifier(token, word) || (kind == .type_definition && i == segment_start) { candidate = i; break; }
            }
        }
        if candidate >= 0 {
            actual_kind := kind;
            symbol_type := type_hash;
            if kind == .struct_member { symbol_type = owner_hash; }
            c_add_symbol(buffer, tokens[candidate], actual_kind, scope_start, scope_end, type_hash = symbol_type, result_type_hash = type_hash);
        }
        if segment_end == end break;
        segment_start = segment_end+1;
    }
}

c_build_semantic_index :: (buffer: *Buffer, cancel_flag: *bool = null) -> completed: bool {
    settings := c_get_settings(buffer);
    if buffer.lang != .C || (!settings.c_parse_functions && !settings.c_parse_variables &&
                             !settings.c_goto_definition && !settings.c_autocomplete) return true;

    #if C_LANGUAGE_FEATURE_TESTS { c_profile_phase_start = current_time_monotonic(); }
    tokens := c_collect_semantic_tokens(buffer, cancel_flag);
    #if C_LANGUAGE_FEATURE_TESTS { c_profile_collect_ms = to_milliseconds(current_time_monotonic()-c_profile_phase_start); c_profile_phase_start = current_time_monotonic(); }
    if !tokens return !c_analysis_cancelled(cancel_flag);

    // The lexical C highlighter intentionally has a broad "word(" fallback.
    // Semantic mode starts from identifiers and only reapplies function color to resolved symbols.
    if settings.c_parse_functions {
        for i: 0..buffer.tokens.count-1 if buffer.tokens[i] == .function then buffer.tokens[i] = .identifier;
    }

    struct_bodies: [..] struct { open: s32; close: s32; owner_hash: u64; };
    struct_bodies.allocator = temp;
    for token, i: tokens {
        if c_analysis_cancelled(cancel_flag) return false;
        if token.kind != .word continue;
        word := c_token_text(buffer, token);
        if word != "struct" && word != "union" && word != "enum" continue;
        j := cast(s32)i+1;
        owner_hash: u64;
        if j < tokens.count && tokens[j].kind == .word {
            owner_hash = c_name_hash(c_token_text(buffer, tokens[j]));
            c_add_symbol(buffer, tokens[j], .type_definition, 0, xx buffer.bytes.count, type_hash = owner_hash, result_type_hash = owner_hash);
            j += 1;
        }
        if j < tokens.count && c_token_is(tokens[j], #char "{") && tokens[j].pair >= 0 {
            close := tokens[j].pair;
            if !owner_hash {
                after := close+1;
                if after < tokens.count && tokens[after].kind == .word then owner_hash = c_name_hash(c_token_text(buffer, tokens[after]));
            }
            if word == "enum" {
                enum_scope_start, enum_scope_end := c_enclosing_scope(buffer, tokens, j);
                expects_constant := true;
                for k: j+1..close-1 {
                    enum_token := tokens[k];
                    if enum_token.brace_depth != tokens[j].brace_depth+1 continue;
                    if c_token_is(enum_token, #char ",") { expects_constant = true; continue; }
                    if expects_constant && enum_token.kind == .word && enum_token.lexical_type == .enum_variant {
                        c_add_symbol(buffer, enum_token, .enum_constant, enum_scope_start, enum_scope_end);
                        expects_constant = false;
                    }
                }
            } else {
                array_add(*struct_bodies, .{ open = j, close = close, owner_hash = owner_hash });
            }

            // Compound typedef aliases live after the closing brace, outside
            // the statement range found by the generic declarator pass:
            // typedef struct Tag { ... } Alias, *AliasPtr;
            statement_start := c_find_statement_start(tokens, xx i);
            aggregate_is_typedef := false;
            for k: statement_start..cast(s32)i {
                if tokens[k].kind == .word && c_token_text(buffer, tokens[k]) == "typedef" {
                    aggregate_is_typedef = true;
                    break;
                }
            }
            if aggregate_is_typedef {
                k := close+1;
                expect_alias := true;
                while k < tokens.count && !c_token_is(tokens[k], #char ";") {
                    alias_token := tokens[k];
                    if c_token_is(alias_token, #char ",") { expect_alias = true; k += 1; continue; }
                    if alias_token.kind == .word && alias_token.lexical_type == .type && expect_alias {
                        c_add_symbol(buffer, alias_token, .type_definition, 0, xx buffer.bytes.count,
                                     type_hash = owner_hash, result_type_hash = owner_hash);
                        expect_alias = false;
                    }
                    k += 1;
                }
            }
        }
    }
    macro_definition_references := c_register_macro_definitions(buffer, cancel_flag);
    if c_analysis_cancelled(cancel_flag) return false;
    #if C_LANGUAGE_FEATURE_TESTS { c_profile_struct_ms = to_milliseconds(current_time_monotonic()-c_profile_phase_start); c_profile_phase_start = current_time_monotonic(); }

    function_statement_ends := NewArray(tokens.count, bool,, allocator = temp);
    if settings.c_parse_functions {
        for token, i: tokens {
            if c_analysis_cancelled(cancel_flag) return false;
            if token.kind != .word || i+1 >= tokens.count || !c_token_is(tokens[i+1], #char "(") || tokens[i+1].pair < 0 continue;
            if token.brace_depth != 0 || c_is_control_word(c_token_text(buffer, token)) continue;
            open := cast(s32)i+1;
            close := tokens[open].pair;
            statement_start := c_find_statement_start(tokens, xx i);
            saw_type := false;
            saw_typedef := false;
            invalid_prefix := false;
            for k: statement_start..cast(s32)i-1 {
                if c_token_is(tokens[k], #char "=") && tokens[k].paren_depth == token.paren_depth { invalid_prefix = true; break; }
                if tokens[k].kind == .word {
                    prefix_word := c_token_text(buffer, tokens[k]);
                    if prefix_word == "typedef" then saw_typedef = true;
                    if c_is_declaration_specifier(tokens[k], prefix_word) then saw_type = true;
                }
            }
            if !saw_type || saw_typedef || invalid_prefix continue;

            after := close+1;
            while after < tokens.count && tokens[after].kind == .word && c_is_attribute_introducer(c_token_text(buffer, tokens[after])) {
                after += 1;
                if after < tokens.count && c_token_is(tokens[after], #char "(") && tokens[after].pair >= 0 then after = tokens[after].pair+1;
            }
            if after >= tokens.count || (!c_token_is(tokens[after], #char "{") && !c_token_is(tokens[after], #char ";")) continue;

            c_add_symbol(buffer, token, .function, 0, xx buffer.bytes.count, result_type_hash = c_type_hash_in_range(buffer, tokens, statement_start, cast(s32)(i-1)));
            if c_token_is(tokens[after], #char ";") then function_statement_ends[after] = true;

            param_scope_start := tokens[open].start;
            param_scope_end := tokens[close].start;
            if c_token_is(tokens[after], #char "{") && tokens[after].pair >= 0 {
                param_scope_end = tokens[tokens[after].pair].start;
            }
            segment_start := open+1;
            for k: open+1..close {
                is_end := k == close || (c_token_is(tokens[k], #char ",") && tokens[k].paren_depth == tokens[open].paren_depth+1);
                if is_end {
                    c_register_declaration_segment(buffer, tokens, segment_start, k, .parameter, param_scope_start, param_scope_end);
                    segment_start = k+1;
                }
            }
        }
    }
    #if C_LANGUAGE_FEATURE_TESTS { c_profile_function_ms = to_milliseconds(current_time_monotonic()-c_profile_phase_start); c_profile_phase_start = current_time_monotonic(); }

    // Typedef names participate in navigation/completion even when variable
    // highlighting itself is disabled.
    for token, semi_index: tokens {
        if c_analysis_cancelled(cancel_flag) return false;
        if !c_token_is(token, #char ";") continue;
        start := c_find_statement_start(tokens, xx semi_index);
        if start >= semi_index continue;
        is_typedef := false;
        for k: start..cast(s32)semi_index-1 {
            if tokens[k].kind == .word && c_token_text(buffer, tokens[k]) == "typedef" { is_typedef = true; break; }
        }
        if is_typedef {
            c_register_declaration_segment(buffer, tokens, start, xx semi_index, .type_definition, 0, xx buffer.bytes.count);
        }
    }

    if settings.c_parse_variables {
        for token, semi_index: tokens {
            if c_analysis_cancelled(cancel_flag) return false;
            if !c_token_is(token, #char ";") continue;
            start := c_find_statement_start(tokens, xx semi_index);
            if start >= semi_index continue;
            // Function declarations already own this statement.
            if function_statement_ends[semi_index] continue;
            is_typedef := false;
            for k: start..cast(s32)semi_index-1 {
                if tokens[k].kind == .word && c_token_text(buffer, tokens[k]) == "typedef" { is_typedef = true; break; }
            }
            if is_typedef continue;

            kind := ifx token.brace_depth == 0 then C_Symbol_Kind.global_variable else C_Symbol_Kind.local_variable;
            scope_start, scope_end := c_enclosing_scope(buffer, tokens, xx semi_index);
            owner_hash: u64;
            for body: struct_bodies {
                if semi_index > body.open && semi_index < body.close && token.brace_depth == tokens[body.open].brace_depth+1 {
                    kind = .struct_member;
                    owner_hash = body.owner_hash;
                    scope_start = tokens[body.open].start;
                    scope_end = tokens[body.close].start;
                    break;
                }
            }
            c_register_declaration_segment(buffer, tokens, start, xx semi_index, kind, scope_start, scope_end, owner_hash);
        }
    }
    #if C_LANGUAGE_FEATURE_TESTS { c_profile_variable_ms = to_milliseconds(current_time_monotonic()-c_profile_phase_start); c_profile_phase_start = current_time_monotonic(); }

    // Resolve every occurrence against the narrowest visible declaration. Keep
    // the result beside the semantic token so chained members are O(1), rather
    // than searching the growing reference list backwards on every access.
    resolved_symbol_by_token := NewArray(tokens.count, s32,, allocator = temp);
    memset(resolved_symbol_by_token.data, 0xff, resolved_symbol_by_token.count*size_of(s32));
    macro_reference_index: s64;
    for token, token_index: tokens {
        if c_analysis_cancelled(cancel_flag) return false;
        while macro_reference_index < macro_definition_references.count &&
              macro_definition_references[macro_reference_index].offset < token.start {
            add(*buffer.c_references, macro_definition_references[macro_reference_index]);
            macro_reference_index += 1;
        }
        if token.kind != .word continue;
        name := c_token_text(buffer, token);
        hash := c_name_hash(name);
        member_access := token_index > 0 && (c_token_is(tokens[token_index-1], #char ".") || c_token_is(tokens[token_index-1], #char "-", #char ">"));

        best: s32 = -1;
        best_scope: s32 = -1;
        best_definition: s32 = -1;
        if member_access {
            owner_type: u64;
            if token_index >= 2 && tokens[token_index-2].kind == .word {
                base_token := tokens[token_index-2];
                base_symbol_index := resolved_symbol_by_token[token_index-2];
                if base_symbol_index >= 0 {
                    owner_type = buffer.c_symbols[base_symbol_index].result_type_hash;
                }
                base_hash := c_name_hash(c_token_text(buffer, tokens[token_index-2]));
                if !owner_type {
                    symbol_index := ifx buffer.c_symbol_bucket_heads.count then buffer.c_symbol_bucket_heads[cast(s64)(base_hash & (C_SYMBOL_BUCKET_COUNT-1))] else -1;
                    while symbol_index >= 0 {
                        symbol := buffer.c_symbols[symbol_index];
                        if symbol.name_hash != base_hash || c_symbol_name(buffer, symbol) != c_token_text(buffer, tokens[token_index-2]) || symbol.kind == .struct_member {
                            symbol_index = symbol.next_same_hash;
                            continue;
                        }
                        if symbol.scope_start <= token.start && token.start <= symbol.scope_end && symbol.definition_offset <= token.start {
                            if symbol.scope_start >= best_scope { owner_type = symbol.result_type_hash; best_scope = symbol.scope_start; }
                        }
                        symbol_index = symbol.next_same_hash;
                    }
                }
            }
            symbol_index := ifx buffer.c_symbol_bucket_heads.count then buffer.c_symbol_bucket_heads[cast(s64)(hash & (C_SYMBOL_BUCKET_COUNT-1))] else -1;
            while symbol_index >= 0 {
                symbol := buffer.c_symbols[symbol_index];
                if symbol.kind == .struct_member && symbol.name_hash == hash && c_symbol_name(buffer, symbol) == name && symbol.type_hash == owner_type {
                    best = symbol_index;
                    break;
                }
                symbol_index = symbol.next_same_hash;
            }
        } else {
            next_is_call := token_index+1 < tokens.count && c_token_is(tokens[token_index+1], #char "(");
            symbol_index := ifx buffer.c_symbol_bucket_heads.count then buffer.c_symbol_bucket_heads[cast(s64)(hash & (C_SYMBOL_BUCKET_COUNT-1))] else -1;
            while symbol_index >= 0 {
                symbol := buffer.c_symbols[symbol_index];
                if symbol.name_hash != hash || c_symbol_name(buffer, symbol) != name ||
                   (symbol.kind == .struct_member && symbol.definition_offset != token.start) {
                    symbol_index = symbol.next_same_hash;
                    continue;
                }
                at_definition := symbol.definition_offset == token.start;
                eligible_kind := c_symbol_matches_token(symbol.kind, token.lexical_type, next_is_call) || at_definition;
                declared_before_use := symbol.kind == .function || symbol.definition_offset <= token.start;
                better := symbol.scope_start > best_scope || (symbol.scope_start == best_scope && symbol.definition_offset > best_definition);
                visible_here := at_definition || (symbol.scope_start <= token.start && token.start <= symbol.scope_end);
                if eligible_kind && declared_before_use && visible_here && better {
                    best = symbol_index;
                    best_scope = symbol.scope_start;
                    best_definition = symbol.definition_offset;
                }
                symbol_index = symbol.next_same_hash;
            }
        }
        if best >= 0 {
            type := c_symbol_token_type(buffer.c_symbols[best].kind);
            resolved_symbol_by_token[token_index] = best;
            memset(buffer.tokens.data + token.start, xx type, token.count);
            add(*buffer.c_references, .{ offset = token.start, count = token.count, symbol_index = best, token_type = type });
        }
    }
    while macro_reference_index < macro_definition_references.count {
        add(*buffer.c_references, macro_definition_references[macro_reference_index]);
        macro_reference_index += 1;
    }
    buffer.c_analysis_revision += 1;
    #if C_LANGUAGE_FEATURE_TESTS { c_profile_resolve_ms = to_milliseconds(current_time_monotonic()-c_profile_phase_start); }
    return true;
}

c_reset_semantic_index :: (buffer: *Buffer) {
    c_semantic_cancel(buffer);
    buffer.c_semantic_active_work = null;
    for buffer.c_diagnostics free(it.message,, allocator = focus_allocator);
    reset_keeping_memory(*buffer.c_symbols);
    reset_keeping_memory(*buffer.c_symbol_bucket_heads);
    reset_keeping_memory(*buffer.c_references);
    reset_keeping_memory(*buffer.c_diagnostics);
}

c_free_semantic_index :: (buffer: *Buffer) {
    c_semantic_cancel(buffer);
    buffer.c_semantic_active_work = null;
    c_compiler_cancel(buffer);
    for buffer.c_diagnostics free(it.message,, allocator = focus_allocator);
    reset(*buffer.c_symbols);
    reset(*buffer.c_symbol_bucket_heads);
    reset(*buffer.c_references);
    reset(*buffer.c_diagnostics);
}

c_reference_at_offset :: (buffer: *Buffer, offset: s32) -> *C_Reference {
    low: s32;
    high := cast(s32) buffer.c_references.count;
    while low < high {
        middle := (low+high)/2;
        ref := *buffer.c_references[middle];
        if offset < ref.offset then high = middle;
        else if offset >= ref.offset+ref.count then low = middle+1;
        else return ref;
    }
    return null;
}

c_action_goto_definition :: () {
    editor, buffer := get_active_editor_and_buffer();
    if !editor || !buffer || buffer.lang != .C || !c_get_settings(buffer).c_goto_definition return;
    cursor := get_main_cursor(editor);
    ref := c_reference_at_offset(buffer, cursor.pos);
    if !ref && cursor.pos > 0 then ref = c_reference_at_offset(buffer, cursor.pos-1);
    if ref {
        if ref.symbol_index < 0 || ref.symbol_index >= buffer.c_symbols.count return;
        definition_offset := buffer.c_symbols[ref.symbol_index].definition_offset;
        history_record_navigation_jump(editor.buffer_id, definition_offset);
        target_cursor := leave_only_main_cursor(editor);
        target_cursor.pos = definition_offset;
        target_cursor.sel = target_cursor.pos;
        target_cursor.col_wanted = -1;
        editor.cursor_moved = true;
        editor.scroll_to_cursor = .yes;
        history_reset_last_seen_cursor();
        return;
    }

    // Cross-buffer references are resolved on demand. This keeps every normal
    // reference compact while still allowing F12 into scanned headers.
    offset := cursor.pos;
    if offset >= buffer.bytes.count || !c_is_word_continue(buffer.bytes[offset]) then offset -= 1;
    if offset < 0 || !c_is_word_continue(buffer.bytes[offset]) {
        add_user_warning("No registered C definition at the caret", dismiss_in_seconds = 2);
        return;
    }
    start := offset;
    end := offset+1;
    while start > 0 && c_is_word_continue(buffer.bytes[start-1]) { start -= 1; }
    while end < buffer.bytes.count && c_is_word_continue(buffer.bytes[end]) { end += 1; }
    name := string.{ data = buffer.bytes.data+start, count = end-start };
    hash := c_name_hash(name);
    lexical_type := ifx start < buffer.tokens.count then buffer.tokens[start] else Token_Type.identifier;
    after := end;
    while after < buffer.bytes.count && (buffer.bytes[after] == #char " " || buffer.bytes[after] == #char "\t") { after += 1; }
    next_is_call := after < buffer.bytes.count && buffer.bytes[after] == #char "(";
    for *candidate_buffer, candidate_buffer_id: open_buffers {
        if candidate_buffer == buffer || !candidate_buffer.c_symbol_bucket_heads.count continue;
        symbol_index := candidate_buffer.c_symbol_bucket_heads[cast(s64)(hash & (C_SYMBOL_BUCKET_COUNT-1))];
        while symbol_index >= 0 {
            symbol := candidate_buffer.c_symbols[symbol_index];
            if symbol.name_hash == hash && c_symbol_name(candidate_buffer, symbol) == name &&
               c_symbol_matches_token(symbol.kind, lexical_type, next_is_call) {
                history_record_navigation_jump(candidate_buffer_id, symbol.definition_offset);
                editors_open_buffer(candidate_buffer_id);
                target_editor, _ := get_active_editor_and_buffer();
                target_cursor := leave_only_main_cursor(target_editor);
                target_cursor.pos = symbol.definition_offset;
                target_cursor.sel = target_cursor.pos;
                target_cursor.col_wanted = -1;
                target_editor.cursor_moved = true;
                target_editor.scroll_to_cursor = .yes;
                history_reset_last_seen_cursor();
                return;
            }
            symbol_index = symbol.next_same_hash;
        }
    }
    add_user_warning("No registered C definition for '%'", name, dismiss_in_seconds = 2);
}

c_clear_completion_candidates :: (state: *C_Completion_State) {
    for state.candidates free(it.name,, allocator = focus_allocator);
    reset_keeping_memory(*state.candidates);
}

c_close_completion :: (editor: *Editor) {
    if !editor.completion.active && editor.completion.candidates.count == 0 return;
    c_clear_completion_candidates(*editor.completion);
    editor.completion.active = false;
    editor.completion.selected = 0;
}

c_completion_find_name :: (state: *C_Completion_State, name: string) -> *C_Completion_Candidate {
    for *candidate: state.candidates if candidate.name == name return candidate;
    return null;
}

c_completion_expectation :: (buffer: *Buffer, prefix_start: s32, cursor: s32) -> C_Completion_Expectation {
    right := cursor;
    while right < buffer.bytes.count && (buffer.bytes[right] == #char " " || buffer.bytes[right] == #char "\t") { right += 1; }
    if right < buffer.bytes.count && buffer.bytes[right] == #char "(" return .function;

    left := prefix_start-1;
    while left >= 0 && (buffer.bytes[left] == #char " " || buffer.bytes[left] == #char "\t" || buffer.bytes[left] == #char "\r" || buffer.bytes[left] == #char "\n") { left -= 1; }
    if left < 0 return .any;
    if buffer.bytes[left] == #char "." ||
       (buffer.bytes[left] == #char ">" && left > 0 && buffer.bytes[left-1] == #char "-") return .member;
    if buffer.bytes[left] == #char "#" return .macro;

    lexical_type := ifx left < buffer.tokens.count then buffer.tokens[left] else Token_Type.default;
    if lexical_type == .type return .variable;

    word_end := left+1;
    word_start := left;
    while word_start > 0 && c_is_word_continue(buffer.bytes[word_start-1]) { word_start -= 1; }
    left_word := string.{ data = buffer.bytes.data+word_start, count = word_end-word_start };
    if left_word == "struct" || left_word == "union" || left_word == "enum" || left_word == "typedef" return .type;
    if left_word == "return" || left_word == "case" || left_word == "sizeof" return .value;

    // Declarators commonly put pointer stars, qualifiers, or earlier names
    // between the declared type and the word currently being completed. Walk
    // back to the statement boundary so `Widget *wid` and `int first, sec`
    // receive the same variable-first ordering as the simple `Widget wid` case.
    scan := left;
    while scan >= 0 {
        c := buffer.bytes[scan];
        if c == #char ";" || c == #char "{" || c == #char "}" || c == #char "(" || c == #char ")" break;
        if c == #char "=" return .any;
        if scan < buffer.tokens.count && buffer.tokens[scan] == .type return .variable;
        scan -= 1;
    }
    return .any;
}

c_completion_priority :: (kind: C_Symbol_Kind, expectation: C_Completion_Expectation) -> u8 {
    if expectation == {
        case .variable;
            if kind == .local_variable || kind == .parameter return 0;
            if kind == .global_variable return 1;
            return 8;
        case .type;      if kind == .type_definition return 0; return 8;
        case .member;    if kind == .struct_member return 0; return 8;
        case .function;
            if kind == .function return 0;
            if kind == .macro return 1;
            return 8;
        case .value;
            if kind == .local_variable || kind == .parameter || kind == .global_variable ||
               kind == .enum_constant || kind == .macro return 0;
            if kind == .function return 1;
            return 8;
        case .macro;     if kind == .macro return 0; return 8;
        case .any;
            if kind == .local_variable || kind == .parameter return 0;
            return 1;
    }
    return 8;
}

c_compare_completion_candidates :: (a: C_Completion_Candidate, b: C_Completion_Candidate) -> s64 {
    if a.priority != b.priority return cast(s64)a.priority-cast(s64)b.priority;
    return compare_strings(a.name, b.name);
}

c_action_autocomplete :: () {
    editor, buffer := get_active_editor_and_buffer();
    if !editor || !buffer || buffer.lang != .C || !c_get_settings(buffer).c_autocomplete return;
    cursor := get_main_cursor(editor);

    if editor.completion.active {
        if editor.completion.candidates.count then editor.completion.selected = (editor.completion.selected+1) % editor.completion.candidates.count;
        return;
    }

    start := cursor.pos;
    while start > 0 && c_is_word_continue(buffer.bytes[start-1]) { start -= 1; }
    if start == cursor.pos return;
    prefix := string.{ data = buffer.bytes.data+start, count = cursor.pos-start };
    expectation := c_completion_expectation(buffer, start, cursor.pos);
    c_clear_completion_candidates(*editor.completion);

    for *candidate_buffer: open_buffers {
        for symbol: candidate_buffer.c_symbols {
            if symbol.kind == .local_variable || symbol.kind == .parameter {
                if candidate_buffer != buffer || !(symbol.scope_start <= cursor.pos && cursor.pos <= symbol.scope_end) continue;
            }
            name := c_symbol_name(candidate_buffer, symbol);
            if name.count <= prefix.count || !begins_with(name, prefix) continue;
            priority := c_completion_priority(symbol.kind, expectation);
            existing := c_completion_find_name(*editor.completion, name);
            if existing {
                if priority < existing.priority { existing.priority = priority; existing.kind = symbol.kind; }
                continue;
            }
            add(*editor.completion.candidates, .{
                name = copy_string(name,, allocator = focus_allocator), kind = symbol.kind, priority = priority,
            });
        }
    }
    if editor.completion.candidates.count == 0 return;
    quick_sort(to_view(editor.completion.candidates), c_compare_completion_candidates);
    editor.completion.prefix_start = start;
    editor.completion.selected = 0;
    editor.completion.active = true;
}

c_get_completion_suffix :: (editor: *Editor, buffer: *Buffer) -> string {
    if !editor.completion.active || editor.completion.candidates.count == 0 return "";
    cursor := get_main_cursor(editor);
    prefix_count := cursor.pos-editor.completion.prefix_start;
    candidate := editor.completion.candidates[editor.completion.selected].name;
    if prefix_count < 0 || prefix_count >= candidate.count return "";
    return .{ data = candidate.data+prefix_count, count = candidate.count-prefix_count };
}

c_language_services_note_edit :: (notification: Buffer.Edit_Notification) {
    if notification.buffer_id < 0 return;
    for *editor: open_editors if editor.buffer_id == notification.buffer_id then c_close_completion(editor);
}

c_language_services_buffer_changed :: (buffer: *Buffer, buffer_id: s64) {
    // The asynchronous compiler runner is updated once per frame from the main loop.
    if buffer.lang == .C && c_get_settings(buffer).c_compiler_syntax_check {
        c_compiler_request(buffer, buffer_id);
    }
}

C_Semantic_Work :: struct {
    buffer_id: s64;
    generation: u64;
    settings: Settings;
    buffer: Buffer;
    cancelled: bool;
    finished: bool;
    state: s32; // 0 queued, 1 running, 2 finished, 3 abandoned before starting
}

c_semantic_thread_group: Thread_Group;
c_semantic_outstanding: [..] *C_Semantic_Work;

c_semantic_init :: () {
    if c_semantic_thread_group.initted return;
    c_semantic_thread_group = .{};
    init(*c_semantic_thread_group, num_threads = 1, group_proc = c_semantic_threadproc);
    start(*c_semantic_thread_group);
}

c_semantic_cancel :: (buffer: *Buffer) {
    work := buffer.c_semantic_active_work;
    if !work return;
    atomic_write(*work.cancelled, true);
    abandoned, _ := compare_and_swap(*work.state, 0, 3);
    if abandoned then c_semantic_release_payload(work);
}

c_reset_semantic_symbols :: (buffer: *Buffer) {
    reset_keeping_memory(*buffer.c_symbols);
    reset_keeping_memory(*buffer.c_symbol_bucket_heads);
    reset_keeping_memory(*buffer.c_references);
}

c_schedule_semantic_index :: (buffer: *Buffer) {
    #if C_LANGUAGE_FEATURE_TESTS { if c_test_suppress_semantic_schedule return; }
    settings := c_get_settings(buffer);
    needed := buffer.lang == .C && (settings.c_parse_functions || settings.c_parse_variables ||
                                    settings.c_goto_definition || settings.c_autocomplete);
    if !needed {
        c_semantic_cancel(buffer);
        buffer.c_semantic_active_work = null;
        c_reset_semantic_symbols(buffer);
        return;
    }
    // Workspace scan workers need a complete local index before returning.
    // Interactive buffers enqueue a cancelable snapshot on every edit.
    if !workspace_scan_complete {
        c_build_semantic_index(buffer);
        return;
    }

    buffer_id: s64 = -1;
    for *candidate, candidate_id: open_buffers {
        if candidate == buffer { buffer_id = candidate_id; break; }
    }
    if buffer_id < 0 {
        c_build_semantic_index(buffer);
        return;
    }

    // Command-line files can be tokenized before init_build_system() runs.
    // Lazy initialization keeps the immediate-on-edit scheduler valid during
    // that startup window as well as after workspace initialization.
    c_semantic_init();
    c_semantic_cancel(buffer);
    buffer.c_semantic_edit_generation += 1;
    c_reset_semantic_symbols(buffer);

    work := New(C_Semantic_Work,, allocator = focus_allocator);
    work.buffer_id = buffer_id;
    work.generation = buffer.c_semantic_edit_generation;
    work.settings = settings.*;
    work.buffer.settings = *work.settings;
    work.buffer.lang = .C;
    resize(*work.buffer.bytes, buffer.bytes.count);
    if buffer.bytes.count then memcpy(work.buffer.bytes.data, buffer.bytes.data, buffer.bytes.count);
    resize(*work.buffer.tokens, buffer.tokens.count);
    if buffer.tokens.count then memcpy(work.buffer.tokens.data, buffer.tokens.data, buffer.tokens.count*size_of(Token_Type));

    buffer.c_semantic_active_work = work;
    array_add(*c_semantic_outstanding, work);
    add_work(*c_semantic_thread_group, work);
}

c_semantic_threadproc :: (group: *Thread_Group, thread: *Thread, work_ptr: *void) -> Thread_Continue_Status {
    work := cast(*C_Semantic_Work) work_ptr;
    defer platform_wake_up_main_thread();
    defer atomic_write(*work.finished, true);
    defer atomic_write(*work.state, 2);
    claimed, _ := compare_and_swap(*work.state, 0, 1);
    if claimed && !atomic_read(*work.cancelled) then c_build_semantic_index(*work.buffer, *work.cancelled);
    return .CONTINUE;
}

c_semantic_release_payload :: (work: *C_Semantic_Work) {
    // free_user_type_index also releases the semantic arrays owned by the
    // snapshot, so this remains safe when cancellation already emptied it.
    free_user_type_index(*work.buffer);
    reset(*work.buffer.bytes);
    reset(*work.buffer.tokens);
}

c_semantic_free_work :: (work: *C_Semantic_Work) {
    c_semantic_release_payload(work);
    free(work,, allocator = focus_allocator);
}

c_semantic_remove_outstanding :: (work: *C_Semantic_Work) {
    for c_semantic_outstanding {
        if it == work { remove it; return; }
    }
}

c_semantic_update :: () {
    if !c_semantic_thread_group.initted return;
    for completed: get_completed_work(*c_semantic_thread_group) {
        work := cast(*C_Semantic_Work) completed;
        cancelled := atomic_read(*work.cancelled);
        if work.buffer_id >= 0 && work.buffer_id < open_buffers.count {
            buffer := *open_buffers[work.buffer_id];
            is_current := buffer.c_semantic_active_work == work && buffer.c_semantic_edit_generation == work.generation;
            if buffer.c_semantic_active_work == work then buffer.c_semantic_active_work = null;
            if is_current && !cancelled && work.buffer.c_analysis_revision {
                resize(*buffer.c_symbols, work.buffer.c_symbols.count);
                if buffer.c_symbols.count then memcpy(buffer.c_symbols.data, work.buffer.c_symbols.data, buffer.c_symbols.count*size_of(C_Symbol));
                resize(*buffer.c_symbol_bucket_heads, work.buffer.c_symbol_bucket_heads.count);
                if buffer.c_symbol_bucket_heads.count then memcpy(buffer.c_symbol_bucket_heads.data, work.buffer.c_symbol_bucket_heads.data, buffer.c_symbol_bucket_heads.count*size_of(s32));
                resize(*buffer.c_references, work.buffer.c_references.count);
                if buffer.c_references.count then memcpy(buffer.c_references.data, work.buffer.c_references.data, buffer.c_references.count*size_of(C_Reference));
                if buffer.tokens.count == work.buffer.tokens.count && buffer.tokens.count then memcpy(buffer.tokens.data, work.buffer.tokens.data, buffer.tokens.count*size_of(Token_Type));
                buffer.c_analysis_revision += 1;
                redraw_requested = true;
            }
        }
        c_semantic_remove_outstanding(work);
        c_semantic_free_work(work);
    }
}

c_semantic_deinit :: () {
    for work: c_semantic_outstanding atomic_write(*work.cancelled, true);
    if c_semantic_thread_group.initted then shutdown(*c_semantic_thread_group);
    for work: c_semantic_outstanding c_semantic_free_work(work);
    array_reset(*c_semantic_outstanding);
    c_semantic_thread_group = .{};
}

C_Compiler_Work :: struct {
    buffer_id: s64;
    generation: u64;
    contents: string;
    original_directory: string;
    executable: string;
    parameters: string;
    temp_file: string;
    output: string;
    process: Process;
    cancelled: bool;
    finished: bool;
    launched: bool;
    state: s32; // 0 queued, 1 running, 2 finished, 3 abandoned before starting
}

c_compiler_thread_group: Thread_Group;
c_compiler_outstanding: [..] *C_Compiler_Work;
c_compiler_warned_launch_failure := false;

c_compiler_init :: () {
    if c_compiler_thread_group.initted return;
    c_compiler_thread_group = .{};
    init(*c_compiler_thread_group, num_threads = 1, group_proc = c_compiler_threadproc);
    start(*c_compiler_thread_group);
}

c_compiler_deinit :: () {
    for *buffer: open_buffers {
        work := buffer.c_compiler_active_work;
        if !work continue;
        atomic_write(*work.cancelled, true);
        if atomic_read(*work.launched) && !atomic_read(*work.finished) then kill_process(*work.process);
    }
    if c_compiler_thread_group.initted then shutdown(*c_compiler_thread_group);
    for work: c_compiler_outstanding c_compiler_free_work(work);
    array_reset(*c_compiler_outstanding);
    c_compiler_thread_group = .{};
}

c_compiler_cancel :: (buffer: *Buffer) {
    work := buffer.c_compiler_active_work;
    if !work return;
    atomic_write(*work.cancelled, true);
    abandoned, _ := compare_and_swap(*work.state, 0, 3);
    if abandoned {
        c_compiler_release_payload(work);
    } else if atomic_read(*work.launched) && !atomic_read(*work.finished) {
        kill_process(*work.process);
    }
    buffer.c_compiler_active_work = null;
}

c_compiler_request :: (buffer: *Buffer, buffer_id: s64) {
    c_compiler_init();
    c_compiler_cancel(buffer);
    buffer.c_compiler_edit_generation += 1;
    c_compiler_clear_diagnostics(buffer);
    settings := c_get_settings(buffer);
    if buffer.lang != .C || !settings.c_compiler_syntax_check || !buffer.has_file {
        buffer.c_compiler_active_work = null;
        return;
    }

    work := New(C_Compiler_Work,, allocator = focus_allocator);
    work.buffer_id = buffer_id;
    work.generation = buffer.c_compiler_edit_generation;
    work.contents = copy_string(to_string(buffer.bytes),, allocator = focus_allocator);
    work.original_directory = copy_string(get_parent_dir_path(buffer.file.full_path),, allocator = focus_allocator);
    work.executable = copy_string(settings.c_compiler_executable,, allocator = focus_allocator);
    work.parameters = copy_string(settings.c_compiler_syntax_check_parameters,, allocator = focus_allocator);
    work.temp_file = sprint("%/focus-compiler-%-%.c", temp_dir, buffer_id, work.generation,, allocator = focus_allocator);

    buffer.c_compiler_active_work = work;
    array_add(*c_compiler_outstanding, work);
    add_work(*c_compiler_thread_group, work);
}

c_compiler_threadproc :: (group: *Thread_Group, thread: *Thread, work_ptr: *void) -> Thread_Continue_Status {
    work := cast(*C_Compiler_Work) work_ptr;
    defer platform_wake_up_main_thread();
    defer atomic_write(*work.finished, true);
    defer atomic_write(*work.state, 2);
    claimed, _ := compare_and_swap(*work.state, 0, 1);
    if claimed then c_compiler_execute_work(work);
    return .CONTINUE;
}

c_compiler_execute_work :: (work: *C_Compiler_Work) {
    if atomic_read(*work.cancelled) return;
    if !write_entire_file(work.temp_file, work.contents) return;
    defer file_delete(work.temp_file);
    if atomic_read(*work.cancelled) return;

    args: [..] string;
    args.allocator = temp;
    array_add(*args, work.executable);
    for arg: break_command_into_strings(work.parameters) array_add(*args, arg);
    array_add(*args, work.temp_file);

    launched := create_process_with_single_output_pipe(*work.process, ..args, work.original_directory);
    atomic_write(*work.launched, launched);
    if !launched return;
    defer deinit(*work.process);
    if atomic_read(*work.cancelled) { kill_process(*work.process); return; }

    output: String_Builder;
    init_string_builder(*output);
    while true {
        output_buffer: [16 * 1024] u8;
        success, count := read_from_process(*work.process, output_buffer);
        if count then append(*output, to_string(output_buffer.data, count));
        if atomic_read(*work.cancelled) { kill_process(*work.process); reset(*output); return; }
        if !success || work.process.output.eof break;
    }
    output_string := builder_to_string(*output);
    work.output = copy_string(output_string,, allocator = focus_allocator);
    free(output_string);
}

c_compiler_clear_diagnostics :: (buffer: *Buffer) {
    for buffer.c_diagnostics free(it.message,, allocator = focus_allocator);
    reset_keeping_memory(*buffer.c_diagnostics);
}

c_compiler_parse_output :: (buffer: *Buffer, work: *C_Compiler_Work) {
    c_compiler_clear_diagnostics(buffer);
    if !buffer.bytes.count return;

    normalized_temp_file := replace(work.temp_file, "\\", "/");
    for raw_line: split(work.output, cast(u8)#char "\n",, temp) {
        line := trim(replace(raw_line, "\\", "/"), " \r\n");
        if !begins_with(line, normalized_temp_file) continue;
        advance(*line, normalized_temp_file.count);
        line = trim_left(line, ":");

        found, line_string, remainder := split_from_left(line, cast(u8)#char ":",, temp);
        if !found continue;
        found_col, col_string, after_col := split_from_left(remainder, cast(u8)#char ":",, temp);
        if !found_col continue;
        remainder = after_col;
        line_number, line_ok := parse_int(*line_string);
        column_number, col_ok := parse_int(*col_string);
        if !line_ok || !col_ok || line_number <= 0 || line_number > buffer.line_starts.count continue;

        remainder = trim_left(remainder, " ");
        severity_is_error := begins_with(remainder, "error:") || begins_with(remainder, "fatal error:");
        if !severity_is_error continue;
        found_message, _, message := split_from_left(remainder, cast(u8)#char ":",, temp);
        if !found_message then message = remainder;
        message = trim(message);

        line_start: s32 = buffer.line_starts[line_number-1];
        line_end: s32 = ifx line_number < buffer.line_starts.count then buffer.line_starts[line_number] else xx buffer.bytes.count;
        offset: s32 = clamp(line_start + cast(s32)column_number-1, 0, cast(s32)buffer.bytes.count-1);
        start := offset;
        while start > line_start && c_is_word_continue(buffer.bytes[start-1]) { start -= 1; }
        end := offset;
        while end < line_end && c_is_word_continue(buffer.bytes[end]) { end += 1; }
        if end == start then end = min(start+1, cast(s32)buffer.bytes.count);
        add(*buffer.c_diagnostics, .{
            offset = start, count = max(end-start, 1), severity = .error,
            message = copy_string(message,, allocator = focus_allocator),
        });
    }
    buffer.c_diagnostic_revision = work.generation;
}

c_compiler_release_payload :: (work: *C_Compiler_Work) {
    free(work.contents,, allocator = focus_allocator);
    free(work.original_directory,, allocator = focus_allocator);
    free(work.executable,, allocator = focus_allocator);
    free(work.parameters,, allocator = focus_allocator);
    free(work.temp_file,, allocator = focus_allocator);
    free(work.output,, allocator = focus_allocator);
    work.contents = "";
    work.original_directory = "";
    work.executable = "";
    work.parameters = "";
    work.temp_file = "";
    work.output = "";
}

c_compiler_free_work :: (work: *C_Compiler_Work) {
    c_compiler_release_payload(work);
    free(work,, allocator = focus_allocator);
}

c_compiler_remove_outstanding :: (work: *C_Compiler_Work) {
    for c_compiler_outstanding {
        if it == work { remove it; return; }
    }
}

c_compiler_update :: () {
    if !c_compiler_thread_group.initted return;
    completed := get_completed_work(*c_compiler_thread_group);
    for completed {
        work := cast(*C_Compiler_Work) it;
        cancelled := atomic_read(*work.cancelled);
        if !cancelled && !work.launched {
            if !c_compiler_warned_launch_failure {
                add_user_warning("Could not launch '%' for C syntax checking", work.executable, dismiss_in_seconds = 8);
                c_compiler_warned_launch_failure = true;
            }
        } else if work.buffer_id >= 0 && work.buffer_id < open_buffers.count {
            buffer := *open_buffers[work.buffer_id];
            if buffer.c_compiler_active_work == work then buffer.c_compiler_active_work = null;
            if !cancelled && buffer.c_compiler_edit_generation == work.generation then c_compiler_parse_output(buffer, work);
        }
        c_compiler_remove_outstanding(work);
        c_compiler_free_work(work);
    }
}

#if C_LANGUAGE_FEATURE_TESTS {
    c_test_suppress_semantic_schedule: bool;
    c_profile_phase_start: Apollo_Time;
    c_profile_collect_ms: s64;
    c_profile_struct_ms: s64;
    c_profile_function_ms: s64;
    c_profile_variable_ms: s64;
    c_profile_resolve_ms: s64;

    c_test_analyze :: (source: string, parse_functions := true, parse_variables := true) -> Buffer {
        buffer: Buffer;
        settings: Settings;
        settings.c_parse_functions = parse_functions;
        settings.c_parse_variables = parse_variables;
        settings.c_goto_definition = parse_functions || parse_variables;
        settings.c_autocomplete = parse_functions || parse_variables;
        buffer.settings = *settings;
        buffer.lang = .C;
        insert_at(*buffer.bytes, 0, cast([]u8)source);
        resize(*buffer.tokens, source.count);
        memset(buffer.tokens.data, 0, buffer.tokens.count);
        c_test_suppress_semantic_schedule = true;
        tokenize_c(*buffer);
        c_test_suppress_semantic_schedule = false;
        c_build_semantic_index(*buffer);
        return buffer;
    }

    c_test_free_buffer :: (buffer: *Buffer) {
        free_user_type_index(buffer);
        reset(*buffer.bytes);
        reset(*buffer.tokens);
        reset(*buffer.line_starts);
    }

    c_test_find :: (source: string, needle: string, occurrence := 0) -> s32 {
        if !needle return -1;
        seen := 0;
        for i: 0..source.count-needle.count {
            candidate := string.{ data = source.data+i, count = needle.count };
            if candidate == needle {
                if seen == occurrence return cast(s32)i;
                seen += 1;
            }
        }
        return -1;
    }

    c_test_has_symbol :: (buffer: *Buffer, name: string, kind: C_Symbol_Kind) -> bool {
        for symbol: buffer.c_symbols if symbol.kind == kind && c_symbol_name(buffer, symbol) == name return true;
        return false;
    }

    c_test_expect_token :: (buffer: *Buffer, source: string, needle: string, occurrence: s64, expected: Token_Type) {
        offset := c_test_find(source, needle, occurrence);
        assert(offset >= 0, "C language test could not find occurrence % of '%'", occurrence, needle);
        assert(buffer.tokens[offset] == expected, "C language token '%' occurrence %: expected %, got %", needle, occurrence, expected, buffer.tokens[offset]);
    }

    c_test_validate_large_index :: (buffer: *Buffer) {
        kind_counts: [C_Symbol_Kind.count] s32;
        previous_reference_offset: s32 = -1;
        for reference: buffer.c_references {
            assert(reference.offset >= previous_reference_offset, "C references must stay sorted for binary caret lookup");
            previous_reference_offset = reference.offset;
        }
        for symbol, symbol_index: buffer.c_symbols {
            assert(symbol.definition_offset >= 0 && symbol.definition_offset+symbol.name_count <= buffer.bytes.count);
            name := c_symbol_name(buffer, symbol);
            assert(name.count == symbol.name_count && name);
            kind_counts[cast(s64)symbol.kind] += 1;

            bucket := cast(s64) (symbol.name_hash & (C_SYMBOL_BUCKET_COUNT-1));
            found_in_index := false;
            candidate := buffer.c_symbol_bucket_heads[bucket];
            while candidate >= 0 {
                if candidate == symbol_index { found_in_index = true; break; }
                candidate = buffer.c_symbols[candidate].next_same_hash;
            }
            assert(found_in_index, "Every registered C word must be reachable through the hash/tree index");

            // F12 and completion are driven by this same registered-word
            // index. Exercise every definition in the large real-world file,
            // not just a hand-picked token from each category.
            definition_reference := c_reference_at_offset(buffer, symbol.definition_offset);
            assert(definition_reference != null,
                   "Every registered C word must be navigable at its definition: '%' (%) at %",
                   name, symbol.kind, symbol.definition_offset);
            assert(definition_reference.symbol_index >= 0 && definition_reference.symbol_index < buffer.c_symbols.count);
            resolved_symbol := buffer.c_symbols[definition_reference.symbol_index];
            assert(c_symbol_name(buffer, resolved_symbol) == name);
            assert(resolved_symbol.kind == symbol.kind,
                   "Redeclarations may share a canonical F12 target, but it must have the same symbol kind");
            assert(definition_reference.token_type == c_symbol_token_type(symbol.kind));
            if symbol.kind == .local_variable || symbol.kind == .parameter {
                assert(symbol.scope_start <= symbol.definition_offset && symbol.definition_offset <= symbol.scope_end,
                       "Every scoped completion candidate must be visible at its definition");
            }
        }

        previous_offset: s32 = -1;
        for *reference: buffer.c_references {
            assert(reference.offset >= previous_offset, "C references must stay sorted for binary caret lookup");
            previous_offset = reference.offset;
            assert(reference.offset >= 0 && reference.offset+reference.count <= buffer.bytes.count);
            assert(reference.count > 0 && buffer.tokens[reference.offset] == reference.token_type);
            assert(c_reference_at_offset(buffer, reference.offset) == reference);
            if reference.symbol_index >= 0 {
                assert(reference.symbol_index < buffer.c_symbols.count);
                symbol := buffer.c_symbols[reference.symbol_index];
                reference_name := string.{ data = buffer.bytes.data+reference.offset, count = reference.count };
                assert(reference_name == c_symbol_name(buffer, symbol));
                assert(reference.token_type == c_symbol_token_type(symbol.kind));
            } else assert(false, "C references use compact local symbol indices; cross-buffer F12 is resolved on demand");
        }

        assert(kind_counts[cast(s64)C_Symbol_Kind.function] > 0);
        assert(kind_counts[cast(s64)C_Symbol_Kind.global_variable] > 0);
        assert(kind_counts[cast(s64)C_Symbol_Kind.local_variable] > 0);
        assert(kind_counts[cast(s64)C_Symbol_Kind.parameter] > 0);
        assert(kind_counts[cast(s64)C_Symbol_Kind.struct_member] > 0);
        assert(kind_counts[cast(s64)C_Symbol_Kind.type_definition] > 0);
        assert(kind_counts[cast(s64)C_Symbol_Kind.macro] > 0);
        assert(kind_counts[cast(s64)C_Symbol_Kind.enum_constant] > 0);
        print("nowgrep.c exhaustive index validation: % registered words and % navigable/highlighted occurrences\n",
              buffer.c_symbols.count, buffer.c_references.count);
    }

    c_run_language_feature_tests :: () {
        old_focus_allocator := focus_allocator;
        focus_allocator = context.allocator;
        defer focus_allocator = old_focus_allocator;
        config.comment_words_automaton = build_aho_corasick_automaton(Highlight_Word.[]);

        print("Starting C language feature tests\n");
        source := #string C
#define LIMIT 7
typedef int Count;
enum Mode { MODE_A, MODE_B = MODE_A + 1 };
Count global_count;
struct Vec { int x; int y; };
struct Other { int x; };
struct Inner { int value; };
struct Outer { struct Inner inner; };
int add(struct Vec *v, int amount);
int add(struct Vec *v, int amount) {
    int local = global_count;
    return v->x + amount + local + LIMIT + MODE_B;
}
void use(struct Other *o) {
    struct Outer outer;
    int x = 0;
    o->x = x;
    outer.inner.value = x;
    unknown->x = x;
    add((struct Vec *)0, 1);
}
C
        buffer := c_test_analyze(source);
        defer c_test_free_buffer(*buffer);

        assert(c_test_has_symbol(*buffer, "add", .function));
        assert(c_test_has_symbol(*buffer, "use", .function));
        assert(c_test_has_symbol(*buffer, "global_count", .global_variable));
        assert(c_test_has_symbol(*buffer, "local", .local_variable));
        assert(c_test_has_symbol(*buffer, "amount", .parameter));
        assert(c_test_has_symbol(*buffer, "x", .struct_member));
        assert(c_test_has_symbol(*buffer, "LIMIT", .macro));
        assert(c_test_has_symbol(*buffer, "Count", .type_definition));
        assert(c_test_has_symbol(*buffer, "Vec", .type_definition));
        assert(c_test_has_symbol(*buffer, "MODE_A", .enum_constant));
        assert(c_test_has_symbol(*buffer, "MODE_B", .enum_constant));
        c_test_expect_token(*buffer, source, "global_count", 0, .variable_global);
        c_test_expect_token(*buffer, source, "local", 0, .variable_local);
        c_test_expect_token(*buffer, source, "amount", 2, .parameter);
        c_test_expect_token(*buffer, source, "add", 2, .function);
        c_test_expect_token(*buffer, source, "v->x", 0, .parameter); // checks base; member checked below
        member_offset := c_test_find(source, "v->x")+3;
        assert(buffer.tokens[member_offset] == .struct_member);
        unknown_member_offset := c_test_find(source, "unknown->x")+9;
        assert(buffer.tokens[unknown_member_offset] == .identifier, "Unresolved member must not borrow another struct's member color");
        chained_member_offset := c_test_find(source, "outer.inner.value")+"outer.inner.".count;
        assert(buffer.tokens[chained_member_offset] == .struct_member, "Chained member access must retain the intermediate member's declared type");
        macro_reference := c_reference_at_offset(*buffer, c_test_find(source, "LIMIT", 1));
        typedef_reference := c_reference_at_offset(*buffer, c_test_find(source, "Count", 1));
        struct_reference := c_reference_at_offset(*buffer, c_test_find(source, "Vec", 1));
        enum_reference := c_reference_at_offset(*buffer, c_test_find(source, "MODE_B", 1));
        assert(macro_reference && buffer.c_symbols[macro_reference.symbol_index].kind == .macro);
        assert(typedef_reference && buffer.c_symbols[typedef_reference.symbol_index].kind == .type_definition);
        assert(struct_reference && buffer.c_symbols[struct_reference.symbol_index].kind == .type_definition);
        assert(enum_reference && buffer.c_symbols[enum_reference.symbol_index].kind == .enum_constant);
        variable_prefix := c_test_find(source, "global_count", 0);
        assert(c_completion_expectation(*buffer, variable_prefix, variable_prefix+3) == .variable);
        member_prefix := c_test_find(source, "v->x")+3;
        assert(c_completion_expectation(*buffer, member_prefix, member_prefix+1) == .member);
        call_prefix := c_test_find(source, "add((struct");
        assert(c_completion_expectation(*buffer, call_prefix, call_prefix+3) == .function);
        assert(c_completion_priority(.local_variable, .variable) < c_completion_priority(.type_definition, .variable));
        assert(c_completion_priority(.type_definition, .type) < c_completion_priority(.global_variable, .type));
        assert(c_completion_priority(.macro, .macro) < c_completion_priority(.function, .macro));
        print("C semantic scope/member tests passed\n");

        declarators := "typedef int Count; typedef int Callback(int); int (*callback)(int); Count *value = add((struct Vec *)0, 2);";
        decl_buffer := c_test_analyze(declarators);
        assert(!c_test_has_symbol(*decl_buffer, "Count", .global_variable));
        assert(!c_test_has_symbol(*decl_buffer, "Callback", .function));
        assert(!c_test_has_symbol(*decl_buffer, "Callback", .global_variable));
        assert(c_test_has_symbol(*decl_buffer, "callback", .global_variable));
        assert(!c_test_has_symbol(*decl_buffer, "callback", .function));
        assert(c_test_has_symbol(*decl_buffer, "value", .global_variable));
        pointer_prefix := c_test_find(declarators, "Count *value")+"Count *".count;
        assert(c_completion_expectation(*decl_buffer, pointer_prefix, pointer_prefix+2) == .variable,
               "Completion after a pointer declarator must prefer variable names");
        c_test_free_buffer(*decl_buffer);
        print("C declarator tests passed\n");

        disabled_source := "int feature(int p) { int local = p; return feature(local); }";
        disabled := c_test_analyze(disabled_source, parse_functions = false, parse_variables = false);
        assert(disabled.c_symbols.count == 0);
        c_test_expect_token(*disabled, disabled_source, "feature", 0, .identifier);
        c_test_free_buffer(*disabled);

        variable_only := c_test_analyze(disabled_source, parse_functions = false, parse_variables = true);
        assert(!c_test_has_symbol(*variable_only, "feature", .function));
        assert(c_test_has_symbol(*variable_only, "local", .local_variable));
        c_test_free_buffer(*variable_only);
        print("C feature-toggle tests passed\n");

        shadow_source := "int value; int first(void) { int value = 1; return value; } int second(void) { return value; }";
        shadow_buffer := c_test_analyze(shadow_source);
        local_reference := c_reference_at_offset(*shadow_buffer, c_test_find(shadow_source, "value", 2));
        global_reference := c_reference_at_offset(*shadow_buffer, c_test_find(shadow_source, "value", 3));
        assert(local_reference && shadow_buffer.c_symbols[local_reference.symbol_index].kind == .local_variable);
        assert(global_reference && shadow_buffer.c_symbols[global_reference.symbol_index].kind == .global_variable);
        c_test_free_buffer(*shadow_buffer);
        print("C shadow-resolution test passed\n");

        assert(!bookmarks, "Bookmark tests expect an isolated test process");
        bookmark_buffer: Buffer;
        bookmark_source := "one\nbookmarked\nthree\n";
        insert_at(*bookmark_buffer.bytes, 0, cast([] u8) bookmark_source);
        array_add(*bookmarks, .{ name = copy_string("deleted-line"), buffer_id = 77, offset = 7 });
        array_add(*bookmarks, .{ name = copy_string("shifted-line"), buffer_id = 77, offset = 17 });
        bookmarks_dirty = false;
        bookmarks_note_buffer_edit_for_id(*bookmark_buffer, 77, 4, 11, 0);
        assert(bookmarks.count == 1, "Deleting a complete bookmarked line must delete its bookmark");
        assert(bookmarks[0].name == "shifted-line" && bookmarks[0].offset == 6,
               "Bookmarks below a deleted line must follow the surviving text");
        assert(bookmarks_dirty, "Bookmark deletion and movement must schedule persistence");
        bookmark_free(*bookmarks[0]);
        bookmarks.count = 0;
        reset(*bookmark_buffer.bytes);

        partial_source := "one\nbookmarked\n";
        insert_at(*bookmark_buffer.bytes, 0, cast([] u8) partial_source);
        array_add(*bookmarks, .{ name = copy_string("partial-edit"), buffer_id = 77, offset = 8 });
        bookmarks_note_buffer_edit_for_id(*bookmark_buffer, 77, 7, 2, 0);
        assert(bookmarks.count == 1 && bookmarks[0].offset == 7,
               "Deleting characters on a bookmarked line must preserve and reposition the bookmark");
        bookmarks_note_buffer_edit_for_id(*bookmark_buffer, 77, 2, 0, 5);
        assert(bookmarks[0].offset == 12, "Insertions above a bookmark must move it down");
        bookmarks_note_buffer_saved(77, "C:/focus-dev/saved-after-bookmark.c");
        assert(bookmarks[0].file_path == "C:/focus-dev/saved-after-bookmark.c",
               "Bookmarks created in untitled buffers must become persistent when the buffer is saved");
        bookmark_dialog.mode = .create;
        array_reset(*bookmark_dialog.filtered);
        bookmark_refresh_entries(construct_fuzzy_filter(""));
        assert(bookmark_dialog.filtered.count == 0,
               "New Bookmark is an input-only dialog and must not list existing bookmarks");
        bookmark_free(*bookmarks[0]);
        bookmarks.count = 0;
        reset(*bookmark_buffer.bytes);
        print("Bookmark line-deletion and edit-tracking tests passed\n");

        make_directory_if_it_does_not_exist(".build");
        bookmark_test_path := ".build/bookmark-persistence-test.bin";
        array_add(*bookmarks, .{
            name = copy_string("persist\tname\nwith whitespace"),
            file_path = copy_string("C:/focus-dev/test1.c"),
            buffer_id = 22,
            offset = 1234,
        });
        array_add(*bookmarks, .{
            name = copy_string("second persisted bookmark"),
            file_path = copy_string("C:/focus-dev/test2.h"),
            buffer_id = 23,
            offset = 44,
        });
        assert(bookmarks_save_to_path(bookmark_test_path));
        bookmarks_clear();
        assert(bookmarks_load_from_path(bookmark_test_path));
        assert(bookmarks.count == 2);
        assert(bookmarks[0].name == "persist\tname\nwith whitespace");
        assert(bookmarks[0].file_path == "C:/focus-dev/test1.c");
        assert(bookmarks[0].buffer_id == -1 && bookmarks[0].offset == 1234,
               "Persistent bookmarks must resolve buffers by path after restart");
        assert(bookmarks[1].name == "second persisted bookmark" && bookmarks[1].offset == 44);
        bookmarks_clear();
        file_delete(bookmark_test_path);
        bookmarks_dirty = false;
        print("Bookmark persistence round-trip test passed\n");

        c_test_caret_history_isolation();
        print("Per-buffer caret history and cross-buffer F12 round-trip tests passed\n");

        diagnostic_source := "int main(void) {\n    return missing_name;\n}\n";
        diagnostic_buffer := c_test_analyze(diagnostic_source);
        add(*diagnostic_buffer.line_starts, 0);
        for byte, i: diagnostic_buffer.bytes if byte == #char "\n" then add(*diagnostic_buffer.line_starts, cast(s32)i+1);
        clang_work := C_Compiler_Work.{
            generation = 9,
            temp_file = "C:/tmp/focus-clang-test.c",
            output = #string OUTPUT
C:/tmp/focus-clang-test.c:2:12: error: use of undeclared identifier 'missing_name'
C:/tmp/focus-clang-test.c:4:1: error: expected declaration at end of input
OUTPUT
        };
        c_compiler_parse_output(*diagnostic_buffer, *clang_work);
        assert(diagnostic_buffer.c_diagnostics.count == 2);
        assert(diagnostic_buffer.c_diagnostics[0].offset == c_test_find(diagnostic_source, "missing_name"));
        assert(diagnostic_buffer.c_diagnostics[0].count == "missing_name".count);
        assert(contains(diagnostic_buffer.c_diagnostics[0].message, "undeclared identifier"));
        assert(diagnostic_buffer.c_diagnostics[1].offset == diagnostic_buffer.bytes.count-1);
        assert(diagnostic_buffer.c_diagnostics[1].count == 1,
               "End-of-file compiler diagnostics must stay inside the drawable buffer range");
        c_test_free_buffer(*diagnostic_buffer);
        print("Clang diagnostic parser test passed\n");

        #if OS == .WINDOWS {
            clang_source := "int main(void) { return definitely_missing_name; }\n";
            clang_buffer := c_test_analyze(clang_source);
            add(*clang_buffer.line_starts, 0);
            clang_integration := C_Compiler_Work.{
                contents = clang_source,
                original_directory = "C:/focus-dev",
                executable = "clang",
                parameters = "-fsyntax-only -fno-color-diagnostics -ferror-limit=100 -x c -Wall -Werror -I .",
                temp_file = "C:/focus-dev/.build/focus-clang-integration-test.c",
            };
            c_compiler_execute_work(*clang_integration);
            assert(clang_integration.launched, "The configured clang executable must launch");
            assert(contains(clang_integration.output, "definitely_missing_name"));
            c_compiler_parse_output(*clang_buffer, *clang_integration);
            assert(clang_buffer.c_diagnostics.count > 0, "Real clang stderr must become editor diagnostics");
            free(clang_integration.output,, allocator = focus_allocator);
            c_test_free_buffer(*clang_buffer);
            print("Real clang -fsyntax-only integration test passed\n");
        }

        completion_editor: Editor;
        completion_buffer: Buffer;
        insert_at(*completion_buffer.bytes, 0, cast([]u8)"pri");
        add(*completion_editor.cursors, Cursor.{ pos = 3, sel = 3 });
        add(*completion_editor.completion.candidates, .{
            name = copy_string("printf",, allocator = focus_allocator), kind = .function,
        });
        completion_editor.completion.active = true;
        completion_editor.completion.prefix_start = 0;
        assert(c_get_completion_suffix(*completion_editor, *completion_buffer) == "ntf");
        c_close_completion(*completion_editor);
        assert(!completion_editor.completion.active && completion_editor.completion.candidates.count == 0);
        reset(*completion_editor.cursors);
        reset(*completion_buffer.bytes);
        print("Autocomplete ghost-state test passed\n");

        // Jobs cancelled before the worker claims them must release their
        // potentially large snapshots immediately, and cleanup must remain
        // idempotent when the completed queue later returns the small shell.
        semantic_cancel_buffer: Buffer;
        semantic_cancel_work := New(C_Semantic_Work,, allocator = focus_allocator);
        resize(*semantic_cancel_work.buffer.bytes, 1024*1024);
        semantic_cancel_buffer.c_semantic_active_work = semantic_cancel_work;
        c_semantic_cancel(*semantic_cancel_buffer);
        assert(semantic_cancel_work.cancelled && semantic_cancel_work.state == 3);
        assert(semantic_cancel_work.buffer.bytes.count == 0);
        c_semantic_free_work(semantic_cancel_work);

        compiler_cancel_buffer: Buffer;
        compiler_cancel_work := New(C_Compiler_Work,, allocator = focus_allocator);
        compiler_cancel_work.contents = copy_string("large compiler snapshot",, allocator = focus_allocator);
        compiler_cancel_work.parameters = copy_string("-fsyntax-only",, allocator = focus_allocator);
        compiler_cancel_buffer.c_compiler_active_work = compiler_cancel_work;
        c_compiler_cancel(*compiler_cancel_buffer);
        assert(compiler_cancel_work.cancelled && compiler_cancel_work.state == 3);
        assert(!compiler_cancel_work.contents && !compiler_cancel_work.parameters);
        assert(compiler_cancel_buffer.c_compiler_active_work == null);
        c_compiler_free_work(compiler_cancel_work);
        print("Cancelable semantic/compiler job lifecycle tests passed\n");

        nowgrep_data, nowgrep_ok := read_entire_file("C:/nowgrep/nowgrep.c");
        if nowgrep_ok {
            lexical_start := current_time_monotonic();
            nowgrep_lexical := c_test_analyze(nowgrep_data, parse_functions = false, parse_variables = false);
            lexical_ms := to_milliseconds(current_time_monotonic()-lexical_start);
            c_test_free_buffer(*nowgrep_lexical);

            semantic_start := current_time_monotonic();
            nowgrep_semantic := c_test_analyze(nowgrep_data);
            semantic_ms := to_milliseconds(current_time_monotonic()-semantic_start);
            assert(c_test_has_symbol(*nowgrep_semantic, "VOLUME_DISK_EXTENTS", .type_definition));
            volume_use := c_test_find(nowgrep_data, "VOLUME_DISK_EXTENTS vde");
            assert(volume_use >= 0);
            volume_reference := c_reference_at_offset(*nowgrep_semantic, volume_use);
            assert(volume_reference && nowgrep_semantic.c_symbols[volume_reference.symbol_index].kind == .type_definition,
                   "F12 must resolve compound struct typedef aliases such as VOLUME_DISK_EXTENTS");
            c_test_validate_large_index(*nowgrep_semantic);
            assert(lexical_ms < 60, "nowgrep.c lexical typing path regression: % ms", lexical_ms);
            assert(semantic_ms < 150, "nowgrep.c full C index regression: % ms", semantic_ms);
            print("nowgrep.c baseline: lexical % ms, lexical+semantic % ms (% bytes, % symbols, % references)\n",
                  lexical_ms, semantic_ms, nowgrep_data.count, nowgrep_semantic.c_symbols.count, nowgrep_semantic.c_references.count);
            print("semantic phases: collect %, structs %, functions %, variables %, resolve % ms\n",
                  c_profile_collect_ms, c_profile_struct_ms, c_profile_function_ms, c_profile_variable_ms, c_profile_resolve_ms);
            print("compact C index layouts: token % bytes, semantic token % bytes, reference % bytes\n",
                  size_of(Token_Type), size_of(C_Semantic_Token), size_of(C_Reference));
            assert(size_of(Token_Type) == 1 && size_of(C_Semantic_Token) == 22 && size_of(C_Reference) == 16);
            c_test_free_buffer(*nowgrep_semantic);
            free(nowgrep_data);
        }

        large_source: String_Builder;
        init_string_builder(*large_source);
        for i: 0..1999 {
            print_to_builder(*large_source, "int function_%(int parameter_%) { int local_% = parameter_% + %; return local_%; }\n", i, i, i, i, i, i);
        }
        large_string := builder_to_string(*large_source);
        start_time := current_time_monotonic();
        large_buffer := c_test_analyze(large_string);
        elapsed_ms := to_milliseconds(current_time_monotonic()-start_time);
        assert(large_buffer.c_symbols.count >= 6000);
        assert(elapsed_ms < 500, "C semantic analysis performance regression: % ms for 2,000 functions", elapsed_ms);
        print("C language feature tests passed (2,000-function semantic benchmark: % ms)\n", elapsed_ms);
        c_test_free_buffer(*large_buffer);
        free(large_string);
    }

}
