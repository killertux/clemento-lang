mod error;
mod scanner;
mod token;

pub use error::LexerError;
pub use scanner::Lexer;
pub use token::{IntegerNumber, Number, Position, Token, TokenType};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex_symbol() {
        let input = "hello";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Symbol("hello".to_string()),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn multiple_symbols() {
        let input = "hello1 hello2\nhello3";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            [
                Token {
                    token_type: TokenType::Symbol("hello1".to_string()),
                    position: Position::new(1, 1, None)
                },
                Token {
                    token_type: TokenType::Symbol("hello2".to_string()),
                    position: Position::new(1, 8, None)
                },
                Token {
                    token_type: TokenType::Symbol("hello3".to_string()),
                    position: Position::new(2, 1, None)
                },
            ]
        );
    }

    #[test]
    fn lex_string() {
        let input = "\"hello\"";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::String("hello".to_string()),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_complex_string() {
        let input = r#""\tHello\nWorld.\n\\Nice \"string\"\\""#;
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::String("\tHello\nWorld.\n\\Nice \"string\"\\".to_string()),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn not_closed_string() {
        let input = r#""Hello"#;
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Err(LexerError::UnexpectedEndOfInput(Position::new(
                1, 7, None
            ))))
        );
    }

    #[test]
    fn invalid_escape() {
        let input = r#""Hello \h""#;
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Err(LexerError::UnexpectedToken(
                r#"\h"#.to_string(),
                Position::new(1, 8, None)
            )))
        );
    }

    #[test]
    fn lex_char_hex_escape() {
        let input = r#"'\x20'"#;
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Char(' '),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_char_hex_escape_uppercase() {
        let input = r#"'\x4A'"#;
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Char('J'),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_string_hex_escape() {
        let input = r#""\x48i\x21""#;
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::String("Hi!".to_string()),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_char_multibyte_hex_escape() {
        // 0xC2 0xA0 is the UTF-8 encoding of U+00A0 (no-break space).
        let input = r#"'\xc2\xa0'"#;
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Char('\u{a0}'),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_string_multibyte_hex_escape() {
        // 0xE2 0x82 0xAC is the UTF-8 encoding of U+20AC (€).
        let input = r#""\xe2\x82\xac""#;
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::String("€".to_string()),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_char_too_many_code_points() {
        let input = r#"'\x41\x42'"#;
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Err(LexerError::UnexpectedToken(
                "'AB'".to_string(),
                Position::new(1, 1, None)
            )))
        );
    }

    #[test]
    fn lex_char_invalid_utf8() {
        let input = r#"'\xff'"#;
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Err(LexerError::UnexpectedToken(
                r#"'\xff'"#.to_string(),
                Position::new(1, 1, None)
            )))
        );
    }

    #[test]
    fn lex_char_hex_escape_invalid_digit() {
        let input = r#"'\xZ0'"#;
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Err(LexerError::UnexpectedToken(
                r#"\xZ"#.to_string(),
                Position::new(1, 3, None)
            )))
        );
    }

    #[test]
    fn lex_parentheses() {
        let input = r#"(Hello)"#;
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![
                Token {
                    token_type: TokenType::LeftParen,
                    position: Position::new(1, 1, None),
                },
                Token {
                    token_type: TokenType::Symbol("Hello".to_string()),
                    position: Position::new(1, 2, None),
                },
                Token {
                    token_type: TokenType::RightParen,
                    position: Position::new(1, 7, None),
                }
            ]
        );
    }

    #[test]
    fn lex_braces() {
        let input = r#"{Hello}"#;
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![
                Token {
                    token_type: TokenType::LeftBrace,
                    position: Position::new(1, 1, None),
                },
                Token {
                    token_type: TokenType::Symbol("Hello".to_string()),
                    position: Position::new(1, 2, None),
                },
                Token {
                    token_type: TokenType::RightBrace,
                    position: Position::new(1, 7, None),
                }
            ]
        );
    }

    #[test]
    fn lex_brackets() {
        let input = r#"[Hello]"#;
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![
                Token {
                    token_type: TokenType::LeftBracket,
                    position: Position::new(1, 1, None),
                },
                Token {
                    token_type: TokenType::Symbol("Hello".to_string()),
                    position: Position::new(1, 2, None),
                },
                Token {
                    token_type: TokenType::RightBracket,
                    position: Position::new(1, 7, None),
                }
            ]
        );
    }

    #[test]
    fn lex_backslash() {
        // `\name` lexes as a Backslash followed by the bare symbol.
        let input = "\\double";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![
                Token {
                    token_type: TokenType::Backslash,
                    position: Position::new(1, 1, None),
                },
                Token {
                    token_type: TokenType::Symbol("double".to_string()),
                    position: Position::new(1, 2, None),
                }
            ]
        );
    }

    #[test]
    fn lex_right_arrow() {
        let input = r#"->"#;
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::RightArrow,
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_positive_integer() {
        let input = "42";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Integer(IntegerNumber::I64(42))),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_negative_integer() {
        let input = "-123";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Integer(IntegerNumber::I64(-123))),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_float() {
        let input = "3.14";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Float("3.14".to_string())),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_negative_float() {
        let input = "-2.5";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Float("-2.5".to_string())),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_hex_number() {
        let input = "0xFF";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Integer(IntegerNumber::U64(255))),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_large_hex_number() {
        let input = "0x1A2B3C4D";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Integer(IntegerNumber::U64(439041101))),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_number_with_underscores() {
        let input = "1_000_000";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Integer(IntegerNumber::I64(1000000))),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_float_with_underscores() {
        let input = "1_000.5_5";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Float("1000.55".to_string())),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_zero() {
        let input = "0";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Integer(IntegerNumber::I64(0))),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_zero_float() {
        let input = "0.0";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Float("0.0".to_string())),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_multiple_numbers() {
        let input = "42 -17 3.14 0xFF";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::I64(42))),
                    position: Position::new(1, 1, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::I64(-17))),
                    position: Position::new(1, 4, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Float("3.14".to_string())),
                    position: Position::new(1, 8, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::U64(255))),
                    position: Position::new(1, 13, None),
                }
            ]
        );
    }

    #[test]
    fn lex_invalid_hex() {
        let input = "0xGHI";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Err(LexerError::InvalidNumber(
                "0xGHI".to_string(),
                Position::new(1, 1, None)
            )))
        );
    }

    #[test]
    fn lex_invalid_float() {
        let input = "3.14.15";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Err(LexerError::InvalidNumber(
                "3.14.15".to_string(),
                Position::new(1, 1, None)
            )))
        );
    }

    #[test]
    fn lex_multiple_numbers_types() {
        let input = "42u8 42u16 42u32 42u64 42u128 42i8 42i16 42i32 42i64 42i128";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::U8(42))),
                    position: Position::new(1, 1, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::U16(42))),
                    position: Position::new(1, 6, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::U32(42))),
                    position: Position::new(1, 12, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::U64(42))),
                    position: Position::new(1, 18, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::U128(42))),
                    position: Position::new(1, 24, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::I8(42))),
                    position: Position::new(1, 31, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::I16(42))),
                    position: Position::new(1, 36, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::I32(42))),
                    position: Position::new(1, 42, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::I64(42))),
                    position: Position::new(1, 48, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::I128(42))),
                    position: Position::new(1, 54, None),
                }
            ]
        );
    }

    #[test]
    fn lex_number_followed_by_symbol() {
        let input = "42hello";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Err(LexerError::InvalidNumber(
                "42hello".to_string(),
                Position::new(1, 1, None)
            )))
        );
    }

    #[test]
    fn lex_dash_without_number() {
        let input = "- hello";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![
                Token {
                    token_type: TokenType::Symbol("-".to_string()),
                    position: Position::new(1, 1, None),
                },
                Token {
                    token_type: TokenType::Symbol("hello".to_string()),
                    position: Position::new(1, 3, None),
                }
            ]
        );
    }

    #[test]
    fn lex_single_line_comment() {
        let input = "// this is a comment";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(tokens, vec![]);
    }

    #[test]
    fn lex_single_line_comment_with_code_before() {
        let input = "hello // this is a comment";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![Token {
                token_type: TokenType::Symbol("hello".to_string()),
                position: Position::new(1, 1, None),
            }]
        );
    }

    #[test]
    fn lex_single_line_comment_with_code_after() {
        let input = "// this is a comment\nhello";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![Token {
                token_type: TokenType::Symbol("hello".to_string()),
                position: Position::new(2, 1, None),
            }]
        );
    }

    #[test]
    fn lex_multiple_single_line_comments() {
        let input = "// comment 1\n// comment 2\nhello\n// comment 3";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![Token {
                token_type: TokenType::Symbol("hello".to_string()),
                position: Position::new(3, 1, None),
            }]
        );
    }

    #[test]
    fn lex_single_line_comment_without_newline() {
        let input = "hello // comment at end of file";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![Token {
                token_type: TokenType::Symbol("hello".to_string()),
                position: Position::new(1, 1, None),
            }]
        );
    }

    #[test]
    fn lex_multi_line_comment() {
        let input = "/* this is a multi-line comment */";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(tokens, vec![]);
    }

    #[test]
    fn lex_multi_line_comment_spanning_lines() {
        let input = "/* this is a\n   multi-line\n   comment */";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(tokens, vec![]);
    }

    #[test]
    fn lex_multi_line_comment_with_code_before() {
        let input = "hello /* comment */ world";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![
                Token {
                    token_type: TokenType::Symbol("hello".to_string()),
                    position: Position::new(1, 1, None),
                },
                Token {
                    token_type: TokenType::Symbol("world".to_string()),
                    position: Position::new(1, 21, None),
                }
            ]
        );
    }

    #[test]
    fn lex_multi_line_comment_with_asterisks_inside() {
        let input = "/* comment with * asterisks * inside */";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(tokens, vec![]);
    }

    #[test]
    fn lex_mixed_comments() {
        let input = "hello // single line\n/* multi\n   line */ world";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![
                Token {
                    token_type: TokenType::Symbol("hello".to_string()),
                    position: Position::new(1, 1, None),
                },
                Token {
                    token_type: TokenType::Symbol("world".to_string()),
                    position: Position::new(3, 12, None),
                }
            ]
        );
    }

    #[test]
    fn lex_slash_without_comment() {
        let input = "a/b";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![Token {
                token_type: TokenType::Symbol("a/b".to_string()),
                position: Position::new(1, 1, None),
            }]
        );
    }

    #[test]
    fn lex_single_slash() {
        let input = "/";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![Token {
                token_type: TokenType::Symbol("/".to_string()),
                position: Position::new(1, 1, None),
            }]
        );
    }

    #[test]
    fn lex_comments_with_special_characters() {
        let input =
            "// comment with symbols !@#$%^&*()\n/* comment with \"quotes\" and 'apostrophes' */";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(tokens, vec![]);
    }

    #[test]
    fn lex_symbol_with_path() {
        let input = "std::std::*";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::SymbolWithPath(vec!["std".into(), "std".into(), "*".into()]),
                position: Position::new(1, 1, None),
            }))
        );
    }
}
