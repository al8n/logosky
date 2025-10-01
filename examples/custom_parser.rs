//! A custom parser example demonstrating the Parseable trait.
//!
//! This example shows how to:
//! - Implement the Parseable trait for custom types
//! - Compose parsers using the trait
//! - Build reusable parser components
//! - Parse structured data with nested elements
//!
//! Run with: cargo run --example custom_parser

use chumsky::prelude::*;
use logos::Logos;
use logosky::{
  Lexed, Parseable, Token,
  utils::{Span, Spanned},
};

type TokenStream<'a> = logosky::TokenStream<'a, ConfigToken<'a>>;

// Define tokens for a simple configuration language
#[derive(Logos, Debug, Clone, Copy, PartialEq, Eq)]
#[logos(skip r"[ \t\n\r]+")]
enum ConfigToken<'a> {
  #[token("=")]
  Equals,

  #[token("{")]
  LBrace,

  #[token("}")]
  RBrace,

  #[token(";")]
  Semicolon,

  #[regex(r#"[a-zA-Z_][a-zA-Z0-9_]*"#, |lex| lex.slice())]
  Identifier(&'a str),

  #[regex(r#""([^"\\]|\\["\\])*""#, |lex| lex.slice())]
  String(&'a str),

  #[regex(r#"[0-9]+"#, |lex| lex.slice())]
  Number(&'a str),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ConfigTokenKind {
  Equals,
  LBrace,
  RBrace,
  Semicolon,
  Identifier,
  String,
  Number,
}

impl<'a> Token<'a> for ConfigToken<'a> {
  type Char = char;
  type Kind = ConfigTokenKind;
  type Logos = Self;

  fn kind(&self) -> Self::Kind {
    match self {
      Self::Equals => ConfigTokenKind::Equals,
      Self::LBrace => ConfigTokenKind::LBrace,
      Self::RBrace => ConfigTokenKind::RBrace,
      Self::Semicolon => ConfigTokenKind::Semicolon,
      Self::Identifier(_) => ConfigTokenKind::Identifier,
      Self::String(_) => ConfigTokenKind::String,
      Self::Number(_) => ConfigTokenKind::Number,
    }
  }
}

// AST types
#[derive(Debug, Clone, PartialEq)]
enum Value {
  String(String),
  Number(i64),
  Block(Vec<Spanned<Property>>),
}

#[derive(Debug, Clone, PartialEq)]
struct Property {
  key: String,
  value: Value,
}

impl Property {
  // Property contains a nested Value, so we need to pass a parser for Value to address recursion problems.
  fn parser_with<'a, E, P>(vp: P) -> impl Parser<'a, TokenStream<'a>, Self, E> + Clone
  where
    P: Parser<'a, TokenStream<'a>, Value, E> + Clone + 'a,
    E: chumsky::extra::ParserExtra<'a, TokenStream<'a>, Error = EmptyErr> + 'a,
  {
    // Parse identifier
    let identifier = any()
      .try_map(|tok: Lexed<'_, ConfigToken<'_>>, span: Span| match tok {
        Lexed::Token(t) if t.kind() == ConfigTokenKind::Identifier => {
          Ok(format!("id[{}..{}]", span.start(), span.end()))
        }
        _ => Err(EmptyErr::default()),
      })
      .boxed();

    // key = value;
    identifier
      .then_ignore(
        any().try_map(|tok: Lexed<'_, ConfigToken<'_>>, _| match tok {
          Lexed::Token(t) if t.kind() == ConfigTokenKind::Equals => Ok(()),
          _ => Err(EmptyErr::default()),
        }),
      )
      .then(vp)
      .then_ignore(
        any().try_map(|tok: Lexed<'_, ConfigToken<'_>>, _| match tok {
          Lexed::Token(t) if t.kind() == ConfigTokenKind::Semicolon => Ok(()),
          _ => Err(EmptyErr::default()),
        }),
      )
      .map(|(key, value)| Property { key, value })
  }
}

// Implement Parseable for Value
impl<'a> Parseable<'a, TokenStream<'a>, ConfigToken<'a>, EmptyErr> for Value {
  fn parser<E>() -> impl chumsky::Parser<'a, TokenStream<'a>, Self, E> + Clone
  where
    Self: Sized + 'a,
    E: chumsky::extra::ParserExtra<'a, TokenStream<'a>, Error = EmptyErr> + 'a,
  {
    recursive(|value| {
      // Parse string values
      let string = any()
        .try_map(|tok: Lexed<'_, ConfigToken<'_>>, span: Span| match tok {
          Lexed::Token(t) if t.kind() == ConfigTokenKind::String => {
            // Extract string content (remove quotes)
            let s = span.start() + 1..span.end() - 1;
            Ok(Value::String(format!("string[{}..{}]", s.start, s.end)))
          }
          _ => Err(EmptyErr::default()),
        })
        .boxed();

      // Parse number values
      let number = any()
        .try_map(|tok: Lexed<'_, ConfigToken<'_>>, _| match tok {
          Lexed::Token(t) => {
            if let ConfigToken::Number(n) = t.data() {
              n.parse::<i64>()
                .map(Value::Number)
                .map_err(|_| EmptyErr::default())
            } else {
              Err(EmptyErr::default())
            }
          }
          _ => Err(EmptyErr::default()),
        })
        .boxed();

      // Parse block values
      let block = any()
        .try_map(|tok: Lexed<'_, ConfigToken<'_>>, _| match tok {
          Lexed::Token(t) if t.kind() == ConfigTokenKind::LBrace => Ok(()),
          _ => Err(EmptyErr::default()),
        })
        .ignore_then(
          Property::parser_with(value.clone())
            .map_with(|prop, exa| Spanned::new(exa.span(), prop))
            .repeated()
            .collect::<Vec<_>>(),
        )
        .then_ignore(
          any().try_map(|tok: Lexed<'_, ConfigToken<'_>>, _| match tok {
            Lexed::Token(t) if t.kind() == ConfigTokenKind::RBrace => Ok(()),
            _ => Err(EmptyErr::default()),
          }),
        )
        .map(Value::Block)
        .boxed();

      choice((string, number, block))
    })
  }
}

impl<'a> Parseable<'a, TokenStream<'a>, ConfigToken<'a>, EmptyErr> for Property {
  fn parser<E>() -> impl chumsky::Parser<'a, TokenStream<'a>, Self, E> + Clone
  where
    Self: Sized + 'a,
    E: chumsky::extra::ParserExtra<'a, TokenStream<'a>, Error = EmptyErr> + 'a,
  {
    Property::parser_with(Value::parser())
  }
}

impl std::fmt::Display for Value {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Value::String(s) => write!(f, "\"{}\"", s),
      Value::Number(n) => write!(f, "{}", n),
      Value::Block(props) => {
        writeln!(f, "{{")?;
        for prop in props {
          writeln!(f, "  {}", prop.data)?;
        }
        write!(f, "}}")
      }
    }
  }
}

impl std::fmt::Display for Property {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{} = {};", self.key, self.value)
  }
}

fn main() {
  println!("Custom Parser Example\n");
  println!("This demonstrates implementing the Parseable trait for custom types.\n");

  // Example configuration files
  let examples = vec![
    ("Simple property", r#"name = "Alice";"#),
    ("Number property", r#"age = 30;"#),
    (
      "Nested block",
      r#"user = {
        name = "Bob";
        age = 25;
      };"#,
    ),
    (
      "Deep nesting",
      r#"config = {
        database = {
          host = "localhost";
          port = 5432;
        };
        timeout = 30;
      };"#,
    ),
  ];

  for (name, input) in examples {
    println!("=== {} ===\n", name);
    println!("Input:\n{}\n", input);

    let stream = TokenStream::<'_>::new(input);
    let parser =
      <Spanned<Property> as Parseable<TokenStream<'_>, ConfigToken<'_>, EmptyErr>>::parser::<
        extra::Err<EmptyErr>,
      >();

    match parser.parse(stream).into_result() {
      Ok(property) => {
        println!("Parsed successfully:");
        println!("{}\n", property.data);
      }
      Err(errors) => {
        println!("Parse errors: {:?}\n", errors);
      }
    }

    println!();
  }
}
