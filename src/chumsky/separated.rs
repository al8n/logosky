use core::cell::RefCell;
use std::rc::Rc;

use chumsky::input::Emitter;

use crate::{
  Lexed, LogoStream, Logos, PunctuatorToken, Source,
  chumsky::{Parser, container::Container as ChumskyContainer, extra::ParserExtra, prelude::*},
  error::{Missing, UnexpectedEot, UnexpectedToken},
  syntax::Language,
  utils::{AsSpan, Span, Spanned},
};

/// Parses `content_parser` items separated by tokens and terminated by an end token.
///
/// This combinator is a recovering analogue of Chumsky’s `separated` helper. It repeatedly
/// parses items using `content_parser`, expects each item (except the last) to be followed
/// by a separator recognised by `is_sep_token`, and stops when `is_end_token` returns
/// `true`. When the parser encounters something other than a separator or end token after
/// a successful item, it emits:
///
/// - [`UnexpectedToken`] tagged with the separator syntax kind supplied by `sep_kind`.
/// - [`Missing<Sep, Lang>`] to mark the gap between the previous item and the unexpected
///   token.
///
/// The unexpected token is **not** consumed, so the item parser (which may provide its own
/// recovery) gets a chance to handle it. Separator/end tokens are also left on the stream,
/// matching Chumsky’s “delimited by” combinators.
///
/// # Type Parameters
///
/// - `T`: Token type produced by the lexer.
/// - `O`: Parsed item type (must expose its span).
/// - `Sep`: Syntax type representing the separator (only used for diagnostics).
/// - `Lang`: Language marker supplying the syntax kind enum.
/// - `C`: Container used to collect parsed items (`Vec`, `SmallVec`, etc.).
/// - `E`: Parser extra carrying the error type.
///
/// This helper accepts any parser for the list items plus two predicates that identify
/// separator tokens (such as commas or semicolons) and the token that closes the sequence
/// (such as `)` or `}`). After each successful item it expects either a separator or the
/// end token. When it encounters anything else, it emits:
///
/// 1. [`UnexpectedToken`] describing the token that appeared where a separator/end was
///    expected (the `sep_kind` closure supplies the expected kind).
/// 2. [`Missing`] describing the gap between the last parsed item and the token that
///    followed it (the gap is attributed to the `Sep` syntax type).
///
/// The unexpected token itself is **not** consumed; it remains on the stream so the item
/// parser (which may have its own recovery) can decide how to handle it. Lexer errors are
/// consumed, reported, and treated as missing separators so the parser keeps forward
/// progress.
///
/// The end token is left in the stream (not consumed). This mirrors Chumsky's built-in
/// `separated` combinator and lets the caller decide whether to keep or ignore the closing
/// delimiter.
///
/// # Type Parameters
///
/// - `T`: Token type produced by the lexer.
/// - `O`: Parsed item type (must expose its span and syntax information).
/// - `Sep`: Syntax type representing the separator itself (used for [`Missing`] diagnostics).
/// - `C`: Container used to accumulate parsed items (`Vec`, `SmallVec`, etc.).
/// - `E`: Chumsky extra carrying the parser's error type/state.
///
/// # Errors
///
/// The returned parser may emit/return:
///
/// - [`UnexpectedToken`] whenever a token other than separator/end appears after an item.
/// - [`Missing`] when a separator is absent between two items.
/// - [`UnexpectedEot`] if the end token is never encountered before EOF.
/// - Lexer errors surfaced by the input stream.
///
/// # Examples
///
/// ```rust,ignore
/// use logosky::chumsky::separated_by;
/// use my_lang::{Identifier, CommaSeparatorSyntax};
///
/// // Parse: identifier (',' identifier)* ')'
/// let parser = separated_by(
///     identifier_parser(),
///    |tok| tok.is_comma(),
///    |tok| tok.is_rparen(),
/// );
///
/// // Define CommaSeparatorSyntax to satisfy the `Sep` parameter:
/// // impl Syntax for CommaSeparatorSyntax { type Lang = MyLang; const KIND = SyntaxKind::Comma; ... }
///
/// let parsed = parser.parse(stream)?;
/// ```
///
/// When the parser sees `identifier identifier` (missing comma), it emits diagnostics such as:
///
/// ```text
/// unexpected token 'identifier', expected ','
/// missing ',' between 10..15 and 15..20
/// ```
pub fn separated_by<'a, 'e: 'a, I, T, E, O, C, Sep, Lang>(
  content_parser: impl Parser<'a, I, O, E> + Clone + 'a,
  is_sep_token: impl Fn(&T) -> bool + Clone + 'a,
  is_end_token: impl Fn(&T) -> bool + Clone + 'a,
  sep_kind: impl Fn() -> Lang::SyntaxKind + Clone + 'a,
  on_trailing_sep: impl Fn(&mut Emitter<E::Error>) + Clone + 'a
) -> impl Parser<'a, I, Spanned<C>, E> + Clone + 'a
where
  T: PunctuatorToken<'a>,
  O: AsSpan<Span> + 'a,
  Sep: 'a,
  Lang: Language,
  Lang::SyntaxKind: 'e,
  E::Error: From<UnexpectedToken<'e, T, Lang::SyntaxKind>>
    + From<UnexpectedEot>
    + From<<T::Logos as Logos<'a>>::Error>
    + From<Missing<Sep, Lang>>
    + 'a,
  I: LogoStream<'a, T, Slice = <<<T>::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
  E: ParserExtra<'a, I> + 'a,
  C: ChumskyContainer<O> + 'a,
{
  custom(move |inp| {
    let mut container = C::default();
    let start_checkpoint = inp.cursor();
    let mut last_span: Span = inp.span_since(&start_checkpoint);
    let mut expect_item = true;

    loop {
      // If we're waiting for an item, allow early termination (empty list or trailing separator)
      if expect_item {
        match inp.peek() {
          Some(Lexed::Token(tok)) if is_end_token(&tok) => {
            // we are expecting an item, but found the end token instead;
            // A trailing separator is found, we should report something!

            // ignore the err, as we just want the emitter
            let _ = inp.parse(any().validate(|_, _, emitter| {
              on_trailing_sep(emitter);
            }).rewind());

            return Ok(Spanned::new(inp.span_since(&start_checkpoint), container));
          }
          Some(Lexed::Token(_)) => {
            let item = inp.parse(content_parser.clone())?;
            last_span = *item.as_span();
            container.push(item);
            expect_item = false;
            continue;
          }
          Some(Lexed::Error(_)) => {
            // Consume lexer error and keep waiting for an item
            inp.parse(any().validate(|lexed, _, emitter| {
              if let Lexed::Error(err) = lexed {
                emitter.emit(E::Error::from(err));
              }
            }))?;
            continue;
          }
          None => {
            return Err(UnexpectedEot::eot(inp.span_since(&start_checkpoint)).into());
          }
        }
      }

      // Expecting a separator or end token after an item
      match inp.peek() {
        Some(Lexed::Token(tok)) if is_sep_token(&tok) => {
          inp.skip();
          expect_item = true;
          continue;
        }
        Some(Lexed::Token(tok)) if is_end_token(&tok) => {
          return Ok(Spanned::new(inp.span_since(&start_checkpoint), container));
        }
        Some(Lexed::Token(Spanned { span, data: tok })) => {
          // Consume the unexpected token while emitting diagnostics
          inp.parse(
            any()
              .validate(|_, _, emitter| {
                emitter.emit(E::Error::from(UnexpectedToken::expected_one_with_found(
                  span,
                  tok.clone(),
                  sep_kind(),
                )));
                emitter.emit(E::Error::from(Missing::new(last_span).with_after(span)));
              })
              .or_not()
              .rewind(),
          )?;
          // Loop continues with expect_item still false, so we'll ask the content_parser
          expect_item = true;
          continue;
        }
        Some(Lexed::Error(_)) => {
          // Consume lexer error and keep waiting for an item
          inp.parse(any().validate(|lexed, exa, emitter| {
            if let Lexed::Error(err) = lexed {
              emitter.emit(E::Error::from(err));
            }
            emitter.emit(E::Error::from(
              Missing::new(last_span).with_after(exa.span()),
            ));
          }))?;
          expect_item = true;
          continue;
        }
        None => {
          return Err(UnexpectedEot::eot(inp.span_since(&start_checkpoint)).into());
        }
      }
    }
  })
}

/// ```
pub fn separated_by_allow_trailing<'a, 'e: 'a, I, T, E, O, C, Sep, Lang>(
  content_parser: impl Parser<'a, I, O, E> + Clone + 'a,
  is_sep_token: impl Fn(&T) -> bool + Clone + 'a,
  is_end_token: impl Fn(&T) -> bool + Clone + 'a,
  sep_kind: impl Fn() -> Lang::SyntaxKind + Clone + 'a,
) -> impl Parser<'a, I, Spanned<C>, E> + Clone + 'a
where
  T: PunctuatorToken<'a>,
  O: AsSpan<Span> + 'a,
  Sep: 'a,
  Lang: Language,
  Lang::SyntaxKind: 'e,
  E::Error: From<UnexpectedToken<'e, T, Lang::SyntaxKind>>
    + From<UnexpectedEot>
    + From<<T::Logos as Logos<'a>>::Error>
    + From<Missing<Sep, Lang>>
    + 'a,
  I: LogoStream<'a, T, Slice = <<<T>::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
  E: ParserExtra<'a, I> + 'a,
  C: ChumskyContainer<O> + 'a,
{
  custom(move |inp| {
    let mut container = C::default();
    let start_checkpoint = inp.cursor();
    let mut last_span: Span = inp.span_since(&start_checkpoint);
    let mut expect_item = true;

    loop {
      // If we're waiting for an item, allow early termination (empty list or trailing separator)
      if expect_item {
        match inp.peek() {
          Some(Lexed::Token(tok)) if is_end_token(&tok) => {
            return Ok(Spanned::new(inp.span_since(&start_checkpoint), container));
          }
          Some(Lexed::Token(_)) => {
            let item = inp.parse(content_parser.clone())?;
            last_span = *item.as_span();
            container.push(item);
            expect_item = false;
            continue;
          }
          Some(Lexed::Error(_)) => {
            // Consume lexer error and keep waiting for an item
            inp.parse(any().validate(|lexed, _, emitter| {
              if let Lexed::Error(err) = lexed {
                emitter.emit(E::Error::from(err));
              }
            }))?;
            continue;
          }
          None => {
            return Err(UnexpectedEot::eot(inp.span_since(&start_checkpoint)).into());
          }
        }
      }

      // Expecting a separator or end token after an item
      match inp.peek() {
        Some(Lexed::Token(tok)) if is_sep_token(&tok) => {
          inp.skip();
          expect_item = true;
          continue;
        }
        Some(Lexed::Token(tok)) if is_end_token(&tok) => {
          return Ok(Spanned::new(inp.span_since(&start_checkpoint), container));
        }
        Some(Lexed::Token(Spanned { span, data: tok })) => {
          // Consume the unexpected token while emitting diagnostics
          inp.parse(
            any()
              .validate(|_, _, emitter| {
                emitter.emit(E::Error::from(UnexpectedToken::expected_one_with_found(
                  span,
                  tok.clone(),
                  sep_kind(),
                )));
                emitter.emit(E::Error::from(Missing::new(last_span).with_after(span)));
              })
              .or_not()
              .rewind(),
          )?;
          // Loop continues with expect_item still false, so we'll ask the content_parser
          expect_item = true;
          continue;
        }
        Some(Lexed::Error(_)) => {
          // Consume lexer error and keep waiting for an item
          inp.parse(any().validate(|lexed, exa, emitter| {
            if let Lexed::Error(err) = lexed {
              emitter.emit(E::Error::from(err));
            }
            emitter.emit(E::Error::from(
              Missing::new(last_span).with_after(exa.span()),
            ));
          }))?;
          expect_item = true;
          continue;
        }
        None => {
          return Err(UnexpectedEot::eot(inp.span_since(&start_checkpoint)).into());
        }
      }
    }
  })
}

/// Writes parsed items into an external container while parsing a delimited list.
///
/// This variant of [`separated_by`] is useful when the caller needs to reuse an existing
/// collection (for instance, when constructing an AST node whose storage already lives on
/// the stack). Instead of returning the container by value, the parser takes an
/// `Rc<RefCell<C>>`, pushes each parsed item into that container, and returns only the span
/// covering the entire delimited sequence. The separator/end handling and recovery
/// behaviour are identical to [`separated_by`].
///
/// Because the container is shared through `Rc<RefCell<_>>`, multiple parsers can write
/// into the same collection (e.g., when parsing nested constructs) without cloning large
/// vectors. The caller is responsible for ensuring the container is empty (or in the
/// desired initial state) before invoking the parser.
///
/// # Type Parameters
///
/// - `T`, `O`, `Sep`, `Lang`, `E`, `I`: Same as [`separated_by`].
/// - `C`: Container type implementing `ChumskyContainer<O>` and `Clone`. It is wrapped in
///   `Rc<RefCell<_>>` so the parser can mutate it across recovery branches.
///
/// # Returns
///
/// A parser that consumes a separator-delimited list, writes items into the provided
/// container, and returns a [`Span`] covering the region between the first item (or the
/// opening delimiter) and the end token. The end token is not consumed.
///
/// # Errors & Recovery
///
/// The parser emits the same diagnostics as [`separated_by`]:
///
/// - [`UnexpectedToken`] for tokens that appear where a separator/end was expected.
/// - [`Missing`] with the provided separator syntax type when a separator is absent.
/// - [`UnexpectedEot`] when the end token is missing at EOF.
/// - Lexer errors are consumed, reported, and treated as missing separators.
///
/// # Example
///
/// ```rust,ignore
/// use logosky::chumsky::separated::separated_by_with_container;
///
/// let args = Rc::new(RefCell::new(Vec::new()));
///
/// let parser = separated_by_with_container(
///     args.clone(),
///     expression_parser(),
///     |tok| tok.is_comma(),
///     |tok| tok.is_rparen(),
///     || SyntaxKind::Comma,
/// );
///
/// let span = parser.parse(stream)?;
/// let arguments = args.borrow().clone(); // populated by the parser
/// ```
pub fn separated_by_with_container<'a, 'e: 'a, I, T, E, O, C, Sep, Lang>(
  container: Rc<RefCell<C>>,
  content_parser: impl Parser<'a, I, O, E> + Clone + 'a,
  is_sep_token: impl Fn(&T) -> bool + Clone + 'a,
  is_end_token: impl Fn(&T) -> bool + Clone + 'a,
  sep_kind: impl Fn() -> Lang::SyntaxKind + Clone + 'a,
) -> impl Parser<'a, I, Span, E> + Clone + 'a
where
  T: PunctuatorToken<'a>,
  O: AsSpan<Span> + 'a,
  Lang: Language,
  Lang::SyntaxKind: 'e,
  E::Error: From<UnexpectedToken<'e, T, Lang::SyntaxKind>>
    + From<UnexpectedEot>
    + From<<T::Logos as Logos<'a>>::Error>
    + From<Missing<Sep, Lang>>
    + 'a,
  I: LogoStream<'a, T, Slice = <<<T>::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
  E: ParserExtra<'a, I> + 'a,
  C: ChumskyContainer<O> + Clone + 'a,
{
  custom(move |inp| {
    let start_checkpoint = inp.cursor();
    let mut last_span: Span = inp.span_since(&start_checkpoint);
    let mut expect_item = true;

    loop {
      // If we're waiting for an item, allow early termination (empty list or trailing separator)
      if expect_item {
        match inp.peek() {
          Some(Lexed::Token(tok)) if is_end_token(&tok) => {
            return Ok(inp.span_since(&start_checkpoint));
          }
          Some(Lexed::Token(_)) => {
            let item = inp.parse(content_parser.clone())?;
            last_span = *item.as_span();
            container.borrow_mut().push(item);
            expect_item = false;
            continue;
          }
          Some(Lexed::Error(_)) => {
            // Consume lexer error and keep waiting for an item
            inp.parse(any().validate(|lexed, _, emitter| {
              if let Lexed::Error(err) = lexed {
                emitter.emit(E::Error::from(err));
              }
            }))?;
            continue;
          }
          None => {
            return Err(UnexpectedEot::eot(inp.span_since(&start_checkpoint)).into());
          }
        }
      }

      // Expecting a separator or end token after an item
      match inp.peek() {
        Some(Lexed::Token(tok)) if is_sep_token(&tok) => {
          inp.skip();
          expect_item = true;
          continue;
        }
        Some(Lexed::Token(tok)) if is_end_token(&tok) => {
          return Ok(inp.span_since(&start_checkpoint));
        }
        Some(Lexed::Token(Spanned { span, data: tok })) => {
          // Consume the unexpected token while emitting diagnostics
          inp.parse(
            any()
              .validate(|_, _, emitter| {
                emitter.emit(E::Error::from(UnexpectedToken::expected_one_with_found(
                  span,
                  tok.clone(),
                  sep_kind(),
                )));
                emitter.emit(E::Error::from(Missing::new(last_span).with_after(span)));
              })
              .or_not()
              .rewind(),
          )?;
          // Loop continues with expect_item still false, so we'll ask the content_parser
          expect_item = true;
          continue;
        }
        Some(Lexed::Error(_)) => {
          // Consume lexer error and keep waiting for an item
          inp.parse(any().validate(|lexed, exa, emitter| {
            if let Lexed::Error(err) = lexed {
              emitter.emit(E::Error::from(err));
            }
            emitter.emit(E::Error::from(
              Missing::new(last_span).with_after(exa.span()),
            ));
          }))?;
          expect_item = true;
          continue;
        }
        None => {
          return Err(UnexpectedEot::eot(inp.span_since(&start_checkpoint)).into());
        }
      }
    }
  })
}
