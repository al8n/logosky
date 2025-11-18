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
/// - `on_trailing_sep`: Callback invoked when a separator is seen but no following
///   item exists (e.g., trailing comma at end of list). Receives the span of the last
///   successfully parsed item, the separator token, and the error emitter so you can
///   produce custom diagnostics.
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
  is_end_token: impl Fn(Option<&T>) -> bool + Clone + 'a,
  sep_kind: impl Fn() -> Lang::SyntaxKind + Clone + 'a,
  on_trailing_sep: impl Fn(Span, Spanned<T>, &mut Emitter<E::Error>) + Clone + 'a,
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
    let mut last_sep: Option<Spanned<T>> = None;

    loop {
      // If we're waiting for an item, allow early termination (empty list or trailing separator)
      if expect_item {
        match inp.peek() {
          Some(Lexed::Token(tok)) if is_end_token(Some(&tok)) => {
            // we are expecting an item, but found the end token instead;
            // A trailing separator is found, we should report something!

            // ignore the err, as we just want the emitter
            if let Some(last_sep) = last_sep.take() {
              let _ = inp.parse(
                any()
                  .validate(|_, _, emitter| {
                    on_trailing_sep(last_span, last_sep.clone(), emitter);
                  })
                  .rewind(),
              );
            }
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
            if let Some(last_sep) = last_sep.take() {
              let _ = inp.parse(
                any()
                  .validate(|_, _, emitter| {
                    on_trailing_sep(last_span, last_sep.clone(), emitter);
                  })
                  .rewind(),
              );
            }

            if is_end_token(None) {
              return Ok(Spanned::new(inp.span_since(&start_checkpoint), container));
            } else {
              return Err(UnexpectedEot::eot(inp.span_since(&start_checkpoint)).into());
            }
          }
        }
      }

      // Expecting a separator or end token after an item
      match inp.peek() {
        Some(Lexed::Token(tok)) if is_sep_token(&tok) => {
          inp.skip();
          expect_item = true;
          last_sep = Some(tok);
          continue;
        }
        Some(Lexed::Token(tok)) if is_end_token(Some(&tok)) => {
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
          if is_end_token(None) {
            return Ok(Spanned::new(inp.span_since(&start_checkpoint), container));
          }

          return Err(UnexpectedEot::eot(inp.span_since(&start_checkpoint)).into());
        }
      }
    }
  })
}

/// Parses a delimited list that tolerates trailing separators.
///
/// This is a convenience wrapper around [`separated_by`] that simply ignores trailing
/// separators instead of reporting them. It is equivalent to calling `separated_by`
/// with a no-op `on_trailing_sep` closure. Use this when your grammar treats
/// `["a", "b", ]` as valid and you do not want to emit diagnostics for the dangling
/// separator.
///
/// All other behaviour (missing separator diagnostics, unexpected tokens, etc.) is
/// identical to [`separated_by`].
pub fn separated_by_allow_trailing<'a, 'e: 'a, I, T, E, O, C, Sep, Lang>(
  content_parser: impl Parser<'a, I, O, E> + Clone + 'a,
  is_sep_token: impl Fn(&T) -> bool + Clone + 'a,
  is_end_token: impl Fn(Option<&T>) -> bool + Clone + 'a,
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
  separated_by(
    content_parser,
    is_sep_token,
    is_end_token,
    sep_kind,
    |_, _, _| {},
  )
}
