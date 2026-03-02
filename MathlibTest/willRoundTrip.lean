import Mathlib.Lean.Name

/-! Tests that if `Lean.Name.willRoundTrip` is true for a name, then it roundtrips. We do not
insist that if `Lean.Name.willRoundTrip` is false, then it does *not* roundtrip. -/
open Lean Name

-- `fun $n : Prop => $n`
def mkTestLambda (n : Name) : Expr :=
  .lam n (.sort 0) (.bvar 0) .default

def mkDocComment (s : String) : TSyntax `Lean.Parser.Command.docComment :=
  .mk <| mkNode ``Parser.Command.docComment #[mkAtom "/--", mkAtom (s ++ "-/")]

open Parser Elab Command in
/--
`test "some.pretty.printed.name" shouldRoundTrip name` is silent iff all of the following are true:
- `name : Name` pretty prints as `"some.pretty.printed.name"` (in a `fun` binder)
- `name.willRoundTrip == shouldRoundTrip`
- `shouldRoundTrip` implies that `"some.pretty.printed.name"` parses as an identifier with name
  `name`
-/
elab "test" str:str bool:(&"false" <|> &"true") name:term : command => do
  let shouldRoundTrip ←
    if bool.raw.matchesLit `token.false "false" then pure false
    else if bool.raw.matchesLit `token.true "true" then pure true
    else throwUnsupportedSyntax
  let n ← liftTermElabM <| unsafe Elab.Term.evalTerm Name (toTypeExpr Name) name
  unless willRoundTrip n == shouldRoundTrip do
    throwErrorAt name "``willRoundTrip {repr n}`` did not equal `{shouldRoundTrip}`"
  let env ← getEnv
  if shouldRoundTrip then
    -- Check that parsing `str` yields `name`. c.f. `Parser.runParserCategory`
    let ictx := mkInputContext str.getString "<test>"
    let s := Parser.ident.fn.run ictx { env, options := ← getOptions } (getTokenTable env)
      (mkParserState str.getString)
    if s.allErrors.isEmpty && ictx.atEnd s.pos then
      unless s.stxStack.back.getId == n do
        throwError "Name{indentD <| repr s.stxStack.back.getId}\nparsed from {str} did not match \
          elaborated name{indentD <| repr n}"
    else
      throwErrorAt str "Failed to parse {str} as an identifier, despite expecting to roundtrip"
  -- Check that pretty-printing `name` recovers `str`
  let doc := mkDocComment s!"info: fun {str.getString} => {str.getString} : Prop → Prop\n"
  elabCommand <| ←
    `(command| $doc:docComment #guard_msgs in #check by_elab return mkTestLambda $name:term)

-- test testing

/-- error: Failed to parse "foo." as an identifier, despite expecting to roundtrip -/
#guard_msgs in
test "foo." true mkSimple "foo."

/--
error: Name
  `bar
parsed from "bar" did not match elaborated name
  `foo
-/
#guard_msgs in
test "bar" true mkSimple "foo"

/--
error: Name
  `foo
parsed from "foo" did not match elaborated name
  `bar
-/
#guard_msgs in
test "foo" true mkSimple "bar"

/--
info: fun a => a : Prop → Prop
---
error: ❌️ Docstring on `#guard_msgs` does not match generated message:

- info: fun foo => foo : Prop → Prop
+ info: fun a => a : Prop → Prop
-/
#guard_msgs in
test "foo" false anonymous

-- tests
test "a" false anonymous
test "[anonymous]" false mkStr1 "_hyg"
test "«»" true mkStr1 ""
test "«.»" true mkStr1 "."
test "«{|}»" true mkStr1 "{|}"
test "««»" true mkStr1 "«"
test "»" false mkStr1 "»"
test "«name»" false mkStr1 "«name»"
test "foo.«».bar" true mkStr3 "foo" "" "bar"
test "«has ».«some space»" true mkStr2 "has " "some space"
test "«example»" true mkStr1 "example"
test "«즊򙷒򉔥񩩰𘔗𫍄򆉧»" true mkStr1 "즊򙷒򉔥񩩰𘔗𫍄򆉧"
test "eee.«58».«#iii»" true mkStr3 "eee" "58" "#iii"
test "«foo.bar».baz" true mkStr2 "foo.bar" "baz"
test "«\x00»" true mkStr1 "\x00"
test "none" true mkStr1 "none"
test "_none" true mkStr1 "_none"
test "__none" true mkStr1 "__none"
test "_none_" true mkStr1 "_none_"
test "_" false mkStr1 "_"
test "#5" false mkStr1 "#5"
test "###" false mkStr1 "###"
test "#foobar" false mkStr1 "#foobar"
test "#foo.bar.baz" false mkStr3 "#foo" "bar" "baz"
test "?m.123" false mkStr1 "?m.123"
test "???" false mkStr1 "???"
test "?a.b.c" false mkStr3 "?a" "b" "c"
test "?_" false mkStr1 "?_"
test "_inaccessible" false mkStr1 "_inaccessible" -- this one does actually parse correctly
test "foo._inaccessible" false mkStr2 "foo" "_inaccessible" -- this one also parses
test "{|}._inaccessible" false mkStr2 "{|}" "_inaccessible" -- but this one doesn't
test "foo✝" false mkStr1 "foo✝"
test "foo..bar✝" false mkStr3 "foo" "" "bar✝"
test "17" false num anonymous 17
test "foo.17" false num (mkStr1 "foo") 17
test "foo.17.bar" false str (num (mkStr1 "foo") 17) "bar"
test "MathlibTest.willRoundTrip" true mkStr2 "MathlibTest" "willRoundTrip"
test "foo" false addMacroScope (str (num `MathlibTest.willRoundTrip 3206987575) "_hygCtx") `foo 2

-- one more test that didn't fit the pattern
/--
info: fun
    «
      » =>
  «
    » : Prop → Prop
-/
#guard_msgs in
#check by_elab return mkTestLambda (mkStr1 "\n")
#guard willRoundTrip (mkStr1 "\n") == false
