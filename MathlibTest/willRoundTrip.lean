import Mathlib.Lean.Name

/-! Tests that if `Lean.Name.willRoundTrip` is true for a name, then it roundtrips. We do not
insist that if `Lean.Name.willRoundTrip` is false, then it does *not* roundtrip. -/
open Lean Name

-- `fun $n : Prop => $n`
def mkTestLambda (n : Name) : Expr :=
  .lam n (.sort 0) (.bvar 0) .default

def mkDocComment (s : String) : TSyntax `Lean.Parser.Command.docComment :=
  .mk <| mkNode ``Parser.Command.docComment #[mkAtom "/--", mkAtom (s ++ "-/")]

-- for easy testing
macro "test" str:str bool:(&"false" <|> &"true") name:term : command => do
  let doc := mkDocComment s!"info: fun {str.getString} => {str.getString} : Prop → Prop\n"
  let bool ←
    if bool.raw.matchesLit `token.false "false" then `(term| false)
    else if bool.raw.matchesLit `token.true "true" then `(term| true)
    else Macro.throwUnsupported
  let command1 ←
    `(command| $doc:docComment #guard_msgs in #check by_elab return mkTestLambda $name:term)
  let command2 ← `(command| #guard willRoundTrip $name:term == $bool)
  `($command1:command $command2:command)

-- test testing
/--
info: fun bar => bar : Prop → Prop
---
error: ❌️ Docstring on `#guard_msgs` does not match generated message:

- info: fun foo => foo : Prop → Prop
+ info: fun bar => bar : Prop → Prop
---
error: Expression
  (mkSimple "bar").willRoundTrip == false
did not evaluate to `true`
-/
#guard_msgs in
-- test that the name `mkSimple "bar"` pretty prints as `foo` and does not roundtrip
test "foo" false mkSimple "bar"

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
test "?m.123" false mkStr1 "?m.123"
test "???" false mkStr1 "???"
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
