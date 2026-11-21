import Mathlib.Tactic.Gavrilovich

open Gavrilovich CategoryTheory

/-! ## Errors found while parsing

The parser only finds the extent of a block (by matching corners), so these are parse errors,
which `#guard_msgs` cannot capture. Instead, we run the term parser on a string and report the
error with its position (`line:column`, with columns counted in codepoints). -/

open Lean Elab Command in
/-- Parse `s` as a term and report the parse error, if any. -/
elab "#parse_diagram " s:str : command => do
  match Parser.runParserCategory (← getEnv) `term s.getString with
  | .ok _ => logInfo "parsed"
  | .error e => logInfo e

/-- info: parsed -/
#guard_msgs in
#parse_diagram "
⌜a   b⌝
  ↘ ↙
⌞  c  ⌟"

-- misaligned bottom-left corner
/--
info: <input>:4:1: `⌞` at column 1 doesn't line up with any open box's `⌜` (open boxes start at column 0)
-/
#guard_msgs in
#parse_diagram "
⌜a   b⌝
  ↘ ↙
 ⌞ c  ⌟"

-- misaligned bottom-right corner
/-- info: <input>:4:7: `⌟` at column 7 doesn't line up with this box's `⌝` (column 6) -/
#guard_msgs in
#parse_diagram "
⌜a   b⌝
  ↘ ↙
⌞  c   ⌟"

-- tab inside a diagram
/-- info: <input>:1:2: tab character inside a diagram (columns would be ambiguous) -/
#guard_msgs in
#parse_diagram "⌜a\tb⌟"

/-! ## Errors found while elaborating -/

-- content row overflowing onto the edge column
/-- error: 'x' sits on this box's edge column (8); is this row misaligned? -/
#guard_msgs in
def bad₁ :=
    ⌜ a ⌝
      ↓ x
    ⌞ b ⌟

-- a width-unsafe glyph (long arrow, U+27F6)
/--
error: glyph '⟹' (U+27F9) is not on the diagram allowlist: alignment is by codepoint, so only glyphs known to render one column wide are allowed
-/
#guard_msgs in
def bad₂ := ⌜a ⟹ b⌟

-- subscript letters missing from Consolas
/--
error: glyph 'ₖ' (U+2096) is not on the diagram allowlist: alignment is by codepoint, so only glyphs known to render one column wide are allowed
-/
#guard_msgs in
def bad₂' := ⌜xₖ⌟

-- commas only inside parentheses
/--
error: `,` outside parentheses in label 'a,' (labels are separated by spaces; a `,` can only be part of a name such as `(a,b)`)
-/
#guard_msgs in
def badComma := ⌜a, b⌟

/-- error: `=` inside parentheses in label '(a=b,c)' (glue whole names, as in `(a,c)=(b,c)`) -/
#guard_msgs in
def badGlueInParens := ⌜(a=b,c)⌟

/-- error: unbalanced `(` in label '(a' -/
#guard_msgs in
def badParen := ⌜(a  b)⌟

-- arrow pointing at nothing
/-- error: this arrow points at nothing (its ray leaves the box) -/
#guard_msgs in
def bad₃ := ⌜a →  ⌟

-- not continuous
/-- error: not continuous: a → b in the source, but no a → b in the target -/
#guard_msgs in
def bad₄ := ⌜a → b⌟ ⇢ ⌜b → a⌟

-- glued source point split in the target
/--
error: the names of 'a=b' land on different target points ('a' and 'b'), so this isn't a function
-/
#guard_msgs in
def bad₅ := ⌜a=b⌟ ⇢ ⌜a  b⌟

-- a name missing from the target
/-- error: no point named 'b' in the target box -/
#guard_msgs in
def bad₆ := ⌜a  b⌟ ⇢ ⌜a⌟

-- labels are in the type: mismatched composition is a type error
def f₁ : ⌜a  b⌟ ⟶ ⌜a=b⌟ := ⌜a  b⌟ ⇢ ⌜a=b⌟
def f₂ : ⌜x⌟ ⟶ ⌜x → y⌟ := ⌜x⌟ ⇢ ⌜x → y⌟

/--
error: Application type mismatch: The argument
  f₂
has type
  ⌜x⌟ ⟶ ⌜x → y⌟
but is expected to have type
  ⌜a=b⌟ ⟶ ?m.5
in the application
  f₁ ≫ f₂
-/
#guard_msgs in
#check f₁ ≫ f₂

-- why `Pts` must be a structure: with a type synonym, differently-labelled spaces unify
def PtsSyn (L : List (List String)) (_E : List (ℕ × ℕ)) : Type := Fin L.length
example (x : PtsSyn [["a"]] []) : PtsSyn [["zzz"]] [] := x      -- accepted!

/--
error: Type mismatch
  x
has type
  ⌜a⌟
but is expected to have type
  ⌜zzz⌟
-/
#guard_msgs in
example (x : ⌜a⌟) : ⌜zzz⌟ := x                                  -- rejected, as it should be

-- a diagram we can't elaborate yet
/--
error: a diagram must currently be one box (a space), two boxes joined by a dashed connective (a morphism), or a box and a term joined by a dashed connective (a type of morphisms)
-/
#guard_msgs in
example := ⌜a⌟ ⇢ ⌜a⌟ ⇢ ⌜a⌟

-- still alive after all of that?
#guard_msgs in
example := ⌜ok⌟

/-! ## Terms in diagrams -/

section
variable (X : TopCat)

-- `⇢` needs a diagram on one side
/-- error: `⇢` is only for Gavrilovich diagrams; use `⟶` for morphisms in general -/
#guard_msgs in
example : X ⇢ X := 𝟙 X

-- text outside the boxes that no connective points at
/--
error: label outside any box (outside boxes, only terms that a connective points at are allowed)
-/
#guard_msgs in
example :
    ⌜a⌝
     ↓     X
    ⌞b⌟ := sorry

-- terms are parsed and elaborated in place
/-- error: unexpected end of input; expected ')', ',' or ':' -/
#guard_msgs in
example :
    ⌜a⌝
     ↓   ⇢ (X
    ⌞b⌟ := sorry

/--
error: Function expected at
  X
but this term has type
  TopCat

Note: Expected a function because this term is being applied to the argument
  X
-/
#guard_msgs in
example :
    ⌜a⌝
     ↓   ⇢ X X
    ⌞b⌟ := sorry

-- a term ends at two consecutive spaces
/--
error: label outside any box (outside boxes, only terms that a connective points at are allowed)
-/
#guard_msgs in
example :
    ⌜a⌝
     ↓   ⇢ X  X
    ⌞b⌟ := sorry
end

/-! ## Points and patterns -/

-- `Space.hom` with a map that isn't continuous
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: not continuous: a → b in the source, but no c → o in the target
-/
#guard_msgs in
def bad₇ : ⌜a → b⌟ ⟶ ⌜o → c⌟ :=
  Space.hom fun | pt(a) => pt(c) | pt(b) => pt(o)

/-- error: no point named 'z' in this space (its points are a=b, c) -/
#guard_msgs in
example : ⌜a=b  c⌟ := pt(z)

/-- error: no point named 'z' in this space (its points are a, b) -/
#guard_msgs in
def g₁ : ⌜a  b⌟ → ℕ
  | pt(a) => 1
  | pt(z) => 2

/-- error: no point named '("a", 2)' in this space -/
#guard_msgs in
example : Space [[("a", 1)], [("b", 2)]] [] := pt[("a", 2)]

/--
error: Missing cases:
(Pts.mk (Fin.mk (Nat.succ (Nat.succ _)) _))
-/
#guard_msgs in
def g₂ : ⌜a  b  c⌟ → ℕ
  | pt(a) => 1
  | pt(b) => 2

/--
error: Redundant alternative: Any expression matching
  pt(a)
will match one of the preceding alternatives
-/
#guard_msgs in
def g₃ : ⌜a=b⌟ → ℕ
  | pt(a) => 1
  | pt(b) => 2

/-! ### Type ascriptions inside a block -/

-- the type of morphisms is `⟶`, not `⇢` (which is a morphism)
/--
error: this connective is a morphism; for the type of morphisms after the `:` of a type ascription, use `⟶` (or `──→`)
-/
#guard_msgs in
example :=
    (⌜       ⌝     ⌜       ⌝     ⌜       ⌝     ⌜       ⌝
      o₁   o₂   ⇢   o₁   o₂   :   o₁   o₂   ⇢   o₁   o₂
        ↘ ↙           ↘ ↙           ↘ ↙           ↘ ↙
     ⌞   c   ⌟     ⌞   c   ⌟     ⌞   c   ⌟     ⌞   c   ⌟)

-- the type is the expected type, so the morphism is relabelled to it, which can be ambiguous
/--
error: this morphism can be relabelled to have type
  ⌜x → z ← y⌟ ⟶ ⌜x → z ← y⌟
in more than one way, giving different maps. Choose one by ascribing names in that type to points, e.g. c(=z), o₁(=x), o₂(=y) in the source box; c(=z), o₁(=x), o₂(=y) in the target box
-/
#guard_msgs in
example :=
    (⌜       ⌝     ⌜       ⌝     ⌜       ⌝     ⌜       ⌝
      o₁   o₂   ⇢   o₁   o₂   :    x   y    ⟶    x   y
        ↘ ↙           ↘ ↙           ↘ ↙           ↘ ↙
     ⌞   c   ⌟     ⌞   c   ⌟     ⌞   z   ⌟     ⌞   z   ⌟)

/-- error: a second type ascription `:` in this block -/
#guard_msgs in
example :=
    (⌜       ⌝     ⌜       ⌝
      o₁   o₂   :   o₁   o₂   :  TopCat
        ↘ ↙           ↘ ↙
     ⌞   c   ⌟     ⌞   c   ⌟)


/-! ### Ascriptions -/

/-- error: an ascription `(=…)` must come at the end of the label 'a(=o)b' -/
#guard_msgs in
example := ⌜a⌟ ⇢ ⌜a(=o)b⌟

/--
error: the label '(=o)' has an ascription but no name before it (write e.g. `a(=o)`, or `_(=o)` for a point that nothing maps to)
-/
#guard_msgs in
example := ⌜a⌟ ⇢ ⌜(=o)⌟

/-- error: malformed glued label 'a(=)' (write `a=b` or `a(=o)`, no spaces) -/
#guard_msgs in
example := ⌜a⌟ ⇢ ⌜a(=)⌟

/--
error: `,` outside parentheses in label 'a(=o,p)' (labels are separated by spaces; a `,` can only be part of a name such as `(a,b)`)
-/
#guard_msgs in
example := ⌜a⌟ ⇢ ⌜a(=o,p)⌟

-- names must be distinct both as names of points, and as names matching points. A plain name is
-- a name of its point only if the box keeps its own names
/--
error: name 'o' appears twice in this box. It is relabelled only if the morphism has a type that says which space this box is; otherwise its plain names are names in it.
-/
#guard_msgs in
example := ⌜a  o⌟ ⇢ ⌜a(=o)  o⌟

/-- error: name 'o' appears twice in this box -/
#guard_msgs in
example := ⌜a⌟ ⇢ ⌜a(=o)  b(=o)⌟

/-- error: name 'a' appears twice in this box -/
#guard_msgs in
example := ⌜a⌟ ⇢ ⌜a(=o)  a(=p)⌟

/--
error: ascriptions `(=…)` are only for the boxes of a morphism, whose points are matched by the names before them
-/
#guard_msgs in
example := ⌜a(=o)⌟

/--
error: ascriptions `(=…)` are only for the boxes of a morphism, whose points are matched by the names before them
-/
#guard_msgs in
example := ⌜a⌟ ⟶ ⌜a(=o)⌟

/-- error: '_(=a)' has no name to find its image in the target box by -/
#guard_msgs in
example := ⌜_(=a)⌟ ⇢ ⌜o⌟

-- given an expected type, ascriptions must be right
/--
error: 'p' is not the name of a point in
  ⌜o → c⌟
-/
#guard_msgs in
example : ⌜a  b⌟ ⟶ ⌜o → c⌟ := ⌜a  b⌟ ⇢ ⌜a(=p) → b⌟

/--
error: this box is relabelled to
  ⌜o → c⌟
which has a point named 'c', but this point goes to its point 'o'
-/
#guard_msgs in
example : ⌜a  b⌟ ⟶ ⌜o → c⌟ := ⌜a  b⌟ ⇢ ⌜a(=c) → b⌟

-- once there is an ascription, plain names in the target box only match points, so they don't
-- choose how it is relabelled, even if they are names in the target space
/--
error: this morphism can be relabelled to have type
  ⌜a  b  c  d⌟ ⟶ ⌜a  b  c  d⌟
in more than one way, giving different maps. Choose one by ascribing names in that type to points, e.g. a(=a), b(=b) in the target box
-/
#guard_msgs in
example : ⌜a  b  c  d⌟ ⟶ ⌜a  b  c  d⌟ := ⌜a  b  c  d⌟ ⇢ ⌜a  b  _(=c)  c=d(=d)⌟

/-! ### Holes -/

/--
error: can't tell the name of this point `_` in its space: give the morphism a type that says which space this box is, or name it, as in `_(=o)`
-/
#guard_msgs in
example := ⌜a⌟ ⇢ ⌜a  _⌟

/--
error: can't tell the name of this point `_` in its space: give the morphism a type that says which space this box is, or name it, as in `_(=o)`
-/
#guard_msgs in
example := (⌜a⌟ ⇢ ⌜a  _⌟ : ⌜a⌟ ⟶ _)

/-- error: `_` is a point named by the expected type of a morphism, so it is only for the boxes of a morphism -/
#guard_msgs in
example := ⌜a  _⌟

/-- error: `_` can't be glued to names in the label '_=a' (`_` matches nothing, so `_=a` is just `a`) -/
#guard_msgs in
example := ⌜a⌟ ⇢ ⌜_=a⌟

/-- error: '_' has no name to find its image in the target box by -/
#guard_msgs in
example : ⌜a⌟ ⟶ ⌜b⌟ := ⌜_⌟ ⇢ ⌜b⌟

/-! ### Box-drawing glyphs -/

/-- error: this connective has no arrowhead (write e.g. `╌╌→`, or `╎` above `↓`) -/
#guard_msgs in
example := ⌜a⌟ ╌╌ ⌜a⌟

/-- error: this connective is a morphism; for the type of morphisms after the `:` of a type ascription, use `⟶` (or `──→`) -/
#guard_msgs in
example :=
    (┌       ┐     ┌     T      ┐     ┌       ┐     ┌   T   ┐
                        ╱ ╲                            ╱ ╲
      o₁   o₂  ╌╌→  TF=o₁  o₂=FT   :   o₁   o₂  ╌╌→  TF   FT
        ╲ ╱              ╲ ╱             ╲ ╱           ╲ ╱
     └   c   ┘     └      c     ┘     └   c   ┘     └   F   ┘)

