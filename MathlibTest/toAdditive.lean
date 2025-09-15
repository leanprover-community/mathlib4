import Mathlib.Algebra.Group.Defs
import Mathlib.Lean.Exception
import Mathlib.Tactic.ReduceModChar.Ext
import Qq.MetaM
open Qq Lean Meta Elab Command ToAdditive

set_option autoImplicit true
-- work in a namespace so that it doesn't matter if names clash
namespace Test

-- [note] use the below options for diagnostics:
-- set_option trace.to_additive true
-- set_option trace.to_additive_detail true
-- set_option pp.universes true
-- set_option pp.explicit true
-- set_option pp.notation false

@[to_additive bar0]
def foo0 {α} [Mul α] [One α] (x y : α) : α := x * y * 1

theorem bar0_works : bar0 3 4 = 7 := by decide

class my_has_pow (α : Type u) (β : Type v) where
  (pow : α → β → α)

instance : my_has_pow Nat Nat := ⟨fun a b => a ^ b⟩

class my_has_scalar (M : Type u) (α : Type v) where
  (smul : M → α → α)

instance : my_has_scalar Nat Nat := ⟨fun a b => a * b⟩
attribute [to_additive (reorder := 1 2) my_has_scalar] my_has_pow
attribute [to_additive (reorder := 1 2, 4 5)] my_has_pow.pow

@[to_additive bar1]
def foo1 {α : Type u} [my_has_pow α ℕ] (x : α) (n : ℕ) : α := @my_has_pow.pow α ℕ _ x n

theorem foo1_works : foo1 3 4 = Nat.pow 3 4 := by decide
theorem bar1_works : bar1 3 4 = 3 * 4 := by decide

infix:80 " ^ " => my_has_pow.pow

instance dummy_pow : my_has_pow ℕ <| PLift ℤ := ⟨fun _ _ => 5⟩

@[to_additive bar2]
def foo2 {α} [my_has_pow α ℕ] (x : α) (n : ℕ) (m : PLift ℤ) : α := x ^ (n ^ m)

theorem foo2_works : foo2 2 3 (PLift.up 2) = Nat.pow 2 5 := by decide
theorem bar2_works : bar2 2 3 (PLift.up 2) = 2 * 5 := by decide

@[to_additive bar3]
def foo3 {α} [my_has_pow α ℕ] (x : α) : ℕ → α := @my_has_pow.pow α ℕ _ x

theorem foo3_works : foo3 2 3 = Nat.pow 2 3 := by decide
theorem bar3_works : bar3 2 3 = 2 * 3 := by decide

@[to_additive bar4]
def foo4 {α : Type u} : Type v → Type (max u v) := @my_has_pow α

@[to_additive bar4_test]
lemma foo4_test {α β : Type u} : @foo4 α β = @my_has_pow α β := rfl

@[to_additive bar5]
def foo5 {α} [my_has_pow α ℕ] [my_has_pow ℕ ℤ] : True := True.intro

@[to_additive bar6]
def foo6 {α} [my_has_pow α ℕ] : α → ℕ → α := @my_has_pow.pow α ℕ _

-- fails because of workaround in `transform`. Not sure if this will show up in practice
-- @[to_additive bar7]
-- def foo7 := @my_has_pow.pow

-- theorem foo7_works : foo7 2 3 = Nat.pow 2 3 := by decide
-- theorem bar7_works : bar7 2 3 = 2 * 3 := by decide

/-- Check that we don't additivize `Nat` expressions. -/
@[to_additive bar8]
def foo8 (a b : ℕ) := a * b

theorem bar8_works : bar8 2 3 = 6 := by decide

/-- Check that we don't additivize `Nat` numerals. -/
@[to_additive bar9]
def foo9 := 1

theorem bar9_works : bar9 = 1 := by decide

@[to_additive bar10]
def foo10 (n m : ℕ) := HPow.hPow n m + n * m * 2 + 1 * 0 + 37 * 1 + 2

theorem bar10_works : bar10 = foo10 := rfl

@[to_additive bar11]
def foo11 (n : ℕ) (m : ℤ) := n * m * 2 + 1 * 0 + 37 * 1 + 2

theorem bar11_works : bar11 = foo11 := rfl

@[to_additive bar12]
def foo12 (_ : Nat) (_ : Int) : Fin 37 := ⟨2, by decide⟩

@[to_additive (reorder := 1 2, 4 5) bar13]
lemma foo13 {α β : Type u} [my_has_pow α β] (x : α) (y : β) : x ^ y = x ^ y := rfl

@[to_additive (reorder := 1 2, 4 5) bar14]
def foo14 {α β : Type u} [my_has_pow α β] (x : α) (y : β) : α := (x ^ y) ^ y

@[to_additive (reorder := 1 2, 4 5) bar15]
lemma foo15 {α β : Type u} [my_has_pow α β] (x : α) (y : β) : foo14 x y = (x ^ y) ^ y := rfl

@[to_additive (reorder := 1 2, 4 5) bar16]
lemma foo16 {α β : Type u} [my_has_pow α β] (x : α) (y : β) : foo14 x y = (x ^ y) ^ y := foo15 x y

@[to_additive bar17]
def foo17 [Group α] (x : α) : α := x * 1

@[to_additive (attr := simp) bar18]
lemma foo18 [Group α] (x : α) : foo17 x = x ∧ foo17 x = 1 * x :=
  ⟨mul_one x, mul_one x |>.trans <| one_mul x |>.symm⟩

example [Group α] (x : α) : foo17 x = 1 * x := by simp
example [Group α] (x : α) : foo17 x = x := by simp
example [AddGroup α] (x : α) : bar17 x = 0 + x := by simp
example [AddGroup α] (x : α) : bar17 x = x := by simp

/- Testing nested to_additive calls -/
@[to_additive (attr := simp, to_additive baz19) bar19]
def foo19 := 1

example {x} (h : 1 = x) : foo19 = x := by simp; guard_target = 1 = x; exact h
example {x} (h : 1 = x) : bar19 = x := by simp; guard_target = 1 = x; exact h
example {x} (h : 1 = x) : baz19 = x := by simp; guard_target = 1 = x; exact h

/- Testing that the order of the attributes doesn't matter -/
@[to_additive (attr := to_additive baz20, simp) bar20]
def foo20 := 1

example {x} (h : 1 = x) : foo20 = x := by simp; guard_target = 1 = x; exact h
example {x} (h : 1 = x) : bar20 = x := by simp; guard_target = 1 = x; exact h
example {x} (h : 1 = x) : baz20 = x := by simp; guard_target = 1 = x; exact h

@[to_additive bar21]
def foo21 {N} {A} [Pow A N] (a : A) (n : N) : A := a ^ n

run_cmd liftCoreM <| MetaM.run' <| guard <| relevantArgAttr.find? (← getEnv) `Test.foo21 == some 1

@[to_additive bar22]
abbrev foo22 {α} [Monoid α] (a : α) : ℕ → α
  | 0 => 1
  | _ => a

run_cmd liftCoreM <| MetaM.run' <| do
  -- make `abbrev` definition `reducible` automatically
  guard <| (← getReducibilityStatus `Test.bar22) == .reducible
  -- make `abbrev` definition `inline` automatically
  guard <| (Compiler.getInlineAttribute? (← getEnv) `Test.bar22) == some .inline
  -- some auxiliary definitions are also `abbrev` but not `reducible`
  guard <| (← getReducibilityStatus `Test.bar22.match_1) != .reducible
  guard <| (Compiler.getInlineAttribute? (← getEnv) `Test.bar22.match_1) == some .inline

/- test the eta-expansion applied on `foo6`. -/
run_cmd do
  let c ← getConstInfo `Test.foo6
  let e : Expr ← liftCoreM <| MetaM.run' <| expand c.value!
  let t ← liftCoreM <| MetaM.run' <| expand c.type
  let decl := c |>.updateName `Test.barr6 |>.updateType t |>.updateValue e |>.toDeclaration!
  liftCoreM <| addAndCompile decl
  -- test that we cannot transport a declaration to itself
  successIfFail <| liftCoreM <| addToAdditiveAttr `bar11_works { ref := ← getRef }

/- Test on inductive types -/
inductive AddInd : ℕ → Prop where
  | basic : AddInd 2
  | zero : AddInd 0

@[to_additive]
inductive MulInd : ℕ → Prop where
  | basic : MulInd 2
  | one : MulInd 1

run_cmd do
  unless findTranslation? (← getEnv) `Test.MulInd.one == some `Test.AddInd.zero do throwError "1"
  unless findTranslation? (← getEnv) `Test.MulInd.basic == some `Test.AddInd.basic do throwError "2"
  unless findTranslation? (← getEnv) `Test.MulInd == some `Test.AddInd do throwError "3"

@[to_additive addFixedNumeralTest]
def fixedNumeralTest {α} [One α] :=
  @OfNat.ofNat ((fun _ => ℕ) (1 : α)) 1 _

@[to_additive addFixedNumeralTest2]
def fixedNumeralTest2 {α} [One α] :=
  @OfNat.ofNat ((fun _ => ℕ) (1 : α)) 1 (@One.toOfNat1 ((fun _ => ℕ) (1 : α)) _)

/-! Test the namespace bug (https://github.com/leanprover-community/mathlib4/pull/8733).
This code should *not* generate a lemma
  `add_some_def.in_namespace`. -/
def some_def.in_namespace : Bool := false

def some_def {α : Type u} [Mul α] (x : α) : α :=
  if some_def.in_namespace then x * x else x

def myFin (_ : ℕ) := ℕ

instance : One (myFin n) := ⟨(1 : ℕ)⟩

@[to_additive bar]
def myFin.foo : myFin (n + 1) := 1

/-- We can pattern-match with `1`, which creates a term with a pure nat literal.
See https://github.com/leanprover-community/mathlib4/pull/2046 -/
@[to_additive]
def mul_foo {α} [Monoid α] (a : α) : ℕ → α
  | 0 => 1
  | 1 => 1
  | (_ + 2) => a


-- cannot apply `@[to_additive]` to `some_def` if `some_def.in_namespace` doesn't have the attribute
run_cmd liftCoreM <| successIfFail <|
    transformDecl { ref := ← getRef} `Test.some_def `Test.add_some_def


attribute [to_additive some_other_name] some_def.in_namespace
attribute [to_additive add_some_def] some_def

run_cmd do liftCoreM <| successIfFail (getConstInfo `Test.add_some_def.in_namespace)

section

set_option linter.unusedVariables false in
def foo_mul {I J K : Type} (n : ℕ) {f : I → Type} (L : Type) [∀ i, One (f i)]
  [Add I] [Mul L] : true := by trivial


@[to_additive]
instance pi.has_one {I : Type} {f : I → Type} [(i : I) → One <| f i] : One ((i : I) → f i) :=
  ⟨fun _ => 1⟩

run_cmd do
  let n ← liftCoreM <| MetaM.run' <| findMultiplicativeArg `Test.pi.has_one
  if n != 1 then throwError "{n} != 1"
  let n ← liftCoreM <| MetaM.run' <| findMultiplicativeArg `Test.foo_mul
  if n != 4 then throwError "{n} != 4"

end

@[to_additive]
def nat_pi_has_one {α : Type} [One α] : One ((x : Nat) → α) := by infer_instance

@[to_additive]
def pi_nat_has_one {I : Type} : One ((x : I) → Nat)  := pi.has_one

example : @pi_nat_has_one = @pi_nat_has_zero := rfl

section instances

class FooClass (α) : Prop where
  refle : ∀ a : α, a = a

@[to_additive]
instance FooClass_one [One α] : FooClass α := ⟨fun _ ↦ rfl⟩

lemma one_fooClass [One α] : FooClass α := by infer_instance

lemma zero_fooClass [Zero α] : FooClass α := by infer_instance

end instances

/- Test that we can rewrite with definitions with the `@[to_additive]` attribute. -/
@[to_additive]
lemma npowRec_zero [One M] [Mul M] (x : M) : npowRec 0 x = 1 := by
  rw [npowRec]

/- Test that we can rewrite with definitions without the `@[to_additive]` attribute. -/
@[to_additive addoptiontest]
lemma optiontest (x : Option α) : x.elim none some = x := by
  cases x <;> rw [Option.elim]

/- Check that `to_additive` works if a `_match` aux declaration is created. -/
@[to_additive]
def IsUnit [Mul M] (a : M) : Prop := a ≠ a

@[to_additive]
theorem isUnit_iff_exists_inv [Mul M] {a : M} : IsUnit a ↔ ∃ _ : α, a ≠ a :=
  ⟨fun h => absurd rfl h, fun ⟨_, hab⟩ => hab⟩

/-! Test that `@[to_additive]` correctly translates auxiliary declarations that do not have the
original declaration name as prefix. -/
@[to_additive]
def IsUnit' [Monoid M] (a : M) : Prop := ∃ b : M, a * b = 1

@[to_additive]
theorem isUnit'_iff_exists_inv [CommMonoid M] {a : M} : IsUnit' a ↔ ∃ b, a * b = 1 := Iff.rfl

@[to_additive]
theorem isUnit'_iff_exists_inv' [CommMonoid M] {a : M} : IsUnit' a ↔ ∃ b, b * a = 1 := by
  simp [isUnit'_iff_exists_inv, mul_comm]

/-! Test a permutation with a cycle of length > 2. -/
@[to_additive (reorder := 3 4 5)]
def reorderMulThree {α : Type _} [Mul α] (x y z : α) : α := x * y * z

/-! Test a permutation that is too big for the list of arguments. -/
/--
error: the permutation
[[2, 3, 50]]
provided by the `(reorder := ...)` option is out of bounds, the type
  {α : Type u_1} → [Mul α] → α → α → α → α
has only 5 arguments
-/
#guard_msgs in
@[to_additive (reorder := 3 4 51)]
def reorderMulThree' {α : Type _} [Mul α] (x y z : α) : α := x * y * z

/-! Test `(reorder := ...)` when the proof needs to be eta-expanded. -/
@[to_additive (reorder := 3 4 5)]
alias reorderMulThree_alias := reorderMulThree

@[to_additive (reorder := 3 4 2)]
alias reorderMulThree_alias' := reorderMulThree

@[to_additive (reorder := 3 4 5)]
def reorderMulThree_alias'' {α : Type _} [Mul α] (x y : α) : α → α := reorderMulThree x y

/--
error: invalid cycle `04`, a cycle must have at least 2 elements.
`(reorder := ...)` uses cycle notation to specify a permutation.
For example `(reorder := 1 2, 5 6)` swaps the first two arguments with each other and the fifth and the sixth argument and `(reorder := 3 4 5)` will move the fifth argument before the third argument.
-/
#guard_msgs in
@[to_additive (reorder := 04)]
example : True := trivial

/-- error: invalid position `00`, positions are counted starting from 1. -/
#guard_msgs in
@[to_additive (reorder := 100 200, 2 00)]
example : True := trivial

example {α : Type _} [Add α] (x y z : α) : reorderAddThree z x y = x + y + z := rfl


def Ones : ℕ → Q(Nat)
  | 0     => q(1)
  | (n + 1) => q($(Ones n) + $(Ones n))


-- This test just exists to see if this finishes in finite time. It should take <100ms.
-- #time
run_cmd do
  let e : Expr := Ones 300
  let _ ← liftCoreM <| MetaM.run' <| applyReplacementFun e

-- testing `isConstantApplication`
run_cmd do
  unless !(q((fun _ y => y) 3 4) : Q(Nat)).isConstantApplication do throwError "1"
  unless (q((fun x _ => x) 3 4) : Q(Nat)).isConstantApplication do throwError "2"
  unless !(q((fun x => x) 3) : Q(Nat)).isConstantApplication do throwError "3"
  unless (q((fun _ => 5) 3) : Q(Nat)).isConstantApplication do throwError "4"

@[to_additive, to_additive_dont_translate]
def MonoidEnd : Type := Unit

run_cmd do
  let stx ← `(Semigroup MonoidEnd)
  liftTermElabM do
    let e ← Term.elabTerm stx none
    guard <| additiveTest (← getEnv) e == some (.inl `Test.MonoidEnd)


@[to_additive instSemiGroupAddMonoidEnd]
instance : Semigroup MonoidEnd where
  mul _ _ := ()
  mul_assoc _ _ _ := rfl

@[to_additive]
lemma monoidEnd_lemma (x y z : MonoidEnd) : x * (y * z) = (x * y) * z := mul_assoc .. |>.symm

/-- info: Test.addMonoidEnd_lemma (x y z : AddMonoidEnd) : x * (y * z) = x * y * z -/
#guard_msgs in
#check addMonoidEnd_lemma

/-!
Some arbitrary tests to check whether additive names are guessed correctly.
-/
section guessName

def checkGuessName (s t : String) : Elab.Command.CommandElabM Unit :=
  unless guessName s == t do throwError "failed: {guessName s} != {t}"

run_cmd
  checkGuessName "HMul_Eq_LEOne_Conj₂MulLT'" "HAdd_Eq_Nonpos_Conj₂AddLT'"
  checkGuessName "OneMulSMulInvDivPow"       "ZeroAddVAddNegSubNSMul"
  checkGuessName "ProdFinprodNPowZPow"       "SumFinsumNSMulZSMul"

  -- The current design swaps all instances of `Comm`+`Add` in order to have
  -- `AddCommMonoid` instead of `CommAddMonoid`.
  checkGuessName "comm_mul_CommMul_commMul" "comm_add_AddComm_addComm"
  checkGuessName "mul_comm_MulComm_mulComm" "add_comm_AddComm_addComm"
  checkGuessName "mul_single_eq_same" "single_eq_same"
  checkGuessName "mul_support" "support"
  checkGuessName "mul_tsupport" "tsupport"
  checkGuessName "mul_indicator" "indicator"

  checkGuessName "CommMonoid" "AddCommMonoid"
  checkGuessName "commMonoid" "addCommMonoid"

  checkGuessName "CancelCommMonoid" "AddCancelCommMonoid"
  checkGuessName "cancelCommMonoid" "addCancelCommMonoid"
  checkGuessName "CancelMonoid" "AddCancelMonoid"
  checkGuessName "cancelMonoid" "addCancelMonoid"
  checkGuessName "RightCancelMonoid" "AddRightCancelMonoid"
  checkGuessName "rightCancelMonoid" "addRightCancelMonoid"
  checkGuessName "LeftCancelMonoid" "AddLeftCancelMonoid"
  checkGuessName "leftCancelMonoid" "addLeftCancelMonoid"

  checkGuessName "IsLeftRegular" "IsAddLeftRegular"
  checkGuessName "isRightRegular" "isAddRightRegular"
  checkGuessName "IsRegular" "IsAddRegular"

  checkGuessName "LTOne_LEOne_OneLE_OneLT" "Neg_Nonpos_Nonneg_Pos"
  checkGuessName "LTHMulHPowLEHDiv" "LTHAddHSMulLEHSub"
  checkGuessName "OneLEHMul" "NonnegHAdd"
  checkGuessName "OneLTHPow" "PosHSMul"
  checkGuessName "OneLTPow" "PosNSMul"
  checkGuessName "instCoeTCOneHom" "instCoeTCZeroHom"
  checkGuessName "instCoeTOneHom" "instCoeTZeroHom"
  checkGuessName "instCoeOneHom" "instCoeZeroHom"
  checkGuessName "invFun_eq_symm" "invFun_eq_symm"
  checkGuessName "MulEquiv.symmInvFun" "AddEquiv.symmInvFun"

end guessName

end Test

run_cmd Elab.Command.liftCoreM <| ToAdditive.insertTranslation `localize `add_localize

@[to_additive] def localize.r := Nat
@[to_additive add_localize] def localize := Nat
@[to_additive] def localize.s := Nat

run_cmd do
  unless findTranslation? (← getEnv) `localize.r == some `add_localize.r do throwError "1"
  unless findTranslation? (← getEnv) `localize   == some `add_localize   do throwError "2"
  unless findTranslation? (← getEnv) `localize.s == some `add_localize.s do throwError "3"

/--
warning: The source declaration one_eq_one was given the simp-attribute(s) simp, reduce_mod_char before calling @[to_additive].
The preferred method is to use something like `@[to_additive (attr := simp, reduce_mod_char)]`
to apply the attribute to both one_eq_one and the target declaration zero_eq_zero.

Note: This linter can be disabled with `set_option linter.existingAttributeWarning false`
-/
#guard_msgs in
@[simp, reduce_mod_char, to_additive]
lemma one_eq_one {α : Type*} [One α] : (1 : α) = 1 := rfl

@[to_additive (attr := reduce_mod_char, simp)]
lemma one_eq_one' {α : Type*} [One α] : (1 : α) = 1 := rfl

section
-- Test the error message for a name that cannot be additivised.

/--
error: to_additive: the generated additivised name equals the original name 'foo', meaning that no part of the name was additivised.
If this is intentional, use the `@[to_additive self]` syntax.
Otherwise, check that your declaration name is correct (if your declaration is an instance, try naming it)
or provide an additivised name using the `@[to_additive my_add_name]` syntax.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
@[to_additive]
local instance foo {α : Type*} [Semigroup α] : Monoid α := sorry

end

-- Test the error message for a wrong `to_additive existing`.

/--
error: `to_additive` validation failed:
  expected 1 universe levels, but 'Nat.le_trans' has 0 universe levels
-/
#guard_msgs in
@[to_additive existing Nat.le_trans]
lemma one_eq_one'' {α : Type*} [One α] : (1 : α) = 1 := rfl


/--
error: `to_additive` validation failed: expected
  ∀ {α : Type u} [inst : Zero α], 0 = 0
but 'Eq.trans' has type
  ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
#guard_msgs in
@[to_additive existing Eq.trans]
lemma one_eq_one''' {α : Type*} [One α] : (1 : α) = 1 := rfl

/-!
Test that @[to_additive] can reorder arguments of raw kernel projections.
-/
open Lean in
elab "unfold%" e:term : term => do
  let e ← Elab.Term.elabTerm e none
  Meta.unfoldDefinition e

@[to_additive]
def myPow {α β : Type} [i : Pow α β] (a : α) := unfold% i.1 a

/--
info: def myPow : {α β : Type} → [i : Pow α β] → α → β → α :=
fun {α β} [i : Pow α β] a => i.1 a
-/
#guard_msgs in
#print myPow
/--
info: def myNSMul : {α β : Type} → [i : SMul β α] → α → β → α :=
fun {α β} [SMul β α] a a_1 => SMul.smul a_1 a
-/
#guard_msgs in
#print myNSMul

@[to_additive]
def myMul {α : Type} [i : Mul α] (a : α) := unfold% i.1 a

/--
info: def myMul : {α : Type} → [i : Mul α] → α → α → α :=
fun {α} [i : Mul α] a => i.1 a
-/
#guard_msgs in
#print myMul
/--
info: def myAdd : {α : Type} → [i : Add α] → α → α → α :=
fun {α} [Add α] a => Add.add a
-/
#guard_msgs in
#print myAdd

/-! Test that the `existingAttributeWarning` linter doesn't fire for `to_additive self`. -/
@[simp, to_additive self]
theorem test1 : 5 = 5 := rfl

/-! Test that we can't write `to_additive self (attr := ..)`. -/

/--
error: invalid `(attr := ...)` after `self`, as there is only one declaration for the attributes.
Instead, you can write the attributes in the usual way.
-/
#guard_msgs in
@[to_additive self (attr := simp)]
theorem test2 : 5 = 5 := rfl

/-! Previously, An application that isn't a constant, such as `(no_index Add) α`, would be seen as
multiplicative, hence `α` would be set as the `to_additive_relevant_arg`. -/

@[to_additive]
def fooMul {α β : Type} (_ : (no_index Add) α) [Mul β] (x y : β) : β := x * y

@[to_additive] -- this would not translate `fooMul`
def barMul {β : Type} [Mul β] (x y : β) : β := fooMul instAddNat x y

/-! Test that additive docstrings work -/

@[to_additive /-- (via `docComment` syntax) I am an additive docstring! -/]
theorem mulTrivial : True := trivial

/-- info: (via `docComment` syntax) I am an additive docstring! -/
#guard_msgs in
run_cmd
  let some doc  ← findDocString? (← getEnv) ``addTrivial
    | throwError "no `docComment` docstring found"
  logInfo doc

/--
warning: String syntax for `to_additive` docstrings is deprecated: Use docstring syntax instead (e.g. `@[to_additive /-- example -/]`)

Update deprecated syntax to:
  "̵/̲-̲-̲ ̲(via `str` syntax) I am an additive docstring!"̵ ̲-̲/̲
-/
#guard_msgs in
@[to_additive "(via `str` syntax) I am an additive docstring!"]
theorem mulTrivial' : True := trivial

/-- info: (via `str` syntax) I am an additive docstring! -/
#guard_msgs in
run_cmd
  let some doc ← findDocString? (← getEnv) ``addTrivial'
    | throwError "no `str` docstring found"
  logInfo doc

/-! Test handling of noncomputability -/

elab "#computability " decl:ident : command => do
  let name ← liftCoreM (realizeGlobalConstNoOverloadWithInfo decl)
  let markedNonComp := isNoncomputable (← getEnv) name
  let hasNoExec := (IR.findEnvDecl (← getEnv) name).isNone
  let desc :=
    if markedNonComp then "is marked noncomputable"
    else if hasNoExec then "has no executable code"
    else "is computable"
  logInfo m!"`{name}` {desc}"

/- Both should be computable -/

@[to_additive]
def mulComputableTest : Nat := 0

/-- info: `mulComputableTest` is computable -/
#guard_msgs in #computability mulComputableTest
/-- info: `addComputableTest` is computable -/
#guard_msgs in #computability addComputableTest

/- Both should be marked noncomputable -/

@[to_additive]
noncomputable def mulMarkedNoncomputable : Nat := 0

/-- info: `mulMarkedNoncomputable` is marked noncomputable -/
#guard_msgs in #computability mulMarkedNoncomputable
/-- info: `addMarkedNoncomputable` is marked noncomputable -/
#guard_msgs in #computability addMarkedNoncomputable

noncomputable section

/- Compilation should succeed despite `noncomputable` -/

@[to_additive]
def mulComputableTest' : Nat := 0

/-- info: `mulComputableTest'` is computable -/
#guard_msgs in #computability mulComputableTest'
/-- info: `addComputableTest'` is computable -/
#guard_msgs in #computability addComputableTest'

/- Both should be marked noncomputable -/

@[to_additive]
noncomputable def mulMarkedNoncomputable' : Nat := 0

/-- info: `mulMarkedNoncomputable'` is marked noncomputable -/
#guard_msgs in #computability mulMarkedNoncomputable'
/-- info: `addMarkedNoncomputable'` is marked noncomputable -/
#guard_msgs in #computability addMarkedNoncomputable'

/-
Compilation should fail silently.

If `mulNoExec` ever becomes marked noncomputable (meaning Lean's handling of
`noncomputable section` has changed), then the check for executable code in
`Mathlib.Tactic.ToAdditive.Frontend` should be replaced with a simple `isNoncomputable` check and
mark `addNoExec` `noncomputable` as well (plus a check for whether the original declaration is an
axiom, if `to_additive` ever handles axioms).
-/

@[to_additive]
def mulNoExec {G} (n : Nonempty G) : G := Classical.choice n

/-- info: `mulNoExec` has no executable code -/
#guard_msgs in #computability mulNoExec
/-- info: `addNoExec` has no executable code -/
#guard_msgs in #computability addNoExec

end

/-! Test structures with a private constructor and private fields -/

structure MyPrivateAdd where
  private mk ::
  private add : Nat

@[to_additive]
structure MyPrivateMul where
  private mk ::
  private mul : Nat

@[to_additive]
def MyPrivateMul.mk' (a : Nat) := MyPrivateMul.mk a

@[to_additive]
def MyPrivateMul.mul' (x : MyPrivateMul) := x.mul

/-! Test the `(dont_translate := ...)` framework -/

class MyRing (α : Type*) extends Group α

@[to_additive (dont_translate := β γ) add_neg_iff_mul_inv]
lemma mul_inv_iff_mul_inv {α β γ : Type} [Group α] [MyRing β] [MyRing γ] (a : α) (b : β) (c : γ) :
    a * a⁻¹ = 1 ↔ b * b⁻¹ = 1 ∨ c * c⁻¹ = 1 := by
  simp

/--
info: add_neg_iff_mul_inv {α β γ : Type} [AddGroup α] [MyRing β] [MyRing γ] (a : α) (b : β) (c : γ) :
  a + -a = 0 ↔ b * b⁻¹ = 1 ∨ c * c⁻¹ = 1
-/
#guard_msgs in
#check add_neg_iff_mul_inv

@[to_additive (dont_translate := β) add_neg_iff_mul_inv]
def Subtype.mul_inv_iff_mul_inv {α β : Type} [Group α] [MyRing β] (a : α) (b : β) :
    {a : α // a * a⁻¹ = 1 ↔ b * b⁻¹ = 1} := by
  exists a
  simp

/--
info: Subtype.mul_inv_iff_mul_inv._proof_1 {α β : Type} [Group α] [MyRing β] (a : α) (b : β) : a * a⁻¹ = 1 ↔ b * b⁻¹ = 1
-/
#guard_msgs in
#check Subtype.mul_inv_iff_mul_inv._proof_1
/--
info: Subtype.add_neg_iff_mul_inv._proof_1 {α β : Type} [AddGroup α] [MyRing β] (a : α) (b : β) : a + -a = 0 ↔ b * b⁻¹ = 1
-/
#guard_msgs in
#check Subtype.add_neg_iff_mul_inv._proof_1

/-!
Test that `relevant_arg` and `reorder` are passed to `simps` and `.eq_1`, and to
structure fields/constructors.
-/

structure SimpleNSMul (β : Type 1) (α : Type) where
  x : Nat

@[to_additive (reorder := 1 2) (relevant_arg := 2)]
structure SimplePow (α : Type) (β : Type 1) where
  x : Nat

@[to_additive (reorder := 1 2) (attr := simps)]
def simplePowZero (α β) : SimplePow α β where
  x := 0

@[to_additive]
lemma simplePowZero_x' {β} : (simplePowZero Nat β).x = 0 := by
  rw [simplePowZero_x]

@[to_additive]
lemma simplePowZero_x'' {β} : (simplePowZero Nat β).x = 0 := by
  rw [simplePowZero.eq_1]

/-- info: simpleNSMulZero_x' {β : Type 1} : (simpleNSMulZero β ℕ).x = 0 -/
#guard_msgs in
#check simpleNSMulZero_x'
/-- info: simpleNSMulZero_x'' {β : Type 1} : (simpleNSMulZero β ℕ).x = 0 -/
#guard_msgs in
#check simpleNSMulZero_x''


structure AddMonoidAlgebra' (k G : Type) where
  x : G → k

@[to_additive (relevant_arg := 2)]
structure MonoidAlgebra' (k G : Type) where
  x : G → k

variable {G : Type} [Monoid G]

@[to_additive]
instance : Mul (MonoidAlgebra' Nat G) where
  mul a b := ⟨fun i => a.1 i * b.1 1⟩

-- Unfortunately, `relevant_arg` information isn't passed to `*.casesOn`:
/--
error: @[to_additive] failed. Type mismatch in additive declaration. For help, see the docstring of `to_additive.attr`, section `Troubleshooting`. Failed to add declaration
instAddAddMonoidAlgebra'Nat_1.match_1:
Application type mismatch: The argument
  fun x => motive x x✝
has type
  AddMonoidAlgebra' ℕ G → Sort u_1
but is expected to have type
  MonoidAlgebra' ℕ G → Sort u_1
in the application
  @MonoidAlgebra'.casesOn ℕ G fun x => motive x x✝
-/
#guard_msgs in
@[to_additive]
instance : Mul (MonoidAlgebra' Nat G) where
  mul | ⟨a⟩, ⟨b⟩ => ⟨fun i => a i * b 1⟩
