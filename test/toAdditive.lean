import Mathlib.Algebra.Group.Defs
import Mathlib.Lean.Exception
import Mathlib.Util.Time
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

class my_has_pow (α : Type u) (β : Type v) :=
  (pow : α → β → α)

instance : my_has_pow Nat Nat := ⟨fun a b => a ^ b⟩

class my_has_scalar (M : Type u) (α : Type v) :=
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

initialize testExt : SimpExtension ←
  registerSimpAttr `simp_test "test"

@[to_additive bar17]
def foo17 [Group α] (x : α) : α := x * 1

@[to_additive (attr := simp) bar18]
lemma foo18 [Group α] (x : α) : foo17 x = x ∧ foo17 x = 1 * x :=
  ⟨mul_one x, mul_one x |>.trans <| one_mul x |>.symm⟩

example [Group α] (x : α) : foo17 x = 1 * x := by simp
example [Group α] (x : α) : foo17 x = x := by simp
example [AddGroup α] (x : α) : bar17 x = 0 + x := by simp
example [AddGroup α] (x : α) : bar17 x = x := by simp

run_cmd do
  let mul1 := `test.toAdditive._auxLemma |>.mkNum 1
  let mul2 := `test.toAdditive._auxLemma |>.mkNum 2
  let add1 := `test.toAdditive._auxLemma |>.mkNum 3
  let add2 := `test.toAdditive._auxLemma |>.mkNum 4
  unless findTranslation? (← getEnv) mul1 == some add1 do throwError "1"
  unless findTranslation? (← getEnv) mul2 == some add2 do throwError "2"

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
  unless findTranslation? (← getEnv) `Test.MulInd.basic == none do throwError "2"
  unless findTranslation? (← getEnv) `Test.MulInd == some `Test.AddInd do throwError "3"

@[to_additive addFixedNumeralTest]
def fixedNumeralTest {α} [One α] :=
  @OfNat.ofNat ((fun _ => ℕ) (1 : α)) 1 _

@[to_additive addFixedNumeralTest2]
def fixedNumeralTest2 {α} [One α] :=
  @OfNat.ofNat ((fun _ => ℕ) (1 : α)) 1 (@One.toOfNat1 ((fun _ => ℕ) (1 : α)) _)

/-! Test the namespace bug (#8733). This code should *not* generate a lemma
  `add_some_def.in_namespace`. -/
def some_def.in_namespace : Bool := false

def some_def {α : Type u} [Mul α] (x : α) : α :=
  if some_def.in_namespace then x * x else x

def myFin (_ : ℕ) := ℕ

instance : One (myFin n) := ⟨(1 : ℕ)⟩

@[to_additive bar]
def myFin.foo : myFin (n+1) := 1

/-- We can pattern-match with `1`, which creates a term with a pure nat literal. See #2046 -/
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

set_option linter.unusedVariables false
-- Porting note: not sure what the tests do, but the linter complains.

def foo_mul {I J K : Type} (n : ℕ) {f : I → Type} (L : Type) [∀ i, One (f i)]
  [Add I] [Mul L] : true := by trivial


@[to_additive]
instance pi.has_one {I : Type} {f : I → Type} [(i : I) → One <| f i] : One ((i : I) → f i) :=
  ⟨fun _ => 1⟩

run_cmd do
  let n ← liftCoreM <| MetaM.run' <| firstMultiplicativeArg `Test.pi.has_one
  if n != 1 then throwError "{n} != 1"
  let n ← liftCoreM <| MetaM.run' <| firstMultiplicativeArg `Test.foo_mul
  if n != 4 then throwError "{n} != 4"

end

@[to_additive]
def nat_pi_has_one {α : Type} [One α] : One ((x : Nat) → α) := by infer_instance

@[to_additive]
def pi_nat_has_one {I : Type} : One ((x : I) → Nat)  := pi.has_one

example : @pi_nat_has_one = @pi_nat_has_zero := rfl

section test_noncomputable

@[to_additive Bar.bar]
noncomputable def Foo.foo (h : ∃ _ : α, True) : α := Classical.choose h

@[to_additive Bar.bar']
def Foo.foo' : ℕ := 2

theorem Bar.bar'_works : Bar.bar' = 2 := by decide

run_cmd (do
  if !isNoncomputable (← getEnv) `Test.Bar.bar then throwError "bar shouldn't be computable"
  if isNoncomputable (← getEnv) `Test.Bar.bar' then throwError "bar' should be computable")
end test_noncomputable

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
lemma optiontest (x : Option α) : x.elim .none Option.some = x := by
  cases x <;> rw [Option.elim]

/- Check that `to_additive` works if a `_match` aux declaration is created. -/
@[to_additive]
def IsUnit [Mul M] (a : M) : Prop := a ≠ a

@[to_additive]
theorem isUnit_iff_exists_inv [Mul M] {a : M} : IsUnit a ↔ ∃ _ : α, a ≠ a :=
  ⟨fun h => absurd rfl h, fun ⟨_, hab⟩ => hab⟩

/-! Test that `@[to_additive]` correctly translates auxiliary declarations that do not have the
original declaration name as prefix.-/
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

example {α : Type _} [Add α] (x y z : α) : reorderAddThree z x y = x + y + z := rfl


def Ones : ℕ → Q(Nat)
  | 0     => q(1)
  | (n+1) => q($(Ones n) + $(Ones n))


-- this test just exists to see if this finishes in finite time. It should take <100ms.
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
