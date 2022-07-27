import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.NormCast
import Mathlib.Lean.Exception
open Lean

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

attribute [to_additive_reorder 1] my_has_pow
attribute [to_additive_reorder 1 4] my_has_pow.pow
attribute [to_additive my_has_scalar] my_has_pow

@[to_additive bar1]
def foo1 {α : Type u} [my_has_pow α ℕ] (x : α) (n : ℕ) : α := @my_has_pow.pow α ℕ _ x n

theorem foo1_works : foo1 3 4 = Nat.pow 3 4 := by decide
theorem bar1_works : bar1 3 4 = 3 * 4 := by decide

infix:80 " ^ " => my_has_pow.pow

instance dummy_pow : my_has_pow ℕ $ plift ℤ := ⟨fun x y => 0⟩
instance dummy_smul : my_has_scalar (plift ℤ) ℕ := ⟨fun x y => 0⟩
attribute [to_additive dummy_smul] dummy_pow

set_option pp.universes true
@[to_additive bar2]
def foo2 {α} [my_has_pow α ℕ] (x : α) (n : ℕ) (m : plift ℤ) : α := x ^ (n ^ m)

theorem foo2_works : foo2 2 3 (plift.up 2) = Nat.pow 2 0 := by decide
-- [todo] should it still be using dummy?
theorem bar2_works : bar2 2 3 (plift.up 2) =  2 * (dummy_smul.1 (plift.up 2) 3) := by decide

@[to_additive bar3]
def foo3 {α} [my_has_pow α ℕ] (x : α) : ℕ → α := @my_has_pow.pow α ℕ _ x

theorem foo3_works : foo3 2 3 = Nat.pow 2 3 := by decide
theorem bar3_works : bar3 2 3 =  2 * 3 := by decide

@[to_additive bar4]
def foo4 {α : Type u} : Type v → Type (max u v) := @my_has_pow α

@[to_additive bar4_test]
lemma foo4_test {α β : Type u} : @foo4 α β = @my_has_pow α β := rfl

@[to_additive bar5]
def foo5 {α} [my_has_pow α ℕ] [my_has_pow ℕ ℤ] : True := True.intro

@[to_additive bar6]
def foo6 {α} [my_has_pow α ℕ] : α → ℕ → α := @my_has_pow.pow α ℕ _

@[to_additive bar7]
def foo7 := @my_has_pow.pow

theorem foo7_works : foo7 2 3 = Nat.pow 2 3 := by decide
theorem bar7_works : bar7 2 3 =  2 * 3 := by decide

/- test the eta-expansion applied on `foo6`. -/
run_cmd do
  let env ← getEnv
  let c ← getConstInfo `Test.foo6
  let e : Expr ← Lean.Elab.Command.liftCoreM <| Lean.Meta.MetaM.run' <| ToAdditive.expand c.value!
  let t ← Lean.Elab.Command.liftCoreM <| Lean.Meta.MetaM.run' <| ToAdditive.expand c.type
  let decl := c |>.updateName `Test.barr6 |>.updateType t |>.updateValue e |>.toDeclaration!
  addAndCompile decl
  return ()

/-! Test the namespace bug (#8733). This code should *not* generate a lemma
  `add_some_def.in_namespace`. -/
def some_def.in_namespace : Bool := false

def some_def {α : Type u} [Mul α] (x : α) : α :=
if some_def.in_namespace then x * x else x


-- cannot apply `@[to_additive]` to `some_def` if `some_def.in_namespace` doesn't have the attribute
run_cmd do
  Lean.Elab.Command.liftCoreM <| successIfFail (ToAdditive.transformDecl `Test.some_def `Test.add_some_def)


attribute [to_additive some_other_name] some_def.in_namespace
attribute [to_additive add_some_def] some_def

run_cmd do
  Lean.Elab.Command.liftCoreM <| successIfFail (getConstInfo `Test.add_some_def.in_namespace)

-- [todo] currently this test breaks.
-- example : (add_units.mk_of_add_eq_zero 0 0 (by simp) : ℕ)
--         = (add_units.mk_of_add_eq_zero 0 0 (by simp) : ℕ) :=
-- by normCast

def foo_mul {I J K : Type} (n : ℕ) {f : I → Type} (L : Type) [∀ i (n : ℕ), Bool → One (f i)]
  [Add I] [Mul L] : true := by trivial


@[to_additive]
instance pi.has_one {I : Type} {f : I → Type} [(i : I) → One $ f i] : One ((i : I) → f i) :=
  ⟨fun _ => 1⟩

run_cmd do
  let n ← Lean.Elab.Command.liftCoreM <| Lean.Meta.MetaM.run' <| ToAdditive.firstMultiplicativeArg `Test.pi.has_one
  if n != some 1 then throwError "{n} != 1"
  let n ← Lean.Elab.Command.liftCoreM <| Lean.Meta.MetaM.run' <| ToAdditive.firstMultiplicativeArg `Test.foo_mul
  if n != some 4 then throwError "{n} != 4"

@[to_additive]
def nat_pi_has_one {α : Type} [One α] : One ((x : Nat) → α) := by infer_instance

@[to_additive]
def pi_nat_has_one {I : Type} : One ((x : I) → Nat)  := pi.has_one

end Test
