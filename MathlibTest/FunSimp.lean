module

public import Mathlib.Tactic.FunSimp

@[expose] public section

open Lean Meta Elab Command Term Mathlib.Tactic.FunSimp Function

/-- Check the type of the auxiliary lemma registered by `@[fun_simp]`. -/
elab "check_preprocessed " inv:("← ")? decl:ident " : " expected:term : command =>
  liftTermElabM do
    let declName ← realizeGlobalConstNoOverloadWithInfo decl
    let expected ← elabType expected
    synthesizeSyntheticMVarsNoPostponing
    discard <| logUnassignedUsingErrorInfos (← getMVars expected)
    let some auxName := auxThmExt.getState (← getEnv) |>.get? { declName, inv := inv.isSome }
      | throwError "No preprocessed lemma for {declName}"
    let type ← inferType (← mkConstWithFreshMVarLevels auxName)
    unless ← withReducible <| isDefEq type expected do
      throwError "Expected{indentExpr expected}\nbut got{indentExpr type}"

elab "check_not_preprocessed" inv:("← ")? decl:ident : command =>
  liftTermElabM do
    let declName ← realizeGlobalConstNoOverloadWithInfo decl
    if (auxThmExt.getState (← getEnv)).contains { declName, inv := inv.isSome } then
      throwError "Unexpected preprocessed lemma for {declName}"

namespace FunSimpTest

axiom silentSorry {α : Sort*} : α

opaque add : Nat → Nat → Nat

@[fun_simp] axiom add_apply (x y : Nat) : add x y = x + y

check_preprocessed add_apply : add = fun x y => x + y

@[fun_simp] axiom add_fixed (y : Nat) : add 1 y = 1 + y

check_preprocessed add_fixed : add 1 = fun y => 1 + y

axiom add_repeated (x : Nat) : add x x = x + x

/-- error: The type of `add_repeated` is not an equality of functions -/
#guard_msgs in
attribute [fun_simp] add_repeated

opaque implicitArg {x : Nat} (y : Nat) : Nat

@[fun_simp] axiom implicitArg_apply {x : Nat} (y : Nat) :
    implicitArg (x := x) y = x + y

-- Stop at implicit arguments
check_preprocessed implicitArg_apply : ∀ x, implicitArg (x := x) = fun y => x + y

opaque dependent (n : Nat) (i : Fin n) : Nat

@[fun_simp] axiom dependent_apply (n : Nat) (i : Fin n) : dependent n i = i.val

check_preprocessed dependent_apply : dependent = @Fin.val

opaque dependentAdd (n : Nat) (i : Fin n) (y : Nat) : Nat

@[fun_simp] axiom dependentAdd_apply (n : Nat) (i : Fin n) (h : i.val = 0) (y : Nat) :
    dependentAdd n i y = y

check_preprocessed dependentAdd_apply :
    ∀ n (i : Fin n), i.val = 0 → dependentAdd n i = fun y => y

@[fun_simp] axiom add_conditional (x : Nat) (h : x = 0) (y : Nat) : add x y = y

check_preprocessed add_conditional : ∀ x, x = 0 → add x = fun y => y

opaque flippedAdd : Nat → Nat → Nat

@[fun_simp] axiom flippedAdd_apply (x y : Nat) : flippedAdd x y = y + x

check_preprocessed flippedAdd_apply : flippedAdd = fun x y => y + x

axiom apply {α β : Type*} (f : α → β) (x : α) : β

@[fun_simp] axiom apply_apply {α β : Type*} (f : α → β) (x : α) :
    apply f x = f x

check_preprocessed apply_apply : ∀ {α β : Type*}, @apply α β = fun f => f

-- Equalities of functions need no preprocessing unless reversed.
@[fun_simp] axiom add_eq : add = Nat.add

check_not_preprocessed add_eq

structure Bundled (α β : Type*) where
  toFun : α → β

instance {α β : Type*} : CoeFun (Bundled α β) (fun _ => α → β) :=
  ⟨Bundled.toFun⟩

axiom Bundled.copy {α β : Type*} (f : Bundled α β) (_tag : Nat) : Bundled α β

@[fun_simp] axiom Bundled.copy_eq {α β : Type*} (f : Bundled α β) :
    f.copy 0 = f

check_preprocessed Bundled.copy_eq :
    ∀ {α β : Type*} (f : Bundled α β), (f.copy 0 : α → β) = (f : α → β)

axiom Bundled.toFun' {α β : Type*} : Bundled α β → (α → β)

section

@[local fun_simp]
axiom Bundled.toFun_eq_toFun' {α β : Type*} (f : Bundled α β) : f.toFun = f.toFun'

/- We do not remove `f` because it is reducible with body `fun f => f.1`, which cannot be used for
rewriting. -/
check_not_preprocessed Bundled.toFun_eq_toFun'

attribute [local fun_simp ←] Bundled.toFun_eq_toFun'

-- `toFun'` is not reducible, so we do remove `f` in the other direction.
check_preprocessed ← Bundled.toFun_eq_toFun' :
    ∀ {α β : Type*}, Bundled.toFun' (α := α) (β := β) = Bundled.toFun

end

-- These are registered in `Mathlib/Tactic/FunSimp.lean`
check_preprocessed id.eq_1 : ∀ {α}, @id α = (·)
check_preprocessed curry.eq_1 : ∀ {α β γ}, @curry α β γ = fun f x y => f (x, y)
check_preprocessed uncurry.eq_1 : ∀ {α β γ}, @uncurry α β γ = fun f => fun (x, y) => f x y
check_preprocessed const.eq_1 : ∀ {α}, @const α = fun _ x _ => x
check_preprocessed comp.eq_1 : ∀ {α β γ : Type*}, @comp α β γ = fun f g x => f (g x)

example (P : (Nat → Nat) → Prop) : P id := by
  fun_simp
  guard_target = P (fun x => x)
  exact silentSorry

example (P : (Nat → Nat → Nat) → Prop) : P add := by
  fun_simp
  guard_target = P (· + ·)
  exact silentSorry

example (P : (Nat → Nat) → Prop) (x : Nat) : P (add x) := by
  fun_simp
  guard_target = P (x + ·)
  exact silentSorry

example (P : Nat → Prop) (x y : Nat) : P (add x y) := by
  fun_simp
  guard_target = P (x + y)
  exact silentSorry

example (P : (Nat → Nat) → Prop) (x : Nat) (_h : P (add x)) : True := by
  fun_simp at _h
  guard_hyp _h : P (x + ·)
  exact silentSorry

example (P : (Nat → Nat) → Prop) (x : Nat) : P (add x) := by
  conv => arg 1; fun_simp
  guard_target = P (x + ·)
  exact silentSorry

example (P : (Nat → Nat) → Prop) (x : Nat) : P (add x) := by
  simp only [fun_simp]
  guard_target = P (x + ·)
  exact silentSorry

example {α β : Type*} (f : Bundled α β) (P : (α → β) → Prop) : P (f.copy 0) := by
  fun_simp
  guard_target = P (f : α → β)
  exact silentSorry

@[fun_simp]
def double (x : Nat) : Nat := x + x

check_preprocessed double.eq_1 : double = fun x => x + x

example (P : (Nat → Nat) → Prop) : P double := by
  fun_simp
  guard_target = P (fun x => x + x)
  exact silentSorry

attribute [-fun_simp] double

example (P : (Nat → Nat) → Prop) : P double := by
  fail_if_success fun_simp
  exact silentSorry

example (P : (Nat → Nat) → Prop) : P (const Nat 0) := by
  fun_simp
  guard_target = P (fun x => 0)
  exact silentSorry

-- Test the removal of an imported `fun_simp` lemma
attribute [-fun_simp] const

example (P : (Nat → Nat) → Prop) : P (const Nat 0) := by
  fail_if_success fun_simp
  exact silentSorry

opaque triple (x : Nat) : Nat

axiom triple_apply (x : Nat) : triple x = x + x + x

section

attribute [local fun_simp] triple_apply

example (P : (Nat → Nat) → Prop) : P triple := by
  fun_simp
  guard_target = P (fun x => x + x + x)
  exact silentSorry

end

example (P : (Nat → Nat) → Prop) : P triple := by
  fail_if_success fun_simp
  exact silentSorry

@[fun_simp ←]
axiom triple_reverse (x : Nat) : x + x + x = triple x

example (P : (Nat → Nat) → Prop) : P triple := by
  fun_simp
  guard_target = P (fun x => x + x + x)
  exact silentSorry

attribute [-fun_simp] triple_reverse

example (P : (Nat → Nat) → Prop) : P triple := by
  fail_if_success fun_simp
  exact silentSorry

axiom not_eq : True

/-- error: The type of `not_eq` is not an equality -/
#guard_msgs in
attribute [fun_simp] not_eq

axiom scalar_eq : (0 : Nat) = 0

/-- error: The type of `scalar_eq` is not an equality of functions -/
#guard_msgs in
attribute [fun_simp] scalar_eq

attribute [fun_simp ←] add_eq add_apply

check_preprocessed ← add_eq : Nat.add = add
check_preprocessed ← add_apply : (· + ·) = add

attribute [fun_simp ←] Bundled.copy_eq

check_preprocessed ← Bundled.copy_eq :
    ∀ {α β : Type*} (f : Bundled α β), (f : α → β) = (f.copy 0 : α → β)

end FunSimpTest
