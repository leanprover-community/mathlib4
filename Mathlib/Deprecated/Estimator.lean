/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Data.Set.Operations
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.RelClasses
import Mathlib.Order.Hom.Basic
import Mathlib.Lean.Thunk

/-!
# Improvable lower bounds.

Note: this entire file is deprecated.

The typeclass `Estimator a ε`, where `a : Thunk α` and `ε : Type`,
states that `e : ε` carries the data of a lower bound for `a.get`,
in the form `bound_le : bound a e ≤ a.get`,
along with a mechanism for asking for a better bound `improve e : Option ε`,
satisfying
```
match improve e with
| none => bound e = a.get
| some e' => bound e < bound e'
```
i.e. it returns `none` if the current bound is already optimal,
and otherwise a strictly better bound.

(The value in `α` is hidden inside a `Thunk` to prevent evaluating it:
the point of this typeclass is to work with cheap-to-compute lower bounds for expensive values.)

An appropriate well-foundedness condition would then ensure that repeated improvements reach
the exact value.
-/

variable {α ε : Type*}

/--
Given `[EstimatorData a ε]`
* a term `e : ε` can be interpreted via `bound a e : α` as a lower bound for `a`, and
* we can ask for an improved lower bound via `improve a e : Option ε`.

The value `a` in `α` that we are estimating is hidden inside a `Thunk` to avoid evaluation.
-/
class EstimatorData (a : Thunk α) (ε : Type*) where
  /-- The value of the bound for `a` representation by a term of `ε`. -/
  bound : ε → α
  /-- Generate an improved lower bound. -/
  improve : ε → Option ε

/--
Given `[Estimator a ε]`
* we have `bound a e ≤ a.get`, and
* `improve a e` returns none iff `bound a e = a.get`,
  and otherwise it returns a strictly better bound.
-/
@[deprecated "No replacement: this was only used \
  in the implementation of the removed `rw_search` tactic." (since := "2025-09-11")]
class Estimator [Preorder α] (a : Thunk α) (ε : Type*) extends EstimatorData a ε where
  /-- The calculated bounds are always lower bounds. -/
  bound_le e : bound e ≤ a.get
  /-- Calling `improve` either gives a strictly better bound,
  or a proof that the current bound is exact. -/
  improve_spec e : match improve e with
    | none => bound e = a.get
    | some e' => bound e < bound e'

-- Everything in this file is deprecated,
-- but we'll just add the deprecation attribute to the main class.
set_option linter.deprecated false

open EstimatorData Set

section trivial

variable [Preorder α]

/-- A trivial estimator, containing the actual value. -/
abbrev Estimator.trivial.{u} {α : Type u} (a : α) : Type u := { b : α // b = a }

instance {a : α} : Bot (Estimator.trivial a) := ⟨⟨a, rfl⟩⟩

instance : WellFoundedGT Unit where
  wf := ⟨fun .unit => ⟨Unit.unit, nofun⟩⟩

instance (a : α) : WellFoundedGT (Estimator.trivial a) :=
  let f : Estimator.trivial a ≃o Unit := RelIso.ofUniqueOfRefl _ _
  let f' : Estimator.trivial a ↪o Unit := f.toOrderEmbedding
  f'.wellFoundedGT

instance {a : α} : Estimator (Thunk.pure a) (Estimator.trivial a) where
  bound b := b.val
  improve _ := none
  bound_le b := b.prop.le
  improve_spec b := b.prop

end trivial

section improveUntil

variable [Preorder α]

attribute [local instance] WellFoundedGT.toWellFoundedRelation in
/-- Implementation of `Estimator.improveUntil`. -/
def Estimator.improveUntilAux
    (a : Thunk α) (p : α → Bool) [Estimator a ε]
    [WellFoundedGT (range (bound a : ε → α))]
    (e : ε) (r : Bool) : Except (Option ε) ε :=
    if p (bound a e) then
      return e
    else
      match improve a e, improve_spec e with
      | none, _ => .error <| if r then none else e
      | some e', _ =>
        improveUntilAux a p e' true
termination_by (⟨_, mem_range_self e⟩ : range (bound a))

/--
Improve an estimate until it satisfies a predicate,
or else return the best available estimate, if any improvement was made.
-/
def Estimator.improveUntil (a : Thunk α) (p : α → Bool)
    [Estimator a ε] [WellFoundedGT (range (bound a : ε → α))] (e : ε) :
    Except (Option ε) ε :=
  Estimator.improveUntilAux a p e false

attribute [local instance] WellFoundedGT.toWellFoundedRelation in
/--
If `Estimator.improveUntil a p e` returns `some e'`, then `bound a e'` satisfies `p`.
Otherwise, that value `a` must not satisfy `p`.
-/
theorem Estimator.improveUntilAux_spec (a : Thunk α) (p : α → Bool)
    [Estimator a ε] [WellFoundedGT (range (bound a : ε → α))] (e : ε) (r : Bool) :
    match Estimator.improveUntilAux a p e r with
    | .error _ => ¬ p a.get
    | .ok e' => p (bound a e') := by
  rw [Estimator.improveUntilAux]
  by_cases h : p (bound a e)
  · simp only [h]; exact h
  · simp only [h]
    match improve a e, improve_spec e with
    | none, eq =>
      simp only [Bool.not_eq_true]
      rw [eq] at h
      exact Bool.bool_eq_false h
    | some e', _ =>
      exact Estimator.improveUntilAux_spec a p e' true
termination_by (⟨_, mem_range_self e⟩ : range (bound a))

/--
If `Estimator.improveUntil a p e` returns `some e'`, then `bound a e'` satisfies `p`.
Otherwise, that value `a` must not satisfy `p`.
-/
theorem Estimator.improveUntil_spec
    (a : Thunk α) (p : α → Bool) [Estimator a ε] [WellFoundedGT (range (bound a : ε → α))] (e : ε) :
    match Estimator.improveUntil a p e with
    | .error _ => ¬ p a.get
    | .ok e' => p (bound a e') :=
  Estimator.improveUntilAux_spec a p e false

end improveUntil

/-! Estimators for sums. -/
section add

variable [Preorder α]

@[simps]
instance [Add α] {a b : Thunk α} (εa εb : Type*) [EstimatorData a εa] [EstimatorData b εb] :
    EstimatorData (a + b) (εa × εb) where
  bound e := bound a e.1 + bound b e.2
  improve e := match improve a e.1 with
  | some e' => some { e with fst := e' }
  | none => match improve b e.2 with
    | some e' => some { e with snd := e' }
    | none => none

instance (a b : Thunk ℕ) {εa εb : Type*} [Estimator a εa] [Estimator b εb] :
    Estimator (a + b) (εa × εb) where
  bound_le e :=
    Nat.add_le_add (Estimator.bound_le e.1) (Estimator.bound_le e.2)
  improve_spec e := by
    dsimp
    have s₁ := Estimator.improve_spec (a := a) e.1
    have s₂ := Estimator.improve_spec (a := b) e.2
    grind

end add

/-! Estimator for the first component of a pair. -/
section fst

variable {β : Type*} [PartialOrder α] [PartialOrder β]

/--
An estimator for `(a, b)` can be turned into an estimator for `a`,
simply by repeatedly running `improve` until the first factor "improves".
The hypothesis that `>` is well-founded on `{ q // q ≤ (a, b) }` ensures this terminates.
-/
structure Estimator.fst
    (p : Thunk (α × β)) (ε : Type*) [Estimator p ε] where
  /-- The wrapped bound for a value in `α × β`,
  which we will use as a bound for the first component. -/
  inner : ε

variable [∀ a : α, WellFoundedGT { x // x ≤ a }]

instance {a : Thunk α} [Estimator a ε] : WellFoundedGT (range (bound a : ε → α)) :=
  let f : range (bound a : ε → α) ↪o { x // x ≤ a.get } :=
    Subtype.orderEmbedding (by rintro _ ⟨e, rfl⟩; exact Estimator.bound_le e)
  f.wellFoundedGT

instance [DecidableLT α] {a : Thunk α} {b : Thunk β}
    (ε : Type*) [Estimator (a.prod b) ε] [∀ (p : α × β), WellFoundedGT { q // q ≤ p }] :
    EstimatorData a (Estimator.fst (a.prod b) ε) where
  bound e := (bound (a.prod b) e.inner).1
  improve e :=
    let bd := (bound (a.prod b) e.inner).1
    Estimator.improveUntil (a.prod b) (fun p => bd < p.1) e.inner
      |>.toOption |>.map Estimator.fst.mk

/-- Given an estimator for a pair, we can extract an estimator for the first factor. -/
-- This isn't an instance as at the sole use case we need to provide
-- the instance arguments by hand anyway.
def Estimator.fstInst [DecidableLT α] [∀ (p : α × β), WellFoundedGT { q // q ≤ p }]
    (a : Thunk α) (b : Thunk β) (i : Estimator (a.prod b) ε) :
    Estimator a (Estimator.fst (a.prod b) ε) where
  bound_le e := (Estimator.bound_le e.inner : bound (a.prod b) e.inner ≤ (a.get, b.get)).1
  improve_spec e := by
    let bd := (bound (a.prod b) e.inner).1
    have := Estimator.improveUntil_spec (a.prod b) (fun p => bd < p.1) e.inner
    revert this
    simp only [EstimatorData.improve, decide_eq_true_eq]
    match Estimator.improveUntil (a.prod b) _ _ with
    | .error _ =>
      simp only
      exact fun w =>
        eq_of_le_of_not_lt
          (Estimator.bound_le e.inner : bound (a.prod b) e.inner ≤ (a.get, b.get)).1 w
    | .ok e' => exact fun w => w

end fst
