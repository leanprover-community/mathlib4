/-
Copyright (c) 2025 Tomaz Mascarenhas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving, Tomaz Mascarenhas
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Computability.QueryComplexity.Defs
import Mathlib.Tactic.Cases

/-!
## Basic properties of `Comp` and its Monad instance.
-/

open Classical
noncomputable section

variable {I : Type*}
variable {ι : I → Type*}
variable {ω : {i : I} → ι i → Type*}
variable {s t u : Set I}
variable {α γ : Type*}
variable {β : Type _}

namespace QueryComplexity

namespace Comp

/-- The definition of `Comp.map` -/
lemma map_eq (f : α → β) (x : Comp ι ω s α) : f <$> x = x >>= (fun x ↦ pure (f x)) := rfl

/-- `Comp` is a lawful monad -/
instance : LawfulMonad (Comp ι ω s) := LawfulMonad.mk'
  (id_map := by
    intro α f
    simp only [map_eq, id, bind, bind']
    induction' f with _ _ _ _ _ h
    · rfl
    · simp only [bind', h])
  (pure_bind := by intro α β x f; simp only [bind, bind'])
  (bind_assoc := by
    intro _ _ _ f _ _
    simp only [bind]
    induction' f with _ _ _ _ _ h
    · rfl
    · simp only [bind', h])

/-- Running `pure` and `pure'` yields the original value -/
@[simp]
lemma value_pure' (x : α) (o : (i : I) → Oracle (ι i) ω) :
    (pure' x : Comp ι ω s α).value o = x := by
  simp only [value, run, map_pure]

@[simp]
lemma value_pure (x : α) (o : (i : I) → Oracle (ι i) ω) : (pure x : Comp ι ω s α).value o = x := by
  simp only [pure, value_pure']

/-- The definition of `Comp.bind` as `simp` lemmas -/
@[simp]
lemma pure'_bind (x : α) (f : α → Comp ι ω s β) : (pure' x : Comp ι ω s α) >>= f = f x := rfl

@[simp]
lemma query'_bind (o : I) (m : o ∈ s) (y : ι o) (f : ω y → Comp ι ω s α)
    (g : α → Comp ι ω s β) : query' o m y f >>= g = .query' o m y fun b => f b >>= g := rfl

/-- `pure` has cost 0 -/
@[simp]
lemma cost_pure (x : α) (o : (i : I) → Oracle (ι i) ω) (i : I) :
    (pure x : Comp ι ω s α).cost o i = 0 := by
  simp only [cost, run]

/-- `pure'` has cost 0 -/
@[simp]
lemma cost_pure' (x : α) (o : (i : I) → Oracle (ι i) ω) (i : I) :
    (pure' x : Comp ι ω s α).cost o i = 0 := by
  simp only [cost, run]

/-- `query'` costs one query, plus the rest -/
@[simp]
lemma cost_query' {i : I} (m : i ∈ s) (y : ι i) (f : ω y → Comp ι ω s α)
    (o : (j : I) → Oracle (ι j) ω) (j : I) :
    (query' i m y f).cost o j = (if j = i then 1 else 0) + (f (o i y)).cost o j := by
  simp [cost, run]
  exact Nat.add_comm (((f (o i y)).run o).snd j) _

@[simp]
lemma cost_query (i : I) (y : ι i) (o : (i : I) → Oracle (ι i) ω) :
    (query i y).cost o i = 1 := by
  simp only [query, cost_query', ite_true, cost_pure, ite_self, add_zero]

/-- Expansion of `query'.run` -/
lemma run_query {i : I} (m : i ∈ s) (y : ι i) (f : ω y → Comp ι ω s α)
    (o : (i : I) → Oracle (ι i) ω) : (query' i m y f).run o =
      let x := (o i) y
      let (z,c) := (f x).run o
      (z, c + fun j => if j = i then 1 else 0) := rfl

/-- The value of `query` and `query'` -/
@[simp]
lemma value_query' (i : I) (m : i ∈ s) (y : ι i) (f : ω y → Comp ι ω s α) (o : (i : I) →
    Oracle (ι i) ω) : (query' i m y f).value o = (f (o i y)).value o := by
  simp only [value, run_query]

@[simp]
lemma value_query (i : I) (y : ι i) (o : (i : I) → Oracle (ι i) ω) :
    (query i y).value o = o i y := by
  simp only [query, value_query']
  rfl

/-- The cost of `f >>= g` is `f.cost + g.cost` -/
lemma cost_bind (f : Comp ι ω s α) (g : α → Comp ι ω s β) (o : (i : I) → Oracle (ι i) ω) (i : I) :
    (f >>= g).cost o i = f.cost o i + ((g (f.value o)).cost o i) := by
  induction' f with _ _ _ _ _ h
  · simp only [cost_pure', zero_add, value_pure', bind, bind']
  · simp only [bind, bind'] at h
    simp only [cost_query', bind, bind', add_assoc, h]
    apply congr_arg₂ _ rfl
    simp only [value_query', add_right_inj]

/-- The value of `f >>= g` is the composition of the two `Comp`s -/
@[simp]
lemma value_bind (f : Comp ι ω s α) (g : α → Comp ι ω s β) (o : (i : I) → Oracle (ι i) ω) :
    (f >>= g).value o = (g (f.value o)).value o := by
  induction' f with _ _ _ _ _ h
  · rfl
  · simp only [value_query', query'_bind, h]

/-!
## `allow` and `allowAll` don't change `Comp.value`, `Comp.cost` and `pure`
-/

@[simp]
lemma value_allow (f : Comp ι ω s α) (st : s ⊆ t) (o : (i : I) → Oracle (ι i) ω) :
    (f.allow st).value o = f.value o := by
  induction' f with _ _ _ _ _ h
  · simp only [allow]
    rfl
  · simp only [allow, value_query', h]

@[simp]
lemma value_allowAll (f : Comp ι ω s α) (o : (i : I) → Oracle (ι i) ω) :
    f.allowAll.value o = f.value o := by
  apply value_allow

@[simp]
lemma cost_allow (f : Comp ι ω s α) (st : s ⊆ t) (o : (i : I) → Oracle (ι i) ω) (i : I) :
    (f.allow st).cost o i = f.cost o i := by
  induction' f with _ _ _ _ _ h
  · simp only [allow, cost_pure, cost_pure']
  · simp only [allow, cost_query', h]

@[simp]
lemma cost_allowAll (f : Comp ι ω s α) (o : (i : I) → Oracle (ι i) ω) (i : I) :
    f.allowAll.cost o i = f.cost o i := by
  apply cost_allow

@[simp]
lemma allow_pure (x : α) (st : s ⊆ t) : (pure x : Comp ι ω s α).allow st = pure x := by
  simp only [allow]

@[simp]
lemma allowAll_pure (x : α) : (pure x : Comp ι ω s α).allowAll = pure x := by
  simp only [allowAll, allow_pure]

/-!
## `map` doesn't change `Comp.value` and `Comp.cost`
-/

@[simp]
lemma value_map (f : α → β) (g : Comp ι ω s α) (o : (i : I) → Oracle (ι i) ω) :
    (f <$> g).value o = f (g.value o) := by
  simp only [map_eq, value_bind, value_pure]

@[simp]
lemma cost_map (f : α → β) (g : Comp ι ω s α) (o : (i : I) → Oracle (ι i) ω) (i : I) :
    (f <$> g).cost o i = g.cost o i := by
  simp only [map_eq, cost_bind, cost_pure, add_zero]

end Comp

end QueryComplexity
