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

/-- The definition of `Comp.bind` as `simp` lemmas -/
@[simp]
lemma pure'_bind (x : α) (f : α → Comp ι ω s β) : (pure' x : Comp ι ω s α) >>= f = f x := rfl

@[simp]
lemma query'_bind (o : I) (m : o ∈ s) (y : ι o) (f : ω y → Comp ι ω s α)
    (g : α → Comp ι ω s β) : query' o m y f >>= g = .query' o m y fun b => f b >>= g := rfl

/-- `Comp` is a lawful monad -/
instance : LawfulMonad (Comp ι ω s) := LawfulMonad.mk'
  (id_map := fun x => by
    simp only [map_eq, id, bind, bind']
    induction x with
    | pure' _ => rfl
    | query' _ _ _ _ h => simp only [bind', h])
  (pure_bind := fun x f => rfl)
  (bind_assoc := fun x f g => by
    simp only [bind]
    induction x with
    | pure' _ => rfl
    | query' _ _ _ _ h => simp only [bind', h])

variable [DecidableEq I]

/-- Running `pure` and `pure'` yields the original value -/
@[simp]
lemma value_pure' (x : α) (o : (i : I) → Oracle (ι i) ω) :
    (pure' x : Comp ι ω s α).value o = x := by
  simp only [value, run, map_pure]

@[simp]
lemma value_pure (x : α) (o : (i : I) → Oracle (ι i) ω) : (pure x : Comp ι ω s α).value o = x := by
  simp only [pure, value_pure']

/-- `pure` has cost 0 -/
@[simp]
lemma cost_pure (x : α) (o : (i : I) → Oracle (ι i) ω) :
    (pure x : Comp ι ω s α).cost o = 0 := by
  ext i
  simp [cost, run]

/-- `pure'` has cost 0 -/
@[simp]
lemma cost_pure' (x : α) (o : (i : I) → Oracle (ι i) ω) :
    (pure' x : Comp ι ω s α).cost o = 0 := by
  ext i
  simp [cost, run]

/-- `query'` costs one query, plus the rest -/
@[simp]
lemma cost_query' {i : I} (m : i ∈ s) (y : ι i) (f : ω y → Comp ι ω s α)
    (o : (j : I) → Oracle (ι j) ω) :
    (query' i m y f).cost o = Pi.single i 1 + (f (o i y)).cost o := by
  ext j
  simp [cost, run]
  exact Nat.add_comm (((f (o i y)).run o).snd j) _

@[simp]
lemma cost_query (i : I) (y : ι i) (o : (i : I) → Oracle (ι i) ω) :
    (query i y).cost o i = 1 := by
  simp [query]

/-- Expansion of `query'.run` -/
lemma run_query {i : I} (m : i ∈ s) (y : ι i) (f : ω y → Comp ι ω s α)
    (o : (i : I) → Oracle (ι i) ω) : (query' i m y f).run o =
      let x := (o i) y
      let (z,c) := (f x).run o
      (z, c + Pi.single i 1) := rfl

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
lemma cost_bind (f : Comp ι ω s α) (g : α → Comp ι ω s β) (o : (i : I) → Oracle (ι i) ω) :
    (f >>= g).cost o = f.cost o + (g (f.value o)).cost o := by
  ext i
  induction f with
  | pure' _ => simp
  | query' _ _ _ _ h =>
    simp only [bind, bind'] at h
    simp only [cost_query', bind, bind', add_assoc, h, Pi.add_apply]
    apply congr_arg₂ _ rfl
    simp only [value_query', add_right_inj]

/-- The value of `f >>= g` is the composition of the two `Comp`s -/
@[simp]
lemma value_bind (f : Comp ι ω s α) (g : α → Comp ι ω s β) (o : (i : I) → Oracle (ι i) ω) :
    (f >>= g).value o = (g (f.value o)).value o := by
  induction f with
  | pure' _ => rfl
  | query' _ _ _ _ h =>
    simp only [value_query', query'_bind, h]

/-!
## `allow` doesn't change `Comp.value`, `Comp.cost` and `pure`
-/

@[simp]
lemma value_allow (f : Comp ι ω s α) (st : s ⊆ t) (o : (i : I) → Oracle (ι i) ω) :
    (f.allow st).value o = f.value o := by
  induction f with
  | pure' _ =>
    simp only [allow]
    rfl
  | query' _ _ _ _ h =>
    simp only [allow, value_query', h]

@[simp]
lemma cost_allow (f : Comp ι ω s α) (st : s ⊆ t) (o : (i : I) → Oracle (ι i) ω) :
    (f.allow st).cost o = f.cost o := by
  induction f with
  | pure' _ => simp only [allow, cost_pure, cost_pure']
  | query' _ _ _ _ h => simp only [allow, cost_query', h]

omit [DecidableEq I] in
@[simp]
lemma allow_pure (x : α) (st : s ⊆ t) : (pure x : Comp ι ω s α).allow st = pure x := by
  simp only [allow]

/-!
## `map` doesn't change `Comp.value` and `Comp.cost`
-/

@[simp]
lemma value_map (f : α → β) (g : Comp ι ω s α) (o : (i : I) → Oracle (ι i) ω) :
    (f <$> g).value o = f (g.value o) := by
  simp only [map_eq, value_bind, value_pure]

@[simp]
lemma cost_map (f : α → β) (g : Comp ι ω s α) (o : (i : I) → Oracle (ι i) ω) :
    (f <$> g).cost o = g.cost o := by
  simp only [map_eq, cost_bind, cost_pure, add_zero]

end Comp

end QueryComplexity
