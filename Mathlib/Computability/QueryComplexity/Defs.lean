/-
Copyright (c) 2025 Tomaz Mascarenhas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving, Tomaz Mascarenhas, Eric Wieser
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Set.Insert

/-!
# Definition of a model of computation based on oracles.

This module defines an abstraction of computation with an oracle, enabling the analysis of upper
bounds on the query complexity of algorithms. It also provides a `Monad` instance for it.

See `Archive/SumOracle.lean` for an example usage.

## References

* A stochastic special case in:
  https://github.com/girving/debate/blob/862fdb1cf55df0d541b802bdb1e672d724df6398/Comp/Oracle.lean
-/


namespace QueryComplexity

/-- A deterministic computation that make decisions by querying an oracle.

A computation is either a pure value or a query to an oracle with input `i : ι` returning `ω i`.
For computations with multiple oracles, a `Sigma` or `inductive` type can be used for `ι`. -/
inductive Comp (ι : Type*) (ω : ι → Type*) (α : Type*) : Type _ where
  /-- A pure value without any oracle interaction. -/
  | protected pure : α → Comp ι ω α
  /-- A query to the oracle, and a computation to continue from its return value. -/
  | queryBind : (i : ι) → (ω i → Comp ι ω α) → Comp ι ω α

namespace Comp

section monad
variable {ι : Type*}
variable {α β : Type*}
variable {ω : ι → Type*}

instance : Pure (Comp ι ω) where pure := Comp.pure

@[simp]
lemma pure_eq : (.pure : α → Comp ι ω α) = pure := rfl

/-- A query to the oracle -/
def query (i : ι) : Comp ι ω (ω i) := queryBind i pure

/-- The standard bind operation for `Comp` -/
protected def bind (f : Comp ι ω α) (g : α → Comp ι ω β) : Comp ι ω β :=
  match f with
  | .pure x => g x
  | .queryBind i f => .queryBind i fun b => (f b).bind g

instance : Bind (Comp ι ω) where bind := Comp.bind

@[simp]
lemma bind_eq {α β} : (Comp.bind : Comp ι ω α → _ → Comp ι ω β) = Bind.bind := rfl

/-- `queryBind` is an implementation detail. -/
@[simp]
theorem queryBind_eq (i : ι) (f : ω i → Comp ι ω α) :
    queryBind i f = (query i).bind f :=
  rfl

@[simp]
protected theorem bind_pure (a : α) (g : α → Comp ι ω β) :
    (pure a : Comp ι ω α).bind g = g a := rfl

@[simp]
theorem bind_queryBind (i : ι) (f : ω i → Comp ι ω α) (g : α → Comp ι ω β) :
    (queryBind i f).bind g = .queryBind i fun b => (f b).bind g := rfl


/-- The standard map operation for `Comp` -/
protected def map (g : α → β) (f : Comp ι ω α) : Comp ι ω β :=
  match f with
  | .pure x => pure (g x)
  | .queryBind i f => .queryBind i fun b => (f b).map g

instance : Functor (Comp ι ω) where map := Comp.map

@[simp]
lemma map_eq {α β} : (Comp.map : (α → β) → (Comp ι ω α → Comp ι ω β)) = Functor.map := rfl

@[simp]
protected theorem map_queryBind (g : α → β) (i : ι) (f : ω i → Comp ι ω α) :
    (queryBind i f).map g = .queryBind i fun b => (f b).map g := rfl

@[simp]
protected theorem map_pure (g : α → β) (a : α) :
    (pure a : Comp ι ω α).map g = pure (g a) := rfl

/-- `Comp` is a monad -/
instance : Monad (Comp ι ω) where
  bind := Comp.bind
  map := Comp.map

/-- `Comp` is a lawful monad -/
instance : LawfulMonad (Comp ι ω) := LawfulMonad.mk'
  (id_map := fun x => by
    simp only [instMonad, Function.comp_id]
    induction x with
    | pure _ => rfl
    | queryBind i f h => simp [h, ← queryBind_eq])
  (pure_bind := fun x f => rfl)
  (bind_assoc := fun x f g => by
    simp [← bind_eq]
    induction x with
    | pure _ => rfl
    | queryBind i f h => simp only [bind_queryBind, h])
  (bind_pure_comp := fun g f => by
    simp [← bind_eq, ← map_eq]
    induction f with
    | pure _ => rfl
    | queryBind i f h => simp only [bind_queryBind, h, Comp.map_queryBind])

/-- A copy of `bind_queryBind` for the universe-monomorphic `Bind.bind`. -/
@[simp]
theorem bind'_query {α β} (i : ι) (f : ω i → Comp ι ω α) (g : α → Comp ι ω β) :
    queryBind i f >>= g = .queryBind i fun b => f b >>= g := rfl

/-- A copy of `map_queryBind` for the universe-monomorphic `Functor.map`. -/
@[simp]
protected theorem map'_query {α β} (g : α → β) (i : ι) (f : ω i → Comp ι ω α) :
    g <$> queryBind i f = .queryBind i fun b => g <$> f b := rfl

end monad

section run
universe u v

-- note that monad composition requires some universe monomorphism here
variable {ι : Type u}
variable {α β : Type v}
variable {ω : ι → Type v}
variable {m : Type v → Type*}
variable [Monad m]

/-- Execute `f` with the oracle `oracle`.

Some notable choices of `m`:
* `Id`, for pure oracles
* `StateT ℕ m`, for oracles which count their invocations
* `PMF` for stochastic oracles. -/
def runM (f : Comp ι ω α) (oracle : (i : ι) → m (ω i)) : m α :=
  match f with
  | .pure x => pure x
  | .queryBind i f => oracle i >>= (f · |>.runM oracle)

@[simp]
theorem runM_pure (a : α) (oracle : (i : ι) → m (ω i)) :
    runM (pure a : Comp ι ω α) oracle = pure a := rfl

@[simp]
theorem runM_queryBind (i : ι) (f : ω i → Comp ι ω α) (oracle : (i : ι) → m (ω i)) :
    runM (.queryBind i f : Comp ι ω α) oracle = oracle i >>= (f · |>.runM oracle) := rfl

@[simp]
theorem runM_query [LawfulMonad m] (i : ι) (oracle : (i : ι) → m (ω i)) :
    runM (.query i : Comp ι ω (ω i)) oracle = oracle i :=
  bind_pure _

@[simp]
theorem runM_bind [LawfulMonad m] (f : Comp ι ω α) (g : α → Comp ι ω β)
    (oracle : (i : ι) → m (ω i)) :
    runM (f >>= g) oracle = runM f oracle >>= fun a => runM (g a) oracle := by
  induction f with
  | pure _ => simp
  | queryBind i f h => simp [h, ← queryBind_eq]

@[simp]
theorem runM_map [LawfulMonad m] (g : α → β) (f : Comp ι ω α) (oracle : (i : ι) → m (ω i)) :
    runM (g <$> f) oracle = g <$> runM f oracle := by
  induction f with
  | pure _ => simp
  | queryBind i f h => simp [h]

end run

end Comp

end QueryComplexity
