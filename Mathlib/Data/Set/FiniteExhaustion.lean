/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Set.Prod
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.FBinop

/-!
# Finite Exhaustions

This file defines a structure called `FiniteExhaustion` which represents an exhaustion of a
countable set by an increasing sequence of finite sets. Given a countable set `s`,
`FiniteExhaustion.choice s` is a choice of a finite exhaustion.
-/

@[expose] public section

open Set

/-- A `FiniteExhaustion` of a set `s` is a monotonically increasing sequence
of finite sets such that their union is `s`. -/
structure Set.FiniteExhaustion {α : Type*} (s : Set α) where
  /-- The underlying sequence of a `FiniteExhaustion`. -/
  toFun : ℕ → Set α
  /-- Every set in a `FiniteExhaustion` is finite. -/
  finite' : ∀ n, Finite (toFun n)
  /-- The sequence of sets in a `FiniteExhaustion` are monotonically increasing. -/
  subset_succ' : ∀ n, toFun n ⊆ toFun (n + 1)
  /-- The union of all sets in a `FiniteExhaustion` equals `s` -/
  iUnion_eq' : ⋃ n, toFun n = s

namespace Set.FiniteExhaustion

instance {α : Type*} {s : Set α} : FunLike (FiniteExhaustion s) ℕ (Set α) where
  coe := toFun
  coe_injective' | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

instance {α : Type*} {s : Set α} : RelHomClass (FiniteExhaustion s) LE.le HasSubset.Subset where
  map_rel K _ _ h := monotone_nat_of_le_succ (fun n ↦ K.subset_succ' n) h

instance {α : Type*} {s : Set α} {K : FiniteExhaustion s} {n : ℕ} : Finite (K n) :=
  K.finite' n

variable {α : Type*} {s : Set α} (K : FiniteExhaustion s)

@[simp]
theorem toFun_eq_coe : K.toFun = K := rfl

protected theorem finite (n : ℕ) : (K n).Finite := K.finite' n

theorem subset_succ (n : ℕ) : K n ⊆ K (n + 1) := K.subset_succ' n

@[gcongr]
protected theorem mono {m n : ℕ} (h : m ≤ n) : K m ⊆ K n :=
  OrderHomClass.mono K h

@[simp]
theorem iUnion_eq : ⋃ n, K n = s :=
  K.iUnion_eq'

/-- A choice of a `FiniteExhaustion` for a countable set `s`. -/
noncomputable def _root_.Set.Countable.finiteExhaustion {s : Set α} (hs : s.Countable) :
    FiniteExhaustion s := by
  apply Classical.choice
  by_cases h : Nonempty s
  · obtain ⟨f, hf⟩ := @exists_surjective_nat s h hs
    refine ⟨fun n ↦ (Subtype.val ∘ f) '' {i | i ≤ n}, ?_, ?_, ?_⟩
    · exact fun n ↦ Finite.image _ (finite_le_nat n)
    · grind
    · simp [← image_image, ← image_iUnion, iUnion_le_nat, range_eq_univ.mpr hf]
  · refine ⟨fun _ ↦ ∅, by simp [Finite.to_subtype], fun n ↦ by simp, ?_⟩
    simp [Set.not_nonempty_iff_eq_empty'.mp h]

lemma Set.nonempty_finiteExhaustion_iff {s : Set α} :
    Nonempty s.FiniteExhaustion ↔ s.Countable := by
  refine ⟨fun ⟨K⟩ ↦ ?_, fun h ↦ ⟨h.finiteExhaustion⟩⟩
  rw [← K.iUnion_eq]
  exact countable_iUnion <| fun i ↦ (K.finite i).countable

section prod

variable {β : Type*} {t : Set β} (K' : FiniteExhaustion t)

/-- Given `K : FiniteExhaustion s` and `K' : FiniteExhaustion t`, `FiniteExhaustion.prod K K'`
is the finite exhaustion on `s ×ˢ t` given by the pointwise set product of the exhaustions. -/
protected def prod :
    FiniteExhaustion (s ×ˢ t) :=
  { toFun n := K n ×ˢ K' n
    finite' n := (K.finite n).prod (K'.finite n)
    subset_succ' := fun n ↦ Set.prod_mono (K.subset_succ n) (K'.subset_succ n)
    iUnion_eq' := by
      rw [Set.iUnion_prod_of_monotone (OrderHomClass.mono K) (OrderHomClass.mono K'),
          K.iUnion_eq, K'.iUnion_eq] }

protected theorem prod_apply (n : ℕ) : (K.prod K') n = K n ×ˢ K' n := by rfl

end prod

end Set.FiniteExhaustion
