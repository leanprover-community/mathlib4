/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Finite.Prod

/-!
# Finite Exhaustions

This file defines a structure called `FiniteExhaustion` which represents an exhaustion of a
countable set by an increasing sequence of finite sets. Given a countable set `s`,
`FiniteExhaustion.choice s` is a choice of a finite exhaustion.
-/

@[expose] public section

/-- A `FiniteExhaustion` of a set `s` is a monotonically increasing sequence
of finite sets such that their union is `s`. -/
structure FiniteExhaustion {α : Type*} (s : Set α) where
  /-- The underlying sequence of a `FiniteExhaustion`. -/
  toFun : ℕ → Set α
  /-- Every set in a `FiniteExhaustion` is finite. -/
  Finite' : ∀ n, Finite (toFun n)
  /-- The sequence of sets in a `FiniteExhaustion` are monotonically increasing. -/
  subset_succ' : ∀ n, toFun n ⊆ toFun (n + 1)
  /-- The union of all sets in a `FiniteExhaustion` equals `s` -/
  iUnion_eq' : ⋃ n, toFun n = s

namespace FiniteExhaustion

instance {α : Type*} {s : Set α} : FunLike (FiniteExhaustion s) ℕ (Set α) where
  coe := toFun
  coe_injective' | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

instance {α : Type*} {s : Set α} : RelHomClass (FiniteExhaustion s) LE.le HasSubset.Subset where
  map_rel K _ _ h := monotone_nat_of_le_succ (fun n ↦ K.subset_succ' n) h

instance {α : Type*} {s : Set α} {K : FiniteExhaustion s} {n : ℕ} : Finite (K n) :=
  K.Finite' n

variable {α : Type*} {s : Set α} (K : FiniteExhaustion s)

@[simp]
theorem toFun_eq_coe : K.toFun = K := rfl

protected theorem Finite (n : ℕ) : (K n).Finite := K.Finite' n

theorem subset_succ (n : ℕ) : K n ⊆ K (n + 1) := K.subset_succ' n

protected theorem subset {m n : ℕ} (h : m ≤ n) : K m ⊆ K n :=
  OrderHomClass.mono K h

theorem iUnion_eq : ⋃ n, K n = s :=
  K.iUnion_eq'

/-- A choice of a `FiniteExhaustion` for a countable set `s`. -/
noncomputable def choice (s : Set α) [Countable s] : FiniteExhaustion s := by
    apply Classical.choice
    by_cases h : Nonempty s
    · obtain ⟨f, hf⟩ := exists_surjective_nat s
      refine ⟨fun n ↦ (Subtype.val ∘ f) '' {i | i ≤ n}, ?_, ?_, ?_⟩
      · exact fun n ↦ Set.Finite.image _ (Set.finite_le_nat n)
      · intro n
        simp only [Function.comp_apply]
        gcongr
        simp
      · simp [← Set.image_image, ← Set.image_iUnion, Set.iUnion_le_nat, Set.range_eq_univ.mpr hf]
    · refine ⟨fun _ ↦ ∅, by simp [Set.Finite.to_subtype], fun n ↦ by simp, ?_⟩
      simp [Set.not_nonempty_iff_eq_empty'.mp h]

noncomputable instance [Countable s] :
    Inhabited (FiniteExhaustion s) :=
  ⟨FiniteExhaustion.choice s⟩

section prod

variable {β : Type*} {t : Set β} (K' : FiniteExhaustion t)

/-- Given `K : FiniteExhaustion s` and `K' : FiniteExhaustion t`, `FiniteExhaustion.prod K K'`
is the finite exhaustion on `s ×ˢ t` given by the pointwise set product of the exhaustions. -/
protected def prod :
    FiniteExhaustion (s ×ˢ t) :=
  { toFun := fun n ↦ K n ×ˢ K' n
    Finite' := fun n ↦ Set.Finite.prod (K.Finite n) (K'.Finite n)
    subset_succ' := fun n ↦ Set.prod_mono (K.subset_succ n) (K'.subset_succ n)
    iUnion_eq' := by
      apply subset_antisymm
      · rw [Set.iUnion_subset_iff]
        refine fun i ↦ Set.prod_mono ?_ ?_
        · simp [← K.iUnion_eq, Set.subset_iUnion]
        · simp [← K'.iUnion_eq, Set.subset_iUnion]
      rintro ⟨a, b⟩ h
      simp only [← K.iUnion_eq, ← K'.iUnion_eq, Set.mem_prod, Set.mem_iUnion] at h
      obtain ⟨⟨i,hi⟩, ⟨j, hj⟩⟩ := h
      simp only [Set.mem_iUnion, Set.mem_prod]
      exact ⟨max i j, K.subset (le_max_left _ _) hi, K'.subset (le_max_right _ _ ) hj⟩ }

protected theorem prod_apply (n : ℕ) : (K.prod K') n = K n ×ˢ K' n := by rfl

end prod

end FiniteExhaustion
