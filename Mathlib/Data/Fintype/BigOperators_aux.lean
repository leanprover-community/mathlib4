/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.Data.Fintype.BigOperators

/-!
A supplement to the file `Data.Fintype.BigOperators`
-/


open scoped BigOperators
set_option autoImplicit true

noncomputable section

variable {ι ι' ι'' : Type _}

section Finset

open Finset

variable {α β γ : Type _}

-- theorem Equiv.finset_image_univ_eq_univ [Fintype α] [Fintype β] [DecidableEq β] (f : α ≃ β) : univ.image f = univ :=
--   Finset.image_univ_of_surjective f.surjective

variable [CommMonoid β]

namespace Finset

-- to Fintype/Sum
@[to_additive]
theorem prod_sum_univ [Fintype α] [Fintype γ] (f : α ⊕ γ → β) :
    ∏ x, f x = (∏ x, f (Sum.inl x)) * ∏ x, f (Sum.inr x) := by
  rw [← univ_disjSum_univ, prod_disj_sum]

@[simp]
theorem card_add_card_compl [DecidableEq α] [Fintype α] (s : Finset α) : s.card + sᶜ.card = Fintype.card α := by
  rw [Finset.card_compl, ← Nat.add_sub_assoc (card_le_univ s), Nat.add_sub_cancel_left]

instance : Unique ({i} : Finset δ) :=
  ⟨⟨⟨i, mem_singleton_self i⟩⟩, fun j ↦ Subtype.ext <| mem_singleton.mp j.2⟩

@[simp]
lemma default_singleton : ((default : ({i} : Finset δ)) : δ) = i := rfl

end Finset

end Finset

open Set
-- namespace Equiv
-- open Set
-- open Sum

-- theorem sum_rec_congr (P : ι ⊕ ι' → Sort _) (f : ∀ i, P (inl i)) (g : ∀ i, P (inr i))
--     {x y : ι ⊕ ι'} (h : x = y) :
--     @Sum.rec _ _ _ f g x = cast (congr_arg P h.symm) (@Sum.rec _ _ _ f g y) := by cases h; rfl
-- end Equiv

open Function Equiv

section Set

open Set

variable {α : Type*} [DecidableEq α] {s t : Finset α}

open Finset
namespace Equiv
/-- `s ∪ t` (using finset union) is equivalent to `s ∪ t` (using set union) -/
@[simps!]
def finsetUnion (s t : Finset α) :
    ((s ∪ t : Finset α) : Set α) ≃ (s ∪ t : Set α) :=
  Equiv.Set.ofEq <| coe_union _ _

/-- The disjoint union of finsets is a sum -/
def Finset.union (s t : Finset α) (h : Disjoint s t) :
    (s ∪ t : Finset α) ≃ s ⊕ t :=
  (Equiv.finsetUnion s t).trans <| Equiv.Set.union (disjoint_coe.mpr h).le_bot

@[simp]
theorem Finset.union_symm_inl (h : Disjoint s t) (x : s) :
    (Equiv.Finset.union s t h).symm (Sum.inl x) = ⟨x, Finset.mem_union.mpr <| Or.inl x.2⟩ :=
  rfl

@[simp]
theorem Finset.union_symm_inr (h : Disjoint s t) (y : t) :
    (Equiv.Finset.union s t h).symm (Sum.inr y) = ⟨y, Finset.mem_union.mpr <| Or.inr y.2⟩ :=
  rfl

def piFinsetUnion {ι} [DecidableEq ι] (α : ι → Type*) {s t : Finset ι} (h : Disjoint s t) :
    ((∀ i : s, α i) × ∀ i : t, α i) ≃ ∀ i : (s ∪ t : Finset ι), α i :=
  let e := (Equiv.Finset.union s t h).symm
  sumPiEquivProdPi (fun b ↦ α (e b)) |>.symm.trans (.piCongrLeft (fun i : ↥(s ∪ t) ↦ α i) e)

end Equiv

theorem eval_preimage {ι} [DecidableEq ι] {α : ι → Type _} {i : ι} {s : Set (α i)} :
    eval i ⁻¹' s = pi univ (update (fun i => univ) i s) := by
  ext x
  simp [@forall_update_iff _ (fun i => Set (α i)) _ _ _ _ fun i' y => x i' ∈ y]

theorem eval_preimage' {ι} [DecidableEq ι] {α : ι → Type _} {i : ι} {s : Set (α i)} :
    eval i ⁻¹' s = pi {i} (update (fun i => univ) i s) := by ext; simp

theorem pi_univ_ite {ι} {α : ι → Type _} (s : Set ι) [DecidablePred (· ∈ s)] (t : ∀ i, Set (α i)) :
    (pi univ fun i => if i ∈ s then t i else univ) = s.pi t := by
  ext; simp_rw [Set.mem_pi]; apply forall_congr'; intro i; split_ifs with h <;> simp [h]

end Set


section Function

open Set

variable {α : ι → Type _}

/-- Given one value over a unique, we get a dependent function. -/
def uniqueElim [Unique ι] (x : α (default : ι)) (i : ι) : α i := by
  rw [Unique.eq_default i]
  exact x

@[simp]
theorem uniqueElim_default {_ : Unique ι} (x : α (default : ι)) : uniqueElim x (default : ι) = x :=
  rfl

theorem uniqueElim_preimage [Unique ι] (t : ∀ i, Set (α i)) :
    uniqueElim ⁻¹' pi univ t = t (default : ι) := by ext; simp [Unique.forall_iff]

theorem pred_update {α} [DecidableEq α] {β : α → Type _} (P : ∀ ⦃a⦄, β a → Prop) (f : ∀ a, β a)
    (a' : α) (v : β a') (a : α) : P (update f a' v a) ↔ a = a' ∧ P v ∨ a ≠ a' ∧ P (f a) := by
  rw [update]
  split_ifs with h
  · subst h
    simp
  · rw [← Ne.def] at h
    simp [h]


namespace Function
variable {ι : Sort _} {π : ι → Sort _} {x : ∀ i, π i}

/-- `updateFinset x s y` is the vector `x` with the coordinates in `s` changed to the values of `y`. -/
def updateFinset (x : ∀ i, π i) (s : Finset ι) [DecidableEq ι] (y : ∀ i : ↥s, π i) (i : ι) :
    π i :=
  if hi : i ∈ s then y ⟨i, hi⟩ else x i

/-
todo: do `updateFinset` this for SetLike, like this:
```
def updateFinset {𝓢} [SetLike 𝓢 ι] (s : 𝓢) (x : ∀ i, π i) (y : ∀ i : ↥s, π i) (i : ι) : π i :=
  if hi : i ∈ s then y ⟨i, hi⟩ else x i
```
however, `Finset` is not currently `SetLike`.
```
instance : SetLike (Finset ι) ι where
  coe := (·.toSet)
  coe_injective' := coe_injective
```
-/

open Finset
variable [DecidableEq ι]

@[simp] theorem updateFinset_empty {y} : updateFinset x ∅ y = x :=
  rfl

theorem updateFinset_singleton {i y} :
    updateFinset x {i} y = Function.update x i (y ⟨i, mem_singleton_self i⟩) := by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_same, updateFinset]
  · simp [hj, updateFinset]

theorem update_eq_updateFinset {i y} :
    Function.update x i y = updateFinset x {i} (uniqueElim y) := by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_same, updateFinset]
    exact uniqueElim_default (α := fun j : ({i} : Finset ι) => π j) y
  · simp [hj, updateFinset]

theorem updateFinset_updateFinset {s t : Finset ι} (hst : Disjoint s t)
    {y : ∀ i : ↥s, π i} {z : ∀ i : ↥t, π i} :
    updateFinset (updateFinset x s y) t z =
    updateFinset x (s ∪ t) (Equiv.piFinsetUnion π hst ⟨y, z⟩) := by
  set e := Equiv.Finset.union s t hst |>.symm
  congr with i
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;>
    simp only [updateFinset, his, hit, dif_pos, dif_neg, Finset.mem_union, true_or_iff,
      false_or_iff, not_false_iff]
  · exfalso; exact Finset.disjoint_left.mp hst his hit
  · exact piCongrLeft_sum_inl (fun b : ↥(s ∪ t) => π b) e y z ⟨i, his⟩ |>.symm
  · exact piCongrLeft_sum_inr (fun b : ↥(s ∪ t) => π b) e y z ⟨i, hit⟩ |>.symm

end Function
end Function
