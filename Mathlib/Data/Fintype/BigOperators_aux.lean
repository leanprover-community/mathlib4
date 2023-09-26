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

theorem Equiv.finset_image_univ_eq_univ [Fintype α] [Fintype β] [DecidableEq β] (f : α ≃ β) : univ.image f = univ :=
  Finset.image_univ_of_surjective f.surjective

variable [CommMonoid β]

namespace Function

-- not yet ported
theorem comp_def (f : β → γ) (g : α → β) : f ∘ g = fun x => f (g x) := rfl

end Function

namespace Finset

theorem insert_compl_insert [DecidableEq ι] [Fintype ι] {s : Finset ι} {i : ι} (hi : i ∉ s) :
    insert i (insert i s)ᶜ = sᶜ := by
  simp_rw [@eq_compl_comm _ _ s, compl_insert, compl_erase, compl_compl, erase_insert hi]

@[to_additive]
theorem mul_prod_eq_prod_insertNone {α} {M} [CommMonoid M] (f : α → M) (x : M) (s : Finset α) :
    x * ∏ i in s, f i = ∏ i in insertNone s, i.elim x f :=
  (prod_insertNone (fun i => i.elim x f) _).symm

-- to Fintype/Sum
@[to_additive]
theorem prod_sum_univ [Fintype α] [Fintype γ] (f : α ⊕ γ → β) :
    ∏ x, f x = (∏ x, f (Sum.inl x)) * ∏ x, f (Sum.inr x) := by
  rw [← univ_disjSum_univ, prod_disj_sum]

@[simp]
theorem card_add_card_compl [DecidableEq α] [Fintype α] (s : Finset α) : s.card + sᶜ.card = Fintype.card α := by
  rw [Finset.card_compl, ← Nat.add_sub_assoc (card_le_univ s), Nat.add_sub_cancel_left]

@[simp]
theorem cast_card_erase_of_mem [DecidableEq α] [AddGroupWithOne R] {s : Finset α} (hs : a ∈ s) :
    ((s.erase a).card : R) = s.card - 1 := by
  rw [card_erase_of_mem hs, Nat.cast_sub, Nat.cast_one]
  rw [Nat.add_one_le_iff, Finset.card_pos]
  exact ⟨a, hs⟩

instance : Unique ({i} : Finset δ) :=
  ⟨⟨⟨i, mem_singleton_self i⟩⟩, fun j ↦ Subtype.ext <| mem_singleton.mp j.2⟩

@[simp]
lemma default_singleton : ((default : ({i} : Finset δ)) : δ) = i := rfl

end Finset

end Finset

section Logic

open Sum

@[simp]
theorem imp_and_neg_imp_iff (p q : Prop) : (p → q) ∧ (¬p → q) ↔ q := by
  simp_rw [imp_iff_or_not, not_not, ← or_and_left, not_and_self_iff, or_false_iff]

theorem Eq.rec_eq_cast {α : Sort _} {P : α → Sort _} {x y : α} (h : x = y) (z : P x) :
    h ▸ z = cast (congr_arg P h) z := ((cast_eq_iff_heq.mpr) <| heq_of_eq_rec_left h rfl).symm

end Logic

open Set
namespace Equiv
open Set

-- simps doesn't work from another module :-(
lemma piCongrLeft_apply_eq_cast {P : β → Sort v} {e : α ≃ β}
    (f : (a : α) → P (e a)) (b : β) :
    piCongrLeft P e f b = cast (congr_arg P (e.apply_symm_apply b)) (f (e.symm b)) :=
  Eq.rec_eq_cast _ _

lemma subtypeEquivRight_apply {p q : α → Prop} (e : ∀ x, p x ↔ q x)
    (z : { x // p x }) : subtypeEquivRight e z = ⟨z, (e z.1).mp z.2⟩ := rfl

lemma subtypeEquivRight_symm_apply {p q : α → Prop} (e : ∀ x, p x ↔ q x)
    (z : { x // q x }) : (subtypeEquivRight e).symm z = ⟨z, (e z.1).mpr z.2⟩ := rfl

variable {α : ι → Type _}

theorem piCongrLeft_symm_preimage_pi (f : ι' ≃ ι) (s : Set ι) (t : ∀ i, Set (α i)) :
    ((f.piCongrLeft α).symm ⁻¹' (f ⁻¹' s).pi fun i' => t <| f i') = s.pi t := by
  ext; simp_rw [mem_preimage, Set.mem_pi, piCongrLeft_symm_apply]
  convert f.forall_congr_left; rfl

theorem piCongrLeft_preimage_univ_pi (f : ι' ≃ ι) (t : ∀ i, Set (α i)) :
    f.piCongrLeft α ⁻¹' pi univ t = pi univ fun i => t (f i) := by
  apply Set.ext; rw [← (f.piCongrLeft α).symm.forall_congr_left]
  intro x; simp_rw [mem_preimage, apply_symm_apply, mem_univ_pi]
  exact f.forall_congr_left.symm

open Sum

/-- The type of dependent functions on a sum type `ι ⊕ ι'` is equivalent to the type of pairs of
functions on `ι` and on `ι'`. This is a dependent version of `Equiv.sumArrowEquivProdArrow`. -/
@[simps]
def sumPiEquivProdPi (π : ι ⊕ ι' → Type _) : (∀ i, π i) ≃ (∀ i, π (inl i)) × ∀ i', π (inr i')
    where
  toFun f := ⟨fun i => f (inl i), fun i' => f (inr i')⟩
  invFun g := Sum.rec g.1 g.2
  left_inv f := by ext (i | i) <;> rfl
  right_inv g := Prod.ext rfl rfl

/-- The equivalence between a product of two dependent functions types and a single dependent
function type. Basically a symmetric version of `Equiv.sumPiEquivProdPi`. -/
@[simps!]
def prodPiEquivSumPi (π : ι → Type _) (π' : ι' → Type _) :
    ((∀ i, π i) × ∀ i', π' i') ≃ ∀ i, Sum.elim π π' i :=
  sumPiEquivProdPi (Sum.elim π π') |>.symm

theorem sumPiEquivProdPi_symm_preimage_univ_pi (π : ι ⊕ ι' → Type _) (t : ∀ i, Set (π i)) :
    (sumPiEquivProdPi π).symm ⁻¹' univ.pi t =
    univ.pi (fun i => t (.inl i)) ×ˢ univ.pi fun i => t (.inr i) := by
  ext
  simp_rw [mem_preimage, mem_prod, mem_univ_pi, sumPiEquivProdPi_symm_apply]
  constructor
  · intro h; constructor <;> intro i <;> apply h
  · rintro ⟨h₁, h₂⟩ (i|i) <;> simp <;> apply_assumption

theorem sum_rec_congr (P : ι ⊕ ι' → Sort _) (f : ∀ i, P (inl i)) (g : ∀ i, P (inr i))
    {x y : ι ⊕ ι'} (h : x = y) :
    @Sum.rec _ _ _ f g x = cast (congr_arg P h.symm) (@Sum.rec _ _ _ f g y) := by cases h; rfl

theorem piCongrLeft_sum_inl (π : ι'' → Type _) (e : ι ⊕ ι' ≃ ι'') (f : ∀ i, π (e (inl i)))
    (g : ∀ i, π (e (inr i))) (i : ι) :
    piCongrLeft π e (sumPiEquivProdPi (fun x => π (e x)) |>.symm (f, g)) (e (inl i)) = f i := by
  simp_rw [piCongrLeft_apply_eq_cast, sumPiEquivProdPi_symm_apply,
    sum_rec_congr _ _ _ (e.symm_apply_apply (inl i)), cast_cast, cast_eq]

theorem piCongrLeft_sum_inr (π : ι'' → Type _) (e : ι ⊕ ι' ≃ ι'') (f : ∀ i, π (e (inl i)))
    (g : ∀ i, π (e (inr i))) (j : ι') :
    piCongrLeft π e (sumPiEquivProdPi (fun x => π (e x)) |>.symm (f, g)) (e (inr j)) = g j := by
  simp_rw [piCongrLeft_apply_eq_cast, sumPiEquivProdPi_symm_apply,
    sum_rec_congr _ _ _ (e.symm_apply_apply (inr j)), cast_cast, cast_eq]
end Equiv

namespace Option

theorem elim_comp {ι α β} (h : α → β) {f : ι → α} {x : α} {i : Option ι} :
    (i.elim (h x) fun j => h (f j)) = h (i.elim x f) := by cases i <;> rfl

theorem elim_comp₂ {ι α β γ} (h : α → β → γ) {f : ι → α} {x : α} {g : ι → β} {y : β}
    {i : Option ι} : (i.elim (h x y) fun j => h (f j) (g j)) = h (i.elim x f) (i.elim y g) := by
  cases i <;> rfl

theorem elim_apply {α β ι : Type _} {f : ι → α → β} {x : α → β} {i : Option ι} {y : α} :
    i.elim x f y = i.elim (x y) fun j => f j y := by rw [elim_comp fun f : α → β => f y]

end Option

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

def piSetUnion {ι} (α : ι → Type*) {s t : Set ι} [DecidablePred (· ∈ s)] (h : Disjoint s t) :
    ((∀ i : s, α i) × ∀ i : t, α i) ≃ ∀ i : (s ∪ t : Set ι), α i :=
  let e := (Equiv.Set.union <| Set.disjoint_iff.mp h).symm
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

/-- `updateSet x s y` is the vector `x` with the coordinates in `s` changed to the values of `y`.
This is `Set.piecewise` where the left argument `x` is dependently-typed
-/
def updateSet (x : ∀ i, π i) (s : Set ι) [DecidablePred (· ∈ s)]  (y : ∀ i : ↥s, π i) (i : ι) : π i :=
  if hi : i ∈ s then y ⟨i, hi⟩ else x i

/-
todo: do `updateSet` this for SetLike, like this:
```
def updateSet {𝓢} [SetLike 𝓢 ι] (s : 𝓢) (x : ∀ i, π i) (y : ∀ i : ↥s, π i) (i : ι) : π i :=
  if hi : i ∈ s then y ⟨i, hi⟩ else x i
```
however, `Finset` is not currently `SetLike`.
```
instance : SetLike (Finset ι) ι where
  coe := (·.toSet)
  coe_injective' := coe_injective
```
-/

open Set
-- variable [DecidablePred (· ∈ s)]

@[simp] theorem updateSet_empty {y} : updateSet x ∅ y = x :=
  rfl

theorem updateSet_singleton [DecidableEq ι] {i y} :
    updateSet x {i} y = Function.update x i (y ⟨i, mem_singleton i⟩) := by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, mem_singleton, update_same, updateSet]
  · simp [hj, updateSet]

theorem update_eq_updateSet [DecidableEq ι] {i y} :
    Function.update x i y = updateSet x {i} (uniqueElim y) := by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, mem_singleton, update_same, updateSet]
    exact uniqueElim_default (α := fun j : ({i} : Finset ι) => π j) y
  · simp [hj, updateSet]

theorem updateSet_updateSet
    {s t : Set ι} (hst : Disjoint s t)
    [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] [DecidablePred (· ∈ s ∪ t)]
    {y : ∀ i : ↥s, π i} {z : ∀ i : ↥t, π i} :
    updateSet (updateSet x s y) t z =
    updateSet x (s ∪ t) (Equiv.piSetUnion π hst ⟨y, z⟩) := by
  set e := Equiv.Set.union (Set.disjoint_iff.mp hst) |>.symm
  congr with i
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;>
    simp only [updateSet, his, hit, dif_pos, dif_neg, mem_union, true_or_iff,
      false_or_iff, not_false_iff]
  · exfalso; exact Set.disjoint_left.mp hst his hit
  · exact piCongrLeft_sum_inl (fun b : ↥(s ∪ t) => π b) e y z ⟨i, his⟩ |>.symm
  · exact piCongrLeft_sum_inr (fun b : ↥(s ∪ t) => π b) e y z ⟨i, hit⟩ |>.symm

theorem updateSet_congr {s t : Set ι} (hst : s = t)
    [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] {y : ∀ i : ↥s, π i} :
    updateSet x s y = updateSet x t (y ∘' Equiv.Set.ofEq hst.symm) := by
  subst hst
  congr!


end Function
end Function
