/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.Data.Fintype.BigOperators

/-!
A supplement to the file `Data.Fintype.BigOperators`
-/


open scoped Classical BigOperators
set_option autoImplicit true

noncomputable section

variable {ι ι' ι'' : Type _}

section Finset

open Finset

variable {α β γ : Type _}

theorem Equiv.finset_image_univ_eq_univ [Fintype α] [Fintype β] (f : α ≃ β) : univ.image f = univ :=
  Finset.image_univ_of_surjective f.surjective

variable [CommMonoid β]

-- very similar to `equiv.prod_comp_finset` in #16948
theorem Finset.prod_comp_equiv {s : Finset α} (f : γ → β) (g : α ≃ γ) :
    ∏ a in s, f (g a) = ∏ b in s.image g, f b := by
  refine'
    prod_bij' (fun x _ => g x) (fun a ha => Finset.mem_image_of_mem _ ha) (fun _ _ => rfl)
      (fun a _ => g.symm a) _ (fun a _ => g.symm_apply_apply a) fun a _ => g.apply_symm_apply a
  simp only [Finset.mem_image, exists_imp]
  rintro _ _ ⟨_, rfl⟩
  simpa

theorem prod_univ_comp_equiv [Fintype α] [Fintype γ] (f : γ → β) (g : α ≃ γ) :
    ∏ a, f (g a) = ∏ b, f b :=
  g.prod_comp f

namespace Function

theorem comp_def (f : β → γ) (g : α → β) : f ∘ g = fun x => f (g x) := rfl

end Function

namespace Finset

theorem insert_compl_insert [Fintype ι] {s : Finset ι} {i : ι} (hi : i ∉ s) :
    insert i (insert i s)ᶜ = sᶜ := by
  simp_rw [@eq_compl_comm _ _ s, compl_insert, compl_erase, compl_compl, erase_insert hi]

-- no longer needed
-- @[to_additive]
-- theorem mul_prod_eq_prod_insertNone {α} {M} [CommMonoid M] (f : α → M) (x : M) (s : Finset α) :
--     x * ∏ i in s, f i = ∏ i in insertNone s, i.elim x f :=
--   (prod_insertNone (fun i => i.elim x f) _).symm

-- to Fintype/Sum
@[to_additive]
theorem prod_sum_univ [Fintype α] [Fintype γ] (f : α ⊕ γ → β) :
    ∏ x, f x = (∏ x, f (Sum.inl x)) * ∏ x, f (Sum.inr x) := by
  rw [← univ_disjSum_univ, prod_disj_sum]

@[simp]
theorem card_add_card_compl [Fintype α] (s : Finset α) : s.card + sᶜ.card = Fintype.card α := by
  rw [Finset.card_compl, ← Nat.add_sub_assoc (card_le_univ s), Nat.add_sub_cancel_left]

@[simp]
theorem cast_card_erase_of_mem [AddGroupWithOne R] {s : Finset α} (hs : a ∈ s) :
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

theorem cast_sum_rec {α β : Type _} {P : α ⊕ β → Sort _} (f : ∀ i, P (inl i)) (g : ∀ j, P (inr j))
    (x y : α ⊕ β) (h : x = y) :
    cast (congr_arg P h) (@Sum.rec _ _ _ f g x) = @Sum.rec _ _ _ f g y := by cases h; rfl

theorem Eq.rec_eq_cast {α : Sort _} {P : α → Sort _} {x y : α} (h : x = y) (z : P x) :
    h ▸ z = cast (congr_arg P h) z := by induction h; rfl

end Logic

open Set
namespace Equiv
open Set

-- simps doesn't work from another module :-(
lemma piCongrLeft_apply' {P : β → Sort v} {e : α ≃ β}
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
functions on `ι` and on `ι'`. This is a dependent version of `equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps]
def piSum (π : ι ⊕ ι' → Type _) : ((∀ i, π (inl i)) × ∀ i', π (inr i')) ≃ ∀ i, π i
    where
  toFun f := Sum.rec f.1 f.2
  invFun g := ⟨fun i => g (inl i), fun i' => g (inr i')⟩
  left_inv f := Prod.ext rfl rfl
  right_inv g := by ext (i | i) <;> rfl

/-- unused -/
def piSum' (π : ι → Type _) (π' : ι' → Type _) :
    ((∀ i, π i) × ∀ i', π' i') ≃ ∀ i, Sum.elim π π' i :=
  Equiv.piSum (Sum.elim π π')

theorem piSum_preimage_univ_pi (π : ι ⊕ ι' → Type _) (t : ∀ i, Set (π i)) :
    piSum π  ⁻¹' pi univ t = pi univ (fun i => t (.inl i)) ×ˢ pi univ fun i => t (.inr i) := by
  ext
  simp_rw [mem_preimage, mem_prod, mem_univ_pi, piSum_apply]
  constructor
  · intro h; constructor <;> intro i <;> apply h
  · rintro ⟨h₁, h₂⟩ (i|i) <;> simp <;> apply_assumption

theorem Set.union_apply_left' {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅)
    {a : α} (ha : a ∈ s) : Equiv.Set.union H ⟨a, Set.mem_union_left _ ha⟩ = Sum.inl ⟨a, ha⟩ :=
  dif_pos ha

theorem Set.union_apply_right' {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅)
    {a : α} (ha : a ∈ t) : Equiv.Set.union H ⟨a, Set.mem_union_right _ ha⟩ = Sum.inr ⟨a, ha⟩ :=
  dif_neg fun h => H ⟨h, ha⟩

theorem sum_rec_congr (P : ι ⊕ ι' → Sort _) (f : ∀ i, P (inl i)) (g : ∀ i, P (inr i))
    {x y : ι ⊕ ι'} (h : x = y) :
    @Sum.rec _ _ _ f g x = cast (congr_arg P h.symm) (@Sum.rec _ _ _ f g y) := by cases h; rfl

theorem piCongrLeft_sum_inl (π : ι'' → Type _) (e : ι ⊕ ι' ≃ ι'') (f : ∀ i, π (e (inl i)))
    (g : ∀ i, π (e (inr i))) (i : ι) :
    piCongrLeft π e (piSum (fun x => π (e x)) (f, g)) (e (inl i)) = f i := by
  simp_rw [piCongrLeft_apply', piSum_apply, sum_rec_congr _ _ _ (e.symm_apply_apply (inl i)),
    cast_cast, cast_eq]

theorem piCongrLeft_sum_inr (π : ι'' → Type _) (e : ι ⊕ ι' ≃ ι'') (f : ∀ i, π (e (inl i)))
    (g : ∀ i, π (e (inr i))) (j : ι') :
    piCongrLeft π e (piSum (fun x => π (e x)) (f, g)) (e (inr j)) = g j := by
  simp_rw [piCongrLeft_apply', piSum_apply, sum_rec_congr _ _ _ (e.symm_apply_apply (inr j)),
    cast_cast, cast_eq]

end Equiv

namespace Option

theorem elim'_comp {ι α β} (h : α → β) {f : ι → α} {x : α} {i : Option ι} :
    (i.elim (h x) fun j => h (f j)) = h (i.elim x f) := by cases i <;> rfl

theorem elim'_comp₂ {ι α β γ} (h : α → β → γ) {f : ι → α} {x : α} {g : ι → β} {y : β}
    {i : Option ι} : (i.elim (h x y) fun j => h (f j) (g j)) = h (i.elim x f) (i.elim y g) := by
  cases i <;> rfl

theorem elim'_apply {α β ι : Type _} {f : ι → α → β} {x : α → β} {i : Option ι} {y : α} :
    i.elim x f y = i.elim (x y) fun j => f j y := by rw [elim'_comp fun f : α → β => f y]

end Option

open Function Equiv

section Set

open Set

variable {α : Type*} [DecidableEq α] {s t : Finset α}

/-- `s ∪ t` (using finset union) is equivalent to `s ∪ t` (using set union) -/
@[simps!]
def Equiv.finsetUnion (s t : Finset α) :
    ((s ∪ t : Finset α) : Set α) ≃ (s ∪ t : Set α) :=
  subtypeEquivRight <| by simp

/-- The disjoint union of finsets is a sum -/
def finsetUnionEquivSum (s t : Finset α) (h : Disjoint s t) :
    (s ∪ t : Finset α) ≃ s ⊕ t :=
  (Equiv.finsetUnion s t).trans <| Equiv.Set.union <| by
    rw [← Finset.coe_inter, ← Finset.coe_empty]
    exact h.le_bot

@[simp]
theorem finsetUnionEquivSum_symm_inl (h : Disjoint s t) (x : s) :
    (finsetUnionEquivSum s t h).symm (Sum.inl x) = ⟨x, Finset.mem_union.mpr <| Or.inl x.2⟩ :=
  rfl

@[simp]
theorem finsetUnionEquivSum_symm_inr (h : Disjoint s t) (y : t) :
    (finsetUnionEquivSum s t h).symm (Sum.inr y) = ⟨y, Finset.mem_union.mpr <| Or.inr y.2⟩ :=
  rfl

@[simp]
theorem finsetUnionEquivSum_symm_inl' (h : Disjoint s t) (x : α) (hx : x ∈ s)
    (h2x : x ∈ s ∪ t) : (finsetUnionEquivSum s t h).symm (Sum.inl ⟨x, hx⟩) = ⟨x, h2x⟩ :=
  rfl

@[simp]
theorem finsetUnionEquivSum_symm_inr' (h : Disjoint s t) (y : t) :
    (finsetUnionEquivSum s t h).symm (Sum.inr y) = ⟨y, Finset.mem_union.mpr <| Or.inr y.2⟩ :=
  rfl

theorem iUnion_univ_pi {ι ι₂} {α : ι → Type _} (t : ∀ i, ι₂ → Set (α i)) :
    (⋃ x : ι → ι₂, pi univ fun i => t i (x i)) = pi univ fun i => ⋃ j : ι₂, t i j := by
  ext
  simp [Classical.skolem]

theorem eval_preimage {ι} [DecidableEq ι] {α : ι → Type _} {i : ι} {s : Set (α i)} :
    eval i ⁻¹' s = pi univ (update (fun i => univ) i s) := by
  ext x
  simp [@forall_update_iff _ (fun i => Set (α i)) _ _ _ _ fun i' y => x i' ∈ y]

theorem eval_preimage' {ι} [DecidableEq ι] {α : ι → Type _} {i : ι} {s : Set (α i)} :
    eval i ⁻¹' s = pi {i} (update (fun i => univ) i s) := by ext; simp

theorem mem_pi_univ {ι : Type _} {α : ι → Type _} (t : ∀ i, Set (α i)) (x : ∀ i, α i) :
    x ∈ pi univ t ↔ ∀ i, x i ∈ t i := by simp

theorem pi_univ_ite {ι} {α : ι → Type _} (s : Set ι) (t : ∀ i, Set (α i)) :
    (pi univ fun i => if i ∈ s then t i else univ) = s.pi t := by
  ext; simp_rw [Set.mem_pi]; apply forall_congr'; intro i; split_ifs with h <;> simp [h]

theorem pi_univ_eq_iInter {ι} {α : ι → Type _} (t : ∀ i, Set (α i)) :
    pi univ t = ⋂ i, eval i ⁻¹' t i := by simp_rw [pi_def, mem_univ, iInter_true]

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


variable {ι : Sort _} {π : ι → Sort _} {x : ∀ i, π i}

/-- `updateSet x s y` is the vector `x` with the coordinates in `s` changed to the values of `y`. -/
def updateSet (x : ∀ i, π i) (s : Finset ι) (y : ∀ i : ↥s, π i) (i : ι) : π i :=
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

open Finset
theorem updateSet_empty {y} : updateSet x ∅ y = x :=
  rfl

theorem updateSet_singleton [DecidableEq ι] {i y} :
    updateSet x {i} y = Function.update x i (y ⟨i, mem_singleton_self i⟩) := by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_same, updateSet]
  · simp [hj, updateSet]

theorem update_eq_updateSet [DecidableEq ι] {i y} :
    Function.update x i y = updateSet x {i} (uniqueElim y) := by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_same, updateSet]
    exact uniqueElim_default (α := fun j : ({i} : Finset ι) => π j) y
  · simp [hj, updateSet]

theorem updateSet_updateSet [DecidableEq ι] {s t : Finset ι} (hst : Disjoint s t) {y z} :
    updateSet (updateSet x s y) t z =
    updateSet x (s ∪ t)
      (Equiv.piCongrLeft (fun i : ↥(s ∪ t) ↦ π i) (finsetUnionEquivSum s t hst).symm <|
      Equiv.piSum _ ⟨y, z⟩) := by
  set e₁ := finsetUnionEquivSum s t hst |>.symm
  congr with i
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;>
    simp only [updateSet, his, hit, dif_pos, dif_neg, Finset.mem_union, true_or_iff, false_or_iff,
      not_false_iff]
  · exfalso; exact Finset.disjoint_left.mp hst his hit
  · exact piCongrLeft_sum_inl (fun b : ↥(s ∪ t) => π b) e₁ y z ⟨i, his⟩ |>.symm
  · exact piCongrLeft_sum_inr (fun b : ↥(s ∪ t) => π b) e₁ y z ⟨i, _⟩ |>.symm

end Function
