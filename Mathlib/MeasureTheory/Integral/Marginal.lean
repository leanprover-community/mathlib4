/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Marginals of multivariate functions
-/


open scoped Classical BigOperators Topology ENNReal
open Filter
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
    ∏ a in s, f (g a) = ∏ b in s.image g, f b :=
  by
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

lemma none_mem_insertNone {s : Finset α} : none ∈ insertNone s := by simp

lemma insertNone_nonempty {s : Finset α} : insertNone s |>.Nonempty := ⟨none, none_mem_insertNone⟩

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

open Function MeasureTheory.OuterMeasure MeasurableSpace Equiv

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

theorem surjective_decode_iget (α : Type _) [Encodable α] [Inhabited α] :
    Surjective fun n => (Encodable.decode (α := α) n).iget := fun x =>
  ⟨Encodable.encode x, by simp_rw [Encodable.encodek]⟩


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

section Measurable

open Set

variable {α : ι → Type _}

theorem measurable_uniqueElim [Unique ι] [∀ i, MeasurableSpace (α i)] :
    Measurable (uniqueElim : α (default : ι) → ∀ i, α i) := by
  simp_rw [measurable_pi_iff, Unique.forall_iff, uniqueElim_default]; exact measurable_id

/-- The measurable equivalence `(∀ i, α i) ≃ᵐ α ⋆` when the domain of `α` only contains `⋆` -/
@[simps (config := .asFn)]
def MeasurableEquiv.piUnique (α : ι → Type _) [Unique ι] [∀ i, MeasurableSpace (α i)] :
    (∀ i, α i) ≃ᵐ α (default : ι) where
      toFun := fun f => f default
      invFun := uniqueElim
      left_inv := fun f => funext fun i => by
        cases Unique.eq_default i
        rfl
      right_inv := fun x => rfl
      measurable_toFun := measurable_pi_apply _
      measurable_invFun := measurable_uniqueElim

theorem MeasurableSet.univ_pi_fintype {δ} {π : δ → Type _} [∀ i, MeasurableSpace (π i)] [Fintype δ]
    {t : ∀ i, Set (π i)} (ht : ∀ i, MeasurableSet (t i)) : MeasurableSet (pi univ t) :=
  MeasurableSet.pi finite_univ.countable fun i _ => ht i

end Measurable

section MeasurableOnFamily

variable {α : ι → Type _}

variable [∀ i, MeasurableSpace (α i)]

variable (α)

theorem measurable_eq_mp {i i' : ι} (h : i = i') : Measurable (congr_arg α h).mp := by
  cases h
  exact measurable_id

theorem Measurable.eq_mp {β} [MeasurableSpace β] {i i' : ι} (h : i = i') {f : β → α i}
    (hf : Measurable f) : Measurable fun x => (congr_arg α h).mp (f x) :=
  (measurable_eq_mp α h).comp hf

variable {α}

theorem measurable_piCongrLeft (f : ι' ≃ ι) : Measurable (piCongrLeft α f) := by
  rw [measurable_pi_iff]
  intro i
  simp_rw [piCongrLeft_apply']
  apply Measurable.eq_mp α (f.apply_symm_apply i)
  exact measurable_pi_apply (f.symm i)

variable (α)
/-- Moving a dependent type along an equivalence of coordinates, as a measurable equivalence. -/
def MeasurableEquiv.piCongrLeft (f : ι' ≃ ι) : (∀ b, α (f b)) ≃ᵐ ∀ a, α a := by
  refine' { Equiv.piCongrLeft α f with .. }
  · exact measurable_piCongrLeft f
  simp only [invFun_as_coe, coe_fn_symm_mk]
  rw [measurable_pi_iff]
  exact fun i => measurable_pi_apply (f i)
variable {α}

theorem MeasurableEquiv.piCongrLeft_eq (f : ι' ≃ ι) :
  (MeasurableEquiv.piCongrLeft α f : _ → _) = f.piCongrLeft α := by rfl

/-- The measurable equivalence between the pi type over a sum type and a product of pi-types.
This is similar to `MeasurableEquiv.piEquivPiSubtypeProd`. -/
def MeasurableEquiv.piSum (α : ι ⊕ ι' → Type _) [∀ i, MeasurableSpace (α i)] :
  ((∀ i, α (.inl i)) × ∀ i', α (.inr i')) ≃ᵐ ∀ i, α i := by
  refine' { Equiv.piSum α with .. }
  · rw [measurable_pi_iff]; rintro (i|i)
    exact measurable_pi_iff.1 measurable_fst _
    exact measurable_pi_iff.1 measurable_snd _
  · refine Measurable.prod ?_ ?_ <;>
      rw [measurable_pi_iff] <;> rintro i <;> apply measurable_pi_apply

theorem MeasurableEquiv.piSum_eq (α : ι ⊕ ι' → Type _) [∀ i, MeasurableSpace (α i)] :
  (MeasurableEquiv.piSum α : _ → _) = Equiv.piSum α := by rfl

end MeasurableOnFamily

open Finset

namespace MeasureTheory

-- workaround for `@[gcongr]` not recognizing some existing lemmas, like `lintegral_mono`, as valid
@[gcongr] theorem lintegral_mono2 ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x, f x ≤ g x) :
    lintegral μ f ≤ lintegral μ g :=
lintegral_mono hfg

@[gcongr] theorem lintegral_mono3 ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x, f x ≤ g x) (h2 : μ ≤ ν) :
    lintegral μ f ≤ lintegral ν g :=
lintegral_mono' h2 hfg

-- @[gcongr] theorem lintegral_congr2 ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x, f x = g x) :
--     lintegral μ f = lintegral μ g :=
-- lintegral_congr hfg

alias ⟨_, _root_.ENNReal.monotone2⟩ := ENNReal.coe_le_coe
attribute [gcongr] ENNReal.monotone2


theorem Subsingleton.measurableSingletonClass {α} [MeasurableSpace α] [Subsingleton α] :
    MeasurableSingletonClass α := by
  refine' ⟨fun i => _⟩
  convert MeasurableSet.univ
  simp [Set.eq_univ_iff_forall]

section Measure

variable {α : ι → Type _}
variable [∀ i, MeasurableSpace (α i)]
variable [Fintype ι] [Fintype ι']
variable {m : ∀ i, OuterMeasure (α i)}
variable [∀ i, MeasurableSpace (α i)] {μ : ∀ i, Measure (α i)}
variable [∀ i, SigmaFinite (μ i)]
variable (μ)

namespace Measure

open Sum

/-- Some properties of `Measure.pi` -/

theorem pi_map_left (f : ι' ≃ ι) :
    map (MeasurableEquiv.piCongrLeft α f) (Measure.pi fun i' => μ (f i')) = Measure.pi μ := by
  refine' (pi_eq fun s _ => _).symm
  rw [MeasurableEquiv.map_apply, MeasurableEquiv.piCongrLeft_eq,
    piCongrLeft_preimage_univ_pi, pi_pi _ _, prod_univ_comp_equiv (fun i => μ i (s i)) f]

theorem pi_sum {π : ι ⊕ ι' → Type _} [∀ i, MeasurableSpace (π i)] (μ : ∀ i, Measure (π i))
    [∀ i, SigmaFinite (μ i)] :
    map (MeasurableEquiv.piSum π)
      ((Measure.pi fun i => μ (.inl i)).prod (Measure.pi fun i => μ (.inr i))) = Measure.pi μ := by
  refine' (pi_eq fun s _ => _).symm
  simp_rw [MeasurableEquiv.map_apply, MeasurableEquiv.piSum_eq, piSum_preimage_univ_pi,
    Measure.prod_prod, Measure.pi_pi, prod_sum_univ]

theorem pi_unique {π : ι → Type _} [Unique ι] [∀ i, MeasurableSpace (π i)]
    (μ : ∀ i, Measure (π i)) :
    map (MeasurableEquiv.piUnique π) (Measure.pi μ) = μ default := by
  set e := MeasurableEquiv.piUnique π
  have : (piPremeasure fun i => (μ i).toOuterMeasure) = Measure.map e.symm (μ default) := by
    ext1 s
    rw [piPremeasure, Fintype.prod_unique, e.symm.map_apply]
    congr 1; exact e.toEquiv.image_eq_preimage s
  simp_rw [Measure.pi, OuterMeasure.pi, this, boundedBy_eq_self, toOuterMeasure_toMeasure,
    MeasurableEquiv.map_map_symm]

end Measure

open Measure
-- todo: use the next lemmas. For them to be useful we want to have a lemma like
-- `MeasurePreserving.lintegral_comp_equiv`
theorem measurePreserving_piCongrLeft (f : ι' ≃ ι) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft α f)
      (Measure.pi fun i' => μ (f i')) (Measure.pi μ) where
  measurable := (MeasurableEquiv.piCongrLeft α f).measurable
  map_eq := pi_map_left μ f

theorem measurePreserving_piSum {π : ι ⊕ ι' → Type _} [∀ i, MeasurableSpace (π i)]
    (μ : ∀ i, Measure (π i)) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (MeasurableEquiv.piSum π)
      ((Measure.pi fun i => μ (.inl i)).prod (Measure.pi fun i => μ (.inr i))) (Measure.pi μ) where
  measurable := (MeasurableEquiv.piSum π).measurable
  map_eq := pi_sum μ

-- generalizes `measurePreserving_funUnique`
theorem measurePreserving_piUnique {π : ι → Type _} [Unique ι] [∀ i, MeasurableSpace (π i)]
    (μ : ∀ i, Measure (π i)) :
    MeasurePreserving (MeasurableEquiv.piUnique π) (Measure.pi μ) (μ default) where
  measurable := (MeasurableEquiv.piUnique π).measurable
  map_eq := pi_unique μ

theorem Measure.map_piUnique_symm [Unique ι] :
    map (MeasurableEquiv.piUnique α).symm (μ (default : ι)) = Measure.pi μ :=
  (measurePreserving_piUnique μ).symm _ |>.map_eq

end Measure


section Marginal

open TopologicalSpace

variable {δ δ' : Type _} {π : δ → Type _} [∀ x, MeasurableSpace (π x)]

variable {μ : ∀ i, Measure (π i)} [∀ i, SigmaFinite (μ i)]

theorem lintegral_of_isEmpty {α} [MeasurableSpace α] [IsEmpty α] (μ : Measure α) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = 0 := by convert lintegral_zero_measure f

variable {s t : Finset δ} {f g : (∀ i, π i) → ℝ≥0∞} {x y : ∀ i, π i} {i : δ}

theorem measurable_updateSet : Measurable (updateSet x s) := by
  simp_rw [updateSet, measurable_pi_iff]
  intro i
  by_cases h : i ∈ s <;> simp [h, measurable_pi_apply]

/-- Integrate `f(x₁,…,xₙ)` over all variables `xᵢ` where `i ∈ s`. Return a function in the
  remaining variables (it will be constant in the `xᵢ` for `i ∈ s`).
  This is the marginal distribution of all variables not in `s`. -/
def marginal (μ : ∀ i, Measure (π i)) (s : Finset δ) (f : (∀ i, π i) → ℝ≥0∞) (x : ∀ i, π i) :
    ℝ≥0∞ :=
  ∫⁻ y : ∀ i : s, π i, f (updateSet x s y) ∂Measure.pi fun i : s => μ i

-- Note: this notation is not a binder. This is more convenient since it returns a function.
notation "∫⋯∫_" s ", " f " ∂" μ:70 => marginal μ s f

notation "∫⋯∫_" s ", " f => marginal (fun _ ↦ volume) s f

variable (μ)

theorem _root_.Measurable.marginal (hf : Measurable f) : Measurable (∫⋯∫_s, f ∂μ) := by
  refine' Measurable.lintegral_prod_right _
  refine' hf.comp _
  rw [measurable_pi_iff]; intro i
  by_cases hi : i ∈ s
  · simp [hi, updateSet]
    exact measurable_pi_iff.1 measurable_snd _
  · simp [hi, updateSet]
    exact measurable_pi_iff.1 measurable_fst _

@[simp] theorem marginal_empty (f : (∀ i, π i) → ℝ≥0∞) : ∫⋯∫_∅, f ∂μ = f := by
  ext1 x
  simp_rw [marginal, Measure.pi_of_empty fun i : (∅ : Finset δ) => μ i]
  apply lintegral_dirac'
  exact Subsingleton.measurable

/-- The marginal distribution is independent of the variables in `s`. -/
-- todo: notation `∀ i ∉ s, ...`
@[gcongr]
theorem marginal_congr {x y : ∀ i, π i} (f : (∀ i, π i) → ℝ≥0∞)
    (h : ∀ (i) (_ : i ∉ s), x i = y i) :
    (∫⋯∫_s, f ∂μ) x = (∫⋯∫_s, f ∂μ) y := by
  dsimp [marginal, updateSet]; rcongr; exact h _ ‹_›

theorem marginal_update_of_mem [DecidableEq δ] {i : δ} (hi : i ∈ s)
    (f : (∀ i, π i) → ℝ≥0∞) (x : ∀ i, π i) (y : π i) :
    (∫⋯∫_s, f ∂μ) (Function.update x i y) = (∫⋯∫_s, f ∂μ) x := by
  gcongr with j hj
  have : j ≠ i := by rintro rfl; exact hj hi
  apply update_noteq this

theorem marginal_union [DecidableEq δ] (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f)
    (hst : Disjoint s t) : ∫⋯∫_s ∪ t, f ∂μ = ∫⋯∫_s, ∫⋯∫_t, f ∂μ ∂μ := by
  ext1 x
  set e₁ := (finsetUnionEquivSum s t hst).symm
  set e₂ := MeasurableEquiv.piCongrLeft (fun i : ↥(s ∪ t) => π i) e₁
  set e₃ := MeasurableEquiv.piSum fun b ↦ π (e₁ b)
  calc (∫⋯∫_s ∪ t, f ∂μ) x
      = ∫⁻ (y : (i : ↥(s ∪ t)) → π i), f (updateSet x (s ∪ t) y)
          ∂.pi fun i' : ↥(s ∪ t) ↦ μ i' := by rfl
    _ = ∫⁻ (y : (i : s ⊕ t) → π (e₁ i)), f (updateSet x (s ∪ t) (e₂ y))
          ∂.pi fun i' : s ⊕ t ↦ μ (e₁ i') := by
        simp_rw [← Measure.pi_map_left _ e₁, lintegral_map_equiv]
    _ = ∫⁻ (y : ((i : s) → π i) × ((j : t) → π j)), f (updateSet x (s ∪ t) (e₂ (e₃ y)))
          ∂(Measure.pi fun i : s ↦ μ i).prod (.pi fun j : t ↦ μ j) := by
        simp_rw [← Measure.pi_sum, lintegral_map_equiv]; rfl
    _ = ∫⁻ (y : (i : s) → π i), ∫⁻ (z : (j : t) → π j), f (updateSet x (s ∪ t) (e₂ (e₃ (y, z))))
          ∂.pi fun j : t ↦ μ j ∂.pi fun i : s ↦ μ i := by
        apply lintegral_prod
        apply Measurable.aemeasurable
        exact hf.comp <| measurable_updateSet.comp <| e₂.measurable.comp e₃.measurable
    _ = (∫⋯∫_s, ∫⋯∫_t, f ∂μ ∂μ) x := by
        simp_rw [marginal, updateSet_updateSet hst]
        rfl

theorem marginal_union' (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {s t : Finset δ}
    (hst : Disjoint s t) : ∫⋯∫_s ∪ t, f ∂μ = ∫⋯∫_t, ∫⋯∫_s, f ∂μ ∂μ := by
  rw [Finset.union_comm, marginal_union μ f hf hst.symm]

variable {μ}

theorem marginal_singleton [DecidableEq δ] (f : (∀ i, π i) → ℝ≥0∞) (i : δ) :
    ∫⋯∫_{i}, f ∂μ = fun x => ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i := by
  let α : Type _ := ({i} : Finset δ)
  let e := (MeasurableEquiv.piUnique fun j : α ↦ π j).symm
  ext1 x
  calc (∫⋯∫_{i}, f ∂μ) x
      = ∫⁻ (y : π (default : α)), f (updateSet x {i} (e y)) ∂μ (default : α) := by
        simp_rw [marginal, ← Measure.map_piUnique_symm, lintegral_map_equiv]
    _ = ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i := by simp [update_eq_updateSet]

theorem integral_update [DecidableEq δ] (f : (∀ i, π i) → ℝ≥0∞) (i : δ) (x : ∀ i, π i) :
    ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i = (∫⋯∫_{i}, f ∂μ) x := by
  simp_rw [marginal_singleton f i]

/-- Peel off a single integral from a `marginal` integral at the beginning (compare with
`marginal_insert'`, which peels off an integral at the end). -/
theorem marginal_insert [DecidableEq δ] (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∉ s) (x : ∀ i, π i) :
    (∫⋯∫_insert i s, f ∂μ) x = ∫⁻ xᵢ, (∫⋯∫_s, f ∂μ) (Function.update x i xᵢ) ∂μ i := by
  rw [Finset.insert_eq, marginal_union μ f hf (Finset.disjoint_singleton_left.mpr hi),
    marginal_singleton]

/-- Peel off a single integral from a `marginal` integral at the beginning (compare with
`marginal_erase'`, which peels off an integral at the end). -/
theorem marginal_erase [DecidableEq δ] (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∈ s) (x : ∀ i, π i) :
    (∫⋯∫_s, f ∂μ) x = ∫⁻ xᵢ, (∫⋯∫_(erase s i), f ∂μ) (Function.update x i xᵢ) ∂μ i := by
  simpa [insert_erase hi] using marginal_insert _ hf (not_mem_erase i s) x

-- move next to `measurable_update` in `MeasureTheory.MeasurableSpace`
-- unused
theorem measurable_update' {δ : Type _} [DecidableEq δ] {π : δ → Type _}
    [∀ a : δ, MeasurableSpace (π a)] {a : δ} :
    Measurable (fun p : (∀ i, π i) × π a ↦ update p.1 a p.2) := by
  rw [measurable_pi_iff]; intro j
  dsimp [update]
  split_ifs with h
  · subst h
    dsimp
    exact measurable_snd
  · exact measurable_pi_iff.1 measurable_fst _

theorem measurable_update_left {δ : Type _} [DecidableEq δ] {π : δ → Type _}
    [∀ a : δ, MeasurableSpace (π a)] {a : δ} {x : π a} :
    Measurable (update · a x) := by
  rw [measurable_pi_iff]; intro j
  dsimp [update]
  split_ifs with h
  · subst h
    exact measurable_const
  · exact measurable_pi_apply j

/-- Peel off a single integral from a `marginal` integral at the end (compare with
`marginal_insert`, which peels off an integral at the beginning). -/
theorem marginal_insert' [DecidableEq δ] (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∉ s) :
    ∫⋯∫_insert i s, f ∂μ = ∫⋯∫_s, (fun x ↦ ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ∂μ := by
  rw [Finset.insert_eq, Finset.union_comm,
    marginal_union (s := s) μ f hf (Finset.disjoint_singleton_right.mpr hi), marginal_singleton]

/-- Peel off a single integral from a `marginal` integral at the end (compare with
`marginal_erase`, which peels off an integral at the beginning). -/
theorem marginal_erase' [DecidableEq δ] (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∈ s) :
    ∫⋯∫_s, f ∂μ = ∫⋯∫_(erase s i), (fun x ↦ ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ∂μ := by
  simpa [insert_erase hi] using marginal_insert' _ hf (not_mem_erase i s)

open Filter

@[gcongr]
theorem marginal_mono {f g : (∀ i, π i) → ℝ≥0∞} (hfg : f ≤ g) : ∫⋯∫_s, f ∂μ ≤ ∫⋯∫_s, g ∂μ :=
  fun _ => lintegral_mono fun _ => hfg _

theorem marginal_univ [Fintype δ] {f : (∀ i, π i) → ℝ≥0∞} :
    ∫⋯∫_univ, f ∂μ = fun _ => ∫⁻ x, f x ∂Measure.pi μ := by
  let e : { j // j ∈ Finset.univ } ≃ δ := Equiv.subtypeUnivEquiv mem_univ
  ext1 x
  simp_rw [marginal, ← Measure.pi_map_left μ e, lintegral_map_equiv, updateSet]
  simp
  rfl

theorem lintegral_eq_marginal_univ [Fintype δ] {f : (∀ i, π i) → ℝ≥0∞} (x : ∀ i, π i) :
    ∫⁻ x, f x ∂Measure.pi μ = (∫⋯∫_univ, f ∂μ) x := by rw [marginal_univ]

theorem marginal_image [DecidableEq δ] {e : δ' → δ} (he : Injective e) (s : Finset δ')
    {f : (∀ i, π (e i)) → ℝ≥0∞} (hf : Measurable f) (x : ∀ i, π i) :
      (∫⋯∫_s.image e, f ∘ (· ∘' e) ∂μ) x = (∫⋯∫_s, f ∂μ ∘' e) (x ∘' e) := by
  have h : Measurable ((· ∘' e) : (∀ i, π i) → _) :=
    measurable_pi_iff.mpr <| λ i ↦ measurable_pi_apply (e i)
  induction s using Finset.induction generalizing x
  case empty => simp
  case insert i s hi ih =>
    rw [image_insert, marginal_insert _ (hf.comp h) (he.mem_finset_image.not.mpr hi),
      marginal_insert _ hf hi]
    simp_rw [ih, ← update_comp_eq_of_injective' x he]

theorem marginal_update_of_not_mem [DecidableEq δ] {i : δ}
    {f : (∀ i, π i) → ℝ≥0∞} (hf : Measurable f) (hi : i ∉ s) (x : ∀ i, π i) (y : π i) :
    (∫⋯∫_s, f ∂μ) (Function.update x i y) = (∫⋯∫_s, f ∘ (Function.update · i y) ∂μ) x := by
  induction s using Finset.induction generalizing x
  case empty => simp
  case insert i' s hi' ih =>
    rw [marginal_insert _ hf hi', marginal_insert _ (hf.comp measurable_update_left) hi']
    have hii' : i ≠ i' := mt (by rintro rfl; exact mem_insert_self i s) hi
    simp_rw [update_comm hii', ih (mt Finset.mem_insert_of_mem hi)]

theorem marginal_eq_of_subset {f g : (∀ i, π i) → ℝ≥0∞} (hst : s ⊆ t)
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫_s, f ∂μ = ∫⋯∫_s, g ∂μ) :
    ∫⋯∫_t, f ∂μ = ∫⋯∫_t, g ∂μ := by
  rw [← union_sdiff_of_subset hst, marginal_union' μ f hf disjoint_sdiff,
    marginal_union' μ g hg disjoint_sdiff, hfg]

theorem marginal_le_of_subset {f g : (∀ i, π i) → ℝ≥0∞} (hst : s ⊆ t)
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫_s, f ∂μ ≤ ∫⋯∫_s, g ∂μ) :
    ∫⋯∫_t, f ∂μ ≤ ∫⋯∫_t, g ∂μ := by
  rw [← union_sdiff_of_subset hst, marginal_union' μ f hf disjoint_sdiff,
    marginal_union' μ g hg disjoint_sdiff]
  exact marginal_mono hfg

theorem lintegral_eq_of_marginal_eq [Fintype δ] (s : Finset δ) {f g : (∀ i, π i) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫_s, f ∂μ = ∫⋯∫_s, g ∂μ) :
    ∫⁻ x, f x ∂Measure.pi μ = ∫⁻ x, g x ∂Measure.pi μ := by
  rcases isEmpty_or_nonempty (∀ i, π i) with h|⟨⟨x⟩⟩
  · simp_rw [lintegral_of_isEmpty]
  simp_rw [lintegral_eq_marginal_univ x, marginal_eq_of_subset (Finset.subset_univ s) hf hg hfg]

theorem integral_le_of_marginal_le [Fintype δ] (s : Finset δ) {f g : (∀ i, π i) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫_s, f ∂μ ≤ ∫⋯∫_s, g ∂μ) :
    ∫⁻ x, f x ∂Measure.pi μ ≤ ∫⁻ x, g x ∂Measure.pi μ := by
  rcases isEmpty_or_nonempty (∀ i, π i) with h|⟨⟨x⟩⟩
  · simp_rw [lintegral_of_isEmpty, le_rfl]
  simp_rw [lintegral_eq_marginal_univ x, marginal_le_of_subset (Finset.subset_univ s) hf hg hfg x]

end Marginal


section

/-! Compute some measures using marginal. -/

variable {α : Fin (n+1) → Type*} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
variable [∀ i, SigmaFinite (μ i)]

open Fin

@[simp]
theorem insertNth_dcomp_succAbove (i : Fin (n + 1)) (x : α i) (p : ∀ j, α (i.succAbove j)) :
    insertNth i x p ∘' i.succAbove = p :=
  funext (insertNth_apply_succAbove i x p)

@[simp]
theorem insertNth_apply_dcomp_succAbove (i : Fin (n + 1)) (x : α i) (z : ∀ i, α i) :
    insertNth i x (z ∘' i.succAbove) = update z i x := by
  ext j
  rcases eq_or_ne i j with rfl|hij
  · simp
  obtain ⟨j', rfl⟩ := exists_succAbove_eq_iff.mpr hij.symm
  simp [dcomp, hij.symm]

theorem insertNth_comp_dcomp_succAbove (i : Fin (n + 1)) (x : α i) :
    insertNth i x ∘ (· ∘' i.succAbove) = (update · i x) := by
  simp [comp]

theorem insertNth_eq_of_ne {i j : Fin (n + 1)} (h : i ≠ j) (x x' : α i)
    (p : ∀ j, α (i.succAbove j)) : insertNth i x p j = insertNth i x' p j := by
  obtain ⟨j', rfl⟩ := exists_succAbove_eq_iff.mpr h.symm
  simp

@[simp]
theorem update_insertNth {i : Fin (n + 1)} (x x' : α i) (p : ∀ j, α (i.succAbove j)) :
    update (insertNth i x p) i x' = insertNth i x' p := by
  ext j
  rcases eq_or_ne i j with rfl|hij
  · simp
  simp [hij.symm, insertNth_eq_of_ne hij x x']

theorem measurable_insertNth {i : Fin (n+1)} (x : α i) :
    Measurable (insertNth i x) := by
  refine measurable_pi_iff.mpr fun j ↦ ?_
  rcases eq_or_ne i j with rfl|hij
  · simp
  obtain ⟨j', rfl⟩ := exists_succAbove_eq_iff.mpr hij.symm
  simp [measurable_pi_apply]

/-- An example of a computation we can do with `marginal`. Working with `marginal` directly is
  probably easier than using this lemma, though. This is roughly `FUBINI_SIMPLE` from HOL Light,
  though this has weaker assumptions (HOL Light assumes that `s` is bounded in `ℝⁿ`).
  Note: we could generalize `i.succAbove : Fin n → Fin (n+1)` to an arbitrary injective map `ι → ι'`
  whose range misses one point. -/
theorem lintegral_measure_insertNth {s : Set (∀ i, α i)} (hs : MeasurableSet s) (i : Fin (n+1)) :
    ∫⁻ x, Measure.pi (μ ∘' i.succAbove) (insertNth i x ⁻¹' s) ∂μ i =
    Measure.pi μ s := by
  rcases isEmpty_or_nonempty (α i) with h|⟨⟨x⟩⟩
  · have : IsEmpty (∀ i, α i) := ⟨λ x ↦ h.elim <| x i⟩
    simp [lintegral_of_isEmpty, Measure.eq_zero_of_isEmpty]
  rcases isEmpty_or_nonempty (∀ j, α (i.succAbove j)) with h|⟨⟨y⟩⟩
  · have : IsEmpty (∀ i, α i) := ⟨λ x ↦ h.elim <| λ j ↦ x _⟩
    simp [Measure.eq_zero_of_isEmpty]
  have hi : i ∉ ({i}ᶜ : Finset _) := not_mem_compl.mpr <| mem_singleton_self i
  let z := insertNth i x y
  calc ∫⁻ x : α i, Measure.pi (μ ∘' succAbove i) (insertNth i x ⁻¹' s) ∂μ i
      = ∫⁻ x : α i, (∫⋯∫_.univ, indicator (insertNth i x ⁻¹' s) 1 ∂μ ∘' succAbove i) y ∂μ i := by
        simp_rw [← lintegral_indicator_one (measurable_insertNth _ hs),
          lintegral_eq_marginal_univ y]
    _ = ∫⁻ x : α i, (∫⋯∫_.univ, indicator (insertNth i x ⁻¹' s) 1 ∂μ ∘' succAbove i)
          (z ∘' i.succAbove) ∂μ i := by
        rw [← insertNth_dcomp_succAbove i x y]
    _ = ∫⁻ x : α i, (∫⋯∫_{i}ᶜ,
          indicator (insertNth i x ⁻¹' s) 1 ∘ (· ∘' succAbove i) ∂μ) z ∂μ i := by
        simp_rw [← λ x ↦ marginal_image succAbove_right_injective (μ := μ) .univ
          (f := indicator (insertNth i x ⁻¹' s) (1 : ((j : Fin n) → α (succAbove i j)) → ℝ≥0∞))
          (measurable_one.indicator (measurable_insertNth _ hs)) z, Fin.image_succAbove_univ]
    _ = ∫⁻ x : α i, (∫⋯∫_{i}ᶜ,
          indicator (insertNth i x ∘ (· ∘' succAbove i) ⁻¹' s) 1 ∂μ) z ∂μ i := by
        rfl
    _ = ∫⁻ x : α i, (∫⋯∫_{i}ᶜ,
          indicator ((Function.update · i x) ⁻¹' s) 1 ∂μ) z ∂μ i := by
        simp [comp]
    _ = (∫⋯∫_insert i {i}ᶜ, indicator s 1 ∂μ) z := by
        simp_rw [marginal_insert _ (measurable_one.indicator hs) hi,
          marginal_update_of_not_mem (measurable_one.indicator hs) hi]
        rfl
    _ = (∫⋯∫_.univ, indicator s 1 ∂μ) z := by simp
    _ = Measure.pi μ s := by rw [← lintegral_indicator_one hs, lintegral_eq_marginal_univ z]

end

section MeasureSpace

/-! Compute some measures using marginal. -/

variable {α : Fin (n+1) → Type*} [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume (α := α i))]

open Fin

theorem lintegral_volume_insertNth {s : Set (∀ i, α i)} (hs : MeasurableSet s) (i : Fin (n+1)) :
    ∫⁻ x, volume (insertNth i x ⁻¹' s) = volume s :=
  lintegral_measure_insertNth (fun _ ↦ volume) hs i

end MeasureSpace


end MeasureTheory
