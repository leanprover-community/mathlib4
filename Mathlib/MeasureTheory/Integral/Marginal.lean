/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module main
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.ContDiff

/-!
# Marginals of multivariate functions
-/


open scoped Classical BigOperators Topology ENNReal
open Filter

noncomputable section

variable {ι ι' ι'' : Type _}

section Finset

open Finset

namespace Real

theorem prod_rpow {ι} (s : Finset ι) {f : ι → ℝ} (hf : 0 ≤ f) (r : ℝ) :
    ∏ i in s, f i ^ r = (∏ i in s, f i) ^ r :=
  finset_prod_rpow s f (fun i _ ↦ hf i) r
#align real.prod_rpow Real.prod_rpow

end Real

namespace NNReal

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

theorem rpow_add_of_nonneg (x : ℝ≥0) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
  x ^ (y + z) = x ^ y * x ^ z := by
  by_cases h : y + z = 0
  · obtain rfl : y = 0 := by linarith
    obtain rfl : z = 0 := by linarith
    simp [h]
  · exact rpow_add' _ h

end NNReal

namespace ENNReal

theorem rpow_add_of_nonneg {x : ℝ≥0∞} (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  induction x using recTopCoe
  · rcases hy.eq_or_lt with rfl|hy
    · rw [rpow_zero, one_mul, zero_add]
    rcases hz.eq_or_lt with rfl|hz
    · rw [rpow_zero, mul_one, add_zero]
    simp [top_rpow_of_pos, hy, hz, add_pos hy hz]
  simp [coe_rpow_of_nonneg, hy, hz, add_nonneg hy hz, NNReal.rpow_add_of_nonneg _ hy hz]

theorem prod_rpow {ι} (s : Finset ι) (f : ι → ℝ≥0∞) (r : ℝ) :
    ∏ i in s, f i ^ r = (∏ i in s, f i) ^ r :=
  sorry


end ENNReal


variable {α β γ : Type _}

theorem Equiv.finset_image_univ_eq_univ [Fintype α] [Fintype β] (f : α ≃ β) : univ.image f = univ :=
  Finset.image_univ_of_surjective f.surjective
#align equiv.finset_image_univ_eq_univ Equiv.finset_image_univ_eq_univ

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
#align finset.prod_comp_equiv Finset.prod_comp_equiv

theorem prod_univ_comp_equiv [Fintype α] [Fintype γ] (f : γ → β) (g : α ≃ γ) :
    ∏ a, f (g a) = ∏ b, f b :=
  g.prod_comp f
#align prod_univ_comp_equiv prod_univ_comp_equiv

namespace Function

@[simp] theorem comp_def (f : β → γ) (g : α → β) : f ∘ g = fun x => f (g x) := rfl

end Function

namespace Finset

theorem insert_compl_insert [Fintype ι] {s : Finset ι} {i : ι} (hi : i ∉ s) :
    insert i (insert i s)ᶜ = sᶜ := by
  simp_rw [@eq_compl_comm _ _ s, compl_insert, compl_erase, compl_compl, erase_insert hi]
#align finset.insert_compl_insert Finset.insert_compl_insert

@[to_additive]
theorem mul_prod_eq_prod_insertNone {α} {M} [CommMonoid M] (f : α → M) (x : M) (s : Finset α) :
    x * ∏ i in s, f i = ∏ i in insertNone s, i.elim x f :=
  (prod_insertNone (fun i => i.elim x f) _).symm
#align finset.mul_prod_eq_prod_insert_none Finset.mul_prod_eq_prod_insertNone
#align finset.add_sum_eq_sum_insert_none Finset.add_sum_eq_sum_insertNone

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

end Finset

end Finset

section Calculus

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] [Fintype ι]

variable {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

-- ⇑(fderiv ℝ (λ (x_1 : ℝ), update x i x_1) y)
theorem fderiv_update {x : ∀ i, E i} {i : ι} (y : E i) :
    fderiv 𝕜 (Function.update x i) y =
      ContinuousLinearMap.pi (Function.update 0 i (ContinuousLinearMap.id 𝕜 (E i))) :=
  sorry
#align fderiv_update fderiv_update

theorem ContinuousLinearMap.norm_le_norm_pi (f : ∀ i, F →L[𝕜] E i) (i : ι) :
    ‖f i‖ ≤ ‖ContinuousLinearMap.pi f‖ :=
  sorry
#align continuous_linear_map.norm_le_norm_pi ContinuousLinearMap.norm_le_norm_pi

theorem ContinuousLinearMap.norm_pi [Nonempty ι] (f : ∀ i, F →L[𝕜] E i) :
    ‖ContinuousLinearMap.pi f‖ =
      (Finset.univ.image fun i => ‖f i‖).max' (Finset.univ_nonempty.image _) :=
  sorry
#align continuous_linear_map.norm_pi ContinuousLinearMap.norm_pi

variable (E)

theorem ContinuousLinearMap.norm_pi_update_eq_one {i : ι} :
    ‖ContinuousLinearMap.pi (Function.update 0 i (ContinuousLinearMap.id 𝕜 (E i)))‖ = 1 :=
  sorry
#align continuous_linear_map.norm_pi_update_eq_one ContinuousLinearMap.norm_pi_update_eq_one

end Calculus

section Logic

open Sum

@[simp]
theorem imp_and_neg_imp_iff (p q : Prop) : (p → q) ∧ (¬p → q) ↔ q := by
  simp_rw [imp_iff_or_not, not_not, ← or_and_left, not_and_self_iff, or_false_iff]
#align imp_and_neg_imp_iff imp_and_neg_imp_iff

theorem cast_sum_rec {α β : Type _} {P : α ⊕ β → Sort _} (f : ∀ i, P (inl i)) (g : ∀ j, P (inr j))
    (x y : α ⊕ β) (h : x = y) :
    cast (congr_arg P h) (@Sum.rec _ _ _ f g x) = @Sum.rec _ _ _ f g y := by cases h; rfl
#align cast_sum_rec cast_sum_rec

theorem Eq.rec_eq_cast {α : Sort _} {P : α → Sort _} {x y : α} (h : x = y) (z : P x) :
    h ▸ z = cast (congr_arg P h) z := by induction h; rfl

end Logic

open Set
namespace Equiv
open Set

-- simps doesn't work from another module :-(
lemma piCongrLeft_apply {P : β → Sort v} {e : α ≃ β}
    (f : (a : α) → P (e a)) (b : β) :
    piCongrLeft P e f b = cast (congr_arg P (e.apply_symm_apply b)) (f (e.symm b)) :=
  Eq.rec_eq_cast _ _

lemma piCongrLeft_symm_apply {P : β → Sort v} {e : α ≃ β}
    (g : (b : β) → P b) (a : α) :
    (piCongrLeft P e).symm g a = g (e a) := rfl

lemma subtypeEquivRight_apply {p q : α → Prop} (e : ∀ x, p x ↔ q x)
    (z : { x // p x }) : subtypeEquivRight e z = ⟨z, (e z.1).mp z.2⟩ := rfl

lemma subtypeEquivRight_symm_apply {p q : α → Prop} (e : ∀ x, p x ↔ q x)
    (z : { x // q x }) : (subtypeEquivRight e).symm z = ⟨z, (e z.1).mpr z.2⟩ := rfl

variable {α : ι → Type _}

theorem piCongrLeft_symm_preimage_pi (f : ι' ≃ ι) (s : Set ι) (t : ∀ i, Set (α i)) :
    ((f.piCongrLeft α).symm ⁻¹' (f ⁻¹' s).pi fun i' => t <| f i') = s.pi t := by
  ext; simp_rw [mem_preimage, Set.mem_pi, piCongrLeft_symm_apply]
  convert f.forall_congr_left; rfl
#align equiv.Pi_congr_left_symm_preimage_pi Equiv.piCongrLeft_symm_preimage_pi

theorem piCongrLeft_preimage_univ_pi (f : ι' ≃ ι) (t : ∀ i, Set (α i)) :
    f.piCongrLeft α ⁻¹' pi univ t = pi univ fun i => t (f i) := by
  apply Set.ext; rw [← (f.piCongrLeft α).symm.forall_congr_left]
  intro x; simp_rw [mem_preimage, apply_symm_apply, piCongrLeft_symm_apply, mem_univ_pi]
  exact f.forall_congr_left.symm
#align equiv.Pi_congr_left_preimage_univ_pi Equiv.piCongrLeft_preimage_univ_pi

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
#align equiv.Pi_sum Equiv.piSum

/-- unused -/
def piSum' (π : ι → Type _) (π' : ι' → Type _) :
    ((∀ i, π i) × ∀ i', π' i') ≃ ∀ i, Sum.elim π π' i :=
  Equiv.piSum (Sum.elim π π')
#align equiv.Pi_sum' Equiv.piSum'

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
#align equiv.set.union_apply_left' Equiv.Set.union_apply_left'

theorem Set.union_apply_right' {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅)
    {a : α} (ha : a ∈ t) : Equiv.Set.union H ⟨a, Set.mem_union_right _ ha⟩ = Sum.inr ⟨a, ha⟩ :=
  dif_neg fun h => H ⟨h, ha⟩
#align equiv.set.union_apply_right' Equiv.Set.union_apply_right'

theorem sum_rec_congr (P : ι ⊕ ι' → Sort _) (f : ∀ i, P (inl i)) (g : ∀ i, P (inr i))
    {x y : ι ⊕ ι'} (h : x = y) :
    @Sum.rec _ _ _ f g x = cast (congr_arg P h.symm) (@Sum.rec _ _ _ f g y) := by cases h; rfl
#align equiv.sum_rec_congr Equiv.sum_rec_congr

theorem piCongrLeft_sum_inl (π : ι'' → Type _) (e : ι ⊕ ι' ≃ ι'') (f : ∀ i, π (e (inl i)))
    (g : ∀ i, π (e (inr i))) (i : ι) :
    piCongrLeft π e (piSum (fun x => π (e x)) (f, g)) (e (inl i)) = f i := by
  simp_rw [piCongrLeft_apply, piSum_apply, sum_rec_congr _ _ _ (e.symm_apply_apply (inl i)),
    cast_cast, cast_eq]
#align equiv.Pi_congr_left_sum_inl Equiv.piCongrLeft_sum_inl

theorem piCongrLeft_sum_inr (π : ι'' → Type _) (e : ι ⊕ ι' ≃ ι'') (f : ∀ i, π (e (inl i)))
    (g : ∀ i, π (e (inr i))) (j : ι') :
    piCongrLeft π e (piSum (fun x => π (e x)) (f, g)) (e (inr j)) = g j := by
  simp_rw [piCongrLeft_apply, piSum_apply, sum_rec_congr _ _ _ (e.symm_apply_apply (inr j)),
    cast_cast, cast_eq]
#align equiv.Pi_congr_left_sum_inr Equiv.piCongrLeft_sum_inr

end Equiv

namespace Option

theorem elim'_comp {ι α β} (h : α → β) {f : ι → α} {x : α} {i : Option ι} :
    (i.elim (h x) fun j => h (f j)) = h (i.elim x f) := by cases i <;> rfl
#align option.elim_comp Option.elim'_comp

theorem elim'_comp₂ {ι α β γ} (h : α → β → γ) {f : ι → α} {x : α} {g : ι → β} {y : β}
    {i : Option ι} : (i.elim (h x y) fun j => h (f j) (g j)) = h (i.elim x f) (i.elim y g) := by
  cases i <;> rfl
#align option.elim_comp₂ Option.elim'_comp₂

theorem elim'_apply {α β ι : Type _} {f : ι → α → β} {x : α → β} {i : Option ι} {y : α} :
    i.elim x f y = i.elim (x y) fun j => f j y := by rw [elim'_comp fun f : α → β => f y]
#align option.elim_apply Option.elim'_apply

end Option

open Function MeasureTheory.OuterMeasure MeasurableSpace Equiv

section Function

open Set

variable {α : ι → Type _}

/-- Given one value over a unique, we get a dependent function. -/
def uniqueElim [Unique ι] (x : α (default : ι)) (i : ι) : α i := by
  rw [Unique.eq_default i]
  exact x
#align unique_elim uniqueElim

@[simp]
theorem uniqueElim_default {_ : Unique ι} (x : α (default : ι)) : uniqueElim x (default : ι) = x :=
  rfl
#align unique_elim_default uniqueElim_default

theorem uniqueElim_preimage [Unique ι] (t : ∀ i, Set (α i)) :
    uniqueElim ⁻¹' pi univ t = t (default : ι) := by ext; simp [Unique.forall_iff]
#align unique_elim_preimage uniqueElim_preimage

theorem pred_update {α} {β : α → Type _} (P : ∀ ⦃a⦄, β a → Prop) (f : ∀ a, β a) (a' : α) (v : β a')
    (a : α) : P (update f a' v a) ↔ a = a' ∧ P v ∨ a ≠ a' ∧ P (f a) := by
  rw [update]
  split_ifs with h
  · subst h
    simp
  · rw [← Ne.def] at h
    simp [h]
#align pred_update pred_update

theorem surjective_decode_iget (α : Type _) [Encodable α] [Inhabited α] :
    Surjective fun n => (Encodable.decode (α := α) n).iget := fun x =>
  ⟨Encodable.encode x, by simp_rw [Encodable.encodek]⟩
#align surjective_decode_iget surjective_decode_iget

end Function

section Set

open Set

-- @[simps apply symm_apply]
/-- `s ∪ t` (using finset union) is equivalent to `s ∪ t` (using set union) -/
def Equiv.finsetUnion {α} (s t : Finset α) : ((s ∪ t : Finset α) : Set α) ≃ (s ∪ t : Set α) :=
  subtypeEquivRight <| by simp
#align equiv.finset_union Equiv.finsetUnion

/-- The disjoint union of finsets is a sum -/
def finsetUnionEquivSum {α} (s t : Finset α) (h : Disjoint s t) : (s ∪ t : Finset α) ≃ s ⊕ t :=
  (Equiv.finsetUnion s t).trans <| Equiv.Set.union <| by
    rw [← Finset.coe_inter, ← Finset.coe_empty]
    exact h.le_bot
#align finset_union_equiv_sum finsetUnionEquivSum

@[simp]
theorem finsetUnionEquivSum_symm_inl {α} {s t : Finset α} (h : Disjoint s t) (x : s) :
    (finsetUnionEquivSum s t h).symm (Sum.inl x) = ⟨x, Finset.mem_union.mpr <| Or.inl x.2⟩ :=
  rfl
#align finset_union_equiv_sum_symm_inl finsetUnionEquivSum_symm_inl

@[simp]
theorem finsetUnionEquivSum_symm_inr {α} {s t : Finset α} (h : Disjoint s t) (y : t) :
    (finsetUnionEquivSum s t h).symm (Sum.inr y) = ⟨y, Finset.mem_union.mpr <| Or.inr y.2⟩ :=
  rfl
#align finset_union_equiv_sum_symm_inr finsetUnionEquivSum_symm_inr

@[simp]
theorem finsetUnionEquivSum_symm_inl' {α} {s t : Finset α} (h : Disjoint s t) (x : α) (hx : x ∈ s)
    (h2x : x ∈ s ∪ t) : (finsetUnionEquivSum s t h).symm (Sum.inl ⟨x, hx⟩) = ⟨x, h2x⟩ :=
  rfl
#align finset_union_equiv_sum_symm_inl' finsetUnionEquivSum_symm_inl'

@[simp]
theorem finsetUnionEquivSum_symm_inr' {α} {s t : Finset α} (h : Disjoint s t) (y : t) :
    (finsetUnionEquivSum s t h).symm (Sum.inr y) = ⟨y, Finset.mem_union.mpr <| Or.inr y.2⟩ :=
  rfl
#align finset_union_equiv_sum_symm_inr' finsetUnionEquivSum_symm_inr'

-- @[simp]
-- theorem finsetUnionEquivSum_left {α} {s t : Finset α} (h : Disjoint s t) (x : (s ∪ t : Finset α))
--     (hx : ↑x ∈ s) :
--     finsetUnionEquivSum s t h x = Sum.inl ⟨x, hx⟩ :=
--   sorry
-- #align finset_union_equiv_sum_left finsetUnionEquivSum_left

-- -- equiv.set.union_apply_left _ $ finset.mem_coe.mp hx
-- @[simp]
-- theorem finsetUnionEquivSum_right {α} {s t : Finset α} (h : Disjoint s t) (x : (s ∪ t : Finset α))
--     (hx : ↑x ∈ t) : finsetUnionEquivSum s t h x = Sum.inr ⟨x, hx⟩ :=
--   sorry
-- #align finset_union_equiv_sum_right finsetUnionEquivSum_right

theorem iUnion_univ_pi {ι ι₂} {α : ι → Type _} (t : ∀ i, ι₂ → Set (α i)) :
    (⋃ x : ι → ι₂, pi univ fun i => t i (x i)) = pi univ fun i => ⋃ j : ι₂, t i j := by
  ext
  simp [Classical.skolem]
#align Union_univ_pi iUnion_univ_pi

theorem eval_preimage {ι} {α : ι → Type _} {i : ι} {s : Set (α i)} :
    eval i ⁻¹' s = pi univ (update (fun i => univ) i s) := by
  ext x
  simp [@forall_update_iff _ (fun i => Set (α i)) _ _ _ _ fun i' y => x i' ∈ y]
#align eval_preimage eval_preimage

theorem eval_preimage' {ι} {α : ι → Type _} {i : ι} {s : Set (α i)} :
    eval i ⁻¹' s = pi {i} (update (fun i => univ) i s) := by ext; simp
#align eval_preimage' eval_preimage'

theorem mem_pi_univ {ι : Type _} {α : ι → Type _} (t : ∀ i, Set (α i)) (x : ∀ i, α i) :
    x ∈ pi univ t ↔ ∀ i, x i ∈ t i := by simp
#align mem_pi_univ mem_pi_univ

theorem pi_univ_ite {ι} {α : ι → Type _} (s : Set ι) (t : ∀ i, Set (α i)) :
    (pi univ fun i => if i ∈ s then t i else univ) = s.pi t := by
  ext; simp_rw [Set.mem_pi]; apply forall_congr'; intro i; split_ifs with h <;> simp [h]
#align pi_univ_ite pi_univ_ite

theorem pi_univ_eq_iInter {ι} {α : ι → Type _} (t : ∀ i, Set (α i)) :
    pi univ t = ⋂ i, eval i ⁻¹' t i := by simp_rw [pi_def, mem_univ, iInter_true]
#align pi_univ_eq_Inter pi_univ_eq_iInter

end Set

section Measurable

open Set

variable {α : ι → Type _}

theorem measurable_uniqueElim [Unique ι] [∀ i, MeasurableSpace (α i)] :
    Measurable (uniqueElim : α (default : ι) → ∀ i, α i) := by
  simp_rw [measurable_pi_iff, Unique.forall_iff, uniqueElim_default]; exact measurable_id
#align measurable_unique_elim measurable_uniqueElim

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
#align measurable_set.univ_pi_fintype MeasurableSet.univ_pi_fintype

end Measurable

section MeasurableOnFamily

variable {α : ι → Type _}

variable [∀ i, MeasurableSpace (α i)]

variable (α)

theorem measurable_eq_mp {i i' : ι} (h : i = i') : Measurable (congr_arg α h).mp := by
  cases h
  exact measurable_id
#align measurable_eq_mp measurable_eq_mp

theorem Measurable.eq_mp {β} [MeasurableSpace β] {i i' : ι} (h : i = i') {f : β → α i}
    (hf : Measurable f) : Measurable fun x => (congr_arg α h).mp (f x) :=
  (measurable_eq_mp α h).comp hf
#align measurable.eq_mp Measurable.eq_mp

variable {α}

theorem measurable_piCongrLeft (f : ι' ≃ ι) : Measurable (piCongrLeft α f) := by
  rw [measurable_pi_iff]
  intro i
  simp_rw [piCongrLeft_apply]
  apply Measurable.eq_mp α (f.apply_symm_apply i)
  exact measurable_pi_apply (f.symm i)
#align measurable_Pi_congr_left measurable_piCongrLeft

variable (α)
/-- Moving a dependent type along an equivalence of coordinates, as a measurable equivalence. -/
def MeasurableEquiv.piCongrLeft (f : ι' ≃ ι) : (∀ b, α (f b)) ≃ᵐ ∀ a, α a := by
  refine' { Equiv.piCongrLeft α f with .. }
  · exact measurable_piCongrLeft f
  simp only [invFun_as_coe, coe_fn_symm_mk]
  rw [measurable_pi_iff]
  exact fun i => measurable_pi_apply (f i)
#align measurable_equiv.Pi_congr_left MeasurableEquiv.piCongrLeft
variable {α}

theorem MeasurableEquiv.piCongrLeft_eq (f : ι' ≃ ι) :
  (MeasurableEquiv.piCongrLeft α f : _ → _) = f.piCongrLeft α := by rfl

/-- The measurable equivalence between the pi type over a sum type and a product of pi-types. -/
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

theorem Subsingleton.measurableSingletonClass {α} [MeasurableSpace α] [Subsingleton α] :
    MeasurableSingletonClass α := by
  refine' ⟨fun i => _⟩
  convert MeasurableSet.univ
  simp [Set.eq_univ_iff_forall]
#align measure_theory.subsingleton.measurable_singleton_class MeasureTheory.Subsingleton.measurableSingletonClass

-- theorem integral_prod_norm_pow_le {α} [measurable_space α] {μ : measure α} (s : finset ι)
--   {f : ι → α → ℝ} (h2f : ∀ i ∈ s, 0 ≤ f i) {p : ι → ℝ} (hp : ∑ i in s, p i = 1)
--   (h2p : ∀ i ∈ s, 0 ≤ p i)
--   (hf : ∀ i ∈ s, mem_ℒp (f i) (ennreal.of_real $ p i) μ) :
--   ∫ a, ∏ i in s, f i a ^ p i ∂μ ≤ ∏ i in s, (∫ a, f i a ∂μ) ^ p i :=
-- sorry
/-- A version of Hölder with multiple arguments -/
theorem lintegral_prod_norm_pow_le {α} [MeasurableSpace α] {μ : Measure α} (s : Finset ι)
    {f : ι → α → ℝ≥0∞} {p : ι → ℝ} (hp : ∑ i in s, p i = 1)
    (h2p : ∀ i ∈ s, 0 ≤ p i) :-- (hf : ∀ i ∈ s, mem_ℒp (f i) (p i) μ)
      ∫⁻ a, ∏ i in s, f i a ^ p i ∂μ ≤
      ∏ i in s, (∫⁻ a, f i a ∂μ) ^ p i :=
  sorry
#align measure_theory.lintegral_prod_norm_pow_le MeasureTheory.lintegral_prod_norm_pow_le

section Measure

variable {α : ι → Type _}
variable [∀ i, MeasurableSpace (α i)]
variable [Fintype ι] [Fintype ι']
variable {m : ∀ i, OuterMeasure (α i)}
variable [∀ i, MeasurableSpace (α i)] {μ : ∀ i, Measure (α i)}
variable [∀ i, SigmaFinite (μ i)]
variable (μ)

namespace Measure
/-- Some properties of `Measure.pi` -/
theorem pi_unique_left [Unique ι] :
    Measure.pi μ = map (MeasurableEquiv.piUnique α).symm (μ (default : ι)) := by
  refine pi_eq (fun s hs => ?_)
  rw [map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi_fintype hs), MeasurableEquiv.piUnique_symm_apply, uniqueElim_preimage]
  symm
  convert Finset.prod_singleton (β := ℝ≥0∞)
  rw [Finset.ext_iff, Unique.forall_iff]
  simp
#align measure_theory.measure.pi_unique_left MeasureTheory.Measure.pi_unique_left

open Sum

theorem pi_map_left (f : ι' ≃ ι) :
    map (MeasurableEquiv.piCongrLeft α f) (Measure.pi fun i' => μ (f i')) = Measure.pi μ := by
  refine' (pi_eq fun s _ => _).symm
  rw [MeasurableEquiv.map_apply, MeasurableEquiv.piCongrLeft_eq,
    piCongrLeft_preimage_univ_pi, pi_pi _ _, prod_univ_comp_equiv (fun i => μ i (s i)) f]
#align measure_theory.measure.pi_map_left MeasureTheory.Measure.pi_map_left

theorem pi_sum {π : ι ⊕ ι' → Type _} [∀ i, MeasurableSpace (π i)] (μ : ∀ i, Measure (π i))
    [∀ i, SigmaFinite (μ i)] :
    map (MeasurableEquiv.piSum π)
      ((Measure.pi fun i => μ (.inl i)).prod (Measure.pi fun i => μ (.inr i))) = Measure.pi μ := by
  refine' (pi_eq fun s _ => _).symm
  simp_rw [MeasurableEquiv.map_apply, MeasurableEquiv.piSum_eq, piSum_preimage_univ_pi,
    Measure.prod_prod, Measure.pi_pi, prod_sum_univ]
#align measure_theory.measure.pi_sum MeasureTheory.Measure.pi_sum

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
-- the next lemmas are currently unused

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

end Measure

section

variable {α E : Type _} [MeasurableSpace α] [NormedAddCommGroup E]

theorem _root_.Measurable.hasFiniteIntegral_dirac {f : α → E}
    (hf : Measurable (fun x => ‖f x‖₊ : α → ℝ≥0∞)) {x : α} :
    HasFiniteIntegral f (Measure.dirac x) := by
  rw [HasFiniteIntegral, lintegral_dirac' _ hf]
  exact ENNReal.coe_lt_top
#align measure_theory.measurable.has_finite_integral_dirac Measurable.hasFiniteIntegral_dirac

theorem hasFiniteIntegral_dirac [MeasurableSingletonClass α] {f : α → E} {x : α} :
    HasFiniteIntegral f (Measure.dirac x) := by
  rw [HasFiniteIntegral, lintegral_dirac]
  exact ENNReal.coe_lt_top
#align measure_theory.has_finite_integral_dirac MeasureTheory.hasFiniteIntegral_dirac

theorem StronglyMeasurable.integrable_dirac [MeasurableSpace E] [BorelSpace E] {f : α → E}
    (hf : StronglyMeasurable f) {x : α} : Integrable f (Measure.dirac x) :=
  ⟨hf.aestronglyMeasurable, hf.measurable.ennnorm.hasFiniteIntegral_dirac⟩
#align measure_theory.strongly_measurable.integrable_dirac MeasureTheory.StronglyMeasurable.integrable_dirac

end

section Marginal

open Finset TopologicalSpace

variable {δ : Type _} {π : δ → Type _} [∀ x, MeasurableSpace (π x)]

variable {μ : ∀ i, Measure (π i)} [∀ i, SigmaFinite (μ i)]

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E]

-- improper version of FTC, maybe works just under condition of the integral existing??
-- similar lemmas in `IntegralEqImproper`
theorem _root_.HasCompactSupport.integral_deriv_eq {f : ℝ → E} (hf : ContDiff ℝ 1 f)
    (h2f : HasCompactSupport f) (b : ℝ) : ∫ x in Set.Iic b, deriv f x = f b := by sorry

theorem lintegral_of_isEmpty {α} [MeasurableSpace α] [IsEmpty α] (μ : Measure α) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = 0 := by convert lintegral_zero_measure f
#align measure_theory.lintegral_of_is_empty MeasureTheory.lintegral_of_isEmpty

-- lemma _root_.has_compact_support.lintegral_deriv_eq {f : ℝ → ℝ} (hf : cont_diff ℝ 1 f)
--   (h2f : has_compact_support f) (b : ℝ) :
--   ennreal.to_real ∫⁻ x in set.Iic b, ennreal.of_real (deriv f x) = f b :=
-- begin
--   sorry
-- end
-- lemma _root_.has_compact_support.norm_lintegral_deriv_eq {f : ℝ → ℝ} (hf : cont_diff ℝ 1 f)
--   (h2f : has_compact_support f) (h3f : 0 ≤ f) (b : ℝ) :
--   (‖ ennreal.to_real ∫⁻ x in set.Iic b, ennreal.of_real (deriv f x)‖₊ : ℝ≥0∞) =
--   ennreal.of_real (f b) :=
-- by rw [h2f.lintegral_deriv_eq hf, ← of_real_norm_eq_coe_nnnorm, real.norm_of_nonneg (h3f b)]
variable {s t : Finset δ} {f g : (∀ i, π i) → ℝ≥0∞} {x y : ∀ i, π i} {i : δ}

/-- `update' s f x` is the function `f` restricted to the subspace containing only
  the coordinates in `s`, where the coordinates outside of `s` are chosen using the default value
  `x`. This is the integrand of the `marginal` function below.
  Another view: `fun x => update' s f x y` is the function `f` where the coordinates in `s`
  are updated to `y`. -/
def update' (s : Finset δ) (f : (∀ i, π i) → ℝ≥0∞) (x : ∀ i, π i) : (∀ i : s, π i) → ℝ≥0∞ :=
  fun y => f fun i => if hi : i ∈ s then y ⟨i, hi⟩ else x i
#align measure_theory.update' MeasureTheory.update'

theorem update'_empty {y} : update' ∅ f x y = f x :=
  rfl
#align measure_theory.update'_empty MeasureTheory.update'_empty

theorem measurable_update_aux :
    Measurable (fun y i => if hi : i ∈ s then y ⟨i, hi⟩ else x i : (∀ i : s, π i) → ∀ i, π i) := by
  rw [measurable_pi_iff]; intro i
  by_cases h : i ∈ s
  · simp [h, measurable_pi_apply]
  · simp [h]
#align measure_theory.measurable_update_aux MeasureTheory.measurable_update_aux

/-- The integrand of `∫⋯∫_s, f ∂μ` is measurable if `f` is. -/
theorem Measurable.update' (hf : Measurable f) {s : Finset δ} {x : ∀ i, π i} :
    Measurable (update' s f x) :=
  hf.comp measurable_update_aux
#align measurable.update' MeasureTheory.Measurable.update'

/-- The integrand of `∫⋯∫_s, f ∂μ` is measurable if `f` is. -/
theorem StronglyMeasurable.update' (hf : StronglyMeasurable f) {s : Finset δ}
    {x : ∀ i, π i} : StronglyMeasurable (update' s f x) :=
  hf.comp_measurable measurable_update_aux
#align measure_theory.strongly_measurable.update' MeasureTheory.StronglyMeasurable.update'

/-- Integrate `f(x₁,…,xₙ)` over all variables `xᵢ` where `i ∈ s`. Return a function in the
  remaining variables (it will be constant in the `xᵢ` for `i ∈ s`).
  This is the marginal distribution of all variables not in `s`. -/
def marginal (μ : ∀ i, Measure (π i)) (s : Finset δ) (f : (∀ i, π i) → ℝ≥0∞) (x : ∀ i, π i) :
    ℝ≥0∞ :=
  ∫⁻ y : ∀ i : s, π i, update' s f x y ∂Measure.pi fun i : s => μ i
#align measure_theory.marginal MeasureTheory.marginal

notation "∫⋯∫_"
  -- Note: this notation is not a binder. This is more convenient since it returns a function.
s ", " f " ∂" μ:70 => marginal μ s f

notation "∫⋯∫_" s ", " f => marginal volume s f

variable (μ)

theorem _root_.Measurable.marginal (hf : Measurable f) : Measurable (∫⋯∫_s, f ∂μ) := by
  refine' Measurable.lintegral_prod_right _
  refine' hf.comp _
  rw [measurable_pi_iff]; intro i
  by_cases h : i ∈ s
  · simp [h]
    refine measurable_pi_iff.1 measurable_snd _
  · simp [h]
    refine measurable_pi_iff.1 measurable_fst _
#align measurable.marginal Measurable.marginal

theorem marginal_empty (f : (∀ i, π i) → ℝ≥0∞) : ∫⋯∫_∅, f ∂μ = f := by
  ext1 x
  simp_rw [marginal, Measure.pi_of_empty fun i : (∅ : Finset δ) => μ i]
  apply lintegral_dirac'
  exact Subsingleton.measurable
#align measure_theory.marginal_empty MeasureTheory.marginal_empty

/-- The marginal distribution is independent of the variables in `s`. -/
-- todo: ∀ i ∉ s, ...
theorem marginal_eq {x y : ∀ i, π i} (f : (∀ i, π i) → ℝ≥0∞) (h : ∀ (i) (_ : i ∉ s), x i = y i) :
    (∫⋯∫_s, f ∂μ) x = (∫⋯∫_s, f ∂μ) y := by dsimp [marginal, update']; rcongr; exact h _ ‹_›
#align measure_theory.marginal_eq MeasureTheory.marginal_eq

theorem marginal_update (x : ∀ i, π i) (f : (∀ i, π i) → ℝ≥0∞) {i : δ} (y : π i) (hi : i ∈ s) :
    (∫⋯∫_s, f ∂μ) (Function.update x i y) = (∫⋯∫_s, f ∂μ) x := by
  refine' marginal_eq μ f fun j hj => _
  have : j ≠ i := by rintro rfl; exact hj hi
  apply update_noteq this
#align measure_theory.marginal_update MeasureTheory.marginal_update

theorem marginal_union (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) (hst : Disjoint s t) :
    ∫⋯∫_s ∪ t, f ∂μ = ∫⋯∫_s, ∫⋯∫_t, f ∂μ ∂μ := by
  ext1 x
  simp_rw [marginal, update', ← Measure.pi_map_left _ (finsetUnionEquivSum s t hst).symm]
  rw [lintegral_map_equiv, ← Measure.pi_sum, lintegral_map_equiv, lintegral_prod]
  · dsimp only [finsetUnionEquivSum_symm_inl, finsetUnionEquivSum_symm_inr, Subtype.coe_mk]
    congr 1; ext1 x; congr 1; ext1 y; congr 1; ext1 i
    by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;>
      simp only [his, hit, dif_pos, dif_neg, Finset.mem_union, true_or_iff, false_or_iff,
        not_false_iff]
    · exfalso; exact Finset.disjoint_left.mp hst his hit
    -- this is ugly, but applying lemmas basically doesn't work because of dependent types
    · change
        piCongrLeft (fun b : ↥(s ∪ t) => π ↑b) (finsetUnionEquivSum s t hst).symm
            (piSum (fun i : s ⊕ t => π ↑((finsetUnionEquivSum s t hst).symm i)) (x, y))
            ((finsetUnionEquivSum s t hst).symm <| Sum.inl ⟨i, his⟩) =
          x ⟨i, his⟩
      rw [piCongrLeft_sum_inl]
    · change
        piCongrLeft (fun b : ↥(s ∪ t) => π ↑b) (finsetUnionEquivSum s t hst).symm
            (piSum (fun i : s ⊕ t => π ↑((finsetUnionEquivSum s t hst).symm i)) (x, y))
            ((finsetUnionEquivSum s t hst).symm <| Sum.inr ⟨i, hit⟩) =
          y ⟨i, hit⟩
      rw [piCongrLeft_sum_inr]
  · set e₁ := (finsetUnionEquivSum s t hst).symm
    set e₂ := MeasurableEquiv.piCongrLeft (fun i : { x // x ∈ s ∪ t } => π i) e₁
    set e₃ := MeasurableEquiv.piSum fun b ↦ π (e₁ b)
    apply Measurable.aemeasurable
    refine hf.comp ?_
    rw [measurable_pi_iff]; intro i
    by_cases h : i ∈ s ∨ i ∈ t
    · simp [h, measurable_pi_apply]
      refine measurable_pi_iff.1 ?_ _
      refine' e₂.measurable.comp e₃.measurable
    · simp [h]
#align measure_theory.marginal_union MeasureTheory.marginal_union

theorem marginal_union' (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {s t : Finset δ}
    (hst : Disjoint s t) : ∫⋯∫_s ∪ t, f ∂μ = ∫⋯∫_t, ∫⋯∫_s, f ∂μ ∂μ := by
  rw [Finset.union_comm, marginal_union μ f hf hst.symm]
#align measure_theory.marginal_union' MeasureTheory.marginal_union'

variable {μ}

theorem marginal_singleton (f : (∀ i, π i) → ℝ≥0∞) (i : δ) :
    ∫⋯∫_{i}, f ∂μ = fun x => ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i := by
  letI : Unique ({i} : Finset δ) :=
    ⟨⟨⟨i, mem_singleton_self i⟩⟩, fun j => Subtype.ext <| mem_singleton.mp j.2⟩
  ext1 x
  simp_rw [marginal, update', Measure.pi_unique_left _]
  rw [lintegral_map_equiv]
  congr with y; congr with j
  by_cases hj : j = i
  · cases hj.symm; simp only [dif_pos, Finset.mem_singleton, update_same]
    exact @uniqueElim_default _ (fun i : (({i} : Finset δ) : Set δ) => π i) _ y
  · simp [hj]
#align measure_theory.marginal_singleton MeasureTheory.marginal_singleton

theorem integral_update (f : (∀ i, π i) → ℝ≥0∞) (i : δ) (x : ∀ i, π i) :
    ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i = (∫⋯∫_{i}, f ∂μ) x := by
  simp_rw [marginal_singleton f i]
#align measure_theory.integral_update MeasureTheory.integral_update

-- lemma marginal_insert (f : (Π i, π i) → ℝ≥0∞) (hf : measurable f) {i : δ}
--   (hi : i ∉ s) :
--   ∫⋯∫_ insert i s, f ∂μ = λ x, ∫ xᵢ, (∫⋯∫_ s, λ x, f (function.update x i xᵢ) ∂μ) x ∂(μ i) :=
-- begin
--   ext x,
--   rw [insert_eq, marginal_union, marginal_singleton],
--   dsimp only,
-- end
theorem marginal_insert_rev (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {i : δ} (hi : i ∉ s)
    (x : ∀ i, π i) :
    ∫⁻ xᵢ, (∫⋯∫_s, f ∂μ) (Function.update x i xᵢ) ∂μ i = (∫⋯∫_insert i s, f ∂μ) x := by
  rw [Finset.insert_eq, marginal_union μ f hf (Finset.disjoint_singleton_left.mpr hi),
    marginal_singleton]
#align measure_theory.marginal_insert_rev MeasureTheory.marginal_insert_rev

open Filter

@[gcongr]
theorem marginal_mono {f g : (∀ i, π i) → ℝ≥0∞} (hfg : f ≤ g) : ∫⋯∫_s, f ∂μ ≤ ∫⋯∫_s, g ∂μ :=
  fun _ => lintegral_mono fun _ => hfg _
#align measure_theory.marginal_mono MeasureTheory.marginal_mono

theorem marginal_univ [Fintype δ] {f : (∀ i, π i) → ℝ≥0∞} :
    ∫⋯∫_univ, f ∂μ = fun _ => ∫⁻ x, f x ∂Measure.pi μ := by
  let e : { j // j ∈ Finset.univ } ≃ δ := Equiv.subtypeUnivEquiv mem_univ
  ext1 x
  simp_rw [marginal, update', ← Measure.pi_map_left μ e]
  rw [lintegral_map_equiv]
  congr with y
  congr with i
  simp
  rfl
#align measure_theory.marginal_univ MeasureTheory.marginal_univ

end Marginal

end MeasureTheory

open MeasureTheory

section Sobolev

open TopologicalSpace

variable [Fintype ι] {π : ι → Type _} [∀ i, MeasurableSpace (π i)] (μ : ∀ i, Measure (π i))
  [∀ i, SigmaFinite (μ i)] (u : (ι → ℝ) → ℝ) {f : (∀ i, π i) → ℝ≥0∞}


local prefix:max "#" => Fintype.card

/--
  The function that is central in the inductive proof of the Sobolev inequality.
-/
def rhsAux (f : (∀ i, π i) → ℝ≥0∞) (s : Finset ι) : (∀ i, π i) → ℝ≥0∞ :=
  (∫⋯∫_s, f ∂μ) ^ ((s.card : ℝ) / (#ι - 1 : ℝ)) *
    ∏ i in sᶜ, (∫⋯∫_insert i s, f ∂μ) ^ ((1 : ℝ) / (#ι - 1 : ℝ))
#align rhs_aux rhsAux

theorem marginal_singleton_rhsAux_le [Nontrivial ι] (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f)
  (s : Finset ι) (i : ι) (hi : i ∉ s) : ∫⋯∫_{i}, rhsAux μ f s ∂μ ≤ rhsAux μ f (insert i s) := by
  simp_rw [rhsAux, ← insert_compl_insert hi]
  rw [prod_insert (not_mem_compl.mpr <| mem_insert_self i s)]
  rw [mul_left_comm, mul_prod_eq_prod_insertNone]
  simp_rw [marginal_singleton]
  simp_rw [Pi.mul_apply, Pi.pow_apply, fun x xᵢ => marginal_update μ x f xᵢ (s.mem_insert_self i)]
  intro x
  dsimp only
  have h2i : i ∈ sᶜ := Finset.mem_compl.mpr hi
  have hι : 1 < (#ι : ℝ) := Nat.one_lt_cast.mpr Fintype.one_lt_card
  have h2ι : 0 ≤ (#ι : ℝ) - 1 := by linarith
  rw [lintegral_const_mul]
  simp_rw [prod_apply, Option.elim'_comp₂ (· ^ ·), Pi.pow_apply]
  refine' (ENNReal.mul_left_mono (lintegral_prod_norm_pow_le _ _ _)).trans_eq _
  · simp_rw [sum_insertNone, compl_insert, not_not, Option.elim, sum_const, nsmul_eq_mul]
    rw [Finset.cast_card_erase_of_mem h2i, mul_one_div, ← add_div, ← add_sub_assoc,
      ← Nat.cast_add, card_add_card_compl, div_self]
    · rw [sub_ne_zero, Nat.cast_ne_one]
      exact Fintype.one_lt_card.ne'
  · rintro (_|i) -
    · exact div_nonneg (by simp) h2ι
    · simp_rw [Option.elim, one_div_nonneg, h2ι]
  simp_rw [prod_insertNone]
  dsimp
  rw [marginal_insert_rev _ hf hi, ← mul_assoc]
  congr
  · rw [← ENNReal.rpow_add_of_nonneg, ← add_div, Finset.card_insert_of_not_mem hi, Nat.cast_add,
      Nat.cast_one, add_comm]
    · simp_rw [one_div_nonneg, h2ι]
    · exact div_nonneg (by simp) h2ι
  simp_rw [prod_apply, Pi.pow_apply]
  refine' prod_congr rfl fun j hj => _
  have h2 : i ∉ insert j s := by
    have : i ≠ j
    · simp [-ne_eq] at hj
      exact hj.1.symm
    simp [this, not_or, hi]
  rw [Insert.comm, marginal_insert_rev _ hf h2]
  · simp
    refine (hf.marginal μ).comp (measurable_update x) |>.pow measurable_const |>.mul ?_
    refine Finset.measurable_prod _ fun i _ ↦ ?_
    exact (hf.marginal μ).comp (measurable_update x) |>.pow measurable_const
#align marginal_rhs_aux_le marginal_singleton_rhsAux_le

lemma Measurable.rhsAux (hf : Measurable f) : Measurable (rhsAux μ f s) := by
  sorry --refine (_ : Measurable _) |>.pow measurable_const |>.mul ?_

theorem marginal_rhsAux_empty_le [Nontrivial ι] (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f)
    (s : Finset ι) : ∫⋯∫_s, rhsAux μ f ∅ ∂μ ≤ rhsAux μ f s := by
  induction' s using Finset.induction with i s hi ih
  · rw [marginal_empty]
  · have hi' : Disjoint {i} s := Finset.disjoint_singleton_left.mpr hi
    conv_lhs => rw [Finset.insert_eq, marginal_union μ _ sorry hi']
    refine' (marginal_mono ih).trans _
    exact marginal_singleton_rhsAux_le μ f hf s i hi
#align marginal_rhs_aux_empty_le marginal_rhsAux_empty_le

theorem lintegral_prod_lintegral_pow_le [Nontrivial ι] (hf : Measurable f) :
    ∫⁻ x, ∏ i, (∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ^ ((1 : ℝ) / (#ι - 1 : ℝ)) ∂Measure.pi μ ≤
      (∫⁻ x, f x ∂Measure.pi μ) ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) := by
  cases isEmpty_or_nonempty (∀ i, π i)
  · simp_rw [lintegral_of_isEmpty]; refine' zero_le _
  inhabit ∀ i, π i
  have := marginal_rhsAux_empty_le μ f hf Finset.univ default
  simp_rw [rhsAux, marginal_univ, Finset.compl_univ, Finset.prod_empty, marginal_empty,
    Finset.card_empty, Nat.cast_zero, zero_div, Finset.compl_empty, mul_one, Pi.mul_def,
    Pi.pow_apply, ENNReal.rpow_zero, one_mul, Finset.prod_fn, Pi.pow_apply, insert_emptyc_eq,
    marginal_singleton f] at this
  exact this
#align lintegral_prod_lintegral_pow_le lintegral_prod_lintegral_pow_le

-- theorem integral_prod_integral_pow_le {f : (∀ i, π i) → ℝ} (hf : Measurable f)
--     (h2f : ∀ x, 0 ≤ f x) :
--     ∫ x,
--         ∏ i,
--           (∫ xᵢ, f (Function.update x i xᵢ) ∂μ i) ^ ((1 : ℝ) / (#ι - 1)) ∂Measure.pi μ ≤
--       (∫ x, f x ∂Measure.pi μ) ^ ((#ι : ℝ) / (#ι - 1)) :=
--   by sorry
-- #align integral_prod_integral_pow_le integral_prod_integral_pow_le

attribute [gcongr] ENNReal.rpow_le_rpow

section

-- move to MeasureTheory.Function.L1Space
theorem _root_.MeasureTheory.Integrable.nnnorm_toL1 {α : Type _} {β : Type _}
    {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β] (f : α → β)
    (hf : Integrable f μ) :
    (‖hf.toL1 f‖₊ : ℝ≥0∞) = ∫⁻ a, ‖f a‖₊ ∂μ := by
  simpa [Integrable.toL1, snorm, snorm'] using ENNReal.coe_toNNReal hf.2.ne

-- move to MeasureTheory.Integral.Bochner
theorem _root_.MeasureTheory.L1.nnnorm_Integral_le_one {α : Type _} {E : Type _}
    [NormedAddCommGroup E] {_ : MeasurableSpace α} {μ : Measure α} [NormedSpace ℝ E]
    [CompleteSpace E] : ‖L1.integralCLM (α := α) (E := E) (μ := μ)‖₊ ≤ (1 : ℝ) :=
  L1.norm_Integral_le_one

-- move to MeasureTheory.Integral.Bochner
theorem _root_.MeasureTheory.L1.nnnorm_integral_le {α : Type _} {E : Type _}
    [NormedAddCommGroup E] {_ : MeasurableSpace α} {μ : Measure α} [NormedSpace ℝ E]
    [CompleteSpace E] (f : α →₁[μ] E) : ‖L1.integral f‖₊ ≤ ‖f‖₊ :=
  L1.norm_integral_le f

end

-- move to MeasureTheory.Integral.Bochner
theorem nnnorm_integral_le_lintegral_nnnorm {α E : Type _} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : α → E) :
    ‖∫ x, f x ∂μ‖₊ ≤ ∫⁻ x, ‖f x‖₊ ∂ μ := by
  rw [integral_def, dif_pos ‹_›]
  split_ifs with hf
  · calc _ ≤ (‖(Integrable.toL1 f hf)‖₊ : ℝ≥0∞) := by norm_cast; apply L1.nnnorm_integral_le
      _ = _ := hf.nnnorm_toL1
  · simp

/-- The Sobolev inequality -/
theorem lintegral_pow_le [Nontrivial ι] [Fintype ι] (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u) :
    ∫⁻ x, ‖u x‖₊ ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) ≤
      (∫⁻ x, ‖fderiv ℝ u x‖₊) ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) := by
  have hu' : Measurable (fun x ↦ (‖fderiv ℝ u x‖₊ : ℝ≥0∞))
  · borelize ((ι → ℝ) →L[ℝ] ℝ)
    have : Measurable (fun x ↦ fderiv ℝ u x) := (hu.continuous_fderiv (le_refl _)).measurable
    measurability
  refine' le_trans _ (lintegral_prod_lintegral_pow_le (fun _ => volume) hu')
  have hι₀ : 1 < #ι := Fintype.one_lt_card
  have hι₁ : (2:ℝ) ≤ #ι := by exact_mod_cast hι₀
  have hι₂ : (1:ℝ) ≤ ↑#ι - 1 := by linarith
  have hι₃ : 0 ≤ (#ι : ℝ) / (#ι - 1 : ℝ) := by positivity
  refine' lintegral_mono fun x => _ -- should be `gcongr`
  dsimp only
  rw [← ENNReal.coe_rpow_of_nonneg _ hι₃]
  simp_rw [div_eq_mul_inv, one_mul, ENNReal.rpow_mul, ENNReal.prod_rpow]
  gcongr
  rw [← card_univ]
  norm_cast
  rw [← prod_const]
  push_cast
  gcongr with i _
  -- `update x i` is `ContDiff` -- make this a lemma
  have h_update : ContDiff ℝ 1 (update x i)
  · rw [contDiff_pi]
    intro j
    simp_rw [update_apply]
    split_ifs
    · exact contDiff_id
    · exact contDiff_const
  have h3u : ContDiff ℝ 1 (u ∘ update x i) := hu.comp h_update
  have h4u : HasCompactSupport (u ∘ update x i)
  · apply h2u.comp_closedEmbedding
    -- `update x i` is a closed embedding -- make this a lemma
    have h5u : LeftInverse (fun v ↦ v i) (update x i) := fun t ↦ update_same i t x
    apply h5u.closedEmbedding
    · exact continuous_apply i
    · have : Continuous (fun t : ℝ ↦ (x, t)) := continuous_const.prod_mk continuous_id
      exact (continuous_update i).comp this
  have := h4u.integral_deriv_eq h3u (x i)
  dsimp only [comp_def, comp_apply] at this
  simp_rw [update_eq_self] at this
  rw [← this]
  refine' (nnnorm_integral_le_lintegral_nnnorm _).trans _
  refine (lintegral_mono' (Measure.restrict_le_self) (le_refl _)).trans ?_
  refine' lintegral_mono fun y => _
  rw [← Function.comp_def u (update x i), deriv]
  rw [fderiv.comp y (hu.differentiable le_rfl).differentiableAt ((h_update.differentiable (le_refl _)) y)]
  rw [ContinuousLinearMap.comp_apply]
  norm_cast
  show ‖_‖ ≤ ‖_‖
  refine' (ContinuousLinearMap.le_op_norm _ _).trans _
  conv_rhs => rw [← mul_one ‖_‖]
  simp_rw [fderiv_update]
  gcongr
  refine' (ContinuousLinearMap.le_op_norm _ _).trans_eq _
  rw [norm_one, mul_one]
  exact ContinuousLinearMap.norm_pi_update_eq_one fun _ => ℝ
#align lintegral_pow_le lintegral_pow_le

-- /-- The Sobolev inequality for the Lebesgue l=integral(?) -/
-- theorem lintegral_pow_le :
--     ∫⁻ x, ‖u x‖₊ ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) ≤
--       (∫⁻ x, ‖fderiv ℝ u x‖₊) ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) :=
--   by sorry
-- #align lintegral_pow_le lintegral_pow_le

end Sobolev
