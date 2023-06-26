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
import Mathlib.Analysis.Calculus.ContDiff

/-!
# Marginals of multivariate functions
-/


noncomputable section

open scoped Classical BigOperators Topology ENNReal

variable {ι ι' ι'' : Type _}

section Finset

open Finset

namespace Real

theorem prod_rpow {ι} (s : Finset ι) {f : ι → ℝ} (hf : 0 ≤ f) (r : ℝ) :
    ∏ i in s, f i ^ r = (∏ i in s, f i) ^ r :=
  sorry
#align real.prod_rpow Real.prod_rpow

end Real

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

@[simp] theorem Function.comp_def (f : β → γ) (g : α → β) : f ∘ g = fun x => f (g x) := rfl

end Function

-- by rw [prod_comp_equiv f g, g.finset_image_univ_eq_univ]
namespace Finset

theorem insert_compl_insert [Fintype ι] {s : Finset ι} {i : ι} (hi : i ∉ s) :
    insert i (insert i sᶜ) = sᶜ := by
  simp_rw [@eq_compl_comm _ _ s, compl_insert, compl_erase, compl_compl, erase_insert hi]
#align finset.insert_compl_insert Finset.insert_compl_insert

@[to_additive (attr := simp)]
theorem mul_prod_eq_prod_insertNone {α} {M} [CommMonoid M] (f : α → M) (x : M) (s : Finset α) :
    x * ∏ i in s, f i = ∏ i in insertNone s, i.elim x f :=
  (prod_insertNone (fun i => i.elim x f) _).symm
#align finset.mul_prod_eq_prod_insert_none Finset.mul_prod_eq_prod_insertNone
#align finset.add_sum_eq_sum_insert_none Finset.add_sum_eq_sum_insertNone

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
theorem imp_and_neg_imp_iff (p q : Prop) [Decidable p] : (p → q) ∧ (¬p → q) ↔ q := by
  simp_rw [imp_iff_or_not, Classical.not_not, ← or_and_left, not_and_self_iff, or_false_iff]
#align imp_and_neg_imp_iff imp_and_neg_imp_iff

@[simp]
theorem cast_sum_rec {α β : Type _} {P : Sum α β → Sort _} (f : ∀ i, P (inl i)) (g : ∀ j, P (inr j))
    (x y : Sum α β) (h : x = y) :
    cast (congr_arg P h) (@Sum.rec _ _ _ f g x) = @Sum.rec _ _ _ f g y := by cases h; rfl
#align cast_sum_rec cast_sum_rec

@[simp]
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
    ((f.piCongrLeft α).symm ⁻¹' (f ⁻¹' s).pi fun i' => t <| f i') = s.pi t :=
  by
  ext; simp_rw [mem_preimage, Set.mem_pi, piCongrLeft_symm_apply]
  convert f.forall_congr_left; rfl
#align equiv.Pi_congr_left_symm_preimage_pi Equiv.piCongrLeft_symm_preimage_pi

theorem piCongrLeft_preimage_univ_pi (f : ι' ≃ ι) (t : ∀ i, Set (α i)) :
    f.piCongrLeft α ⁻¹' pi univ t = pi univ fun i => t (f i) :=
  by
  apply Set.ext; rw [← (f.piCongrLeft α).symm.forall_congr_left]
  intro x; simp only [mem_univ_pi, mem_preimage, apply_symm_apply, piCongrLeft_symm_apply]
  exact f.forall_congr_left.symm
#align equiv.Pi_congr_left_preimage_univ_pi Equiv.piCongrLeft_preimage_univ_pi

open Sum

/-- The type of dependent functions on a sum type `ι ⊕ ι'` is equivalent to the type of pairs of
  functions on `ι` and on `ι'`. This is a dependent version of `equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps]
def piSum (π : Sum ι ι' → Type _) : ((∀ i, π (inl i)) × ∀ i', π (inr i')) ≃ ∀ i, π i
    where
  toFun f := Sum.rec f.1 f.2
  invFun g := ⟨fun i => g (inl i), fun i' => g (inr i')⟩
  left_inv f := Prod.ext rfl rfl
  right_inv g := by ext (i | i) <;> rfl
#align equiv.Pi_sum Equiv.piSum

def piSum' (π : ι → Type _) (π' : ι' → Type _) :
    ((∀ i, π i) × ∀ i', π' i') ≃ ∀ i, Sum.elim π π' i :=
  Equiv.piSum (Sum.elim π π')
#align equiv.Pi_sum' Equiv.piSum'

theorem Set.union_apply_left' {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅)
    {a : α} (ha : a ∈ s) : Equiv.Set.union H ⟨a, Set.mem_union_left _ ha⟩ = Sum.inl ⟨a, ha⟩ :=
  dif_pos ha
#align equiv.set.union_apply_left' Equiv.Set.union_apply_left'

theorem Set.union_apply_right' {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅)
    {a : α} (ha : a ∈ t) : Equiv.Set.union H ⟨a, Set.mem_union_right _ ha⟩ = Sum.inr ⟨a, ha⟩ :=
  dif_neg fun h => H ⟨h, ha⟩
#align equiv.set.union_apply_right' Equiv.Set.union_apply_right'

theorem sum_rec_congr (P : Sum ι ι' → Sort _) (f : ∀ i, P (inl i)) (g : ∀ i, P (inr i))
    {x y : Sum ι ι'} (h : x = y) :
    @Sum.rec _ _ _ f g x = cast (congr_arg P h.symm) (@Sum.rec _ _ _ f g y) := by cases h; rfl
#align equiv.sum_rec_congr Equiv.sum_rec_congr

theorem piCongrLeft_sum_inl (π : ι'' → Type _) (e : Sum ι ι' ≃ ι'') (f : ∀ i, π (e (inl i)))
    (g : ∀ i, π (e (inr i))) (i : ι) :
    piCongrLeft π e (piSum (fun x => π (e x)) (f, g)) (e (inl i)) = f i := by
  simp_rw [piCongrLeft_apply, piSum_apply, sum_rec_congr _ _ _ (e.symm_apply_apply (inl i)),
    cast_cast, cast_eq]
#align equiv.Pi_congr_left_sum_inl Equiv.piCongrLeft_sum_inl

theorem piCongrLeft_sum_inr (π : ι'' → Type _) (e : Sum ι ι' ≃ ι'') (f : ∀ i, π (e (inl i)))
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

def finsetUnionEquivSum {α} (s t : Finset α) (h : Disjoint s t) : (s ∪ t : Finset α) ≃ Sum s t :=
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

@[simp]
theorem finsetUnionEquivSum_left {α} {s t : Finset α} (h : Disjoint s t) (x : (s ∪ t : Finset α))
    (hx : ↑x ∈ s) :
    finsetUnionEquivSum s t h x = Sum.inl ⟨x, hx⟩ :=
  sorry
#align finset_union_equiv_sum_left finsetUnionEquivSum_left

-- equiv.set.union_apply_left _ $ finset.mem_coe.mp hx
@[simp]
theorem finsetUnionEquivSum_right {α} {s t : Finset α} (h : Disjoint s t) (x : (s ∪ t : Finset α))
    (hx : ↑x ∈ t) : finsetUnionEquivSum s t h x = Sum.inr ⟨x, hx⟩ :=
  sorry
#align finset_union_equiv_sum_right finsetUnionEquivSum_right

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

theorem MeasurableEquiv.piCongrLeft (f : ι' ≃ ι) : (∀ b, α (f b)) ≃ᵐ ∀ a, α a := by
  refine' { Equiv.piCongrLeft α f with .. }
  exact measurable_piCongrLeft f
  simp only [invFun_as_coe, coe_fn_symm_mk]
  rw [measurable_pi_iff]
  exact fun i => measurable_pi_apply (f i)
#align measurable_equiv.Pi_congr_left MeasurableEquiv.piCongrLeft

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

namespace Measure

variable {α : ι → Type _}

variable [∀ i, MeasurableSpace (α i)]

variable [Fintype ι] [Fintype ι']

variable {m : ∀ i, OuterMeasure (α i)}

variable [∀ i, MeasurableSpace (α i)] {μ : ∀ i, Measure (α i)}

variable [∀ i, SigmaFinite (μ i)]

variable (μ)

/-- Some properties of `Measure.pi` -/
theorem pi_unique_left [Unique ι] : Measure.pi μ = map uniqueElim (μ (default : ι)) := by
  apply pi_eq
  intro s hs
  rw [map_apply measurable_uniqueElim (MeasurableSet.univ_pi_fintype hs), uniqueElim_preimage]
  symm
  convert Finset.prod_singleton (β := ℝ≥0∞)
  rw [Finset.ext_iff, Unique.forall_iff]
  simp
#align measure_theory.measure.pi_unique_left MeasureTheory.Measure.pi_unique_left

open Sum

theorem pi_map_left (f : ι' ≃ ι) :
    map (f.piCongrLeft α) (Measure.pi fun i' => μ (f i')) = Measure.pi μ := by
  refine' (pi_eq _).symm; intro s hs
  rw [map_apply _ (MeasurableSet.univ_pi_fintype hs)]
  · simp_rw [piCongrLeft_preimage_univ_pi, pi_pi _ _, prod_univ_comp_equiv (fun i => μ i (s i)) f]
  · apply measurable_piCongrLeft
#align measure_theory.measure.pi_map_left MeasureTheory.Measure.pi_map_left

theorem pi_sum {π : Sum ι ι' → Type _} [∀ i, MeasurableSpace (π i)] (μ : ∀ i, Measure (π i))
    [∀ i, SigmaFinite (μ i)] :
    map (Equiv.piSum π)
        ((Measure.pi fun i => μ (Sum.inl i)).prod (Measure.pi fun i => μ (Sum.inr i))) =
      Measure.pi μ := by
  refine' (pi_eq fun s hs => _).symm
  rw [map_apply]
  all_goals sorry
#align measure_theory.measure.pi_sum MeasureTheory.Measure.pi_sum

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

theorem _root_.HasCompactSupport.integral_deriv_eq {f : ℝ → E} (hf : ContDiff ℝ 1 f)
    (h2f : HasCompactSupport f) (b : ℝ) : ∫ x in Set.Iic b, deriv f x = f b := by sorry
#align has_compact_support.integral_deriv_eq HasCompactSupport.integral_deriv_eq

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

/-- The integrand of `marginal _ _ f` is measurable if `f` is. -/
theorem Measurable.update' (hf : Measurable f) {s : Finset δ} {x : ∀ i, π i} :
    Measurable (update' s f x) :=
  hf.comp measurable_update_aux
#align measurable.update' MeasureTheory.Measurable.update'

/-- The integrand of `marginal _ _ f` is measurable if `f` is. -/
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

theorem _root_.Measurable.marginal (hf : Measurable f) : Measurable (∫⋯∫_s, f ∂μ) := by
  refine' Measurable.lintegral_prod_right _
  sorry
#align measurable.marginal Measurable.marginal

theorem marginal_empty (f : (∀ i, π i) → ℝ≥0∞) : ∫⋯∫_∅, f ∂μ = f := by
  ext1 x
  simp_rw [marginal, Measure.pi_of_empty fun i : (∅ : Finset δ) => μ i]
  apply lintegral_dirac'
  exact Subsingleton.measurable
#align measure_theory.marginal_empty MeasureTheory.marginal_empty

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (i «expr ∉ » s) -/
/-- The marginal distribution is independent of the variables in `s`. -/
theorem marginal_eq {x y : ∀ i, π i} (f : (∀ i, π i) → ℝ≥0∞) (h : ∀ (i) (_ : i ∉ s), x i = y i) :
    (∫⋯∫_s, f ∂μ) x = (∫⋯∫_s, f ∂μ) y := by dsimp [marginal, update']; rcongr; exact h _ ‹_›
#align measure_theory.marginal_eq MeasureTheory.marginal_eq

variable (μ)

theorem marginal_update (x : ∀ i, π i) (f : (∀ i, π i) → ℝ≥0∞) {i : δ} (y : π i) (hi : i ∈ s) :
    (∫⋯∫_s, f ∂μ) (Function.update x i y) = (∫⋯∫_s, f ∂μ) x := by
  refine' marginal_eq f fun j hj => _
  have : j ≠ i := by rintro rfl; exact hj hi
  apply update_noteq this
#align measure_theory.marginal_update MeasureTheory.marginal_update

theorem marginal_union (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) (hst : Disjoint s t) :
    ∫⋯∫_s ∪ t, f ∂μ = ∫⋯∫_s, ∫⋯∫_t, f ∂μ ∂μ := by
  ext1 x
  simp_rw [marginal, update', ← Measure.pi_map_left _ (finsetUnionEquivSum s t hst).symm]
  rw [lintegral_map, ← Measure.pi_sum, lintegral_map, lintegral_prod]
  dsimp only [finsetUnionEquivSum_symm_inl, finsetUnionEquivSum_symm_inr, Subtype.coe_mk]
  congr 1; ext1 x; congr 1; ext1 y; congr 1; ext1 i
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;>
    simp only [his, hit, dif_pos, dif_neg, Finset.mem_union, true_or_iff, false_or_iff,
      not_false_iff]
  · exfalso; exact Finset.disjoint_left.mp hst his hit
  -- this is ugly, but applying lemmas basically doesn't work because of dependent types
  · change
      piCongrLeft (fun b : ↥(s ∪ t) => π ↑b) (finsetUnionEquivSum s t hst).symm
          (piSum (fun i : Sum s t => π ↑((finsetUnionEquivSum s t hst).symm i)) (x, y))
          ((finsetUnionEquivSum s t hst).symm <| Sum.inl ⟨i, his⟩) =
        x ⟨i, his⟩
    rw [piCongrLeft_sum_inl]
  · change
      piCongrLeft (fun b : ↥(s ∪ t) => π ↑b) (finsetUnionEquivSum s t hst).symm
          (piSum (fun i : Sum s t => π ↑((finsetUnionEquivSum s t hst).symm i)) (x, y))
          ((finsetUnionEquivSum s t hst).symm <| Sum.inr ⟨i, hit⟩) =
        y ⟨i, hit⟩
    rw [piCongrLeft_sum_inr]
  -- simp_rw [cast_sum_rec],
  -- simp only [piCongrLeft_apply, piSum_apply, dif_neg, not_false_iff],
  -- dsimp only [equiv.symm_symm],
  -- dsimp only [e, set.union_symm_apply_left],
  all_goals sorry
#align measure_theory.marginal_union MeasureTheory.marginal_union

theorem marginal_union' (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {s t : Finset δ}
    (hst : Disjoint s t) : ∫⋯∫_s ∪ t, f ∂μ = ∫⋯∫_t, ∫⋯∫_s, f ∂μ ∂μ :=
  by
  ext x
  simp_rw [marginal, ← Measure.pi_map_left _ (finsetUnionEquivSum s t hst).symm]
  rw [lintegral_map, ← Measure.pi_sum, lintegral_map, lintegral_prod]
  dsimp only [finsetUnionEquivSum_symm_inl, finsetUnionEquivSum_symm_inr, Subtype.coe_mk]
  congr 1
  -- dsimp only [e, set.union_symm_apply_left],
  all_goals sorry
#align measure_theory.marginal_union' MeasureTheory.marginal_union'

--
-- { symmetry, congr' with x, congr' with y, congr' with i, symmetry,
-- by_cases his : i ∈ s; by_cases hit : i ∈ t,
--   { exact false.elim (this ⟨his, hit⟩) },
--   all_goals { simp only [his, hit, piCongrLeft_apply, dif_pos, or_false, false_or,
--     Measure.equiv.piSum_apply, dif_neg, not_false_iff, finset.mem_union] },
--   all_goals { dsimp only [e, trans_apply, finset_union_apply, set.union_apply_left,
--   set.union_apply_right, subtype.coe_mk], rw [← heq_iff_eq], refine (eq_mpr_heq _ _).trans _ },
--   exact congr_arg_heq _ (set.union_apply_left' this his),
--   exact congr_arg_heq _ (set.union_apply_right' this hit) },
variable {μ}

theorem marginal_singleton (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) (i : δ) :
    ∫⋯∫_{i}, f ∂μ = fun x => ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i :=
  by
  letI : Unique ({i} : Finset δ) :=
    ⟨⟨⟨i, mem_singleton_self i⟩⟩, fun j => Subtype.ext <| mem_singleton.mp j.2⟩
  ext1 x
  simp_rw [marginal, update', Measure.pi_unique_left _]
  rw [lintegral_map]
  congr with y; congr with j
  by_cases hj : j = i
  · cases hj.symm; simp only [dif_pos, Finset.mem_singleton, update_same]
    exact @uniqueElim_default _ (fun i : (({i} : Finset δ) : Set δ) => π i) _ y
  · simp [hj]
  · sorry
  · exact measurable_uniqueElim
#align measure_theory.marginal_singleton MeasureTheory.marginal_singleton

theorem integral_update (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) (i : δ) (x : ∀ i, π i) :
    ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i = (∫⋯∫_{i}, f ∂μ) x := by
  simp_rw [marginal_singleton f hf i]
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
    ∫⁻ xᵢ, (∫⋯∫_s, f ∂μ) (Function.update x i xᵢ) ∂μ i = (∫⋯∫_insert i s, f ∂μ) x :=
  by
  rw [Finset.insert_eq, marginal_union, marginal_singleton]
  dsimp only
  sorry
  sorry
  sorry
#align measure_theory.marginal_insert_rev MeasureTheory.marginal_insert_rev

open Filter

theorem marginal_mono {f g : (∀ i, π i) → ℝ≥0∞} (hfg : f ≤ g) : ∫⋯∫_s, f ∂μ ≤ ∫⋯∫_s, g ∂μ :=
  fun _ => lintegral_mono fun _ => hfg _
#align measure_theory.marginal_mono MeasureTheory.marginal_mono

theorem marginal_univ [Fintype δ] {f : (∀ i, π i) → ℝ≥0∞} (hf : Measurable f) :
    ∫⋯∫_univ, f ∂μ = fun _ => ∫⁻ x, f x ∂Measure.pi μ :=
  by
  let e : { j // j ∈ Finset.univ } ≃ δ := Equiv.subtypeUnivEquiv mem_univ
  ext1 x
  simp_rw [marginal, update', ← Measure.pi_map_left μ e]
  rw [lintegral_map hf]
  congr with y
  congr with i
  simp
  rfl
  sorry
#align measure_theory.marginal_univ MeasureTheory.marginal_univ

end Marginal

end MeasureTheory

open MeasureTheory

section Sobolev

open TopologicalSpace

variable [Fintype ι] {π : ι → Type _} [∀ i, MeasurableSpace (π i)] (μ : ∀ i, Measure (π i))
  [∀ i, SigmaFinite (μ i)] (u : (ι → ℝ) → ℝ) {f : (∀ i, π i) → ℝ≥0∞}

def rhsAux (f : (∀ i, π i) → ℝ≥0∞) (s : Finset ι) : (∀ i, π i) → ℝ≥0∞ :=
  marginal μ s f ^ ((s.card : ℝ) / (Fintype.card ι - 1 : ℝ)) *
    ∏ i in sᶜ, marginal μ (insert i s) f ^ ((1 : ℝ) / (Fintype.card ι - 1 : ℝ))
#align rhs_aux rhsAux

theorem marginal_rhsAux_le (f : (∀ i, π i) → ℝ≥0∞) (s : Finset ι) (i : ι) (hi : i ∉ s) :
    ∫⋯∫_{i}, rhsAux μ f s ∂μ ≤ rhsAux μ f (insert i s) :=
  by
  simp_rw [rhsAux, ← insert_compl_insert hi]
  rw [prod_insert (not_mem_compl.mpr <| mem_insert_self i s)]
  rw [mul_left_comm, mul_prod_eq_prod_insertNone]
  simp_rw [marginal_singleton _ sorry]
  have := fun x xᵢ => marginal_update μ x f xᵢ (s.mem_insert_self i)
  simp_rw [Pi.mul_apply, Pi.pow_apply, this]
  clear this
  intro x
  dsimp only
  have h1 : (∫⋯∫_insert i s, f ∂μ) x ^ ((1 : ℝ) / (↑(Fintype.card ι) - 1 : ℝ)) ≠ ∞ := by sorry
  simp_rw [lintegral_const_mul' _ _ h1, prod_apply, Option.elim'_comp₂, Pi.pow_apply]
  refine' (ENNReal.mul_left_mono (lintegral_prod_norm_pow_le _ _ _)).trans_eq _
  · sorry
  · sorry
  simp_rw [prod_insertNone]
  dsimp
  simp_rw [marginal_insert_rev _ sorry hi]
  rw [← mul_assoc]
  congr
  · convert (ENNReal.rpow_add _ _ _ _).symm using 2
    sorry
    sorry
    sorry
  simp_rw [prod_apply, Pi.pow_apply]
  refine' prod_congr rfl fun j hj => _
  congr 1
  rw [Insert.comm]
  have h2 : i ∉ insert j s := by sorry
  simp_rw [marginal_insert_rev _ sorry h2]
#align marginal_rhs_aux_le marginal_rhsAux_le

theorem marginal_rhsAux_empty_le (f : (∀ i, π i) → ℝ≥0∞) (s : Finset ι) :
    ∫⋯∫_s, rhsAux μ f ∅ ∂μ ≤ rhsAux μ f s :=
  by
  induction' s using Finset.induction with i s hi ih
  · rw [marginal_empty]
  · have hi' : Disjoint {i} s := sorry
    conv_lhs => rw [Finset.insert_eq, marginal_union μ _ sorry hi']
    refine' (marginal_mono ih).trans _
    exact marginal_rhsAux_le μ f s i hi
#align marginal_rhs_aux_empty_le marginal_rhsAux_empty_le

theorem lintegral_prod_lintegral_pow_le (hf : Measurable f) :
    ∫⁻ x, ∏ i,
      (∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ^
        ((1 : ℝ) / (Fintype.card ι - 1 : ℝ)) ∂Measure.pi μ ≤
      (∫⁻ x, f x ∂Measure.pi μ) ^ ((Fintype.card ι : ℝ) / (Fintype.card ι - 1 : ℝ)) :=
  by
  cases isEmpty_or_nonempty (∀ i, π i)
  · simp_rw [lintegral_of_isEmpty]; refine' zero_le _
  inhabit ∀ i, π i
  have := marginal_rhsAux_empty_le μ f Finset.univ default
  simp_rw [rhsAux, marginal_univ hf, Finset.compl_univ, Finset.prod_empty, marginal_empty,
    Finset.card_empty, Nat.cast_zero, zero_div, Finset.compl_empty, mul_one, Pi.mul_def,
    Pi.pow_apply, ENNReal.rpow_zero, one_mul, Finset.prod_fn, Pi.pow_apply, insert_emptyc_eq,
    marginal_singleton f sorry] at this
  rw [marginal_univ] at this
  exact this
  sorry
#align lintegral_prod_lintegral_pow_le lintegral_prod_lintegral_pow_le

theorem integral_prod_integral_pow_le {f : (∀ i, π i) → ℝ} (hf : Measurable f)
    (h2f : ∀ x, 0 ≤ f x) :
    ∫ x,
        ∏ i,
          (∫ xᵢ, f (Function.update x i xᵢ) ∂μ i) ^ ((1 : ℝ) / (Fintype.card ι - 1)) ∂Measure.pi μ ≤
      (∫ x, f x ∂Measure.pi μ) ^ ((Fintype.card ι : ℝ) / (Fintype.card ι - 1)) :=
  by sorry
#align integral_prod_integral_pow_le integral_prod_integral_pow_le

/-- The Sobolev inequality -/
theorem integral_pow_le (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u) :
    ∫ x, ‖u x‖ ^ ((Fintype.card ι : ℝ) / (Fintype.card ι - 1)) ≤
      (∫ x, ‖fderiv ℝ u x‖) ^ ((Fintype.card ι : ℝ) / (Fintype.card ι - 1)) :=
  by
  refine' le_trans _ (integral_prod_integral_pow_le (fun _ => volume) sorry fun x => norm_nonneg _)
  refine' integral_mono sorry sorry fun x => _
  dsimp only
  simp_rw [div_eq_mul_inv, one_mul, Real.rpow_mul sorry, Real.prod_rpow _ sorry]
  refine' Real.rpow_le_rpow sorry _ sorry
  norm_cast
  rw [← card_univ, ← prod_const]
  refine' prod_le_prod (fun i hi => norm_nonneg _) fun i hi => _
  have h3u : ContDiff ℝ 1 fun t => u (update x i t) := by sorry
  have h4u : HasCompactSupport fun t => u (update x i t) := by sorry
  have := h4u.integral_deriv_eq h3u (x i)
  dsimp only at this
  simp_rw [update_eq_self] at this
  rw [← this]
  refine' (norm_integral_le_integral_norm _).trans _
  refine' (set_integral_mono_set sorry sorry _).trans _
  exact Set.univ
  refine' (Set.subset_univ _).eventuallyLE
  rw [integral_univ]
  refine' integral_mono sorry sorry fun y => _
  rw [← Function.comp_def u (update x i), deriv]
  rw [fderiv.comp y (hu.differentiable le_rfl).differentiableAt (sorry : DifferentiableAt ℝ (update x i) y)]
  rw [ContinuousLinearMap.comp_apply]
  refine' (ContinuousLinearMap.le_op_norm _ _).trans _
  conv_rhs => rw [← mul_one ‖_‖]
  simp_rw [fderiv_update]
  refine' mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine' (ContinuousLinearMap.le_op_norm _ _).trans_eq _
  rw [norm_one, mul_one]
  exact ContinuousLinearMap.norm_pi_update_eq_one fun _ => ℝ
#align integral_pow_le integral_pow_le

/-- The Sobolev inequality for the Lebesgue integral(?) -/
theorem lintegral_pow_le :
    ∫⁻ x, ‖u x‖₊ ^ ((Fintype.card ι : ℝ) / (Fintype.card ι - 1 : ℝ)) ≤
      (∫⁻ x, ‖fderiv ℝ u x‖₊) ^ ((Fintype.card ι : ℝ) / (Fintype.card ι - 1 : ℝ)) :=
  by sorry
#align lintegral_pow_le lintegral_pow_le

end Sobolev
