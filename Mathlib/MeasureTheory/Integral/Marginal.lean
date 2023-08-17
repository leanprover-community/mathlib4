/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module main
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Support

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

open NNReal

theorem rpow_add_of_nonneg {x : ℝ≥0∞} (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  induction x using recTopCoe
  · rcases hy.eq_or_lt with rfl|hy
    · rw [rpow_zero, one_mul, zero_add]
    rcases hz.eq_or_lt with rfl|hz
    · rw [rpow_zero, mul_one, add_zero]
    simp [top_rpow_of_pos, hy, hz, add_pos hy hz]
  simp [coe_rpow_of_nonneg, hy, hz, add_nonneg hy hz, NNReal.rpow_add_of_nonneg _ hy hz]

theorem prod_rpow_of_nonneg {ι} {s : Finset ι} {f : ι → ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) :
    ∏ i in s, f i ^ r = (∏ i in s, f i) ^ r := by
  induction s using Finset.induction
  case empty => simp
  case insert i s hi ih => simp_rw [prod_insert hi, ih, ← mul_rpow_of_nonneg _ _ hr]

-- unused
theorem prod_rpow_of_ne_top {ι} {s : Finset ι} {f : ι → ℝ≥0∞} (hf : ∀ i ∈ s, f i ≠ ∞) (r : ℝ) :
    ∏ i in s, f i ^ r = (∏ i in s, f i) ^ r := by
  induction s using Finset.induction
  case empty => simp
  case insert i s hi ih =>
    have h2f : ∀ i ∈ s, f i ≠ ∞ := fun i hi ↦ hf i <| mem_insert_of_mem hi
    rw [prod_insert hi, prod_insert hi, ih h2f, ← mul_rpow_of_ne_top <| hf i <| mem_insert_self ..]
    apply prod_lt_top h2f |>.ne

-- unused
theorem prod_coe_rpow {ι} (s : Finset ι) (f : ι → ℝ≥0) (r : ℝ) :
    ∏ i in s, (f i : ℝ≥0∞) ^ r = ((∏ i in s, f i : ℝ≥0) : ℝ≥0∞) ^ r := by
  induction s using Finset.induction
  case empty => simp
  case insert i s hi ih => simp_rw [prod_insert hi, ih, ← coe_mul_rpow, coe_mul]

end ENNReal


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

@[simp] theorem comp_def (f : β → γ) (g : α → β) : f ∘ g = fun x => f (g x) := rfl

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

section Calculus

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] [Fintype ι]

variable {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem contDiff_update (k : ℕ∞) (x : ∀ i, E i) (i : ι) : ContDiff 𝕜 k (Function.update x i) := by
  rw [contDiff_pi]
  intro j
  dsimp [Function.update]
  split_ifs with h
  · subst h
    exact contDiff_id
  · exact contDiff_const

theorem hasFDerivAt_sub_const {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]  {x : E} (c : E) :
    HasFDerivAt (· - c) (ContinuousLinearMap.id 𝕜 (E)) x :=
  (hasFDerivAt_id x).sub_const c

theorem hasFDerivAt_update {x : ∀ i, E i} {i : ι} (y : E i) :
    HasFDerivAt (Function.update x i)
      (ContinuousLinearMap.pi (Function.update 0 i (ContinuousLinearMap.id 𝕜 (E i)))) y := by
  set l := (ContinuousLinearMap.pi (Function.update 0 i (ContinuousLinearMap.id 𝕜 (E i))))
  have update_eq : Function.update x i = (fun _ ↦ x) + l ∘ (· - x i)
  · ext t j
    dsimp [Function.update]
    split_ifs with hji
    · subst hji
      simp
    · simp
  rw [update_eq]
  convert (hasFDerivAt_const _ _).add (l.hasFDerivAt.comp y (hasFDerivAt_sub_const (x i)))
  rw [zero_add, ContinuousLinearMap.comp_id]

theorem fderiv_update {x : ∀ i, E i} {i : ι} (y : E i) :
    fderiv 𝕜 (Function.update x i) y =
      ContinuousLinearMap.pi (Function.update 0 i (ContinuousLinearMap.id 𝕜 (E i))) :=
  (hasFDerivAt_update y).fderiv

theorem hasDerivAt_update {x : ι → 𝕜} {i : ι} (y : 𝕜) :
    HasDerivAt (Function.update x i) (Pi.single i (1:𝕜)) y := by
  convert (hasFDerivAt_update (E := fun _ ↦ 𝕜) y).hasDerivAt
  ext z j
  rw [Pi.single, Function.update_apply]
  split_ifs with h
  · simp [h]
  · simp [Function.update_noteq h]

theorem deriv_update {x : ι → 𝕜} {i : ι} (y : 𝕜) :
    deriv (Function.update x i) y = (Pi.single i (1:𝕜)) :=
  (hasDerivAt_update y).deriv

open NNReal

theorem Pi.nnnorm_single (y : E i) : ‖Pi.single i y‖₊ = ‖y‖₊ := by
  classical
  have H : ∀ b, ‖single i y b‖₊ = single (f := fun _ ↦ ℝ≥0) i ‖y‖₊ b
  · intro b
    refine Pi.apply_single (fun i (x : E i) ↦ ‖x‖₊) ?_ i y b
    simp
  simp [Pi.nnnorm_def, H, Pi.single_apply, Finset.sup_ite,
    Finset.filter_eq' (Finset.univ : Finset ι)]

theorem Pi.norm_single (y : E i) : ‖Pi.single i y‖ = ‖y‖ :=
  congr_arg Subtype.val (Pi.nnnorm_single y)

end Calculus

section RealCalculus

open Set MeasureTheory

variable {E : Type*} {f f' : ℝ → E} {g g' : ℝ → ℝ} {a b l : ℝ} {m : E} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E]

/-- **Fundamental theorem of calculus-2**, on semi-infinite intervals `(-∞, a)`.
When a function has a limit `m` at `-∞`, and its derivative is integrable, then the
integral of the derivative on `(-∞, a)` is `f a - m`. Version assuming differentiability
on `(-∞, a)` and continuity on `(-∞, a]`.-/
theorem integral_Iio_of_hasDerivAt_of_tendsto (hcont : ContinuousOn f (Iic a))
    (hderiv : ∀ x ∈ Iio a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Iic a))
    (hf : Tendsto f atBot (𝓝 m)) : ∫ x in Iic a, f' x = f a - m := by
  refine' tendsto_nhds_unique (intervalIntegral_tendsto_integral_Iic a f'int tendsto_id) _
  apply Tendsto.congr' _ (hf.const_sub _)
  filter_upwards [Iic_mem_atBot a] with x hx
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx
    (hcont.mono Icc_subset_Iic_self) fun y hy => hderiv y hy.2
  rw [intervalIntegrable_iff_integrable_Ioc_of_le hx]
  exact f'int.mono (fun y hy => hy.2) le_rfl

theorem atBot_le_cocompact : atBot ≤ cocompact ℝ := by simp
theorem atTop_le_cocompact : atTop ≤ cocompact ℝ := by simp

theorem _root_.Filter.EventuallyEq.tendsto [TopologicalSpace β] {f : α → β} {l : Filter α} {a : β}
    (hf : f =ᶠ[l] fun _ ↦ a) : Tendsto f l (𝓝 a) :=
  tendsto_nhds_of_eventually_eq hf

-- very special case of `integral_Iio_of_hasDerivAt_of_tendsto`.
theorem _root_.HasCompactSupport.integral_deriv_eq {f : ℝ → E} (hf : ContDiff ℝ 1 f)
    (h2f : HasCompactSupport f) (b : ℝ) : ∫ x in Iic b, deriv f x = f b := by
  have := fun x (_ : x ∈ Iio b) ↦ hf.differentiable le_rfl x |>.hasDerivAt
  rw [integral_Iio_of_hasDerivAt_of_tendsto hf.continuous.continuousOn this, sub_zero]
  refine hf.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport h2f.deriv |>.integrableOn
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at h2f
  exact h2f.filter_mono atBot_le_cocompact |>.tendsto

end RealCalculus

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

theorem piCongrLeft_preimage_univ_pi (f : ι' ≃ ι) (t : ∀ i, Set (α i)) :
    f.piCongrLeft α ⁻¹' pi univ t = pi univ fun i => t (f i) := by
  apply Set.ext; rw [← (f.piCongrLeft α).symm.forall_congr_left]
  intro x; simp_rw [mem_preimage, apply_symm_apply, piCongrLeft_symm_apply, mem_univ_pi]
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
  simp_rw [piCongrLeft_apply, piSum_apply, sum_rec_congr _ _ _ (e.symm_apply_apply (inl i)),
    cast_cast, cast_eq]

theorem piCongrLeft_sum_inr (π : ι'' → Type _) (e : ι ⊕ ι' ≃ ι'') (f : ∀ i, π (e (inl i)))
    (g : ∀ i, π (e (inr i))) (j : ι') :
    piCongrLeft π e (piSum (fun x => π (e x)) (f, g)) (e (inr j)) = g j := by
  simp_rw [piCongrLeft_apply, piSum_apply, sum_rec_congr _ _ _ (e.symm_apply_apply (inr j)),
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

-- @[simps apply symm_apply]
/-- `s ∪ t` (using finset union) is equivalent to `s ∪ t` (using set union) -/
def Equiv.finsetUnion {α} (s t : Finset α) : ((s ∪ t : Finset α) : Set α) ≃ (s ∪ t : Set α) :=
  subtypeEquivRight <| by simp

/-- The disjoint union of finsets is a sum -/
def finsetUnionEquivSum {α} (s t : Finset α) (h : Disjoint s t) : (s ∪ t : Finset α) ≃ s ⊕ t :=
  (Equiv.finsetUnion s t).trans <| Equiv.Set.union <| by
    rw [← Finset.coe_inter, ← Finset.coe_empty]
    exact h.le_bot

@[simp]
theorem finsetUnionEquivSum_symm_inl {α} {s t : Finset α} (h : Disjoint s t) (x : s) :
    (finsetUnionEquivSum s t h).symm (Sum.inl x) = ⟨x, Finset.mem_union.mpr <| Or.inl x.2⟩ :=
  rfl

@[simp]
theorem finsetUnionEquivSum_symm_inr {α} {s t : Finset α} (h : Disjoint s t) (y : t) :
    (finsetUnionEquivSum s t h).symm (Sum.inr y) = ⟨y, Finset.mem_union.mpr <| Or.inr y.2⟩ :=
  rfl

@[simp]
theorem finsetUnionEquivSum_symm_inl' {α} {s t : Finset α} (h : Disjoint s t) (x : α) (hx : x ∈ s)
    (h2x : x ∈ s ∪ t) : (finsetUnionEquivSum s t h).symm (Sum.inl ⟨x, hx⟩) = ⟨x, h2x⟩ :=
  rfl

@[simp]
theorem finsetUnionEquivSum_symm_inr' {α} {s t : Finset α} (h : Disjoint s t) (y : t) :
    (finsetUnionEquivSum s t h).symm (Sum.inr y) = ⟨y, Finset.mem_union.mpr <| Or.inr y.2⟩ :=
  rfl

theorem iUnion_univ_pi {ι ι₂} {α : ι → Type _} (t : ∀ i, ι₂ → Set (α i)) :
    (⋃ x : ι → ι₂, pi univ fun i => t i (x i)) = pi univ fun i => ⋃ j : ι₂, t i j := by
  ext
  simp [Classical.skolem]

theorem eval_preimage {ι} {α : ι → Type _} {i : ι} {s : Set (α i)} :
    eval i ⁻¹' s = pi univ (update (fun i => univ) i s) := by
  ext x
  simp [@forall_update_iff _ (fun i => Set (α i)) _ _ _ _ fun i' y => x i' ∈ y]

theorem eval_preimage' {ι} {α : ι → Type _} {i : ι} {s : Set (α i)} :
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

theorem pred_update {α} {β : α → Type _} (P : ∀ ⦃a⦄, β a → Prop) (f : ∀ a, β a) (a' : α) (v : β a')
    (a : α) : P (update f a' v a) ↔ a = a' ∧ P v ∨ a ≠ a' ∧ P (f a) := by
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
theorem updateSet_singleton {i y} :
    updateSet x {i} y = Function.update x i (y ⟨i, mem_singleton_self i⟩) := by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_same, updateSet]
  · simp [hj, updateSet]

theorem update_eq_updateSet {i y} :
    Function.update x i y = updateSet x {i} (uniqueElim y) := by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_same, updateSet]
    exact uniqueElim_default (α := fun j : ({i} : Finset ι) => π j) y
  · simp [hj, updateSet]

theorem updateSet_updateSet {s t : Finset ι} (hst : Disjoint s t) {y z} :
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
  simp_rw [piCongrLeft_apply]
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

-- workaround for `@[gcongr]` not recognizing some existing lemmas, like `lintegral_mono`, as valid
@[gcongr] theorem lintegral_mono2 ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x, f x ≤ g x) :
    lintegral μ f ≤ lintegral μ g :=
lintegral_mono hfg

@[gcongr] theorem lintegral_mono3 ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x, f x ≤ g x) (h2 : μ ≤ ν) :
    lintegral μ f ≤ lintegral ν g :=
lintegral_mono' h2 hfg

@[gcongr] theorem lintegral_congr2 ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x, f x = g x) :
    lintegral μ f = lintegral μ g :=
lintegral_congr hfg

alias ENNReal.coe_le_coe ↔ _ ENNReal.monotone2
attribute [gcongr] ENNReal.monotone2 ENNReal.rpow_le_rpow


theorem Subsingleton.measurableSingletonClass {α} [MeasurableSpace α] [Subsingleton α] :
    MeasurableSingletonClass α := by
  refine' ⟨fun i => _⟩
  convert MeasurableSet.univ
  simp [Set.eq_univ_iff_forall]

/-- A different formulation of Hölder's inequality for two functions -/
theorem ENNReal.lintegral_mul_norm_pow_le {α} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    ∫⁻ a, f a ^ p * g a ^ q ∂μ ≤ (∫⁻ a, f a ∂μ) ^ p * (∫⁻ a, g a ∂μ) ^ q := by
  rcases hp.eq_or_lt with rfl|hp
  · simp at hpq
    subst hpq
    simp
  rcases hq.eq_or_lt with rfl|hq
  · simp at hpq
    subst hpq
    simp
  have h2p : 1 < 1 / p
  · rw [one_div]
    apply one_lt_inv hp
    linarith
  have h2pq : 1 / (1 / p) + 1 / (1 / q) = 1
  · simp [hp.ne', hq.ne', hpq]
  have := ENNReal.lintegral_mul_le_Lp_mul_Lq μ ⟨h2p, h2pq⟩ (hf.pow_const p) (hg.pow_const q)
  simpa [← ENNReal.rpow_mul, hp.ne', hq.ne'] using this


@[to_additive]
theorem prod_insert_div [CommGroup β] [DecidableEq α] (ha : a ∉ s) {f : α → β} :
    (∏ x in insert a s, f x) / f a = ∏ x in s, f x := by simp [ha]

/-- A version of Hölder with multiple arguments -/
theorem ENNReal.lintegral_prod_norm_pow_le {α} [MeasurableSpace α] {μ : Measure α} (s : Finset ι)
    (hs : s.Nonempty)
    {f : ι → α → ℝ≥0∞} (hf : ∀ i ∈ s, AEMeasurable (f i) μ) {p : ι → ℝ} (hp : ∑ i in s, p i = 1)
    (h2p : ∀ i ∈ s, 0 ≤ p i) :
      ∫⁻ a, ∏ i in s, f i a ^ p i ∂μ ≤
      ∏ i in s, (∫⁻ a, f i a ∂μ) ^ p i := by
  induction s using Finset.induction generalizing p
  case empty =>
    simp at hs
  case insert i₀ s hi₀ ih =>
    rcases eq_or_ne (p i₀) 1 with h2i₀|h2i₀
    · simp [hi₀]
      have h2p : ∀ i ∈ s, p i = 0
      · simpa [hi₀, h2i₀, sum_eq_zero_iff_of_nonneg (fun i hi ↦ h2p i <| mem_insert_of_mem hi)]
          using hp
      calc ∫⁻ a, f i₀ a ^ p i₀ * ∏ i in s, f i a ^ p i ∂μ
          = ∫⁻ a, f i₀ a ^ p i₀ * ∏ i in s, 1 ∂μ := by
            congr with x
            congr 1
            apply prod_congr rfl fun i hi ↦ by rw [h2p i hi, ENNReal.rpow_zero]
        _ ≤ (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * ∏ i in s, 1 := by simp [h2i₀]
        _ = (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * ∏ i in s, (∫⁻ a, f i a ∂μ) ^ p i := by
            congr 1
            apply prod_congr rfl fun i hi ↦ by rw [h2p i hi, ENNReal.rpow_zero]
    · have hs : s.Nonempty
      · rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        simp [h2i₀] at hp
      have hpi₀ : 0 ≤ 1 - p i₀
      · simp_rw [sub_nonneg, ← hp, single_le_sum h2p (mem_insert_self ..)]
      have h2pi₀ : 1 - p i₀ ≠ 0
      · rwa [sub_ne_zero, ne_comm]
      let q := fun i ↦ p i / (1 - p i₀)
      have hq : ∑ i in s, q i = 1
      · rw [← sum_div, ← sum_insert_sub hi₀, hp, div_self h2pi₀]
      have h2q : ∀ i ∈ s, 0 ≤ q i
      · exact fun i hi ↦ div_nonneg (h2p i <| mem_insert_of_mem hi) hpi₀
      calc ∫⁻ a, ∏ i in insert i₀ s, f i a ^ p i ∂μ
          = ∫⁻ a, f i₀ a ^ p i₀ * ∏ i in s, f i a ^ p i ∂μ := by simp [hi₀]
        _ = ∫⁻ a, f i₀ a ^ p i₀ * (∏ i in s, f i a ^ q i) ^ (1 - p i₀) ∂μ := by
            simp [← ENNReal.prod_rpow_of_nonneg hpi₀, ← ENNReal.rpow_mul,
              div_mul_cancel (h := h2pi₀)]
        _ ≤ (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * (∫⁻ a, ∏ i in s, f i a ^ q i ∂μ) ^ (1 - p i₀) := by
            apply ENNReal.lintegral_mul_norm_pow_le
            · exact hf i₀ <| mem_insert_self ..
            · exact s.aemeasurable_prod <| fun i hi ↦ (hf i <| mem_insert_of_mem hi).pow_const _
            · exact h2p i₀ <| mem_insert_self ..
            · exact hpi₀
            · apply add_sub_cancel'_right
        _ ≤ (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * (∏ i in s, (∫⁻ a, f i a ∂μ) ^ q i) ^ (1 - p i₀) := by
            gcongr
            exact ih hs (fun i hi ↦ hf i <| mem_insert_of_mem hi) hq h2q
        _ = (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * ∏ i in s, (∫⁻ a, f i a ∂μ) ^ p i := by
            simp [← ENNReal.prod_rpow_of_nonneg hpi₀, ← ENNReal.rpow_mul,
              div_mul_cancel (h := h2pi₀)]
        _ = ∏ i in insert i₀ s, (∫⁻ a, f i a ∂μ) ^ p i := by simp [hi₀]

/-- A version of Hölder with multiple arguments, one of which plays a distinguished role -/
theorem ENNReal.lintegral_mul_prod_norm_pow_le {α} [MeasurableSpace α] {μ : Measure α} (s : Finset ι)
    {g : α →  ℝ≥0∞} {f : ι → α → ℝ≥0∞} (hg : AEMeasurable g μ) (hf : ∀ i ∈ s, AEMeasurable (f i) μ)
    (q : ℝ) {p : ι → ℝ} (hpq : q + ∑ i in s, p i = 1) (hq :  0 ≤ q)
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    ∫⁻ a, g a ^ q * ∏ i in s, f i a ^ p i ∂μ ≤
      (∫⁻ a, g a ∂μ) ^ q * ∏ i in s, (∫⁻ a, f i a ∂μ) ^ p i := by
  calc
    ∫⁻ t, g t ^ q * ∏ j in s, (f j t) ^ p j ∂μ
      = ∫⁻ t, ∏ j in insertNone s,
            Option.elim j (g t) (fun j ↦ f j t) ^ Option.elim j q p ∂μ := by
          congr! 1
          ext t
          rw [prod_insertNone]
          dsimp
    _ ≤ ∏ j in insertNone s,
          (∫⁻ t, Option.elim j (g t) (fun j ↦ f j t) ∂μ) ^ Option.elim j q p := by
          refine ENNReal.lintegral_prod_norm_pow_le _ insertNone_nonempty ?_ ?_ ?_
          · rintro (_|i) hi
            · exact hg
            · refine hf i ?_
              simpa using hi
          · simp_rw [sum_insertNone, compl_insert, Option.elim, sum_const, nsmul_eq_mul]
            exact hpq
          · rintro (_|i) hi
            · exact hq
            · refine hp i ?_
              simpa using hi
    _ = (∫⁻ t, g t ∂μ) ^ q * ∏ j in s, (∫⁻ t, f j t ∂μ) ^ p j := by
          -- this proof could be `simp [prod_insertNone]` but that's too slow
          simp_rw [prod_insertNone]
          dsimp

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

section

variable {α E : Type _} [MeasurableSpace α] [NormedAddCommGroup E]

theorem _root_.Measurable.hasFiniteIntegral_dirac {f : α → E}
    (hf : Measurable (fun x => ‖f x‖₊ : α → ℝ≥0∞)) {x : α} :
    HasFiniteIntegral f (Measure.dirac x) := by
  rw [HasFiniteIntegral, lintegral_dirac' _ hf]
  exact ENNReal.coe_lt_top

theorem hasFiniteIntegral_dirac [MeasurableSingletonClass α] {f : α → E} {x : α} :
    HasFiniteIntegral f (Measure.dirac x) := by
  rw [HasFiniteIntegral, lintegral_dirac]
  exact ENNReal.coe_lt_top

theorem StronglyMeasurable.integrable_dirac [MeasurableSpace E] [BorelSpace E] {f : α → E}
    (hf : StronglyMeasurable f) {x : α} : Integrable f (Measure.dirac x) :=
  ⟨hf.aestronglyMeasurable, hf.measurable.ennnorm.hasFiniteIntegral_dirac⟩


end

section Marginal

open TopologicalSpace

variable {δ : Type _} {π : δ → Type _} [∀ x, MeasurableSpace (π x)]

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

theorem marginal_empty (f : (∀ i, π i) → ℝ≥0∞) : ∫⋯∫_∅, f ∂μ = f := by
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

theorem marginal_update (x : ∀ i, π i) (f : (∀ i, π i) → ℝ≥0∞) {i : δ} (y : π i) (hi : i ∈ s) :
    (∫⋯∫_s, f ∂μ) (Function.update x i y) = (∫⋯∫_s, f ∂μ) x := by
  gcongr with j hj
  have : j ≠ i := by rintro rfl; exact hj hi
  apply update_noteq this

theorem marginal_union (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) (hst : Disjoint s t) :
    ∫⋯∫_s ∪ t, f ∂μ = ∫⋯∫_s, ∫⋯∫_t, f ∂μ ∂μ := by
  ext1 x
  set e₁ := (finsetUnionEquivSum s t hst).symm
  set e₂ := MeasurableEquiv.piCongrLeft (fun i : ↥(s ∪ t) => π i) e₁
  set e₃ := MeasurableEquiv.piSum fun b ↦ π (e₁ b)
  calc (∫⋯∫_s ∪ t, f ∂μ) x
      = ∫⁻ (y : (i : ↥(s ∪ t)) → π i), f (updateSet x (s ∪ t) y)
          ∂.pi fun i' : ↥(s ∪ t) ↦ μ i' := by rfl
    _ = ∫⁻ (y : (i : s ⊕ t) → π (e₁ i)), f (updateSet x (s ∪ t) (e₂ y))
          ∂.pi fun i' : s ⊕ t ↦ μ (e₁ i') := by
        simp_rw [marginal, ← Measure.pi_map_left _ e₁, lintegral_map_equiv]
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

theorem marginal_singleton (f : (∀ i, π i) → ℝ≥0∞) (i : δ) :
    ∫⋯∫_{i}, f ∂μ = fun x => ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i := by
  let α : Type _ := ({i} : Finset δ)
  let e := (MeasurableEquiv.piUnique fun j : α ↦ π j).symm
  ext1 x
  calc (∫⋯∫_{i}, f ∂μ) x
      = ∫⁻ (y : π (default : α)), f (updateSet x {i} (e y)) ∂μ (default : α) := by
        simp_rw [marginal, ← Measure.map_piUnique_symm, lintegral_map_equiv]
    _ = ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i := by simp [update_eq_updateSet]

theorem integral_update (f : (∀ i, π i) → ℝ≥0∞) (i : δ) (x : ∀ i, π i) :
    ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i = (∫⋯∫_{i}, f ∂μ) x := by
  simp_rw [marginal_singleton f i]

theorem marginal_insert (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {i : δ} (hi : i ∉ s)
    (x : ∀ i, π i) :
    (∫⋯∫_insert i s, f ∂μ) x = ∫⁻ xᵢ, (∫⋯∫_s, f ∂μ) (Function.update x i xᵢ) ∂μ i := by
  rw [Finset.insert_eq, marginal_union μ f hf (Finset.disjoint_singleton_left.mpr hi),
    marginal_singleton]

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
    ∏ i in sᶜ, (∫⋯∫_insert i s, f ∂μ) ^ (1 / (#ι - 1 : ℝ))

lemma rhsAux_empty (f : (∀ i, π i) → ℝ≥0∞) (x : ∀ i, π i) :
    rhsAux μ f ∅ x = ∏ i, (∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ^ ((1 : ℝ) / (#ι - 1 : ℝ)) := by
  simp [rhsAux, marginal_singleton]

lemma rhsAux_univ (f : (∀ i, π i) → ℝ≥0∞) (x : ∀ i, π i) :
   rhsAux μ f univ x = (∫⁻ x, f x ∂(Measure.pi μ)) ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) := by
  simp [rhsAux, marginal_univ, Finset.card_univ]

/- Isolate the occurrence of `∫⋯∫_insert i s` in `rhsAux`, for an index `i ∉ s`. -/
lemma rhsAux_not_mem (f : (∀ i, π i) → ℝ≥0∞) {s : Finset ι} {i : ι} (hi : i ∉ s) (x : ∀ i, π i) :
    rhsAux μ f s x
      = (∫⋯∫_insert i s, f ∂μ) x ^ (1 / ((#ι:ℝ) - 1))
            * ((∫⋯∫_s, f ∂μ) x ^ ((s.card:ℝ) * (1 / ((#ι:ℝ) - 1)))
            * ∏ j in (insert i s)ᶜ, (∫⋯∫_insert j s, f ∂μ) x ^ (1 / ((#ι:ℝ) - 1))) := by
  set p := 1 / ((#ι:ℝ) - 1)
  set m : ℝ := ↑(s.card)
  calc
    rhsAux μ f s x
      = (∫⋯∫_s, f ∂μ) x ^ (m * p) * ∏ j in sᶜ, (∫⋯∫_insert j s, f ∂μ) x ^ p := by
              dsimp [rhsAux]
              rw [prod_apply]
              dsimp
              -- this proof could be `ring_nf` but that's too slow`
              congr! 2
              ring
    _ = (∫⋯∫_s, f ∂μ) x ^ (m * p) * ((∫⋯∫_insert i s, f ∂μ) x ^ p
          * ∏ j in (insert i s)ᶜ, (∫⋯∫_insert j s, f ∂μ) x ^ p) := by
              simp_rw [← insert_compl_insert hi]
              rw [prod_insert (not_mem_compl.mpr <| mem_insert_self i s)]
    _ = (∫⋯∫_insert i s, f ∂μ) x ^ p * ((∫⋯∫_s, f ∂μ) x ^ (m * p)
          * ∏ j in (insert i s)ᶜ, (∫⋯∫_insert j s, f ∂μ) x ^ p) := by ring

set_option maxHeartbeats 400000 in
/--
The main inductive step

Note: this also holds without assuming `Nontrivial ι`, by tracing through the junk values
(note that `s = ∅` in that case).
-/
theorem marginal_singleton_rhsAux_le [Nontrivial ι] (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f)
    (s : Finset ι) (i : ι) (hi : i ∉ s) (x : ∀ i, π i):
    ∫⁻ t, rhsAux μ f s (update x i t) ∂(μ i) ≤ rhsAux μ f (insert i s) x := by
  have hι : 2 ≤ (#ι : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have : 1 ≤ (#ι:ℝ) - 1 := by linarith
  let p : ℝ := 1 / ((#ι:ℝ) - 1)
  have hp : s.card * p + (insert i s)ᶜ.card * p = 1
  · have H₁ : ((insert i s).card : ℝ) = s.card + 1 := by exact_mod_cast Finset.card_insert_of_not_mem hi
    have H₂ : ((insert i s).card : ℝ) + (insert i s)ᶜ.card = #ι := by exact_mod_cast (insert i s).card_add_card_compl
    have H₃ : p * (#ι - 1) = 1
    · dsimp only
      have : (#ι:ℝ) - 1 ≠ 0 := by positivity
      field_simp [this]
    linear_combination -p * H₁ + p * H₂ + H₃
  let m : ℝ := s.card
  calc ∫⁻ t, rhsAux μ f s (update x i t) ∂(μ i)
      = ∫⁻ t, ((∫⋯∫_insert i s, f ∂μ) (update x i t) ^ p * ((∫⋯∫_s, f ∂μ) (update x i t) ^ (m * p)
          * ∏ j in (insert i s)ᶜ, (∫⋯∫_insert j s, f ∂μ) (update x i t) ^ p)) ∂(μ i) := by
              simp_rw [rhsAux_not_mem μ f hi]
    _ = (∫⋯∫_insert i s, f ∂μ) x ^ p * (∫⁻ t, ((∫⋯∫_s, f ∂μ) (update x i t) ^ (m * p)
          * ∏ j in (insert i s)ᶜ, ((∫⋯∫_insert j s, f ∂μ) (update x i t)) ^ p) ∂(μ i)) := by
              clear_value p m
              simp_rw [fun x xᵢ => marginal_update μ x f xᵢ (s.mem_insert_self i)]
              rw [lintegral_const_mul]
              refine (hf.marginal μ).comp (measurable_update x) |>.pow measurable_const |>.mul ?_
              refine Finset.measurable_prod _ fun i _ ↦ ?_
              exact (hf.marginal μ).comp (measurable_update x) |>.pow measurable_const
    _ ≤ ((∫⋯∫_insert i s, f ∂μ) x) ^ p *
          ((∫⁻ t, (∫⋯∫_s, f ∂μ) (update x i t) ∂μ i) ^ (m * p) *
            ∏ j in (insert i s)ᶜ, (∫⁻ t, (∫⋯∫_insert j s, f ∂μ) (update x i t) ∂(μ i)) ^ p) := by
              gcongr
              -- we now apply Hölder's inequality
              apply ENNReal.lintegral_mul_prod_norm_pow_le
              · exact (hf.marginal μ |>.comp <| measurable_update _).aemeasurable
              · intros
                exact (hf.marginal μ |>.comp <| measurable_update _).aemeasurable
              · simp_rw [sum_const, nsmul_eq_mul]
                exact hp
              · positivity
              · intros
                positivity
    _ = ((∫⋯∫_insert i s, f ∂μ) x) ^ p * (((∫⋯∫_insert i s, f ∂μ) x) ^ (m * p) *
            ∏ j in (insert i s)ᶜ, ((∫⋯∫_insert i (insert j s), f ∂μ) x) ^ p) := by
              rw [marginal_insert _ hf hi]
              congr! 2; refine prod_congr rfl fun j hj => ?_
              have hi' : i ∉ insert j s
              · simp only [Finset.mem_insert, Finset.mem_compl] at hj ⊢
                tauto
              rw [marginal_insert _ hf hi']
    _ = ((∫⋯∫_insert i s, f ∂μ) x) ^ ((m + 1 : ℝ) * p) *
            ∏ j in (insert i s)ᶜ, ((∫⋯∫_insert i (insert j s), f ∂μ) x) ^ p := by
              rw [← mul_assoc]
              congr
              rw [← ENNReal.rpow_add_of_nonneg]
              · -- this proof could be `ring_nf` but that's too slow`
                congr
                ring
              · positivity
              · positivity
    _ = ((∫⋯∫_insert i s, f ∂μ) ^ (((insert i s).card : ℝ) * p) *
            ∏ j in (insert i s)ᶜ, (∫⋯∫_insert j (insert i s), f ∂μ) ^ p) x := by
              -- this proof could be `simp [Insert.comm, Finset.card_insert_of_not_mem hi]` but
              -- that's too slow
              dsimp
              simp_rw [Insert.comm, prod_apply, Finset.card_insert_of_not_mem hi]
              push_cast
              rfl
    _ = rhsAux μ f (insert i s) x := by
              rw [rhsAux]
              -- this proof could be `ring_nf` but that's too slow`
              congr! 2
              ring

lemma Measurable.rhsAux (hf : Measurable f) : Measurable (rhsAux μ f s) := by
  simp [_root_.rhsAux]
  refine Measurable.mul ?_ ?_
  · dsimp
    exact (hf.marginal μ).pow measurable_const
  simp_rw [prod_apply]
  refine Finset.measurable_prod _ fun i _ ↦ ?_
  dsimp
  exact hf.marginal μ |>.pow measurable_const

theorem marginal_rhsAux_empty_le [Nontrivial ι] (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f)
    (s : Finset ι) : ∫⋯∫_s, rhsAux μ f ∅ ∂μ ≤ rhsAux μ f s := by
  induction' s using Finset.induction with i s hi ih
  · simp [marginal_empty]
  intro x
  calc (∫⋯∫_insert i s, rhsAux μ f ∅ ∂μ) x
      = ∫⁻ t, (∫⋯∫_s, rhsAux μ f ∅ ∂μ) (update x i t) ∂(μ i) := by
        rw [marginal_insert]
        · exact hf.rhsAux μ
        · exact hi
    _ ≤ ∫⁻ t, rhsAux μ f s (update x i t) ∂(μ i) := by
        apply lintegral_mono; intro t; dsimp -- should be `gcongr`
        apply ih
    _ ≤ rhsAux μ f (insert i s) x := marginal_singleton_rhsAux_le _ _ hf _ _ hi x

theorem lintegral_prod_lintegral_pow_le [Nontrivial ι] (hf : Measurable f) :
    ∫⁻ x, ∏ i, (∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ^ ((1 : ℝ) / (#ι - 1 : ℝ)) ∂Measure.pi μ ≤
      (∫⁻ x, f x ∂Measure.pi μ) ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) := by
  cases isEmpty_or_nonempty (∀ i, π i)
  · simp_rw [lintegral_of_isEmpty]; refine' zero_le _
  inhabit ∀ i, π i
  simpa [marginal_univ, rhsAux_empty, rhsAux_univ] using
    marginal_rhsAux_empty_le μ f hf Finset.univ default

-- theorem integral_prod_integral_pow_le {f : (∀ i, π i) → ℝ} (hf : Measurable f)
--     (h2f : ∀ x, 0 ≤ f x) :
--     ∫ x,
--         ∏ i,
--           (∫ xᵢ, f (Function.update x i xᵢ) ∂μ i) ^ ((1 : ℝ) / (#ι - 1)) ∂Measure.pi μ ≤
--       (∫ x, f x ∂Measure.pi μ) ^ ((#ι : ℝ) / (#ι - 1)) :=
--   by sorry
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

/-- The Gagliardo-Nirenberg-Sobolev inequality -/
theorem lintegral_pow_le [Nontrivial ι] [Fintype ι] (hu : ContDiff ℝ 1 u)
    (h2u : HasCompactSupport u) : ∫⁻ x, ‖u x‖₊ ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) ≤
      (∫⁻ x, ‖fderiv ℝ u x‖₊) ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) := by
  have : (1:ℝ) ≤ ↑#ι - 1
  · have hι : (2:ℝ) ≤ #ι := by exact_mod_cast Fintype.one_lt_card
    linarith
  calc ∫⁻ x, ‖u x‖₊ ^ ((#ι : ℝ) / (#ι - 1 : ℝ))
      = ∫⁻ x, ((‖u x‖₊ : ℝ≥0∞) ^ (1 / (#ι - 1 : ℝ))) ^ (#ι : ℝ) := by
        gcongr with x
        rw [← ENNReal.coe_rpow_of_nonneg _ (by positivity), ← ENNReal.rpow_mul]
        field_simp
    _ = ∫⁻ x, ∏ _i : ι, (‖u x‖₊ : ℝ≥0∞) ^ (1 / (#ι - 1 : ℝ)) := by
        gcongr with x
        simp_rw [prod_const, card_univ]
        norm_cast
    _ ≤ ∫⁻ x, ∏ i, (∫⁻ xᵢ, ‖fderiv ℝ u (Function.update x i xᵢ)‖₊) ^ ((1 : ℝ) / (#ι - 1 : ℝ)) := ?_
    _ ≤ (∫⁻ x, ‖fderiv ℝ u x‖₊) ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) := by
        apply lintegral_prod_lintegral_pow_le
        borelize ((ι → ℝ) →L[ℝ] ℝ)
        have : Measurable (fun x ↦ fderiv ℝ u x) := (hu.continuous_fderiv (le_refl _)).measurable
        measurability
  gcongr with x i
  calc (‖u x‖₊ : ℝ≥0∞)
      = (‖∫ xᵢ : ℝ in Set.Iic (x i), deriv (u ∘ update x i) xᵢ‖₊ : ℝ≥0∞) := by
        have h3u : ContDiff ℝ 1 (u ∘ update x i) := hu.comp (contDiff_update 1 x i)
        have h4u : HasCompactSupport (u ∘ update x i)
        · apply h2u.comp_closedEmbedding
          -- `update x i` is a closed embedding -- make this a lemma
          have h5u : LeftInverse (fun v ↦ v i) (update x i) := fun t ↦ update_same i t x
          apply h5u.closedEmbedding
          · exact continuous_apply i
          · have : Continuous (fun t : ℝ ↦ (x, t)) := continuous_const.prod_mk continuous_id
            exact (continuous_update i).comp this
        rw [h4u.integral_deriv_eq h3u (x i)]
        simp
    _ ≤ ∫⁻ xᵢ : ℝ in Set.Iic (x i), ‖deriv (u ∘ update x i) xᵢ‖₊ :=
        nnnorm_integral_le_lintegral_nnnorm _
    _ ≤ ∫⁻ (xᵢ : ℝ), ↑‖fderiv ℝ u (update x i xᵢ)‖₊ := ?_
  gcongr with y; swap; exact Measure.restrict_le_self
  calc ‖deriv (u ∘ update x i) y‖₊ = ‖fderiv ℝ u (update x i y) (deriv (update x i) y)‖₊ := by
        rw [fderiv.comp_deriv _ (hu.differentiable le_rfl).differentiableAt
          (hasDerivAt_update y).differentiableAt]
    _ ≤ ‖fderiv ℝ u (update x i y)‖₊ * ‖deriv (update x i) y‖₊ :=
        ContinuousLinearMap.le_op_nnnorm ..
    _ ≤ ‖fderiv ℝ u (update x i y)‖₊ := by simp [deriv_update, Pi.nnnorm_single]

-- /-- The Sobolev inequality for the Lebesgue l=integral(?) -/
-- theorem lintegral_pow_le :
--     ∫⁻ x, ‖u x‖₊ ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) ≤
--       (∫⁻ x, ‖fderiv ℝ u x‖₊) ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) :=
--   by sorry

end Sobolev
