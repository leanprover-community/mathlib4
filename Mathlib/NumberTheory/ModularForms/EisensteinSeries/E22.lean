/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.IccSums
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Eisenstein Series E2

We define the Eisenstein series `E2` of weight `2` and level `1` as a limit of partial sums
over non-symmetric intervals.

-/

open UpperHalfPlane hiding I

open ModularForm EisensteinSeries  TopologicalSpace  intervalIntegral
  Metric Filter Function Complex MatrixGroups Finset ArithmeticFunction Set

open scoped Interval Real Topology BigOperators Nat

noncomputable section

variable {α β γ : Type*}

variable [CommMonoid α] [TopologicalSpace α]

@[to_additive]
def HasProdFilter (L : Filter (Finset β)) (f : β → α) (a : α) : Prop :=
  Tendsto (fun s : Finset β ↦ ∏ b ∈ s, f b) L (𝓝 a)

@[to_additive
/-- `SummableAlongFilter f` means that `f` has some (infinite) sum. -/]
def MultipliableFilter (L : Filter (Finset β)) (f : β → α) : Prop :=
  ∃ a, HasProdFilter L f a

open scoped Classical in
/-- `∏' i, f i` is the product of `f` if along the filter `L` if it exists or 1 otherwise. -/
@[to_additive /-- `∑' i, f i` is the sum  of `f` if along the filter `L` if it exists
 or 0 otherwise. -/]
noncomputable irreducible_def tprodFilter {β} (L : Filter (Finset β)) (f : β → α) :=
  if h : MultipliableFilter L f then
   h.choose
  else 1

@[inherit_doc tprod]
notation3 "∏' " "[" L "]" (...)", "r:67:(scoped f => tprodFilter L f) => r
@[inherit_doc tsumFilter]
notation3 "∑' " "[" L "]" (...)", "r:67:(scoped f => tsumFilter L f) => r

variable (L : Filter (Finset β)) {f : β → α} {a : α}

@[to_additive]
theorem HasProdFilter.multipliableFilter (h : HasProdFilter L f a) : MultipliableFilter L f :=
  ⟨a, h⟩

@[to_additive]
theorem tprodFilter_eq_one_of_not_multipliableFilter (h : ¬MultipliableFilter L f) :
    ∏'[L] b, f b = 1 := by
  simp [tprodFilter_def, h]

@[to_additive, simp]
lemma tprod_one_eq_one {β : Type*} (L : Filter (Finset β)) : ∏'[L] b, (1 : α) = 1 := by
  simp [tprodFilter_def, MultipliableFilter, HasProdFilter]
  sorry



@[to_additive]
theorem MultipliableFilter.hasProdFilter (ha : MultipliableFilter L f) :
    HasProdFilter L f (∏'[L] b, f b) := by
  simp only [tprodFilter_def, ha, dite_true]
  apply ha.choose_spec

@[to_additive]
theorem HasProdFilter.unique {a₁ a₂ : α} [T2Space α] [L.NeBot] :
    HasProdFilter L f a₁ → HasProdFilter L f a₂ → a₁ = a₂ := by
  classical exact tendsto_nhds_unique

variable [T2Space α]

@[to_additive]
theorem HasProdFilter.tprodFilter_eq (ha : HasProdFilter L f a) [L.NeBot] : ∏'[L] b, f b = a :=
  (MultipliableFilter.hasProdFilter L ha.multipliableFilter).unique L ha


@[to_additive]
theorem MultipliableFilter.hasProdFilter_iff (h : MultipliableFilter L f) [L.NeBot] :
    HasProdFilter L f a ↔ ∏'[L] b, f b = a := by
  apply Iff.intro
  · intro h
    apply h.tprodFilter_eq
  · intro H
    have := h.hasProdFilter
    rw [H] at this
    exact this

@[to_additive]
protected theorem HasProdFilter.map [CommMonoid γ] [TopologicalSpace γ] (hf : HasProdFilter L f a) {G}
    [FunLike G α γ] [MonoidHomClass G α γ] (g : G) (hg : Continuous g) :
    HasProdFilter L (g ∘ f) (g a) := by
  have : (g ∘ fun s : Finset β ↦ ∏ b ∈ s, f b) = fun s : Finset β ↦ ∏ b ∈ s, (g ∘ f) b :=
    funext <| map_prod g _
  unfold HasProdFilter
  rw [← this]
  exact (hg.tendsto a).comp hf

variable {γ : Type*} [NonUnitalNonAssocSemiring γ] [TopologicalSpace γ] [IsTopologicalSemiring γ] {f : β → γ}
[T2Space γ]

theorem HasSumFilter.mul_left (a a₁ : γ) (L : Filter (Finset β)) (h : HasSumFilter L f a₁) :
      HasSumFilter L (fun i ↦ a * f i) (a * a₁) := by
  simpa using h.map L (AddMonoidHom.mulLeft a)  (continuous_const.mul continuous_id)

theorem SummableFilter.mul_left (a) (hf : SummableFilter L f) : SummableFilter L fun i ↦ a * f i :=
  (hf.hasSumFilter.mul_left _).summableFilter

protected theorem SummableFilter.tsumFilter_mul_left {α : Type*} [DivisionSemiring α]
    [TopologicalSpace α] [T2Space α] [IsTopologicalSemiring α] (a : α) (f : β → α)
    [L.NeBot] (hf : SummableFilter L f) :
    ∑'[L] i, a * f i = a * ∑'[L] i, f i :=
  ((hf.hasSumFilter.mul_left) a).tsumFilter_eq

theorem hasSumFilter_mul_left_iff {α : Type*} [DivisionSemiring α] [TopologicalSpace α] [T2Space α]
    [L.NeBot] [IsTopologicalSemiring α] {a a₁ : α} (h : a ≠ 0) (f : β → α) :
      HasSumFilter L (fun i ↦ a * f i) (a * a₁) ↔ HasSumFilter L f a₁ :=
  ⟨fun H ↦ by simpa only [inv_mul_cancel_left₀ h] using H.mul_left a⁻¹, HasSumFilter.mul_left _ _ L⟩

theorem summableFilter_mul_left_iff {α : Type*} [DivisionSemiring α] [TopologicalSpace α] [T2Space α]
    [ L.NeBot] [ IsTopologicalSemiring α] {a : α}  (h : a ≠ 0) (f : β → α) :
      (SummableFilter L fun i ↦ a * f i) ↔ SummableFilter L f :=
  ⟨fun H ↦ by simpa only [inv_mul_cancel_left₀ h] using H.mul_left L a⁻¹ , fun H ↦ H.mul_left L _⟩

lemma tprodFilter_mul_left {α : Type*} [DivisionSemiring α] [TopologicalSpace α] [T2Space α]
    [ L.NeBot] [ IsTopologicalSemiring α] (a : α) (f : β → α) :
    ∑'[L] b, a * f b = a * ∑'[L] b, f b := by
  classical
  exact if hf : SummableFilter L f then hf.tsumFilter_mul_left L a
  else if ha : a = 0 then by simp [ha];  apply tsum_zero_eq_zero
  else by rw [tsumFilter_eq_zero_of_not_summableFilter L hf,
              tsumFilter_eq_zero_of_not_summableFilter L
                (mt (summableFilter_mul_left_iff L ha f).mp hf), mul_zero]


omit [T2Space α] in
@[to_additive]
theorem MultipliableFilter.mul {f g : β → α} [ContinuousMul α] (hf : MultipliableFilter L f)
    (hg : MultipliableFilter L g) :
    MultipliableFilter L (fun b ↦ f b * g b) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a * b
  simp [HasProdFilter] at *
  have := Tendsto.mul (ha) (hb)
  apply this.congr
  intro s
  exact Eq.symm prod_mul_distrib

omit [T2Space α] in
@[to_additive]
lemma mulipliable_iff_multipliableFilter_atTop {f : β → α} :
    Multipliable f ↔ MultipliableFilter atTop f := by
  simp [Multipliable, MultipliableFilter, HasProd, HasProdFilter]

omit [T2Space α] in
@[to_additive]
lemma hasProd_iff_hasProdFilter_atTop {f : β → α} {a : α} :
    HasProd f a ↔ HasProdFilter atTop f a := by
  simp [HasProd, HasProdFilter]

lemma tprod_eq_tproFilter_atTop (f : β → α) : ∏' [atTop] b, f b = ∏' b, f b := by
  by_cases h : MultipliableFilter atTop f
  · have := h.hasProdFilter
    rw [this.tprodFilter_eq atTop]
    rw [← mulipliable_iff_multipliableFilter_atTop] at h
    have H := h.hasProd
    rw [← hasProd_iff_hasProdFilter_atTop] at this
    apply HasProd.unique this H
  · rw [tprodFilter_eq_one_of_not_multipliableFilter atTop h, tprod_eq_one_of_not_multipliable h]

variable {ι : Type*} {X : α → Type*} [∀ x, CommMonoid (X x)] [∀ x, TopologicalSpace (X x)]

omit [CommMonoid α] [TopologicalSpace α] [T2Space α] in
@[to_additive]
theorem Pi.hasProdFilter {f : β → ∀ x, X x} {g : ∀ x, X x} :
    HasProdFilter L f g ↔ ∀ x, HasProdFilter L (fun i ↦ f i x) (g x) := by
  simp only [HasProdFilter, tendsto_pi_nhds, prod_apply]

omit [CommMonoid α] [TopologicalSpace α] [T2Space α] in
@[to_additive]
theorem Pi.multipliableFilter {f : β → ∀ x, X x} :
    MultipliableFilter L f ↔ ∀ x, MultipliableFilter L fun i ↦ f i x := by
  simp only [MultipliableFilter, Pi.hasProdFilter, Classical.skolem]

omit [CommMonoid α] [TopologicalSpace α] [T2Space α] in
@[to_additive]
theorem tprodFilter_apply [∀ x, T2Space (X x)] {f : β → ∀ x, X x} {x : α} [L.NeBot]
    (hf : MultipliableFilter L f) : (∏'[L] i, f i) x = ∏'[L] i, f i x :=
  ((Pi.hasProdFilter L).mp hf.hasProdFilter x).tprodFilter_eq.symm

def Icc_filter : Filter (Finset ℤ) := atTop.map (fun N : ℕ ↦ Icc (-(N : ℤ)) N)

def Ico_filter : Filter (Finset ℤ) := atTop.map (fun N : ℕ ↦ Ico (-(N : ℤ)) N)

instance : NeBot (Icc_filter) := by
  simp [Icc_filter, Filter.NeBot.map]

instance : NeBot (Ico_filter) := by
  simp [Ico_filter, Filter.NeBot.map]

@[to_additive]
lemma prodFilter_int_atTop_eq_Icc_filter {f : ℤ → α}
    (hf : MultipliableFilter atTop f) : ∏'[atTop] b, f b  = ∏'[Icc_filter] b, f b := by
  have := (hf.hasProdFilter).comp tendsto_Icc_atTop_atTop
  simp only [Icc_filter] at *
  apply symm
  apply HasProdFilter.tprodFilter_eq
  simp only [HasProdFilter, tendsto_map'_iff]
  apply this.congr
  simp


@[to_additive]
lemma prodFilter_int_atTop_eq_Ico_filter {f : ℤ → α}
    (hf : MultipliableFilter atTop f) : ∏'[atTop] b, f b  = ∏'[Ico_filter] b, f b := by
  have := (hf.hasProdFilter).comp tendsto_Ico_atTop_atTop
  simp only [Ico_filter] at *
  apply symm
  apply HasProdFilter.tprodFilter_eq
  simp only [HasProdFilter, tendsto_map'_iff]
  apply this.congr
  simp

@[to_additive] --this needs a hyp, but lets see what the min it needs
lemma multipliableFilter_int_Icc_eq_Ico_filter {α : Type*} {f : ℤ → α} [CommGroup α]
    [TopologicalSpace α] [ContinuousMul α] [T2Space α] (hf : MultipliableFilter Icc_filter f)
    (hf2 : Tendsto (fun N : ℕ ↦ (f ↑N)⁻¹) atTop (𝓝 1)) : MultipliableFilter Ico_filter f := by
  have := (hf.hasProdFilter)
  apply HasProdFilter.multipliableFilter
  simp only [Ico_filter] at *
  simp only [HasProdFilter, tendsto_map'_iff] at *
  apply Filter.Tendsto_of_div_tendsto_one _ (by apply this)
  conv =>
    enter [1, N]
    simp
    rw [prod_Icc_eq_prod_Ico_succ _ (by omega)]
    simp
  apply hf2

@[to_additive] --this needs a hyp, but lets see what the min it needs
lemma prodFilter_int_Icc_eq_Ico_filter {α : Type*} {f : ℤ → α} [CommGroup α] [TopologicalSpace α]
    [ContinuousMul α] [T2Space α] (hf : MultipliableFilter Icc_filter f)
    (hf2 : Tendsto (fun N : ℕ ↦ (f ↑N)⁻¹) atTop (𝓝 1)) :
    ∏'[Icc_filter] b, f b  = ∏'[Ico_filter] b, f b := by
  have := (hf.hasProdFilter)
  simp only [Ico_filter] at *
  apply symm
  apply HasProdFilter.tprodFilter_eq
  simp only [HasProdFilter, tendsto_map'_iff] at *
  apply Filter.Tendsto_of_div_tendsto_one _ (by apply this)
  conv =>
    enter [1, N]
    simp
    rw [prod_Icc_eq_prod_Ico_succ _ (by omega)]
    simp
  apply hf2


/-- This is an auxilary summand used to define the Eisenstein serires `G2`. -/
def e2Summand (m : ℤ) (z : ℍ) : ℂ := ∑' n, eisSummand 2 ![m, n] z

lemma e2Summand_summable (m : ℤ) (z : ℍ) : Summable (fun n => eisSummand 2 ![m, n] z) := by
  apply (linear_right_summable z m (k := 2) (by omega)).congr
  simp [eisSummand]

@[simp]
lemma e2Summand_zero_eq_riemannZeta_two (z : ℍ) : e2Summand 0 z = 2 * riemannZeta 2 := by
  simpa [e2Summand, eisSummand] using
    (two_riemannZeta_eq_tsum_int_inv_even_pow (k := 2) (by omega) (by simp)).symm

theorem e2Summand_even (z : ℍ) (n : ℤ) : e2Summand n z = e2Summand (-n) z := by
  simp only [e2Summand, ← tsum_int_eq_tsum_neg (fun a => eisSummand 2 ![-n, a] z)]
  congr
  ext b
  simp only [eisSummand, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, Int.cast_neg, neg_mul, inv_inj]
  rw_mod_cast [Int.cast_neg]
  ring

/-- The Eisenstein series of weight `2` and level `1` defined as the limit as `N` tends to
infinity of the partial sum of `m` in `[N,N)` of `e2Summand m`. This sum over symmetric
intervals is handy in showing it is Cauchy. -/
def G2 : ℍ → ℂ := fun z => ∑'[Icc_filter] m, e2Summand m z

/-- The normalised Eisenstein series of weight `2` and level `1`. -/
def E2 : ℍ → ℂ := (1 / (2 * riemannZeta 2)) •  G2

/-- This function measures the defect in `E2` being a modular form. -/
def D2 (γ : SL(2, ℤ)) : ℍ → ℂ := fun z => (2 * π * I * γ 1 0) / (denom γ z)

lemma G2_partial_sum_eq (z : ℍ) (N : ℕ) : ∑ m ∈ Icc (-N : ℤ) N, e2Summand m z =
    (2 * riemannZeta 2) + (∑ m ∈ range N, -8 * π ^ 2  *
    ∑' n : ℕ+, n  * cexp (2 * π * I * (m + 1) * z) ^ (n : ℕ)) := by
  rw [sum_Icc_of_even_eq_range (e2Summand_even z), Finset.sum_range_succ', mul_add]
  nth_rw 2 [two_mul]
  ring_nf
  have (a : ℕ) := EisensteinSeries.qExpansion_identity_pnat (k := 1) (by omega)
    ⟨(a + 1) * z, by simpa [show  0 < a + (1 : ℝ) by positivity] using z.2⟩
  simp only [coe_mk_subtype, add_comm, Nat.reduceAdd, one_div, mul_comm, mul_neg, even_two,
    Even.neg_pow, Nat.factorial_one, Nat.cast_one, div_one, pow_one, e2Summand, eisSummand,
    Nat.cast_add, Fin.isValue, Matrix.cons_val_zero, Int.cast_add, Int.cast_natCast, Int.cast_one,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, mul_sum, Int.cast_zero,
    zero_mul, add_zero] at *
  congr
  · simpa using (two_riemannZeta_eq_tsum_int_inv_even_pow (k := 2) (by omega) (by simp)).symm
  · ext a
    norm_cast at *
    simp_rw [this a, ← tsum_mul_left, ← tsum_neg,ofReal_mul, ofReal_ofNat, mul_pow, I_sq, neg_mul,
      one_mul, Nat.cast_add, Nat.cast_one, mul_neg, ofReal_pow]
    grind

private lemma aux_tsum_identity (z : ℍ) : ∑' m : ℕ, (-8 * π ^ 2  *
    ∑' n : ℕ+, n * cexp (2 * π * I * (m + 1) * z) ^ (n : ℕ))  =
    -8 * π ^ 2 * ∑' (n : ℕ+), (σ 1 n) * cexp (2 * π * I * z) ^ (n : ℕ) := by
  have := tsum_prod_pow_cexp_eq_tsum_sigma 1 z
  rw [tsum_pnat_eq_tsum_succ (f:= fun d =>
    ∑' (c : ℕ+), (c ^ 1 : ℂ) * cexp (2 * π * I * d * z) ^ (c : ℕ))] at this
  simp [← tsum_mul_left, ← this]

private lemma aux_G2_tendsto (z : ℍ) : Tendsto (fun N ↦ ∑ x ∈ range N, -8 * π ^ 2 *
    ∑' (n : ℕ+), n * cexp (2 * π * I * (x + 1) * z) ^ (n : ℕ)) atTop
    (𝓝 (-8 * π ^ 2 * ∑' (n : ℕ+), ((σ 1) n) * cexp (2 * π * I * z) ^ (n : ℕ))) := by
  rw [← aux_tsum_identity]
  have hf : Summable fun m : ℕ => (-8 * π ^ 2 *
      ∑' n : ℕ+, n ^ ((2 - 1)) * cexp (2 * π * I * (m + 1) * z) ^ (n : ℕ)) := by
    apply Summable.mul_left
    have := (summable_prod_aux 1 z).prod
    have h0 := summable_pnat_iff_summable_succ
      (f := fun b ↦ ∑' (c : ℕ+), c * cexp (2 * π * I * b * z) ^ (c : ℕ))
    simp only [pow_one, cexp_pow_aux, Nat.cast_add, Nat.cast_one, Nat.add_one_sub_one] at *
    rw [← h0]
    apply this
  simpa using (hf.hasSum).comp tendsto_finset_range

lemma G2_cauchy (z : ℍ) : CauchySeq (fun N : ℕ ↦ ∑ m ∈ Icc (-N : ℤ) N, e2Summand m z) := by
  conv =>
    enter [1, n]
    rw [G2_partial_sum_eq]
  apply CauchySeq.const_add
  apply Tendsto.cauchySeq (x := -8 * π ^ 2 * ∑' (n : ℕ+), (σ 1 n) * cexp (2 * π * I * z) ^ (n : ℕ))
  simpa using aux_G2_tendsto z


def G2' : ℍ → ℂ := fun z => ∑'[Icc_filter] m, e2Summand m z

lemma SummableFilter_G2 (z : ℍ) : SummableFilter Icc_filter (fun m : ℤ => e2Summand m z) := by
  simp [SummableFilter, HasSumFilter, Icc_filter ]
  have := G2_cauchy z
  have := cauchySeq_tendsto_of_complete this
  simpa using this



lemma G2_q_exp (z : ℍ) : G2 z =
    (2 * riemannZeta 2) - 8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * cexp (2 * π * I * z) ^ (n : ℕ) := by
  rw [G2, sub_eq_add_neg]
  apply  HasSumFilter.tsumFilter_eq
  simp only [HasSumFilter, Icc_filter, tendsto_map'_iff]
  conv =>
    enter [1, N]
    simp [G2_partial_sum_eq z N]
  apply Filter.Tendsto.add (by simp) (by simpa using aux_G2_tendsto z)

section transform

private lemma tendsto_zero_of_cauchySeq_sum_Icc {F : Type*} [NormedRing F] [NormSMulClass ℤ F]
    {f : ℤ → F} (hc : CauchySeq fun N : ℕ ↦ ∑ m ∈ Icc (-N : ℤ) N, f m) (hs : ∀ n , f n = f (-n)) :
    Tendsto f atTop (𝓝 0) := by
  simp only [cauchySeq_iff_le_tendsto_0, Metric.tendsto_atTop, gt_iff_lt, ge_iff_le,
    dist_zero_right, Real.norm_eq_abs] at *
  obtain ⟨g, hg, H, Hg⟩ := hc
  intro ε hε
  obtain ⟨N, hN⟩ := (Hg (2 * ε) (by positivity))
  refine ⟨N + 1, fun n hn => ?_⟩
  have H2 := (H n.natAbs (n -1).natAbs N (by omega) (by omega))
  rw [sum_Icc_add_endpoints f (by omega)] at H2
  have h1 : |n| = n := by
    rw [abs_eq_self]
    omega
  have h2 : |n - 1| = n - 1 := by
    rw [abs_eq_self, Int.sub_nonneg]
    omega
  have := norm_smul (2 : ℤ) (f n)
  simp only [Nat.cast_natAbs, h1, Int.cast_eq, ← hs n, (two_mul (f n)).symm, neg_sub, h2,
    Int.cast_sub, Int.cast_one, dist_add_self_left, zsmul_eq_mul, Int.cast_ofNat] at *
  simpa [this, Int.norm_eq_abs] using lt_of_le_of_lt (le_trans H2 (le_abs_self (g N)))
    (hN N (by rfl))


lemma SummableFilter_G2_Ico (z : ℍ) : SummableFilter Ico_filter (fun m : ℤ => e2Summand m z) := by
  apply summableFilter_int_Icc_eq_Ico_filter (SummableFilter_G2 z)
  have h0 := tendsto_zero_of_cauchySeq_sum_Icc (G2_cauchy z) (by apply e2Summand_even)
  simpa using  (Filter.Tendsto.neg h0).comp tendsto_natCast_atTop_atTop

lemma G2_eq_Ico (z : ℍ) : G2 z = ∑'[Ico_filter] m, e2Summand m z := by
  rw [G2, sumFilter_int_Icc_eq_Ico_filter (SummableFilter_G2 z) ?_]
  have h0 := tendsto_zero_of_cauchySeq_sum_Icc (G2_cauchy z) (by apply e2Summand_even)
  simpa using  (Filter.Tendsto.neg h0).comp tendsto_natCast_atTop_atTop

lemma aux_tendsto_Ico (z : ℍ) :
    Tendsto (fun (N : ℕ) ↦ ∑ m ∈ Ico (-(N : ℤ)) N, e2Summand m z) atTop (𝓝 (G2 z)) := by
  have := SummableFilter_G2_Ico z
  obtain ⟨a, ha⟩ := this
  have HA := ha
  rw [SummableFilter.hasSumFilter_iff] at ha
  · rw [G2_eq_Ico z, ha]
    simp [HasSumFilter, Ico_filter, tendsto_map'_iff] at *
    apply HA.congr
    simp
  · apply SummableFilter_G2_Ico

/- lemma G2_Ico (z : ℍ) : G2 z = limUnder atTop (fun N : ℕ ↦ ∑ m ∈ Ico (-N : ℤ) N, e2Summand m z) := by
  apply symm
  rw [G2, Filter.Tendsto.limUnder_eq]
  apply Tendsto_of_sub_tendsto_zero _ (CauchySeq.tendsto_limUnder (G2_cauchy z))
  have h0 := tendsto_zero_of_cauchySeq_sum_Icc (G2_cauchy z) (by apply e2Summand_even)
  conv =>
    enter [1, N]
    rw [Pi.sub_apply, sum_Icc_eq_sum_Ico_succ _ (by omega), sub_add_cancel_left]
  simpa using  (Filter.Tendsto.neg h0).comp tendsto_natCast_atTop_atTop -/

lemma aux_cauchySeq_Ico (z : ℍ) : CauchySeq fun N : ℕ ↦ ∑ m ∈ Ico (-N : ℤ) N, e2Summand m z := by
  apply Filter.Tendsto.cauchySeq
  apply (aux_tendsto_Ico z)

theorem aux_sum_Ico_S_indentity (z : ℍ) (N : ℕ) :
    ((z : ℂ) ^ 2)⁻¹ * (∑ x ∈ Ico (-N : ℤ) N, ∑' (n : ℤ), (((x : ℂ) * (-↑z)⁻¹ + n) ^ 2)⁻¹) =
    ∑' (n : ℤ), ∑ x ∈ Ico (-N : ℤ) N, (((n : ℂ) * z + x) ^ 2)⁻¹ := by
  simp_rw [inv_neg, mul_neg]
  rw [Finset.mul_sum, Summable.tsum_finsetSum]
  · apply sum_congr rfl fun n hn => ?_
    rw [← tsum_mul_left, ← tsum_int_eq_tsum_neg]
    apply tsum_congr fun d => ?_
    rw [← mul_inv,  ← mul_pow, ← neg_pow_two]
    congr
    field_simp [ne_zero z]
    simp
  · exact fun i hi => linear_left_summable (ne_zero z) (i : ℤ) (k := 2) (by omega)

lemma G2_S_act (z : ℍ) :
    Tendsto (fun N : ℕ => (∑' (n : ℤ), ∑ m ∈ Ico (-N : ℤ) N, (1 / ((n : ℂ) * z + m) ^ 2))) atTop
    (𝓝 ((z.1 ^ 2)⁻¹ * G2 (ModularGroup.S • z))) := by
  rw [modular_S_smul, G2_eq_Ico]
  congr
  ext N
  simpa [UpperHalfPlane.coe, e2Summand, eisSummand, UpperHalfPlane.mk] using
    (aux_sum_Ico_S_indentity z N)

lemma Ico_succ_eq (b : ℕ) : Finset.Ico (-(b+1) : ℤ) (b+1) = Finset.Ico (-(b : ℤ)) (b) ∪
    {-((b+1) : ℤ), (b : ℤ)} :=  by
  ext n
  simp only [neg_add_rev, Int.reduceNeg, Finset.mem_Ico, add_neg_le_iff_le_add, Finset.union_insert,
    Finset.union_singleton, neg_le_self_iff, Nat.cast_nonneg, Finset.Ico_insert_right,
    Finset.mem_insert, Finset.mem_Icc]
  omega

theorem telescope_aux (z : ℂ) (m : ℤ) (b : ℕ) :
    ∑ n ∈ Ico (-b : ℤ) b, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)) =
    1 / (m * z - b) - 1 / (m * z + b) := by
  induction' b  with b ihb
  · aesop
  · simp only [Nat.cast_add, Nat.cast_one, one_div, Finset.sum_sub_distrib] at *
    rw [Ico_succ_eq, Finset.sum_union (by simp), Finset.sum_union (by simp),
      Finset.sum_pair (by omega), Finset.sum_pair (by omega), add_sub_add_comm]
    simp only [ihb, neg_add_rev, Int.reduceNeg, Int.cast_add, Int.cast_neg, Int.cast_one,
      Int.cast_natCast]
    ring

theorem tendstozero_inv_linear (z : ℂ) (b : ℤ) :
    Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * z + d)) atTop (𝓝 0) := by
  apply Asymptotics.IsBigO.trans_tendsto ?_ tendsto_inverse_atTop_nhds_zero_nat
  have := (Asymptotics.isBigO_sup.mp (Int.cofinite_eq ▸ linear_inv_isBigO_right b z)).2
  simpa [← Nat.map_cast_int_atTop, Asymptotics.isBigO_map] using this

theorem tendstozero_inv_linear_sub (z : ℍ) (b : ℤ) :
    Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * z - d)) atTop (𝓝 0) := by
  have := (tendstozero_inv_linear z (-b)).neg
  simp only [Int.cast_neg, neg_mul, one_div, neg_zero, ← inv_neg] at *
  exact this.congr (fun _ => by ring)

lemma limUnder_sum_eq_zero (z : ℍ) (m : ℤ) : limUnder atTop (fun N : ℕ =>
    ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)), (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1))) = 0 := by
  apply Filter.Tendsto.limUnder_eq
  conv =>
    enter [1, N]
    rw [telescope_aux z m N]
  simpa using Filter.Tendsto.sub (tendstozero_inv_linear_sub z m) (tendstozero_inv_linear z m)


theorem int_tsum_pNat {α : Type*} [UniformSpace α] [CommRing α] [IsUniformAddGroup α]
  [CompleteSpace α] [T2Space α] {f : ℤ → α} (hf2 : Summable f) :
  ∑' n, f n = f 0 + ∑' n : ℕ+, f n + ∑' m : ℕ+, f (-m) := by
  rw [summable_int_iff_summable_nat_and_neg_add_zero, tsum_of_add_one_of_neg_add_one] at *
  · simp only [neg_add_rev, Int.reduceNeg, tsum_pnat_eq_tsum_succ (f := fun n => f n), Nat.cast_add,
    Nat.cast_one, tsum_pnat_eq_tsum_succ (f := fun n => f (-n)), add_left_inj]
    ring
  · have hf21 := hf2.1
    rw [← summable_nat_add_iff (k := 1)] at hf21
    simpa using hf21
  · simpa using hf2.2

lemma summable_pnat_iff_summable_nat {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] {f : ℕ → G} : Summable (fun n : ℕ+ => f n) ↔ Summable f := by
  rw [summable_pnat_iff_summable_succ , summable_nat_add_iff]

private lemma linear_sub_linear_eq (z : ℍ) (a b m : ℤ) (hm : m ≠ 0) :
    1 / ((m : ℂ) * z + a) - 1 / (m * z + b) = (b - a) * (1 / ((m * z + a) * (m * z + b))) := by
  rw [← one_div_mul_sub_mul_one_div_eq_one_div_add_one_div]
  · simp only [one_div, add_sub_add_left_eq_sub, mul_inv_rev]
    ring
  · simpa using UpperHalfPlane.linear_ne_zero z (cd := ![m, a]) (by simp [hm])
  · simpa using UpperHalfPlane.linear_ne_zero z (cd := ![m, b]) (by simp [hm])

lemma summable_one_div_linear_sub_one_div_linear (z : ℍ) (a b : ℤ) :
    Summable fun m : ℤ ↦ 1 / (m * (z : ℂ) + a) - 1 / (m * z + b) := by
  have := Summable.mul_left  (b - a : ℂ) (summable_linear_mul_linear (ne_zero z) a b)
  rw [← Finset.summable_compl_iff (s := {0})] at *
  apply this.congr
  intro m
  rw [linear_sub_linear_eq z a b m (by grind)]
  simp

private lemma aux_tsum_identity_2 (z : ℍ) (d : ℕ+) :
    ∑' (m : ℤ), (1 / ((m : ℂ) * z - d) - 1 / (m * z + d)) = -(2 / d) +
    ∑' m : ℕ+, (1 / ((m : ℂ) * z - d) + 1 / (-m * z + -d) - 1 / ((m : ℂ) * z + d) -
    1 / (-m * z + d)) := by
  rw [eq_neg_add_iff_add_eq (b := 2 / (d : ℂ)), int_tsum_pNat]
  · simp only [Int.cast_zero, zero_mul, zero_sub, one_div, zero_add, Int.cast_natCast, Int.cast_neg,
      neg_mul]
    ring_nf
    rw [←  Summable.tsum_add]
    · grind
    · apply (summable_pnat_iff_summable_nat.mpr ((summable_int_iff_summable_nat_and_neg.mp
        (summable_one_div_linear_sub_one_div_linear z (-d) d)).1)).congr
      grind [Int.cast_natCast, Int.cast_neg, one_div]
    · apply (summable_pnat_iff_summable_nat.mpr ((summable_int_iff_summable_nat_and_neg.mp
        (summable_one_div_linear_sub_one_div_linear z (-d) d)).2)).congr
      grind [Int.cast_neg, Int.cast_natCast, neg_mul, one_div]
  · apply (summable_one_div_linear_sub_one_div_linear z (-d) d).congr
    grind [Int.cast_neg, Int.cast_natCast, one_div, sub_left_inj, inv_inj]

private lemma aux_tsum_identity_3 (z : ℍ) (d : ℕ+) :
    ∑' m : ℕ+, ((1 / ((m : ℂ) * z - d) + 1 / (-m * z + -d)) - (1 / (m * z + d)) -
    1 / (-m * z + d)) = (2 / z) * ∑' m : ℕ+, ((1 / (-(d : ℂ) / z - m) + 1 / (-d / z + m))) := by
  rw [← Summable.tsum_mul_left]
  · congr
    funext m
    simp_rw [sub_eq_add_neg, ← div_neg]
    ring_nf
    rw [add_comm]
    field_simp [ne_zero z]
  · have := (Summable_cotTerm (x := -d / (z : ℂ))
      (by simpa using int_div_upperHalfPlane_mem_integerComplement z (-d) (by simp at *)))
    simp only [cotTerm, one_div] at *
    conv at this =>
      enter [1, n]
      rw [show ((n : ℂ) + 1) = (n + 1 : ℕ) by simp]
    rw [summable_nat_add_iff (k := 1)
      (f := fun n => (-d / (z : ℂ) - (n))⁻¹ + (-d / (z : ℂ) + (n))⁻¹)] at this
    apply this.subtype

lemma pnat_div_upper (n : ℕ+) (z : ℍ) : 0 < (-(n : ℂ) / z).im := by
  simp only [div_im, neg_im, natCast_im, neg_zero, coe_re, zero_mul,
    zero_div, neg_re, natCast_re, coe_im, neg_mul, zero_sub, Left.neg_pos_iff, div_neg_iff]
  right
  simpa using ⟨z.2, ne_zero z⟩

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

lemma tendsto_zero_geometric_tsum {r : 𝕜} (hr : ‖r‖ < 1) :
    Tendsto (fun m : ℕ+ => ∑' (n : ℕ+), r ^ (n * m : ℕ)) atTop (𝓝 0) := by
  have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (g := fun (n : ℕ+) => 0)
    (f := fun d n : ℕ+ => r ^ (n * d : ℕ)) (bound := fun n : ℕ+ => (‖r ^ (n : ℕ)‖))
  simp only [tsum_zero] at this
  apply this
  · have hs : Summable fun n : ℕ ↦ ‖r ^ n‖ := by simp [hr]
    apply hs.subtype
  · intro k
    have ht : Tendsto (fun x : ℕ ↦ r ^ (k * x)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp [pow_mul, tendsto_pow_atTop_nhds_zero_iff, pow_lt_one_iff_of_nonneg, hr]
    exact tendsto_comp_val_Ioi_atTop.mpr ht
  · simp only [eventually_atTop, ge_iff_le, norm_pow]
    exact ⟨1, fun b hb k =>
      pow_le_pow_of_le_one (norm_nonneg _) hr.le (Nat.le_mul_of_pos_right k hb)⟩

lemma aux_tendsto_tsum_cexp_pnat (z : ℍ) :
    Tendsto (fun N : ℕ+ => ∑' (n : ℕ+), cexp (2 * π * I * (-N / z)) ^ (n : ℕ)) atTop (𝓝 0) := by
  have := tendsto_zero_geometric_tsum (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨-1 / z,
    by simpa using (pnat_div_upper 1 z)⟩)
  simp only [← exp_nsmul, mul_neg, neg_div] at *
  apply this.congr fun n => ?_
  congr
  grind [one_div, coe_mk_subtype, mul_neg, smul_neg, nsmul_eq_mul, Nat.cast_mul, neg_inj]

private theorem aux_tendsto_tsum (z : ℍ) : Tendsto (fun n : ℕ => (2 / z *
    ∑' (m : ℕ+), (1 / (-(n : ℂ) / z - m) + 1 / (-n / z + m)))) atTop (𝓝 (-2 * π * I / z)) := by
  suffices Tendsto (fun n : ℕ+ => (2 / (z : ℂ) * ∑' (m : ℕ+),
      (1 / (-(n : ℂ) / z - m) + 1 / (-n / z + m)))) atTop (𝓝 (-2 * π * I / z)) by
    rw [← tendsto_comp_val_Ioi_atTop]
    exact this
  have H0 : (fun n : ℕ+ => (2 / z * ∑' (m : ℕ+), (1 / (-(n : ℂ) / z - m) + 1 / (-n / z + m)))) =
      (fun N : ℕ+ => (-2 * π * I / z) - (2 / z * (2 * π * I)) *
      (∑' n : ℕ+, cexp (2 * π * I * (-N / z)) ^ (n : ℕ)) + 2 / N) := by
    ext N
    let Z : ℍ := ⟨-N / z, pnat_div_upper N z⟩
    have h2 := cot_series_rep (UpperHalfPlane.coe_mem_integerComplement Z)
    rw [pi_mul_cot_pi_q_exp, ← sub_eq_iff_eq_add'] at h2
    simp only [coe_mk_subtype, one_div, inv_div, neg_mul, Z] at *
    rw [← h2, ← tsum_zero_pnat_eq_tsum_nat
      (by simpa using norm_exp_two_pi_I_lt_one ⟨-N / z, pnat_div_upper N z⟩), mul_sub]
    field_simp [ne_zero z]
    ring
  rw [H0]
  nth_rw 2 [show -2 * π * I / z = (-2 * π * I / z) - (2 / z * (2 * π * I)) * 0 + 2 * 0 by ring]
  apply Tendsto.add (Tendsto.sub (by simp) ((aux_tendsto_tsum_cexp_pnat z).const_mul _))
  apply Tendsto.const_mul
  have H4 : Tendsto (fun x : ℕ ↦ 1 / (x : ℂ)) atTop (𝓝 0) := by
    simpa using tendstozero_inv_linear z 0
  rw [← tendsto_comp_val_Ioi_atTop] at H4
  simpa using H4

lemma tendsto_tsum_one_div_linear_sub_succ_eq (z : ℍ) : Tendsto (fun N : ℕ+ ↦ ∑ n ∈ Ico (-N : ℤ) N,
    ∑' m : ℤ, (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) atTop (𝓝 (-2 * π * I / z)) := by
  have : (fun N : ℕ+ => ∑ n ∈ (Ico (-N : ℤ) N),
      ∑' m : ℤ , (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1))) = (fun N : ℕ+ =>
      ∑' m : ℤ ,  ∑ n ∈ Ico (-N : ℤ) N, (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1))) := by
    ext n
    rw [Summable.tsum_finsetSum]
    intro i hi
    apply (summable_one_div_linear_sub_one_div_linear z ((i : ℤ)) (i + 1 : ℤ)).congr
    grind [one_div, Int.cast_add, Int.cast_one, sub_right_inj, inv_inj]
  conv at this =>
    enter [2, n]
    conv =>
      enter [1, m]
      rw [telescope_aux z]
    rw [show (n : ℂ) = (n : ℕ+) by simp, aux_tsum_identity_2 z]
  rw [this, show -2 * π * I / z = 0 + -2 * π * I / z by ring]
  apply Tendsto.add
  · have : Tendsto (fun x : ℕ ↦ -(2 / (x : ℂ))) atTop (𝓝 0) := by
      simpa [tendsto_zero_iff_norm_tendsto_zero] using Filter.Tendsto.const_div_atTop
        (g := fun n : ℕ => ‖(n : ℂ)‖) (r := 2) (by simpa using tendsto_natCast_atTop_atTop)
    exact tendsto_comp_val_Ioi_atTop.mpr this
  · conv =>
      enter [1, n]
      rw [aux_tsum_identity_3]
    have HH := aux_tendsto_tsum z
    rw [← tendsto_comp_val_Ioi_atTop] at HH
    exact HH

--these are the two key lemmas
lemma limUnder_tsum_eq (z : ℍ) : limUnder atTop (fun N : ℕ => ∑ n ∈ (Ico (-N : ℤ) N),
    ∑' m : ℤ , (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1))) = -2 * π * I / z := by
  apply Filter.Tendsto.limUnder_eq
  exact tendsto_comp_val_Ioi_atTop.mp (tendsto_tsum_one_div_linear_sub_succ_eq z)

lemma tsum_limUnder_eq (z : ℍ) : ∑' m : ℤ, (limUnder atTop (fun N : ℕ => ∑ n ∈ (Ico (-N : ℤ) N),
    (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1)))) = 0 := by
  convert tsum_zero
  exact limUnder_sum_eq_zero z _

/-- This is an auxiliary correction term for proving how E2 transforms. It allows us to work with
nicer indexing sets for our infinite sums. -/
private def δ (x : Fin 2 → ℤ) : ℂ := if x = ![0,0] then 1 else if x = ![0, -1] then 2 else 0

@[simp]
private lemma δ_eq : δ ![0,0] = 1 := by simp [δ]

private lemma δ_eq2 : δ ![0, -1] = 2 := by simp [δ]

private lemma δ_neq (a b : ℤ) (h : a ≠ 0) : δ ![a,b] = 0 := by
  simp [δ, h]

/-- This gives term gives and alternative infinte sum for G2 which is absolutely convergent. -/
abbrev G2Term (z : ℍ) (m : Fin 2 → ℤ) : ℂ := (((m 0 : ℂ) * z + m 1) ^ 2 * (m 0 * z + m 1 + 1))⁻¹

lemma G_2_alt_summable (z : ℍ) : Summable (fun m => (G2Term z m)) := by
  have hk' : 2 < (3 : ℝ) := by linarith
  apply summable_inv_of_isBigO_rpow_norm_inv hk'
  simpa [pow_three, pow_two, ← mul_assoc] using ((isBigO_linear_add_const_vec z 0 1).mul
    (isBigO_linear_add_const_vec z 0 0)).mul (isBigO_linear_add_const_vec z 0 0)

lemma G_2_alt_summable_δ (z : ℍ) : Summable fun (m : Fin 2 → ℤ) => (G2Term z m + δ m):= by
  let s : Finset (Fin 2 → ℤ) := {![0,0], ![0,-1]}
  rw [← Finset.summable_compl_iff s]
  apply ((G_2_alt_summable z).subtype sᶜ).congr
  intro b
  have hb1 : b.1 ≠ ![0, 0] := by aesop
  have hb2 : b.1 ≠ ![0, -1] := by aesop
  simp [δ, hb1, hb2]

lemma G2_prod_summable1_δ (z : ℍ) (b : ℤ) : Summable fun c ↦ G2Term z ![b,c] + δ ![b, c] := by
  have := G_2_alt_summable_δ z
  simp only [G2Term, Fin.isValue, mul_inv_rev, ← (finTwoArrowEquiv _).symm.summable_iff,
    finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at *
  exact this.prod_factor b

theorem extracted_2_δ (z : ℍ) (b : ℤ) : CauchySeq fun N : ℕ ↦ ∑ n ∈ Ico (-N : ℤ) N,
    (G2Term z ![b,n] + δ ![b, n]) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' (x : ℤ),
        (((b  : ℂ) * z + x + 1)⁻¹ * (((b : ℂ) * z + x) ^ 2)⁻¹  + δ ![b, x]))
  simpa using (G2_prod_summable1_δ z b).hasSum.comp tendsto_Ico_atTop_atTop

theorem extracted_3 (z : ℍ) (b : ℤ) : CauchySeq fun N : ℕ ↦
  ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / ((b : ℂ) * z + n) - 1 / (b * z + n + 1)) := by
  simp_rw [telescope_aux ]
  apply Filter.Tendsto.cauchySeq
  simpa using Filter.Tendsto.sub (tendstozero_inv_linear_sub z b) (tendstozero_inv_linear z b)

lemma extracted_4 (z : ℍ) (b : ℤ) :
    CauchySeq fun N : ℕ ↦ ∑ n ∈ Ico (-N : ℤ) N, (1 / ((b : ℂ) * z + n) ^ 2 ) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' (x : ℤ), ((((b : ℂ) * z + x) ^ 2)⁻¹))
  simpa using ((linear_right_summable z b  (k := 2) (by norm_num)).hasSum).comp
    tendsto_Ico_atTop_atTop

lemma poly_id (z : ℍ) (b n : ℤ) : ((b : ℂ) * z + n + 1)⁻¹ * (((b : ℂ) * z + n) ^ 2)⁻¹ +
    (δ ![b, n]) + (((b : ℂ) * z + n)⁻¹ - ((b : ℂ) * z + n + 1)⁻¹) = (((b : ℂ) * z + n) ^ 2)⁻¹ := by
  by_cases h : b = 0 ∧ n = 0
  · simp_rw [h.1, h.2]
    simp
  · simp only [not_and] at h
    by_cases hb : b = 0
    · by_cases hn : n = -1
      · simp only [hb, Int.cast_zero, zero_mul, hn, Int.reduceNeg, Int.cast_neg, Int.cast_one,
        zero_add, neg_add_cancel, inv_zero, even_two, Even.neg_pow, one_pow, inv_one, mul_one,
        δ_eq2, inv_neg, sub_zero]
        ring
      · have hn0 : (n : ℂ) ≠ 0 := by aesop
        have hn1 : (n : ℂ) + 1 ≠ 0 := by norm_cast; omega
        simp only [hb, Int.cast_zero, zero_mul, zero_add, δ, Nat.succ_eq_add_one, Nat.reduceAdd,
          Matrix.vecCons_inj, h hb, and_true, and_false, ↓reduceIte, Int.reduceNeg, hn, add_zero]
        field_simp
        ring
    · simp only [δ, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.vecCons_inj, hb, and_true,
        false_and, ↓reduceIte, Int.reduceNeg, add_zero]
      have h0 : ((b : ℂ) * z + n + 1) ≠ 0 := by
        simpa [add_assoc] using linear_ne_zero (cd := ![b, n + 1]) z (by aesop)
      have h1 : ((b : ℂ) * z + n) ≠ 0 := by
        simpa using linear_ne_zero (cd := ![b, n]) z (by aesop)
      field_simp
      ring

lemma auxr (z : ℍ) (b : ℤ) :
    ((limUnder atTop fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (G2Term z ![b,n] + δ ![b, n])) +
    limUnder atTop fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / ((b : ℂ) * z + n) - 1 / (b * z + n + 1))) =
    limUnder atTop fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / ((b : ℂ) * z + n) ^ 2) := by
  have := limUnder.add (f := fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (G2Term z ![b,n] + δ ![b, n]))
    (g := fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / ((b : ℂ) * z + n) - 1 / (b * z + n + 1)))
      (by simpa [G2Term] using extracted_2_δ z b) (by apply extracted_3 z b)
  rw [this]
  apply limUnder_congr_eventually _ _ _
    (by apply CauchySeq.add (by simpa [G2Term] using extracted_2_δ z b) (extracted_3 z b))
    (by apply extracted_4 z b)
  simp only [one_div, mul_inv_rev, Pi.add_apply, eventually_atTop,
    ge_iff_le]
  use 1
  intro c hc
  rw [← Finset.sum_add_distrib ]
  congr
  exact funext fun n ↦ poly_id z b n


--this sum is now abs convergent. Idea is to subtract limUnder_sum_eq_zero from the G2 defn.
lemma G2_alt_eq (z : ℍ) : G2 z = ∑' m, ∑' n, (G2Term z ![m, n] + δ ![m, n]) := by
  set t :=  ∑' m, ∑' n,  (G2Term z ![m, n] + δ ![m, n])
  rw [G2, show t = t + 0 by ring, ←  tsum_limUnder_eq z, ← Summable.tsum_add]
  · rw [int_tsum_limUnder_Icc_atTop]
    · congr
      ext n
      congr
      ext m
      rw [e2Summand, int_tsum_limUnder_Ico_atTop ( e2Summand_summable m z),
        int_tsum_limUnder_Ico_atTop (by simpa using G2_prod_summable1_δ z m), auxr z m]
      simp only [eisSummand, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, one_div]
      rfl
    · apply (((finTwoArrowEquiv _).symm.summable_iff.mpr (G_2_alt_summable_δ z)).prod).congr
      intro b
      simpa using limUnder_sum_eq_zero z b
  · apply (((finTwoArrowEquiv _).symm.summable_iff.mpr (G_2_alt_summable_δ z)).prod).congr
    simp
  · apply summable_zero.congr
    intro b
    simp [← limUnder_sum_eq_zero z b]

lemma CauchySeq.const_smul {𝕜 : Type*} [NormedRing 𝕜] [NormMulClass 𝕜] {f : ℕ → 𝕜} (c : 𝕜)
    (hf : CauchySeq f) : CauchySeq (c • f) := by
  simp [Metric.cauchySeq_iff'] at *
  by_cases hc : c = 0
  · simp only [hc, zero_mul, dist_self]
    aesop
  · intro ε hε
    have hC : 0 < ‖c‖ := by simp [ne_eq, hc, not_false_eq_true]
    obtain ⟨N, hN⟩ := hf (ε / ‖c‖) (by rw [lt_div_iff₀' hC]; simp [hε])
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    simp only [dist_eq_norm, gt_iff_lt, ← mul_sub, norm_mul] at *
    rw [lt_div_iff₀' (by simp [hc])] at h1
    exact h1

/-- The map that swaps the two co-ordinates of a `Fin 2 → α` -/
def swap {α : Type*} : (Fin 2 → α) → (Fin 2 → α) := fun x => ![x 1, x 0]

@[simp]
lemma swap_apply {α : Type*} (b : Fin 2 → α) : swap b = ![b 1, b 0] := rfl

lemma swap_involutive {α : Type*} (b : Fin 2 → α) : swap (swap b) = b := by
  ext i
  fin_cases i <;> rfl

/-- An equivalence between `Fin 2 → α` and itself given by swapping the two co-ordinates -/
def swap_equiv {α : Type*} : Equiv (Fin 2 → α) (Fin 2 → α) := Equiv.mk swap swap
  (by rw [Function.LeftInverse]; apply swap_involutive)
  (by rw [Function.RightInverse]; apply swap_involutive)

lemma G2_inde_lhs (z : ℍ) : (z.1 ^ 2)⁻¹ * G2 (ModularGroup.S • z) - -2 * π * I / z =
  ∑' n : ℤ, ∑' m : ℤ, (G2Term z ![m, n] + δ ![m, n]) := by
  rw [G2_S_act, ← limUnder_tsum_eq z, int_tsum_limUnder_Ico_atTop, limUnder.sub]
  · congr
    ext N
    simp only [one_div, Pi.sub_apply, mul_inv_rev]
    rw [Summable.tsum_finsetSum , ← Finset.sum_sub_distrib ]
    · apply sum_congr rfl fun n hn => ?_
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [← Summable.tsum_sub]
      · exact tsum_congr fun m => by nth_rw 1 [← poly_id z m n, add_sub_cancel_right]
      · exact linear_left_summable (ne_zero z) n (k := 2) (by norm_num)
      · simpa [← add_assoc] using (summable_one_div_linear_sub_one_div_linear z n (n + 1))
    · exact fun i hi => linear_left_summable (ne_zero z) i (k := 2) (by norm_num)
  · conv =>
      enter [1, N]
      rw [Summable.tsum_finsetSum
        (by intro i hi; simpa using linear_left_summable (ne_zero z) i (k := 2) (by norm_num))]
    have hzn : ((UpperHalfPlane.coe z) ^ 2)⁻¹ ≠ 0 := by simp [ne_eq, ne_zero z, pow_eq_zero_iff]
    have := (aux_cauchySeq_Ico ⟨-1 / z, by simpa using pnat_div_upper 1 z⟩).const_smul
      ((UpperHalfPlane.coe z) ^ 2)⁻¹
    simp only [ne_eq, inv_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      e2Summand, eisSummand, Fin.isValue, Matrix.cons_val_zero, coe_mk_subtype, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, one_div] at *
    conv at this =>
      enter [1, 2, N, 2, x]
      rw [← tsum_int_eq_tsum_neg]
    convert this
    simp_rw [Int.cast_neg, Pi.smul_apply, smul_eq_mul, mul_sum, ← tsum_mul_left]
    exact sum_congr (rfl) fun a ha => tsum_congr fun b => by field_simp; ring
  · apply Filter.Tendsto.cauchySeq (x := (-2 * π * I / z))
    rw [← tendsto_comp_val_Ioi_atTop]
    simpa using (tendsto_tsum_one_div_linear_sub_succ_eq z)
  · have := G_2_alt_summable_δ z
    rw [← swap_equiv.summable_iff, ← (finTwoArrowEquiv _).symm.summable_iff] at this
    simpa using Summable.prod this

lemma G2_alt_indexing_δ (z : ℍ) : ∑' (m : Fin 2 → ℤ), (G2Term z m + δ m)  =
    ∑' m : ℤ, ∑' n : ℤ, (G2Term z ![m, n] + (δ ![m, n])) := by
  rw [ ← (finTwoArrowEquiv _).symm.tsum_eq]
  simp only [Fin.isValue, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_inv_rev]
  refine Summable.tsum_prod' ?_ ?_
  · have := G_2_alt_summable_δ z
    simp at this
    rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
    exact this
  · intro b
    have := G_2_alt_summable_δ z
    simp only [Fin.isValue, mul_inv_rev, ← (finTwoArrowEquiv _).symm.summable_iff] at this
    exact this.prod_factor b

lemma G2_alt_indexing2_δ (z : ℍ) : ∑' (m : Fin 2 → ℤ), (G2Term z m + δ m)  =
    ∑' n : ℤ, ∑' m : ℤ, (G2Term z ![m, n] + δ ![m, n]) := by
  have := (G_2_alt_summable_δ z)
  simp at this
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
  rw [ Summable.tsum_comm', G2_alt_indexing_δ]
  · apply this.congr
    intro b
    simp
    rfl
  · intro b
    simp only [mul_inv_rev]
    apply this.prod_factor
  · intro c
    have H := (G_2_alt_summable_δ z)
    rw [← swap_equiv.summable_iff, ← (finTwoArrowEquiv _).symm.summable_iff] at H
    simpa using H.prod_factor c

lemma G2_transf_aux (z : ℍ) :
    (z.1 ^ 2)⁻¹ * G2 (ModularGroup.S • z) - -2 * π * I / z = G2 z := by
  rw [G2_inde_lhs, G2_alt_eq z , ← G2_alt_indexing2_δ , G2_alt_indexing_δ]

end transform
