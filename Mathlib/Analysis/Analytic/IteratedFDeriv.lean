/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Data.Fintype.Perm

/-!
# The iterated derivative of an analytic function

If a function is analytic, written as `f (x + y) = ∑ pₙ (y, ..., y)` then its `n`-th iterated
derivative at `x` is given by `(v₁, ..., vₙ) ↦ ∑ pₙ (v_{σ (1)}, ..., v_{σ (n)})` where the sum
is over all permutations of `{1, ..., n}`. In particular, it is symmetric.
-/

open scoped ENNReal
open Equiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
{f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : ℝ≥0∞}

noncomputable def FormalMultilinearSeries.iteratedFDerivSeries
    (p : FormalMultilinearSeries 𝕜 E F) (k : ℕ) :
    FormalMultilinearSeries 𝕜 E (E [×k]→L[𝕜] F) :=
  match k with
  | 0 => (continuousMultilinearCurryFin0 𝕜 E F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.compFormalMultilinearSeries p
  | (k + 1) => (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) ↦ E) F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.compFormalMultilinearSeries
      (p.iteratedFDerivSeries k).derivSeries

/-- If a function has a power series on a ball, then so do its iterated derivatives. -/
protected theorem HasFPowerSeriesWithinOnBall.iteratedFDerivWithin [CompleteSpace F]
    (h : HasFPowerSeriesWithinOnBall f p s x r) (k : ℕ) (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    HasFPowerSeriesWithinOnBall (iteratedFDerivWithin 𝕜 k f s)
      (p.iteratedFDerivSeries k) s x r := by
  induction k with
  | zero =>
    exact (continuousMultilinearCurryFin0 𝕜 E F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall h
  | succ k ih =>
    rw [iteratedFDerivWithin_succ_eq_comp_left]
    apply (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) ↦ E) F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall
        (ih.fderivWithin_of_mem hu hx)

lemma FormalMultilinearSeries.iteratedFDerivSeries_eq_zero {k n : ℕ}
    (h : p (n + k) = 0) : p.iteratedFDerivSeries k n = 0 := by
  induction k generalizing n with
  | zero =>
    ext
    have : p n = 0 := p.congr_zero rfl h
    simp [FormalMultilinearSeries.iteratedFDerivSeries, this]
  | succ k ih =>
    ext
    simp only [iteratedFDerivSeries, Nat.succ_eq_add_one,
      ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, Function.comp_apply,
      continuousMultilinearCurryLeftEquiv_symm_apply, ContinuousMultilinearMap.zero_apply]
    rw [derivSeries_eq_zero]
    · rfl
    · apply ih
      apply p.congr_zero (by abel) h

lemma HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_zero [CompleteSpace F]
    (h : HasFPowerSeriesWithinOnBall f p s x r)
    (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ} (hn : p n = 0) :
    iteratedFDerivWithin 𝕜 n f s x = 0 := by
  have : iteratedFDerivWithin 𝕜 n f s x = p.iteratedFDerivSeries n 0 (fun _ ↦ 0) :=
    ((h.iteratedFDerivWithin n hu hx).coeff_zero _).symm
  rw [this, p.iteratedFDerivSeries_eq_zero (p.congr_zero (Nat.zero_add n).symm hn)]
  rfl

lemma ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal
    {n : ℕ} (f : E [×n]→L[𝕜] F) (x : E) (v : Fin n → E) :
    iteratedFDeriv 𝕜 n (fun x ↦ f (fun _ ↦ x)) x v = ∑ σ : Perm (Fin n), f (fun i ↦ v (σ i)) := by
  rw [← sum_comp (Equiv.inv (Perm (Fin n)))]
  let g : E →L[𝕜] (Fin n → E) := ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.id 𝕜 E)
  change iteratedFDeriv 𝕜 n (f ∘ g) x v = _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ f.contDiff _ le_rfl, f.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.iteratedFDeriv,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply, Set.mem_range, Pi.compRightL_apply]
  rw [← sum_comp (Equiv.embeddingEquivOfFinite (Fin n))]
  congr with σ
  congr with i
  have A : ∃ y, σ y = i := by
    have : Function.Bijective σ := (Fintype.bijective_iff_injective_and_card _).2 ⟨σ.injective, rfl⟩
    exact this.surjective i
  rcases A with ⟨y, rfl⟩
  simp only [EmbeddingLike.apply_eq_iff_eq, exists_eq, ↓reduceDIte,
    Function.Embedding.toEquivRange_symm_apply_self, ContinuousLinearMap.coe_pi',
    ContinuousLinearMap.coe_id', id_eq, g]
  congr 1
  symm
  simp [coe_fn_mk, inv_apply, Perm.inv_def,
    ofBijective_symm_apply_apply, Function.Embedding.equivOfFiniteSelfEmbedding]

lemma glouk [CompleteSpace F]
    (h : HasFPowerSeriesWithinOnBall f p s x r)
    (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hx : x ∈ s)
    {n : ℕ} (v : Fin n → E) (h's : s ⊆ EMetric.ball x r) :
    iteratedFDerivWithin 𝕜 n f s x v = ∑ σ : Perm (Fin n), p n (fun i ↦ v (σ i)) := by
  have I : insert x s ∩ EMetric.ball x r = s := by
    rw [Set.insert_eq_of_mem hx]
    exact Set.inter_eq_left.2 h's
  have fcont : ContDiffOn 𝕜 (↑n) f s := by
    apply AnalyticOn.contDiffOn _ hu
    simpa [I] using h.analyticOn
  let g : E → F := fun z ↦ p n (fun _ ↦ z - x)
  let q : FormalMultilinearSeries 𝕜 E F := fun k ↦ if h : n = k then (h ▸ p n) else 0
  have A : HasFiniteFPowerSeriesOnBall g q x (n + 1) r := by
    apply HasFiniteFPowerSeriesOnBall.mk' _ h.r_pos
    · intro y hy
      rw [Finset.sum_eq_single_of_mem n]
      · simp [q, g]
      · simp
      · intro i hi h'i
        simp [q, h'i.symm]
    · intro m hm
      have : n ≠ m := by omega
      simp [q, this]
  have B : HasFPowerSeriesWithinOnBall g q s x r :=
    A.toHasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall
  have gcont : ContDiffOn 𝕜 (↑n) g s := by
    apply AnalyticOn.contDiffOn _ hu
    simpa [I] using B.analyticOn
  have J1 : iteratedFDerivWithin 𝕜 n f s x =
      iteratedFDerivWithin 𝕜 n g s x + iteratedFDerivWithin 𝕜 n (f - g) s x := by
    have : f = g + (f - g) := by abel
    nth_rewrite 1 [this]
    rw [iteratedFDerivWithin_add_apply gcont (by exact fcont.sub gcont) hu hx]
  have J2 : iteratedFDerivWithin 𝕜 n (f - g) s x = 0 := by
    apply (h.sub B).iteratedFDerivWithin_eq_zero hu hx
    simp [q]
