import Mathlib.Analysis.NormedSpace.Multilinear.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Extension.Well
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.NormedSpace.Multilinear.Curry
import Mathlib.Analysis.Analytic.CPolynomial

open ContinuousLinearMap Metric
open Topology NNReal Asymptotics ENNReal
open NormedField BigOperators Finset

universe u uι v w

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {ι : Type uι} [Fintype ι]
  {E : ι → Type v} {F : Type w} [(i : ι) → NormedAddCommGroup (E i)]
  [(i : ι) → NormedSpace 𝕜 (E i)] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}

namespace MultilinearMap

open ContinuousMultilinearMap in
lemma domDomRestrict_bound [DecidableEq ι] (f : ContinuousMultilinearMap 𝕜 E F) (P : ι → Prop)
    [DecidablePred P] [DecidableEq {a // P a}]
    (z : (i : {a : ι // ¬ P a}) → E i) (x : (i : {a // P a}) → E i) :
    ‖f.domDomRestrict P z x‖ ≤ ‖f‖  * (∏ i, ‖z i‖) * (∏ i, ‖x i‖) := by
  rw [domDomRestrict_apply, mul_assoc, mul_comm (∏ i, ‖z i‖)]
  refine le_trans (le_op_norm _ _) (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  set f : ι → ℝ := fun i ↦ if h : P i then ‖x ⟨i, h⟩‖ else ‖z ⟨i, h⟩‖
  rw [prod_congr rfl (g := f)
    (fun i _ ↦ by by_cases h : P i; all_goals (simp only [h, dite_true, dite_false]))]
  rw [prod_congr rfl (g := fun (i : {a // P a}) ↦ f i.1), ← prod_subtype (filter P univ)
    (fun _ ↦ by simp only [mem_filter, mem_univ, true_and]),
    prod_congr rfl (g := fun (i : {a // ¬ P a}) ↦ f i.1), ← prod_subtype
    (filter (fun a ↦ ¬ P a) univ) (fun _ ↦ by simp only [mem_filter, mem_univ, true_and])]
  · rw [← compl_filter, prod_mul_prod_compl]
  · exact fun i _ ↦ by simp only [i.2, dite_false]
  · exact fun i _ ↦ by simp only [i.2, dite_true]

lemma linearDeriv_bound [DecidableEq ι] (f : ContinuousMultilinearMap 𝕜 E F) (x y : (i : ι) → E i) :
    ‖f.linearDeriv x y‖ ≤ ‖f‖ * (∑ i, (∏ j in univ.erase i, ‖x j‖)) * ‖y‖ := by
  rw [linearDeriv_apply, mul_sum, sum_mul]
  apply norm_sum_le_of_le
  refine' fun i _ ↦ le_trans ?_ (mul_le_mul_of_nonneg_left (norm_le_pi_norm y i) (mul_nonneg
    (norm_nonneg _) (prod_nonneg (fun i _ ↦ norm_nonneg _))))
  conv_rhs => congr; rfl; rw [← (Function.update_same i (y i) x)]
  rw [mul_assoc, prod_congr rfl (g := fun j ↦ ‖Function.update x i (y i) j‖)
    (fun _ hj ↦ by simp only; rw [Function.update_noteq (ne_of_mem_erase hj)]),
    prod_erase_mul univ _ (Finset.mem_univ _)]
  apply ContinuousMultilinearMap.le_op_norm

end MultilinearMap

namespace ContinuousMultilinearMap

noncomputable def domDomRestrict [DecidableEq ι] (f : ContinuousMultilinearMap 𝕜 E F)
    (P : ι → Prop) [DecidablePred P] [DecidableEq {a // P a}] (z : (i : {a : ι // ¬ P a}) → E i) :
    ContinuousMultilinearMap 𝕜 (fun (i : {a // P a}) => E i) F :=
  MultilinearMap.mkContinuous (f.toMultilinearMap.domDomRestrict P z)
  (‖f‖ * (∏ i, ‖z i‖)) (MultilinearMap.domDomRestrict_bound f P z)

@[simp]
lemma domDomRestrict_apply [DecidableEq ι] (f : ContinuousMultilinearMap 𝕜 E F)
    (P : ι → Prop) [DecidablePred P] [DecidableEq {a // P a}]
    (z : (i : {a : ι // ¬ P a}) → E i) (x : (i : {a // P a}) → E i) :
  f.domDomRestrict P z x = f (fun i => if h : P i then x ⟨i, h⟩ else z ⟨i, h⟩) := rfl

lemma domDomRestrict_norm_le [DecidableEq ι] (f : ContinuousMultilinearMap 𝕜 E F)
    (P : ι → Prop) [DecidablePred P] [DecidableEq {a // P a}] (z : (i : {a : ι // ¬ P a}) → E i) :
    ‖f.domDomRestrict P z‖ ≤ ‖f‖ * (∏ i, ‖z i‖) :=
  ContinuousMultilinearMap.op_norm_le_bound _ (mul_nonneg (norm_nonneg _) (prod_nonneg
  (fun _ _ ↦ norm_nonneg _))) (MultilinearMap.domDomRestrict_bound f P z)

noncomputable def fderiv [DecidableEq ι] (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    ((i : ι) → E i) →L[𝕜] F :=
  LinearMap.mkContinuous (f.toMultilinearMap.linearDeriv x)
  (‖f‖ * ∑ i, (∏ j in univ.erase i, ‖x j‖)) (fun y ↦ MultilinearMap.linearDeriv_bound f x y)

@[simp]
lemma fderiv_apply [DecidableEq ι] (f : ContinuousMultilinearMap 𝕜 E F) (x y : (i : ι) → E i) :
    f.fderiv x y = ∑ i, f (Function.update x i (y i)) := by
  simp only [fderiv, mem_univ, not_true_eq_false, LinearMap.mkContinuous_apply,
    MultilinearMap.linearDeriv_apply, coe_coe]

lemma fderiv_norm_le [DecidableEq ι] (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    ‖f.fderiv x‖ ≤ ‖f‖ * ∑ i, (∏ j in univ.erase i, ‖x j‖) :=
  ContinuousLinearMap.op_norm_le_bound _ (mul_nonneg (norm_nonneg _) (sum_nonneg (fun _ _ ↦
  (prod_nonneg (fun _ _ ↦ norm_nonneg _))))) (fun z ↦ MultilinearMap.linearDeriv_bound f x z)

noncomputable def toFormalMultilinearSeries [LinearOrder ι]
    (f : ContinuousMultilinearMap 𝕜 E F) : FormalMultilinearSeries 𝕜 ((i : ι) → E i) F :=
  fun n ↦ if h : n = Fintype.card ι then
    (f.compContinuousLinearMap (fun i ↦ ContinuousLinearMap.proj i)).domDomCongr
    (Fintype.equivFinOfCardEq (Eq.symm h))
  else 0

lemma toFormalMultilinearSeries_support [LinearOrder ι] (f : ContinuousMultilinearMap 𝕜 E F)
    {n : ℕ} (hn : (Fintype.card ι).succ ≤ n) :
    f.toFormalMultilinearSeries n = 0 := by
  simp only [toFormalMultilinearSeries, Ne.symm (ne_of_lt (Nat.lt_of_succ_le hn)), dite_false]

lemma toFormalMultilinearSeries_radius [LinearOrder ι]
    (f : ContinuousMultilinearMap 𝕜 E F) : f.toFormalMultilinearSeries.radius = ⊤ :=
  FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero _ (Fintype.card ι).succ
  (fun n ↦ f.toFormalMultilinearSeries_support (Nat.le_add_left (Fintype.card ι).succ n))

lemma toFormalMultilinearSeries_partialSum [LinearOrder ι]
    (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    f x = f.toFormalMultilinearSeries.partialSum (Fintype.card ι).succ x := by
  unfold toFormalMultilinearSeries FormalMultilinearSeries.partialSum
  rw [Finset.sum_eq_single_of_mem (Fintype.card ι) (by simp only [mem_range, Nat.lt_succ_self])
    (fun _ _ hm ↦ by simp only [hm, dite_false, zero_apply])]
  simp only [dite_true, domDomCongr_apply, compContinuousLinearMap_apply, proj_apply]

lemma toFormalMultilinearSeries_hasSum [LinearOrder ι] (f : ContinuousMultilinearMap 𝕜 E F)
    (x : (i : ι) → E i) : HasSum (fun (n : ℕ) => (f.toFormalMultilinearSeries n)
    fun (_ : Fin n) => x) (f x) := by
  rw [toFormalMultilinearSeries_partialSum]
  exact hasSum_sum_of_ne_finset_zero
    (fun _ hn ↦ by simp only [Finset.mem_range, not_lt] at hn
                   rw [f.toFormalMultilinearSeries_support (lt_of_lt_of_le
                        (Nat.lt_succ_self _) hn), zero_apply])

def hasFiniteFPowerSeriesAtOrigin [LinearOrder ι] (f : ContinuousMultilinearMap 𝕜 E F) :
    HasFiniteFPowerSeriesOnBall f f.toFormalMultilinearSeries 0  (Fintype.card ι).succ ⊤ where
  r_le := by rw [toFormalMultilinearSeries_radius]
  r_pos := zero_lt_top
  hasSum _ := by rw [zero_add]; exact f.toFormalMultilinearSeries_hasSum _
  finite _ h := f.toFormalMultilinearSeries_support h

lemma cPolynomialAt (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    CPolynomialAt 𝕜 f x := by
  letI : LinearOrder ι := WellFounded.wellOrderExtension emptyWf.wf
  exact HasFiniteFPowerSeriesOnBall.cPolynomialAt_of_mem f.hasFiniteFPowerSeriesAtOrigin
    (by simp only [emetric_ball_top, Set.mem_univ])

lemma cPolyomialOn (f : ContinuousMultilinearMap 𝕜 E F) :
    CPolynomialOn 𝕜 f ⊤ :=
  fun x _ ↦ f.cPolynomialAt x

lemma contDiffAt (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) {n : ℕ∞} :
    ContDiffAt 𝕜 n f x := CPolynomialAt.contDiffAt (f.cPolynomialAt x)

lemma changeOriginSeries_support [LinearOrder ι] (f : ContinuousMultilinearMap 𝕜 E F) {k l : ℕ}
    (h : k + l ≠ Fintype.card ι) :
    f.toFormalMultilinearSeries.changeOriginSeries k l = 0 := by
  unfold FormalMultilinearSeries.changeOriginSeries
  exact Finset.sum_eq_zero (fun _ _ ↦ by
    rw [FormalMultilinearSeries.changeOriginSeriesTerm, AddEquivClass.map_eq_zero_iff]
    simp only [toFormalMultilinearSeries, h, dite_false])

lemma fderiv_eq [DecidableEq ι] (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    _root_.fderiv 𝕜 f x = f.fderiv x := by
  letI : LinearOrder ι := WellFounded.wellOrderExtension emptyWf.wf
  ext y
  have := f.hasFiniteFPowerSeriesAtOrigin.changeOrigin (y := x) (r := ⊤) (by simp only [coe_lt_top])
  rw [zero_add] at this
  rw [this.hasFPowerSeriesAt.fderiv_eq, fderiv_apply]
  unfold FormalMultilinearSeries.changeOrigin FormalMultilinearSeries.sum
  rw [tsum_eq_single (Fintype.card ι - 1)]
  · simp only [continuousMultilinearCurryFin1_apply]
    by_cases he : IsEmpty ι
    · simp only [univ_eq_empty, sum_empty]
      letI := he
      rw [Fintype.card_eq_zero, Nat.zero_sub, changeOriginSeries_support, zero_apply, zero_apply]
      rw [Fintype.card_eq_zero, add_zero]
      exact Nat.one_ne_zero
    · unfold FormalMultilinearSeries.changeOriginSeries
      simp only [ContinuousMultilinearMap.sum_apply, continuousMultilinearCurryFin1_apply]
      have heq : Fin.snoc 0 y = (fun _ : Fin (0 + 1) ↦ y) := by
        ext _ _
        unfold Fin.snoc
        simp only [Fin.coe_fin_one, lt_self_iff_false, Fin.castSucc_castLT, Pi.zero_apply,
          cast_eq, dite_eq_ite, ite_false]
      rw [heq, sum_apply, sum_apply]
      have hcard : Fintype.card ι = 1 + (Fintype.card ι - 1) := by
        letI := not_isEmpty_iff.mp he
        rw [← Nat.succ_eq_one_add, ← Nat.pred_eq_sub_one, Nat.succ_pred Fintype.card_ne_zero]
      set I : (i : ι) → i ∈ Finset.univ → {s : Finset (Fin (1 + (Fintype.card ι - 1))) //
          s.card = Fintype.card ι - 1} := by
        intro i _
        refine ⟨Finset.univ.erase (Fintype.equivFinOfCardEq hcard i), ?_⟩
        simp only [mem_univ, not_true_eq_false, card_erase_of_mem, card_fin, ge_iff_le,
          add_le_iff_nonpos_right, nonpos_iff_eq_zero, tsub_eq_zero_iff_le, add_tsub_cancel_left]
      rw [Finset.sum_bij I (fun _ _ ↦ Finset.mem_univ _) (fun _ _ _ _ ↦ by
          simp only [mem_univ, not_true_eq_false, Subtype.mk.injEq,
          Finset.erase_inj _ (Finset.mem_univ _), Equiv.apply_eq_iff_eq, imp_self])]
      · intro ⟨s, hs⟩ _
        have h : sᶜ.card = 1 := by
          rw [Finset.card_compl, hs]
          simp only [ge_iff_le, Fintype.card_fin, add_le_iff_nonpos_left, nonpos_iff_eq_zero,
            add_tsub_cancel_right]
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
        existsi ((Fintype.equivFinOfCardEq hcard).symm a), Finset.mem_univ _
        simp only [mem_univ, not_true_eq_false, Equiv.apply_symm_apply, Subtype.mk.injEq]
        rw [Finset.erase_eq, ← ha]
        simp only [sdiff_compl, ge_iff_le, le_eq_subset, subset_univ, inf_of_le_right]
      · intro i _
        rw [FormalMultilinearSeries.changeOriginSeriesTerm_apply, toFormalMultilinearSeries]
        simp only [ge_iff_le, Eq.symm hcard, dite_true, piecewise_erase_univ, domDomCongr_apply,
          ne_eq, EmbeddingLike.apply_eq_iff_eq, compContinuousLinearMap_apply, proj_apply]
        congr
        ext j
        by_cases hj : j = i
        · rw [hj, Function.update_same, Function.update_same]
        · rw [Function.update_noteq hj, Function.update_noteq]
          rw [ne_eq, Equiv.apply_eq_iff_eq]
          exact hj
  · intro m hm
    rw [f.changeOriginSeries_support (k := 1) (l := m), zero_apply]
    exact fun h ↦ by
      apply_fun Nat.pred at h
      rw [← Nat.succ_eq_one_add, Nat.pred_succ, Nat.pred_eq_sub_one] at h
      exact hm h

end ContinuousMultilinearMap
