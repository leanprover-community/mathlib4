/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Tactic.Positivity.Finset

/-! # Hölder's inequality for `lp` spaces

This file proves Hölder's inequality for `lp` spaces. We follow the established pattern for
Hölder's inequality for `MeasureTheory.Lp` of generalizing multiplication to any continuous bilinear
map. Since `lp` is a dependent Π-type, we actually need a uniformly bounded family of bilinear maps.

## Implementation notes

Although it would be possible to bundle the uniformly bounded family of bilinear maps into a term
`B : lp (fun i ↦ E i →L[𝕜] F i →L[𝕜] G i) ∞`, this has some downsides. For example, we would
then have to bundle `fun i ↦ (B i).flip` into a term of this type in order to use it, so we opt to
leave `B` unbundled.

-/

@[expose] public section

open scoped lp ENNReal NNReal

namespace lp
-- the material in this section could be moved to `lpSpace`, but would require some extra imports

section NontriviallyNormedField

variable {α 𝕜 : Type*} {E F : α → Type*} [NontriviallyNormedField 𝕜]
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
variable {p q r : ℝ≥0∞}

/-- A uniformly bounded family of continuous linear maps, as a continuous linear map
on the `lp` space. -/
@[simps!]
noncomputable def mapCLM (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : ∀ i, E i →L[𝕜] F i) {K : ℝ} (hK : 0 ≤ K) (hTK : ∀ i, ‖T i‖ ≤ K) :
    lp E p →L[𝕜] lp F p :=
  haveI key (i : α) (x : E i) : ‖T i x‖ ≤ K * ‖x‖ := (T i).le_of_opNorm_le (hTK i) _
  LinearMap.mkContinuous
    { toFun x := ⟨fun i ↦ T i (⇑x i), lp.memℓp x |>.norm.const_mul K |>.mono
        (fun _ ↦ by simpa [abs_of_nonneg hK] using key ..) |>.of_norm⟩
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
    K
    fun x ↦ by
      rw [← norm_toNorm]
      conv_rhs => rw [← norm_toNorm, ← abs_of_nonneg hK, ← Real.norm_eq_abs, ← norm_smul]
      apply norm_mono (zero_lt_one.trans_le Fact.out).ne' fun i ↦ ?_
      simpa [abs_of_nonneg hK] using key ..

lemma norm_mapCLM_le (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : ∀ i, E i →L[𝕜] F i) {K : ℝ} (hK : 0 ≤ K) (hTK : ∀ i, ‖T i‖ ≤ K) :
    ‖mapCLM p T hK hTK‖ ≤ K :=
  LinearMap.mkContinuous_norm_le _ hK _

end NontriviallyNormedField

lemma norm_tsumCLM {α 𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] :
    ‖tsumCLM 𝕜 α E‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end lp

variable {ι 𝕜 : Type*} {E F G : ι → Type*} [RCLike 𝕜]
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]

open ENNReal

variable {p q : ℝ≥0∞} (r : ℝ≥0∞) [hpqr : p.HolderTriple q r]

namespace Memℓp

theorem bilin_of_top_left (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i)
    {K : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K) {e : Π i, E i} {f : Π i, F i}
    (he : Memℓp e ∞) (hf : Memℓp f q) :
    Memℓp (fun i ↦ B i (e i) (f i)) q := by
  obtain (h | h) := isEmpty_or_nonempty ι
  · exact all _
  obtain ⟨C, hC⟩ := by
    simpa [memℓp_infty_iff, BddAbove, Set.Nonempty, Set.range, upperBounds] using he
  refine hf.norm.const_mul (K * C) |>.mono fun i ↦ ?_
  have hK_nonneg : 0 ≤ K := norm_nonneg (B (Classical.arbitrary ι)) |>.trans <| hBK _
  calc
    ‖B i (e i) (f i)‖ ≤ ‖B i‖ * ‖e i‖ * ‖f i‖ := (B i (e i)).le_of_opNorm_le ((B i).le_opNorm _) _
    _ ≤ K * C * ‖f i‖ := by gcongr; exacts [hBK i, hC i]

theorem bilin_of_top_right (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i)
    {K : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K) {e : Π i, E i} {f : Π i, F i}
    (he : Memℓp e p) (hf : Memℓp f ∞) :
    Memℓp (fun i ↦ B i (e i) (f i)) p :=
  hf.bilin_of_top_left (fun i ↦ (B i).flip) (by simpa using hBK) he

theorem bilin_of_zero_left (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i)
    {e : Π i, E i} {f : Π i, F i} (he : Memℓp e 0) :
    Memℓp (fun i ↦ B i (e i) (f i)) 0 := by
  rw [memℓp_zero_iff] at he ⊢
  exact he.subset fun i hi h ↦ hi <| by simp [h]

theorem bilin_of_zero_right (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i)
    {e : Π i, E i} {f : Π i, F i} (hf : Memℓp f 0) :
    Memℓp (fun i ↦ B i (e i) (f i)) 0 :=
  hf.bilin_of_zero_left (fun i ↦ (B i).flip)

lemma holder_top_left_bound
    {e : (i : ι) → E i} {f : (i : ι) → F i} (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i)
    {K C D : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hCe : ∀ i, ‖e i‖ ≤ C) (hDf : ∀ s, ∑ i ∈ s, ‖f i‖ ^ q.toReal ≤ D) (s : Finset ι) :
    ∑ i ∈ s, ‖B i (e i) (f i)‖ ^ q.toReal ≤ (K * C) ^ q.toReal * D := by
  grw [← hDf s, s.mul_sum]
  apply s.sum_le_sum fun i hi ↦ ?_
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  gcongr
  exact (B i (e i)).le_of_opNorm_le ((B i).le_of_opNorm_le_of_le (hBK i) (hCe i)) _

lemma holder_top_right_bound
    {e : (i : ι) → E i} {f : (i : ι) → F i} (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i)
    {K C D : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hCe : ∀ s, ∑ i ∈ s, ‖e i‖ ^ p.toReal ≤ C) (hDf : ∀ i, ‖f i‖ ≤ D) (s : Finset ι) :
    ∑ i ∈ s, ‖B i (e i) (f i)‖ ^ p.toReal ≤ (K * D) ^ p.toReal * C :=
  holder_top_left_bound (B · |>.flip) (by simpa) hK hD hDf hCe s

lemma holder_gen_bound {e : (i : ι) → E i} {f : (i : ι) → F i}
    (hp : 0 < p.toReal) (hq : 0 < q.toReal)
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K C D : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hCe : ∀ s, ∑ i ∈ s, ‖e i‖ ^ p.toReal ≤ C)
    (hDf : ∀ s, ∑ i ∈ s, ‖f i‖ ^ q.toReal ≤ D) (s : Finset ι) :
    ∑ i ∈ s, ‖B i (e i) (f i)‖ ^ r.toReal ≤
      K ^ r.toReal * C ^ (r.toReal / p.toReal) * D ^ (r.toReal / q.toReal) := by
  have hpqr := hpqr.toReal r hp hq
  have hr := hpqr.pos'
  suffices ∑ i ∈ s, (‖e i‖ * ‖f i‖) ^ r.toReal ≤
      C ^ (r.toReal / p.toReal) * D ^ (r.toReal / q.toReal) from calc
    ∑ i ∈ s, ‖B i (e i) (f i)‖ ^ r.toReal
    _ ≤ K ^ r.toReal * ∑ i ∈ s, (‖e i‖ * ‖f i‖) ^ r.toReal := by
      rw [s.mul_sum]
      gcongr with i hi
      rw [← Real.mul_rpow (by positivity) (by positivity), ← mul_assoc]
      gcongr
      exact (B i (e i)).le_of_opNorm_le ((B i).le_of_opNorm_le (hBK i) _) _
    _ ≤ _ := by
      rw [mul_assoc]
      gcongr
  calc
    _ ≤ (∑ i ∈ s, ‖e i‖ ^ p.toReal) ^ (r.toReal / p.toReal) *
        (∑ i ∈ s, ‖f i‖ ^ q.toReal) ^ (r.toReal / q.toReal) := by
      apply Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg s hpqr <;> (intros; positivity)
    _ ≤ _ := by
      gcongr
      · exact hCe s
      · exact hDf s

lemma holder {e : (i : ι) → E i} {f : (i : ι) → F i} (he : Memℓp e p) (hf : Memℓp f q)
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K) :
    Memℓp (fun i ↦ B i (e i) (f i)) r := by
  obtain (h | h) := isEmpty_or_nonempty ι
  · exact all _
  have hK : 0 ≤ K := norm_nonneg (B (Classical.arbitrary ι)) |>.trans <| hBK _
  have hpqr' := hpqr.inv_eq
  obtain (rfl | rfl | hp) := p.trichotomy
  · simp_all only [ENNReal.inv_zero, top_add, inv_eq_top]
    exact he.bilin_of_zero_left B
  · simp_all only [inv_top, zero_add, inv_inj]
    exact he.bilin_of_top_left B hBK hf
  obtain (rfl | rfl | hq) := q.trichotomy
  · simp_all only [ENNReal.inv_zero, add_top, inv_eq_top]
    exact hf.bilin_of_zero_right B
  · simp_all only [inv_top, add_zero, inv_inj]
    exact he.bilin_of_top_right B hBK hf
  obtain ⟨C, hC, hCe⟩ := memℓp_gen_iff'' hp |>.mp he
  obtain ⟨D, hD, hDf⟩ := memℓp_gen_iff'' hq |>.mp hf
  exact memℓp_gen' <| holder_gen_bound r hp hq B hBK hK hC hCe hDf

end Memℓp

namespace lp

/-- The map between `lp` spaces satisfying `ENNReal.HolderTriple` induced by a
uniformly bounded family of continuous bilinear maps on the underlying spaces. -/
@[simps]
def holder (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K)
    (e : lp E p) (f : lp F q) :
    lp G r where
  val := fun i ↦ B i (e i) (f i)
  property := (lp.memℓp e).holder _ (lp.memℓp f) B hBK

/-- `lp.holder` as a bilinear map. -/
@[simps!]
noncomputable def holderₗ (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K) :
    lp E p →ₗ[𝕜] lp F q →ₗ[𝕜] lp G r :=
  .mk₂ 𝕜 (holder r B hBK) ?_ ?_ ?_ ?_ where finally
    all_goals intros; ext; simp

/-- `lp.holder` as a continuous bilinear map. -/
noncomputable def holderL [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K : ℝ≥0} (hBK : ∀ i, ‖B i‖ ≤ K) :
    lp E p →L[𝕜] lp F q →L[𝕜] lp G r :=
  holderₗ r B hBK |>.mkContinuous₂ K fun e f ↦ by
    obtain ⟨(rfl | hp), (rfl | hq)⟩ := And.intro p.dichotomy q.dichotomy
    · obtain rfl : r = ⊤ := ENNReal.HolderTriple.unique ∞ ∞ r ∞
      refine norm_le_of_forall_le (by positivity) fun i ↦ ?_
      refine (B i).le_of_opNorm₂_le_of_le (hBK i) ?_ ?_
      all_goals exact norm_apply_le_norm (by simp) ..
    · obtain rfl : r = q := ENNReal.HolderTriple.unique ∞ q r q
      refine norm_le_of_forall_sum_le (zero_lt_one.trans_le hq) (by positivity) fun s ↦ ?_
      rw [Real.mul_rpow (by positivity) (by positivity)]
      refine Memℓp.holder_top_left_bound B hBK
        (by positivity) (by positivity) (norm_apply_le_norm (by simp) _) ?_ s
      exact sum_rpow_le_norm_rpow (zero_lt_one.trans_le hq) f
    · obtain rfl : r = p := ENNReal.HolderTriple.unique p ∞ r p
      refine norm_le_of_forall_sum_le (zero_lt_one.trans_le hp) (by positivity) fun s ↦ ?_
      rw [mul_right_comm, Real.mul_rpow (by positivity) (by positivity)]
      refine Memℓp.holder_top_right_bound B hBK
        (by positivity) (by positivity) ?_ (norm_apply_le_norm (by simp) _) s
      exact sum_rpow_le_norm_rpow (zero_lt_one.trans_le hp) e
    · have hpqr := hpqr.toReal r (zero_lt_one.trans_le hp) (zero_lt_one.trans_le hq)
      have hp := hpqr.pos
      have hq := hpqr.symm.pos
      refine norm_le_of_forall_sum_le hpqr.pos' (by positivity) fun s ↦ ?_
      simp only [holderₗ_apply_apply_coe]
      calc
        _ ≤ K ^ r.toReal * (‖e‖ ^ p.toReal) ^ (r.toReal / p.toReal) *
          (‖f‖ ^ q.toReal) ^ (r.toReal / q.toReal) :=
          Memℓp.holder_gen_bound r hp hq B hBK (by positivity) (by positivity)
            (sum_rpow_le_norm_rpow hp e) (sum_rpow_le_norm_rpow hq f) s
        _ ≤ _ := by
          rw [← Real.rpow_mul, ← Real.rpow_mul]
          · simp only [← mul_div_assoc, ne_eq, hp.ne', not_false_eq_true, mul_div_cancel_left₀,
            hq.ne', fieldLe]
            rw [Real.mul_rpow, Real.mul_rpow]
            all_goals positivity
          all_goals positivity

lemma norm_holderL_le [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K : ℝ≥0} (hBK : ∀ i, ‖B i‖ ≤ K) :
    ‖holderL (p := p) (q := q) r B hBK‖ ≤ K :=
  LinearMap.mkContinuous₂_norm_le _ K.2 _

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] [CompleteSpace H]

variable (p q) in
/-- The natural pairing between `lp E p` and `lp F q` (for Hölder conjugate `p q : ℝ≥0∞`) with
values in a space `H` induced by a family of bilinear maps `B : (i : ι) → E i →L[𝕜] F i →L[𝕜] H`.

This is given by `∑' i, B (e i) (f i)`.

In the special case when `B := (NormedSpace.inclusionInDoubleDual 𝕜 E).flip`, which is
definitionally the same as `B := ContinuousLinearMap.id 𝕜 (E →L[𝕜] 𝕜)`, this is the natural map
`lp (fun _ ↦ StrongDual 𝕜 E) p →L[𝕜] StrongDual 𝕜 (lp E q)`.
-/
noncomputable def dualPairing [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] H) {K : ℝ≥0} (hBK : ∀ i, ‖B i‖ ≤ K) :
    lp E p →L[𝕜] lp F q →L[𝕜] H :=
  (tsumCLM 𝕜 ι H |>.postcomp <| lp F q) ∘L (holderL 1 B hBK)

lemma dualPairing_apply [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] H) {K : ℝ≥0} (hBK : ∀ i, ‖B i‖ ≤ K)
    (e : lp E p) (f : lp F q) :
    dualPairing p q B hBK e f = ∑' i, B i (e i) (f i) :=
  rfl

lemma norm_dualPairing [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] H) {K : ℝ≥0} (hBK : ∀ i, ‖B i‖ ≤ K) :
    ‖dualPairing p q B hBK‖ ≤ K := calc
  ‖dualPairing p q B hBK‖
  _ ≤ ‖(tsumCLM 𝕜 ι H).postcomp (lp F q)‖ * ‖holderL 1 B hBK‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  _ ≤ 1 * K := by
    gcongr
    · exact ContinuousLinearMap.norm_postcomp_le _ |>.trans norm_tsumCLM
    · exact norm_holderL_le 1 B hBK
  _ = K := one_mul _

end lp
