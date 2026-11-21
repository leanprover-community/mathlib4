import Mathlib

/-!
# Schatten operators

This file defines the Schatten operators.

## TODO:
 - generalize from `ℂ` to `𝕜`
 - determine proper junk value for `p=0`
 - expand APIs

-/

open scoped ENNReal NNReal InnerProductSpace ContinuousLinearMap

noncomputable section



namespace ContinuousLinearMap

section Trace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open scoped ComplexConjugate ENNReal

/-- The trace of an operator on `E`. -/
def traceOfBasis (A : E →L[ℂ] E) {ι : Type*} (b : HilbertBasis ι ℂ E) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (RCLike.re ⟪b i, A (b i)⟫_ℂ)

theorem traceOfBasis_eq {A : E →L[ℂ] E} (hA : 0 ≤ A) {ι ι' : Type*}
    (b : HilbertBasis ι ℂ E) (b' : HilbertBasis ι' ℂ E) :
    traceOfBasis A b = traceOfBasis A b' := by
  unfold traceOfBasis
  set S := CFC.sqrt A with hS
  have hS' : S.adjoint * S = A := by
    simp [hS, CFC.sqrt_mul_sqrt_self A hA, (CFC.sqrt_nonneg A).isSelfAdjoint.adjoint_eq]
  simp_rw +singlePass [← hS', mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right,
    ← b'.tsum_inner_mul_inner (S (b _)), ← inner_conj_symm (S (b _)),
    ← b.tsum_inner_mul_inner (S (b' _)), ← inner_conj_symm (S (b' _)),
    RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_tsum]
  simp only [Complex.coe_algebraMap, RCLike.re_to_complex, Complex.ofReal_re]
  simp_rw [fun x => ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
    (b.orthonormal.inner_products_summable x),
    fun x => ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
      (b'.orthonormal.inner_products_summable x)]
  rw [ENNReal.tsum_comm]
  simp_rw [← LinearMap.IsSymmetric.apply_clm (T := S)
    (CFC.sqrt_nonneg A).isSelfAdjoint.isSymmetric (b' _) (b _), norm_inner_symm (S (b' _)) (b _)]

/-- The trace of an operator on `E`. -/
def trace (A : E →L[ℂ] E) : ℝ≥0∞ := traceOfBasis A
  (Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ E)))

variable {A B : E →L[ℂ] E}

theorem trace_eq_traceOfBasis (hA : 0 ≤ A) {ι : Type*}
    (b : HilbertBasis ι ℂ E) : trace A = traceOfBasis A b := by
  unfold trace
  exact traceOfBasis_eq hA _ b

@[simp]
theorem trace_zero : trace (0 : E →L[ℂ] E) = 0 := by simp [trace, traceOfBasis]

theorem trace_add_le : trace (A + B) ≤ trace A + trace B := by
  unfold trace traceOfBasis
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun i => ?_
  simp only [add_apply, inner_add_right, map_add]
  exact ENNReal.ofReal_add_le

@[simp]
theorem trace_add (hA : 0 ≤ A) (hB : 0 ≤ B) : trace (A + B) = trace A + trace B := by
  unfold trace traceOfBasis
  simp_rw [add_apply, inner_add_right, map_add, ← ENNReal.tsum_add]
  refine tsum_congr fun i ↦ ?_
  refine ENNReal.ofReal_add ?_ ?_
  · simpa only [sub_zero] using hA.re_inner_nonneg_right _
  · simpa only [sub_zero] using hB.re_inner_nonneg_right _

theorem trace_eq_zero (hA : 0 ≤ A) : trace A = 0 ↔ A = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  unfold trace traceOfBasis at h
  set b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ E))
  set S := CFC.sqrt A with hS
  have hS' : S.adjoint * S = A := by
    simp [hS, CFC.sqrt_mul_sqrt_self A hA, (CFC.sqrt_nonneg A).isSelfAdjoint.adjoint_eq]
  simp_rw [ENNReal.tsum_eq_zero, ← hS', mul_apply_eq_comp,
    ContinuousLinearMap.adjoint_inner_right, ENNReal.ofReal_eq_zero, re_inner_self_nonpos] at h
  rw [← hS']
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  rintro _ ⟨i, rfl⟩
  simp [h i]

end Trace

section

variable (p : ℝ≥0∞) (q : ℝ) {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def modulus (T : E →L[ℂ] F) : E →L[ℂ] E := CFC.sqrt (T.adjoint ∘L T)

scoped notation "|" T "|" => modulus T

@[simp]
theorem modulus_zero : |(0 : E →L[ℂ] F)| = 0 := by simp [modulus]
@[simp]
theorem modulus_neg (T : E →L[ℂ] F) : |-T| = |T| := by simp [modulus]
@[simp]
theorem modulus_nonneg (T : E →L[ℂ] F) : 0 ≤ |T| := by simp [modulus]
@[simp]
theorem modulus_modulus (T : E →L[ℂ] F) : |(|T|)| = |T| := by
  rw [modulus, T.modulus_nonneg.isSelfAdjoint.adjoint_eq]
  exact CFC.sqrt_mul_self |T|

theorem modulus_eq_zero (T : E →L[ℂ] F) : |T| = 0 ↔ T = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  simp only [modulus] at h
  rw [CFC.sqrt_eq_zero_iff (adjoint T ∘SL T)
    (nonneg_iff_isPositive.mpr (ContinuousLinearMap.isPositive_adjoint_comp_self T))] at h
  exact adjoint_comp_self_eq_zero_iff.mp h

theorem modulus_comp_modulus (T : E →L[ℂ] F) :
    |T| ∘L |T| = T.adjoint ∘L T := by
  simpa [modulus, ← ContinuousLinearMap.mul_def] using
    CFC.sqrt_mul_sqrt_self (adjoint T ∘L T)
      (nonneg_iff_isPositive.mpr (ContinuousLinearMap.isPositive_adjoint_comp_self T))

theorem norm_modulus_apply (T : E →L[ℂ] F) (x : E) : ‖|T| x‖ = ‖T x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp_rw [apply_norm_sq_eq_inner_adjoint_left, ContinuousLinearMap.comp_apply]
  rw [T.modulus_nonneg.isSelfAdjoint.adjoint_eq]
  simp [modulus, ← mul_apply_eq_comp, CFC.sqrt_mul_sqrt_self (adjoint T ∘SL T)
      (nonneg_iff_isPositive.mpr (ContinuousLinearMap.isPositive_adjoint_comp_self T)),
    ContinuousLinearMap.comp_apply]

theorem ker_modulus_eq (T : E →L[ℂ] F) : |T|.ker = T.ker := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← norm_eq_zero (a := T.toLinearMap x),
    ← norm_eq_zero (a := |T|.toLinearMap x)]
  simp [norm_modulus_apply]

def _root_.Submodule.inclusionL {R M : Type*} [Semiring R]
  [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  {p p' : Submodule R M} (h : p ≤ p') :
  p →L[R] p' := p.subtypeL.codRestrict p' fun ⟨_, hx⟩ => h hx

@[simp]
theorem _root_.LinearMap.coe_toLinearIsometry {R E F : Type*} [Semiring R]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [Module R E] [Module R F]
    (f : E →ₗ[R] F) (hf : Isometry f) : ⇑(f.toLinearIsometry hf) = f := rfl

def polarₚₗᵢ (T : E →L[ℂ] F) : |T|.range.topologicalClosure →ₗᵢ[ℂ] F :=
  LinearMap.extendOfIsometry
    ((Submodule.liftQ _ T (le_of_eq_of_le T.ker_modulus_eq fun ⦃x⦄ a ↦ a))
      ∘ₗ (|T|.quotKerEquivRange).symm.toLinearMap)
    (e := Submodule.inclusion |T|.range.le_topologicalClosure)
    (by
      erw [denseRange_inclusion_iff (by
        simpa [← SetLike.coe_subset_coe] using |T|.range.le_topologicalClosure)]
      simp)
    (by
      rintro ⟨_, x, rfl⟩
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      erw [|T|.quotKerEquivRange_symm_apply_image x]
      simp [norm_modulus_apply])

theorem polarₚₗᵢ_apply (T : E →L[ℂ] F) (x : E) :
    T.polarₚₗᵢ ⟨|T| x, |T|.range.le_topologicalClosure ⟨x, rfl⟩⟩ = T x := by
  change T.polarₚₗᵢ (Submodule.inclusionL |T|.range.le_topologicalClosure ⟨|T| x, ⟨x, rfl⟩⟩) = _
  simp only [polarₚₗᵢ]
  erw [LinearMap.extendOfIsometry_eq, LinearMap.comp_apply,
    |T|.quotKerEquivRange_symm_apply_image x]
  simp

theorem range_polarₚₗᵢ (T : E →L[ℂ] F) :
    T.polarₚₗᵢ.toContinuousLinearMap.range = T.range.topologicalClosure := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    have hd : DenseRange (Submodule.inclusion |T|.range.le_topologicalClosure) := by
      erw [denseRange_inclusion_iff (by
        simpa [← SetLike.coe_subset_coe] using |T|.range.le_topologicalClosure)]
      simp
    refine hd.induction_on m
      (isClosed_closure.preimage T.polarₚₗᵢ.toContinuousLinearMap.continuous) ?_
    rintro ⟨_, x, rfl⟩
    exact subset_closure ⟨x, (T.polarₚₗᵢ_apply x).symm ▸ rfl⟩
  · exact Submodule.topologicalClosure_minimal _
      (by
        rintro _ ⟨x, rfl⟩
        exact ⟨⟨|T| x, |T|.range.le_topologicalClosure ⟨x, rfl⟩⟩, T.polarₚₗᵢ_apply x⟩)
      T.polarₚₗᵢ.isometry.isClosedEmbedding.isClosed_range

theorem polarₚₗᵢ_adjoint_comp (T : E →L[ℂ] F) :
    T.polarₚₗᵢ.toContinuousLinearMap.adjoint ∘L T.polarₚₗᵢ.toContinuousLinearMap
     = ContinuousLinearMap.id ℂ _ := by
  refine ContinuousLinearMap.ext fun x => ext_inner_right ℂ fun y => ?_
  erw [comp_apply, ContinuousLinearMap.adjoint_inner_left]
  simp [LinearIsometry.inner_map_map T.polarₚₗᵢ x y]

theorem polarₚₗᵢ_comp_adjoint (T : E →L[ℂ] F) :
    T.polarₚₗᵢ.toContinuousLinearMap ∘L T.polarₚₗᵢ.toContinuousLinearMap.adjoint
     = T.range.topologicalClosure.starProjection := by
  have : (T.polarₚₗᵢ.toContinuousLinearMap.range).HasOrthogonalProjection := by
    rw [range_polarₚₗᵢ]; infer_instance
  refine ContinuousLinearMap.ext fun x => ?_
  conv_lhs => erw [← Submodule.starProjection_add_starProjection_orthogonal
    (K := T.range.topologicalClosure) x]
  have h0 : T.polarₚₗᵢ.toContinuousLinearMap.adjoint
      ((T.polarₚₗᵢ.toContinuousLinearMap.range : Submodule ℂ F)ᗮ.starProjection x) = 0 :=
    ext_inner_right ℂ fun m => by
      rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
      simp only [LinearIsometry.toLinearMap_toContinuousLinearMap,
        LinearIsometry.coe_toContinuousLinearMap]
      exact Submodule.inner_left_of_mem_orthogonal (K := T.polarₚₗᵢ.range) ⟨m, rfl⟩
        (Submodule.starProjection_apply_mem (T.polarₚₗᵢ.range)ᗮ x)
  simp only [← T.range_polarₚₗᵢ, LinearIsometry.toLinearMap_toContinuousLinearMap, map_add,
    comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  erw [h0, map_zero, add_zero]
  obtain ⟨m, hm⟩ := Submodule.starProjection_apply_mem
    (T.polarₚₗᵢ.toContinuousLinearMap.range : Submodule ℂ F) x
  erw [← hm, LinearIsometry.toLinearMap_toContinuousLinearMap, LinearIsometry.coe_toLinearMap,
    LinearIsometry.map_eq_iff, ← comp_apply, T.polarₚₗᵢ_adjoint_comp]
  simp

def polar (T : E →L[ℂ] F) : E →L[ℂ] F :=
  T.polarₚₗᵢ.toContinuousLinearMap ∘L |T|.range.topologicalClosure.orthogonalProjectionOnto

theorem apply_eq_zero_tfae (T : E →L[ℂ] F) (x : E) :
    List.TFAE [T x = 0, T.polar x = 0, |T| x = 0] := by
  tfae_have 1 ↔ 3 := by
    rw [← norm_eq_zero (a := T x), ← norm_eq_zero (a := |T| x), norm_modulus_apply]
  tfae_have 2 ↔ 3 := by
    rw [polar, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      map_eq_zero_iff _ T.polarₚₗᵢ.injective,
      Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_closure,
      Submodule.mem_orthogonal]
    constructor
    · intro h
      apply (inner_self_eq_zero (𝕜 := ℂ)).mp
      rw [← ContinuousLinearMap.adjoint_inner_left, T.modulus_nonneg.isSelfAdjoint.adjoint_eq]
      exact h (|T| (|T| x)) ⟨|T| x, rfl⟩
    · rintro h _ ⟨y, rfl⟩
      rw [← T.modulus_nonneg.isSelfAdjoint.adjoint_eq]
      simp [← ContinuousLinearMap.adjoint_inner_right, h]
  tfae_finish

theorem polar_eq_zero_iff (T : E →L[ℂ] F) (x : E) : T.polar x = 0 ↔ T x = 0 := by
  exact ((T.apply_eq_zero_tfae x).out 2 1)

theorem modulus_eq_zero_iff (T : E →L[ℂ] F) (x : E) : |T| x = 0 ↔ T x = 0 := by
  exact ((T.apply_eq_zero_tfae x).out 3 1)

theorem polar_eq_zero_iff_modulus_eq_zero (T : E →L[ℂ] F) (x : E) :
    T.polar x = 0 ↔ |T| x = 0 := by
  exact ((T.apply_eq_zero_tfae x).out 2 3)

theorem ker_polar_eq (T : E →L[ℂ] F) : T.polar.ker = T.ker := by
  ext x
  simp [LinearMap.mem_ker, T.polar_eq_zero_iff]

theorem polar_comp_polar_adjoint_eq_starProjection (T : E →L[ℂ] F) :
    T.polar ∘L T.polar.adjoint = T.range.topologicalClosure.starProjection := by
  have hPP : |T|.range.topologicalClosure.orthogonalProjectionOnto
      ∘L |T|.range.topologicalClosure.subtypeL = ContinuousLinearMap.id ℂ _ := by
    ext x; simp
  unfold polar
  simp_rw +singlePass [adjoint_comp, comp_assoc, Submodule.adjoint_orthogonalProjectionOnto]
  rw [← comp_assoc |T|.range.topologicalClosure.orthogonalProjectionOnto, hPP]
  simp [polarₚₗᵢ_comp_adjoint]

theorem polar_adjoint_comp_polar_eq_starProjection (T : E →L[ℂ] F) :
    T.polar.adjoint ∘L T.polar = |T|.range.topologicalClosure.starProjection := by
  unfold polar
  simp_rw +singlePass [adjoint_comp, comp_assoc,
    ← comp_assoc T.polarₚₗᵢ.toContinuousLinearMap.adjoint]
  simp [Submodule.adjoint_orthogonalProjectionOnto, one_def, id_comp]
  rfl

theorem polar_comp_modulus (T : E →L[ℂ] F) : T.polar ∘L |T| = T := by
  ext x
  simp only [polar, ContinuousLinearMap.comp_apply]
  have hT : |T| x ∈ (|T|).toLinearMap.range := by simp
  nth_rw 4 [← polarₚₗᵢ_apply]
  simp
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨|T| x, |T|.range.le_topologicalClosure hT⟩

theorem polar_adjoint_comp_self_eq_modulus (T : E →L[ℂ] F) : T.polar.adjoint ∘L T = |T| := by
  nth_rw 2 [← T.polar_comp_modulus]
  erw [← comp_assoc, T.polar_adjoint_comp_polar_eq_starProjection]
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  exact Submodule.starProjection_eq_self_iff.mpr (|T|.range.le_topologicalClosure ⟨x, rfl⟩)

theorem polar_unique {T : E →L[ℂ] F} {W : E →L[ℂ] F} (h : W ∘L |T| = T)
    (hker : W.ker = T.ker) : W = T.polar := by
  ext x
  erw [← Submodule.starProjection_add_starProjection_orthogonal (K := T.ker) x, map_add, map_add]
  refine congr_arg₂ _ ?_ ?_
  · refine (fun z hz => ?_ : ∀ z ∈ T.ker, W z = T.polar z) _
      (Submodule.starProjection_apply_mem T.ker x)
    have hWz : z ∈ W.ker := hker ▸ hz
    have hTz : z ∈ T.polar.ker := T.ker_polar_eq ▸ hz
    erw [LinearMap.mem_ker.mp hTz, LinearMap.mem_ker.mp hWz]
  · refine (fun z hz => ?_ : ∀ z ∈ T.kerᗮ, W z = T.polar z) _
      (Submodule.starProjection_apply_mem T.kerᗮ x)
    have hcl : z ∈ |T|.range.topologicalClosure := by
      rw [← Submodule.orthogonal_orthogonal_eq_closure]
      refine Submodule.orthogonal_le (fun w hw => ?_) hz
      erw [LinearMap.mem_ker, ← norm_eq_zero, ← norm_modulus_apply]
      refine norm_eq_zero.mpr ((inner_self_eq_zero (𝕜 := ℂ) (x := |T| w)).mp ?_)
      rw [← ContinuousLinearMap.adjoint_inner_left, T.modulus_nonneg.isSelfAdjoint.adjoint_eq]
      exact (Submodule.mem_orthogonal _ _).mp hw _ ⟨|T| w, rfl⟩
    exact Set.EqOn.closure (s := (|T|.range : Set E))
      (by
        rintro _ ⟨y, rfl⟩
        exact (DFunLike.congr_fun h y).trans (DFunLike.congr_fun T.polar_comp_modulus y).symm
      )
      W.continuous
      T.polar.continuous
      hcl

theorem adjoint_modulus (T : E →L[ℂ] F) :
    T.adjoint.modulus = T.polar ∘L |T| ∘L T.polar.adjoint := by
  have h : (T.polar ∘L |T| ∘L T.polar.adjoint) ∘L
      (T.polar ∘L |T| ∘L T.polar.adjoint) = T ∘L T.adjoint := by
    calc
      (T.polar ∘L |T| ∘L T.polar.adjoint) ∘L (T.polar ∘L |T| ∘L T.polar.adjoint)
        = T.polar ∘L |T| ∘L
            ((T.polar.adjoint ∘L T.polar ∘L |T|) ∘L T.polar.adjoint) := by
          simp only [ContinuousLinearMap.comp_assoc]
      _ = T.polar ∘L |T| ∘L (|T| ∘L T.polar.adjoint) := by
          erw [T.polar_comp_modulus, T.polar_adjoint_comp_self_eq_modulus]
      _ = (T.polar ∘L |T|) ∘L (T.polar ∘L |T|).adjoint := by
          simp only [ContinuousLinearMap.adjoint_comp, T.modulus_nonneg.isSelfAdjoint.adjoint_eq,
            ContinuousLinearMap.comp_assoc]
      _ = T ∘L T.adjoint := by rw [T.polar_comp_modulus]
  change CFC.sqrt (T.adjoint.adjoint ∘L T.adjoint) = _
  rw [ContinuousLinearMap.adjoint_adjoint, ← h]
  exact CFC.sqrt_mul_self _
    (nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp T.modulus_nonneg).conj_adjoint T.polar))

theorem adjoint_polar (T : E →L[ℂ] F) : T.adjoint.polar = T.polar.adjoint := by
  apply Eq.symm
  apply polar_unique (T := T.adjoint)
  · erw [T.adjoint_modulus]
    calc
      T.polar.adjoint ∘L T.polar ∘L |T| ∘L T.polar.adjoint =
          (T.polar.adjoint ∘L (T.polar ∘L |T|)) ∘L T.polar.adjoint := by
        simp only [comp_assoc]
      _ = |T| ∘L T.polar.adjoint := by
        rw [T.polar_comp_modulus, T.polar_adjoint_comp_self_eq_modulus]
      _ = T.adjoint := by
        nth_rw 3 [← T.polar_comp_modulus]
        simp [adjoint_comp, T.modulus_nonneg.isSelfAdjoint.adjoint_eq]
  · ext x
    simp_rw [LinearMap.mem_ker]
    constructor
    · rintro hx
      refine ext_inner_right ℂ (fun y => ?_)
      rw [← T.polar_comp_modulus]
      simp [ContinuousLinearMap.adjoint_inner_left]
      erw [← ContinuousLinearMap.adjoint_inner_left, hx, inner_zero_left]
    · rintro hx
      have hxo : x ∈ T.range.topologicalClosureᗮ := by
        rw [Submodule.orthogonal_closure, Submodule.mem_orthogonal]
        rintro _ ⟨y, rfl⟩
        erw [← ContinuousLinearMap.adjoint_inner_right, hx, inner_zero_right]
      have h := congrArg (fun A => A x) T.polar_comp_polar_adjoint_eq_starProjection
      simp only [ContinuousLinearMap.comp_apply] at h
      apply (inner_self_eq_zero (𝕜 := ℂ)).mp
      erw [ContinuousLinearMap.adjoint_inner_left, h, inner_eq_zero_symm]
      exact Submodule.inner_right_of_mem_orthogonal
        (Submodule.starProjection_apply_mem _ x) hxo

theorem norm_polar_le_one (T : E →L[ℂ] F) : ‖T.polar‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul, polar, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]
  exact Submodule.norm_orthogonalProjectionOnto_apply_le _ x

def eSpNorm' (T : E →L[ℂ] F) : ℝ≥0∞ := (CFC.nnrpow |T| q.toNNReal).trace ^ (1 / q)

@[simp]
theorem eSpNorm'_apply (T : E →L[ℂ] F) :
    eSpNorm' q T = (CFC.nnrpow |T| q.toNNReal).trace ^ (1 / q) :=
  rfl

@[simp]
theorem eSpNorm'_zero {q} (hq : 0 < q) : eSpNorm' q (0 : E →L[ℂ] F) = 0 := by
  simp [eSpNorm', hq]

theorem modulus_trace' (T : E →L[ℂ] F) : eSpNorm' 1 T = |T|.trace := by
  simp [CFC.nnrpow_one]

theorem eSpNorm'_modulus (T : E →L[ℂ] F) : eSpNorm' q |T| = eSpNorm' q T := by
  simp

theorem eSpNorm'_eq_zero {q} (hq : 0 < q) (T : E →L[ℂ] F) : eSpNorm' q T = 0 ↔ T = 0 := by
  constructor
  · rintro hT
    have hq' : ¬(q < 0) := by sorry
    have hq'' : q.toNNReal ≠ 0 := by sorry
    simp [hq, hq', trace_eq_zero] at hT
    simp [← CFC.nnrpow_inv_eq 0 |T| hq'' (le_refl 0) (T.modulus_nonneg)] at hT
    exact (modulus_eq_zero T).mp (Eq.symm hT)
  · rintro hT
    simp [eSpNorm', hT, hq]

def eSpNorm (T : E →L[ℂ] F) : ℝ≥0∞ :=
  if p = 0 then 0 else
    if p = ∞ then ‖T‖ₑ else
      eSpNorm' p.toReal T

@[simp]
theorem eSpNorm_apply (T : E →L[ℂ] F) :
    eSpNorm p T = if p = 0 then 0 else
    if p = ∞ then ‖T‖ₑ else
      eSpNorm' p.toReal T :=
  rfl

theorem modulus_trac (T : E →L[ℂ] F) : |T|.trace = eSpNorm 1 T := by
  simp [CFC.nnrpow_one]

theorem eSpNorm_modulus (T : E →L[ℂ] F) : eSpNorm p |T| = eSpNorm p T := by
  sorry

open Topology Filter in
theorem IsCompactOperator.exists_hilbertBasis_hasEigenvector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hTc : IsCompactOperator T) (hTa : IsSelfAdjoint T) :
    ∃ (ι : Type*) (b : HilbertBasis ι ℂ H) (μ : ι → ℝ),
      (∀ i, Module.End.HasEigenvector (T : Module.End ℂ H) (μ i : ℂ) (b i)) ∧
      Filter.Tendsto μ Filter.cofinite (𝓝 0) := by
  sorry

theorem hasEigenvalue.nonneg {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {T : H →L[ℂ] H} (hT : 0 ≤ T)
    {b : HilbertBasis ι ℂ H} {μ : ι → ℝ} {i : ι}
    (he : Module.End.HasEigenvector (T : Module.End ℂ H) (μ i : ℂ) (b i)) : 0 ≤ μ i := by
  calc
    0 ≤ RCLike.re ⟪b i, T (b i)⟫_ℂ := (nonneg_iff_isPositive.mp hT).re_inner_nonneg_right (b i)
    _ = RCLike.re ⟪b i, (μ i) • (b i)⟫_ℂ := by
      rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at he
      simp at he
      rw [he.1]
    _ = RCLike.re (μ i) := by simp [inner_smul_right_eq_smul (b i) (b i) (μ i), b.orthonormal.1]

theorem hasEigenvector.rpow {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {T : H →L[ℂ] H} (hT : 0 ≤ T)
    {b : HilbertBasis ι ℂ H} {μ : ι → ℝ} {i : ι} (hq : 0 < q)
    (he : Module.End.HasEigenvector (T : Module.End ℂ H) (μ i : ℂ) (b i)) :
    Module.End.HasEigenvector ((CFC.nnrpow T q.toNNReal : H →L[ℂ] H) : Module.End ℂ H)
      (((μ i) ^ q : ℝ) : ℂ) (b i) := by sorry

theorem eSpNorm'_eq_tsum [Fact (0 < q)] (T : E →L[ℂ] F)
    {ι : Type*} (b : HilbertBasis ι ℂ E) {μ : ι → ℝ}
    (hb : ∀ i, Module.End.HasEigenvector (|T| : Module.End ℂ E) (μ i : ℂ) (b i)) :
    eSpNorm' q T = (∑' i, ENNReal.ofReal (μ i) ^ q) ^ (1 / q) := by
  have hT : 0 ≤ (|T| ^ q.toNNReal) := CFC.nnrpow_nonneg
  have hbq (i : ι) : (|T| ^ q.toNNReal) (b i) = (((μ i) ^ q : ℝ) : ℂ) • (b i) := by
    simpa using (hasEigenvector.rpow q T.modulus_nonneg Fact.out (hb i)).apply_eq_smul
  simp only [eSpNorm'_apply, trace, CFC.nnrpow_eq_pow, one_div, traceOfBasis_eq hT _ b]
  simp [traceOfBasis, ENNReal.ofReal_rpow_of_nonneg
    (ContinuousLinearMap.hasEigenvalue.nonneg T.modulus_nonneg (hb _))
    (Fact.out : 0 < q).le, hbq _,
    b.orthonormal.1 _]

theorem eSpNorm_eq_tsum [Fact (0 < p)] (T : E →L[ℂ] F)
    {ι : Type*} (b : HilbertBasis ι ℂ E) {μ : ι → ℝ}
    (hb : ∀ i, Module.End.HasEigenvector (|T| : Module.End ℂ E) (μ i : ℂ) (b i)) :
    eSpNorm p T = if p = ∞ then ⨆ i, ENNReal.ofReal (μ i)
      else (∑' i, ENNReal.ofReal (μ i) ^ p.toReal) ^ (1 / p.toReal) := by
  have hp : p ≠ 0 := (Fact.out : 0 < p).ne'
  simp only [eSpNorm_apply, hp, ↓reduceIte]
  by_cases hp : p = ∞
  · simp [hp]
    apply le_antisymm
    · -- define `opENorm_le_bound'` mirroring `opNorm_le_bound'` to get rid of the cases below.
      apply ContinuousLinearMap.opENorm_le_bound T
      intro e
      by_cases he : ‖e‖ₑ = 0
      · rw [enorm_eq_zero] at he
        simp [he]
      · -- use theorem to go to `⊢ ‖T e‖ₑ ^ 2 ≤ (⨆ i, ENNReal.ofReal (μ i)) ^ 2 * ‖e‖ₑ ^ 2`
        -- use calc to show
        --   ‖T e‖ₑ ^ 2 = ⟪T e, T e⟫
        --   __ = ⟪T.adjoint ∘ T e, e⟫
        --   __ = ∑' i, ⟪(T.adjoint ∘L T) e, b i⟫ • ⟪b i, e⟫
        --   __ = ∑' i, ⟪e, |T| ^ 2 (b i)⟫ • ⟪b i, e⟫
        --   __ = ∑' i, ⟪e, (μ i) ^ 2 (b i)⟫ • ⟪b i, e⟫
        --   __ = ∑' i, ENNReal.ofReal (μ i) ^ 2 * ⟪e, b i⟫ • ⟪b i, e⟫
        --   __ = ∑' i, ENNReal.ofReal (μ i) ^ 2 * |⟪e, b i⟫| ^ 2
        --   __ ≤ (⨆ i, ENNReal.ofReal (μ i)) ^ 2 * ∑' i, |⟪e, b i⟫| ^ 2
        --   __ = (⨆ i, ENNReal.ofReal (μ i)) ^ 2 * ‖e‖ₑ ^ 2
        sorry
      -- finish by taking the supremum over `this`
    · sorry
      -- take index that attains `⨆ i, ENNReal.ofReal (μ i)`. Call that `j : ι`
      -- use calc to show
      --   (⨆ i, ENNReal.ofReal (μ i)) ^ 2 = ENNReal.ofReal (μ j) ^ 2
      --   _ = ENNReal.ofReal ⟪b j, (μ j) ^ 2 • b j⟫_𝕜
      --   _ = ENNReal.ofReal ⟪b j, |T| ^ 2 (b j)⟫_𝕜
      --   _ = ENNReal.ofReal ⟪b j, (T.adjoint ∘L T) (b j)⟫_𝕜
      --   _ = ENNReal.ofReal ⟪T (b j), T (b j)⟫_𝕜
      --   _ = ‖T (b j)‖ₑ
      --   _ ≤ ‖T‖ₑ
  · let : Fact (0 < p.toReal) := by sorry
    simp only [hp, ↓reduceIte]
    exact eSpNorm'_eq_tsum p.toReal T b hb

/-- Hölder's inequality for Schatten-class operators -/
theorem eSpNorm_one_comp_le_mul (A : F →L[ℂ] E) (B : E →L[ℂ] F) {q : ℝ≥0∞}
    (hpq : p.HolderConjugate q) :
    eSpNorm 1 (A ∘L B) ≤ eSpNorm p A * eSpNorm q B := sorry

theorem trace_comp_eq_mul_right (A : F →L[ℂ] E) (B : E →L[ℂ] F) :
    (A ∘L B).trace ≤ eSpNorm 1 A * ‖B‖ₑ := by
  sorry

theorem trace_comp_eq_mul_left (A : F →L[ℂ] E) (B : E →L[ℂ] F) :
    (A ∘L B).trace ≤ ‖A‖ₑ * eSpNorm 1 B := by
  sorry

/-- Required for the `q > 1` part whilst matching the `q = 1`, so it was made a separate theorem. -/
private theorem eSpNorm'_one_add_le (A B : E →L[ℂ] F) :
    eSpNorm' 1 (A + B) ≤ eSpNorm' 1 A + eSpNorm' 1 B := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ E
  rw [modulus_trace']
  rw [← polar_adjoint_comp_self_eq_modulus (A + B)]
  rw [comp_add (adjoint (A + B).polar) A B]
  grw [trace_add_le, trace_comp_eq_mul_left, trace_comp_eq_mul_left]
  simp_rw [LinearIsometryEquiv.enorm_map adjoint, ← ofReal_norm]
  grw [norm_polar_le_one]
  simp

theorem eSpNorm'_add_le {q} (hq : 1 ≤ q) (A B : E →L[ℂ] F) :
    eSpNorm' q (A + B) ≤ eSpNorm' q A + eSpNorm' q B := by
  rcases hq.eq_or_lt with rfl | hq
  · exact eSpNorm'_one_add_le A B
  obtain ⟨p, hconj⟩ : ∃ p, q.HolderConjugate p := ⟨_, Real.HolderConjugate.conjExponent hq⟩
  set R := A + B with hR
  set D := CFC.nnrpow |R| (q - 1).toNNReal ∘L R.polar.adjoint with hD
  sorry

theorem eSpNorm_add_le [Fact (1 ≤ p)] (A B : E →L[ℂ] F) :
    eSpNorm p (A + B) ≤ eSpNorm p A + eSpNorm p B := by
  have hp : p ≠ 0 := sorry
  by_cases hp' : p = ∞
  · simp [hp, hp', ESeminormedAddMonoid.enorm_add_le A B]
  have hp'' : 1 ≤ p.toNNReal := by sorry
  simp [hp, hp', eSpNorm, -eSpNorm_apply, -eSpNorm'_apply]
  exact eSpNorm'_add_le hp'' A B

theorem eSpNorm_eq_zero [Fact (0 < p)] (T : E →L[ℂ] F) : eSpNorm p T = 0 ↔ T = 0 := by
  simp [-eSpNorm'_apply]
  refine ⟨fun hT ↦ ?_,  fun hT ↦ ?_⟩
  · have hp : ¬(p=0) := by sorry
    by_cases hp' : p = ∞
    · simp_all
    · have : 0 < p.toReal := by sorry
      simp [hp, hp', this, -eSpNorm'_apply] at hT
      exact (T.eSpNorm'_eq_zero this).mp hT
  · rintro hp
    by_cases hp' : p = ∞
    · simp [hp', hT]
    · have : 0 < p.toReal := by sorry
      simp [hp', hT, this]

def spNorm (T : E →L[ℂ] F) : ℝ := (eSpNorm p T).toReal

def MemSp (T : E →L[ℂ] F) : Prop := eSpNorm p T < ∞

set_option linter.unusedVariables false in
def Sp (p : ℝ≥0∞) (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] : Type _ :=
  E →L[ℂ] F

end

namespace Sp

variable (p : ℝ≥0∞) (q : ℝ) {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

instance : FunLike (Sp p E F) E F := inferInstanceAs (FunLike (E →L[ℂ] F) E F)
instance : ContinuousLinearMapClass (Sp p E F) ℂ E F :=
  inferInstanceAs (ContinuousLinearMapClass (E →L[ℂ] F) ℂ E F)
instance : AddCommGroup (Sp p E F) := inferInstanceAs (AddCommGroup (E →L[ℂ] F))
instance : Module ℂ (Sp p E F) := inferInstanceAs (Module ℂ (E →L[ℂ] F))

def toCLM : (Sp p E F) ≃ₗ[ℂ] (E →L[ℂ] F) := LinearEquiv.refl _ _
def ofCLM : (E →L[ℂ] F) ≃ₗ[ℂ] (Sp p E F) := LinearEquiv.refl _ _

instance : ENorm (Sp p E F) where
  enorm T := eSpNorm p (toCLM p T)

@[simp]
theorem enorm_def (T : Sp p E F) : ‖T‖ₑ = eSpNorm p (toCLM p T) := rfl

@[simp]
theorem enorm_zero : ‖(0 : Sp p E F)‖ₑ = 0 := by
  simp
  rintro hn0 hnt
  exact ENNReal.toReal_pos hn0 hnt

theorem enorm_add_le [Fact (1 ≤ p)] (T T' : Sp p E F) : ‖T + T'‖ₑ ≤ ‖T‖ₑ + ‖T'‖ₑ :=
  eSpNorm_add_le _ _ _

theorem enorm_eq_zero [Fact (0 < p)] (T : Sp p E F) : ‖T‖ₑ = 0 ↔ T = 0 :=
  eSpNorm_eq_zero _ _

local instance [Fact (1 ≤ p)] : Fact (0 < p) := sorry

instance [Fact (1 ≤ p)] : EMetricSpace (Sp p E F) where
  edist f g := ‖f - g‖ₑ
  edist_self f := by
    rw [sub_self, enorm_zero]
  edist_comm f g:= by
    simp [eSpNorm, enorm_sub_rev, ← modulus_neg (toCLM p f - toCLM p g)]
  edist_triangle f g h := by
    simpa using enorm_add_le p (f-g) (g-h)
  eq_of_edist_eq_zero hfg := by
    rw [← sub_eq_zero]
    exact (enorm_eq_zero p _).mp hfg

instance [Fact (1 ≤ p)] : ENormedAddMonoid (Sp p E F) where
  continuous_enorm := by
    refine continuous_of_le_add_edist 1 ENNReal.one_ne_top fun f g => ?_
    have := enorm_add_le p g (f - g)
    rw [add_sub_cancel g f] at this
    rw [one_mul]
    exact this
  enorm_zero := enorm_zero p
  enorm_add_le := enorm_add_le p
  enorm_eq_zero := enorm_eq_zero p

end Sp

namespace MemSp

end MemSp

end ContinuousLinearMap
