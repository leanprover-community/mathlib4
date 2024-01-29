import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner

open IsROrC Real Filter
namespace InnerProductSpace

variable {ι₁ ι₂ 𝕜 E F A : Type*}

noncomputable section prodBasis

variable [IsROrC 𝕜] [Fintype ι₁] [Fintype ι₂]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

def _root_.OrthonormalBasis.prod (v : OrthonormalBasis ι₁ 𝕜 E) (w : OrthonormalBasis ι₂ 𝕜 F) :
    OrthonormalBasis (ι₁ ⊕ ι₂) 𝕜 (WithLp 2 (E × F)) :=
  ((v.toBasis.prod w.toBasis).map (WithLp.linearEquiv 2 𝕜 (E × F)).symm).toOrthonormalBasis
  (by
    constructor
    · simp [Sum.forall, norm_eq_sqrt_inner (𝕜 := 𝕜), Real.sqrt_eq_one]
      simp [← sqrt_eq_one, ← norm_eq_sqrt_inner (𝕜 := 𝕜), v.orthonormal.1, w.orthonormal.1]
    · unfold Pairwise
      simp [Sum.forall]
      exact ⟨v.orthonormal.2, w.orthonormal.2⟩)

@[simp] theorem _root_.OrthonormalBasis.prod_apply (v : OrthonormalBasis ι₁ 𝕜 E)
    (w : OrthonormalBasis ι₂ 𝕜 F) :
    ∀ i : ι₁ ⊕ ι₂, v.prod w i = Sum.elim ((LinearMap.inl 𝕜 E F) ∘ v) ((LinearMap.inr 𝕜 E F) ∘ w) i := by
  rw [Sum.forall]
  unfold OrthonormalBasis.prod
  constructor
  · intro
    simp
    rfl
  · intro
    simp
    rfl

end prodBasis

noncomputable section prodMeasure

variable [IsROrC 𝕜] [Fintype ι₁] [Fintype ι₂]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem _root_.Basis.prod_parallelepiped (v : Basis ι₁ ℝ E) (w : Basis ι₂ ℝ F) :
    (v.prod w).parallelepiped = v.parallelepiped.prod w.parallelepiped := by
  ext x
  simp only [Basis.coe_parallelepiped, TopologicalSpace.PositiveCompacts.coe_prod, Set.mem_prod]
  simp_rw [mem_parallelepiped_iff]
  constructor
  · intro h
    rcases h with ⟨t, ht1, ht2⟩
    constructor
    · use t ∘ Sum.inl
      constructor
      · simp only [Set.mem_Icc] at ht1 ⊢
        exact ⟨fun x ↦ ht1.1 (Sum.inl x), fun x ↦ ht1.2 (Sum.inl x)⟩
      simp [ht2, Prod.fst_sum, Prod.snd_sum]
    · use t ∘ Sum.inr
      constructor
      · simp only [Set.mem_Icc] at ht1 ⊢
        exact ⟨fun x ↦ ht1.1 (Sum.inr x), fun x ↦ ht1.2 (Sum.inr x)⟩
      simp [ht2, Prod.fst_sum, Prod.snd_sum]
  intro h
  rcases h with ⟨⟨t, ht1, ht2⟩, ⟨s, hs1, hs2⟩⟩
  use Sum.elim t s
  constructor
  · simp only [Set.mem_Icc] at ht1 hs1 ⊢
    constructor
    · have : ∀ x : ι₁ ⊕ ι₂, 0 ≤ Sum.elim t s x := by
        rw [Sum.forall]
        simp only [Sum.elim_inr, Sum.elim_inl]
        exact ⟨ht1.1, hs1.1⟩
      exact this
    · have : ∀ x : ι₁ ⊕ ι₂, Sum.elim t s x ≤ 1 := by
        rw [Sum.forall]
        simp only [Sum.elim_inr, Sum.elim_inl]
        exact ⟨ht1.2, hs1.2⟩
      exact this
  ext
  · simp [ht2, Prod.fst_sum]
  · simp [hs2, Prod.snd_sum]

theorem _root_.Basis.prod_addHaar (v : Basis ι₁ ℝ E) (w : Basis ι₂ ℝ F) :
    (v.prod w).addHaar = MeasureTheory.Measure.prod v.addHaar w.addHaar := by
  rw [(v.prod w).addHaar_eq_iff, Basis.prod_parallelepiped]
  simp [Basis.addHaar_self]

end prodMeasure

noncomputable section

variable [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (K : Submodule 𝕜 E) [CompleteSpace K]

theorem blubb (v : Kᗮ) : orthogonalProjection K v = 0 := by
  rcases v with ⟨v, hv⟩
  simpa only [orthogonalProjection_eq_zero_iff]

def foo (K : Submodule 𝕜 E) [CompleteSpace K] : E →ₗᵢ[𝕜] WithLp 2 (K × Kᗮ) :=
  LinearMap.isometryOfInner
  ((WithLp.linearEquiv 2 𝕜 (K × Kᗮ)).symm.comp
    ((orthogonalProjection K).prod (orthogonalProjection Kᗮ)).toLinearMap)
  (by
    intro x y
    simp only [ContinuousLinearMap.coe_prod, LinearMap.coe_comp, LinearEquiv.coe_coe,
      WithLp.linearEquiv_symm_apply, Function.comp_apply, LinearMap.prod_apply, Pi.prod,
      ContinuousLinearMap.coe_coe, WithLp.prod_inner_apply, WithLp.equiv_symm_fst,
      inner_orthogonalProjection_eq_of_mem_left, WithLp.equiv_symm_snd,
      orthogonalProjection_orthogonal_val]
    have hx : x ∈ K ⊔ Kᗮ := by
      simp only [Submodule.sup_orthogonal_of_completeSpace, Submodule.mem_top]
    rw [Submodule.mem_sup'] at hx
    rcases hx with ⟨v1x, v2x, hx⟩
    have hy : y ∈ K ⊔ Kᗮ := by
      simp only [Submodule.sup_orthogonal_of_completeSpace, Submodule.mem_top]
    rw [Submodule.mem_sup'] at hy
    rcases hy with ⟨v1y, v2y, hy⟩
    rw [← hx, ← hy]
    simp only [map_add, orthogonalProjection_mem_subspace_eq_self, blubb, add_zero, add_sub_cancel']
    rw [inner_add_left] )

@[simp] theorem foo_apply_fst (K : Submodule 𝕜 E) [CompleteSpace K] (a : K) :
    (foo K a).1 = a := by
  unfold foo
  simp

@[simp] theorem foo_apply_snd (K : Submodule 𝕜 E) [CompleteSpace K] (a : K) :
    (foo K a).2 = 0 := by
  unfold foo
  simp

@[simp] theorem foo_apply'_fst (K : Submodule 𝕜 E) [CompleteSpace K] (a : Kᗮ) :
    (foo K a).1 = 0 := by
  unfold foo
  simp

@[simp] theorem foo_apply'_snd (K : Submodule 𝕜 E) [CompleteSpace K] (a : Kᗮ) :
    (foo K a).2 = a := by
  unfold foo
  simp

theorem foo_apply (K : Submodule 𝕜 E) [CompleteSpace K] (a : K) :
    foo K a = (WithLp.equiv 2 (K × Kᗮ)).symm (a, 0) := by
  unfold foo
  simp

theorem foo_apply' (K : Submodule 𝕜 E) [CompleteSpace K] (a : Kᗮ) :
    foo K a = (WithLp.equiv 2 (K × Kᗮ)).symm (0, a) := by
  unfold foo
  simp

def foo' (K : Submodule 𝕜 E) [CompleteSpace K] : E ≃ₗᵢ[𝕜] WithLp 2 (K × Kᗮ) :=
  LinearIsometryEquiv.ofSurjective (foo K)
  (by
    intro y
    use (WithLp.equiv 2 (K × Kᗮ) y).fst + (WithLp.equiv 2 (K × Kᗮ) y).snd
    apply (WithLp.equiv 2 (K × Kᗮ)).injective
    ext
    · simp [foo_apply, foo_apply', Prod.fst_add (y.1, 0) (0, y.2)]
    · simp [foo_apply, foo_apply', Prod.snd_add (y.1, 0) (0, y.2)] )

theorem foo'_apply (K : Submodule 𝕜 E) [CompleteSpace K] (a : K) :
    foo' K a = (WithLp.equiv 2 (K × Kᗮ)).symm (a, 0) := by
  unfold foo'
  simp [foo_apply]

theorem foo'_apply' (K : Submodule 𝕜 E) [CompleteSpace K] (a : Kᗮ) :
    foo' K a = (WithLp.equiv 2 (K × Kᗮ)).symm (0, a) := by
  unfold foo'
  simp [foo_apply']

end

open MeasureTheory MeasureTheory.Measure FiniteDimensional

variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
   [iMF : MeasurableSpace F] [BorelSpace F]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [iME : MeasurableSpace E] [BorelSpace E]

variable (f : E ≃ₗᵢ[ℝ] F)

/-- Every linear isometry on a real finite dimensional Hilbert space is measure-preserving. -/
theorem _root_.LinearIsometryEquiv.measurePreserving : MeasurePreserving f := by
  refine ⟨f.toContinuousLinearEquiv.continuous.measurable, ?_⟩
  rcases exists_orthonormalBasis ℝ E with ⟨w, b, _hw⟩
  erw [← OrthonormalBasis.addHaar_eq_volume b, ← OrthonormalBasis.addHaar_eq_volume (b.map f),
    Basis.map_addHaar _ f.toContinuousLinearEquiv]
  congr

def _root_.LinearIsometryEquiv.toMeasureEquiv : E ≃ᵐ F where
  toEquiv := f
  measurable_toFun := f.continuous.measurable
  measurable_invFun := f.symm.continuous.measurable

@[simp] theorem _root_.LinearIsometryEquiv.toMeasureEquiv_apply (x : E) :
  f.toMeasureEquiv x = f x := rfl

theorem _root_.LinearIsometryEquiv.toMeasureEquiv_symm_apply (x : F) :
  f.symm.toMeasureEquiv x = f.symm x := rfl

variable  [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem _root_.LinearIsometryEquiv.integral_comp (g : F → A) :
    ∫ (x : E), g (f x) = ∫ (y : F), g y :=
  f.measurePreserving.integral_comp' (f := f.toMeasureEquiv) g

theorem _root_.LinearIsometryEquiv.integrable_comp (g : F → A) :
    Integrable (g ∘ f) ↔ Integrable g :=
  f.measurePreserving.integrable_comp_emb f.toMeasureEquiv.measurableEmbedding

instance : MeasurableSpace (WithLp 2 (E × F)) := iME.prod iMF

instance : BorelSpace (WithLp 2 (E × F)) := Prod.borelSpace

instance : FiniteDimensional ℝ (WithLp 2 (E × F)) :=
  FiniteDimensional.of_injective (WithLp.linearEquiv 2 ℝ (E × F)).toLinearMap
    (WithLp.linearEquiv 2 ℝ (E × F)).injective

variable (E F)

theorem _root_.WithLp.equiv_prod_measurePreserving : MeasurePreserving (WithLp.equiv 2 (E × F)) := by
  refine ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ E F).continuous.measurable, ?_⟩
  rw [MeasureTheory.Measure.volume_eq_prod]
  rcases exists_orthonormalBasis ℝ E with ⟨w1, b1, _hw⟩
  rcases exists_orthonormalBasis ℝ F with ⟨w2, b2, _hw⟩
  rw [← OrthonormalBasis.addHaar_eq_volume b1, ← OrthonormalBasis.addHaar_eq_volume b2]
  rw [← OrthonormalBasis.addHaar_eq_volume (b1.prod b2)]
  erw [Basis.map_addHaar _ (WithLp.prodContinuousLinearEquiv 2 ℝ E F)]
  rw [← Basis.prod_addHaar]
  congr
  apply Basis.eq_of_apply_eq
  rw [Sum.forall]
  constructor
  · intro
    simp
    rfl
  · intro
    simp
    rfl
