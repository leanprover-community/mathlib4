/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Extend
public import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.VectorBundle.Misc
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.TrivPrelim

/-!
# Supporting lemmas for CovariantDerivative.Basic

TODO: PR all this to appropriate places.

-/

open Bundle Filter Module Topology Set

open scoped Bundle Manifold ContDiff


@[expose] public section tangent_bundle_normedSpace

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

instance (f : F) : CoeOut (TangentSpace 𝓘(ℝ, F) f) F :=
  ⟨fun x ↦ x⟩

end tangent_bundle_normedSpace

@[expose] public section mfderiv

open Function

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

-- unused; could move to `SpecificFunctions`
lemma injective_mfderiv_of_eventually_leftInverse
    {f : M → M'} (x : M) {g : M' → M}
    (hg : MDiffAt g (f x)) (hf : MDiffAt f x)
    (hfg : g ∘ f =ᶠ[𝓝 x] id) : Injective (mfderiv% f x) := by
  have := mfderiv_comp x hg hf
  rw [hfg.mfderiv_eq] at this
  have : LeftInverse (mfderiv% g (f x)) (mfderiv% f x) := by
    intro u
    simpa using congr($this u).symm
  exact LeftInverse.injective this

-- unused; could move to `SpecificFunctions`
lemma surjective_mfderiv_of_eventually_rightInverse
    {f : M → M'} {x : M} {y : M'} (hxy : y = f x) {g : M' → M}
    (hg : MDiffAt g y) (hf : MDiffAt f x)
    (hfg : g ∘ f =ᶠ[𝓝 x] id) : Surjective (mfderiv% g y) := by
  rw [hxy] at hg
  have := mfderiv_comp x hg hf
  rw [hfg.mfderiv_eq] at this
  have : RightInverse (mfderiv% f x) (mfderiv% g (f x)) := by
    intro u
    simpa using congr($this u).symm
  rw [← hxy] at this
  exact RightInverse.surjective this

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

set_option backward.isDefEq.respectTransparency false in
-- cleaned up and PRed in #34262
lemma mfderiv_const_smul (s : M → F) {x : M} (a : 𝕜) (v : TangentSpace I x) :
    mfderiv% (a • s) x v = a • mfderiv% s x v := by
  by_cases hs : MDiffAt s x
  · have hs' := hs.const_smul a
    suffices
      (fderivWithin 𝕜 ((a • s) ∘ (chartAt H x).symm ∘ I.symm) (range I) (I ((chartAt H x) x))) v =
       a • (fderivWithin 𝕜 (s ∘ (chartAt H x).symm ∘ I.symm) (range I)
       (I ((chartAt H x) x))) v by simpa [mfderiv, hs, hs']
    change fderivWithin 𝕜 (a • (s ∘ ↑(chartAt H x).symm ∘ ↑I.symm)) _ _ _ = _
    rw [fderivWithin_const_smul_field _ I.uniqueDiffWithinAt_image ]
    rfl
  · by_cases ha : a = 0
    · have : a • s = 0 := by ext; simp [ha]
      rw [this, ha]
      change (mfderiv I 𝓘(𝕜, F) (fun _ ↦ 0) x) v = _
      simp
    have hs' : ¬ MDiffAt (a • s) x :=
      fun h ↦ hs (by simpa [ha] using h.const_smul a⁻¹)
    rw [mfderiv_zero_of_not_mdifferentiableAt hs, mfderiv_zero_of_not_mdifferentiableAt hs']
    simp
    rfl

-- PRed and cleaned up in #34263
set_option linter.flexible false in -- FIXME
lemma mfderiv_smul [IsManifold I 1 M] {f : M → F} {s : M → 𝕜} {x : M} (hf : MDiffAt f x)
    (hs : MDiffAt s x) (v : TangentSpace I x) :
    letI dsxv : 𝕜 := mfderiv% s x v
    letI dfxv : F := mfderiv% f x v
    mfderiv% (s • f) x v = (s x) • dfxv + dsxv • f x := by
  set φ := chartAt H x
  -- TODO: the next two have should be special cases of the same lemma
  have hs' : DifferentiableWithinAt 𝕜 (s ∘ φ.symm ∘ I.symm) (range I) (I (φ x)) := by
    have hφ := mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x) (I := I)
    have : (extChartAt I x).symm (extChartAt I x x) = x := extChartAt_to_inv x
    rw [← this] at hs
    have := hs.comp_mdifferentiableWithinAt (extChartAt I x x) hφ
    exact mdifferentiableWithinAt_iff_differentiableWithinAt.mp this
  have hf' : DifferentiableWithinAt 𝕜 (f ∘ φ.symm ∘ I.symm) (range I) (I (φ x)) := by
    have hφ := mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x) (I := I)
    have : (extChartAt I x).symm (extChartAt I x x) = x := extChartAt_to_inv x
    rw [← this] at hf
    have := hf.comp_mdifferentiableWithinAt (extChartAt I x x) hφ
    exact mdifferentiableWithinAt_iff_differentiableWithinAt.mp this
  have hsf : MDiffAt (s • f) x := hs.smul hf
  simp [mfderiv, hsf, hs, hf]
  have uniq : UniqueDiffWithinAt 𝕜 (range I) (I (φ x)) :=
    ModelWithCorners.uniqueDiffWithinAt_image I
  erw [fderivWithin_smul uniq hs' hf']
  simp [φ.left_inv (ChartedSpace.mem_chart_source x)]
  rfl
end mfderiv

@[expose] public section -- TODO: think if we want to expose all definitions!

section general_lemmas -- those lemmas should move

section linear_algebra
variable (𝕜 : Type*) [Field 𝕜]
         {E : Type*} [AddCommGroup E] [Module 𝕜 E]
         {E' : Type*} [AddCommGroup E'] [Module 𝕜 E']

lemma exists_map_of (u : E) (u' : E') :
    ∃ φ : E →ₗ[𝕜] E', (u = 0 → u' = 0) → φ u = u' := by
  by_cases h : u = 0
  · simp [h]
    tauto
  · have indep : LinearIndepOn 𝕜 id {u} := LinearIndepOn.singleton h
    let s := indep.extend (subset_univ _)
    have hus : u ∈ s := singleton_subset_iff.mp <| indep.subset_extend (subset_univ _)
    use (Basis.extend indep).constr (M' := E') (S := 𝕜) fun _ ↦ u'
    simpa [h, Basis.extend_apply_self] using (Basis.extend indep).constr_basis _ _ ⟨u, hus⟩

open Classical in
noncomputable def map_of (u : E) (u' : E') : E →ₗ[𝕜] E' := (exists_map_of 𝕜 u u').choose

variable {𝕜}
lemma map_of_spec (u : E) (u' : E') (h : u = 0 → u' = 0) : map_of 𝕜 u u' u = u' :=
  (exists_map_of 𝕜 u u').choose_spec h
end linear_algebra


section
variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] -- [IsManifold I 0 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']


variable (𝕜) in
noncomputable def map_of_loc_one_jet (e u : E) (e' u' : E') : E → E' :=
  fun x ↦ e' + map_of 𝕜 u u' (x - e)

lemma map_of_loc_one_jet_spec [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    (e u : E) (e' u' : E') (hu : u = 0 → u' = 0) :
    map_of_loc_one_jet 𝕜 e u e' u' e = e' ∧
    DifferentiableAt 𝕜 (map_of_loc_one_jet 𝕜 e u e' u') e ∧
    fderiv 𝕜 (map_of_loc_one_jet 𝕜 e u e' u') e u = u' := by
  unfold map_of_loc_one_jet
  let φ := (map_of 𝕜 u u').toContinuousLinearMap
  have diff : Differentiable 𝕜 (map_of 𝕜 u u') :=
    (map_of 𝕜 u u').toContinuousLinearMap.differentiable
  refine ⟨by simp, ?_, ?_⟩
  · apply (differentiableAt_const e').add
    apply diff.differentiableAt.comp
    fun_prop
  · simp only [map_sub, fderiv_const_add]
    rw [fderiv_sub_const]
    change (fderiv 𝕜 φ e) u = _
    rw [φ.hasFDerivAt.fderiv]
    exact map_of_spec u u' hu

noncomputable
def map_of_one_jet {x : M} (u : TangentSpace I x) {x' : M'} (u' : TangentSpace I' x') :
    M → M' :=
  letI ψ := extChartAt I' x'
  letI φ := extChartAt I x
  ψ.symm ∘
  (map_of_loc_one_jet 𝕜 (φ x) (mfderiv% φ x u) (ψ x') (mfderiv% ψ x' u')) ∘
  φ

-- TODO: version assuming `x` and `x'` are in the interior, or maybe `x` is enough.

/-- For any `(x, u) ∈ TM` and `(x', u') ∈ TM'`, `map_of_one_jet u u'` sends `x` to `x'` and
its derivative sends `u` to `u'`. We need to assume the target manifold `M'` has no boundary
since we cannot hope the result is `x` and `x'` are boundary points and `u` is inward
while `u'` is outward.
-/
lemma map_of_one_jet_spec [IsManifold I 1 M] [IsManifold I' 1 M']
      [BoundarylessManifold I' M']
      [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
      {x : M} (u : TangentSpace I x) {x' : M'}
      (u' : TangentSpace I' x') (hu : u = 0 → u' = 0) :
    map_of_one_jet u u' x = x' ∧
    MDiffAt (map_of_one_jet u u') x ∧
    mfderiv% (map_of_one_jet u u') x u = u' := by
  let ψ := extChartAt I' x'
  let φ := extChartAt I x
  let g := map_of_loc_one_jet 𝕜 (φ x) (mfderiv% φ x u) (ψ x') (mfderiv% ψ x' u')
  have hψ : MDiffAt ψ x' := mdifferentiableAt_extChartAt (ChartedSpace.mem_chart_source x')
  have hφ : MDiffAt φ x := mdifferentiableAt_extChartAt (ChartedSpace.mem_chart_source x)
  replace hu : mfderiv% φ x u = 0 → mfderiv% ψ x' u' = 0 := by
    have : Function.Injective (mfderiv% φ x) :=
      (isInvertible_mfderiv_extChartAt (mem_extChartAt_source x)).injective
    rw [injective_iff_map_eq_zero] at this
    have := map_zero (mfderiv% ψ x')
    grind
  rcases map_of_loc_one_jet_spec (𝕜 := 𝕜) (φ x) (mfderiv% φ x u) (ψ x') (mfderiv% ψ x' u') hu with
    ⟨h : g (φ x) = ψ x', h', h''⟩
  have hg : MDiffAt g (φ x) := mdifferentiableAt_iff_differentiableAt.mpr h'
  have hgφ : MDiffAt (g ∘ φ) x := h'.comp_mdifferentiableAt hφ
  let Ψi : E' → M' := ψ.symm -- FIXME: this is working around a limitation of MDiffAt elaborator
  have hψi : MDiffAt Ψi (g (φ x)) := by
    rw [h]
    have := mdifferentiableWithinAt_extChartAt_symm (I := I') (mem_extChartAt_target x')
    exact this.mdifferentiableAt (range_mem_nhds_isInteriorPoint <|
      BoundarylessManifold.isInteriorPoint' x')
  unfold map_of_one_jet
  refold_let g φ ψ at *
  refine ⟨by simp [h, ψ], hψi.comp x hgφ, ?_⟩
  rw [mfderiv_comp x hψi hgφ, mfderiv_comp x hg hφ, mfderiv_eq_fderiv]
  change (mfderiv% Ψi (g (φ x))) (fderiv 𝕜 g (φ x) <| mfderiv% φ x u) = u'
  rw [h] at hψi
  rw [h'', h, ← mfderiv_comp_apply x' hψi hψ]
  have : Ψi ∘ ψ =ᶠ[𝓝 x'] id := by
    have : ∀ᶠ z in 𝓝 x', z ∈ ψ.source := extChartAt_source_mem_nhds x'
    filter_upwards [this] with z hz
    exact ψ.left_inv hz
  simp [this.mfderiv_eq]
  rfl
end

end general_lemmas

section tensoriality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

variable
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [(x : M) → AddCommGroup (V x)] [(x : M) → Module ℝ (V x)] [(x : M) → TopologicalSpace (V x)]
  -- TODO can probably remove the next two hypotheses, by transport
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

variable
  (F' : Type*) [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')] [(x : M) → AddCommGroup (V' x)]
  [(x : M) → Module ℝ (V' x)] [(x : M) → TopologicalSpace (V' x)]
  -- TODO can probably remove the next two hypotheses, by transport
  [∀ x, IsTopologicalAddGroup (V' x)] [∀ x, ContinuousSMul ℝ (V' x)]
  [FiberBundle F' V'] [VectorBundle ℝ F' V']

noncomputable def mkTensorAt
    -- `φ` explicit to make it easier to generate the side conditions at point of use
    (φ : (Π x : M, V x) → (Π x, V' x)) (x)
    (φ_smul : ∀ f : M → ℝ, ∀ σ, MDiffAt f x → MDiffAt (T% σ) x →
      φ (f • σ) x = f x • φ σ x)
    (φ_add : ∀ σ σ', MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      φ (σ + σ') x = φ σ x + φ σ' x) :
    V x →L[ℝ] V' x :=
    let Ψ : V x ≃L[ℝ] F := (trivializationAt F V x).continuousLinearEquivAt ℝ x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    have : T2Space (V x) := Ψ.symm.toHomeomorph.t2Space
    have : FiniteDimensional ℝ (V x) := Ψ.symm.toLinearEquiv.finiteDimensional
    LinearMap.toContinuousLinearMap {
      toFun v := φ (_root_.extend I F v) x
      map_add' v₁ v₂ := by
        rw [← φ_add]
        · apply tensoriality_criterion I F _ F' _ _ _ _ φ_smul φ_add
          · exact mdifferentiable_extend ..
          · apply mdifferentiableAt_add_section
            · exact mdifferentiable_extend ..
            · exact mdifferentiable_extend ..
          · simp
        · exact mdifferentiable_extend ..
        · exact mdifferentiable_extend ..
      map_smul' c v := by
        dsimp
        rw [← φ_smul (fun _ ↦ c)]
        · apply tensoriality_criterion I F _ F' _ _ _ _ φ_smul φ_add
          · exact mdifferentiable_extend ..
          · apply MDifferentiableAt.smul_section
            · exact mdifferentiableAt_const
            · exact mdifferentiable_extend ..
          · simp
        · exact mdifferentiable_const ..
        · exact mdifferentiable_extend .. }

variable {I} in
theorem mkTensorAt_apply
    -- `φ` explicit to make it easier to generate the side conditions at point of use
    {φ : (Π x : M, V x) → (Π x, V' x)} {x}
    (φ_smul : ∀ f : M → ℝ, ∀ σ, MDiffAt f x → MDiffAt (T% σ) x →
      φ (f • σ) x = f x • φ σ x)
    (φ_add : ∀ σ σ', MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      φ (σ + σ') x = φ σ x + φ σ' x) {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) :
    mkTensorAt I F F' φ x φ_smul φ_add (σ x) = φ σ x := by
  apply tensoriality_criterion I F _ F' _ _ hσ _ φ_smul φ_add
  · exact mdifferentiable_extend ..
  · simp

noncomputable def mkTensor
    -- `φ` explicit to make it easier to generate the side conditions at point of use
    (φ : (Π x : M, V x) → (Π x, V' x))
    -- TODO could weaken `φ_smul` and `φ_add` to require the property only globally, is it useful?
    (φ_smul : ∀ x, ∀ f : M → ℝ, ∀ σ, MDiffAt f x → MDiffAt (T% σ) x → φ (f • σ) x = f x • φ σ x)
    (φ_add : ∀ x, ∀ σ σ', MDiffAt (T% σ) x → MDiffAt (T% σ') x → φ (σ + σ') x = φ σ x + φ σ' x)
    (x : M) :
    V x →L[ℝ] V' x :=
  mkTensorAt I F F' φ x (φ_smul x) (φ_add x)

theorem contMDiff_mkTensor
    (φ : (Π x : M, V x) → (Π x, V' x))
    (φ_smul : ∀ x, ∀ f : M → ℝ, ∀ σ, MDiffAt f x → MDiffAt (T% σ) x → φ (f • σ) x = f x • φ σ x)
    (φ_add : ∀ x, ∀ σ σ', MDiffAt (T% σ) x → MDiffAt (T% σ') x → φ (σ + σ') x = φ σ x + φ σ' x)
    -- hopefully this is the correct smoothness criterion!
    {k} (φ_contMDiff : ∀ (σ : Π x : M, V x), CMDiff k (T% σ) → CMDiff k (T% (φ σ))) :
    -- elaborators not working here
    let T (x : M) : TotalSpace (F →L[ℝ] F') (fun x ↦ V x →L[ℝ] V' x) :=
      ⟨x, mkTensor I F F' φ φ_smul φ_add x⟩
    ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F')) k T := by
  sorry

-- TODO allow the two input types to differ
noncomputable def mk2TensorAt
    -- `φ` explicit to make it easier to generate the side conditions at point of use
    (φ : (Π x : M, V x) → (Π x : M, V x) → (Π x, V' x)) {x}
    (σ_smul : ∀ {f : M → ℝ}, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x →
      φ (f • σ) τ x = f x • φ σ τ x)
    (σ_add : ∀ {σ σ' τ}, MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      φ (σ + σ') τ x = φ σ τ x + φ σ' τ x)
    (τ_smul : ∀ {f : M → ℝ}, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% τ) x →
        φ σ (f • τ) x = f x • φ σ τ x)
    (τ_add : ∀ {σ τ τ'}, MDiffAt (T% τ) x → MDiffAt (T% τ') x →
        φ σ (τ + τ') x = φ σ τ x + φ σ τ' x) :
    V x →L[ℝ] V x →L[ℝ] V' x :=
    let Ψ : V x ≃L[ℝ] F := (trivializationAt F V x).continuousLinearEquivAt ℝ x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    have : T2Space (V x) := Ψ.symm.toHomeomorph.t2Space
    have : FiniteDimensional ℝ (V x) := Ψ.symm.toLinearEquiv.finiteDimensional
    have H : IsBilinearMap ℝ
      (fun (v w : V x) ↦ φ (_root_.extend I F v) (_root_.extend I F w) x) :=
    { add_left v₁ v₂ w := by
        rw [← σ_add]
        · apply tensoriality_criterion₂ I F _ F' _ _ _ _ _ _ rfl σ_smul σ_add τ_smul τ_add
          · exact mdifferentiable_extend ..
          · apply mdifferentiableAt_add_section
            · exact mdifferentiable_extend ..
            · exact mdifferentiable_extend ..
          · exact mdifferentiable_extend ..
          · exact mdifferentiable_extend ..
          · simp
        · exact mdifferentiable_extend ..
        · exact mdifferentiable_extend ..
      smul_left c v w := by
        rw [← σ_smul (f := fun _ ↦ c)]
        · apply tensoriality_criterion₂ I F _ F' _ _ _ _ _ _ rfl σ_smul σ_add τ_smul τ_add
          · exact mdifferentiable_extend ..
          · apply MDifferentiableAt.smul_section
            · exact mdifferentiableAt_const
            · exact mdifferentiable_extend ..
          · exact mdifferentiable_extend ..
          · exact mdifferentiable_extend ..
          · simp
        · exact mdifferentiable_const ..
        · exact mdifferentiable_extend ..
      add_right v w₁ w₂ := by
        rw [← τ_add]
        · apply tensoriality_criterion₂ I F _ F' _ _ _ _ _ rfl _ σ_smul σ_add τ_smul τ_add
          · exact mdifferentiable_extend ..
          · exact mdifferentiable_extend ..
          · exact mdifferentiable_extend ..
          · apply mdifferentiableAt_add_section
            · exact mdifferentiable_extend ..
            · exact mdifferentiable_extend ..
          · simp
        · exact mdifferentiable_extend ..
        · exact mdifferentiable_extend ..
      smul_right c v w := by
        rw [← τ_smul (f := fun _ ↦ c)]
        · apply tensoriality_criterion₂ I F _ F' _ _ _ _ _ rfl _ σ_smul σ_add τ_smul τ_add
          · exact mdifferentiable_extend ..
          · exact mdifferentiable_extend ..
          · exact mdifferentiable_extend ..
          · apply MDifferentiableAt.smul_section
            · exact mdifferentiableAt_const
            · exact mdifferentiable_extend ..
          · simp
        · exact mdifferentiable_const ..
        · exact mdifferentiable_extend .. }
    H.toContinuousLinearMap

variable {I} in
theorem mk2TensorAt_apply
    -- `φ` explicit to make it easier to generate the side conditions at point of use
    {φ : (Π x : M, V x) → (Π x : M, V x) → (Π x, V' x)} {x}
    (σ_smul : ∀ {f : M → ℝ}, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x →
      φ (f • σ) τ x = f x • φ σ τ x)
    (σ_add : ∀ {σ σ' τ}, MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      φ (σ + σ') τ x = φ σ τ x + φ σ' τ x)
    (τ_smul : ∀ {f : M → ℝ}, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% τ) x →
        φ σ (f • τ) x = f x • φ σ τ x)
    (τ_add : ∀ {σ τ τ'}, MDiffAt (T% τ) x → MDiffAt (T% τ') x →
        φ σ (τ + τ') x = φ σ τ x + φ σ τ' x)
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) {τ : Π x : M, V x} (hτ : MDiffAt (T% τ) x) :
    mk2TensorAt I F F' φ σ_smul σ_add τ_smul τ_add (σ x) (τ x) = φ σ τ x := by
  apply tensoriality_criterion₂ I F _ F' _ _ hσ _ hτ _ _ σ_smul σ_add τ_smul τ_add
  · exact mdifferentiable_extend ..
  · exact mdifferentiable_extend ..
  · simp
  · simp

theorem mk2TensorAt_add
    (φ : (Π x : M, V x) → (Π x : M, V x) → (Π x, V' x)) {x}
    (φ_σ_smul : ∀ {f : M → ℝ}, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x →
      φ (f • σ) τ x = f x • φ σ τ x)
    (φ_σ_add : ∀ {σ σ' τ}, MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      φ (σ + σ') τ x = φ σ τ x + φ σ' τ x)
    (φ_τ_smul : ∀ {f : M → ℝ}, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% τ) x →
        φ σ (f • τ) x = f x • φ σ τ x)
    (φ_τ_add : ∀ {σ τ τ'}, MDiffAt (T% τ) x → MDiffAt (T% τ') x →
        φ σ (τ + τ') x = φ σ τ x + φ σ τ' x)
    (ψ : (Π x : M, V x) → (Π x : M, V x) → (Π x, V' x))
    (ψ_σ_smul : ∀ {f : M → ℝ}, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x →
      ψ (f • σ) τ x = f x • ψ σ τ x)
    (ψ_σ_add : ∀ {σ σ' τ}, MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      ψ (σ + σ') τ x = ψ σ τ x + ψ σ' τ x)
    (ψ_τ_smul : ∀ {f : M → ℝ}, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% τ) x →
        ψ σ (f • τ) x = f x • ψ σ τ x)
    (ψ_τ_add : ∀ {σ τ τ'}, MDiffAt (T% τ) x → MDiffAt (T% τ') x →
        ψ σ (τ + τ') x = ψ σ τ x + ψ σ τ' x) :
    mk2TensorAt I F F' (φ + ψ)
      (fun {_ _ τ} hf hσ ↦
      (congr($(φ_σ_smul hf hσ (τ := τ)) + $(ψ_σ_smul hf hσ (τ := τ)))).trans (smul_add _ _ _).symm)
      (fun {σ₁ σ₂} τ hσ₁ hσ₂ ↦
        (congr($(φ_σ_add hσ₁ hσ₂ (τ := τ)) + $(ψ_σ_add hσ₁ hσ₂ (τ := τ)))).trans <| by
        dsimp
        abel)
      (fun {_ σ _} hf hτ ↦
      (congr($(φ_τ_smul hf hτ (σ := σ)) + $(ψ_τ_smul hf hτ (σ := σ)))).trans (smul_add _ _ _).symm)
      (fun σ {τ₁ τ₂} hτ₁ hτ₂ ↦
        (congr($(φ_τ_add hτ₁ hτ₂ (σ := σ)) + $(ψ_τ_add hτ₁ hτ₂ (σ := σ)))).trans <| by
        dsimp
        abel)
    = mk2TensorAt I F F' φ φ_σ_smul φ_σ_add φ_τ_smul φ_τ_add
      + mk2TensorAt I F F' ψ ψ_σ_smul ψ_σ_add ψ_τ_smul ψ_τ_add := by
  ext
  simp [mk2TensorAt, IsBilinearMap.toContinuousLinearMap, IsBilinearMap.toLinearMap]

end tensoriality

section linear_algebra_isCompl
lemma LinearMap.comap_isCompl {R R₂ M M₂ : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M] [Semiring R₂]
    {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    [AddCommMonoid M₂] [Module R₂ M₂]
    {f : M →ₛₗ[σ₁₂] M₂} (hf : Function.Bijective f)
    {p q : Submodule R₂ M₂} (h : IsCompl p q) :
    IsCompl (Submodule.comap f p) (Submodule.comap f q) := by
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at *
  constructor
  · rw [← Submodule.comap_inf, h.1]
    simp [LinearMap.ker_eq_bot_of_injective hf.1]
  · rw [← Submodule.comap_sup_of_injective, h.2]
    · exact Submodule.comap_top f
    · exact hf.1
    · intro x hx
      exact hf.2 x
    · intro x hx
      exact hf.2 x

lemma LinearEquiv.comap_isCompl {R R₂ M M₂ : Type*}
  [Semiring R] [AddCommMonoid M] [Module R M] [Semiring R₂]
  {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  [AddCommMonoid M₂] [Module R₂ M₂]
  (f : M ≃ₛₗ[σ₁₂] M₂) {p q : Submodule R₂ M₂} (h : IsCompl p q) :
    IsCompl (Submodule.comap f.toLinearMap p) (Submodule.comap f.toLinearMap q) := by
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at *
  constructor
  · rw [← Submodule.comap_inf, h.1]
    simp
  · rw [← Submodule.comap_sup_of_injective, h.2]
    · exact Submodule.comap_top f.toLinearMap
    · exact f.injective
    · simp
    · simp

end linear_algebra_isCompl
