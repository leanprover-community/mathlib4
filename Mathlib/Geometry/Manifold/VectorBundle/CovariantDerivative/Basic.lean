/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

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

/-!
# Covariant derivatives

TODO: add a more complete doc-string

-/

open Bundle Filter Module Topology Set

open scoped Bundle Manifold ContDiff

@[expose] public section mfderiv

open Function

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

lemma injective_mfderiv_of_eventually_leftInverse
    {f : M → M'} (x : M) {g : M' → M}
    (hg : MDifferentiableAt I' I g (f x)) (hf : MDifferentiableAt I I' f x)
    (hfg : g ∘ f =ᶠ[𝓝 x] id) : Injective (mfderiv I I' f x) := by
  have := mfderiv_comp x hg hf
  rw [hfg.mfderiv_eq] at this
  have : LeftInverse (mfderiv I' I g (f x)) (mfderiv I I' f x) := by
    intro u
    simpa using congr($this u).symm
  exact LeftInverse.injective this

lemma surjective_mfderiv_of_eventually_rightInverse
    {f : M → M'} {x : M} {y : M'} (hxy : y = f x) {g : M' → M}
    (hg : MDifferentiableAt I' I g y) (hf : MDifferentiableAt I I' f x)
    (hfg : g ∘ f =ᶠ[𝓝 x] id) : Surjective (mfderiv I' I g y) := by
  rw [hxy] at hg
  have := mfderiv_comp x hg hf
  rw [hfg.mfderiv_eq] at this
  have : RightInverse (mfderiv I I' f x) (mfderiv I' I g (f x)) := by
    intro u
    simpa using congr($this u).symm
  rw [← hxy] at this
  exact RightInverse.surjective this

end mfderiv

@[expose] public section delaborators

-- TODO: decide whether we want this and move
-- This delaborates `TotalSpace.mk x v` to `⟨x, v⟩`
open Lean PrettyPrinter Delaborator SubExpr

@[app_delab TotalSpace.mk] meta def delabTotalSpace_mk : Delab := do
  whenPPOption getPPNotation do
  let #[_B, _F, _E, _b, _v] := (← getExpr).getAppArgs | failure
  let bd : Term ← withNaryArg 3 <| delab
  let vd : Term ← withNaryArg 4 <| delab
  `(⟨$bd, $vd⟩)

@[app_delab MDifferentiableAt] meta def delabMDifferentiableAt : Delab := do
  whenPPOption getPPNotation do
  let args := (← getExpr).getAppArgs
  if args.size < 22 then failure
  let pt : Term ← withNaryArg 21 <| delab
  let f := args[20]!
  try
    if let .lam _ _ b _ := f then
      if b.isAppOf ``Bundle.TotalSpace.mk' then
        let s := b.getAppArgs[4]!.getAppFn
        if s matches .fvar .. then
          let ss ← PrettyPrinter.delab s
          return ← `(MDiffAt (T% $ss) $pt)
    throwError "nope"
  catch _ =>
    let x : Term ← withNaryArg 20 <| delab
    return ← `(MDiffAt $x $pt)

end delaborators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

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

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] -- [IsManifold I 0 M]

section
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
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
  (map_of_loc_one_jet 𝕜 (φ x) (mfderiv I 𝓘(𝕜, E) φ x u) (ψ x') (mfderiv I' 𝓘(𝕜, E') ψ x' u')) ∘
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
    mfderiv I I' (map_of_one_jet u u') x u = u' := by
  let ψ := extChartAt I' x'
  let φ := extChartAt I x
  let g := map_of_loc_one_jet 𝕜 (φ x) (mfderiv I 𝓘(𝕜, E) φ x u) (ψ x') (mfderiv I' 𝓘(𝕜, E') ψ x' u')
  let Ψ : M' → E' := ψ -- FIXME: this is working around a limitation of MDiffAt elaborator
  have hψ : MDiffAt Ψ x' := mdifferentiableAt_extChartAt (ChartedSpace.mem_chart_source x')
  let Φ : M → E := φ -- FIXME: this is working around a limitation of MDiffAt elaborator
  have hφ : MDiffAt Φ x := mdifferentiableAt_extChartAt (ChartedSpace.mem_chart_source x)
  replace hu : mfderiv I 𝓘(𝕜, E) φ x u = 0 → mfderiv I' 𝓘(𝕜, E') ψ x' u' = 0 := by
    have : Function.Injective (mfderiv I 𝓘(𝕜, E) φ x) :=
      (isInvertible_mfderiv_extChartAt (mem_extChartAt_source x)).injective
    rw [injective_iff_map_eq_zero] at this
    have := map_zero (mfderiv I' 𝓘(𝕜, E') ψ x')
    grind
  rcases  map_of_loc_one_jet_spec (𝕜 := 𝕜)
    (φ x) (mfderiv I 𝓘(𝕜, E) φ x u) (ψ x') (mfderiv I' 𝓘(𝕜, E') ψ x' u') hu with
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
  change (mfderiv 𝓘(𝕜, E') I' Ψi (g (φ x))) (fderiv 𝕜 g (φ x) <| mfderiv I 𝓘(𝕜, E) φ x u) = u'
  rw [h] at hψi
  rw [h'', h, ← mfderiv_comp_apply x' hψi hψ]
  have : Ψi ∘ ψ =ᶠ[𝓝 x'] id := by
    have : ∀ᶠ z in 𝓝 x', z ∈ ψ.source := extChartAt_source_mem_nhds x'
    filter_upwards [this] with z hz
    exact ψ.left_inv hz
  simp [this.mfderiv_eq]
  rfl
end

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  -- `V` vector bundle

lemma mfderiv_const_smul (s : M → F) {x : M} (a : 𝕜) (v : TangentSpace I x) :
    mfderiv I 𝓘(𝕜, F) (a • s) x v = a • mfderiv I 𝓘(𝕜, F) s x v := by
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
    have hs' : ¬ MDifferentiableAt I 𝓘(𝕜, F) (a • s) x :=
      fun h ↦ hs (by simpa [ha] using h.const_smul a⁻¹)
    rw [mfderiv_zero_of_not_mdifferentiableAt hs, mfderiv_zero_of_not_mdifferentiableAt hs']
    simp
    rfl

set_option linter.flexible false in -- FIXME
lemma mfderiv_smul [IsManifold I 1 M] {f : M → F} {s : M → 𝕜} {x : M} (hf : MDiffAt f x)
    (hs : MDiffAt s x) (v : TangentSpace I x) :
    letI dsxv : 𝕜 := mfderiv I 𝓘(𝕜, 𝕜) s x v
    letI dfxv : F := mfderiv I 𝓘(𝕜, F) f x v
    mfderiv I 𝓘(𝕜, F) (s • f) x v = (s x) • dfxv + dsxv • f x := by
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

end general_lemmas

section extend
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  -- `V` vector bundle

-- TODO: either change `localFrame` to make sure it is everywhere smooth
-- or introduce a cut-off here. First option is probaly better.
-- TODO: comment why we chose the second option in the end, and adapt the definition accordingly
-- new definition: smooth a bump function, then smul with localExtensionOn
/-- Extend a vector `v ∈ V x` to a section of the bundle `V`, whose value at `x` is `v`.
The details of the extension are mostly unspecified: for covariant derivatives, the value of
`s` at points other than `x` will not matter (except for shorter proofs).
Thus, we choose `s` to be somewhat nice: our chosen construction is linear in `v`.
-/
noncomputable def extend [FiniteDimensional ℝ F] [T2Space M] {x : M} (v : V x) :
    (x' : M) → V x' :=
  letI b := Basis.ofVectorSpace ℝ F
  letI t := trivializationAt F V x
  -- Choose a smooth bump function ψ near `x`, supported within t.baseSet
  -- and return ψ • V₀ instead.
  letI ht := t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  let ψ := Classical.choose <| (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.1 ht
  ψ.toFun • localExtensionOn b t v

variable {I F}

-- NB. These two lemmas don't hold for *any* choice of extension of `v`, but they hold for
-- *well-chosen* extensions (such as ours).
-- so, one may argue this is mathematically wrong, but it encodes the "choice some extension
-- with this and that property" nicely
-- a different proof would be to argue only the value at a point matters for cov
@[simp]
lemma extend_add [FiniteDimensional ℝ F] [T2Space M] {x : M} (v v' : V x) :
    extend I F (v + v') = extend I F v + extend I F v' := by
  simp [extend, localExtensionOn_add]

@[simp]
lemma extend_smul [FiniteDimensional ℝ F] [T2Space M] {a : ℝ} {x : M} (v : V x) :
  extend I F (a • v) = a • extend I F v := by simp [extend, localExtensionOn_smul]; module

@[simp]
lemma extend_zero [FiniteDimensional ℝ F] [T2Space M] (x : M) :
  extend I F (0 : V x) = 0 := by simp [extend, localExtensionOn_zero]

@[simp] lemma extend_apply_self [FiniteDimensional ℝ F] [T2Space M] {x : M} (v : V x) :
    extend I F v x = v := by
  simpa [extend] using
    localExtensionOn_apply_self _ _ (FiberBundle.mem_baseSet_trivializationAt' x) v

variable (I F)

lemma contMDiff_extend [IsManifold I ∞ M] [FiniteDimensional ℝ F] [T2Space M]
    [ContMDiffVectorBundle ∞ F V I] {x : M} (σ₀ : V x) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (extend I F σ₀)) := by
  letI t := trivializationAt F V x
  letI ht := t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let ψ := Classical.choose <| (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.1 ht
  let hψ :=
    Classical.choose_spec <| (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.1 ht
  exact .smul_section_of_tsupport ψ.contMDiff.contMDiffOn t.open_baseSet hψ.1
    (contMDiffOn_localExtensionOn _ hx _)

lemma mdifferentiable_extend [IsManifold I ∞ M] [FiniteDimensional ℝ F] [T2Space M]
    [ContMDiffVectorBundle ∞ F V I] {x : M} (σ₀ : V x) :
    MDiff (T% (extend I F σ₀)) :=
  contMDiff_extend I F σ₀ |>.mdifferentiable (by simp)

theorem contDiff_extend
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    (x : E) (y : E') : ContDiff ℝ ∞ (extend 𝓘(ℝ, E) E' y (x := x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x'
  rw [← contMDiffAt_iff_contDiffAt]
  simpa [contMDiffAt_section] using contMDiff_extend (V := Trivial E E') _ _ y x'

end extend

section any_field
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] -- [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  -- [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] --[VectorBundle 𝕜 F V]
  -- `V` vector bundle

structure IsCovariantDerivativeOn [IsManifold I 1 M]
    (f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x))
    (s : Set M := Set.univ) : Prop where
  -- All the same axioms as CovariantDerivative, but restricted to the set s.
  addX (f) {X X' : Π x : M, TangentSpace I x} {σ : Π x : M, V x} {x : M}
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) (hσ : MDiffAt (T% σ) x)
    (hx : x ∈ s := by trivial) :
    f (X + X') σ x = f X σ x + f X' σ x
  smulX {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x} {g : M → 𝕜} {x : M}
    (hX : MDiffAt (T% X) x) (hσ : MDiffAt (T% σ) x) (hg : MDiffAt g x) (hx : x ∈ s := by trivial) :
    f (g • X) σ x = g x • f X σ x
  addσ {X : Π x : M, TangentSpace I x} {σ σ' : Π x : M, V x} {x}
    (hX : MDiffAt (T% X) x) (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hx : x ∈ s := by trivial) :
    f X (σ + σ') x = f X σ x + f X σ' x
  leibniz {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x} {g : M → 𝕜} {x}
    (hX : MDiffAt (T% X) x) (hσ : MDiffAt (T% σ) x) (hg : MDiffAt g x) (hx : x ∈ s := by trivial):
    f X (g • σ) x = (g • f X σ) x + ((bar _).toFun (mfderiv I 𝓘(𝕜) g x (X x))) • σ x
  smul_const_σ {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x} {x} (a : 𝕜)
    (hX : MDiffAt (T% X) x) (hσ : MDiffAt (T% σ) x) (hx : x ∈ s := by trivial) :
    f X (a • σ) x = a • f X σ x

/--
A covariant derivative ∇ is called of class `C^k` iff,
whenever `X` is a `C^k` section and `σ` a `C^{k+1}` section, the result `∇ X σ` is a `C^k` section.
This is a class so typeclass inference can deduce this automatically.
-/
class ContMDiffCovariantDerivativeOn [IsManifold I 1 M] (k : ℕ∞)
    (cov : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x))
    (u : Set M)  where
  contMDiff : ∀ {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x},
    CMDiff[u] (k + 1) (T% σ) → CMDiff[u] k (T% X) →
    CMDiff[u] k (T% (cov X σ))

variable {F}

namespace IsCovariantDerivativeOn

variable [IsManifold I 1 M]

variable (E) in
/-- If `E` is the trivial vector space, the axioms of a covariant derivative are vacuous. -/
lemma of_subsingleton [hE : Subsingleton E]
    (f : ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x) →
      ((x : M) → TangentSpace I x)) :
    IsCovariantDerivativeOn E f Set.univ := by
  have (X) (Y) (x) : f X Y x = 0 := by
    have : Subsingleton (TangentSpace I x) := inferInstanceAs (Subsingleton E)
    exact Subsingleton.eq_zero _
  exact {
    addX {_X _X' _σ x} hX hX' hσ hx := by simp [this]
    smulX {_X _σ _g _x} hX hσ hg hx := by simp [this]
    smul_const_σ {X _σ x} a hX hσ hx := by simp [this]
    addσ {X σ σ' x} hX hσ hσ' hx := by simp [this]
    leibniz {X σ g x} hX hσ hg hx := by
      have hσ : σ x = 0 := by
        have : Subsingleton (TangentSpace I x) := inferInstanceAs (Subsingleton E)
        exact Subsingleton.eq_zero _
      simp [this, hσ] }

section changing_set
/-! Changing set

In this changing we change `s` in `IsCovariantDerivativeOn F f s`.

-/
lemma mono
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)} {s t : Set M}
    (hf : IsCovariantDerivativeOn F f t) (hst : s ⊆ t) : IsCovariantDerivativeOn F f s where
  addX {_X _X' _σ} _x hX hX' hσ hx := hf.addX hX hX' hσ (hst hx)
  smulX {_X _σ _g} _x hX hσ hg hx := hf.smulX hX hσ hg (hst hx)
  addσ {_X _σ _σ' _x} hX hσ hσ' hx := hf.addσ hX hσ hσ' (hst hx)
  leibniz {_X _σ _f _x} hX hσ hf' hx := hf.leibniz hX hσ hf' (hst hx)
  smul_const_σ {_X _σ _x} a hX hσ hx := hf.smul_const_σ a hX hσ (hst hx)

lemma iUnion {ι : Type*}
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)} {s : ι → Set M}
    (hf : ∀ i, IsCovariantDerivativeOn F f (s i)) : IsCovariantDerivativeOn F f (⋃ i, s i) where
  addX {_X _X' _σ _x} hX hX' hσ hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).addX hX hX' hσ hxsi
  smulX {_X _σ _g _x} hX hσ hg hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).smulX hX hσ hg hxsi
  addσ {_X _σ _σ' _x} hX hσ hσ' hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).addσ hX hσ hσ'
  leibniz {X σ f x} hX hσ hf' hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).leibniz hX hσ hf'
  smul_const_σ {_X _σ _x} a hX hσ hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).smul_const_σ _ hX hσ

end changing_set

/- Congruence properties -/
section

lemma congr {f g : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)} {s : Set M}
    (hf : IsCovariantDerivativeOn F f s)
    -- Is this too strong? Will see!
    (hfg : ∀ {X : Π x : M, TangentSpace I x},
      ∀ {σ : Π x : M, V x}, ∀ {x}, x ∈ s → f X σ x = g X σ x) :
    IsCovariantDerivativeOn F g s where
  addX hX hX' hσ hx := by simp [← hfg hx, hf.addX hX hX' hσ]
  smulX hX hσ hg hx := by simp [← hfg hx, hf.smulX hX hσ hg]
  addσ hX hσ hσ' hx := by simp [← hfg hx, hf.addσ hX hσ hσ']
  leibniz hX hσ hf' hx := by simp [← hfg hx, hf.leibniz hX hσ hf']
  smul_const_σ a hX hσ hx := by simp [← hfg hx, hf.smul_const_σ a hX hσ]

end

section computational_properties

lemma smul_const_X
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {s : Set M} (h : IsCovariantDerivativeOn F f s) {x} (a : 𝕜)
    {X : Π x, TangentSpace I x} {σ : Π x, V x} (hX : MDiffAt (T% X) x) (hσ : MDiffAt (T% σ) x)
    (hx : x ∈ s := by trivial) :
    f (a • X) σ x = a • f X σ x :=
  h.smulX hX hσ mdifferentiableAt_const

variable {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)} {s : Set M}

@[simp]
lemma zeroX (hf : IsCovariantDerivativeOn F f s)
    {x : M} (hx : x ∈ s := by trivial)
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) : f 0 σ x = 0 := by
  -- TODO: writing MDiffAt here yields an error!
  have : MDifferentiableAt I (I.prod 𝓘(𝕜, E)) (T% (fun x ↦ (0 : TangentSpace I x))) x :=
    -- TODO: add mdifferentiable{,At}_zeroSection
    (contMDiff_zeroSection _ _).mdifferentiableAt one_ne_zero
  simpa using IsCovariantDerivativeOn.addX f hf (X := 0) this this hσ

@[simp]
lemma zeroσ [VectorBundle 𝕜 F V] (hf : IsCovariantDerivativeOn F f s)
    {X : Π x : M, TangentSpace I x} {x} (hX : MDiffAt (T% X) x) (hx : x ∈ s := by trivial) :
    f X 0 x = 0 := by
  simpa using (hf.addσ hX (mdifferentiableAt_zeroSection ..)
    (mdifferentiableAt_zeroSection ..) : f X (0 + 0) x = _)

lemma sum_X (hf : IsCovariantDerivativeOn F f s)
    {ι : Type*} {u : Finset ι} {X : ι → Π x : M, TangentSpace I x} {σ : Π x : M, V x}
    {x} (hx : x ∈ s) (hX : ∀ i, MDiffAt (T% (X i)) x) (hσ : MDiffAt (T% σ) x) :
    f (∑ i ∈ u, X i) σ x = ∑ i ∈ u, f (X i) σ x := by
  classical
  have := hf.zeroX hx hσ
  induction u using Finset.induction_on with
  | empty => simp [hf.zeroX hx hσ]
  | insert a u ha h =>
    have : MDiffAt (T% (∑ i ∈ u, X i)) x := by simpa using MDifferentiableAt.sum_section (s := u) hX
    simp [Finset.sum_insert ha, ← h, hf.addX (hX a) this hσ hx]

end computational_properties

section operations

variable {s : Set M}
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}

/-- A convex combination of covariant derivatives is a covariant derivative. -/
@[simps]
def convexCombination
    {f' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (hf : IsCovariantDerivativeOn F f s) (hf' : IsCovariantDerivativeOn F f' s) (g : M → 𝕜) :
    IsCovariantDerivativeOn F (fun X σ ↦ (g • (f X σ)) + (1 - g) • (f' X σ)) s where
  addX {X X' σ} x hX hX' hσ hx := by simp [hf.addX hX hX' hσ, hf'.addX hX hX' hσ]; module
  smulX {_X _σ _φ} x hX hσ hφ hx := by simp [hf.smulX hX hσ hφ, hf'.smulX hX hσ hφ]; module
  addσ {_X _σ _σ' x} hX hσ hσ' hx := by
    simp [hf.addσ hX hσ hσ', hf'.addσ hX hσ hσ']
    module
  smul_const_σ {_X _σ _x} a hX hσ hx := by
    simp [hf.smul_const_σ a hX hσ, hf'.smul_const_σ a hX hσ]
    module
  leibniz {X σ φ x} hX hσ hφ hx := by
    simp [hf.leibniz hX hσ hφ, hf'.leibniz hX hσ hφ]
    module

/-- A convex combination of two `C^k` connections is a `C^k` connection. -/
lemma _root_.ContMDiffCovariantDerivativeOn.convexCombination
    [VectorBundle 𝕜 F V]
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {u: Set M} {f : M → 𝕜} {n : ℕ∞} (hf : CMDiff[u] n f)
    (Hcov : ContMDiffCovariantDerivativeOn (F := F) n cov u)
    (Hcov' : ContMDiffCovariantDerivativeOn (F := F) n cov' u) :
    ContMDiffCovariantDerivativeOn F n (fun X σ ↦ (f • (cov X σ)) + (1 - f) • (cov' X σ)) u where
  contMDiff hX hσ := by
    apply ContMDiffOn.add_section
    · exact hf.smul_section <| Hcov.contMDiff hX hσ
    · exact (contMDiffOn_const.sub hf).smul_section <| Hcov'.contMDiff hX hσ

/-- A finite convex combination of covariant derivatives is a covariant derivative. -/
def convexCombination' {ι : Type*} {s : Finset ι} [Nonempty s]
    {u : Set M} {cov : ι → (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (h : ∀ i, IsCovariantDerivativeOn F (cov i) u) {f : ι → M → 𝕜} (hf : ∑ i ∈ s, f i = 1) :
    IsCovariantDerivativeOn F (fun X σ x ↦ ∑ i ∈ s, (f i x) • (cov i) X σ x) u where
  addX {_X _X' _σ} x hx hX hX' hσ := by
    rw [← Finset.sum_add_distrib]
    congr
    ext i
    simp [(h i).addX hx hX hX' hσ]
  smulX {_X _σ _g} x hx hX hσ hg := by
    rw [Finset.smul_sum]
    congr
    ext i
    simp [(h i).smulX hx hX hσ hg]
    module
  addσ {_X _σ _σ' _x} hX hσ hσ' hx := by
    rw [← Finset.sum_add_distrib]
    congr
    ext i
    rw [← smul_add, (h i).addσ hX hσ hσ' hx]
  smul_const_σ {_X _σ _x} a hX hσ hx := by
    rw [Finset.smul_sum]
    congr
    ext i
    simp [(h i).smul_const_σ a hX hσ]
    module
  leibniz {X σ g x} hX hσ hg hx := by
    calc ∑ i ∈ s, f i x • (cov i) X (g • σ) x
      _ = ∑ i ∈ s, ((g • (f i • (cov i) X σ)) x
            + f i x • (bar (g x)) ((mfderiv I 𝓘(𝕜) g x) (X x)) • σ x) := by
        congr
        ext i
        rw [(h i).leibniz hX hσ hg]
        simp_rw [Pi.smul_apply', smul_add]
        dsimp
        rw [smul_comm]
      _ = ∑ i ∈ s, ((g • (f i • (cov i) X σ)) x)
        + ∑ i ∈ s, f i x • (bar (g x)) ((mfderiv I 𝓘(𝕜) g x) (X x)) • σ x := by
        rw [Finset.sum_add_distrib]
      _ = (g • ∑ i ∈ s, f i • (cov i) X σ) x + (bar (g x)) ((mfderiv I 𝓘(𝕜) g x) (X x)) • σ x := by
        -- There has to be a shorter proof!
        simp only [Finset.smul_sum, Pi.smul_apply', Finset.sum_apply, add_right_inj]
        set B := (bar (g x)) ((mfderiv I 𝓘(𝕜) g x) (X x)) • σ x
        trans (∑ i ∈ s, f i x) • B
        · rw [Finset.sum_smul]
        have : ∑ i ∈ s, f i x = 1 := by convert congr_fun hf x; simp
        rw [this, one_smul]
    simp

/-- A convex combination of finitely many `C^k` connections on `u` is a `C^k` connection on `u`. -/
lemma _root_.ContMDiffCovariantDerivativeOn.convexCombination' {n : ℕ∞}
    [VectorBundle 𝕜 F V] {ι : Type*} {s : Finset ι} {u : Set M}
    {cov : ι → (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (hcov : ∀ i ∈ s, ContMDiffCovariantDerivativeOn F n (cov i) u)
    {f : ι → M → 𝕜} (hf : ∀ i ∈ s, CMDiff[u] n (f i)) :
    ContMDiffCovariantDerivativeOn F n (fun X σ x ↦ ∑ i ∈ s, (f i x) • (cov i) X σ x) u where
  contMDiff hσ hX :=
    ContMDiffOn.sum_section (fun i hi ↦ (hf i hi).smul_section <| (hcov i hi).contMDiff hσ hX)

variable {s : Set M}
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}

lemma add_one_form [∀ (x : M), IsTopologicalAddGroup (V x)]
    [∀ (x : M), ContinuousSMul 𝕜 (V x)] (hf : IsCovariantDerivativeOn F f s)
    (A : Π x : M, TangentSpace I x →L[𝕜] V x →L[𝕜] V x) :
    IsCovariantDerivativeOn F (fun X σ x ↦ f X σ x + A x (X x) (σ x)) s where
  addX {_X _X' _σ} x hx hX hX' hσ := by
    simp [hf.addX hx hX hX' hσ]
    abel
  smulX {_X _σ _g} x hx hX hσ hg := by
    simp [hf.smulX hx hX hσ hg]
  addσ {_X _σ _σ' _x} hX hσ hσ' hx := by
    simp [hf.addσ hX hσ hσ']
    abel
  smul_const_σ {_X _σ _x} a hX hσ hx := by simp [hf.smul_const_σ a hX hσ]
  leibniz {X σ g x} hX hσ hg hx := by
    simp [hf.leibniz hX hσ hg]
    module

end operations

section trivial_bundle

variable (I M F) in
@[simps]
noncomputable def trivial [IsManifold I 1 M] :
    IsCovariantDerivativeOn F (V := Trivial M F)
      (fun X s x ↦ mfderiv I 𝓘(𝕜, F) s x (X x)) univ where
  addX {_X _X' _σ} x _ hX hX' hσ := by simp
  smulX {_X _σ} c' x _ := by simp
  addσ {_X σ σ' x} hX hσ hσ' hx := by
    rw [mdifferentiableAt_section] at hσ hσ'
    -- TODO: specialize mdifferentiableAt_section to trivial bundles?
    change MDifferentiableAt I 𝓘(𝕜, F) σ x at hσ
    change MDifferentiableAt I 𝓘(𝕜, F) σ' x at hσ'
    rw [mfderiv_add hσ hσ']
    rfl
  smul_const_σ {_X _σ _x} a hX hσ hx := by rw [mfderiv_const_smul]
  leibniz {X σ f x} hX hσ hf hx := by
    rw [mdifferentiableAt_section] at hσ
    exact mfderiv_smul hσ hf (X x)

lemma of_endomorphism (A : (x : M) → TangentSpace I x →L[𝕜] F →L[𝕜] F) :
    IsCovariantDerivativeOn F
      (fun (X : Π x : M, TangentSpace I x) (s : M → F) x ↦
        letI d : F := mfderiv I 𝓘(𝕜, F) s x (X x)
        d + A x (X x) (s x)) univ :=
  trivial I M F |>.add_one_form A

end trivial_bundle

end IsCovariantDerivativeOn

/-! Bundled global covariant derivatives -/

variable (I F V) in
@[ext]
structure CovariantDerivative [IsManifold I 1 M] where
  toFun : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)
  isCovariantDerivativeOn : IsCovariantDerivativeOn F toFun Set.univ

namespace CovariantDerivative

attribute [coe] toFun

variable [IsManifold I 1 M]

/-- Coercion of a `CovariantDerivative` to function -/
instance : CoeFun (CovariantDerivative I F V)
    fun _ ↦ (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x) :=
  ⟨fun e ↦ e.toFun⟩

instance (cov : CovariantDerivative I F V) {s : Set M} :
    IsCovariantDerivativeOn F cov s := by
  apply cov.isCovariantDerivativeOn.mono (fun ⦃a⦄ a ↦ trivial)

/-- If `f : Vec(M) × Γ(E) → Vec(M)` is a covariant derivative on each set in an open cover,
it is a covariant derivative. -/
def of_isCovariantDerivativeOn_of_open_cover {ι : Type*} {s : ι → Set M}
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (hf : ∀ i, IsCovariantDerivativeOn F f (s i)) (hs : ⋃ i, s i = Set.univ) :
    CovariantDerivative I F V :=
  ⟨f, hs ▸ IsCovariantDerivativeOn.iUnion hf⟩

@[simp]
lemma of_isCovariantDerivativeOn_of_open_cover_coe {ι : Type*} {s : ι → Set M}
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (hf : ∀ i, IsCovariantDerivativeOn F f (s i)) (hs : ⋃ i, s i = Set.univ) :
    of_isCovariantDerivativeOn_of_open_cover hf hs = f := rfl


/--
A covariant derivative ∇ is called of class `C^k` iff,
whenever `X` is a `C^k` section and `σ` a `C^{k+1}` section, the result `∇ X σ` is a `C^k` section.
This is a class so typeclass inference can deduce this automatically.
-/
class ContMDiffCovariantDerivative (cov : CovariantDerivative I F V) (k : ℕ∞) where
  contMDiff : ContMDiffCovariantDerivativeOn F k cov.toFun Set.univ

@[simp]
lemma contMDiffCovariantDerivativeOn_univ_iff {cov : CovariantDerivative I F V} {k : ℕ∞} :
    ContMDiffCovariantDerivativeOn F k cov.toFun Set.univ ↔ ContMDiffCovariantDerivative cov k :=
  ⟨fun h ↦ ⟨h⟩, fun h ↦ h.contMDiff⟩

-- future: if g is a C^k metric on a manifold M, the corresponding Levi-Civita connection
-- is of class C^k (up to off-by-one errors)

section computational_properties

@[simp]
lemma zeroX (cov : CovariantDerivative I F V) {σ : Π x : M, V x} (hσ : MDiff (T% σ)) :
    cov 0 σ = 0 := by
  ext x
  exact cov.isCovariantDerivativeOn.zeroX (by trivial) (hσ x)

@[simp]
lemma zeroσ [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V)
    {X : Π x : M, TangentSpace I x} (hX : MDiff (T% X)) : cov X 0 = 0 := by
  ext x
  exact cov.isCovariantDerivativeOn.zeroσ (hX x)

lemma sum_X (cov : CovariantDerivative I F V)
    {ι : Type*} {s : Finset ι} {X : ι → Π x : M, TangentSpace I x} {σ : Π x : M, V x}
    (hX : ∀ i, MDiff (T% (X i))) (hσ : MDiff (T% σ)):
    cov (∑ i ∈ s, X i) σ = ∑ i ∈ s, cov (X i) σ := by
  ext x
  simpa using cov.isCovariantDerivativeOn.sum_X trivial (fun i ↦ hX i x) (hσ x)

end computational_properties

section operations

/-- A convex combination of covariant derivatives is a covariant derivative. -/
@[simps]
def convexCombination (cov cov' : CovariantDerivative I F V) (g : M → 𝕜) :
    CovariantDerivative I F V where
  toFun := fun X σ ↦ (g • (cov X σ)) + (1 - g) • (cov' X σ)
  isCovariantDerivativeOn :=
    cov.isCovariantDerivativeOn.convexCombination cov'.isCovariantDerivativeOn _

/-- A finite convex combination of covariant derivatives is a covariant derivative. -/
def convexCombination' {ι : Type*} {s : Finset ι} [Nonempty s]
    (cov : ι → CovariantDerivative I F V) {f : ι → M → 𝕜} (hf : ∑ i ∈ s, f i = 1) :
    CovariantDerivative I F V where
  toFun X t x := ∑ i ∈ s, (f i x) • (cov i) X t x
  isCovariantDerivativeOn := IsCovariantDerivativeOn.convexCombination'
    (fun i ↦ (cov i).isCovariantDerivativeOn) hf

/-- A convex combination of two `C^k` connections is a `C^k` connection. -/
lemma ContMDiffCovariantDerivative.convexCombination [VectorBundle 𝕜 F V]
  (cov cov' : CovariantDerivative I F V)
    {f : M → 𝕜} {n : ℕ∞} (hf : ContMDiff I 𝓘(𝕜) n f)
    (hcov : ContMDiffCovariantDerivative cov n) (hcov' : ContMDiffCovariantDerivative cov' n) :
    ContMDiffCovariantDerivative (convexCombination cov cov' f) n where
  contMDiff :=
    ContMDiffCovariantDerivativeOn.convexCombination hf.contMDiffOn hcov.contMDiff hcov'.contMDiff

/-- A convex combination of finitely many `C^k` connections is a `C^k` connection. -/
lemma ContMDiffCovariantDerivative.convexCombination' [VectorBundle 𝕜 F V]
    {ι : Type*} {s : Finset ι} [Nonempty s]
    (cov : ι → CovariantDerivative I F V) {f : ι → M → 𝕜} (hf : ∑ i ∈ s, f i = 1) {n : ℕ∞}
    (hf' : ∀ i ∈ s, ContMDiff I 𝓘(𝕜) n (f i))
    (hcov : ∀ i ∈ s, ContMDiffCovariantDerivative (cov i) n) :
    ContMDiffCovariantDerivative (convexCombination' cov hf) n where
  contMDiff :=
    ContMDiffCovariantDerivativeOn.convexCombination'
      (fun i hi ↦ (hcov i hi).contMDiff) (fun i hi ↦ (hf' i hi).contMDiffOn)

-- Future: prove a version with a locally finite sum, and deduce that C^k connections always
-- exist (using a partition of unity argument)

end operations

section trivial_bundle

variable (I M F) in
@[simps]
noncomputable def trivial [IsManifold I 1 M] : CovariantDerivative I F (Trivial M F) where
  toFun X s x := mfderiv I 𝓘(𝕜, F) s x (X x)
  isCovariantDerivativeOn := -- TODO use previous work
  { addX {_X _X' _σ} x _ hX hX' hσ := by simp
    smulX {_X _σ} c' x _ := by simp
    addσ {_X σ σ' x} hX hσ hσ' hx := by
      rw [mdifferentiableAt_section] at hσ hσ'
      -- TODO: specialize mdifferentiableAt_section to trivial bundles?
      change MDifferentiableAt I 𝓘(𝕜, F) σ x at hσ
      change MDifferentiableAt I 𝓘(𝕜, F) σ' x at hσ'
      rw [mfderiv_add hσ hσ']
      rfl
    smul_const_σ {_X _σ _x} a hX hσ hx := by rw [mfderiv_const_smul]
    leibniz {X σ f x} hX hσ hf hx := by
      rw [mdifferentiableAt_section] at hσ
      exact mfderiv_smul hσ hf (X x) }

end trivial_bundle

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']


-- TODO: does it make sense to speak of analytic connections? if so, change the definition of
-- regularity and use ∞ from `open scoped ContDiff` instead.

/-- The trivial connection on the trivial bundle is smooth -/
lemma trivial_isSmooth : ContMDiffCovariantDerivative (𝕜 := 𝕜) (trivial 𝓘(𝕜, E) E E') (⊤ : ℕ∞) where
  contMDiff := by -- {X σ} hX hσ
    sorry /-
    -- except for local trivialisations, contDiff_infty_iff_fderiv covers this well
    simp only [trivial]
    -- use a local trivialisation
    intro x
    specialize hX x
    -- TODO: use contMDiffOn instead, to get something like
    -- have hX' : ContMDiffOn 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (∞ + 1)
    --  (T% σ) (trivializationAt x).baseSet := hX.contMDiffOn
    -- then want a version contMDiffOn_totalSpace
    rw [contMDiffAt_totalSpace] at hX ⊢
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.trivialization_apply]
    refine ⟨contMDiff_id _, ?_⟩
    obtain ⟨h₁, h₂⟩ := hX
    -- ... hopefully telling me
    -- have h₂scifi : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E') ∞
    --   (fun x ↦ σ x) (trivializationAt _).baseSet_ := sorry
    simp at h₂
    -- now use ContMDiffOn.congr and contDiff_infty_iff_fderiv,
    -- or perhaps a contMDiffOn version of this lemma?
    sorry -/

noncomputable def of_endomorphism (A : E → E →L[𝕜] E' →L[𝕜] E') :
    CovariantDerivative 𝓘(𝕜, E) E' (Trivial E E') where
  toFun X σ := fun x ↦ fderiv 𝕜 σ x (X x) + A x (X x) (σ x)
  isCovariantDerivativeOn := by
    convert IsCovariantDerivativeOn.of_endomorphism (I := 𝓘(𝕜, E)) A
    ext f x v
    rw [mfderiv_eq_fderiv]
end CovariantDerivative
end any_field

section real

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]
  -- `V` vector bundle

namespace IsCovariantDerivativeOn

/-- `cov X σ x` only depends on `X` via `X x` -/
lemma congr_X_at [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [VectorBundle ℝ F V]
    {cov : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {u : Set M} (hcov : IsCovariantDerivativeOn F cov u)
    {X X' : Π x : M, TangentSpace I x}
    {σ : Π x : M, V x} {x : M}
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hσ : MDiffAt (T% σ) x)
    (hx : x ∈ u) (hXX' : X x = X' x) :
    cov X σ x = cov X' σ x := by
  refine tensoriality_criterion I E (TangentSpace I) (φ := fun X ↦ cov X σ)  F V hX hX' hXX' ?_ ?_
  · intro f X hf hX
    exact hcov.smulX hX hσ hf hx
  · intro X X' hX hX'
    exact hcov.addX hX hX' hσ hx

lemma congr_σ_smoothBumpFunction [T2Space M] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E]
    {cov : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {u : Set M} (hcov : IsCovariantDerivativeOn F cov u)
    (X : Π x : M, TangentSpace I x) {σ : Π x : M, V x}
    (hX : MDiffAt (T% X) x)
    (hσ : MDiffAt (T% σ) x)
    (f : SmoothBumpFunction I x)
    (hx : x ∈ u) :
    cov X ((f : M → ℝ) • σ) x = cov X σ x := by
  have hf : MDiffAt f x := f.contMDiffAt.mdifferentiableAt (by simp)
  have := hcov.leibniz hX hσ hf hx
  rw [hcov.leibniz hX hσ _ hx]
  swap; · apply f.contMDiff.mdifferentiable (by norm_num)
  calc _
    _ = cov X σ x + 0 := ?_
    _ = cov X σ x := by rw [add_zero]
  suffices mfderiv% (1 : M → ℝ) x (X x) = 0 ∨ σ x = 0 by
    simpa [f.eq_one, f.eventuallyEq_one.mfderiv_eq]
  rw [show mfderiv I 𝓘(ℝ, ℝ) 1 x = 0 by apply mfderiv_const]
  left
  rfl

lemma congr_σ_of_eqOn [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [VectorBundle ℝ F V]
    {cov : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)
    {X : Π x : M, TangentSpace I x} {σ σ' : Π x : M, V x}
    (hX : MDiffAt (T% X) x)
    (hσ : MDiffAt (T% σ) x)
    (hσ' : MDiffAt (T% σ') x)
    (hxs : s ∈ 𝓝 x)
    (hσσ' : ∀ x ∈ s, σ x = σ' x) :
    cov X σ x = cov X σ' x := by
  -- Choose a smooth bump function ψ with support around `x` contained in `s`
  obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hxs).mem_iff.1 hxs
  -- Observe that `ψ • σ = ψ • σ'` as dependent functions.
  have (x : M) : ((ψ : M → ℝ) • σ) x = ((ψ : M → ℝ) • σ') x := by
    by_cases h : x ∈ s
    · simp [hσσ' x h]
    · simp [Function.notMem_support.mp fun a ↦ h (hψ a)]
  -- Then, it's a chain of (dependent) equalities.
  calc cov X σ x
    _ = cov X ((ψ : M → ℝ) • σ) x := by
          rw [hcov.congr_σ_smoothBumpFunction X hX hσ ψ (mem_of_mem_nhds hxs)]
    _ = cov X ((ψ : M → ℝ) • σ') x := by rw [funext this]
    _ = cov X σ' x := by
          rw [hcov.congr_σ_smoothBumpFunction X hX hσ' ψ (mem_of_mem_nhds hxs)]

-- TODO: prove that `cov X σ x` depends on σ only via σ(X) and the 1-jet of σ at x
-- this should be easy using the projection formula below.

/-- The difference of two covariant derivatives, as a function `Γ(TM) × Γ(E) → Γ(E)`.
Future lemmas will upgrade this to a map `TM ⊕ E → E`. -/
def differenceAux (cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)) :
    (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x) :=
  fun X σ ↦ cov X σ - cov' X σ

omit [(x : M) → Module ℝ (V x)] [(x : M) → TopologicalSpace (V x)] in
@[simp]
lemma differenceAux_apply
    (cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x))
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    differenceAux cov cov' X σ = cov X σ - cov' X σ := rfl

variable [IsManifold I 1 M]

lemma differenceAux_smul_eq
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {u : Set M} (hcov : IsCovariantDerivativeOn F cov u)
    (hcov' : IsCovariantDerivativeOn F cov' u)
    {X : Π x : M, TangentSpace I x} (σ : Π x : M, V x) (f : M → ℝ)
    {x : M} (hx : x ∈ u := by trivial)
    (hX : MDiffAt (T% X) x)
    (hσ : MDiffAt (T% σ) x)
    (hf : MDiffAt f x) :
    differenceAux cov cov' X ((f : M → ℝ) • σ) x = f x • differenceAux cov cov' X σ x:=
  calc _
    _ = cov X ((f : M → ℝ) • σ) x - cov' X ((f : M → ℝ) • σ) x := rfl
    _ = (f x • cov X σ x +  ((bar _).toFun <| mfderiv I 𝓘(ℝ) f x (X x)) • σ x)
        - (f x • cov' X σ x +  ((bar _).toFun <| mfderiv I 𝓘(ℝ) f x (X x)) • σ x) := by
      simp [hcov.leibniz hX hσ hf, hcov'.leibniz hX hσ hf]
    _ = f x • cov X σ x - f x • cov' X σ x := by simp
    _ = f x • (cov X σ x - cov' X σ x) := by simp [smul_sub]
    _ = _ := rfl

lemma differenceAux_smul_eq'
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {u : Set M} (hcov : IsCovariantDerivativeOn F cov u)
    (hcov' : IsCovariantDerivativeOn F cov' u)
    {X : Π x : M, TangentSpace I x}
    (hX : MDiffAt (T% X) x)
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x)
    {f : M → ℝ} (hf : MDiffAt f x)
    (hx : x ∈ u := by trivial) :
    differenceAux cov cov' (f • X) σ x = f x • differenceAux cov cov' X σ x := by
  simp [differenceAux, hcov.smulX hX hσ hf, hcov'.smulX hX hσ hf, smul_sub]

/-- The value of `differenceAux cov cov' X σ` at `x₀` depends only on `X x₀` and `σ x₀`. -/
lemma differenceAux_tensorial
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {u : Set M} (hcov : IsCovariantDerivativeOn F cov u)
    (hcov' : IsCovariantDerivativeOn F cov' u)
    [T2Space M] [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {X X' : Π x : M, TangentSpace I x} {σ σ' : Π x : M, V x} {x₀ : M}
    (hX : MDiffAt (T% X) x₀) -- TODO: is this hypotheses truly necessary?
    (hX' : MDiffAt (T% X') x₀)
    (hσ : MDiffAt (T% σ) x₀)
    (hσ' : MDiffAt (T% σ') x₀)
    (hXX' : X x₀ = X' x₀) (hσσ' : σ x₀ = σ' x₀) (hx : x₀ ∈ u := by trivial) :
    differenceAux cov cov' X σ x₀ = differenceAux cov cov' X' σ' x₀ := by
  trans differenceAux cov cov' X' σ x₀
  · let φ : (Π x : M, TangentSpace I x) → (Π x, V x) := fun X ↦ differenceAux cov cov' X σ
    change φ X x₀ = φ X' x₀
    -- TODO: is there a version of `tensoriality_criterion` which does not require `hX`?
    apply tensoriality_criterion (E := E) (I := I) E (TangentSpace I) F V hX hX' hXX'
    · intro f X hf hX
      exact hcov.differenceAux_smul_eq' hcov' hX hσ hf
    · intro X X' hX hX'
      unfold φ differenceAux
      simp only [Pi.sub_apply, hcov.addX hX hX' hσ, hcov'.addX hX hX' hσ]
      abel
  · let φ : (Π x : M, V x) → (Π x, V x) := fun σ ↦ differenceAux cov cov' X' σ
    change φ σ x₀ = φ σ' x₀
    apply tensoriality_criterion (E := E) (I := I) F V F V hσ hσ' hσσ'
    · intro f σ x hf
      exact hcov.differenceAux_smul_eq hcov' σ f hx hX' hf x
    · intro σ σ' hσ hσ'
      unfold φ differenceAux
      simp only [Pi.sub_apply]
      rw [hcov.addσ, hcov'.addσ] <;> try assumption
      abel

lemma isBilinearMap_differenceAux
    [FiniteDimensional ℝ F] [T2Space M] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I] {s : Set M} {cov cov'} {x : M}
    (hcov : IsCovariantDerivativeOn F cov s)
    (hcov' : IsCovariantDerivativeOn F cov' s) (hx : x ∈ s := by trivial) :
    IsBilinearMap ℝ (fun (X₀ : TangentSpace I x) (σ₀ : V x) ↦
      differenceAux cov cov' (extend I E X₀) (extend I F σ₀) x) where
  add_left u v w := by
    simp only [differenceAux, extend_add, Pi.sub_apply]
    rw [hcov.addX, hcov'.addX]; · abel
    all_goals apply mdifferentiable_extend
  add_right u v w := by
    simp only [differenceAux, extend_add, Pi.sub_apply]
    rw [hcov.addσ, hcov'.addσ]; · abel
    all_goals apply mdifferentiable_extend
  smul_left a u v := by
    simp only [differenceAux, extend_smul, Pi.sub_apply]
    rw [hcov.smul_const_X, hcov'.smul_const_X]; · module
    all_goals apply mdifferentiable_extend
  smul_right a u v := by
    simp only [differenceAux, extend_smul, Pi.sub_apply]
    rw [hcov.smul_const_σ, hcov'.smul_const_σ]; · module
    all_goals apply mdifferentiable_extend

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

/-- The difference of two covariant derivatives, as a tensorial map -/
noncomputable def difference [∀ x, FiniteDimensional ℝ (V x)] [∀ x, T2Space (V x)]
    [FiniteDimensional ℝ F] [T2Space M] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {s : Set M}
    (hcov : IsCovariantDerivativeOn F cov s)
    (hcov' : IsCovariantDerivativeOn F cov' s)
    (x : M) : TangentSpace I x →L[ℝ] V x →L[ℝ] V x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := by assumption
  open Classical in
  if hx : x ∈ s then (isBilinearMap_differenceAux (F := F) hcov hcov').toContinuousLinearMap
  else 0

lemma difference_def [∀ x, FiniteDimensional ℝ (V x)] [∀ x, T2Space (V x)]
    [FiniteDimensional ℝ F] [T2Space M] [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {s : Set M} {x : M}
    (hcov : IsCovariantDerivativeOn F cov s)
    (hcov' : IsCovariantDerivativeOn F cov' s)
    (hx : x ∈ s := by trivial) (X₀ : TangentSpace I x) (σ₀ : V x) :
    difference hcov hcov' x X₀ σ₀ =
      cov (extend I E X₀) (extend I F σ₀) x - cov' (extend I E X₀) (extend I F σ₀) x := by
  simp only [difference, hx, reduceDIte]
  rfl

@[simp]
lemma difference_apply [∀ x, FiniteDimensional ℝ (V x)] [∀ x, T2Space (V x)]
    [FiniteDimensional ℝ F] [T2Space M] [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {s : Set M} {x : M}
    (hcov : IsCovariantDerivativeOn F cov s)
    (hcov' : IsCovariantDerivativeOn F cov' s)
    (hx : x ∈ s := by trivial) {X : Π x, TangentSpace I x} {σ : Π x, V x}
    (hX : MDiffAt (T% X) x) (hσ : MDiffAt (T% σ) x) :
    difference hcov hcov' x (X x) (σ x) =
      cov X σ x - cov' X σ x := by
  simp only [difference, hx, reduceDIte]
  exact hcov.differenceAux_tensorial hcov' (mdifferentiable_extend ..) hX
    (mdifferentiable_extend ..) hσ (extend_apply_self _) (extend_apply_self _) hx

-- The classification of real connections over a trivial bundle
section classification

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [IsManifold I ∞ M]

/-- Classification of covariant derivatives over a trivial vector bundle: every connection
is of the form `D + A`, where `D` is the trivial covariant derivative, and `A` a zeroth-order term
-/
lemma exists_one_form {cov : (Π x : M, TangentSpace I x) → (M → F) → (M → F)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s) :
    ∃ (A : (x : M) → TangentSpace I x →L[ℝ] F →L[ℝ] F),
    ∀ X : (x : M) → TangentSpace I x, ∀ σ : M → F, ∀ x ∈ s,
    MDiffAt (T% X) x → MDiffAt (T% σ) x →
    letI d : F := mfderiv I 𝓘(ℝ, F) σ x (X x)
    cov X σ x = d + A x (X x) (σ x) := by
  use fun x ↦ hcov.difference (trivial I M F |>.mono <| subset_univ s) x
  intro X σ x hx hX hσ
  rw [hcov.difference_apply _ (by trivial) hX hσ]
  module

noncomputable def one_form {cov : (Π x : M, TangentSpace I x) → (M → F) → (M → F)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s) :
    Π x : M, TangentSpace I x →L[ℝ] F →L[ℝ] F :=
  hcov.exists_one_form.choose

lemma eq_one_form {cov : (Π x : M, TangentSpace I x) → (M → F) → (M → F)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)
    {X : (x : M) → TangentSpace I x} {σ : M → F}
    {x : M} (hX : MDiffAt (T% X) x) (hσ : MDiffAt (T% σ) x) (hx : x ∈ s := by trivial) :
    letI d : F := mfderiv I 𝓘(ℝ, F) σ x (X x)
    cov X σ x = d + hcov.one_form x (X x) (σ x) :=
  hcov.exists_one_form.choose_spec X σ x hx hX hσ

lemma _root_.CovariantDerivative.exists_one_form
    (cov : CovariantDerivative I F (Bundle.Trivial M F)) :
    ∃ (A : (x : M) → TangentSpace I x →L[ℝ] F →L[ℝ] F),
    ∀ X : (x : M) → TangentSpace I x, ∀ σ : M → F, ∀ x,
    MDiffAt (T% X) x → MDiffAt (T% σ) x →
    letI d : F := mfderiv I 𝓘(ℝ, F) σ x (X x)
    cov X σ x = d + A x (X x) (σ x) := by
  simpa using cov.isCovariantDerivativeOn.exists_one_form

end classification

section projection_trivial_bundle

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [IsManifold I ∞ M]

local notation "TM" => TangentSpace I

instance (f : F) : CoeOut (TangentSpace 𝓘(ℝ, F) f) F :=
  ⟨fun x ↦ x⟩

variable {cov : (Π x : M, TangentSpace I x) → (M → F) → (M → F)} {s : Set M}

noncomputable
def projection (hcov : IsCovariantDerivativeOn F cov s) (x : M) (f : F) : (TM x) × F →L[ℝ] F :=
  .snd ℝ (TM x) F + (evalL ℝ F F f ∘L hcov.one_form x ∘L .fst ℝ (TM x) F)

@[simp]
lemma projection_apply (hcov : IsCovariantDerivativeOn F cov s) (x : M) (f : F) (v : TM x) (w : F) :
  hcov.projection x f (v, w) = w + hcov.one_form x v f := rfl

lemma cov_eq_proj (hcov : IsCovariantDerivativeOn F cov s) (X : Π x : M, TM x) (σ : M → F)
    {x : M} (hX : MDiffAt (T% X) x) (hσ : MDiffAt (T% σ) x) (hx : x ∈ s := by trivial) :
    cov X σ x = hcov.projection x (σ x) (X x, mfderiv I 𝓘(ℝ, F) σ x (X x)) := by
  simpa using hcov.eq_one_form hX hσ

noncomputable def horiz (hcov : IsCovariantDerivativeOn F cov s) (x : M) (f : F) :
    Submodule ℝ (TM x × F) :=
  (hcov.projection x f).ker

lemma horiz_vert_direct_sum (hcov : IsCovariantDerivativeOn F cov s) (x : M) (f : F) :
    IsCompl (hcov.horiz x f) (.prod ⊥ ⊤) := by
  refine IsCompl.of_eq ?_ ?_
  · refine (Submodule.eq_bot_iff _).mpr ?_
    rintro ⟨u, w⟩ ⟨huw, hu, hw⟩
    simp_all [horiz]
  · apply Submodule.sup_eq_top_iff _ _ |>.2
    intro u
    use u - (0, hcov.projection x f u), ?_, (0, hcov.projection x f u), ?_, ?_
    all_goals simp [horiz]

lemma mem_horiz_iff_exists (hcov : IsCovariantDerivativeOn F cov s) {x : M} {f : F}
    {u : TM x} {v : F} (hx : x ∈ s := by trivial) : (u, v) ∈ hcov.horiz x f ↔
    ∃ σ : M → F, MDiffAt (T% σ) x ∧
                 σ x = f ∧
                 mfderiv I 𝓘(ℝ, F) σ x u = v ∧
                 cov (extend I E u) σ x = 0 := by
  constructor
  · intro huv
    simp only [horiz, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, projection_apply] at huv
    let w : TangentSpace 𝓘(ℝ, F) f := v
    by_cases hu : u = 0
    · subst hu
      replace huv : v = 0 := by simpa using huv
      subst huv
      use fun x ↦ f
      simp [hcov.zeroX, mdifferentiableAt_section,  mdifferentiableAt_const]
    rcases map_of_one_jet_spec u w (by tauto) with ⟨h, h', h''⟩
    use map_of_one_jet u w, ?_, h, h''
    · rw [hcov.eq_one_form (mdifferentiable_extend ..)]
      · simp [w, h'', h, huv]
      · rwa [mdifferentiableAt_section]
    · rwa [mdifferentiableAt_section]
  · rintro ⟨σ, σ_diff, rfl, rfl, covσ⟩
    simp only [horiz, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, projection_apply, ← covσ]
    rw [hcov.eq_one_form (mdifferentiable_extend ..) σ_diff, extend_apply_self]

end projection_trivial_bundle

end IsCovariantDerivativeOn

section to_trivialization

variable (e : Trivialization F (π F V)) [MemTrivializationAtlas e] [IsManifold I 1 M]

lemma Trivialization.map_add
    [VectorBundle ℝ F V]
    {x : M} (hx : x ∈ e.baseSet) (v v' : V x) :
    (e ⟨x, v + v'⟩).2 = (e ⟨x, v⟩).2 + (e ⟨x, v'⟩).2 :=
  e.linear ℝ hx |>.map_add v v'

lemma Trivialization.symm_map_add [VectorBundle ℝ F V] {x : M} (f f' : F) :
    e.symm x (f + f') = e.symm x f + e.symm x f' :=
  (symmL ℝ e x).map_add f f'

lemma Trivialization.symm_map_smul [VectorBundle ℝ F V] {x : M} (a : ℝ) (f : F) :
    e.symm x (a • f) = a • e.symm x f :=
  (symmL ℝ e x).map_smul a f

lemma Trivialization.map_smul
    [VectorBundle ℝ F V]
    {x : M} (hx : x ∈ e.baseSet) (a : ℝ) (v : V x) :
    (e ⟨x, a • v⟩).2 = a • (e ⟨x, v⟩).2 :=
  e.linear ℝ hx |>.map_smul a v

omit [NormedSpace ℝ F] [(x : M) → Module ℝ (V x)] [MemTrivializationAtlas e]
  [(x : M) → AddCommGroup (V x)]
  [(x : M) → TopologicalSpace (V x)] [FiberBundle F V] in
lemma Trivialization.baseSet_mem_nhds {x : M} (hx : x ∈ e.baseSet) : e.baseSet ∈ 𝓝 x :=
  e.open_baseSet.mem_nhds_iff.mpr hx

omit [NormedSpace ℝ F] [(x : M) → Module ℝ (V x)] [MemTrivializationAtlas e]
  [(x : M) → AddCommGroup (V x)] in
lemma Trivialization.preimage_baseSet_mem_nhds {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet) :
    TotalSpace.proj ⁻¹' e.baseSet ∈ 𝓝 v :=
  FiberBundle.continuous_proj F V |>.continuousAt <| e.baseSet_mem_nhds  hv

omit [NormedSpace ℝ F] [(x : M) → Module ℝ (V x)] [MemTrivializationAtlas e]
  [(x : M) → AddCommGroup (V x)] [(x : M) → TopologicalSpace (V x)] in
lemma Trivialization.baseSet_prod_univ_mem_nhds {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet) :
    e.baseSet ×ˢ univ ∈ 𝓝 (e v) := by
  rw [← mk_proj_snd' e hv]
  exact prod_mem_nhds (e.baseSet_mem_nhds hv) univ_mem

omit [NormedSpace ℝ F] [(x : M) → Module ℝ (V x)] [(x : M) → TopologicalSpace (V x)]
    [FiberBundle F V] [MemTrivializationAtlas e] [(x : M) → AddCommGroup (V x)] in
lemma Trivialization.comp_invFun_eventuallyEq
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet) : e ∘ e.invFun =ᶠ[𝓝 (e v)] id := by
  filter_upwards [e.baseSet_prod_univ_mem_nhds hv] with p hp using
    apply_symm_apply e <| (mem_target e).2 hp.1

omit [NormedSpace ℝ F] [(x : M) → Module ℝ (V x)] [MemTrivializationAtlas e]
  [(x : M) → AddCommGroup (V x)] in
lemma Trivialization.invFun_comp_eventuallyEq
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet) : e.invFun ∘ e =ᶠ[𝓝 v] id := by
  filter_upwards [e.preimage_baseSet_mem_nhds hv] with w hw using
    symm_apply_apply e <| (mem_source e).mpr hw

variable (I) in
omit [MemTrivializationAtlas e] [IsManifold I 1 M] in
lemma Trivialization.fst_comp_eventuallyEq
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet) :
    Prod.fst ∘ e =ᶠ[𝓝 v] TotalSpace.proj := by
  filter_upwards [preimage_baseSet_mem_nhds e hv] with y hy using coe_fst' e hy

omit [IsManifold I 1 M] in
lemma Trivialization.mdifferentiableAt
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {x : M} (hx : x ∈ e.baseSet) (v : V x) :
MDifferentiableAt (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) e v := by
  have : ⟨x, v⟩ ∈ e.source := (coe_mem_source e).mpr hx
  have foo := e.contMDiffOn (IB := I) (n := 1) v this
  have := foo.contMDiffAt (e.open_source.mem_nhds this)
  exact this.mdifferentiableAt zero_ne_one.symm

omit [IsManifold I 1 M] in
lemma Trivialization.mdifferentiableAt_invFun
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {x : M} (hx : x ∈ e.baseSet) (f : F) :
    MDifferentiableAt (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) e.invFun (x, f) := by
  have : ⟨x, f⟩ ∈ e.target := (mk_mem_target e).mpr hx
  have foo := e.contMDiffOn_symm (IB := I) (n := 1) _ this
  have := foo.contMDiffAt (e.open_target.mem_nhds this)
  exact this.mdifferentiableAt zero_ne_one.symm

-- Note: The definition below (ab)uses definitional
-- equality of `TangentSpace (I.prod 𝓘(ℝ, F)) (↑t v)`
-- which is $T_{t(v)} (M × F)$ and `TM v.proj × F`
-- which is $T_{π(v)} M × F$.
variable (I) in
noncomputable
def Trivialization.deriv (v : TotalSpace F V) :
    TangentSpace (I.prod 𝓘(ℝ, F)) v →L[ℝ] TangentSpace I v.proj × F :=
  mfderiv (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) e v

omit [IsManifold I 1 M] in
lemma Trivialization.bijective_deriv
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet) :
    Function.Bijective (e.deriv I v) := by
  have D₁ := e.mdifferentiableAt_invFun (I := I) hv (e v).2
  rw [mk_proj_snd' e hv] at D₁
  have D₂ : MDifferentiableAt _ _ e v := e.mdifferentiableAt (I := I) hv v.2
  constructor
  · apply injective_mfderiv_of_eventually_leftInverse v D₁ D₂
    apply e.invFun_comp_eventuallyEq hv
  · have : v = e.invFun (e v) :=
      (Eventually.self_of_nhds <| e.invFun_comp_eventuallyEq hv).symm
    apply surjective_mfderiv_of_eventually_rightInverse this D₂ D₁
      (e.comp_invFun_eventuallyEq hv)

omit [NormedSpace ℝ F]
     [(x : M) → Module ℝ (V x)] [(x : M) → TopologicalSpace (V x)]
     [FiberBundle F V] [MemTrivializationAtlas e] in
lemma Trivialization.symm_apply_apply_mk_eventuallyEq
    {x : M} (hx : x ∈ e.baseSet) (σ : Π x, V x) :
    (T% fun x' ↦ e.symm x' (e (T% σ x')).2) =ᶠ[𝓝 x] T% σ := by
  filter_upwards [e.baseSet_mem_nhds hx] with y hy
  simp [symm_apply_apply_mk e hy (σ y)]

omit [NormedSpace ℝ F] [(x : M) → AddCommGroup (V x)]
     [(x : M) → Module ℝ (V x)] [(x : M) → TopologicalSpace (V x)]
     [FiberBundle F V] [MemTrivializationAtlas e] in
lemma Trivialization.apply_section_eventuallyEq
    {x : M} (hx : x ∈ e.baseSet) (σ : Π x, V x) :
    e ∘ T%σ =ᶠ[𝓝 x] fun x ↦ ⟨x, (e (σ x)).2⟩ := by
  filter_upwards [e.baseSet_mem_nhds hx] with y hy
  ext
  · exact coe_coe_fst e hy
  · simp

omit [NormedSpace ℝ F] [(x : M) → Module ℝ (V x)]
[(x : M) → TopologicalSpace (V x)] [FiberBundle F V] [MemTrivializationAtlas e] in
@[simp]
lemma Trivialization.apply_symm_eventuallyEq {x : M} (hx : x ∈ e.baseSet) (s : M → F) :
  (fun x ↦ (e ⟨x, e.symm x (s x)⟩).2) =ᶠ[𝓝 x] s := by
    filter_upwards [e.baseSet_mem_nhds hx] with y hy
    rw [e.apply_mk_symm hy]

omit [IsManifold I 1 M] in
lemma Trivialization.mdifferentiableAt_section_of_function
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {x : M} (hx : x ∈ e.baseSet) {s : M → F}
    (hs : MDiffAt s x) :
    MDiffAt ((fun x' ↦ (⟨x', e.symm x' (s x')⟩ : TotalSpace F V))) x := by
  rw [e.mdifferentiableAt_section_iff (IB := I) _ hx]
  have := e.apply_symm_eventuallyEq hx s
  exact hs.congr_of_eventuallyEq this

omit [IsManifold I 1 M] in
noncomputable def _root_.Bundle.vert (v : TotalSpace F V) :
    Submodule ℝ (TangentSpace (I.prod 𝓘(ℝ, F)) v) :=
  (mfderiv (I.prod 𝓘(ℝ, F)) I Bundle.TotalSpace.proj v).ker

omit [IsManifold I 1 M] in
lemma Trivialization.comap_vert
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet) :
    Bundle.vert v = Submodule.comap (e.deriv I v).toLinearMap
      (Submodule.prod ⊥ ⊤) := by
  ext x
  have : Prod.fst ∘ e =ᶠ[𝓝 v] TotalSpace.proj := e.fst_comp_eventuallyEq I hv
  unfold vert
  rw [← this.mfderiv_eq]
  have mdiffe : MDifferentiableAt (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) e v :=
    e.mdifferentiableAt hv _
  rw [mfderiv_comp v mdifferentiableAt_fst mdiffe]
  simp
  rfl

-- FIXME: is this really missing??
omit [NormedSpace ℝ F] [(x : M) → Module ℝ (V x)]
  [(x : M) → TopologicalSpace (V x)] [FiberBundle F V] [MemTrivializationAtlas e] in
lemma Trivialization.eq_of {x : M} {v v' : V x}
   (hx : x ∈ e.baseSet) (hvv' : (e v).2 = (e v').2) :
    v = v' := by
  have := e.symm_proj_apply v hx
  rw [hvv'] at this
  grind [e.symm_proj_apply v' hx]

omit [IsManifold I 1 M] in
lemma Trivialization.mfderiv_comp_section
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {σ : Π x : M, V x} {x : M} (hσ : MDiffAt T%σ x)
    (u : TangentSpace I x) (hx : x ∈ e.baseSet) :
    letI s := fun x ↦ (e (σ x)).2
    (e.deriv I (σ x)).toLinearMap ((mfderiv% T%σ x) u) = (u, mfderiv I 𝓘(ℝ, F) s x u) := by
  have mdiffe : MDifferentiableAt (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) e (σ x) :=
    e.mdifferentiableAt hx _
  have : mfderiv I (I.prod 𝓘(ℝ, F)) (e ∘ T%σ) x =
    (e.deriv I (σ x)) ∘L (mfderiv% T%σ x) :=
    mfderiv_comp x mdiffe hσ
  have : mfderiv I (I.prod 𝓘(ℝ, F)) (e ∘ T%σ) x u =
    e.deriv I (σ x) ((mfderiv% T%σ x) u) := by
    rw [this]
    rfl
  erw [← this]
  let s := fun x ↦ (e (σ x)).2
  change mfderiv I (I.prod 𝓘(ℝ, F)) (e ∘ T%σ) x u = (u, mfderiv% s x u)
  rw [(e.apply_section_eventuallyEq hx _).mfderiv_eq]
  erw [mfderiv_prodMk, mfderiv_id]
  · change (ContinuousLinearMap.id _ _).prod (mfderiv% s x) u = _
    simp
  · apply mdifferentiableAt_id
  · exact (mdifferentiableAt_section_iff I e σ hx).mp hσ

noncomputable
def Trivialization.pushCovDer
    (cov : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)) :
    (Π x : M, TangentSpace I x) → (M → F) → (M → F) :=
  fun X σ x ↦ e (cov X (fun x' ↦ e.symm x' <| σ x') x) |>.2

omit [MemTrivializationAtlas e] in
lemma Trivialization.pushCovDer_ofSect [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [IsManifold I ∞ M]
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {cov : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (hcov : IsCovariantDerivativeOn F cov e.baseSet)
    {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x} {x : M}
    (hX : MDiffAt T%X x) (hσ : MDiffAt T%σ x)
    (hx : x ∈ e.baseSet := by assumption) :
    (e.pushCovDer cov) X (fun x ↦ (e (σ x)).2) x = (e (cov X σ x)).2 := by
  have : cov X (fun x' ↦ e.symm x' (e (T% σ x')).2) x = cov X σ x := by
    apply hcov.congr_σ_of_eqOn hX _ hσ (e.baseSet_mem_nhds hx)
    · exact fun y hy ↦ symm_apply_apply_mk e hy (σ y) --FIXME extract as lemma?
    · rw [(e.symm_apply_apply_mk_eventuallyEq hx σ).mdifferentiableAt_iff]
      exact hσ
  unfold pushCovDer
  rw [this]

omit [IsManifold I 1 M] in
@[simp]
lemma mdifferentiableAt_section_trivial_iff {s : M → F} {x : M} :
    MDiffAt (T% s) x ↔ MDiffAt s x := by
  rw [mdifferentiableAt_section I]
  simp

variable {cov : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    -- {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)

lemma Trivialization.pushCovDer_isCovariantDerivativeOn
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    (hcov : IsCovariantDerivativeOn F cov e.baseSet) :
    IsCovariantDerivativeOn F (e.pushCovDer cov) e.baseSet where
  addX {X X' σ x} hX hX' hσ hx := by
    set s := (fun x' ↦ e.symm x' (σ x'))
    have hs : MDiffAt (T% s) x :=
      e.mdifferentiableAt_section_of_function hx <| mdifferentiableAt_section_trivial_iff.1 hσ
    unfold Trivialization.pushCovDer
    rw [hcov.addX hX hX' hs, e.map_add hx]
  smulX {X σ g x} hX hσ hg hx := by
    set s := (fun x' ↦ e.symm x' (σ x'))
    have hs : MDiffAt (T% s) x :=
      e.mdifferentiableAt_section_of_function hx <| mdifferentiableAt_section_trivial_iff.1 hσ
    unfold Trivialization.pushCovDer
    rw [hcov.smulX hX hs hg, e.map_smul hx]
  smul_const_σ {X σ x} a hX hσ hx := by
    set s := (fun x' ↦ e.symm x' (σ x'))
    have hs : MDiffAt (T% s) x :=
      e.mdifferentiableAt_section_of_function hx <| mdifferentiableAt_section_trivial_iff.1 hσ
    unfold Trivialization.pushCovDer
    rw [← e.map_smul hx, ← hcov.smul_const_σ a hX hs hx]
    congr
    ext y
    simp [e.symm_map_smul, s]
  addσ {X σ σ' x} hX hσ hσ' hx := by
    set s := (fun x' ↦ e.symm x' (σ x'))
    have hs : MDiffAt (T% s) x :=
      e.mdifferentiableAt_section_of_function hx <| mdifferentiableAt_section_trivial_iff.1 hσ
    set s' := (fun x' ↦ e.symm x' (σ' x'))
    have hs' : MDiffAt (T% s') x :=
      e.mdifferentiableAt_section_of_function hx <| mdifferentiableAt_section_trivial_iff.1
      hσ'
    unfold Trivialization.pushCovDer
    rw [← e.map_add hx]
    congr
    rw [← hcov.addσ hX hs hs' hx]
    congr
    ext y
    simp [e.symm_map_add, s, s']
  leibniz {X σ g x} hX hσ hg hx := by
    set s := (fun x' ↦ e.symm x' (σ x'))
    have hs : MDiffAt (T% s) x :=
      e.mdifferentiableAt_section_of_function hx <| mdifferentiableAt_section_trivial_iff.1 hσ
    unfold Trivialization.pushCovDer
    have : (fun x' ↦ e.symm x' ((g • σ) x')) = g • s := by
      ext y
      simp [s, e.symm_map_smul]
    rw [this, hcov.leibniz hX hs hg hx]
    suffices g x • (e ⟨x, cov X s x⟩).2 + (bar (g x)) ((mfderiv% g x) (X x)) • (e ⟨x, s x⟩).2 =
      g x • (e ⟨x, cov X (fun x' ↦ e.symm x' (σ x')) x⟩).2 +
      (bar (g x)) ((mfderiv% g x) (X x)) • σ x by simpa [e.map_add hx, e.map_smul hx]
    congr
    rw [e.apply_mk_symm hx]

end to_trivialization

section horiz
namespace CovariantDerivative

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [IsManifold I ∞ M]
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]

local notation "TM" => TangentSpace I

-- FIXME the statement of CovariantDerivative.isCovariantDerivativeOn should work on any set

noncomputable
def proj (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    TangentSpace (I.prod 𝓘(ℝ, F)) v →L[ℝ] V v.proj :=
  letI t := trivializationAt F V v.proj
  haveI d_covDerOn := t.pushCovDer_isCovariantDerivativeOn
    (cov.isCovariantDerivativeOn.mono fun _ _ ↦ mem_univ _)
  letI tproj := d_covDerOn.projection v.proj (t v).2
  letI Tvt := t.deriv I v
  t.symmL ℝ v.proj ∘L tproj ∘L Tvt

lemma snd_triv_proj (cov : CovariantDerivative I F V) (v : TotalSpace F V) (u : TangentSpace (I.prod
  𝓘(ℝ, F)) v) :
    letI t := trivializationAt F V v.proj
    haveI d_covDerOn := t.pushCovDer_isCovariantDerivativeOn
      (cov.isCovariantDerivativeOn.mono fun _ _ ↦ mem_univ _)
    letI tproj := d_covDerOn.projection v.proj (t v).2
    letI Tvt := t.deriv I v
    (t <| cov.proj v u).2 = tproj (Tvt u) := by
  simp [CovariantDerivative.proj, (mem_baseSet_trivializationAt F V v.proj)]


noncomputable def horiz (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    Submodule ℝ (TangentSpace (I.prod 𝓘(ℝ, F)) v) :=
  (cov.proj v).ker

lemma comap_trivializationAt_horiz (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    letI t := trivializationAt F V v.proj
    haveI d_covDerOn := t.pushCovDer_isCovariantDerivativeOn
      (cov.isCovariantDerivativeOn.mono fun _ _ ↦ mem_univ _)
    horiz cov v = Submodule.comap (t.deriv I v).toLinearMap
      (d_covDerOn.horiz v.proj (t v).2) := by
  -- FIXME: needing all those lets and the change is awful
  let t := trivializationAt F V v.proj
  let Tvt := t.deriv I v
  have hcov := t.pushCovDer_isCovariantDerivativeOn
    (cov.isCovariantDerivativeOn.mono fun _ _ ↦ mem_univ _)
  let tproj := hcov.projection v.proj (t v).2
  let t' := t.continuousLinearEquivAt ℝ v.proj (mem_baseSet_trivializationAt F V v.proj)
  ext u
  change t'.symm (tproj (Tvt u)) = 0 ↔ tproj (Tvt u) = 0
  simp

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

omit [ContMDiffVectorBundle 1 F V I] in
lemma horiz_vert_direct_sum [ContMDiffVectorBundle 1 F V I]
    (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    IsCompl (cov.horiz v) (vert v) := by
  let t := trivializationAt F V v.proj
  let Tvt := t.deriv I v
  have hcov := t.pushCovDer_isCovariantDerivativeOn
    (cov.isCovariantDerivativeOn.mono fun _ _ ↦ mem_univ _)
  rw [t.comap_vert (mem_baseSet_trivializationAt F V v.proj), comap_trivializationAt_horiz]
  apply LinearMap.comap_isCompl
  · apply t.bijective_deriv
    exact FiberBundle.mem_baseSet_trivializationAt' v.proj
  · apply hcov.horiz_vert_direct_sum

variable [IsManifold I 1 M]
variable {cov : CovariantDerivative I F V}

omit [ContMDiffVectorBundle 1 F V I] in
lemma proj_mderiv [ContMDiffVectorBundle 1 F V I]
    {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x} (x : M)
    (hX : MDiffAt (T% X) x)
    (hσ : MDiffAt (T% σ) x) :
    cov X σ x = cov.proj (σ x)
      (mfderiv I (I.prod 𝓘(ℝ, F)) (T% σ) x (X x)) := by
  let t := trivializationAt F V x
  let s := fun x ↦ (t (σ x)).2
  let Tσx := mfderiv% (T% σ) x
  -- FIXME `mfderiv%` fails in next line (fixed on master?)
  let Ttσx := mfderiv (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) t (σ x)
  change cov X σ x = (cov.proj (T% σ x)) ((mfderiv% (T% σ) x) (X x))
  have hcov := t.pushCovDer_isCovariantDerivativeOn
    (cov.isCovariantDerivativeOn.mono fun _ _ ↦ mem_univ _)
  have hx := mem_baseSet_trivializationAt F V x
  have hs : MDiffAt (T% s) x := by
    rw [t.mdifferentiableAt_section_iff I σ hx] at hσ
    exact (mdifferentiableAt_section I s).mpr hσ
  apply t.eq_of hx
  erw  [cov.snd_triv_proj (T% σ x),
       ← t.pushCovDer_ofSect (cov.isCovariantDerivativeOn.mono fun _ _ ↦ mem_univ _) hX hσ,
       hcov.cov_eq_proj X s hX hs, t.mfderiv_comp_section hσ _ hx]

end CovariantDerivative
end horiz

end real


-- variable (E E') in
-- /-- The trivial connection on a trivial bundle, given by the directional derivative -/
-- @[simps]
-- noncomputable def trivial : CovariantDerivative 𝓘(𝕜, E) E'
--   (Bundle.Trivial E E') where
--   toFun X s := fun x ↦ fderiv 𝕜 s x (X x)
--   isCovariantDerivativeOn :=
--   { addX X X' σ x _ := by simp
--     smulX X σ c' x _ := by simp
--     addσ X σ σ' x hσ hσ' hx := by
--       rw [Bundle.Trivial.mdifferentiableAt_iff] at hσ hσ'
--       rw [fderiv_add hσ hσ']
--       rfl
--     smul_const_σ X σ a x hx := by simp [fderiv_const_smul_of_field a]
--     leibniz X σ f x hσ hf hx := by
--       have : fderiv 𝕜 (f • σ) x = f x • fderiv 𝕜 σ x + (fderiv 𝕜 f x).smulRight (σ x) :=
--         fderiv_smul (by simp_all) (by simp_all)
--       simp [this, bar]
--       rfl }
