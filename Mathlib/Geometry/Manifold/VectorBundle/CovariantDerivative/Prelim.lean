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
# Supporting lemmas for CovariantDerivative.Basic

TODO: PR all this to appropriate places.

-/

open Bundle Filter Module Topology Set

open scoped Bundle Manifold ContDiff

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
  simp [extend]

@[simp]
lemma extend_smul [FiniteDimensional ℝ F] [T2Space M] {a : ℝ} {x : M} (v : V x) :
  extend I F (a • v) = a • extend I F v := by simp [extend]; module

@[simp]
lemma extend_zero [FiniteDimensional ℝ F] [T2Space M] (x : M) :
  extend I F (0 : V x) = 0 := by simp [extend]

@[simp] lemma extend_apply_self [FiniteDimensional ℝ F] [T2Space M] {x : M} (v : V x) :
    extend I F v x = v := by
  simpa [extend] using
    localExtensionOn_apply_self _ _ (FiberBundle.mem_baseSet_trivializationAt' x) v

variable (I F)

lemma contMDiff_extend [IsManifold I ∞ M] [FiniteDimensional ℝ F] [T2Space M]
    [ContMDiffVectorBundle ∞ F V I] {x : M} (σ₀ : V x) :
    CMDiff ∞ (T% (extend I F σ₀)) := by
  letI t := trivializationAt F V x
  letI ht := t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let ψ := Classical.choose <| (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.1 ht
  let hψ :=
    Classical.choose_spec <| (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.1 ht
  exact ContMDiffOn.smul_section_of_tsupport ψ.contMDiff.contMDiffOn t.open_baseSet hψ.1
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

namespace Bundle.Trivialization

section trivilization_topology

variable {B F Z : Type*} [TopologicalSpace B]
  [TopologicalSpace F]

section any_proj

variable [TopologicalSpace Z] {proj : Z → B} (e : Trivialization F proj)
lemma baseSet_mem_nhds {x : B} (hx : x ∈ e.baseSet) : e.baseSet ∈ 𝓝 x :=
  e.open_baseSet.mem_nhds_iff.mpr hx

lemma baseSet_prod_univ_mem_nhds {v : Z}
    (hv : proj v ∈ e.baseSet) : e.baseSet ×ˢ univ ∈ 𝓝 (e v) := by
  rw [← mk_proj_snd' e hv]
  exact prod_mem_nhds (e.baseSet_mem_nhds hv) univ_mem

lemma comp_invFun_eventuallyEq
    {v : Z} (hv : proj v ∈ e.baseSet) : e ∘ e.invFun =ᶠ[𝓝 (e v)] id := by
  filter_upwards [e.baseSet_prod_univ_mem_nhds hv] with p hp
    using by simp [(mem_target e).2 hp.1]

end any_proj

section fiber_bundle
variable {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  (e : Trivialization F (π F E))

lemma proj_invFun_eventuallyEq
    {v : TotalSpace F E} (hv : v.proj ∈ e.baseSet) :
    (TotalSpace.proj ∘ e.invFun) =ᶠ[𝓝 (e v)] Prod.fst := by
  filter_upwards [e.baseSet_prod_univ_mem_nhds hv] with ⟨x, f⟩ ⟨hx, hf⟩
  simp [hx]

lemma injective_symm [(x : B) → Zero (E x)]
  {v : TotalSpace F E} (hv : v.proj ∈ e.baseSet) :
    Function.Injective (e.symm v.proj) := by
  intro f f' hff'
  simpa [hv] using congr(e $hff')

lemma surjective_symm [(x : B) → Zero (E x)]
  {v : TotalSpace F E} (hv : v.proj ∈ e.baseSet) :
    Function.Surjective (e.symm v.proj) :=
  fun u ↦ ⟨(e u).2, by simp [*]⟩

lemma bijective_symm [(x : B) → Zero (E x)]
  {v : TotalSpace F E} (hv : v.proj ∈ e.baseSet) :
    Function.Bijective (e.symm v.proj) :=
  ⟨e.injective_symm hv, e.surjective_symm hv⟩

variable [(b : B) → TopologicalSpace (E b)] [FiberBundle F E]

lemma preimage_baseSet_mem_nhds
   {v : TotalSpace F E} (hv : v.proj ∈ e.baseSet) :
    TotalSpace.proj ⁻¹' e.baseSet ∈ 𝓝 v :=
  FiberBundle.continuous_proj F E |>.continuousAt <| e.baseSet_mem_nhds hv

lemma fst_comp_eventuallyEq
   {v : TotalSpace F E} (hv : v.proj ∈ e.baseSet) :
    Prod.fst ∘ e =ᶠ[𝓝 v] (π F E) := by
  filter_upwards [preimage_baseSet_mem_nhds e hv] with y hy using coe_fst' e hy

lemma invFun_comp_eventuallyEq
  {v : TotalSpace F E} (hv : v.proj ∈ e.baseSet) :
   e.invFun ∘ e =ᶠ[𝓝 v] id := by
  filter_upwards [e.preimage_baseSet_mem_nhds hv] with w hw using
    by simp [(mem_source e).mpr hw]

end fiber_bundle

section
variable {B F : Type*} {E : B → Type*} [TopologicalSpace B]
  [TopologicalSpace F] [TopologicalSpace (TotalSpace F E)]
  [(x : B) → Zero (E x)]
  (e : Trivialization F (π F E))

lemma eq_of {x : B} {v v' : E x}
   (hx : x ∈ e.baseSet) (hvv' : (e v).2 = (e v').2) :
    v = v' := by
  have := e.symm_proj_apply v hx
  rw [hvv'] at this
  grind [e.symm_proj_apply v' hx]

@[simp]
lemma apply_symm_eventuallyEq {x : B} (hx : x ∈ e.baseSet) (s : B → F) :
  (fun x ↦ (e ⟨x, e.symm x (s x)⟩).2) =ᶠ[𝓝 x] s := by
    filter_upwards [e.baseSet_mem_nhds hx] with y hy using by simp [hy]

variable [(b : B) → TopologicalSpace (E b)] [FiberBundle F E]

-- FIXME super weird elaborator bug: removing the
-- omitted assumption from the variable line breaks the lemma
omit [(b : B) → TopologicalSpace (E b)] [FiberBundle F E] in
lemma symm_apply_apply_mk_eventuallyEq
    {b : B} (hb : b ∈ e.baseSet) (σ : Π x, E x) :
    (T% fun x' ↦ e.symm x' (e (T% σ x')).2) =ᶠ[𝓝 b] T% σ := by
  filter_upwards [e.baseSet_mem_nhds hb] with y hy using by simp [*]

-- FIXME super weird elaborator bug: removing the
-- omitted assumption from the variable line breaks the lemma
omit [(x : B) → Zero (E x)] [(b : B) → TopologicalSpace (E b)] [FiberBundle F E] in
lemma apply_section_eventuallyEq
    {x : B} (hx : x ∈ e.baseSet) (σ : Π x, E x) :
    e ∘ T%σ =ᶠ[𝓝 x] fun x ↦ ⟨x, (e (σ x)).2⟩ := by
  filter_upwards [e.baseSet_mem_nhds hx] with y hy
  ext
  · exact coe_coe_fst e hy
  · simp

end

end trivilization_topology

section topological_vector_bundle

section
variable {R B F : Type*} {E : B → Type*} [Semiring R]
  [TopologicalSpace F] [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  (e : Trivialization F (π F E))
  [AddCommMonoid F] [Module R F] [(x : B) → AddCommMonoid (E x)] [(x : B) → Module R (E x)]

lemma map_smul [Trivialization.IsLinear R e]
    {b : B} (hb : b ∈ e.baseSet) (a : R) (v : E b) :
    (e ⟨b, a • v⟩).2 = a • (e ⟨b, v⟩).2 :=
  e.linear R hb |>.map_smul a v

variable (R)

lemma map_add [Trivialization.IsLinear R e]
    {b : B} (hb : b ∈ e.baseSet) (v v' : E b) :
    (e ⟨b, v + v'⟩).2 = (e ⟨b, v⟩).2 + (e ⟨b, v'⟩).2 :=
  e.linear R hb |>.map_add v v'

end

section

variable (R : Type*) {B F : Type*} {E : B → Type*}
  [NontriviallyNormedField R] [(x : B) → AddCommMonoid (E x)]
  [(x : B) → Module R (E x)] [NormedAddCommGroup F]
  [NormedSpace R F] [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  [(x : B) → TopologicalSpace (E x)]
  [FiberBundle F E] (e : Trivialization F (π F E))

lemma symm_map_add [Trivialization.IsLinear R e] {x : B}
  (f f' : F) :
    e.symm x (f + f') = e.symm x f + e.symm x f' :=
  (symmL R e x).map_add f f'

@[simp]
lemma symm_map_zero [Trivialization.IsLinear R e] {x : B} :
    e.symm x 0 = 0 :=
  (symmL R e x).map_zero

variable {R}

lemma symm_map_smul [Trivialization.IsLinear R e] {x : B} (a : R) (f : F) :
    e.symm x (a • f) = a • e.symm x f :=
  (symmL R e x).map_smul a f

end

end topological_vector_bundle

section to_trivialization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [FiberBundle F V]

variable (e : Trivialization F (π F V)) [MemTrivializationAtlas e]

lemma mdifferentiableAt
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {x : M} (hx : x ∈ e.baseSet) (v : V x) :
    MDifferentiableAt (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) e v := by
  have : ⟨x, v⟩ ∈ e.source := (coe_mem_source e).mpr hx
  have foo := e.contMDiffOn (IB := I) (n := 1) v this
  have := foo.contMDiffAt (e.open_source.mem_nhds this)
  exact this.mdifferentiableAt zero_ne_one.symm

lemma mdifferentiableAt_invFun
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
def deriv (v : TotalSpace F V) :
    TangentSpace (I.prod 𝓘(ℝ, F)) v →L[ℝ] TangentSpace I v.proj × F :=
  mfderiv (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) e v

variable (I) in
noncomputable
def derivInv (v : TotalSpace F V) :
    TangentSpace I v.proj × F →L[ℝ] TangentSpace (I.prod 𝓘(ℝ, F)) v :=
  mfderiv (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) e.invFun (e v)

@[simp]
lemma derivInv_deriv
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet) :
    (e.derivInv I v) ∘L (e.deriv I v) = .id ℝ _ := by
  have D₁ := e.mdifferentiableAt_invFun (I := I) hv (e v).2
  have D₂ : MDifferentiableAt _ _ e v := e.mdifferentiableAt (I := I) hv v.2
  have D1' := D₁
  simp only [PartialEquiv.invFun_as_coe, OpenPartialHomeomorph.coe_coe_symm] at D1'
  rw [mk_proj_snd' e hv] at D₁
  have comp := mfderiv_comp v D₁ D₂
  rw [(invFun_comp_eventuallyEq e hv).mfderiv_eq, mfderiv_id] at comp
  simp [deriv, derivInv, comp]
  rfl

@[simp]
lemma derivInv_deriv_apply
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet)
    (u : TangentSpace (I.prod 𝓘(ℝ, F)) v) :
    (e.derivInv I v (e.deriv I v u)) = u :=
  show ((e.derivInv I v) ∘L (e.deriv I v)) u = u by simp [hv]

@[simp]
lemma mfderiv_proj_fst_deriv
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet)
    (u : TangentSpace (I.prod 𝓘(ℝ, F)) v) :
    mfderiv (I.prod 𝓘(ℝ, F)) I TotalSpace.proj v u = (e.deriv I v u).1 := by
  have := e.fst_comp_eventuallyEq hv
  rw [← this.mfderiv_eq, mfderiv_comp v mdifferentiableAt_fst (e.mdifferentiableAt (I := I) hv v.2)]
  simp
  rfl -- TODO: understand why `simp` does not handle `ContinuousLinearMap.fst`

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma mfderiv_proj_derivInv_apply
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet)
    (u : TangentSpace (I.prod 𝓘(ℝ, F)) v) :
    mfderiv (I.prod 𝓘(ℝ, F)) I TotalSpace.proj v (e.derivInv I v u) = u.1 := by
  have D₁ := e.mdifferentiableAt_invFun (I := I) hv (e v).2
  rw [mk_proj_snd' e hv] at D₁
  have diff : MDifferentiableAt (I.prod 𝓘(ℝ, F)) I TotalSpace.proj v :=
    mdifferentiableAt_proj _
  have eq : e.invFun (e v) = v := by simp [((mem_source e).mpr hv)]
  rw [← eq] at diff
  have := mfderiv_comp (e v) diff D₁
  have C : (TotalSpace.proj ∘ e.invFun) =ᶠ[𝓝 (e v)] Prod.fst := by
    filter_upwards [e.baseSet_prod_univ_mem_nhds hv] with ⟨x, f⟩ ⟨hx, hf⟩
    simp [hx]
  rw [C.mfderiv_eq, eq] at this
  have := congr($this u).symm
  change mfderiv (I.prod 𝓘(ℝ, F)) I TotalSpace.proj v _ = _ at this
  -- Why all this pain??
  convert this
  ext x
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma deriv_derivInv
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet) :
    (e.deriv I v) ∘L (e.derivInv I v) = .id ℝ _ := by
  have D₁ := e.mdifferentiableAt_invFun (I := I) hv (e v).2
  rw [mk_proj_snd' e hv] at D₁
  have D₂ : MDifferentiableAt _ _ e v := e.mdifferentiableAt (I := I) hv v.2
  have : e.invFun (e v) = v := by simp [(mem_source e).mpr hv]
  rw [← this] at D₂
  have comp := mfderiv_comp (e v) D₂ D₁
  rw [(comp_invFun_eventuallyEq e hv).mfderiv_eq, mfderiv_id] at comp
  symm
  convert comp <;> rw [this]

@[simp]
lemma deriv_derivInv_apply
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet)
    (u : TangentSpace I v.proj × F) :
    e.deriv I v (e.derivInv I v u) = u :=
  show ((e.deriv I v) ∘L (e.derivInv I v)) u = u by simp [hv]

lemma bijective_deriv
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet) :
    Function.Bijective (e.deriv I v) := by
   refine Function.bijective_iff_has_inverse.mpr ?_
   use e.derivInv I v
   constructor
   all_goals { intro u; simp [hv] }

lemma mdifferentiableAt_section_of_function
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {x : M} (hx : x ∈ e.baseSet) {s : M → F}
    (hs : MDiffAt s x) :
    MDiffAt ((fun x' ↦ (⟨x', e.symm x' (s x')⟩ : TotalSpace F V))) x := by
  rw [e.mdifferentiableAt_section_iff (IB := I) _ hx]
  have := e.apply_symm_eventuallyEq hx s
  exact hs.congr_of_eventuallyEq this

noncomputable def _root_.Bundle.vert (v : TotalSpace F V) :
    Submodule ℝ (TangentSpace (I.prod 𝓘(ℝ, F)) v) :=
  (mfderiv (I.prod 𝓘(ℝ, F)) I Bundle.TotalSpace.proj v).ker

lemma comap_vert
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet) :
    Bundle.vert v = Submodule.comap (e.deriv I v).toLinearMap
      (Submodule.prod ⊥ ⊤) := by
  ext x
  have : Prod.fst ∘ e =ᶠ[𝓝 v] TotalSpace.proj := e.fst_comp_eventuallyEq hv
  unfold vert
  rw [← this.mfderiv_eq]
  have mdiffe : MDifferentiableAt (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) e v :=
    e.mdifferentiableAt hv _
  rw [mfderiv_comp v mdifferentiableAt_fst mdiffe]
  simp
  rfl

lemma mfderiv_comp_section
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {σ : Π x : M, V x} {x : M} (hσ : MDiffAt T%σ x)
    (u : TangentSpace I x) (hx : x ∈ e.baseSet) :
    letI s := fun x ↦ (e (σ x)).2
    (e.deriv I (σ x)).toLinearMap ((mfderiv% T%σ x) u) = (u, mfderiv% s x u) := by
  have mdiffe : MDifferentiableAt (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) e (σ x) :=
    e.mdifferentiableAt hx _
  have : mfderiv% (e ∘ T%σ) x = (e.deriv I (σ x)) ∘L (mfderiv% T%σ x) :=
    mfderiv_comp x mdiffe hσ
  have : mfderiv% (e ∘ T%σ) x u = e.deriv I (σ x) ((mfderiv% T%σ x) u) := by
    rw [this]
    rfl
  erw [← this]
  let s := fun x ↦ (e (σ x)).2
  change mfderiv% (e ∘ T%σ) x u = (u, mfderiv% s x u)
  rw [(e.apply_section_eventuallyEq hx _).mfderiv_eq]
  erw [mfderiv_prodMk, mfderiv_id]
  · change (ContinuousLinearMap.id _ _).prod (mfderiv% s x) u = _
    simp
  · apply mdifferentiableAt_id
  · exact (mdifferentiableAt_section_iff I e σ hx).mp hσ

@[simp]
lemma _root_.mdifferentiableAt_section_trivial_iff {s : M → F} {x : M} :
    MDiffAt (T% s) x ↔ MDiffAt s x := by
  rw [mdifferentiableAt_section I]
  simp

end to_trivialization

end Bundle.Trivialization

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
