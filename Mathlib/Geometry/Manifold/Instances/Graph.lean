/-
Copyright (c) 2026 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Topology.Constructions.Graph

/-!
# Graphs of Continuous Functions as Manifolds

This file proves that the graph of a continuous function `f : M → M'` between manifolds
inherits a manifold structure from the domain, that the inclusion of the graph into the product
`M × M'` is smooth if and only if `f` is smooth, and that the graph map `m ↦ (m, f m)` of
a `C^n` function is a `C^n` immersion.

The homeomorphism between a graph and its domain is in
`Mathlib.Topology.Constructions.Graph`.

## Main Results

* `Set.graphOn.instChartedSpace`: The graph inherits a `ChartedSpace` structure from the domain.
* `Set.graphOn.instIsManifold`: The graph is a smooth manifold when the domain is.
* `Set.graphOn.contMDiff_subtype_val_iff`: Smoothness of graph inclusion into `M × M'` is
  equivalent to smoothness of the graph function on the domain manifold.
* `Set.graphOn.isImmersion_graphMap`: The graph map `m ↦ (m, f m)` of a `C^n` function
  is a `C^n` immersion with complement `E'`, showing that the graph is an immersed submanifold
  of `M × M'`.

## Implementation Notes

The charted space structure on the graph is obtained via `Homeomorph.chartedSpace` applied to
`Set.graphOn.homeomorph`. Chart transitions factor through this homeomorphism, and since the
homeomorphism cancels in the composition, chart compatibility follows from compatibility in
the domain.

The immersion proof constructs a **straightened codomain chart** on `M × M'` by composing the
standard product chart `φ.prod ψ` with a local straightening homeomorphism on `H × H'`:
`(h, h') ↦ (h, I'.symm(I'(h') - I'(ψ(f(φ.symm h)))))`. In this chart the graph map looks like
`u ↦ (u, 0)`. The straightening belongs to the `contDiffGroupoid` because at the extend level
it equals `(a, b) ↦ (a, b - g(a))` where `g = writtenInExtChartAt` is `C^n` by `contMDiff_iff`.
-/

@[expose] public section

open Set Topology

namespace Set.graphOn

section Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {M : Type*} [TopologicalSpace M] {M' : Type*} [TopologicalSpace M']
  (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
  {n : WithTop ℕ∞}

/--
The graph of a continuous function inherits a `ChartedSpace` structure from the domain.

Given `f : M → M'` continuous on `s ⊆ M`, the graph `s.graphOn f` is charted over `H`
via the homeomorphism `Set.graphOn.homeomorph` and `Homeomorph.chartedSpace`.
-/
def instChartedSpace {s : Set M} {f : M → M'} (hf : ContinuousOn f s) [ChartedSpace H s] :
    ChartedSpace H (s.graphOn f) :=
  (homeomorph hf).chartedSpace

omit [NormedSpace 𝕜 E'] in
/--
The graph of a continuous function on a manifold is itself a manifold.

This follows from the fact that the graph is homeomorphic to the domain,
so chart transitions factor through the homeomorphism which cancels.
-/
theorem instIsManifold {s : Set M} {f : M → M'} (hf : ContinuousOn f s)
    [ChartedSpace H s] [IsManifold I n s] :
    let _ := instChartedSpace (H := H) hf
    IsManifold I n (s.graphOn f) := by
  letI : ChartedSpace H (s.graphOn f) := instChartedSpace (H := H) hf
  have compat : ∀ {e e' : OpenPartialHomeomorph (s.graphOn f) H},
      e ∈ atlas H (s.graphOn f) →
        e' ∈ atlas H (s.graphOn f) → e.symm.trans e' ∈ contDiffGroupoid n I := by
    rintro e e' ⟨e0, he0_mem, rfl⟩ ⟨e0', he0'_mem, rfl⟩
    have h_grp := (contDiffGroupoid n I).compatible he0_mem he0'_mem
    apply (contDiffGroupoid n I).mem_of_eqOnSource h_grp
    refine ⟨?_, ?_⟩
    · -- source equality
      ext x
      simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
                 OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
                 univ_inter]
      constructor <;> rintro ⟨hx1, hx2⟩
      · exact ⟨hx1.1, hx2⟩
      · exact ⟨⟨hx1, trivial⟩, hx2⟩
    · -- function equality on source
      intro x hx; simp
  haveI : HasGroupoid (H := H) (M := s.graphOn f) (contDiffGroupoid n I) := ⟨compat⟩
  exact IsManifold.mk' I n (s.graphOn f)

omit [NormedSpace 𝕜 E'] in
private theorem homeomorph_liftPropOn {s : Set M} {f : M → M'} (hf : ContinuousOn f s)
    [ChartedSpace H s] [IsManifold I n s] :
    letI := instChartedSpace (H := H) hf
    ChartedSpace.LiftPropOn
      (contDiffGroupoid n I).IsLocalStructomorphWithinAt
      (homeomorph hf).toOpenPartialHomeomorph
      (homeomorph hf).toOpenPartialHomeomorph.source := by
  letI : ChartedSpace H (s.graphOn f) := instChartedSpace (H := H) hf
  letI : IsManifold I n (s.graphOn f) := instIsManifold I hf
  let h := (homeomorph hf).toOpenPartialHomeomorph
  change ChartedSpace.LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt h h.source
  intro x hx
  refine ⟨h.continuousAt hx |>.continuousWithinAt, fun _ ↦ ?_⟩
  let e : OpenPartialHomeomorph H H := (chartAt H x).symm.trans (h.trans (chartAt H (h x)))
  refine ⟨e, ?_, (by intro y hy; simp [e, h] at hy ⊢), by simp [e, h]⟩
  exact (contDiffGroupoid n I).compatible (chart_mem_atlas H x) (by
    dsimp [h, e]
    exact ⟨chartAt H (homeomorph hf x), chart_mem_atlas H (homeomorph hf x), rfl⟩)

omit [NormedSpace 𝕜 E'] in
/-- Smoothness of the graph-domain homeomorphism for the induced manifold structure on the
graph. -/
theorem contMDiff_homeomorph_toFun {s : Set M} {f : M → M'} (hf : ContinuousOn f s)
    [ChartedSpace H s] [IsManifold I n s] :
    letI := instChartedSpace (H := H) hf
    ContMDiff I I n (homeomorph hf) := by
  letI : ChartedSpace H (s.graphOn f) := instChartedSpace (H := H) hf
  letI : IsManifold I n (s.graphOn f) := instIsManifold I hf
  let h := (homeomorph hf).toOpenPartialHomeomorph
  simpa [h, contMDiffOn_univ] using
    ((isLocalStructomorphOn_contDiffGroupoid_iff h).1 (homeomorph_liftPropOn I hf)).1

omit [NormedSpace 𝕜 E'] in
/-- Smoothness of the inverse graph-domain homeomorphism for the induced manifold structure on the
graph. -/
theorem contMDiff_homeomorph_invFun {s : Set M} {f : M → M'} (hf : ContinuousOn f s)
    [ChartedSpace H s] [IsManifold I n s] :
    letI := instChartedSpace (H := H) hf
    ContMDiff I I n (homeomorph hf).symm := by
  letI : ChartedSpace H (s.graphOn f) := instChartedSpace (H := H) hf
  letI : IsManifold I n (s.graphOn f) := instIsManifold I hf
  let h := (homeomorph hf).toOpenPartialHomeomorph
  simpa [h, contMDiffOn_univ] using
    ((isLocalStructomorphOn_contDiffGroupoid_iff h).1 (homeomorph_liftPropOn I hf)).2

/--
If `s` is a `C^n` manifold and `m ≤ n`, then the inclusion map from the graph into the ambient
product space `M × M'` is `C^m` if and only if the graph function is `C^m` on `s`.

This characterizes when the graph, with the manifold structure inherited from the domain,
is a `C^m` embedded submanifold of the product space `M × M'`, assuming
`Subtype.val : s → M` is `C^m`.
-/
theorem contMDiff_subtype_val_iff {s : Set M} {f : M → M'} (hf : ContinuousOn f s)
    {m n : WithTop ℕ∞} [ChartedSpace H M] [ChartedSpace H' M']
    [ChartedSpace H s] [IsManifold I n s] (hmn : m ≤ n)
    (hval : ContMDiff I I m (Subtype.val : s → M)) :
    let _ := instChartedSpace (H := H) hf
    ContMDiff I (I.prod I') m
      (Subtype.val : s.graphOn f → M × M') ↔
    ContMDiff I I' m (fun x : s ↦ f x) := by
  letI : IsManifold I m s := IsManifold.of_le hmn
  letI : ChartedSpace H (s.graphOn f) := instChartedSpace (H := H) hf
  -- The inclusion factors: Subtype.val = (fun x ↦ (x, f x)) ∘ homeomorph
  have factorization : (Subtype.val : s.graphOn f → M × M') =
      (fun x : s ↦ (x.val, f x.val)) ∘ (homeomorph hf) := by
    ext z <;> rcases z with ⟨⟨x, y⟩, hxy⟩ <;>
      simp [Function.comp_apply, (mem_graphOn.mp hxy).2]
  rw [factorization]
  constructor
  · intro h
    have hcomp := h.comp (contMDiff_homeomorph_invFun I hf)
    simp only [Function.comp_assoc, Homeomorph.self_comp_symm, Function.comp_id] at hcomp
    rw [contMDiff_prod_iff] at hcomp
    simpa [Function.comp_apply] using hcomp.2
  · intro hf_smooth
    apply ContMDiff.comp _ (contMDiff_homeomorph_toFun I hf)
    rw [contMDiff_prod_iff]
    constructor
    · simpa [Function.comp_apply] using hval
    · simpa [Function.comp_apply] using hf_smooth

end Manifold

/-! ## Graph Immersion -/

section Immersion

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
    {n : WithTop ℕ∞}

open Manifold

/-! ### Helper lemmas -/

/-- Two `OpenPartialHomeomorph`s with equal underlying `PartialEquiv`s are `EqOnSource`. -/
private lemma eqOnSource_of_eq_toPartialEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (a b : OpenPartialHomeomorph X Y) (h : a.toPartialEquiv = b.toPartialEquiv) :
    a.EqOnSource b :=
  ⟨congr_arg PartialEquiv.source h, fun _ _ ↦ congr_fun (congr_arg PartialEquiv.toFun h) _⟩

/-! ### Local straightening -/

/-- Local straightening `OpenPartialHomeomorph` on `H × H'`. Given charts `φ` on `M` and `ψ` on
`M'`, and a continuous function `f : M → M'`, this maps `(h, h') ↦ (h, I'.symm(I'(h') -
I'(ψ(f(φ.symm h)))))` on the open set `W ×ˢ univ` where `W = φ.target ∩ φ.symm ⁻¹' (f ⁻¹'
ψ.source)`. The inverse adds back `I'(ψ(f(φ.symm h)))`. This straightening makes graph points
`(φ m, ψ(f m))` map to `(φ m, I'.symm 0)`, i.e., the graph function is "subtracted off". -/
private noncomputable def localStraighten [I'.Boundaryless]
    (φ : OpenPartialHomeomorph M H) (ψ : OpenPartialHomeomorph M' H')
    (f : M → M') (hf_cont : Continuous f) :
    OpenPartialHomeomorph (ModelProd H H') (ModelProd H H') where
  toPartialEquiv := {
    toFun := fun ⟨h, h'⟩ ↦ (h, I'.symm (I' h' - I' (ψ (f (φ.symm h)))))
    invFun := fun ⟨h, h'⟩ ↦ (h, I'.symm (I' h' + I' (ψ (f (φ.symm h)))))
    source := (φ.target ∩ φ.symm ⁻¹' (f ⁻¹' ψ.source)) ×ˢ univ
    target := (φ.target ∩ φ.symm ⁻¹' (f ⁻¹' ψ.source)) ×ˢ univ
    map_source' := fun ⟨_, _⟩ ⟨hw, _⟩ ↦ ⟨hw, trivial⟩
    map_target' := fun ⟨_, _⟩ ⟨hw, _⟩ ↦ ⟨hw, trivial⟩
    left_inv' := fun ⟨_, h'⟩ _ ↦ Prod.ext rfl (by
      simp only
      rw [I'.right_inv (by rw [I'.range_eq_univ]; trivial), sub_add_cancel, I'.left_inv h'])
    right_inv' := fun ⟨_, h'⟩ _ ↦ Prod.ext rfl (by
      simp only
      rw [I'.right_inv (by rw [I'.range_eq_univ]; trivial), add_sub_cancel_right, I'.left_inv h'])
  }
  open_source :=
    IsOpen.prod (φ.isOpen_inter_preimage_symm (hf_cont.isOpen_preimage _ ψ.open_source)) isOpen_univ
  open_target :=
    IsOpen.prod (φ.isOpen_inter_preimage_symm (hf_cont.isOpen_preimage _ ψ.open_source)) isOpen_univ
  continuousOn_toFun := ContinuousOn.prodMk continuousOn_fst
    (I'.continuous_symm.comp_continuousOn
      (.sub (I'.continuous.comp_continuousOn continuousOn_snd)
        (I'.continuous.comp_continuousOn (ψ.continuousOn.comp (hf_cont.comp_continuousOn
          (φ.continuousOn_symm.comp continuousOn_fst (fun ⟨_, _⟩ ⟨⟨hh, _⟩, _⟩ ↦ hh)))
          (fun ⟨_, _⟩ ⟨⟨_, hf'⟩, _⟩ ↦ hf')))))
  continuousOn_invFun := ContinuousOn.prodMk continuousOn_fst
    (I'.continuous_symm.comp_continuousOn
      (.add (I'.continuous.comp_continuousOn continuousOn_snd)
        (I'.continuous.comp_continuousOn (ψ.continuousOn.comp (hf_cont.comp_continuousOn
          (φ.continuousOn_symm.comp continuousOn_fst (fun ⟨_, _⟩ ⟨⟨hh, _⟩, _⟩ ↦ hh)))
          (fun ⟨_, _⟩ ⟨⟨_, hf'⟩, _⟩ ↦ hf')))))

/-! ### Groupoid membership -/

/-- The domain of the straightened codomain chart equals `D ×ˢ univ`. -/
private lemma localStraighten_domain_eq (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    [I.Boundaryless] [I'.Boundaryless]
    {f : M → M'} (hf_cont : Continuous f) (m₀ : M) :
    let str := localStraighten (I' := I') (chartAt H m₀) (chartAt H' (f m₀)) f hf_cont
    let D := (extChartAt I m₀).target ∩
      (extChartAt I m₀).symm ⁻¹' (f ⁻¹' (extChartAt I' (f m₀)).source)
    ((↑(I.prod I').symm ⁻¹' str.source) ∩ range ↑(I.prod I')) = D ×ˢ univ := by
  intro str D
  apply Set.ext
  rintro ⟨a, snd⟩
  have h_r_prod : (a, snd) ∈ range (I.prod I') := by
    rw [ModelWithCorners.range_prod]; exact ⟨I.mem_range a, I'.mem_range snd⟩
  have h_f_eq : (chartAt H m₀).symm (I.symm a) = (extChartAt I m₀).symm a := rfl
  have h_symm : (↑(I.prod I').symm : E × E' → H × H') (a, snd) = (I.symm a, I'.symm snd) := rfl
  have h_str_source : str.source = (chartAt H m₀).target ×ˢ univ ∩
      ((chartAt H m₀).symm ∘ Prod.fst) ⁻¹' (f ⁻¹' (chartAt H' (f m₀)).source) := by
    ext ⟨x, y⟩
    simp only [str, localStraighten, mem_inter_iff, mem_preimage]
    exact ⟨fun ⟨⟨hx, hf⟩, hy⟩ ↦ ⟨⟨hx, hy⟩, hf⟩, fun ⟨⟨hx, hy⟩, hf⟩ ↦ ⟨⟨hx, hf⟩, hy⟩⟩
  simp only [D, h_str_source, extChartAt_target, extChartAt_source, h_symm,
    mem_inter_iff, mem_prod, mem_preimage]
  dsimp only [Function.comp_apply, Prod.fst]
  constructor
  · intro ⟨⟨⟨h_tgt, _⟩, h_pre⟩, h_rng⟩
    exact ⟨⟨⟨h_tgt, I.mem_range a⟩, by rw [← h_f_eq]; exact h_pre⟩, trivial⟩
  · intro ⟨⟨⟨h_tgt, _⟩, h_pre⟩, _⟩
    exact ⟨⟨⟨h_tgt, trivial⟩, by rw [h_f_eq]; exact h_pre⟩, h_r_prod⟩

/-- Coordinate expression for the forward local straightening map. -/
private lemma localStraighten_extend_toFun
    (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    [I.Boundaryless] [I'.Boundaryless]
    {f : M → M'} (hf_cont : Continuous f) (m₀ : M) :
    let str := localStraighten (I' := I') (chartAt H m₀) (chartAt H' (f m₀)) f hf_cont
    let g := extChartAt I' (f m₀) ∘ f ∘ (extChartAt I m₀).symm
    let D := (extChartAt I m₀).target ∩
      (extChartAt I m₀).symm ⁻¹' (f ⁻¹' (extChartAt I' (f m₀)).source)
    ∀ p : E × E', p ∈ D ×ˢ (univ : Set E') →
      (↑(I.prod I') ∘ ↑str ∘ ↑(I.prod I').symm) p = (p.1, p.2 - g p.1) := by
  intro str g D ⟨a, snd⟩ _
  have h_symm : (↑(I.prod I').symm : E × E' → H × H') (a, snd) = (I.symm a, I'.symm snd) := rfl
  rw [Function.comp_apply, Function.comp_apply, h_symm]
  dsimp [g, str, localStraighten, ModelWithCorners.prod_apply]
  have h_g_eq : I' (chartAt H' (f m₀) (f ((chartAt H m₀).symm (I.symm a)))) = g a := rfl
  rw [h_g_eq]
  rw [I'.right_inv (I'.mem_range snd)]
  exact Prod.ext (I.right_inv (I.mem_range a)) (I'.right_inv (I'.mem_range _))

/-- Coordinate expression for the inverse local straightening map. -/
private lemma localStraighten_extend_invFun
    (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    [I.Boundaryless] [I'.Boundaryless]
    {f : M → M'} (hf_cont : Continuous f) (m₀ : M) :
    let str := localStraighten (I' := I') (chartAt H m₀) (chartAt H' (f m₀)) f hf_cont
    let g := extChartAt I' (f m₀) ∘ f ∘ (extChartAt I m₀).symm
    let D := (extChartAt I m₀).target ∩
      (extChartAt I m₀).symm ⁻¹' (f ⁻¹' (extChartAt I' (f m₀)).source)
    ∀ p : E × E', p ∈ D ×ˢ (univ : Set E') →
      (↑(I.prod I') ∘ ↑str.symm ∘ ↑(I.prod I').symm) p = (p.1, p.2 + g p.1) := by
  intro str g D ⟨a, snd⟩ _
  dsimp [g, str, localStraighten, ModelWithCorners.prod_apply]
  have h_g_eq : I' (chartAt H' (f m₀) (f ((chartAt H m₀).symm (I.symm a)))) = g a := rfl
  rw [h_g_eq]
  rw [I'.right_inv (I'.mem_range snd)]
  exact Prod.ext (I.right_inv (I.mem_range a)) (I'.right_inv (I'.mem_range _))

/-- The local straightening belongs to the `contDiffGroupoid`. At the `E × E'` extend level,
the straightening is `(a, b) ↦ (a, b - g(a))` where `g = writtenInExtChartAt`, which is `C^n`
by `contMDiff_iff`. -/
private lemma localStraighten_mem_contDiffGroupoid
    [I.Boundaryless] [I'.Boundaryless] [IsManifold I n M] [IsManifold I' n M']
    {f : M → M'} (hf : ContMDiff I I' n f) (m₀ : M) :
    localStraighten (I' := I') (chartAt H m₀) (chartAt H' (f m₀)) f hf.continuous ∈
      contDiffGroupoid n (I.prod I') := by
  set str := localStraighten (I' := I') (chartAt H m₀) (chartAt H' (f m₀)) f hf.continuous
  set g := extChartAt I' (f m₀) ∘ f ∘ (extChartAt I m₀).symm
  set D := (extChartAt I m₀).target ∩
    (extChartAt I m₀).symm ⁻¹' (f ⁻¹' (extChartAt I' (f m₀)).source)
  have hg : ContDiffOn 𝕜 n g D := (contMDiff_iff.mp hf).2 m₀ (f m₀)
  have h_domain_eq := localStraighten_domain_eq I I' hf.continuous m₀
  apply mem_groupoid_of_pregroupoid.mpr
  refine ⟨?_, ?_⟩
  · change ContDiffOn 𝕜 n (↑(I.prod I') ∘ ↑str ∘ ↑(I.prod I').symm) _
    rw [h_domain_eq]
    apply (ContDiffOn.prodMk contDiff_fst.contDiffOn (.sub contDiff_snd.contDiffOn
      (hg.comp contDiff_fst.contDiffOn (fun ⟨_, _⟩ ⟨ha, _⟩ ↦ ha)))).congr
    exact localStraighten_extend_toFun I I' hf.continuous m₀
  · change ContDiffOn 𝕜 n (↑(I.prod I') ∘ ↑str.symm ∘ ↑(I.prod I').symm) _
    have h_target_eq_source : str.target = str.source := rfl
    rw [h_target_eq_source, h_domain_eq]
    apply (ContDiffOn.prodMk contDiff_fst.contDiffOn (.add contDiff_snd.contDiffOn
      (hg.comp contDiff_fst.contDiffOn (fun ⟨_, _⟩ ⟨ha, _⟩ ↦ ha)))).congr
    exact localStraighten_extend_invFun I I' hf.continuous m₀

/-! ### Maximal atlas membership -/

/-- The straightened codomain chart (product chart composed with local straightening) is in the
maximal atlas of `M × M'`. Uses `PartialEquiv.trans_assoc` to factor the chart transitions. -/
private lemma straightCodChart_mem_maximalAtlas [I.Boundaryless] [I'.Boundaryless]
    [IsManifold I n M] [IsManifold I' n M'] {f : M → M'} (hf : ContMDiff I I' n f) (m₀ : M) :
    ((chartAt H m₀).prod (chartAt H' (f m₀))).trans
      (localStraighten (I' := I') (chartAt H m₀) (chartAt H' (f m₀)) f hf.continuous) ∈
      IsManifold.maximalAtlas (I.prod I') n (M × M') := by
  rw [IsManifold.mem_maximalAtlas_iff, mem_maximalAtlas_iff]
  intro e' he'
  let G := contDiffGroupoid n (I.prod I')
  let str := localStraighten (I' := I') (chartAt H m₀) (chartAt H' (f m₀)) f hf.continuous
  have h_str : str ∈ G := localStraighten_mem_contDiffGroupoid hf m₀
  have h_prodC : (chartAt H m₀).prod (chartAt H' (f m₀)) ∈ atlas (ModelProd H H') (M × M') :=
    chart_mem_atlas (ModelProd H H') (m₀, f m₀)
  exact ⟨G.mem_of_eqOnSource (G.trans' str.symm _ (G.symm' str h_str) (G.compatible h_prodC he'))
          (eqOnSource_of_eq_toPartialEquiv _ _ (by
            simp only [OpenPartialHomeomorph.trans_toPartialEquiv,
              OpenPartialHomeomorph.symm_toPartialEquiv]
            rw [PartialEquiv.trans_symm_eq_symm_trans_symm, PartialEquiv.trans_assoc])),
         G.mem_of_eqOnSource (G.trans' _ str (G.compatible he' h_prodC) h_str)
          (eqOnSource_of_eq_toPartialEquiv _ _ (by
            simp only [OpenPartialHomeomorph.trans_toPartialEquiv,
              OpenPartialHomeomorph.symm_toPartialEquiv]
            rw [PartialEquiv.trans_assoc]))⟩

/-! ### Main theorem -/

/-- The graph map `m ↦ (m, f m) : M → M × M'` of a `C^n` function is a `C^n` immersion,
showing that the graph of `f` is an immersed submanifold of `M × M'`.

The proof constructs a straightened codomain chart on `M × M'` by composing the standard
product chart with a local straightening homeomorphism `(h, h') ↦ (h, I'.symm(I'(h') -
I'(ψ(f(φ.symm h)))))`. In this straightened chart, the graph map looks like `u ↦ (u, 0)`,
which is the defining property of an immersion with complement `E'`.

TODO: To derive that the inclusion `Subtype.val : s.graphOn f → M × M'` is an immersion (for `s`
with a compatible charted space), compose with the graph-domain homeomorphism once
`IsImmersion.comp` is available. -/
theorem isImmersion_graphMap {f : M → M'}
    [I.Boundaryless] [I'.Boundaryless]
    [IsManifold I n M] [IsManifold I' n M']
    (hf : ContMDiff I I' n f) :
    IsImmersion I (I.prod I') n (fun m ↦ (m, f m)) := by
  refine (show IsImmersionOfComplement E' I (I.prod I') n (fun m ↦ (m, f m)) from
    fun m₀ => ?_).isImmersion
  set φ := chartAt H m₀
  set ψ := chartAt H' (f m₀)
  set str := localStraighten (I' := I') φ ψ f hf.continuous
  set codChart := (φ.prod ψ).trans str
  -- Use the restricted domain chart so its extend target maps into the codChart source
  set domChart := φ.restr (f ⁻¹' ψ.source)
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    (ContinuousAt.prodMk continuous_id.continuousAt hf.continuous.continuousAt)
    (ContinuousLinearEquiv.refl 𝕜 (E × E'))
    domChart (codChart.symm.symm)
    (show m₀ ∈ domChart.source from by
      simp only [domChart, OpenPartialHomeomorph.restr_source, mem_inter_iff]
      refine ⟨mem_chart_source H m₀, ?_⟩
      rw [(hf.continuous.isOpen_preimage _ ψ.open_source).interior_eq]
      exact mem_chart_source H' (f m₀))
    (show (m₀, f m₀) ∈ codChart.source from by
      rw [OpenPartialHomeomorph.trans_source]
      refine ⟨⟨mem_chart_source H m₀, mem_chart_source H' (f m₀)⟩, ?_⟩
      simp only [str, localStraighten, mem_preimage, OpenPartialHomeomorph.prod_apply, mem_prod_eq,
        mem_inter_iff, mem_univ, and_true]
      exact ⟨φ.map_source (mem_chart_source H m₀),
             by rw [φ.left_inv (mem_chart_source H m₀)]; exact mem_chart_source H' (f m₀)⟩)
    (restr_mem_maximalAtlas (contDiffGroupoid n I) (IsManifold.chart_mem_maximalAtlas m₀)
      (hf.continuous.isOpen_preimage _ ψ.open_source))
    (straightCodChart_mem_maximalAtlas hf m₀)
  intro u hu
  have hu_W : I.symm u ∈ φ.target ∩ φ.symm ⁻¹' (f ⁻¹' ψ.source) := by
    obtain ⟨hu_I, hu_dom_tgt⟩ := hu
    obtain ⟨hu_tgt, hu_pre⟩ := hu_dom_tgt
    have hu_pre' : I.symm u ∈ φ.symm ⁻¹' (f ⁻¹' ψ.source) := by
      change I.symm u ∈ φ.symm ⁻¹' (interior (f ⁻¹' ψ.source)) at hu_pre
      rw [(hf.continuous.isOpen_preimage _ ψ.open_source).interior_eq] at hu_pre
      exact hu_pre
    exact ⟨hu_tgt, hu_pre'⟩
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm]
  dsimp [domChart, codChart, str, localStraighten, ModelWithCorners.prod_apply]
  exact Prod.ext (by rw [φ.right_inv hu_W.1, I.right_inv (I.mem_range _)])
         (by rw [φ.right_inv hu_W.1, sub_self]; exact I'.right_inv (I'.mem_range _))

end Immersion

end Set.graphOn
