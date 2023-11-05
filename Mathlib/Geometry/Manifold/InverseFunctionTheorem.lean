/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Analysis.Calculus.Inverse
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Tactic.RewriteSearch

/-! # The inverse function theorem for manifolds

TODO: write a docstring when I'm done

**TODO**
* allow M and N to be modelled on different normed spaces (even if they must be isomorphic)
* don't assume M and N are smooth: the groupoid containing the C^1 groupoid suffices
* handle models with corners in my "charts are structomorphs" argument

* extend the arguments to manifolds with boundary, for instance like this:
  - at an interior point, we can choose U and V to be open - so the argument for the boundaryless case applies
  - f being C¹ at a boundary point x, means f has a C¹ extension to an open neighbourhood of range I\subset E:
  work with that like in the previous bullet point
  - to phrase these above two bullet points, mathlib needs to gain
  the concepts of interior and boundary points, and that the interior is an open subset
-/

open Function Manifold Set TopologicalSpace Topology

-- Let M and N be manifolds over (E,H) and (E',H'), respectively.
-- We don't assume smoothness, but allow any structure groupoid (which contains C¹ maps).
variable {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
   [TopologicalSpace N] [ChartedSpace H N]
  -- TODO: relax these conditions!!
  (I : ModelWithCorners ℝ E H) [SmoothManifoldWithCorners I M]
  (J : ModelWithCorners ℝ E' H) [SmoothManifoldWithCorners J N]
  -- these lines are what I actually want
  --(I : ModelWithCorners ℝ E H) (G : StructureGroupoid H) [HasGroupoid M G]
  -- (J : ModelWithCorners ℝ E' H') (G' : StructureGroupoid H') [HasGroupoid N G']


-- inconsistent: HasFDerivAt f f' x vs HasMFDerivAt f x f'

/-! Pre-requisite results: the differential of a function is surjective/injective/a linear iso
  iff the differential of its coordinate representation (w.r.t. any charts) is.
  Already proven on a branch; just waiting for the most conceptual proof.

  Let `f: M → N` be `C^1` near `x`. For (extended) charts `φ` and `ψ` around `x` and `f x`,
  respectively, denote `f_loc := ψ ∘ f ∘ φ⁻¹`. We show that the differential `df_x` of `f`
  is injective, surjective resp. a linear isomorphism iff `(df_loc)_(φ x)` is. -/
section Prerequisites
variable {f : M → N} {x : M}

-- xxx: for unextended charts, this doesn't make sense unless H is also a normed space
variable (hf : ContMDiffAt I J 1 f x)
  {e : LocalHomeomorph M H} (he : e ∈ atlas H M)
  {e' : LocalHomeomorph N H} (he' : e' ∈ atlas H N)

/-- `df_x` is a linear isomorphism iff `(df_loc)_(φ x)` is a linear isomorphism.-/
-- part 1: isomorphism
def differential_in_charts_iso (dfx : TangentSpace I x ≃L[ℝ] TangentSpace J (f x))
    (hx : HasMFDerivAt I J f x dfx) : E ≃L[ℝ] E' := sorry

variable (e e') in
-- part 2: this isomorphism is really the fderiv
lemma differential_in_charts_iso_coe (dfx : TangentSpace I x ≃L[ℝ] TangentSpace J (f x))
    (hx : HasMFDerivAt I J f x dfx) : (differential_in_charts_iso I J dfx hx).toFun =
      fderiv ℝ ((e'.extend J) ∘ f ∘ (e.extend I).symm) ((e.extend I) x) := sorry

-- FIXME: add converse version, differential_iso_of_in_charts plus `coe` version
-- should follow easily from this one

/-- `df_x` is injective iff `(df_loc)_(φ x)` is injective.-/
lemma differential_injective_iff_in_charts : Injective (mfderiv I J f x) ↔ Injective
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') ((e'.extend J) ∘ f ∘ (e.extend I).symm) ((e.extend I) x)) := sorry

/-- `df_x` is surjective iff `(df_loc)_(φ x)` is sujective.-/
lemma diff_surjective_iff_in_charts_extend : Surjective (mfderiv I J f x) ↔ Surjective
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') ((e'.extend J) ∘ f ∘ (e.extend I).symm) ((e.extend I) x)) := sorry
end Prerequisites

-- Experimenting with another design towards local diffeomorphisms.
section LocalDiffeos
variable {G : StructureGroupoid H}

/-- A structomorph induces a map in the structure groupoid. -/
lemma Structomorph.toFun_mem_groupoid (h : Structomorph G H H) : h.toLocalHomeomorph ∈ G := by
  -- FIXME: is there a more elegant way to prove this?
  have : ∀ (c c' : LocalHomeomorph H H), c ∈ atlas H H → c' ∈ atlas H H → h.toLocalHomeomorph ∈ G := by
    intro c c' hc hc'
    have : c.symm ≫ₕ h.toHomeomorph.toLocalHomeomorph ≫ₕ c' = h.toLocalHomeomorph := by
      rw [chartedSpaceSelf_atlas.mp hc, chartedSpaceSelf_atlas.mp hc']
      simp
    exact this ▸ (h.mem_groupoid c c' hc hc')
  apply this (c := LocalHomeomorph.refl H) (c' := LocalHomeomorph.refl H) rfl rfl

/-- If `h` is a `Structomorph` on `H`,it is also a local structomorphism at every point. -/
lemma Structomorph.toLocalStructomorphAt (h : Structomorph G H H) {x : H} :
    G.IsLocalStructomorphWithinAt h.toFun univ x :=
  fun y ↦ ⟨h.toLocalHomeomorph, h.toFun_mem_groupoid, eqOn_refl h.toFun _, y⟩

/-- If `f : H → H` is a local structomorphism at each `x`, it induces a structomorphism on `H`. -/
noncomputable def Structomorph.of_localStructomorphs {f : H → H}
    (hf : ∀ x, ∃ s : Set H, x ∈ s ∧ G.IsLocalStructomorphWithinAt f s x) : Structomorph G H H := by
  -- for each x, choose an s and a local homeomorph x
  choose s hs  using hf
  choose hxs e he using hs
  -- Choose the inverse by taking the point-wise inverse under our construction.
  let g : H → H := fun x ↦ (e x (hxs x)) x
  -- Now: show all the boilerplate to argue this defines an inverse.
  have hf : Continuous f := by
    have : ∀ x, ContinuousAt f x := by
      intro x
      sorry
    exact continuous_iff_continuousAt.mpr this
  have hg : Continuous g := sorry
  let h : Homeomorph H H := {
    toFun := f
    invFun := g
    left_inv := sorry
    right_inv := sorry
    continuous_toFun := hf
    continuous_invFun := hg
  }
  exact {
    h with
    mem_groupoid := sorry
  }
end LocalDiffeos

/-! Inverse function theorem for manifolds. -/
section IFT
namespace ContMDiffAt
variable {f : M → N} {x : M} {f' : TangentSpace I x ≃L[ℝ] TangentSpace J (f x)} [CompleteSpace E]

/-- Given a `ContMDiff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible
derivative at `x`, returns a `LocalHomeomorph` with `to_fun = f` and `x ∈ source`. -/
theorem toLocalHomeomorph {n : ℕ∞} [I.Boundaryless] [J.Boundaryless]
    (hf : ContMDiffAt I J n f x) (hf' : HasMFDerivAt I J f x f') (hn : 1 ≤ n) : LocalHomeomorph M N := by
  -- This follows from the analogous statement on charts.
  -- Consider the charts φ and ψ on `M` resp. `N` around `x` and `f x`, respectively,
  -- and the local coordinate representation `f_loc` of `f` w.r.t. these charts.
  let φ := extChartAt I x
  let ψ := extChartAt J (f x)
  let f_loc := ψ ∘ f ∘ φ.invFun
  -- `f_loc` maps `U` to `V`; these are open sets (at least morally).
  let U := φ '' (φ.source ∩ f ⁻¹' ψ.source)
  let V := ψ '' (f '' φ.source ∩ ψ.source)
  have : MapsTo f_loc U V := by
    intro x hx
    rcases hx with ⟨x', hx', hx'x⟩
    have : φ.invFun (φ x') = x' := φ.left_inv (mem_of_mem_inter_left hx')
    have : f_loc x = (ψ ∘ f) x' := calc f_loc x
      _ = (ψ ∘ f ∘ φ.invFun) (φ x') := by rw [hx'x]
      _ = (ψ ∘ f) (φ.invFun (φ x')) := rfl
      _ = (ψ ∘ f) x' := by rw [this]
    --have : f x' ∈ (f '' φ.source ∩ ψ.source) := by aesop
    aesop
  -- openness of U and V were obvious for just charts; it's not as obvious here
  -- for instance, a priori we only know `f` is continuous *at x*, not *near* `x`
  -- XXX: I'll see if we need this
  -- have : IsOpen U := sorry
  -- have : IsOpen V := sorry
  -- have : U ⊆ φ.target := sorry
  -- have : V ⊆ ψ.target := sorry

  -- By definition, `f_loc` is `C^1` at `x' := φ x`. (At least, if `M` is boundaryless.)
  set x' := φ x
  have : ContDiffWithinAt ℝ n f_loc (range I) x' := ((contMDiffAt_iff I J).mp hf).2
  have : ContDiffAt ℝ n f_loc (φ x) := by rw [I.range_eq_univ] at this; exact this
  -- As shown before, `(df_loc)_φ x is also a linear isomorphism.
  have df_loc : E ≃L[ℝ] E' := differential_in_charts_iso I J f' hf'
  let temp := differential_in_charts_iso_coe I J (chartAt H x) (chartAt H (f x)) f' hf'
  -- this should be obvious/easy - I did this already on a different branch
  have hdf'loc : HasFDerivAt (𝕜 := ℝ) f_loc df_loc x' := sorry

  -- By the Inverse Function Theorem on normed spaces, there's a local homeomorphism
  -- to `toFun = f_loc` and `x' ∈ source`.
  let f_loc' := this.toLocalHomeomorph f_loc hdf'loc hn
  -- Composing with the inverse charts yields the local homeomorphism we want.
  -- (If M and N are boundaryless, that is: otherwise, we'd have to work harder.)
  let φ' := (chartAt H x).trans I.toHomeomorph.toLocalHomeomorph
  let ψ' := (chartAt H (f x)).trans J.toHomeomorph.toLocalHomeomorph
  have : φ'.toFun = φ.toFun := rfl
  have : ψ'.toFun = ψ.toFun := rfl
  exact φ' ≫ₕ f_loc' ≫ₕ ψ'.symm

-- TODO: sanity-check that I got the directions right?
-- @[simp]
-- theorem toLocalHomeomorph_coe {n : ℕ∞} [I.Boundaryless] [J.Boundaryless]
--     (hf : ContMDiffAt I J n f x) (hf' : HasMFDerivAt I J f x f') (hn : 1 ≤ n) :
--     (hf.toLocalHomeomorph I J hf' hn : M → N) = f :=
--   rfl
end ContMDiffAt

-- do I want counterparts of mem_toLocalHomeomorph_source, image_mem_toLocalHomeomorph_target also?

-- step 2, separately in each category
-- if f is C^k, analytic, etc. and df_x is invertible, then f_loc is a local structo within thingy
-- StructureGroupoid.IsLocalStructomorphWithinAt
-- this has been shown for C^n already, just quote it!

-- step 3, general: if f_loc is a `IsLocalStructomorphWithinAt`, so is the local inverse
-- (general nonsense, structure groupoid is closed under inverses)

/-- If f : H → H is a local structomorphism at `x` relative to `s` and has a local inverse `g`,
  then `g` is a local structomorphism at `f x` relative to `f '' x`. -/
-- no differentiability here! wouldn't make sense either :-)
lemma StructureGroupoid.localInverse_isLocalStructomorphWithin {f : H → H} (s : Set H) (x : H)
    (G : StructureGroupoid H) (hf : G.IsLocalStructomorphWithinAt f s x)
    -- TODO: changing to f '' s to s should fail somewhere...!
    {g : H → H} (hinv : InvOn g f s (f '' s)) (hgx : g (f x) = x) :
    G.IsLocalStructomorphWithinAt g (f '' s) (f x) := by
  intro hfx
  -- `hgx` is required so this is true: need to exclude the case x ∉ s, but f x ∈ f'' s.
  have : x ∈ s := by
    rcases hfx with ⟨x', hx's, hx'y⟩
    have : x = x' := by rw [(hinv.1 hx's).symm, hx'y, hgx]
    exact mem_of_eq_of_mem this hx's
  rcases hf this with ⟨e, heg, heq, hxsource⟩
  refine ⟨e.symm, G.symm heg, ?_, ?_⟩
  · -- g = e.symm on f '' s ∩ e.symm.source
    show EqOn g e.symm (f '' s ∩ e.symm.source)
    -- heq tells us: EqOn f (↑e.toLocalEquiv) (s ∩ e.source)
    -- now, need to use both-sided inverses; shouldn't be hard, but didn't think yet
    sorry
  · -- show f x ∈ e.symm.source
    rw [LocalHomeomorph.symm_source, ← e.image_source_eq_target, heq (mem_inter this hxsource)]
    apply mem_image_of_mem e hxsource

-- step 4, specific: if f is C^k at x, then f_loc is C^k, hence also g_loc
--> in the smooth case, get a diffeo between things (right phrasing touches the local diffeo q.)

end IFT

variable {f : M → N} {x : M}
-- Suppose G consists of C¹ maps, i.e. G\leq contDiffGroupoid n.
/-- Suppose `G` consists of `C^1` maps. Suppose `f:M → N` is `C^1` at `x` and
  the differential $df_x$ is a linear isomorphism.
  Then `x` and `f x` admit neighbourhoods `U ⊆ M` and `V ⊆ N`, respectively such that
  `f` is a structomorphism between `U` and `V`. -/
theorem IFT_manifolds [CompleteSpace E] [HasGroupoid M (contDiffGroupoid 1 I)] [I.Boundaryless]
    (G : StructureGroupoid H) [HasGroupoid M G]
    (hf : ContMDiffAt I J 1 f x) {f' : TangentSpace I x ≃L[ℝ] TangentSpace J (f x)}
    (hf' : HasMFDerivAt I J f x f') :
    -- TODO: state the correct statement: h.toFun and f "are the same"
    ∃ U : Opens M, ∃ V : Opens N, ∃ h : Structomorph G U V, True /-(∀ x : U → h x = f x.1-/ := by
  -- part 1: bookkeeping on the manifolds
  -- Consider the charts φ and ψ on `M` resp. `N` around `x` and `f x`, respectively.
  let φ := extChartAt I x
  let ψ := extChartAt J (f x)
  -- Consider the local coordinate representation `f_loc` of `f` w.r.t. these charts.
  let f_loc := ψ ∘ f ∘ φ.invFun
  let U := φ '' (φ.source ∩ f ⁻¹' ψ.source)
  let V := ψ '' (f '' φ.source ∩ ψ.source)
  -- Check: `U` and `V` are open and `f_loc` maps `U` to `V`.
  -- have : U ⊆ φ.target := sorry -- will see when I need these!
  -- have : V ⊆ ψ.target := sorry
  -- clear for charts; not as obvious for extended charts
  have : IsOpen U := sorry
  have : IsOpen V := sorry
  have : MapsTo f_loc U V := by
    intro x hx
    rcases hx with ⟨x', hx', hx'x⟩
    have : φ.invFun (φ x') = x' := φ.left_inv (mem_of_mem_inter_left hx')
    have : f_loc x = (ψ ∘ f) x' := calc f_loc x
      _ = (ψ ∘ f ∘ φ.invFun) (φ x') := by rw [hx'x]
      _ = (ψ ∘ f) (φ.invFun (φ x')) := rfl
      _ = (ψ ∘ f) x' := by rw [this]
    --have : f x' ∈ (f '' φ.source ∩ ψ.source) := by aesop
    aesop
  -- By definition, `f_loc` is `C^1` at `x' := φ x`.
  set x' := φ x
  have : ContDiffWithinAt ℝ 1 f_loc (range I) x' := ((contMDiffAt_iff I J).mp hf).2
  have : ContDiffAt ℝ 1 f_loc (φ x) := by rw [I.range_eq_univ] at this; exact this
  -- As shown before, `(df_loc)_φ x is also a linear isomorphism.
  have df_loc : E ≃L[ℝ] E' := differential_in_charts_iso I J f' hf'
  let temp := differential_in_charts_iso_coe I J (chartAt H x) (chartAt H (f x)) f' hf'
  -- have temp' : ((differential_in_charts_iso I J f' hf').toLinearEquiv).toAddHom.toFun = (fderiv ℝ f_loc x') := temp
  -- have temp'' : (df_loc.toLinearEquiv).toAddHom.toFun = (fderiv ℝ f_loc x') := sorry -- not the same temp'
  -- TODO: different lemmas don't match; both expressions should be `fderiv ℝ f_loc x'`
  obtain ⟨der, part2⟩ := this.differentiableAt (by rfl)
  have mismatch : der = df_loc := by sorry
  have hdf'loc : HasFDerivAt (𝕜 := ℝ) f_loc df_loc x' := by rw [← mismatch]; exact part2

  -- By the Inverse Function Theorem on normed spaces, there are neighbourhoods U' and V' of x' and
  -- ψ(f x)=f_loc x' and a C¹ function g_loc:V' \to U' such that f_loc and g_loc are inverses.
  let r := this.toLocalHomeomorph f_loc hdf'loc (by rfl)
  let U' := r.source
  let V' := r.target
  have aux : x' ∈ U' := this.mem_toLocalHomeomorph_source hdf'loc (le_refl 1)
  have aux : f_loc x' ∈ V' := this.image_mem_toLocalHomeomorph_target hdf'loc (le_refl 1)

  let g_loc := this.localInverse hdf'loc (by rfl)
  let gloc_diff := this.to_localInverse hdf'loc (by rfl)
  -- have : ContDiffAt ℝ 1 g_loc (f_loc x') := gloc_diff
  -- xxx: is this missing API to argue r and g_loc are the same? I'll see!

  -- Shrinking U' and V' jointly if necessary, we may assume U'\subset U and V'\subset V.
  -- Skipping this for the moment; the details are slightly annoying.
  have : U' ⊆ U := sorry
  have : V' ⊆ V := sorry

  -- These yield open subsets `U` and `V` containing `x` and `f x`, respectively,
  let U := φ ⁻¹' U'
  let V := ψ ⁻¹' V'
  have : IsOpen U := sorry
  have : x ∈ U := sorry
  have : IsOpen V := sorry
  have : f x ∈ V := sorry
  -- and a local inverse g of f.
  let g := φ.invFun ∘ g_loc ∘ ψ
  have : MapsTo g V U := sorry -- check!

  -- We compute f = \psi^{-1}\circ\psi \tilde{f}\circ\phi^{-1}\circ\phi = \psi^{-1}\circ \tilde{f}\circ\phi on U. Hence, we deduce g\circ f=id on U and f\circ g =id_V.
  -- g is C¹, since in the charts \phi and \psi, the local coordinate representation is \tilde{g},
  -- which is C¹ by definition.

  sorry
