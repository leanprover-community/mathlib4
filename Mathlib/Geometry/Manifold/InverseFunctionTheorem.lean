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

/-- A `Structomorph` on the model space `H` lies in the structure groupoid. -/
lemma Structomorph.toLocalHomeomorph_mem_groupoid (h : Structomorph G H H) : h.toLocalHomeomorph ∈ G := by
  -- FIXME: is there a more elegant way to prove this?
  have : ∀ (c c' : LocalHomeomorph H H), c ∈ atlas H H → c' ∈ atlas H H → h.toLocalHomeomorph ∈ G := by
    intro c c' hc hc'
    have : c.symm ≫ₕ h.toHomeomorph.toLocalHomeomorph ≫ₕ c' = h.toLocalHomeomorph := by
      rw [chartedSpaceSelf_atlas.mp hc, chartedSpaceSelf_atlas.mp hc']
      simp
    exact this ▸ (h.mem_groupoid c c' hc hc')
  apply this (c := LocalHomeomorph.refl H) (c' := LocalHomeomorph.refl H) rfl rfl

/-- If a local homeomorphism on the model space `H` lies in the structure groupoid,
  it induces a `Structomorph` on the model space `H`. -/
def LocalHomeomorph.toStructomorph_of_mem_groupoid (e : LocalHomeomorph H H)
    (hs : e.source = univ) (ht : e.target = univ) (h : e ∈ G) : Structomorph G H H := by
  -- XXX: can I simplify this, e.g. by rewriting e.toHomeomorphSourceTarget?
  let ehom : Homeomorph H H := {
    toFun := e.toFun
    invFun := e.invFun
    left_inv := fun x ↦e.left_inv' (by rw [hs]; trivial)
    right_inv := fun x ↦e.right_inv' (by rw [ht]; trivial)
    continuous_toFun := by
      let r := hs ▸ e.continuous_toFun
      exact continuous_iff_continuousOn_univ.mpr r
    continuous_invFun := by
      let r := ht ▸ e.continuous_invFun
      exact continuous_iff_continuousOn_univ.mpr r
  }
  exact {
    ehom with
    mem_groupoid := by
      -- As `H` has only one chart, we only need to check ehom ∈ G: but ehom is equal to e.
      intro c c' hc hc'
      rw [chartedSpaceSelf_atlas.mp hc, chartedSpaceSelf_atlas.mp hc']
      simp only [LocalHomeomorph.refl_symm, LocalHomeomorph.trans_refl, LocalHomeomorph.refl_trans]
      exact G.eq_on_source h (⟨hs.symm, eqOn_refl _ _⟩)
  }

/-- If `h` is a `Structomorph` on `H`, it is also a local structomorphism at every point. -/
lemma Structomorph.toLocalStructomorphAt (h : Structomorph G H H) {x : H} :
    G.IsLocalStructomorphWithinAt h.toFun univ x :=
  fun y ↦ ⟨h.toLocalHomeomorph, h.toLocalHomeomorph_mem_groupoid, eqOn_refl h.toFun _, y⟩

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

-- Work the on the concept of pregroupoids: hopefully, this is the right framework to *state*
-- the Inverse Function theorem in general.
section Pregroupoids
variable (H : Type*) [TopologicalSpace H]
-- warm-up: the pregroupoid of continuous functions
-- I suspect the mathlib definition is misnamed... let me define my own, for practice
def contPregroupoid : Pregroupoid H where
  property := fun f s => ContinuousOn f s
  comp := fun hf hg _ _ _ ↦ hg.comp' hf
  id_mem := continuousOn_id
  locality := fun _ h ↦ continuousOn_of_locally_continuousOn h
  congr := fun _ congr hf ↦ hf.congr congr

/-- A pregroupoid `P` on `H` is called **good** (placeholder name)
  iff it is stable under local inverses:
if `f` lies in `P` and has a local inverse function `g`, then `g` also lies in `P`.
Simplest special case: if `P` is e.g. the contPregroupoid (which is monotone),
suppose `f` is continuous on `U` (i.e., we have `contPregroupoid.property f U`)
and g : H → H is a local inverse of `f` on `s`: we have `InvOn g f s t` for some `t ⊆ H`.
Then, `g` is continuous on `t` (i.e. property `g t`). -/
structure GoodPregroupoid (H : Type*) [TopologicalSpace H] extends Pregroupoid H where
  inverse : ∀ {f g s t}, property f s → InvOn g f s t → property g t

/- Note: If `f` is continuous on `u`, while `InvOn g f s t`,
`InvOn.mono` implies `InvOn g f s∩u t∩f(u)`: thus, it suffices to consider the case `s=u`. -/
example {X Y : Type*} {u s : Set X} {t : Set Y} {f : X → Y} {g : Y → X} (h : InvOn g f s t) :
  InvOn g f (s ∩ u) (t ∩ (f '' u)) := h.mono (inter_subset_left s u) (inter_subset_left _ _)

/-- The groupoid associated to a good pregroupoid. -/
def GoodPregroupoid.groupoid (PG : GoodPregroupoid H) : StructureGroupoid H :=
  (PG.toPregroupoid).groupoid

-- The continuous pregroupoid is not good: not in general, not even if `H` is compact and Hausdorff.
-- Need to show that f continuous on s (and g being the point-wise inverse) implies g cont on t;
-- this is simply false: a bijective function is not bi-continuous in general.
-- A *variant* assuming only compact s were true. Not interesting to use.
-- XXX: not enough, a priori `s` is any set!

variable {n : ℕ∞} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
-- XXX: generalise to any field 𝕜 which is ℝ or ℂ

-- C^n functions on E: warm-up case (only one chart); full definition in SmoothManifoldsWithCorners
def contDiffPregroupoidWarmup : Pregroupoid E := {
  property := fun f s ↦ ContDiffOn ℝ n f s
  comp := fun {f g} {u v} hf hg _ _ _ ↦ hg.comp' hf
  id_mem := contDiffOn_id
  locality := fun _ h ↦ contDiffOn_of_locally_contDiffOn h
  congr := by intro f g u _ congr hf; exact (contDiffOn_congr congr).mpr hf
}

-- test this works: this is a good pregroupoid -> no, it doesn't, my assumptions are still too weak!
lemma contDiffPregroupoidGoodWarmup : GoodPregroupoid E where
  -- TODO: fix copy-paste!
  property := fun f s ↦ ContDiffOn ℝ n f s
  comp := fun {f g} {u v} hf hg _ _ _ ↦ hg.comp' hf
  id_mem := contDiffOn_id
  locality := fun _ h ↦ contDiffOn_of_locally_contDiffOn h
  congr := by intro f g u _ congr hf; exact (contDiffOn_congr congr).mpr hf
  --toPregroupoid := contDiffPregroupoidWarmup E
  inverse := by
    intro f g s t hf hinv
    have : ContDiffOn ℝ n f s := hf
    show ContDiffOn ℝ n g t
    sorry

-- FIXME: this is getting close; make it match exactly!
structure BetterPregroupoid (H : Type*) [TopologicalSpace H]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  extends Pregroupoid H where
  -- If `f ∈ P` defines a homeomorphism `s → t` with inverse `g`, then `g ∈ P` also.
  -- For instance, if `f` is a local homeo at `x`, we're good.
  inverse : ∀ {f g s t x}, ∀ {f' : H ≃L[ℝ] H}, x ∈ s → IsOpen s → property f s →
    /- HasFDerivAt (𝕜 := ℝ) f f' x →-/ -- TODO: this is not accepted by Lean!
    InvOn g f s t → property g t

-- this is the key lemma I need to showing that C^n maps define a better pregroupoid
-- only done in the affine case, FIXME generalise
-- FIXME: not entirely true; I get that g is ContDiff in *some* nhd of x, might be smaller than t!
-- we need to work over ℝ or ℂ, otherwise `toLocalInverse` doesn't apply
lemma Iwant {f g : E → E} {s t : Set E} {x : E} {f' : E ≃L[ℝ] E} (hinv : InvOn g f s t)
    (hf : ContDiffAt ℝ n f x) (hf' : HasFDerivAt (𝕜 := ℝ) f f' x) (hn : 1 ≤ n) :
    ContDiffOn ℝ n g t := by
  let r := hf.to_localInverse (f' := f') hf' hn -- ContDiffAt ℝ n (hf.localInverse hf' hn) (f x)
  sorry

lemma contDiffPregroupoidBetterWarmup (hn : 1 ≤ n) {x : E} : BetterPregroupoid E where
  -- TODO: fix copy-paste!
  property := fun f s ↦ ContDiffOn ℝ n f s
  comp := fun {f g} {u v} hf hg _ _ _ ↦ hg.comp' hf
  id_mem := contDiffOn_id
  locality := fun _ h ↦ contDiffOn_of_locally_contDiffOn h
  congr := by intro f g u _ congr hf; exact (contDiffOn_congr congr).mpr hf
  inverse := by
    intro f g s t x f' hx hs hf hinv
    have : ContDiffOn ℝ n f s := hf
    show ContDiffOn ℝ n g t
    -- TODO: add this to the groupoid assumptions...
    have : HasFDerivAt (𝕜 := ℝ) f f' x := sorry
    exact Iwant hinv (hf.contDiffAt (hs.mem_nhds hx)) this hn

/- my vision for the general IFT/general shape should go like this:
    - consider a "good pregroupoid" P: inverses should exist;
      basically, we put all the necessary properties so the inverse by the IFT is also in P
    - let G be the groupoid associated to P
    - suppose f ∈ P is differentiable at x with invertible differential,
      construct a local inverse (I have this already)
    - categorical statement of the IFT on H, over any good pregroupoid P
      if f : H → H, f ∈ P with differential df_x invertible,
      yields f.isLocalStructomorphWithin s x for some s
    - conceptual statement of the IFT, over any suitable pregroupoid:
        pull up this property over charts using ChartedSpace.LiftPropOn
    - perhaps: can I characterise, over any suitable pregroupoid, this as sth like
        f:M → M' (ove the same model I) is a local structo for G iff f and f' are in P
      generalising `isLocalStructomorphOn_contDiffGroupoid_iff` to all categories
  specialise to specific categories: C^n and 𝕜-analytic ones, show they satisfy this.

∀ x, f':..., f with df_x=f'
if f is contDiff at x with invertible differential,
g is the IFT inverse, then the inverse is also in P

perhaps generalise: LocalHomeomorph.contDiffAt_symm
if f is a local homeo, ContDiffAt x and df_x is an inverse, we're good

  the framework works for any C^k, also for analytic functions, just the same -/

end Pregroupoids

/-! Inverse function theorem for manifolds. -/
section IFT
namespace ContMDiffAt
variable {f : M → N} {x : M} {f' : TangentSpace I x ≃L[ℝ] TangentSpace J (f x)} [CompleteSpace E]

/-- Given a `ContMDiff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible
derivative at `x`, returns a `LocalHomeomorph` with `to_fun = f` and `x ∈ source`. -/
noncomputable def toLocalHomeomorph {n : ℕ∞} [I.Boundaryless] [J.Boundaryless]
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
  -- have : MapsTo f_loc U V := by
  --   intro x hx
  --   rcases hx with ⟨x', hx', hx'x⟩
  --   have : φ.invFun (φ x') = x' := φ.left_inv (mem_of_mem_inter_left hx')
  --   have : f_loc x = (ψ ∘ f) x' := calc f_loc x
  --     _ = (ψ ∘ f ∘ φ.invFun) (φ x') := by rw [hx'x]
  --     _ = (ψ ∘ f) (φ.invFun (φ x')) := rfl
  --     _ = (ψ ∘ f) x' := by rw [this]
  --   --have : f x' ∈ (f '' φ.source ∩ ψ.source) := by aesop
  --   aesop
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
  -- have : φ'.toFun = φ.toFun := rfl
  -- have : ψ'.toFun = ψ.toFun := rfl
  exact φ' ≫ₕ f_loc' ≫ₕ ψ'.symm

-- TODO: sanity-check that I got the directions right?
-- @[simp]
-- theorem toLocalHomeomorph_coe {n : ℕ∞} [I.Boundaryless] [J.Boundaryless]
--     (hf : ContMDiffAt I J n f x) (hf' : HasMFDerivAt I J f x f') (hn : 1 ≤ n) :
--     (hf.toLocalHomeomorph I J hf' hn : M → N) = f :=
--   rfl
end ContMDiffAt

-- do I want counterparts of mem_toLocalHomeomorph_source, image_mem_toLocalHomeomorph_target also?

-- XXX: good name for this?
variable {X Y : Type*} {f f' : X → Y} {g g' : Y → X} {s : Set X} {t : Set Y} in
lemma InvOn.eqOn_inverse_of_eqOn (h : InvOn g f s t) (h' : InvOn g' f' s t) (heq : EqOn f f' s)
    (hg : MapsTo g t s) : EqOn g g' t := by
  intro y hy
  -- We have y = f x = f' x for x := g y ∈ s, hence can apply our assumptions.
  set x := g y
  rw [← (h.2 hy), heq (hg hy)]
  exact (h'.1 (hg hy)).symm

-- xxx: why is my variant better?
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : LocalHomeomorph X Y) in
lemma LocalHomeomorph.restr_target' {s : Set X} (hs : IsOpen s) :
    (e.restr s).target = e '' (e.source ∩ s) := by
  rw [← (e.restr s).image_source_eq_target, e.restr_source s, hs.interior_eq, e.restr_apply]

variable {X Y : Type*} {s : Set X} {f : X → Y} {g : Y → X} in
lemma InvOn.mapsTo_image (hinv : InvOn g f s (f '' s)) : MapsTo g (f '' s) s := by
  rintro y ⟨x, hxs, hxy⟩
  rw [← hxy]
  exact mem_of_eq_of_mem (hinv.1 hxs) hxs

/-- If `f : H → H` is a local structomorphism at `x` relative to `s` and has a local inverse `g`,
  then `g` is a local structomorphism at `f x` relative to `f '' x`. -/
-- no differentiability here! wouldn't make sense either :-)
lemma StructureGroupoid.localInverse_isLocalStructomorphWithin {f : H → H} {s : Set H} {x : H}
    {G : StructureGroupoid H} [ClosedUnderRestriction G] (hf : G.IsLocalStructomorphWithinAt f s x)
    (hs : IsOpen s) {g : H → H} (hinv : InvOn g f s (f '' s)) (hgx : g (f x) = x) :
    G.IsLocalStructomorphWithinAt g (f '' s) (f x) := by
  intro hfx
  -- `hgx` is required so this is true: need to exclude the case x ∉ s, but f x ∈ f'' s.
  have hxs : x ∈ s := by
    rcases hfx with ⟨x', hx's, hx'y⟩
    have : x = x' := by rw [(hinv.1 hx's).symm, hx'y, hgx]
    exact mem_of_eq_of_mem this hx's
  rcases hf hxs with ⟨e, heg, heq, hxsource⟩
  -- XXX: `heq` and `restr_target` disagree about order of sets,
  -- so need to rewrite by inter_comm, here and below.
  have e'source : (e.restr s).symm.source = e '' (e.source ∩ s) := by
    rw [(e.restr s).symm_source, e.restr_target' hs]
  rw [inter_comm] at e'source
  have image_eq : e '' (e.source ∩ s) = f '' (e.source ∩ s) := by
    rw [inter_comm]; exact image_congr heq.symm
  refine ⟨(e.restr s).symm, G.symm (closedUnderRestriction' heg hs), ?_, ?_⟩
  · intro y hy
    rw [e'source] at hy
    -- write y = e x = f x for some x ∈ e.source ∩ s
    rcases mem_of_mem_inter_right hy with ⟨x, hx, hxy⟩
    have : f x = y := by rw [heq hx]; exact hxy
    have hy' : y ∈ f '' (s ∩ e.source) := this ▸ mem_image_of_mem f hx
    -- Now, it's a general lemma about two-sided inverses.
    have hinv' : InvOn g f (s ∩ e.source) (f '' (s ∩ e.source)) :=
      hinv.mono (inter_subset_left s e.source) (image_subset _ (inter_subset_left _ _))
    have aux : InvOn (e.restr s).symm (e.restr s) (s ∩ e.source) (f '' (s ∩ e.source)) := by
      have : f '' (s ∩ e.source) = e '' (s ∩ e.source) := image_congr heq
      rw [this]
      have : (e.restr s).source = s ∩ e.source := by
        rw [inter_comm]
        let r := hs.interior_eq ▸ e.restr_source s
        exact r
      rw [← e'source, ← this]
      exact (e.restr s).invOn
    exact (InvOn.eqOn_inverse_of_eqOn hinv' aux heq) (InvOn.mapsTo_image hinv') hy'
  · show f x ∈ (e.restr s).symm.source
    rw [(e.restr s).symm_source, e.restr_target' hs]
    rw [image_eq]
    apply mem_image_of_mem f (mem_inter hxsource hxs)

/-- If `f : M → N` is a local `G`-structomorphism, so is its inverse. -/
-- This is the global version of the previous lemma.
lemma aux (f : LocalHomeomorph M N) (G : StructureGroupoid H) [ClosedUnderRestriction G] -- needed?!
    (hf : ChartedSpace.LiftPropOn G.IsLocalStructomorphWithinAt f f.source) :
    ChartedSpace.LiftPropOn G.IsLocalStructomorphWithinAt f.symm f.symm.source := by
  intro y hy
  let x := f.symm y
  rcases hf x (f.map_target hy) with ⟨_, h2⟩
  -- *Essentially*, this reduces to the local statement shown before.
  -- Need to check a number of details though:
  --   - local reps of f and f.symm are mutually inverse (use f.invOn plus extra argument)
  --   - the inverse map g_loc maps x to x
  --   - possibly some more things I didn't check yet
  -- Introduce notation to make the goal readable.
  let s := G.localInverse_isLocalStructomorphWithin h2
  set f_loc := (chartAt H (f x)) ∘ f ∘ (chartAt H x).symm with eq
  set g_loc := (chartAt H x) ∘ f.symm ∘ (chartAt H (f x)).symm
  set x' := (chartAt H x) x
  set U := (chartAt H x).symm ⁻¹' f.source
  -- Details to prove. TODO!
  -- XXX: I might need to tweak this, by restricting to a smaller set,
  -- so f.source and chart domains play nicely with each other: in essence, use trans instead of ∘
  have aux1 : IsOpen U := sorry -- need chartAt H x.source contains f.source or so; then it's easy
  have aux2 : InvOn g_loc f_loc U (f_loc '' U) := by
    refine ⟨?_, sorry⟩ -- other sorry the same
    · intro y hy
      let x'' := (chartAt H x).symm y
      have : x'' ∈ f.source := sorry -- from hx
      calc g_loc (f_loc y)
        _ = ((chartAt H x) ∘ f.symm ∘ (chartAt H (f x)).symm ∘ (chartAt H (f x)) ∘ f ∘ (chartAt H x).symm) y := rfl
        -- x'' ∈ f.source by hypothesis hx, so f x'' ∈ f.target
        _ = ((chartAt H x) ∘ f.symm ∘ (chartAt H (f x)).symm ∘ (chartAt H (f x)) ∘ f) x'' := rfl
        -- cancel middle two charts: xxx need f x'' nice enough
        _ = ((chartAt H x) ∘ f.symm ∘ f) x'' := sorry
        -- cancel, as in f.target
        _ = (chartAt H x) x'' := sorry
        _ = ((chartAt H x) ∘ (chartAt H x).symm) y := rfl
        _ = y := sorry -- cancel again: somehow, assume x lies in the chart source/target whatever
  have aux3 : g_loc (f_loc x') = x' := sorry -- if x ∈ U, this follows from aux2
  -- This is the local statement from the previous lemma: now lift back to a global statement.
  let s := s aux1 aux2 aux3
  refine ⟨f.continuous_invFun y hy, ?_⟩
  · sorry -- is s, up to change of notation??!!

-- Corollary: if `f` in the IFT is a local structomorphism, so is the local inverse.
-- XXX: can I write this more nicely, not with such exploding terms?
lemma aux_cor (f : LocalHomeomorph M N) (G : StructureGroupoid H) [ClosedUnderRestriction G]
    -- suppose f has a local inverse per the IFT. TODO: pare down these assumptions!
    {n : ℕ∞} [I.Boundaryless] [J.Boundaryless] [CompleteSpace E] {x : M}
    (hfdiff : ContMDiffAt I J n f x) {f' : TangentSpace I x ≃L[ℝ] TangentSpace J (f x)}
    (hf' : HasMFDerivAt I J f x f') (hn : 1 ≤ n)
    -- and f is a local structo wrt G
    (hf : ChartedSpace.LiftPropOn G.IsLocalStructomorphWithinAt f f.source) :
    ChartedSpace.LiftPropOn G.IsLocalStructomorphWithinAt (hfdiff.toLocalHomeomorph I J hf' hn).symm
      (hfdiff.toLocalHomeomorph I J hf' hn).symm.source := by
  set r := hfdiff.toLocalHomeomorph I J hf' hn
  let s := aux f G hf
  -- missing piece: hfdiff.toLocalHomeomorph produces the inverse
  have : r.symm = f.symm := sorry
  rw [this]
  exact s

-- step 2, separately in each category
-- if f is C^k, analytic, etc. and df_x is invertible, then f_loc is a local structo within thingy
-- StructureGroupoid.IsLocalStructomorphWithinAt
-- this has been shown for C^n already, just quote it!

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
