/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.Normed.Module.Complemented

/-! # Linear maps which split

TODO: better doc-string, move this to a better place


-/

open Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E E' F F' G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

noncomputable section

/-- A continuous linear map `f : E → F` *splits* iff it is injective, has closed range and
its image has a closed complement. -/
protected def ContinuousLinearMap.Splits (f : E →L[𝕜] F) : Prop :=
  Injective f ∧ IsClosed (Set.range f) ∧ Submodule.ClosedComplemented (LinearMap.range f)

-- XXX: should this be about ContinuousLinearMapClass?
namespace ContinuousLinearMap.Splits

variable {f : E →L[𝕜] F} {g : E' →L[𝕜] F'}

lemma injective (h : f.Splits) : Injective f := h.1

lemma isClosed_range (h : f.Splits) : IsClosed (Set.range f) := h.2.1

lemma closedComplemented (h : f.Splits) : Submodule.ClosedComplemented (LinearMap.range f) :=
  h.2.2

/-- Choice of a closed complement of `range f` -/
def complement (h : f.Splits) : Submodule 𝕜 F :=
  Classical.choose h.closedComplemented.exists_isClosed_isCompl

lemma complement_isClosed (h : f.Splits) : IsClosed (X := F) h.complement :=
  (Classical.choose_spec h.closedComplemented.exists_isClosed_isCompl).1

lemma complement_isCompl (h : f.Splits) : IsCompl (LinearMap.range f) h.complement :=
  (Classical.choose_spec h.closedComplemented.exists_isClosed_isCompl).2

/-- TODO! add missing documentation -/
def foo (h : f.Splits) : F ≃L[𝕜] E × h.complement :=
  -- use `Submodule.ClosedComplemented.exists_submodule_equiv_prod `, or so!
  -- choose a complement E' of im f (in Lean: is h.complement)
  -- put F ≅ range f ⊕ h.complement → E ⊕ h.complement,
  -- where the last map is (f.equivImage).symm ⊕ id
  sorry

lemma foo_bar (h : f.Splits) : h.foo ∘ f = (·, 0) :=
  -- compute using the definition above... perhaps without the noncomputable?
  sorry

/-- A continuous linear equivalence splits. -/
lemma _root_.ContinuousLinearEquiv.splits (f : E ≃L[𝕜] F) : f.toContinuousLinearMap.Splits := by
  refine ⟨?_, ?_, ?_⟩
  · rw [f.coe_coe]
    apply EquivLike.injective
  · rw [f.coe_coe, EquivLike.range_eq_univ]
    exact isClosed_univ
  · erw [LinearMap.range_eq_top_of_surjective f (EquivLike.surjective f)]
    exact Submodule.closedComplemented_top

/-- If `f` and `g` split, then so does `f × g`. -/
lemma prodMap (hf : f.Splits) (hg : g.Splits) : (f.prodMap g).Splits := by
  refine ⟨hf.injective.prodMap hg.injective, ?_, ?_⟩
  · rw [coe_prodMap', range_prod_map]
    exact (hf.isClosed_range).prod hg.isClosed_range
  · have : LinearMap.range (f.prodMap g) = (LinearMap.range f).prod (LinearMap.range g) := by
      -- seems to be missing...
      sorry
    rw [this]
    sorry -- also missing: Submodule.ClosedComplemented.prod

-- Outline of missing ingredient:
-- Thm. X, Y Banach, f:X\to Y continuous linear. Then
-- f injective with closed range <=> \exists 0 < c, ∀ x, c|x| ≤ |f x|
-- Reduce: range (g ∘ f) below, and also g(F') below are closed:
--   (if s ⊆ G is closed, then g(s) is closed, uses injectivity and the open mapping theorem)

-- XXX: is this completeness hypothesis required?
/-- The composition of split continuous linear maps splits. -/
lemma comp [CompleteSpace G] {g : F →L[𝕜] G} (hf : f.Splits) (hg : g.Splits) : (g.comp f).Splits := by
  have h1 : IsClosed (range ⇑(g.comp f)) := sorry
  refine ⟨hg.injective.comp hf.injective, h1, ?_⟩
  · let F' := hf.complement
    let G' := hg.complement
    rw [Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl]
    refine ⟨h1, (F'.map g) + G', ?_, ?_⟩
    · -- missing (also missing hypotheses?): sum of closed submodules is closed
      sorry
    · sorry

lemma compCLE_left [CompleteSpace F] {f₀ : F' ≃L[𝕜] E} (hf : f.Splits) :
    (f.comp f₀.toContinuousLinearMap).Splits :=
  f₀.splits.comp hf

lemma compCLE_right [CompleteSpace F'] {g : F ≃L[𝕜] F'} (hf : f.Splits) :
    (g.toContinuousLinearMap.comp f).Splits :=
  hf.comp g.splits

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {E E' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [FiniteDimensional 𝕜 F] {f : E →L[𝕜] F} {g : E' →L[𝕜] F'}

/-- If `f : E → F` is injective and `F` is finite-dimensional, then `f` splits. -/
lemma of_injective_of_finiteDimensional [FiniteDimensional 𝕜 F] (hf : Injective f) : f.Splits := by
  have aux : IsClosed (Set.range f) := sorry -- should follow from fin-dim
  exact ⟨hf, aux, Submodule.ClosedComplemented.of_finiteDimensional (LinearMap.range f)⟩

/-- If `f : E → F` is injective, `E` is finite-dimensional and `F` is Banach, then `f` splits. -/
lemma of_injective_of_finiteDimensional_of_completeSpace
    [FiniteDimensional 𝕜 E] [CompleteSpace F] (hf : Injective f) : f.Splits := by
  have aux : IsClosed (Set.range f) := sorry -- should follow from fin-dim
  exact ⟨hf, aux, Submodule.ClosedComplemented.of_finiteDimensional (LinearMap.range f)⟩

-- If `f : E → F` is injective, `E` and `F` are Banach and `f` is Fredholm, then `f` splits.

end RCLike

end ContinuousLinearMap.Splits

end

-- section

-- variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E E' F F' G : Type*}
--   [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
--   [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
--   [NormedAddCommGroup G] [NormedSpace 𝕜 G]
-- variable {f : E → F} {x : E} {n : WithTop ℕ∞}

-- -- TODO: I'm not very happy yet with the naming... want to namespace, but this is not it yet

-- variable (𝕜) in
-- /-- If `f : E → F` is differentiable at `x`, we say `f` splits at `x` iff `fderiv 𝕜 f x` splits. -/
-- def DifferentiableAt.SplitsAt (f : E → F) (x : E) : Prop :=
--   DifferentiableAt 𝕜 f x ∧ (fderiv 𝕜 f x).Splits

-- variable (𝕜) in
-- /-- If `f : E → F` is differentiable, we say `f` splits iff it splits at every `x`,
-- i.e. each `fderiv 𝕜 f x` splits. -/
-- def Differentiable.Splits (f : E → F) : Prop := ∀ x, DifferentiableAt.SplitsAt 𝕜 f x

-- open scoped Manifold

-- namespace DifferentiableAt.SplitsAt

-- lemma comp [CompleteSpace G] {f : E → F} {g : F → G}
--     (hf : SplitsAt 𝕜 f x) (hg : SplitsAt 𝕜 g (f x)) : SplitsAt 𝕜 (g ∘ f) x := by
--   dsimp only [SplitsAt] at hf hg ⊢
--   rw [fderiv_comp _ hg.1 hf.1]
--   exact ⟨hg.1.comp _ hf.1, hf.2.comp hg.2⟩

-- -- prodMap also

-- lemma congr {f g : E → F} (hf : SplitsAt 𝕜 f x) (hfg : g =ᶠ[nhds x] f) : SplitsAt 𝕜 g x := by
--   dsimp only [SplitsAt] at hf ⊢
--   constructor
--   · exact hf.1.congr_of_eventuallyEq hfg
--   · have : fderiv 𝕜 f x = fderiv 𝕜 g x := sorry -- missing?
--     rw [← this]
--     exact hf.2

-- end DifferentiableAt.SplitsAt

-- namespace Differentiable.Splits

-- lemma prodMap {f : E → F} {g : E' → F'} (hf : Splits 𝕜 f) (hg : Splits 𝕜 g) :
--     Splits 𝕜 (Prod.map f g) :=
--   sorry

-- lemma comp [CompleteSpace G] {f : E → F} {g : F → G} (hf : Splits 𝕜 f) (hg : Splits 𝕜 g) :
--     Splits 𝕜 (g ∘ f) :=
--   fun x ↦ (hf x).comp (hg (f x))

-- -- comp_left, comp_right

-- lemma congr {f g : E → F} (hf : Splits 𝕜 f) (hfg : g = f) : Splits 𝕜 g :=
--   fun x ↦ (hf x).congr hfg.eventuallyEq

-- section RCLike

-- -- TODO: copy the analogous statements from above

-- end RCLike

-- end Differentiable.Splits

-- end

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E E' F F' G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : WithTop ℕ∞} [IsManifold I n M] [IsManifold I' n M']
variable {f : M → M'} {x : M} {n : WithTop ℕ∞}

local instance : NormedAddCommGroup (TangentSpace I x) := by
  show NormedAddCommGroup E
  infer_instance

local instance : NormedSpace 𝕜 (TangentSpace I x) := by
  show NormedSpace 𝕜 E
  infer_instance

variable (I I' f x) in
/-- If `f : M → M` is differentiable at `x`,
we say `f` splits at `x` iff `mfderiv 𝕜 f I I' x` splits. -/
def MSplitsAt (f : M → M') (x : M) : Prop :=
  MDifferentiableAt I I' f x ∧ (mfderiv I I' f x).Splits

namespace MSplitsAt

variable {f g : M → M'} {x : M}

lemma congr (hf : MSplitsAt I I' f x) (hfg : g =ᶠ[nhds x] f) : MSplitsAt I I' g x := by
  obtain ⟨hdiff, hdf⟩ := hf
  refine ⟨hdiff.congr_of_eventuallyEq hfg, ?_⟩
  -- mfderivWithin_congr helps
  sorry

lemma _root_.IsLocalDiffeomorphAt.msplitsAt {f : M → M'}
    (hf : IsLocalDiffeomorphAt I I' n f x) (hn : 1 ≤ n) : MSplitsAt I I' f x := by
  refine ⟨hf.mdifferentiableAt hn, ?_⟩
  -- proven on a different branch: differential is a continuous linear equivalence
  sorry -- apply ContinuousLinearEquiv.splits

/-- if `f` is split at `x` and `g` is split at `f x`, then `g ∘ f` is split at `x`. -/
lemma comp [CompleteSpace F] {g : M' → N} (hf : MSplitsAt I I' f x) (hg : MSplitsAt I' J g (f x)) :
    MSplitsAt I J (g ∘ f) x := by
  refine ⟨hg.1.comp x hf.1, ?_⟩
  · rw [mfderiv_comp x hg.1 hf.1]
    have : CompleteSpace (TangentSpace J ((g ∘ f) x)) := by show CompleteSpace F; assumption
    exact hf.2.comp hg.2

end MSplitsAt

variable (I I') in
/-- If `f : M → M` is differentiable, we say `f` splits iff it splits at every `x`,
i.e. each `mfderiv 𝕜 I I' f x` splits. -/
def MSplits (f : M → M') : Prop := ∀ x, MSplitsAt I I' f x

namespace MSplits

variable {f g : M → M'}

lemma congr (hf : MSplits I I' f) (hfg : g = f) : MSplits I I' g :=
  fun x ↦ (hf x).congr hfg.eventuallyEq

lemma _root_.IsLocalDiffeomorph.splits {f : M → M'}
    (hf : IsLocalDiffeomorph I I' n f) (hn : 1 ≤ n) : MSplits I I' f :=
  fun x ↦ (hf x).msplitsAt hn

lemma _root_.Diffeomorph.splits (f : Diffeomorph I I' M M' n) (hn : 1 ≤ n) : MSplits I I' f :=
  f.isLocalDiffeomorph.splits hn

/-- If `f` and `g` split, then so does `g ∘ f`. -/
lemma comp [CompleteSpace F] {g : M' → N} (hf : MSplits I I' f) (hg : MSplits I' J g) :
    MSplits I J (g ∘ f) :=
  fun x ↦ (hf x).comp (hg (f x))

-- TODO: transfer all these to MSplitsAt, then prove these lemmas in terms of them

lemma compDiffeomorph_left [CompleteSpace E'] (hf : MSplits I I' f)
    (f₀ : Diffeomorph J I N M n) (hn : 1 ≤ n) : MSplits J I' (f ∘ f₀) :=
  (f₀.splits hn).comp hf

lemma compDiffeomorph_left_iff [CompleteSpace E'] (f₀ : Diffeomorph J I N M n) (hn : 1 ≤ n) :
    MSplits I I' f ↔ MSplits J I' (f ∘ f₀) :=
  ⟨fun hf ↦ hf.compDiffeomorph_left f₀ hn,
    fun h ↦ (h.compDiffeomorph_left f₀.symm hn).congr (by ext; simp)⟩

lemma compDiffeomorph_right [CompleteSpace F] (g : Diffeomorph I' J M' N n) (hn : 1 ≤ n)
    (hf : MSplits I I' f) : MSplits I J (g ∘ f) :=
  hf.comp (g.splits hn)

lemma compDiffeomorph_right_iff [CompleteSpace F] [CompleteSpace E']
    {g : Diffeomorph I' J M' N n} (hn : 1 ≤ n) : MSplits I I' f ↔  MSplits I J (g ∘ f) :=
  ⟨fun hf ↦ hf.compDiffeomorph_right g hn,
    fun h ↦ (h.compDiffeomorph_right g.symm hn).congr (by ext; simp)⟩

-- corollary: MSplitsAt holds iff some coordinate representation splits
--   iff *any* coordinate representation splits


section RCLike

-- TODO: copy the analogous statements from above

end RCLike

end MSplits

open scoped Manifold

end
