/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.NormedSpace.HahnBanach.Splits
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Analysis.Normed.Operator.Banach

/-! # MDifferentiable maps which split

TODO: better doc-string

-/

open Function Set

section

-- does NontriviallyNormedField also suffice? composition seems to require this...
variable {𝕜 : Type*} [RCLike 𝕜] {E E' F F' G : Type*}
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

lemma mfderiv_injective (hf : MSplitsAt I I' f x) : Injective (mfderiv I I' f x) :=
  hf.2.injective

lemma congr (hf : MSplitsAt I I' f x) (hfg : g =ᶠ[nhds x] f) : MSplitsAt I I' g x := by
  obtain ⟨hdiff, hdf⟩ := hf
  refine ⟨hdiff.congr_of_eventuallyEq hfg, ?_⟩
  -- mfderivWithin_congr helps
  sorry

section

variable [IsManifold I 1 M] {e : PartialHomeomorph M H} {x : M}

/-- The `mfderiv` of an extended chart is a local diffeomorphism. -/
-- XXX: proven on a prior version of #9273; without any assumptions on the boundary
def extend_mfderiv_toContinousLinearEquiv
    (he : e ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ (chartAt H x).source) :
    ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) E := sorry

@[simp, mfld_simps]
lemma extend_mfderiv_toContinousLinearEquiv_coe
    (he : e ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ (chartAt H x).source) :
    (extend_mfderiv_toContinousLinearEquiv he hx).toContinuousLinearMap =
      mfderiv I (modelWithCornersSelf 𝕜 E) (e.extend I) x :=
  sorry -- rfl

def extend_symm_mfderiv_toContinousLinearEquiv
    (he : e ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ (chartAt H x).source) :
    ContinuousLinearEquiv (RingHom.id 𝕜) E (TangentSpace I x) := sorry

@[simp, mfld_simps]
lemma extend_symm_mfderiv_toContinousLinearEquiv_coe
    (he : e ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ (chartAt H x).source) :
    (extend_symm_mfderiv_toContinousLinearEquiv he hx).toContinuousLinearMap =
      mfderiv (modelWithCornersSelf 𝕜 E) I (e.extend I).symm (e.extend I x) := sorry

------------------

lemma extend (he : e ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ (chartAt H x).source) :
    MSplitsAt I (modelWithCornersSelf 𝕜 E) (e.extend I) x := by
  constructor
  · sorry -- analogue of mdifferentiableAt_extChartAt... also on my old branch?
  · exact (extend_mfderiv_toContinousLinearEquiv he hx).splits.congr (by simp)

lemma extend_symm (he : e ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ (chartAt H x).source) :
    MSplitsAt (modelWithCornersSelf 𝕜 E) I (e.extend I).symm (e.extend I x) := by
  constructor
  · sorry -- analogue of mdifferentiableAt_extChartAt_symm ... also on my old branch?
  · exact (extend_symm_mfderiv_toContinousLinearEquiv he hx).splits.congr (by simp)

end

lemma _root_.IsLocalDiffeomorphAt.msplitsAt {f : M → M'}
    (hf : IsLocalDiffeomorphAt I I' n f x) (hn : 1 ≤ n) : MSplitsAt I I' f x :=
  ⟨hf.mdifferentiableAt hn,
    (hf.mfderiv_toContinuousLinearEquiv hn).splits.congr (by symm; simp)⟩

/-- If `f` is split at `x` and `g` is split at `f x`, then `g ∘ f` is split at `x`. -/
lemma comp [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    {g : M' → N} (hg : MSplitsAt I' J g (f x)) (hf : MSplitsAt I I' f x) :
    MSplitsAt I J (g ∘ f) x := by
  refine ⟨hg.1.comp x hf.1, ?_⟩
  · rw [mfderiv_comp x hg.1 hf.1]
    have : CompleteSpace (TangentSpace I x) := by show CompleteSpace E; assumption
    have : CompleteSpace (TangentSpace I' (f x)) := by show CompleteSpace E'; assumption
    have : CompleteSpace (TangentSpace J (g (f x))) := by show CompleteSpace F; assumption
    exact hg.2.comp hf.2

lemma comp_isLocalDiffeomorphAt_left [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    (hf : MSplitsAt I I' f x) {f₀ : N → M} {y : N} (hxy : f₀ y = x)
    (hf₀ : IsLocalDiffeomorphAt J I n f₀ y) (hn : 1 ≤ n) :
    MSplitsAt J I' (f ∘ f₀) y := by
  have : CompleteSpace (TangentSpace I x) := by show CompleteSpace E; assumption
  have : CompleteSpace (TangentSpace I' (f x)) := by show CompleteSpace E'; assumption
  apply MSplitsAt.comp ?_ (hf₀.msplitsAt hn)
  convert hf -- proper way: custom congr lemma...

lemma comp_isLocalDiffeomorphAt_left_iff [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    {f₀ : N → M} {y : N} (hxy : f₀ y = x) (hf₀ : IsLocalDiffeomorphAt J I n f₀ y) (hn : 1 ≤ n) :
    MSplitsAt I I' f x ↔ MSplitsAt J I' (f ∘ f₀) y := by
  refine ⟨fun hf ↦ hf.comp_isLocalDiffeomorphAt_left hxy hf₀ hn,
    fun h ↦ ?_⟩
  let g₀ : M → N := hf₀.localInverse
  have hg₀' : IsLocalDiffeomorphAt I J n hf₀.localInverse (f₀ y) :=
    hf₀.localInverse_isLocalDiffeomorphAt
  have hg₀ : IsLocalDiffeomorphAt I J n (hf₀.localInverse) (f₀ y) := hxy ▸ hg₀'
  have : g₀ x = y := hxy ▸ hf₀.localInverse_left_inv hf₀.localInverse_mem_target
  sorry -- let asdf := h.comp_isLocalDiffeomorphAt_left this hg₀ hn
  -- apply asdf.congr
  -- locally, the inverse agrees: TODO complete all the details!

lemma comp_isLocalDiffeomorphAt_right [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    {g : M' → N} (hg : IsLocalDiffeomorphAt I' J n g (f x)) (hn : 1 ≤ n) (hf : MSplitsAt I I' f x) :
    MSplitsAt I J (g ∘ f) x :=
  (hg.msplitsAt hn).comp hf

-- TODO: complete this proof later
lemma comp_isLocalDiffeomorphAt_right_iff [CompleteSpace E] [CompleteSpace F] [CompleteSpace E']
    {g : M' → N} (hg : IsLocalDiffeomorphAt I' J n g (f x)) (hn : 1 ≤ n) :
    MSplitsAt I I' f x ↔  MSplitsAt I J (g ∘ f) x := by
  refine ⟨fun hf ↦ hf.comp_isLocalDiffeomorphAt_right hg hn,
    fun h ↦ ?_⟩
  sorry
  -- something like this: need to choose a local inverse of a local diffeo
  -- let asdf := h.comp_isLocalDiffeomorphAt_right hg.symm hn--).congr (by ext; simp)⟩

-- corollary: MSplitsAt holds iff some coordinate representation splits
--   iff *any* coordinate representation splits

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
lemma comp [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    {g : M' → N} (hg : MSplits I' J g) (hf : MSplits I I' f) : MSplits I J (g ∘ f) :=
  fun x ↦ (hg (f x)).comp (hf x)

-- NB. the next four lemmas could be generalised to local diffeomorphism,
-- and perhaps even proven in terms of their MSplitsAt versions

lemma comp_diffeomorph_left [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    (hf : MSplits I I' f) (f₀ : Diffeomorph J I N M n) (hn : 1 ≤ n) : MSplits J I' (f ∘ f₀) :=
  hf.comp (f₀.splits hn)

lemma comp_diffeomorph_left_iff [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    (f₀ : Diffeomorph J I N M n) (hn : 1 ≤ n) : MSplits I I' f ↔ MSplits J I' (f ∘ f₀) :=
  ⟨fun hf ↦ hf.comp_diffeomorph_left f₀ hn,
    fun h ↦ (h.comp_diffeomorph_left f₀.symm hn).congr (by ext; simp)⟩

lemma comp_diffeomorph_right [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    (g : Diffeomorph I' J M' N n) (hn : 1 ≤ n) (hf : MSplits I I' f) : MSplits I J (g ∘ f) :=
  (g.splits hn).comp hf

lemma comp_diffeomorph_right_iff [CompleteSpace E] [CompleteSpace F] [CompleteSpace E']
    {g : Diffeomorph I' J M' N n} (hn : 1 ≤ n) : MSplits I I' f ↔  MSplits I J (g ∘ f) :=
  ⟨fun hf ↦ hf.comp_diffeomorph_right g hn,
    fun h ↦ (h.comp_diffeomorph_right g.symm hn).congr (by ext; simp)⟩

-- corollary: MSplitsAt holds iff some coordinate representation splits
--   iff *any* coordinate representation splits

section RCLike

-- TODO: modify these statements mutatis mutandis

-- variable {𝕜 : Type*} [RCLike 𝕜] {E E' F F' : Type*}
--   [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
--   [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
--   [FiniteDimensional 𝕜 F] {f : E →L[𝕜] F} {g : E' →L[𝕜] F'}

-- /-- If `f : E → F` is injective and `F` is finite-dimensional, then `f` splits. -/
-- lemma of_injective_of_finiteDimensional [FiniteDimensional 𝕜 F] (hf : Injective f) : f.Splits := by
--   have aux : IsClosed (Set.range f) := sorry -- should follow from fin-dim
--   exact ⟨hf, aux, Submodule.ClosedComplemented.of_finiteDimensional (LinearMap.range f)⟩

-- /-- If `f : E → F` is injective, `E` is finite-dimensional and `F` is Banach, then `f` splits. -/
-- lemma of_injective_of_finiteDimensional_of_completeSpace
--     [FiniteDimensional 𝕜 E] [CompleteSpace F] (hf : Injective f) : f.Splits := by
--   have aux : IsClosed (Set.range f) := sorry -- should follow from fin-dim
--   exact ⟨hf, aux, Submodule.ClosedComplemented.of_finiteDimensional (LinearMap.range f)⟩

-- -- If `f : E → F` is injective, `E` and `F` are Banach and `f` is Fredholm, then `f` splits.

end RCLike

end MSplits

open scoped Manifold

end
