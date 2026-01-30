/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Analysis.NormedSpace.HahnBanach.Splits
public import Mathlib.Analysis.Normed.Module.Complemented
public import Mathlib.Analysis.Normed.Operator.Banach

/-! # MDifferentiable maps which split

TODO: better doc-string

-/

open Function Set

public section

-- XXX. I *think* a `NontriviallyNormedField` suffices; if RCLike is required, it will be for the
-- composition of split continuous linear maps. I believe this is fine, but the proof is not
-- sorry-free yet.
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

-- move, perhaps to e.g. ContMDiff.Basic
/-- If `f : M → M'` has injective differential at `x`, it is `mdifferentiable` at `x`. -/
lemma mdifferentiableAt_of_mfderiv_injective {f : M → M'} (hf : Injective (mfderiv I I' f x)) :
    MDifferentiableAt I I' f x := by
  replace hf : LinearMap.ker (mfderiv I I' f x).toLinearMap = ⊥ := by
    rw [LinearMap.ker_eq_bot]; exact hf
  by_cases h: Subsingleton E
  · exact mdifferentiable_of_subsingleton.mdifferentiableAt
  · by_contra h'
    have : (⊥ : Submodule 𝕜 (TangentSpace I x)) = ⊤ := by
      simp [mfderiv_zero_of_not_mdifferentiableAt h', ← hf]
    have : Subsingleton (Submodule 𝕜 E) := subsingleton_of_bot_eq_top this
    simp_all only [Submodule.subsingleton_iff]

-- FIXME: is there a way to avoid the next two instance?
local instance : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
local instance : NormedSpace 𝕜 (TangentSpace I x) := inferInstanceAs (NormedSpace 𝕜 E)

variable (I I' f x) in
/-- If `f : M → M` is differentiable at `x`,
we say `f` splits at `x` iff `mfderiv 𝕜 f I I' x` splits. -/
def MSplitsAt (f : M → M') (x : M) : Prop := (mfderiv I I' f x).Splits

namespace MSplitsAt

variable {f g : M → M'} {x : M}

lemma mfderiv_injective (hf : MSplitsAt I I' f x) : Injective (mfderiv I I' f x) :=
  hf.injective

lemma mdifferentiableAt (hf : MSplitsAt I I' f x) : MDifferentiableAt I I' f x :=
  mdifferentiableAt_of_mfderiv_injective hf.injective

lemma continuousAt (hf : MSplitsAt I I' f x) : ContinuousAt f x := hf.mdifferentiableAt.continuousAt

lemma congr (hf : MSplitsAt I I' f x) (hfg : g =ᶠ[nhds x] f) : MSplitsAt I I' g x := by
  have : mfderiv I I' f x = mfderiv I I' g x := hfg.symm.mfderiv_eq
  unfold MSplitsAt
  exact this ▸ hf

lemma prodMap {y : N} (hf : MSplitsAt I I' f x) {g : N → N'} (hg : MSplitsAt J J' g y) :
    MSplitsAt (I.prod J) (I'.prod J') (Prod.map f g) (x, y) := by
  -- missing lemma: mfderiv of Prod.map
  unfold MSplitsAt at hf hg ⊢
  -- then apply Splits.prodMap to hf and hg
  sorry

section

variable [IsManifold I 1 M] {e : OpenPartialHomeomorph M H} {x : M}

/-- The `mfderiv` of an extended chart is a local diffeomorphism. -/
-- XXX: proven on a prior version of #9273; without any assumptions on the boundary
def extendMfderivToContinousLinearEquiv
    (he : e ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ (chartAt H x).source) :
    ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) E := sorry

@[simp, mfld_simps]
lemma extendMfderivToContinousLinearEquiv_coe
    (he : e ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ (chartAt H x).source) :
    (extendMfderivToContinousLinearEquiv he hx).toContinuousLinearMap =
      mfderiv I (modelWithCornersSelf 𝕜 E) (e.extend I) x :=
  sorry -- rfl

def extend_symm_mfderivToContinousLinearEquiv
    (he : e ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ (chartAt H x).source) :
    ContinuousLinearEquiv (RingHom.id 𝕜) E (TangentSpace I x) := sorry

@[simp, mfld_simps]
lemma extend_symm_mfderivToContinousLinearEquiv_coe
    (he : e ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ (chartAt H x).source) :
    (extend_symm_mfderivToContinousLinearEquiv he hx).toContinuousLinearMap =
      mfderiv (modelWithCornersSelf 𝕜 E) I (e.extend I).symm (e.extend I x) := sorry

------------------

lemma extend (he : e ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ (chartAt H x).source) :
    MSplitsAt I (modelWithCornersSelf 𝕜 E) (e.extend I) x :=
  (extendMfderivToContinousLinearEquiv he hx).splits.congr (by simp)

lemma extend_symm (he : e ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ (chartAt H x).source) :
    MSplitsAt (modelWithCornersSelf 𝕜 E) I (e.extend I).symm (e.extend I x) :=
  (extend_symm_mfderivToContinousLinearEquiv he hx).splits.congr (by simp)

end

lemma _root_.IsLocalDiffeomorphAt.msplitsAt {f : M → M'}
    (hf : IsLocalDiffeomorphAt I I' n f x) (hn : n ≠ 0) : MSplitsAt I I' f x :=
  (hf.mfderivToContinuousLinearEquiv hn).splits.congr (by symm; simp)

/-- If `f` is split at `x` and `g` is split at `f x`, then `g ∘ f` is split at `x`. -/
lemma comp [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    {g : M' → N} (hg : MSplitsAt I' J g (f x)) (hf : MSplitsAt I I' f x) :
    MSplitsAt I J (g ∘ f) x := by
  rw [MSplitsAt] -- slight code smell?
  rw [mfderiv_comp x (mdifferentiableAt_of_mfderiv_injective hg.mfderiv_injective)
    (mdifferentiableAt_of_mfderiv_injective hf.mfderiv_injective)]
  have : CompleteSpace (TangentSpace I x) := by assumption
  have : CompleteSpace (TangentSpace I' (f x)) := by assumption
  have : CompleteSpace (TangentSpace J (g (f x))) := by assumption
  rw [MSplitsAt] at hf hg
  apply hg.comp hf

lemma comp_isLocalDiffeomorphAt_left [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    (hf : MSplitsAt I I' f x) {f₀ : N → M} {y : N} (hxy : f₀ y = x)
    (hf₀ : IsLocalDiffeomorphAt J I n f₀ y) (hn : n ≠ 0) :
    MSplitsAt J I' (f ∘ f₀) y :=
  MSplitsAt.comp (hxy ▸ hf) (hf₀.msplitsAt hn)

lemma comp_isLocalDiffeomorphAt_left_iff [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    {f₀ : N → M} {y : N} (hxy : f₀ y = x) (hf₀ : IsLocalDiffeomorphAt J I n f₀ y) (hn : n ≠ 0) :
    MSplitsAt I I' f x ↔ MSplitsAt J I' (f ∘ f₀) y := by
  refine ⟨fun hf ↦ hf.comp_isLocalDiffeomorphAt_left hxy hf₀ hn,
    fun h ↦ ?_⟩
  have hg₀' : IsLocalDiffeomorphAt I J n hf₀.localInverse (f₀ y) :=
    hf₀.localInverse_isLocalDiffeomorphAt
  have : hf₀.localInverse x = y := hxy ▸ hf₀.localInverse_left_inv hf₀.localInverse_mem_target
  have : MSplitsAt I I' (f ∘ f₀ ∘ hf₀.localInverse) x :=
    h.comp_isLocalDiffeomorphAt_left this (hxy ▸ hg₀') hn
  apply this.congr
  exact (hxy ▸ hf₀.localInverse_eventuallyEq_right.symm).fun_comp f

lemma comp_isLocalDiffeomorphAt_right [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    (hf : MSplitsAt I I' f x) {g : M' → N} (hg : IsLocalDiffeomorphAt I' J n g (f x)) (hn : n ≠ 0) :
    MSplitsAt I J (g ∘ f) x :=
  (hg.msplitsAt hn).comp hf

section

-- Does this lemma already exist?
lemma foo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {g g' : Y → Y} {x : X} (hf : ContinuousAt f x) (hg : g =ᶠ[nhds (f x)] g') :
    g ∘ f =ᶠ[nhds x] g' ∘ f := by
  rw [Filter.eventuallyEq_iff_exists_mem] at hg ⊢
  choose s hs hgs using hg
  exact ⟨f ⁻¹' s, hf.preimage_mem_nhds hs, fun x hx ↦ hgs (by simp_all)⟩

end

-- TODO: fix the last sorry, is a small mathematical question
lemma comp_isLocalDiffeomorphAt_right_iff [CompleteSpace E] [CompleteSpace F] [CompleteSpace E']
    {g : M' → N} (hg : IsLocalDiffeomorphAt I' J n g (f x)) (hn : n ≠ 0) :
    MSplitsAt I I' f x ↔  MSplitsAt I J (g ∘ f) x := by
  refine ⟨fun hf ↦ hf.comp_isLocalDiffeomorphAt_right hg hn,
    fun h ↦ ?_⟩
  have hg' : IsLocalDiffeomorphAt J I' n hg.localInverse (g (f x)) :=
    hg.localInverse_isLocalDiffeomorphAt
  apply (h.comp_isLocalDiffeomorphAt_right hg' hn).congr
  symm
  have := hg.localInverse_eventuallyEq_left

  -- question: must we have `ContinuousAt f x`? if so, the proof is easy

  -- this certainly holds... but is not what we want!
  have aux : ContinuousAt (hg.localInverse.toPartialEquiv ∘ g ∘ f) x := by
    apply ContinuousAt.comp ?_ h.continuousAt
    sorry -- missing prereq, local inverse of a local diffeo is continuous at its point

  have hf : ContinuousAt f x := by
    -- issue: cannot apply ContinuousAt.congr_of_eventuallyEq aux as that'd be cyclic!
    sorry
  exact foo hf this

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

lemma prodMap (hf : MSplits I I' f) {g : N → N'} (hg : MSplits J J' g) :
    MSplits (I.prod J) (I'.prod J') (Prod.map f g) := fun (x, y) ↦ (hf x).prodMap (hg y)

lemma _root_.IsLocalDiffeomorph.splits {f : M → M'}
    (hf : IsLocalDiffeomorph I I' n f) (hn : n ≠ 0) : MSplits I I' f :=
  fun x ↦ (hf x).msplitsAt hn

lemma _root_.Diffeomorph.splits (f : Diffeomorph I I' M M' n) (hn : n ≠ 0) : MSplits I I' f :=
  f.isLocalDiffeomorph.splits hn

/-- If `f` and `g` split, then so does `g ∘ f`. -/
lemma comp [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    {g : M' → N} (hg : MSplits I' J g) (hf : MSplits I I' f) : MSplits I J (g ∘ f) :=
  fun x ↦ (hg (f x)).comp (hf x)

lemma comp_isLocalDiffeomorph_left [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    (hf : MSplits I I' f) {f₀ : N → M} (hf₀ : IsLocalDiffeomorph J I n f₀) (hn : n ≠ 0) :
    MSplits J I' (f ∘ f₀) :=
  hf.comp (hf₀.splits hn)

-- XXX: is this true if hf₀ is just a local diffeomorphism and *not* surjective?
-- (With surjective, this reduces to its MSplitsAt cousin.)
lemma comp_diffeomorph_left_iff [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    (f₀ : Diffeomorph J I N M n) (hn : n ≠ 0) : MSplits I I' f ↔ MSplits J I' (f ∘ f₀) :=
  ⟨fun hf ↦ hf.comp_isLocalDiffeomorph_left f₀.isLocalDiffeomorph hn,
    fun h ↦ (h.comp_isLocalDiffeomorph_left f₀.symm.isLocalDiffeomorph hn).congr (by ext; simp)⟩

lemma comp_isLocalDiffeomorph_right [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    {g : M' → N} (hg : IsLocalDiffeomorph I' J n g) (hn : n ≠ 0) (hf : MSplits I I' f) :
    MSplits I J (g ∘ f) :=
  (hg.splits hn).comp hf

lemma comp_diffeomorph_right_iff [CompleteSpace E] [CompleteSpace F] [CompleteSpace E']
    {g : M' → N} (hg : IsLocalDiffeomorph I' J n g) (hn : n ≠ 0) :
    MSplits I I' f ↔  MSplits I J (g ∘ f) := by
  refine ⟨fun hf ↦ hf.comp_isLocalDiffeomorph_right hg hn, fun h x ↦ ?_⟩
  rw [MSplitsAt.comp_isLocalDiffeomorphAt_right_iff (hg (f x)) hn (I := I)]
  exact h x

-- corollary: MSplitsAt holds iff some coordinate representation splits
--   iff *any* coordinate representation splits

-- TODO: should I augment the definition of MSplits, to demand being C^n?

variable {𝕜 : Type*} [RCLike 𝕜] {E E' F F' G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {f : M → N} {x : M} {n : WithTop ℕ∞}

/-- If `f : M → N` is injective and `M` is finite-dimensional, then `f` splits. -/
lemma of_injective_of_finiteDimensional [FiniteDimensional 𝕜 E]
    (hf' : ∀ x, Injective (mfderiv I J f x)) : MSplits I J f := by
  intro x
  have : FiniteDimensional 𝕜 (TangentSpace I x) := by assumption
  exact ContinuousLinearMap.Splits.of_injective_of_finiteDimensional_of_completeSpace (hf' x)

/-- If `f : M → N` is injective and `N` is finite-dimensional, then `f` splits. -/
lemma of_injective_of_finiteDimensional' [FiniteDimensional 𝕜 F]
    (hf' : ∀ x, Injective (mfderiv I J f x)) : MSplits I J f := by
  intro x
  have : FiniteDimensional 𝕜 (TangentSpace J (f x)) := by assumption
  exact ContinuousLinearMap.Splits.of_injective_of_finiteDimensional (hf' x)

-- FUTURE (once mathlib has a notion of Fredholm operators):
-- If `f : M → N` is injective, `M` and `N` are Banach manifolds and each differential
-- `mfderiv I J f x` is Fredholm, then `f` splits.

end MSplits

open scoped Manifold

end
