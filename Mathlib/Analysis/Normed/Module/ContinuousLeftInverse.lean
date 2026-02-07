/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.Normed.Module.Complemented
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Continuous linear maps with a continuous left inverse

This file defines continuous linear maps which admit a coutinuous left inverse.

We prove that this class of maps
* is closed under products,
* is closed under composition
* contains linear equivalences and (in the future) Fredholm operators

as well as various weakenings: for instance, an injective linear map on a finite-dimensional space
always admits a continuous/bounded right inverse.

This concept is used to give a conceptual definition of immersions between Banach manifolds.
HOPEFULLY, IF EVERYTHING WORKS OUT!

## TODO
- is "split epimorphism/split surjection" a better term?

-/

public section

open Function Set

variable {R : Type*} [Semiring R] {E E' F F' G : Type*}
  [TopologicalSpace E] [AddCommMonoid E] [Module R E]
  [TopologicalSpace E'] [AddCommMonoid E'] [Module R E']
  [TopologicalSpace F] [AddCommMonoid F] [Module R F]
  [TopologicalSpace F'] [AddCommMonoid F'] [Module R F']

noncomputable section

/-- A continuous linear map admits a left inverse which is a continuous linear map itself. -/
@[expose] protected def ContinuousLinearMap.HasBoundedLeftInverse (f : E →L[R] F) : Prop :=
  ∃ g : F →L[R] E, LeftInverse g f

namespace ContinuousLinearMap.HasBoundedLeftInverse

variable {f : E →L[R] F}

/-- Choice of right inverse for `f` -/
def leftInverse (h : f.HasBoundedLeftInverse) : F →L[R] E := Classical.choose h

lemma leftInverse_leftInverse (h : f.HasBoundedLeftInverse) : LeftInverse h.leftInverse f :=
  Classical.choose_spec h

lemma injective (h : f.HasBoundedLeftInverse) : Injective f :=
  h.leftInverse_leftInverse.injective

example (h : f.HasBoundedLeftInverse) (x : E) : h.leftInverse (f x) = x :=
  h.leftInverse_leftInverse x

lemma congr {g : E →L[R] F} (hf : f.HasBoundedLeftInverse) (hfg : g = f) :
    g.HasBoundedLeftInverse :=
  hfg ▸ hf

/-- A continuous linear equivalence has a continuous left inverse. -/
lemma _root_.ContinuousLinearEquiv.hasBoundedLeftInverse (f : E ≃L[R] F) :
    f.toContinuousLinearMap.HasBoundedLeftInverse :=
  ⟨f.symm, rightInverse_of_comp (by simp)⟩

/-- An invertible continuous linear map splits. -/
lemma of_isInvertible (hf : IsInvertible f) : f.HasBoundedLeftInverse := by
  obtain ⟨e, rfl⟩ := hf
  exact e.hasBoundedLeftInverse

-- FUTURE (once mathlib has a notion of Fredholm operators):
-- If `E` and `F` are Banach and `f : E → F` is Fredholm, then `f` has a continuous right inverse.

/-- If `f` and `g` split, then so does `f × g`. -/
lemma prodMap {g : E' →L[R] F'} (hf : f.HasBoundedLeftInverse) (hg : g.HasBoundedLeftInverse) :
    (f.prodMap g).HasBoundedLeftInverse := by
  sorry -- left for Samantha

variable [TopologicalSpace G] [AddCommMonoid G] [Module R G]

lemma comp {g : F →L[R] G} (hg : g.HasBoundedLeftInverse) (hf : f.HasBoundedLeftInverse) :
    (g.comp f).HasBoundedLeftInverse := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  refine ⟨finv.comp ginv, fun x ↦ ?_⟩
  simp only [coe_comp', Function.comp_apply]
  rw [hginv, hfinv]

lemma of_comp {g : F →L[R] G} (hfg : (g.comp f).HasBoundedLeftInverse) :
    f.HasBoundedLeftInverse := by
  obtain ⟨fginv, hfginv⟩ := hfg
  refine ⟨fginv.comp g, fun y ↦ ?_⟩
  simp only [coe_comp', Function.comp_apply]
  exact hfginv y

lemma compCLE_left {f₀ : F' ≃L[R] E} (hf : f.HasBoundedLeftInverse) :
    (f.comp f₀.toContinuousLinearMap).HasBoundedLeftInverse :=
  hf.comp f₀.hasBoundedLeftInverse

lemma compCLE_right {g : F ≃L[R] F'} (hf : f.HasBoundedLeftInverse) :
    (g.toContinuousLinearMap.comp f).HasBoundedLeftInverse :=
  g.hasBoundedLeftInverse.comp hf

-- add analogues of this one, TODO (but easy -> postponed)
-- /-- `ContinuousLinearMap.fst` has a continuous left inverse. -/
-- lemma continuousLinearMap_fst : (ContinuousLinearMap.fst R F G).HasBoundedLeftInverse := by
--   use (ContinuousLinearMap.id _ _).prod 0
--   intro x
--   simp

-- /-- `ContinuousLinearMap.snd` has a continuous left inverse. -/
-- lemma continuousLinearMap_snd : (ContinuousLinearMap.snd R F G).HasBoundedLeftInverse := by
--   use ContinuousLinearMap.prod 0 (.id R G)
--   intro x
--   simp

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E E' F F' G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {f : E →L[𝕜] F}

/-- If `f : E → F` is injective and `E` is finite-dimensional,
`f` has a continuous left inverse. -/
lemma of_injective_of_finiteDimensional [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    (hf : Injective f) :
    f.HasBoundedLeftInverse := by
  -- A surjective linear map has a linear inverse. It is continuous because its domain is.
  obtain ⟨g, hg⟩ :=
    f.toLinearMap.exists_leftInverse_of_injective (f.ker_eq_bot_of_injective hf)
  exact ⟨⟨g, LinearMap.continuous_of_finiteDimensional _⟩, fun x ↦ congr($hg x)⟩

end NontriviallyNormedField

end ContinuousLinearMap.HasBoundedLeftInverse

-- This definition needs stronger hypotheses.
variable {R E E' F F' G : Type*} [Ring R]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace E'] [AddCommMonoid E'] [Module R E']
  [TopologicalSpace F] [AddCommGroup F] [Module R F]
  [TopologicalSpace F'] [AddCommMonoid F'] [Module R F']

/-- A continuous linear map `f : E → F` **splits** iff it is injective, has closed range and
its image has a closed complement. -/
@[expose] protected def ContinuousLinearMap.Splits (f : E →L[R] F) : Prop :=
  Injective f ∧ IsClosed (Set.range f) ∧ Submodule.ClosedComplemented f.range

namespace ContinuousLinearMap.Splits

variable {f : E →L[R] F} {g : E' →L[R] F'}

lemma injective (h : f.Splits) : Injective f := h.1

lemma isClosed_range (h : f.Splits) : IsClosed (Set.range f) := h.2.1

lemma closedComplemented (h : f.Splits) : Submodule.ClosedComplemented f.range :=
  h.2.2

lemma congr {g : E →L[R] F} (hf : f.Splits) (hfg : g = f) : g.Splits :=
  hfg ▸ hf

variable [T1Space F] -- let's assume this for now

/-- Choice of a closed complement of `range f` -/
def complement (h : f.Splits) : Submodule R F :=
  h.closedComplemented.complement

lemma isClosed_complement (h : f.Splits) : IsClosed (X := F) h.complement :=
  h.closedComplemented.isClosed_complement

lemma isCompl_complement (h : f.Splits) : IsCompl f.range h.complement :=
  h.closedComplemented.isCompl_complement

end ContinuousLinearMap.Splits

-- The first test: continuous left inverse implies splits

namespace ContinuousLinearMap

-- the kernel of the left inverse has a closed complement; nice!
lemma HasBoundedLeftInverse.foo [IsTopologicalAddGroup F]
    {f : E →L[R] F} (hf : f.HasBoundedLeftInverse) :
    (hf.leftInverse.ker).ClosedComplemented :=
  ContinuousLinearMap.closedComplemented_ker_of_rightInverse _ f hf.leftInverse_leftInverse

lemma HasBoundedLeftInverse.splits {f : E →L[R] F} (hf : f.HasBoundedLeftInverse) : f.Splits := by
  refine ⟨hf.injective, ?_, ?_⟩
  · -- Proof sketch: assume z_n = f y_n is a sequence in range f converging to z.
    -- Then z_n = f y_n = f g (f y_n) converges to f g z (by continuity of f and g),
    -- hence (if in a T2 space, perhaps weaker) z = f (g z) ∈ range f also.
    -- Not sure about the best way to formalise this, but it certainly works.
    sorry
  -- Let g be a left inverse for f. Then ker g is a closed subspace of F,
  -- and a complement to range f. Proof sketch:
  -- If y = f x ∈ ker g, we have x = g f x = g y = 0, so y = f 0 = 0 is trivial.
  -- For any z ∈ F, observe that z = (z - f g z) + f g z; the latter lies in range f,
  -- while the former is in ker g as we have g (f g z) = g z for any z.

  -- Issue: Lean expects a continuous projection to f.range instead, so we cannot just do
  -- `use hf.leftInverse.ker`. TODO how does this work? just some API gap?
  -- idea: do y ↦ f g y; is continuous as both maps are, idempotent as continuous left inverse
  let p' := f.comp hf.leftInverse
  -- have aux : ∀ (x : (f).range), (p'.codRestrict (f).range (by intro y; simp [p'])) x = x := by
  --   intro y; simp [p']
  --   sorry
  use p'.codRestrict f.range (by intro y; simp [p'])
  intro ⟨y, hy⟩
  have : p' y = y := by
    obtain ⟨x, rfl⟩ := hy
    simp only [coe_coe, coe_comp', Function.comp_apply, p']
    rw [hf.leftInverse_leftInverse]
  sorry -- some Lean quibbles; morally the previous sorry
#check Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl
-- would also work, but might be more effort than this one...

variable {R E F : Type*} [NontriviallyNormedField R] -- XXX weaken later!
  [NormedAddCommGroup E] [NormedSpace R E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace R F] [CompleteSpace F]


#check LinearMap.exists_leftInverse_of_injective -- without continuity, is easy
-- Conversely, suppose f is injective with closed range and a closed complement Y ⊆ F.
-- We need to find a continuous left inverse g : F → X.
-- We will define g to be zero on Y, and an inverse to f on range f.
-- TODO: how can we make sure to do this linearly, while g is continuous?
-- (If we could choose a closed complement X of ker f, we'd get an iso f : X → range f,
-- and the inverse would be our natural choice. It would be bounded as f is anti-Lipschitz
-- because... well, somehow should be true.)
-- Actually, I'm stupid: f is injective, so the kernel of course has a complement.
-- In fact, f is anti-Lipschitz (assuming sufficient completeness), hence the inverse is bounded.
/- So, proof strategy is:
1. restrict f to range f; observe that map is still injective
2. therefore, it is an equivalence (mathlib knows this) and has an inverse (range f) → X
3. define the inverse g as y ∈ Y -> project to (range f) -> X; that projection exists by our
  definition of closed complement. :-)
4. the inverse is bounded as f was anti-Lipschitz
  (and we had a closed complement, i.e. continuous projection)!

Why is this map a left inverse? need to check g f x = x for all x.
Observe y = f x ∈ range f, so g y = inv (y) = x... by construction (hopefully!)
-/
#check ContinuousLinearMap.rangeRestrict -- restrict f, step 1
-- step 2, restriction is injective: missing lemma, but almost "by grind"
-- -> is a linear equiv, has an inverse: should be in Lean

/-- A choice of continuous left inverse of an injective continuous linear map with closed range:
this is `LinearMap.leftInverse` as a continuous linear map;
by injectivity, the junk value of `leftInverse` never matters, and continuity of the inverse
follows form the closed range condition. -/
def leftInverse_of_injective_of_isClosed_range
    (f : E →L[R] F) (hf : Injective f) (hf' : IsClosed (range f)) : f.range →L[R] E :=
  letI K := f.antilipschitzConstant_of_injective_of_isClosed_range hf hf'
  letI hfK := f.antilipschitz_antiLipschitzConstant_of_injective_of_isClosed_range hf hf'
  LinearMap.mkContinuous f.rangeRestrict.leftInverse K (by
    rintro ⟨y, ⟨x, rfl⟩⟩
    have aux := hfK.le_mul_dist x 0
    simp only [dist_zero_right, map_zero] at aux
    convert aux
    exact f.rangeRestrict.leftInverse_apply_of_inj
      (by rw [ker_codRestrict]; exact LinearMap.ker_eq_bot.mpr hf) x
  )

/-- A split linear map has a bounded left inverse. -/
lemma Splits.hasBoundedLeftInverse {f : E →L[R] F} (hf : f.Splits) : f.HasBoundedLeftInverse := by
  have : (f.rangeRestrict).ker = ⊥ := by
    rw [ker_codRestrict]; exact LinearMap.ker_eq_bot.mpr hf.injective
  -- We compose the continuous inverse of `f : E → range f` with the projection `p : F → range f`.
  obtain ⟨p, hp⟩ := hf.closedComplemented
  let g := f.leftInverse_of_injective_of_isClosed_range hf.injective hf.isClosed_range
  refine ⟨g.comp p, fun x ↦ ?_⟩
  simpa [g, hp (⟨f x, by simp⟩)] using f.rangeRestrict.leftInverse_apply_of_inj this x

end ContinuousLinearMap

end
