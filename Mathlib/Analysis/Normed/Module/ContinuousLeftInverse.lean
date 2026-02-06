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

end
