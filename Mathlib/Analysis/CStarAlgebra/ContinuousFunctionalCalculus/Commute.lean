/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-! # Commuting with applications of the continuous functional calculus

This file shows that if an element `b` commutes with both `a` and `star a`, then it commutes
with `cfc f a` (or `cfcₙ f a`). In the case where `a` is selfadjoint, we may reduce the hypotheses.

## Main results

* `Commute.cfc` and `Commute.cfcₙ`: an element commutes with `cfc f a` or `cfcₙ f a` if it
  commutes with both `a` and `star a`. Specialized versions for `ℝ` and `ℝ≥0` or for
  `IsSelfAdjoint a` which do not require the user to show the element commutes with `star a` are
  provided for convenience.

## Implementation notes

The proof of `Commute.cfcHom` and `Commute.cfcₙHom` could be made simpler by appealing to basic
facts about double commutants, but doing so would require extra type class assumptions so that we
can talk about topological star algebras. Instead, we avoid this to minimize the work Lean must do
to call these lemmas, and give a straightforward proof by induction.

-/

public section

variable {𝕜 A : Type*}

open scoped NNReal

section Unital

section RCLike

variable {p : A → Prop} [RCLike 𝕜] [Ring A] [StarRing A] [Algebra 𝕜 A]
variable [TopologicalSpace A] [ContinuousFunctionalCalculus 𝕜 A p]
  [IsSemitopologicalRing A] [T2Space A]

open StarAlgebra.elemental in
protected theorem Commute.cfcHom {a b : A} (ha : p a) (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : C(spectrum 𝕜 a, 𝕜)) :
    Commute (cfcHom ha f) b := by
  open scoped ContinuousFunctionalCalculus in
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    conv =>
      enter [1, 2]
      equals algebraMap 𝕜 _ r => rfl
    rw [AlgHomClass.commutes]
    exact Algebra.commute_algebraMap_left r b
  | id => rwa [cfcHom_id ha]
  | star_id => rwa [map_star, cfcHom_id]
  | add f g hf hg => rw [map_add]; exact hf.add_left hg
  | mul f g hf hg => rw [map_mul]; exact mul_left hf hg
  | frequently f hf =>
    rw [commute_iff_eq, ← Set.mem_setOf (p := fun x => x * b = b * x),
      ← (isClosed_eq (by fun_prop) (by fun_prop)).closure_eq]
    apply mem_closure_of_frequently_of_tendsto hf
    exact cfcHom_continuous ha |>.tendsto _

protected theorem IsSelfAdjoint.commute_cfcHom {a b : A} (ha : p a)
    (ha' : IsSelfAdjoint a) (hb : Commute a b) (f : C(spectrum 𝕜 a, 𝕜)) :
    Commute (cfcHom ha f) b :=
  hb.cfcHom ha (ha'.star_eq.symm ▸ hb) f

/-- An element commutes with `cfc f a` if it commutes with both `a` and `star a`.

If the base ring is `ℝ` or `ℝ≥0`, see `Commute.cfc_real` or `Commute.cfc_nnreal` which don't require
the `Commute (star a) b` hypothesis. -/
@[grind ←]
protected theorem Commute.cfc {a b : A} (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : 𝕜 → 𝕜) :
    Commute (cfc f a) b :=
  cfc_cases (fun x ↦ Commute x b) a f (Commute.zero_left _)
    fun hf ha ↦ hb₁.cfcHom ha hb₂ ⟨_, hf.restrict⟩

/-- For `a` selfadjoint, an element commutes with `cfc f a` if it commutes with `a`.

If the base ring is `ℝ` or `ℝ≥0`, see `Commute.cfc_real` or `Commute.cfc_nnreal` which don't require
the `IsSelfAdjoint` hypothesis on `a` (due to the junk value `cfc f a = 0`). -/
protected theorem IsSelfAdjoint.commute_cfc {a b : A}
    (ha : IsSelfAdjoint a) (hb₁ : Commute a b) (f : 𝕜 → 𝕜) :
    Commute (cfc f a) b :=
  hb₁.cfc (ha.star_eq.symm ▸ hb₁) f

end RCLike

section NNReal

variable [Ring A] [StarRing A] [Algebra ℝ A] [TopologicalSpace A]
variable [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [IsTopologicalRing A] [T2Space A]

/-- A version of `Commute.cfc` or `IsSelfAdjoint.commute_cfc` which does not require any interaction
with `star` when the base ring is `ℝ`. -/
@[grind ←]
protected theorem Commute.cfc_real {a b : A} (hb : Commute a b) (f : ℝ → ℝ) :
    Commute (cfc f a) b :=
  cfc_cases (fun x ↦ Commute x b) a f (Commute.zero_left _) fun hf ha ↦ by
    rw [← cfc_apply ..]
    exact hb.cfc (ha.star_eq.symm ▸ hb) _

variable [PartialOrder A] [NonnegSpectrumClass ℝ A] [StarOrderedRing A]

/-- A version of `Commute.cfc` or `IsSelfAdjoint.commute_cfc` which does not require any interaction
with `star` when the base ring is `ℝ≥0`. -/
@[grind ←]
protected theorem Commute.cfc_nnreal {a b : A} (hb : Commute a b) (f : ℝ≥0 → ℝ≥0) :
    Commute (cfc f a) b := by
  by_cases ha : 0 ≤ a
  · rw [cfc_nnreal_eq_real ..]
    exact hb.cfc_real _
  · simp [cfc_apply_of_not_predicate a ha]

end NNReal

end Unital

section NonUnital

section RCLike

variable {p : A → Prop} [RCLike 𝕜] [NonUnitalRing A] [StarRing A]
variable [Module 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [TopologicalSpace A]
variable [NonUnitalContinuousFunctionalCalculus 𝕜 A p] [IsTopologicalRing A] [T2Space A]

open ContinuousMapZero

open NonUnitalStarAlgebra.elemental in
protected theorem Commute.cfcₙHom {a b : A} (ha : p a) (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : C(quasispectrum 𝕜 a, 𝕜)₀) :
    Commute (cfcₙHom ha f) b := by
  open scoped NonUnitalContinuousFunctionalCalculus in
  induction f using ContinuousMapZero.induction_on_of_compact with
  | zero => simp
  | smul r f hf => rw [map_smul]; exact hf.smul_left r
  | id => rwa [cfcₙHom_id ha]
  | star_id => rwa [map_star, cfcₙHom_id]
  | add f g hf hg => rw [map_add]; exact hf.add_left hg
  | mul f g hf hg => rw [map_mul]; exact mul_left hf hg
  | frequently f hf =>
    rw [commute_iff_eq, ← Set.mem_setOf (p := fun x => x * b = b * x),
      ← (isClosed_eq (by fun_prop) (by fun_prop)).closure_eq]
    apply mem_closure_of_frequently_of_tendsto hf
    exact cfcₙHom_continuous ha |>.tendsto _

protected theorem IsSelfAdjoint.commute_cfcₙHom {a b : A} (ha : p a)
    (ha' : IsSelfAdjoint a) (hb : Commute a b) (f : C(quasispectrum 𝕜 a, 𝕜)₀) :
    Commute (cfcₙHom ha f) b :=
  hb.cfcₙHom ha (ha'.star_eq.symm ▸ hb) f

/-- An element commutes with `cfcₙ f a` if it commutes with both `a` and `star a`.

If the base ring is `ℝ` or `ℝ≥0`, see `Commute.cfcₙ_real` or `Commute.cfcₙ_nnreal` which don't
require the `Commute (star a) b` hypothesis. -/
@[grind ←]
protected theorem Commute.cfcₙ {a b : A} (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : 𝕜 → 𝕜) :
    Commute (cfcₙ f a) b :=
  cfcₙ_cases (fun x ↦ Commute x b) a f (Commute.zero_left _)
    fun hf hf₀ ha ↦ hb₁.cfcₙHom ha hb₂ ⟨⟨_, hf.restrict⟩, hf₀⟩

/-- For `a` selfadjoint, an element commutes with `cfcₙ f a` if it commutes with `a`.

If the base ring is `ℝ` or `ℝ≥0`, see `Commute.cfcₙ_real` or `Commute.cfcₙ_nnreal` which don't
require the `IsSelfAdjoint` hypothesis on `a` (due to the junk value `cfcₙ f a = 0`). -/
protected theorem IsSelfAdjoint.commute_cfcₙ {a b : A}
    (ha : IsSelfAdjoint a) (hb₁ : Commute a b) (f : 𝕜 → 𝕜) :
    Commute (cfcₙ f a) b :=
  hb₁.cfcₙ (ha.star_eq.symm ▸ hb₁) f

end RCLike

section NNReal

variable [NonUnitalRing A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
variable [SMulCommClass ℝ A A] [TopologicalSpace A]
variable [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [IsTopologicalRing A] [T2Space A]

/-- A version of `Commute.cfcₙ` or `IsSelfAdjoint.commute_cfcₙ` which does not require any
interaction with `star` when the base ring is `ℝ`. -/
@[grind ←]
protected theorem Commute.cfcₙ_real {a b : A} (hb : Commute a b) (f : ℝ → ℝ) :
    Commute (cfcₙ f a) b :=
  cfcₙ_cases (fun x ↦ Commute x b) a f (Commute.zero_left _)
    fun hf hf0 ha ↦ by
      rw [← cfcₙ_apply ..]
      exact hb.cfcₙ (ha.star_eq.symm ▸ hb) _

variable [PartialOrder A] [NonnegSpectrumClass ℝ A] [StarOrderedRing A]

set_option backward.isDefEq.respectTransparency false in
/-- A version of `Commute.cfcₙ` or `IsSelfAdjoint.commute_cfcₙ` which does not require any
interaction with `star` when the base ring is `ℝ≥0`. -/
@[grind ←]
protected theorem Commute.cfcₙ_nnreal {a b : A} (hb : Commute a b) (f : ℝ≥0 → ℝ≥0) :
    Commute (cfcₙ f a) b := by
  by_cases ha : 0 ≤ a
  · rw [cfcₙ_nnreal_eq_real ..]
    exact hb.cfcₙ_real _
  · simp [cfcₙ_apply_of_not_predicate a ha]

end NNReal

end NonUnital
