/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Lie.Derivation.Basic

/-!
# Graded Lie algebras

This file defines typeclasses `SetLike.GradedBracket` and `GradedLieAlgebra`, for working with Lie
algebras that are graded by a collection `ℒ` of submodules. The additivity of degree with respect to
the bracket product is encoded by an addition condition so we can avoid the usual difficulties of
adding elements of `A (i + j)` to elements of `A (j + i)`.

## Main definitions

* `SetLike.GradedBracket`: A typeclass for a bracket to respect an additive grading.
* `GradedLieAlgebra`: A typeclass for a Lie algebra to respect an additive grading.
* `LieDerivation.ofGradingSum`: A Lie derivation on the direct sum of graded pieces, that scalar-
  multiplies the pieces by an additive map applied to degree.
* `LieDerivation.ofGrading`: A Lie derivation on a graded Lie algebra, that scalar-multiplies graded
  pieces by an additive map applied to degree.

-/

@[expose] public section

open DirectSum

variable {ι σ R L : Type*}

section SetLike

/-- A class that ensures a bracket product preserves an additive grading. -/
class SetLike.GradedBracket [SetLike σ L] [Bracket L L] [Add ι] (ℒ : ι → σ) : Prop where
  /-- Bracket is homogeneous -/
  bracket_mem : ∀ ⦃i j k⦄ {gi gj}, i + j = k → gi ∈ ℒ i → gj ∈ ℒ j → ⁅gi, gj⁆ ∈ ℒ k

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι → Submodule R L)

/-- A class that ensures a Lie algebra has a bracket that preserves a decomposition. -/
class GradedLieAlgebra extends SetLike.GradedBracket ℒ, DirectSum.Decomposition ℒ

end SetLike

namespace DirectSum

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι → Submodule R L) [GradedLieAlgebra ℒ]

instance : LieRing (⨁ i, ℒ i) where
  bracket x y := decomposeLinearEquiv ℒ
    ⁅(decomposeLinearEquiv ℒ).symm x, (decomposeLinearEquiv ℒ).symm y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp

lemma bracket_apply_apply (x y : ⨁ i, ℒ i) :
    ⁅x, y⁆ =
      decomposeLinearEquiv ℒ ⁅(decomposeLinearEquiv ℒ).symm x, (decomposeLinearEquiv ℒ).symm y⁆ :=
  rfl

attribute [local simp] bracket_apply_apply

@[simp]
lemma decompose_bracket (x y : L) : decompose ℒ ⁅x, y⁆ = ⁅decompose ℒ x, decompose ℒ y⁆ := by
  simp only [← decomposeLinearEquiv_apply]
  simp

@[simp]
lemma decompose_symm_bracket (x y : ⨁ i, ℒ i) :
    (decompose ℒ).symm ⁅x, y⁆ = ⁅(decompose ℒ).symm x, (decompose ℒ).symm y⁆ := by
  simp only [← decomposeLinearEquiv_symm_apply]
  simp

instance : LieAlgebra R (⨁ i, ℒ i) where
  add_smul _ _ _ := by simp [add_smul]
  zero_smul _ := by simp
  lie_smul _ _ _ := by simp

/-- If `L` is graded by `ι` with degree `i` component `ℒ i`, then it is isomorphic as
a Lie algebra to a direct sum of components. -/
def decomposeLieEquiv : L ≃ₗ⁅R⁆ ⨁ i, ℒ i :=
  { decomposeLinearEquiv ℒ with
    map_lie' := by simp }

end DirectSum

namespace LieDerivation

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι → Submodule R L) [GradedLieAlgebra ℒ]

/-- A derivation on the direct sum of graded pieces of a graded Lie algebra, induced by an additive
map on the grading monoid. -/
def ofGradingSum (φ : ι →+ R) : LieDerivation R (⨁ i, ℒ i) (⨁ i, ℒ i) :=
  { __ := DirectSum.toModule R ι (⨁ i, ℒ i)
      fun i ↦ (lof R ι (ℒ ·) i).comp (Module.End.smulLeft (φ i) (by simp))
    leibniz' x y := by
      have hM (k : ι) (b : ⨁ i, ℒ i) (hb : (decompose ℒ).symm b ∈ ℒ k) :
          (toModule R ι (⨁ (i : ι), ℒ i) fun i ↦ lof R ι (ℒ ·) i ∘ₗ (φ i • .id)) b = (φ k) • b := by
        obtain ⟨_, rfl⟩ : b ∈ LinearMap.range (lof R ι (ℒ ·) k) := by
          use ⟨(decompose ℒ).symm b, hb⟩
          simp [lof_eq_of, ← decompose_of_mem]
        simp
      ext j
      induction x using DirectSum.induction_on' with
      | h0 => simp
      | hadd i a f _ _ ih =>
        simp only [Module.End.smulLeft_eq, DirectSum.sub_apply, AddSubgroupClass.coe_sub] at ih
        simp only [Module.End.smulLeft_eq, add_lie, map_add, DirectSum.add_apply, Submodule.coe_add,
          ih, lie_add, DirectSum.sub_apply, AddSubgroupClass.coe_sub]
        rw [add_sub_add_comm, add_right_cancel_iff, hM i (of (ℒ ·) i a) (by simp)]
        clear ih
        induction y using DirectSum.induction_on' with
        | h0 => simp
        | hadd k b f _ _ ih =>
          simp only [lie_add, map_add, DirectSum.add_apply, Submodule.coe_add, ih, lie_smul,
            add_lie, smul_add, add_sub, ← sub_sub]
          congr 1
          have : (decompose ℒ).symm ⁅of (fun i ↦ ℒ i) i a, of (fun i ↦ ℒ i) k b⁆ ∈ ℒ (i + k) := by
            simp [SetLike.GradedBracket.bracket_mem rfl (Submodule.coe_mem a) (Submodule.coe_mem b)]
          rw [hM _ _ this, hM k (of (ℒ ·) k b) (by simp), ← lie_skew (of (ℒ ·) k b),
            add_sub_right_comm, add_right_cancel_iff, add_comm i k, map_add, add_smul,
            DirectSum.add_apply, Submodule.coe_add, sub_eq_add_neg, lie_smul, add_left_cancel_iff,
            smul_neg, ← sub_eq_zero, sub_neg_eq_add, ← Submodule.coe_add, Submodule.coe_eq_zero,
            ← DirectSum.add_apply, add_neg_cancel, DirectSum.zero_apply] }

@[simp]
lemma ofGradingSum_of (φ : ι →+ R) (i : ι) (a : ℒ i) :
    ofGradingSum ℒ φ (of (ℒ ·) i a) = (φ i) • (of (ℒ ·) i a) := by
  simp [← lof_eq_of R, ofGradingSum]

/-- The Lie derivation on a graded Lie algebra that scalar-multiplies by an additive function of
the degree. -/
def ofGrading (φ : ι →+ R) :
    LieDerivation R L L where
  toFun x := (decomposeLinearEquiv ℒ).symm <| ofGradingSum ℒ φ <| decomposeLinearEquiv ℒ x
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  leibniz' x y := by simp [decomposeLinearEquiv_apply, decomposeLinearEquiv_symm_apply]

lemma ofGrading_apply_apply (φ : ι →+ R) {i : ι} {a : L} (ha : a ∈ ℒ i) :
    ofGrading ℒ φ a = φ i • a := by
  simp [ofGrading, decomposeLinearEquiv_apply, decompose_of_mem ℒ ha]
  simp [decomposeLinearEquiv_symm_apply]

end LieDerivation
