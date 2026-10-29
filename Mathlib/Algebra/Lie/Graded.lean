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
algebras that are graded by a collection `ℒ` of submodules.

## Main definitions

* `SetLike.GradedBracket`: A typeclass for a bracket to be compatible with a vector-additive
  grading.
* `GradedLieAlgebra`: A typeclass for a Lie algebra bracket to respect an additive grading.
* `GradedLieModule`: A typeclass for a Lie module to be compatible with a vector-additive grading.
* `LieDerivation.ofGradingSum`: A Lie derivation on the direct sum of graded pieces, that scalar-
  multiplies the pieces by an additive map applied to degree.
* `LieDerivation.ofGrading`: A Lie derivation on a graded Lie algebra, that scalar-multiplies graded
  pieces by an additive map applied to degree.

## Implementation notes

For now we only implement internally-graded Lie algebras; supporting the externally-graded case
would be achieved by generalizing the `LieRing (⨁ i, ℒ i)` instance to take a family of types,
and defining a new `GradedMonoid.GBracket` class to provide the data piecewise.

-/

@[expose] public section

open DirectSum

variable {ι κ σ τ R L M : Type*}

section SetLike

/-- A `graded bracket` class that ensures a bracket action preserves a vector-additive grading. -/
class SetLike.GradedBracket [SetLike σ L] [SetLike τ M] [Bracket L M] [VAdd ι κ] (ℒ : ι → σ)
    (ℳ : κ → τ) : Prop where
  /-- Bracket is homogeneous -/
  bracket_mem : ∀ ⦃i j⦄ {gi hj}, gi ∈ ℒ i → hj ∈ ℳ j → ⁅gi, hj⁆ ∈ ℳ (i +ᵥ j)

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι → Submodule R L) [DecidableEq κ] [VAdd ι κ] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M] (ℳ : κ → Submodule R M)

/-- A class that ensures a Lie algebra has a bracket that preserves a decomposition. -/
class GradedLieAlgebra extends SetLike.GradedBracket ℒ ℒ, DirectSum.Decomposition ℒ

/-- A class that ensures a Lie algebra has a bracket that preserves a decomposition. -/
class GradedLieModule [GradedLieAlgebra ℒ] [DirectSum.Decomposition ℳ] extends
    SetLike.GradedBracket ℒ ℳ

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

lemma bracket_apply_apply_self (x y : ⨁ i, ℒ i) :
    ⁅x, y⁆ =
      decomposeLinearEquiv ℒ ⁅(decomposeLinearEquiv ℒ).symm x, (decomposeLinearEquiv ℒ).symm y⁆ :=
  rfl

attribute [local simp] bracket_apply_apply_self

variable [DecidableEq κ] [AddCommGroup M] [Module R M] [LieRingModule L M]
  (ℳ : κ → Submodule R M) [DirectSum.Decomposition ℳ]

instance : LieRingModule (⨁ i, ℒ i) (⨁ k, ℳ k) where
  bracket x y := decomposeLinearEquiv ℳ
    ⁅(decomposeLinearEquiv ℒ).symm x, (decomposeLinearEquiv ℳ).symm y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  leibniz_lie _ _ _ := by simp

lemma bracket_apply_apply (x : ⨁ i, ℒ i) (y : ⨁ k, ℳ k) :
    ⁅x, y⁆ =
      decomposeLinearEquiv ℳ ⁅(decomposeLinearEquiv ℒ).symm x, (decomposeLinearEquiv ℳ).symm y⁆ :=
  rfl

attribute [local simp] bracket_apply_apply

lemma decompose_bracket (x : L) (y : M) :
    decompose ℳ ⁅x, y⁆ = ⁅decompose ℒ x, decompose ℳ y⁆ := by
  simp only [← decomposeLinearEquiv_apply, bracket_apply_apply]
  simp

@[simp]
lemma decompose_symm_bracket (x : ⨁ i, ℒ i) (y : ⨁ k, ℳ k) :
    (decompose ℳ).symm ⁅x, y⁆ = ⁅(decompose ℒ).symm x, (decompose ℳ).symm y⁆ := by
  simp only [← decomposeLinearEquiv_symm_apply, bracket_apply_apply]
  simp

instance : LieAlgebra R (⨁ i, ℒ i) where
  add_smul _ _ _ := by simp [add_smul]
  zero_smul _ := by simp
  lie_smul _ _ _ := by simp

instance [LieModule R L M] : LieModule R (⨁ i, ℒ i) (⨁ k, ℳ k) where
  smul_lie _ _ _ := by simp
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
            simp [← vadd_eq_add,
              SetLike.GradedBracket.bracket_mem (Submodule.coe_mem a) (Submodule.coe_mem b)]
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
  leibniz' x y := by
    simp [decomposeLinearEquiv_apply, decomposeLinearEquiv_symm_apply,
      Equiv.symm_apply_eq (decompose ℒ)]
    simp [decompose_bracket ℒ]

lemma ofGrading_apply_apply (φ : ι →+ R) {i : ι} {a : L} (ha : a ∈ ℒ i) :
    ofGrading ℒ φ a = φ i • a := by
  simp [ofGrading, decomposeLinearEquiv_apply, decompose_of_mem ℒ ha]
  simp [decomposeLinearEquiv_symm_apply]

end LieDerivation
