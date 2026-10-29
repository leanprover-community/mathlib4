/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.FunLike
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Bases and scalar multiplication

This file defines the scalar multiplication of bases by multiplying each basis vector.

-/

@[expose] public section

assert_not_exists Ordinal

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι R R₂ M : Type*}

namespace Module.Basis
variable [Semiring R] [AddCommMonoid M] [Module R M] (b : Basis ι R M)

section SMul
variable {G G'}
variable [Group G] [Group G']
variable [DistribMulAction G M] [DistribMulAction G' M]
variable [SMulCommClass G R M] [SMulCommClass G' R M]

/-- The action on a `Basis` by acting on each element.

See also `Basis.unitsSMul` and `Basis.groupSMul`, for the cases when a different action is applied
to each basis element. -/
instance : SMul G (Basis ι R M) where
  smul g b := b.map <| DistribMulAction.toLinearEquiv _ _ g

instance : IsSMulApply G (Basis ι R M) where

@[deprecated _root_.smul_apply +typeChanged (since := "2026-10-26")]
protected theorem smul_apply (g : G) (b : Basis ι R M) (i : ι) : (g • b) i = g • b i := rfl

@[deprecated FunLike.coe_smul +typeChanged (since := "2026-10-26")]
theorem coe_smul (g : G) (b : Basis ι R M) : ⇑(g • b) = g • ⇑b := rfl

/-- When the group in question is the automorphisms, `•` coincides with `Basis.map`. -/
@[simp]
theorem smul_eq_map (g : M ≃ₗ[R] M) (b : Basis ι R M) : g • b = b.map g := rfl

@[simp] theorem repr_smul (g : G) (b : Basis ι R M) :
    (g • b).repr = (DistribMulAction.toLinearEquiv _ _ g).symm.trans b.repr := rfl

instance : MulAction G (Basis ι R M) := fast_instance% FunLike.mulAction

instance [SMulCommClass G G' M] : SMulCommClass G G' (Basis ι R M) := FunLike.smulCommClass

instance [SMul G G'] [IsScalarTower G G' M] : IsScalarTower G G' (Basis ι R M) :=
  FunLike.isScalarTower

end SMul

section CommSemiring

variable {v : ι → M} {x y : M}

theorem groupSMul_span_eq_top {G : Type*} [Group G] [SMul G R] [MulAction G M]
    [IsScalarTower G R M] {v : ι → M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι → G} :
    Submodule.span R (Set.range (w • v)) = ⊤ := by
  rw [eq_top_iff]
  intro j hj
  rw [← hv] at hj
  rw [Submodule.mem_span] at hj ⊢
  refine fun p hp => hj p fun u hu => ?_
  obtain ⟨i, rfl⟩ := hu
  have : ((w i)⁻¹ • (1 : R)) • w i • v i ∈ p := p.smul_mem ((w i)⁻¹ • (1 : R)) (hp ⟨i, rfl⟩)
  rwa [smul_one_smul, inv_smul_smul] at this

/-- Given a basis `v` and a map `w` such that for all `i`, `w i` are elements of a group,
`groupSMul` provides the basis corresponding to `w • v`. -/
def groupSMul {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] [SMulCommClass G R M] (v : Basis ι R M) (w : ι → G) : Basis ι R M :=
  Basis.mk (LinearIndependent.group_smul v.linearIndependent w) (groupSMul_span_eq_top v.span_eq).ge

theorem groupSMul_apply {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] [SMulCommClass G R M] {v : Basis ι R M} {w : ι → G} (i : ι) :
    v.groupSMul w i = (w • (v : ι → M)) i :=
  mk_apply (LinearIndependent.group_smul v.linearIndependent w)
    (groupSMul_span_eq_top v.span_eq).ge i

theorem units_smul_span_eq_top {v : ι → M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι → Rˣ} :
    Submodule.span R (Set.range (w • v)) = ⊤ :=
  groupSMul_span_eq_top hv

/-- Given a basis `v` and a map `w` such that for all `i`, `w i` is a unit, `unitsSMul`
provides the basis corresponding to `w • v`. -/
def unitsSMul (v : Basis ι R M) (w : ι → Rˣ) : Basis ι R M :=
  Basis.mk (LinearIndependent.units_smul v.linearIndependent w)
    (units_smul_span_eq_top v.span_eq).ge

theorem unitsSMul_apply {v : Basis ι R M} {w : ι → Rˣ} (i : ι) : unitsSMul v w i = w i • v i :=
  mk_apply (LinearIndependent.units_smul v.linearIndependent w)
    (units_smul_span_eq_top v.span_eq).ge i

variable [CommSemiring R₂] [Module R₂ M]

@[simp]
theorem coord_unitsSMul (e : Basis ι R₂ M) (w : ι → R₂ˣ) (i : ι) :
    (unitsSMul e w).coord i = (w i)⁻¹ • e.coord i := by
  classical
    apply e.ext
    intro j
    trans ((unitsSMul e w).coord i) ((w j)⁻¹ • (unitsSMul e w) j)
    · simp [Basis.unitsSMul, ← mul_smul]
    simp only [Basis.coord_apply, LinearMap.smul_apply, Basis.repr_self, Units.smul_def,
      map_smul, Finsupp.single_apply]
    split_ifs with h <;> simp [h]

@[simp]
theorem repr_unitsSMul (e : Basis ι R₂ M) (w : ι → R₂ˣ) (v : M) (i : ι) :
    (e.unitsSMul w).repr v i = (w i)⁻¹ • e.repr v i :=
  congr($(e.coord_unitsSMul w i) v)

/-- A version of `unitsSMul` that uses `IsUnit`. -/
def isUnitSMul (v : Basis ι R M) {w : ι → R} (hw : ∀ i, IsUnit (w i)) : Basis ι R M :=
  unitsSMul v fun i => (hw i).unit

theorem isUnitSMul_apply {v : Basis ι R M} {w : ι → R} (hw : ∀ i, IsUnit (w i)) (i : ι) :
    v.isUnitSMul hw i = w i • v i :=
  unitsSMul_apply i

theorem repr_isUnitSMul {v : Basis ι R₂ M} {w : ι → R₂} (hw : ∀ i, IsUnit (w i)) (x : M) (i : ι) :
    (v.isUnitSMul hw).repr x i = (hw i).unit⁻¹ • v.repr x i :=
  repr_unitsSMul _ _ _ _

end CommSemiring
end Module.Basis
