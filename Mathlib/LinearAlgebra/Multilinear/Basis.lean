/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Eric Wieser, Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Multilinear.Finsupp

/-!
# Multilinear maps in relation to bases.

This file proves lemmas about the action of multilinear maps on basis vectors and constructs a
basis for multilinear maps given bases on the domain and codomain.

-/

@[expose] public section


open MultilinearMap

variable {ι R : Type*} [CommSemiring R]
  {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]

/-- Two multilinear maps indexed by a `Fintype` are equal if they are equal when all arguments
are basis vectors. -/
theorem Module.Basis.ext_multilinear [Finite ι] {f g : MultilinearMap R M N} {ιM : ι → Type*}
    (e : ∀ i, Basis (ιM i) R (M i))
    (h : ∀ v : (i : ι) → ιM i, (f fun i ↦ e i (v i)) = g fun i ↦ e i (v i)) : f = g := by
  cases nonempty_fintype ι
  classical
  ext m
  rcases Function.Surjective.piMap (fun i ↦ (e i).repr.symm.surjective) m with ⟨x, rfl⟩
  unfold Pi.map
  simp_rw [(e _).repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum_finset, map_smul_univ, h]

@[deprecated (since := "2025-05-12")]
alias Basis.ext_multilinear_fin := Module.Basis.ext_multilinear

namespace Basis

open Module

variable {κ : ι → Type*} (b : (i : ι) → Basis (κ i) R (M i))
  {ι' N : Type*} [AddCommMonoid N] [Module R N] (b' : Basis ι' R N)

open scoped Classical in
/-- A basis for multilinear maps given a finite basis on each domain and a basis on the codomain. -/
noncomputable def multilinearMap [Finite ι] [∀ i, Finite (κ i)] :
    Basis ((Π i, κ i) × ι') R (MultilinearMap R M N) where
  repr :=
    have : Fintype ι := Fintype.ofFinite _
    have (i : ι) : Fintype (κ i) := Fintype.ofFinite _
    LinearEquiv.multilinearMapCongrLeft (fun i => (b i).repr.symm) ≪≫ₗ
      (b'.repr).multilinearMapCongrRight R ≪≫ₗ freeFinsuppEquiv.symm

variable [Fintype ι] [∀ i, Fintype (κ i)]

theorem multilinearMap_apply (i : (Π i, κ i) × ι') :
    Basis.multilinearMap b b' i =
      ((LinearMap.id (M := R)).smulRight (b' i.2)).compMultilinearMap
        (MultilinearMap.mkPiRing R ι 1 |>.compLinearMap fun i' => (b i').coord (i.1 i')) := by
  ext x
  simp only [multilinearMap, Basis.coe_ofRepr, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, LinearEquiv.multilinearMapCongrRight_symm_apply, Basis.coe_repr_symm,
    LinearEquiv.multilinearMapCongrLeft_symm_apply, compLinearMap_apply, LinearEquiv.coe_coe,
    LinearMap.compMultilinearMap_apply, freeFinsuppEquiv_single, one_smul,
    Finsupp.linearCombination_single, Basis.coord_apply, mkPiRing_apply, smul_eq_mul, mul_one,
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, Subsingleton.elim (Fintype.ofFinite ι)]

/-- The elements of the basis are the maps which scale `b' ii.2` by the
product of all the `ii.1 ·` coordinates along `b i`. -/
theorem multilinearMap_apply_apply (ii : (Π i, κ i) × ι') (v) :
    Basis.multilinearMap b b' ii v = (∏ i, (b i).repr (v i) (ii.1 i)) • b' ii.2 := by
  simp [Basis.multilinearMap_apply]

end Basis
