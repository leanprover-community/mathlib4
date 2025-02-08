/-
Copyright (c) 2024 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
import Mathlib.RingTheory.FilteredAlgebra.Basic
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic.LinearCombination'
/-!
# The filtration on abelian group and ring
In this file, we defined the fitration induced by a homomorphism,
and extend it to get the filtration on ring and module.

# Main definitions
* `SetLikeHom` This class adds the necessary conditions to describe `σA` and `σB`, ensuring that f
can induce a map from σA to σB. In this way, we can define `FB` and `FB_lt` under very weak
conditions.

* `HomtoFiltration` If `FA` and `FA_lt` is a filtration of A, then a map f: A → B induces a
filtration of B, which we call `FB` and `FB_lt`

* `RingHomtoFiltration` If `FA` and `FA_lt` is a ring filtration of A, then a ring homomorphism
 f: A →+* B induces a ring filtration of B, which we call `FB` and `FB_lt`

* `ModuleHomtoFiltration` When FM and FM_lt is a filtration of M, then a module homomorphism
 f: M → N induces a module filtration of N, which we call `FB` and `FB_lt`-/

variable {ι : Type*} [OrderedCancelAddCommMonoid ι]

section HomtoFiltration

variable {A : Type*} (σA : Type*) [SetLike σA A] {B : Type*} (σB : Type*) [SetLike σB B]

/-- It add some necessary conditions to describe σA and σB,ensure f can induce a map from σA → σB.-/
class SetLikeHom (f : A → B) where
  /-- It is the corresponding map from σA → σB with `coe_map` property -/
  map : σA → σB
  /-- It is a map from σB → σA with `galois` property-/
  comap : σB → σA
  coe_map (x : σA) : f '' (x : Set A) = map x
  /-- the design of `GaloisConnection` avoid adding `Preorder` to `σA` and `σB`, there are also
  theorems such as `Subgroup.gc_map_comap` to handle different conditions in the similar structures.
  -/
  galois : GaloisConnection map comap



open SetLikeHom Set
/-- It is `F` part of the filtration induced by f: A → B -/
def FB (FA : ι → σA) (f : A → B) [SetLikeHom σA σB f]: ι → σB := fun i ↦ map f (FA i)
/-- It is `F_lt` part of the filtration induced by f: A → B -/
def FB_lt (FA_lt : ι → σA) (f : A → B) [SetLikeHom σA σB f] : outParam <| ι → σB :=
 fun i ↦ map f (FA_lt i)

/-- When FA and FA_lt is a filtration of A, then f: A → B induce a filtration of B which is called
`FB` and `FB_lt`-/
instance HomtoFiltration (FA FA_lt : ι → σA) (f : A → B) [fil : IsFiltration FA FA_lt]
[SetLikeHom σA σB f] : IsFiltration (FB σA σB FA f) (FB_lt σA σB FA_lt f) (ι := ι) where
  mono {i j i_le_j}:= by
    show (((map f <| FA i) : σB) : Set B) ≤ (((map f <| FA j) : σB) : Set B)
    rw[← coe_map <| FA i, ← coe_map <| FA j]
    exact le_iff_subset.mpr <| image_mono <| IsFiltration.mono i_le_j
  is_le {i j i_lt_j}:= by
    show (((map f <| FA i) : σB) : Set B) ≤ (((map f <| FA_lt j) : σB) : Set B)
    rw[← coe_map <| FA i, ← coe_map <| FA_lt j]
    exact le_iff_subset.mpr <| image_mono <| IsFiltration.is_le i_lt_j
  is_sup {Sup j h}:= by
    apply galois.l_le
    have h : ∀ i < j, FA i ≤ comap f Sup := fun i i_lt_j ↦ galois.le_u <| h i i_lt_j
    exact IsFiltration.is_sup (comap f Sup) j h

end HomtoFiltration



section RingHomtoFiltration

variable {R : Type*} [Ring R] (σR : Type*) [SetLike σR R] [AddSubgroupClass σR R] {S : Type*}
 [Ring S] (σS : Type*) [SetLike σS S] [AddSubgroupClass σS S]

/-- It is `F` part of the ring filtration induced by f: A →+* B -/
def FS (FR : ι → σR)(f : R →+* S)[SetLikeHom σR σS f] :  ι → σS := FB σR σS FR f

/-- It is `F_lt` part of the ring filtration induced by f: A →+* B -/
def FS_lt (FR_lt : ι → σR) (f : R →+* S) [SetLikeHom σR σS f] :
outParam <| ι → σS := FB_lt σR σS FR_lt f

variable (FR : ι → σR) (FR_lt : outParam <| ι → σR) (f : R →+* S) [IsRingFiltration FR FR_lt]
[SetLikeHom σR σS f]

open SetLikeHom Set
/- When FA and FA_lt is a ring filtration of A, then ring hom f: A →+* B induce a ring filtration
 of B which is called `FB` and `FB_lt` -/
instance RingHomtoFiltration (FR FR_lt: ι → σR) [fil : IsRingFiltration FR FR_lt] :
    IsRingFiltration (FS σR σS FR f) (FS_lt σR σS FR_lt f) where
  __ := HomtoFiltration σR σS FR FR_lt f
  one_mem := by
    show 1 ∈ ((map f <| FR 0 : σS) : Set S)
    rw[← coe_map <| FR 0]
    use 1
    simp only [SetLike.mem_coe, IsRingFiltration.one_mem, map_one, and_self]
  mul_mem {i j x y x_in_i y_in_j}:= by
    show x * y ∈ ((map f <| FR <| i + j : σS) : Set S)
    rw[← coe_map <| FR <| i + j]
    have x_in_i : x ∈ ((map f (FR i) : σS) : Set S) := x_in_i
    rw[← coe_map <| FR i] at x_in_i
    have y_in_j : y ∈ ((map f (FR j) : σS) : Set S) := y_in_j
    rw[← coe_map <| FR j] at y_in_j
    obtain ⟨x₁, x_in, x_eq⟩ := x_in_i
    obtain ⟨y₁, y_in, y_eq⟩ := y_in_j
    use x₁ * y₁
    simp only [SetLike.mem_coe, IsRingFiltration.mul_mem x_in y_in, map_mul,
      Mathlib.Tactic.LinearCombination'.mul_pf x_eq y_eq, and_self]

end RingHomtoFiltration



section ModuleHomtoFiltration

variable {R : Type*} [Ring R] (σR : Type*) [SetLike σR R] [AddSubgroupClass σR R]
variable (FR : ι → σR) (FR_lt : outParam <| ι → σR) [fil : IsRingFiltration FR FR_lt]

variable {M : Type*} [AddCommMonoid M] [Module R M] (σM : Type*) [SetLike σM M]
[AddSubmonoidClass σM M] [SMulMemClass σM R M] (FM : ι → σM) (FM_lt : outParam <| ι → σM)

variable {N : Type*} [AddCommMonoid N] [Module R N] (σN : Type*) [SetLike σN N]
[AddSubmonoidClass σN N] [SMulMemClass σN R N]

variable [filM : IsModuleFiltration FR FR_lt FM FM_lt] (f : M →ₗ[R] N)

/-- It is `F'` part of the module filtration induced by f: A →+* B -/
def FN (FM : ι → σM) (f : M →ₗ[R] N) [SetLikeHom σM σN f] : ι → σN := FB σM σN FM f

/-- It is `F'_lt` part of the module filtration induced by f: A →+* B -/
def FN_lt (FM_lt : ι → σM) (f : M →ₗ[R] N) [SetLikeHom σM σN f] : outParam <| ι → σN :=
 FB_lt σM σN FM_lt f

/- When FM and FM_lt is a filtration of M, then module hom f: M → N induce a module filtration of B
 which is called `FB` and `FB_lt`-/
open SetLikeHom
instance ModuleHomtoFiltration [SetLikeHom σM σN f] :
    IsModuleFiltration FR FR_lt (FN σM σN FM f) (FN_lt σM σN FM_lt f) where
  __ := HomtoFiltration σM σN (f := f.toFun) (ι := ι) (FA := FM) (FA_lt := FM_lt)
  smul_mem {i j r n hr hn}:= by
    have hn : n ∈ ((map f <| FM j : σN) : Set N) := hn
    rw[← coe_map <| FM j] at hn
    obtain⟨m, hm, heq⟩ := hn
    show r • n ∈ ((map f (FM <| i + j) : σN) : Set N)
    rw[← coe_map <| FM (i + j), ← heq, ← (LinearMap.CompatibleSMul.map_smul f r m)]
    use r • m
    have := IsModuleFiltration.smul_mem hr hm
    rw[vadd_eq_add] at this
    simp only [SetLike.mem_coe, this, map_smul, and_self]

end ModuleHomtoFiltration
