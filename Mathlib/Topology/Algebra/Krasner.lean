/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/

import Mathlib.Topology.Algebra.Valuation
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Topology.Defs.Induced
import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.NormedValued
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Connected.Separation

/-!
# TODO:
1. delete IsConjSet
2. decompose val_eq

# Krasner's Lemma

In this file, we define the type class for field extensions that Krasner's lemma holds and prove
that for extensions between complete non-archimediean fields, the Krasner's lemma hold.

Let `A` be a valued `R` algebra. We say that the Krasner's property holds for `A` over `R`, if for
any pair of elements `x y` in `A` satisfying that for all conjugates `x'` of `x` over `R` not
equal to `x`, `|x - y| < |x - x'|`, we have `y` falls in the image of `R` in `A` adjoining `x`.

## Main Definition

* `IsKrasner R A` : `A` over `R` satisfies the Krasner's property

## Reference

## Tag
Krasner's lemma, Valued, Non-archimedean field
-/

variable {R : Type*} {A : Type*} [CommRing R] [Ring A] [Algebra R A]

variable (K : Type*) {L : Type*} {Γ : outParam Type*} [LinearOrderedCommGroupWithZero Γ] [Field K] [Field L] [Algebra K L] [vL : Valued L Γ]

section conj

variable (R) in
def IsConjRoot (x x' : A) : Prop := (minpoly R x) = (minpoly R x')
-- Galois action

namespace IsConjRoot

theorem refl {x : A} : IsConjRoot R x x := sorry

theorem symm {x x' : A} (h : IsConjRoot R x x') : IsConjRoot R x' x := sorry -- Eq.symm h

theorem trans {x x' x'': A} (h₁ : IsConjRoot R x x') (h₂ : IsConjRoot R x' x'') : IsConjRoot R x x'' := sorry

theorem of_minpoly_eq {x x' : A} (h : minpoly R x = minpoly R x') : IsConjRoot R x x' := sorry

theorem algEquiv_apply (x : A) (s : A ≃ₐ[R] A) : IsConjRoot R x (s x) := sorry

theorem algEquiv_apply' (x : A) (s₁ s₂ : A ≃ₐ[R] A) : IsConjRoot R (s₁ x) (s₂ x) := sorry

theorem eq_of_isConjRoot_algebraMap {r : R} {x : A} (h : IsConjRoot R x (algebraMap R A r)) : x = algebraMap R A r := sorry

theorem neg {x x' : A} (r : R) (h : IsConjRoot R x x') :  IsConjRoot R (-x) (-x') := sorry

theorem add_algebraMap {x x' : A} (r : R) (h : IsConjRoot R x x') :  IsConjRoot R (x + algebraMap R A r) (x' + algebraMap R A r) := sorry

theorem sub_algebraMap {x x' : A} (r : R) (h : IsConjRoot R x x') :  IsConjRoot R (x - algebraMap R A r) (x' - algebraMap R A r) := sorry

theorem smul {x x' : A} (r : R) (h : IsConjRoot R x x') :  IsConjRoot R (r • x) (r • x') := sorry

variable (R) in
theorem of_isScalarTower {S : Type*} [CommRing S] [Algebra R S] [Algebra S A] [IsScalarTower R S A] {x x' : A} (h : IsConjRoot S x x') : IsConjRoot R x x' := sorry

variable {K} in
theorem not_mem_iff_exist_ne {x : L} (sep : (minpoly K x).Separable) : x ∉ (⊥ : Subalgebra K L) ↔ ∃ x' : L, x ≠ x' ∧ IsConjRoot K x x' := sorry

variable {K} in
theorem isIntegral {x x' : L} (hx : IsIntegral K x) (h : IsConjRoot K x x') : IsIntegral K x' := by sorry

theorem iff_eq_zero {x : A} : IsConjRoot R 0 x ↔ x = 0 := sorry

theorem ne_zero {x x' : A} (hx : x ≠ 0) (h : IsConjRoot R x x') : x' ≠ 0 := sorry

end IsConjRoot

-- Key theorem -- K with restriction topology
-- theorem Polynomial.val_coeff_pow_natDegree [vR : Valued R Γ] [vR.v.RankOne] (f : Polynomial R) (h : Irreducible f) (hm : f.Monic) (i : ℕ) : vR.v (f.coeff i) ^ (f.natDegree) ≤ vR.v (f.coeff 0) ^ (f.natDegree - i) := sorry

-- theorem Polynomial.val_coeff_pow_natDegree' [vR : Valued R Γ] [vR.v.RankOne] (f : Polynomial R) (h : Irreducible f) (hm : f.Monic) (h0 : vR.v (f.coeff 0) = 1) (i : ℕ) : vR.v (f.coeff i) ^ (f.natDegree) ≤ 1 := sorry

theorem val_algebraMap_minpoly_coeff_le_iff_val_le_one (v : Valuation L Γ) (x : L) (hx : IsIntegral K x) : (∀ i : ℕ, v (algebraMap K L ((minpoly K x).coeff i)) ≤ 1) ↔ v x ≤ 1 := by sorry

theorem minpoly_inv_eq (x : L) : minpoly K x⁻¹ = ((minpoly K x).coeff 0)⁻¹ • (minpoly K x).reverse := sorry

variable {K} in
theorem IsIntegral.inv {x : L} (h : IsIntegral K x) : IsIntegral K x⁻¹ := sorry

variable {K} in
theorem IsIntegral.div {x y : L} (hx : IsIntegral K x) (hx : IsIntegral K y) : IsIntegral K (x/y) := sorry

theorem IsConjRoot.val_eq [UniformSpace K] [CompleteSpace K] [vL.v.RankOne] (h : Embedding (algebraMap K L)) {x x' : L} (hx : IsIntegral K x) (h : IsConjRoot K x x') : vL.v x = vL.v x' := by
  by_cases h0 : x = 0
  simp only [h0, map_zero, IsConjRoot.iff_eq_zero.mp (h0 ▸ h)]
  let y := x/x'
  have hy : IsIntegral K y := hx.div (IsConjRoot.isIntegral hx h)
  suffices vL.v y = 1 by sorry
  by_cases g : vL.v y ≤ 1
  · let F := minpoly K y
    have : F.coeff 0 = 1 := sorry -- need calculation to show
    have : vL.v y⁻¹ ≤ 1 := by
      rw [← val_algebraMap_minpoly_coeff_le_iff_val_le_one (K := K) vL.v _ hy.inv, show minpoly K y⁻¹ = (minpoly K y).reverse by simpa [this] using minpoly_inv_eq K y]
      intro i
      rw [Polynomial.coeff_reverse]
      exact ((val_algebraMap_minpoly_coeff_le_iff_val_le_one K vL.v y) hy).mpr g _
    simp only [map_inv₀, inv_le_one₀ <| vL.v.ne_zero_iff.mpr <| div_ne_zero h0 (h.ne_zero h0)] at this
    exact eq_of_le_of_le g this
  · sorry -- use y⁻¹ instead of y


-- show this for x in vL.v.integer
-- x algebraic/v.integer same as x'
-- show x/x' in (vL.v.integer)ˣ, one of x/x', x'/x falls in, minpoly has every coefficient val ≤ 1, and a₀ = 1! => the inverse also satiesfies an monic poly, coeffents ≤ 1, => the inverse is integer.
-- v (x/x') is one




/-

#check Polynomial.roots
def conjRootSet (R : Type*) {A : Type*} [CommRing R] [Ring A] [Algebra R A] (x : A) : Set A := {x' | IsConjRoot R x x'}

theorem finite {x : A} (h : IsIntegral R x) : Set.Finite {x' | IsConjRoot R x x'} := sorry

-- open Classical in
-- noncomputable def conjRootSet (R : Type*) {A : Type*} [CommRing R] [Ring A] [Algebra R A] (x : A) : Finset A :=
--   if h : IsIntegral R x then Set.Finite.toFinset (IsConjRoot.finite h) else ∅

theorem conjRootSet.self_mem (x : A) : x ∈ conjRootSet R x := sorry

-- theorem mem_of_conj_eq_singleton (x : L) (sep : (minpoly K x).Separable) [Subsingleton (conjRootSet K x)] : x ∈ (⊥ : Subalgebra K L) := sorry

variable {K} in
theorem not_mem_iff_nontrvial {x : L} (sep : (minpoly K x).Separable) : x ∉ (⊥ : Subalgebra K L) ↔ Nontrivial (conjRootSet K x) := sorry

-/


end conj

section Separable
-- do we need elementwise IsSeparable (just like IsIntegral) and rename old one into Field.IsSeparable

theorem Polynomial.Separable.minpoly_add {x y : A} (hx : (minpoly R x).Separable) (hy : (minpoly R y).Separable) : (minpoly R (x + y)).Separable := sorry

theorem Polynomial.Separable.minpoly_neg {x : A} (hx : (minpoly R x).Separable) : (minpoly R (-x)).Separable := sorry

theorem Polynomial.Separable.minpoly_sub {x y : A} (hx : (minpoly R x).Separable) (hy : (minpoly R y).Separable) : (minpoly R (x - y)).Separable := sorry

-- theorem Polymonial.Separable.minpoly_mul

-- smul

-- pow

variable (A : Type*) {B : Type*} [Field A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem Polynomial.minpoly_separable_of_isScalarTower {x : B} (h : (minpoly R x).Separable) : (minpoly A x).Separable := by
  apply Polynomial.Separable.of_dvd (Polynomial.Separable.map h)
  exact minpoly.dvd_map_of_isScalarTower R A x

end Separable

section RankOne

instance Valuation.RankOne.comap (v : Valuation A Γ) [h : v.RankOne] : (v.comap (algebraMap R A)).RankOne where
  hom := h.hom
  strictMono' := h.strictMono'
  nontrivial' := sorry

end RankOne
-- section topology

-- variable {X Y} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
-- #check IsClosed.isComplete
-- def ClosedEmbedding.uniformSpace [UniformSpace Y] (h : ClosedEmbedding f) : UniformSpace X := sorry

-- def ClosedEmbedding.completeSpace [UniformSpace Y] [CompleteSpace Y] (h : ClosedEmbedding f) : @CompleteSpace X (h.uniformSpace) := sorry

-- end topology

section valuedfield

instance : TotallySeparatedSpace L := sorry

instance (R : Type*) [Ring R] [UniformSpace R] [UniformAddGroup R] (M : Subring R) : UniformAddGroup M := sorry

variable (M : Subfield L)
#synth UniformAddGroup M

end valuedfield

section krasner

open Algebra
open IntermediateField

variable (L) in
class IsKrasner : Prop where
  krasner' : ∀ {x y : L}, (minpoly K x).Separable → IsIntegral K y →
    (∀ x' : L, IsConjRoot K x x' →  x ≠ x' → vL.v (x - y) < vL.v (x - x')) →
      x ∈ K⟮y⟯

namespace IsKrasner

variable [IsKrasner K L]

theorem krasner {x y : L} (hx : (minpoly K x).Separable) (hy : IsIntegral K y) (h : (∀ x' : L, IsConjRoot K x x' → x ≠ x' → vL.v (x - y) < vL.v (x - x'))) : x ∈ K⟮y⟯ := IsKrasner.krasner' hx hy h
-- Algebra.adjoin R {x} ≤ Algebra.adjoin R {y}

-- #check FiniteDimensional.complete
#check TotallySeparatedSpace.t2Space
-- more is needed, K has restriction topology, or embedding

instance id : IsKrasner L L := sorry

instance of_discrete : sorry := sorry

theorem of_complete [u : UniformSpace K] [c : CompleteSpace K] [vL.v.RankOne] (h : Embedding (algebraMap K L)) : IsKrasner K L := by
  constructor
  intro x y xsep hyK hxy
  let z := x - y
  let M := K⟮y⟯
  let FDM := IntermediateField.adjoin.finiteDimensional hyK
  let I'' : UniformAddGroup M := inferInstanceAs (UniformAddGroup M.toSubfield)
  let vK : Valued K Γ := Valued.mk' (vL.v.comap (algebraMap K L))
  let vKrankone : vK.v.RankOne := Valuation.RankOne.comap vL.v
  let NFK : NormedField K := vK.toNormedField
  let NNFK : NontriviallyNormedField K := {
    NFK with
    non_trivial := sorry
  }
  let CSMul : ContinuousSMul K M := sorry
  have : u = NFK.toUniformSpace := sorry
  subst this
  let hM : Embedding (algebraMap M L) := Function.Injective.embedding_induced Subtype.val_injective -- M with UniformSpace already, as subspace of L
  letI : CompleteSpace M := FiniteDimensional.complete K M-- @FiniteDimensional.complete K M sorry sorry _ _ _ sorry _ _ _  -- this need all topology on M is the same and complete?
  have hy : y ∈ K⟮y⟯ := IntermediateField.subset_adjoin K {y} rfl
  have zsep : (minpoly M z).Separable := by
    apply Polynomial.Separable.minpoly_sub (Polynomial.minpoly_separable_of_isScalarTower M xsep)
    simpa only using
      minpoly.eq_X_sub_C_of_algebraMap_inj (⟨y, hy⟩ : M)
          (NoZeroSMulDivisors.algebraMap_injective (↥M) L) ▸
        Polynomial.separable_X_sub_C (x := (⟨y, hy⟩ : M))
  suffices z ∈ K⟮y⟯ by simpa [z] using add_mem this hy
  by_contra hnin
  have : z ∈ K⟮y⟯ ↔ z ∈ (⊥ : Subalgebra M L) := by simp [Algebra.mem_bot]
  rw [this.not] at hnin
  obtain ⟨z', hne, h1⟩ := (IsConjRoot.not_mem_iff_exist_ne zsep).mp hnin
  -- rw [not_mem_iff_nontrvial zsep] at hnin
  -- obtain ⟨⟨z', h1⟩, hne⟩ := exists_ne (⟨z, conjRootSet.self_mem z⟩ : { x // x ∈ conjRootSet M z })
  simp only [ne_eq, Subtype.mk.injEq] at hne
  -- simp only [conjRootSet, Set.coe_setOf, Set.mem_toFinset, Set.mem_setOf_eq] at h1
  have : vL.v z = vL.v z' := IsConjRoot.val_eq M hM (Polynomial.Separable.isIntegral zsep) h1 -- IsConjRoot.val_eq M hM zsep h1
  have : vL.v (z - z') < vL.v (z - z') := by
    calc
      _ ≤ vL.v (x - y) := by simpa only [max_self, ← this] using Valuation.map_sub vL.v z z'
      _ < vL.v (x - (z' + y)) := by
        apply hxy (z' + y)
        · apply IsConjRoot.of_isScalarTower (S := M) K
          simpa only [IntermediateField.algebraMap_apply, sub_add_cancel, z] using
            IsConjRoot.add_algebraMap ⟨y, hy⟩ h1
        · simpa [z, sub_eq_iff_eq_add] using hne
      _ = vL.v (z - z') := by congr 1; ring
  simp only [lt_self_iff_false] at this

end IsKrasner

end krasner
