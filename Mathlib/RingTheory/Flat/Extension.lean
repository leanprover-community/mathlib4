/-
Copyright (c) 2026 Nailin Guan, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jingting Wang
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.SmallObject.Iteration.Nonempty
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.RingHom.Flat

/-!

# Existence of Flat extension

-/

@[expose] public section

universe u v

open IsLocalRing CategoryTheory SmallObject Limits

open scoped Polynomial

variable (R : Type u) [CommRing R]

variable [IsLocalRing R] (K : Type u) [Field K] [Algebra R K] [IsLocalHom (algebraMap R K)]

section monogenic

variable (S : Type u) [CommRing S] [Algebra S K]

set_option linter.unusedVariables false in
abbrev adjoinAlgebraic (x : K) (int : IsIntegral S x) : Type u := S[X] ⧸ Ideal.span {minpoly S x}

instance (x : K) (int : IsIntegral S x) : Module.Finite S (adjoinAlgebraic K S x int) :=
  (minpoly.monic int).finite_quotient

instance (x : K) (int : IsIntegral S x) : Module.Free S (adjoinAlgebraic K S x int) :=
  (minpoly.monic int).free_quotient

variable [IsLocalRing S] [IsLocalHom (algebraMap S K)]

variable {S K} in
private lemma algebraMap_eq_zero (x : S) (mem : x ∈ maximalIdeal S) : algebraMap S K x = 0 := by
  simp only [mem_maximalIdeal, mem_nonunits_iff] at mem
  exact (iff_not_comm.mp isUnit_iff_ne_zero).mpr ((IsLocalHom.map_nonunit x).mt mem)

private instance [IsLocalHom (algebraMap S K)] : Algebra (ResidueField S) K :=
  (Ideal.Quotient.lift _ (algebraMap S K) (fun x hx ↦ algebraMap_eq_zero x hx)).toAlgebra

private instance : IsScalarTower S (ResidueField S) K :=
  IsScalarTower.of_algebraMap_eq' rfl

set_option linter.unusedVariables false in
abbrev adjoinTranscendental (x : K) (nint : ¬ IsIntegral S x) : Type u :=
  Localization.AtPrime ((maximalIdeal S).map Polynomial.C)

omit [IsLocalHom (algebraMap S K)] in
lemma adjoinTranscendental_maximalIdeal_eq_map (x : K) (nint : ¬ IsIntegral S x) :
    maximalIdeal (adjoinTranscendental K S x nint) =
    (maximalIdeal S).map (algebraMap S (adjoinTranscendental K S x nint)) := by
  rw [IsScalarTower.algebraMap_eq S S[X], ← Ideal.map_map]
  exact Localization.AtPrime.map_eq_maximalIdeal.symm

end monogenic

structure FlatExtension where
  Ring : Type u
  [commRing : CommRing Ring]
  [isLocalRing : IsLocalRing Ring]
  [algebra : Algebra R Ring]
  [algebraK : Algebra Ring K]
  [isScalarTower : IsScalarTower R Ring K]
  [flat : Module.Flat R Ring]
  eqmap : maximalIdeal Ring = (maximalIdeal R).map (algebraMap R Ring)

namespace FlatExtension

attribute [instance] commRing algebra isLocalRing algebraK isScalarTower flat

instance : CoeSort (FlatExtension R K) (Type u) := ⟨FlatExtension.Ring⟩

attribute [coe] FlatExtension.Ring

instance (S : FlatExtension R K) : IsLocalHom (algebraMap R S) :=
  ((IsLocalRing.local_hom_TFAE _).out 0 2).mpr (le_of_eq S.eqmap.symm)

instance (S : FlatExtension R K) : IsLocalHom (algebraMap S K) := by
  apply ((IsLocalRing.local_hom_TFAE _).out 0 2).mpr
  rw [S.eqmap, Ideal.map_map, ← IsScalarTower.algebraMap_eq R]
  exact ((IsLocalRing.local_hom_TFAE _).out 0 2).mp ‹_›

noncomputable def trivial : FlatExtension R K where
  Ring := R
  isScalarTower := IsScalarTower.left R
  eqmap := by simp

variable {R K} in
structure Hom (S₁ S₂ : FlatExtension R K) where
  algHom : S₁.Ring →ₐ[R] S₂.Ring
  comm : (IsScalarTower.toAlgHom R S₂ K).comp algHom = IsScalarTower.toAlgHom R S₁ K

--prove it is indeed local hom

variable {R K}

def Hom.id (S : FlatExtension R K) : Hom S S := ⟨AlgHom.id R S.Ring, by simp⟩

def Hom.comp {S₁ S₂ S₃ : FlatExtension R K} (f : Hom S₁ S₂) (g : Hom S₂ S₃) :
    Hom S₁ S₃ := ⟨g.algHom.comp f.algHom, by simp [← AlgHom.comp_assoc, g.comm, f.comm]⟩

instance : Category (FlatExtension R K) where
  Hom S₁ S₂ := Hom S₁ S₂
  id S := Hom.id S
  comp f g := f.comp g

end FlatExtension
