/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Algebraic.Integral

/-! # Algebraic extensions of the residue field -/

instance {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] :
    Algebra.IsAlgebraic (R ⧸ p) p.ResidueField :=
  IsLocalization.isAlgebraic _ (nonZeroDivisors (R ⧸ p))

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) (P : Ideal S)
    [p.IsPrime] [P.IsPrime] [P.LiesOver p] [Algebra.IsIntegral R S] :
    Algebra.IsAlgebraic p.ResidueField P.ResidueField := by
  have : Algebra.IsIntegral (R ⧸ p) (S ⧸ P) :=
    .tower_top R
  letI := ((algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P))).toAlgebra
  haveI : IsScalarTower (R ⧸ p) (S ⧸ P) P.ResidueField := .of_algebraMap_eq' rfl
  haveI : Algebra.IsAlgebraic (R ⧸ p) P.ResidueField := .trans _ (S ⧸ P) _
  haveI : IsScalarTower (R ⧸ p) p.ResidueField P.ResidueField := by
    refine .of_algebraMap_eq fun x ↦ ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [RingHom.algebraMap_toAlgebra, Algebra.ofId_apply]
  refine .extendScalars (Ideal.injective_algebraMap_quotient_residueField p)
