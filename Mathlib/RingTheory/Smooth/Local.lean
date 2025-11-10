/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Formally smooth local algebras
-/

open TensorProduct IsLocalRing KaehlerDifferential

/--
The **Jacobian criterion** for smoothness of local algebras.
Suppose `S` is a local `R`-algebra, and `0 → I → P → S → 0` is a presentation such that
`P` is formally-smooth over `R`, `Ω[P⁄R]` is finite free over `P`,
(typically satisfied when `P` is the localization of a polynomial ring of finite type)
and `I` is finitely generated.
Then `S` is formally smooth iff `k ⊗ₛ I/I² → k ⊗ₚ Ω[P/R]` is injective,
where `k` is the residue field of `S`.
-/
theorem Algebra.FormallySmooth.iff_injective_lTensor_residueField.{u} {R S : Type*} [CommRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] (P : Algebra.Extension.{u} R S)
    [FormallySmooth R P.Ring]
    [Module.Free P.Ring Ω[P.Ring⁄R]] [Module.Finite P.Ring Ω[P.Ring⁄R]]
    (h' : P.ker.FG) :
    Algebra.FormallySmooth R S ↔
      Function.Injective (P.cotangentComplex.lTensor (ResidueField S)) := by
  have : Module.Finite P.Ring P.Cotangent :=
    have : Module.Finite P.Ring P.ker := ⟨(Submodule.fg_top _).mpr h'⟩
    .of_surjective _ Extension.Cotangent.mk_surjective
  have : Module.Finite S P.Cotangent := Module.Finite.of_restrictScalars_finite P.Ring _ _
  rw [← IsLocalRing.split_injective_iff_lTensor_residueField_injective,
    P.formallySmooth_iff_split_injection]
