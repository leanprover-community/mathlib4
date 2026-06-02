/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Extension.Cotangent.BaseChange

/-!
# Etale descends along faithfully flat ring maps

In this file we show that smooth, unramified and étale algebras descend along faithfully flat
base change.

## Main results

- `Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat`: Smooth descends.
- `Algebra.Unramified.of_smooth_tensorProduct_of_faithfullyFlat`: Unramified descends.
- `Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat`: Etale descends.

We also provide the corresponding `RingHom.CodescendsAlong` lemmas.

## TODOs

- The lemma `Algebra.FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat` has an
  additional `Algebra.FinitePresentation` assumption, because the proof uses that a flat module
  of finite presentation is projective and the former descends. This also holds without
  the finite presentation assumption, but requires showing that projectivity descends
  along faithfully flat base change, which is due to Raynaud and Gruson
  (see https://stacks.math.columbia.edu/tag/058B).
-/

public section

open TensorProduct

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (T : Type*) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]

lemma FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat
    [FormallyUnramified T (T ⊗[R] S)] :
    FormallyUnramified R S := by
  constructor
  let _ : Algebra S (T ⊗[R] S) := TensorProduct.rightAlgebra
  have : Subsingleton (T ⊗[R] Ω[S⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivBase R T S (T ⊗[R] S)).subsingleton
  exact Module.FaithfullyFlat.lTensor_reflects_triviality R T _

/-- Formally smooth algebras descend along faithfully flat base change. See the TODO
in the module docstring. -/
proof_wanted FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (T : Type*) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [FormallySmooth T (T ⊗[R] S)] :
    FormallySmooth R S

lemma Smooth.of_smooth_tensorProduct_of_faithfullyFlat [Smooth T (T ⊗[R] S)] :
    Smooth R S := by
  have : Algebra.FinitePresentation R S := .of_finitePresentation_tensorProduct_of_faithfullyFlat T
  refine ⟨?_, .of_finitePresentation_tensorProduct_of_faithfullyFlat T⟩
  rw [formallySmooth_iff]
  constructor
  · let _ : Algebra T (S ⊗[R] T) := TensorProduct.rightAlgebra
    let e : S ⊗[R] T ≃ₐ[T] T ⊗[R] S :=
      .ofRingEquiv (f := TensorProduct.comm R S T) <| by simp [RingHom.algebraMap_toAlgebra]
    have : FormallySmooth T (S ⊗[R] T) := .of_equiv e.symm
    let e' : (S ⊗[R] T) ⊗[S] Ω[S⁄R] ≃ₗ[S ⊗[R] T] Ω[S ⊗[R] T⁄T] :=
      KaehlerDifferential.tensorKaehlerEquiv R T S (S ⊗[R] T)
    have : Module.Flat (S ⊗[R] T) ((S ⊗[R] T) ⊗[S] Ω[S⁄R]) := .of_linearEquiv e'
    have : Module.Flat S Ω[S⁄R] := Module.Flat.of_flat_tensorProduct _ _ (S ⊗[R] T)
    exact Module.Flat.projective_of_finitePresentation
  · have : Subsingleton (T ⊗[R] H1Cotangent R S) := (tensorH1CotangentOfFlat R S T).subsingleton
    exact Module.FaithfullyFlat.lTensor_reflects_triviality R T (H1Cotangent R S)

lemma Unramified.of_unramified_tensorProduct_of_faithfullyFlat [Unramified T (T ⊗[R] S)] :
    Unramified R S :=
  ⟨.of_formallyUnramified_tensorProduct_of_faithfullyFlat T,
    .of_finiteType_tensorProduct_of_faithfullyFlat T⟩

lemma Etale.of_etale_tensorProduct_of_faithfullyFlat [Etale T (T ⊗[R] S)] :
    Etale R S := by
  rw [Etale.iff_formallyUnramified_and_smooth]
  exact ⟨.of_formallyUnramified_tensorProduct_of_faithfullyFlat T,
    .of_smooth_tensorProduct_of_faithfullyFlat T⟩

end Algebra

namespace RingHom

lemma Smooth.codescendsAlong_faithfullyFlat : CodescendsAlong Smooth FaithfullyFlat := by
  refine .mk _ Smooth.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [smooth_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_smooth_tensorProduct_of_faithfullyFlat S

lemma FormallyUnramified.codescendsAlong_faithfullyFlat :
    CodescendsAlong FormallyUnramified FaithfullyFlat := by
  refine .mk _ FormallyUnramified.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [formallyUnramified_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_formallyUnramified_tensorProduct_of_faithfullyFlat S

lemma Etale.codescendsAlong_faithfullyFlat : CodescendsAlong Etale FaithfullyFlat := by
  refine .mk _ Etale.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [etale_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_etale_tensorProduct_of_faithfullyFlat S

end RingHom
