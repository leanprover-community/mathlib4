/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!

# Zero locus of a set of sections

If `X` is a ringed space and `s` is a set of sections over an open set `U`, the zero locus
of `s` in `U` is the closed set of `U`, where all elements of `f` vanish.

-/

universe u

open TopologicalSpace CategoryTheory Opposite

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace} {U : Opens X}

def zeroLocus (s : Set (X.presheaf.obj (op U))) : Set X :=
  ⋂ f ∈ s, (X.basicOpen f)ᶜ

lemma zeroLocus_singleton (f : X.presheaf.obj (op U)) :
    zeroLocus {f} = (X.basicOpen f).carrierᶜ := by
  simp [zeroLocus]

lemma mem_zeroLocus_iff (s : Set (X.presheaf.obj (op U))) (x : X) :
    x ∈ zeroLocus s ↔ ∀ f ∈ s, x ∉ X.basicOpen f := by
  simp [zeroLocus]


lemma Scheme.zeroLocus_primeSpectrum_zeroLocus' {X : Scheme} (s : Set (Scheme.Γ.obj (op X))) :
    X.toΓSpecFun ⁻¹' PrimeSpectrum.zeroLocus s = RingedSpace.zeroLocus s := by
  simp only [RingedSpace.zeroLocus]
  have (i : Scheme.Γ.obj (op X)) (_ : i ∈ s) : (X.basicOpen i).carrierᶜ =
        X.toΓSpecFun ⁻¹' (PrimeSpectrum.basicOpen i).carrierᶜ := by
    symm
    rw [Set.preimage_compl, X.toΓSpec_preim_basicOpen_eq i]
    simp
    rfl
  erw [Set.iInter₂_congr this]
  rw [← Set.preimage_iInter₂]
  simp only [Scheme.Γ_obj, Opens.carrier_eq_coe, PrimeSpectrum.basicOpen_eq_zeroLocus_compl, compl_compl]
  rw [← PrimeSpectrum.zeroLocus_iUnion₂]
  simp

