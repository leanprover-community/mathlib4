/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Triangularizable linear endomorphisms

TODO write something

-/

open Set Function Module

variable {K R M : Type*} [CommRing R] [Field K] [AddCommGroup M] [Module R M] [Module K M]
  {p : Submodule K M} {f : End K M}

namespace Module.End

/-- An endomorphism of a module is said to be triangularizable if its generalized eigenspaces span
the entire module.

All endomorphisms of a finite-dimensional vector space over an algebraically-closed field are
triangularizable, see `Module.End.isTriangularizable_of_isAlgClosed`. -/
def IsTriangularizable (f : End R M) : Prop :=
  ⨆ μ, ⨆ k, f.generalizedEigenspace μ k = ⊤

lemma IsTriangularizable.iSup_eq {f : End R M} (hf : f.IsTriangularizable) :
    ⨆ μ, ⨆ k, f.generalizedEigenspace μ k = ⊤ :=
  hf

end Module.End

namespace Submodule

theorem inf_iSup_generalizedEigenspace (h : ∀ x ∈ p, f x ∈ p) :
    p ⊓ ⨆ μ, ⨆ k, f.generalizedEigenspace μ k = ⨆ μ, ⨆ k, p ⊓ f.generalizedEigenspace μ k := by
  sorry

theorem eq_iSup_inf_generalizedEigenspace (h : ∀ x ∈ p, f x ∈ p) (h' : f.IsTriangularizable) :
    p = ⨆ μ, ⨆ k, p ⊓ f.generalizedEigenspace μ k := by
  rw [← inf_iSup_generalizedEigenspace h, h'.iSup_eq, inf_top_eq]

end Submodule

theorem Module.End.IsTriangularizable.isTriangularizable_restrict
    (h : ∀ x ∈ p, f x ∈ p) (h' : f.IsTriangularizable) :
    End.IsTriangularizable (LinearMap.restrict f h) := by
  have := congr_arg (Submodule.comap p.subtype) (Submodule.eq_iSup_inf_generalizedEigenspace h h')
  have h_inj : Function.Injective p.subtype := Subtype.coe_injective
  simp_rw [Submodule.inf_generalizedEigenspace f p h, Submodule.comap_subtype_self,
    ← Submodule.map_iSup, Submodule.comap_map_eq_of_injective h_inj] at this
  exact this.symm
