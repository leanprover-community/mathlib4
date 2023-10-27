/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

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

open FiniteDimensional

theorem inf_iSup_generalizedEigenspace [FiniteDimensional K M] (h : ∀ x ∈ p, f x ∈ p) :
    p ⊓ ⨆ μ, ⨆ k, f.generalizedEigenspace μ k = ⨆ μ, ⨆ k, p ⊓ f.generalizedEigenspace μ k := by
  refine le_antisymm (fun m hm ↦ ?_)
    (le_inf_iff.mpr ⟨iSup₂_le fun μ k ↦ inf_le_left, iSup₂_mono fun μ k ↦ inf_le_right⟩)
  obtain ⟨hm₀ : m ∈ p, hm₁ : m ∈ ⨆ μ, ⨆ k, f.generalizedEigenspace μ k⟩ := hm
  classical
  obtain ⟨m, hm₂, rfl⟩ := (mem_iSup_iff_exists_finsupp _ _).mp hm₁
  suffices ∀ μ, (m μ : M) ∈ p by
    simp_rw [←(f.generalizedEigenspace _).mono.directed_le.inf_iSup_eq, mem_iSup_iff_exists_finsupp]
    exact ⟨m, fun μ ↦ mem_inf.mp ⟨this μ, hm₂ μ⟩, rfl⟩
  intro μ
  let σ : Finset K := (Module.End.finite_hasEigenvalue f).toFinset \ {μ}
  have h_comm : ∀ (μ₁ μ₂ : K),
    Commute ((f - algebraMap K (End K M) μ₁) ^ finrank K M)
            ((f - algebraMap K (End K M) μ₂) ^ finrank K M) := by
    sorry
  let g : Module.End K M := σ.noncommProd _ fun μ₁ _ μ₂ _ _ ↦ h_comm μ₁ μ₂
  have hg₁ : g (m.sum fun _μ mμ ↦ mμ) = g (m μ) := by
    sorry
  have hg₂ : MapsTo g p p := by
    sorry
  replace hm₀ : g (m μ) ∈ p := hg₁ ▸ hg₂ hm₀
  -- To finish: `g` restricted to `⨆ k, f.generalizedEigenspace μ k` is an equivalence, hence
  -- `g (m μ) ∈ p` ↔ `m μ ∈ p` [probably some lemmas to break out of this].
  sorry

theorem eq_iSup_inf_generalizedEigenspace [FiniteDimensional K M]
    (h : ∀ x ∈ p, f x ∈ p) (h' : f.IsTriangularizable) :
    p = ⨆ μ, ⨆ k, p ⊓ f.generalizedEigenspace μ k := by
  rw [← inf_iSup_generalizedEigenspace h, h'.iSup_eq, inf_top_eq]

end Submodule

theorem Module.End.IsTriangularizable.isTriangularizable_restrict [FiniteDimensional K M]
    (h : ∀ x ∈ p, f x ∈ p) (h' : f.IsTriangularizable) :
    End.IsTriangularizable (LinearMap.restrict f h) := by
  have := congr_arg (Submodule.comap p.subtype) (Submodule.eq_iSup_inf_generalizedEigenspace h h')
  have h_inj : Function.Injective p.subtype := Subtype.coe_injective
  simp_rw [Submodule.inf_generalizedEigenspace f p h, Submodule.comap_subtype_self,
    ← Submodule.map_iSup, Submodule.comap_map_eq_of_injective h_inj] at this
  exact this.symm
