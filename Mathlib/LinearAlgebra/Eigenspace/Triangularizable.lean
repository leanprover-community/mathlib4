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
  simp_rw [← (f.generalizedEigenspace _).mono.directed_le.inf_iSup_eq]
  refine le_antisymm (fun m hm ↦ ?_)
    (le_inf_iff.mpr ⟨iSup_le fun μ ↦ inf_le_left, iSup_mono fun μ ↦ inf_le_right⟩)
  classical
  obtain ⟨hm₀ : m ∈ p, hm₁ : m ∈ ⨆ μ, ⨆ k, f.generalizedEigenspace μ k⟩ := hm
  obtain ⟨m, hm₂, rfl⟩ := (mem_iSup_iff_exists_finsupp _ _).mp hm₁
  suffices ∀ μ, (m μ : M) ∈ p by
    exact (mem_iSup_iff_exists_finsupp _ _).mpr ⟨m, fun μ ↦ mem_inf.mp ⟨this μ, hm₂ μ⟩, rfl⟩
  intro μ
  by_cases hμ : μ ∈ m.support; swap; simp only [Finsupp.not_mem_support_iff.mp hμ, p.zero_mem]
  have h_comm : ∀ (μ₁ μ₂ : K),
    Commute ((f - algebraMap K (End K M) μ₁) ^ finrank K M)
            ((f - algebraMap K (End K M) μ₂) ^ finrank K M) := fun μ₁ μ₂ ↦
    ((Commute.sub_right rfl <| Algebra.commute_algebraMap_right _ _).sub_left
      (Algebra.commute_algebraMap_left _ _)).pow_pow _ _
  let g : Module.End K M := (m.support.erase μ).noncommProd _ fun μ₁ _ μ₂ _ _ ↦ h_comm μ₁ μ₂
  have hfg : Commute f g := Finset.noncommProd_commute _ _ _ _ fun μ' hμ' ↦
    (Commute.sub_right rfl <| Algebra.commute_algebraMap_right _ _).pow_right _
  have hg₀ : g (m.sum fun _μ mμ ↦ mμ) = g (m μ) := by
    suffices ∀ μ' ∈ m.support, g (m μ') = if μ' = μ then g (m μ) else 0 by
      rw [map_finsupp_sum, Finsupp.sum_congr (g2 := fun μ' m' ↦ if μ' = μ then g (m μ) else 0) this,
        Finsupp.sum_ite_eq', if_pos hμ]
    rintro μ' hμ'
    split_ifs with hμμ'; rw [hμμ']
    replace hm₂ : ((f - algebraMap K (End K M) μ') ^ finrank K M) (m μ') = 0 := by
      obtain ⟨k, hk⟩ := (mem_iSup_of_chain _ _).mp (hm₂ μ')
      exact Module.End.generalizedEigenspace_le_generalizedEigenspace_finrank _ _ k hk
    have : _ = g := (m.support.erase μ).noncommProd_erase_mul (Finset.mem_erase.mpr ⟨hμμ', hμ'⟩)
      (fun μ ↦ (f - algebraMap K (End K M) μ) ^ finrank K M) (fun μ₁ _ μ₂ _ _ ↦ h_comm μ₁ μ₂)
    rw [← this, LinearMap.mul_apply, hm₂, _root_.map_zero]
  have hg₁ : MapsTo g p p := Finset.noncommProd_induction _ _ _ (fun g' : End K M ↦ MapsTo g' p p)
      (fun f₁ f₂ ↦ MapsTo.comp) (mapsTo_id _) fun μ' hμ' ↦ by
    suffices MapsTo (f - algebraMap K (End K M) μ') p p by
      simp only [LinearMap.coe_pow]; exact this.iterate (finrank K M)
    intro x hx
    rw [LinearMap.sub_apply, algebraMap_end_apply]
    exact p.sub_mem (h _ hx) (smul_mem p μ' hx)
  have hg₂ : MapsTo g ↑(⨆ k, f.generalizedEigenspace μ k) ↑(⨆ k, f.generalizedEigenspace μ k) :=
    f.mapsTo_iSup_generalizedEigenspace_of_comm hfg μ
  have hg₃ : InjOn g ↑(⨆ k, f.generalizedEigenspace μ k) := by
    -- Wait, this is non-trivial: I'll need the independence of the generalized eigenspaces.
    -- Unfortunately `Module.End.eigenspaces_independent` only does this for eigenspaces *sigh*
    sorry
  have hg₄ : SurjOn g
      ↑(p ⊓ ⨆ k, f.generalizedEigenspace μ k) ↑(p ⊓ ⨆ k, f.generalizedEigenspace μ k) := by
    -- Looks like this is only place we'll need finite-dimensionality (we'll get it from `InjOn`).
    sorry
  specialize hm₂ μ
  obtain ⟨y, ⟨hy₀ : y ∈ p, hy₁ : y ∈ ⨆ k, f.generalizedEigenspace μ k⟩, hy₂ : g y = g (m μ)⟩ :=
    hg₄ ⟨(hg₀ ▸ hg₁ hm₀), hg₂ hm₂⟩
  rwa [← hg₃ hy₁ hm₂ hy₂]

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
