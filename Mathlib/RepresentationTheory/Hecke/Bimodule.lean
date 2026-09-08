/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.Hecke.Basic
public import Mathlib.RepresentationTheory.Hecke.LeftFiniteDoubleCoset

/-!
# Hecke bimodules and action on Hecke modules

This file introduces the Hecke bimodule `Hom_G(k[G ⧸ H₁], k[G ⧸ H₂])`, which naturally can be viewed
as an `(End_G(k[G ⧸ H₁])ᵒᵖ, End_G(k[G ⧸ H₂]))`-bimodule. We identify this intertwining space with
the free module over double cosets admitting finite left-coset decomposition.
-/

@[expose] public section

variable {k : Type*} [CommRing k] {G : Type*} [Group G] {H₁ H₂ : Subgroup G}
variable {V : Type*} [AddCommGroup V] [Module k V]

open DoubleCoset MonoidAlgebra

namespace Representation

variable (k H₁ H₂) in
/-- The interwining space `Hom_G(k[G ⧸ H₁], k[G ⧸ H₂])`, which naturally can be viewed as an
`(End_G(k[G ⧸ H₁])ᵒᵖ, End_G(k[G ⧸ H₂]))`-bimodule. -/
abbrev HeckeBimodule := HeckeModule H₁ (ofMulAction k G (G ⧸ H₂))

variable (k) in
/-- The characteristic vector of a double coset. -/
noncomputable def doubleCosetVector : DoubleCoset₀ H₁ H₂ → k[G ⧸ H₂] :=
  fun x => ∑ (i : x.leftDecomposition), cosetVector k i

lemma doubleCosetVector_def (x : DoubleCoset₀ H₁ H₂) :
    doubleCosetVector k x = ∑ (i : x.leftDecomposition), cosetVector k i := rfl

@[simp]
lemma coeff_doubleCosetVector (x : DoubleCoset₀ H₁ H₂) (c : G ⧸ H₂)
    [Decidable (c ∈ x.leftDecomposition)] :
    (doubleCosetVector k x).coeff c = if c ∈ x.leftDecomposition then (1 : k) else 0 := by classical
  simp [doubleCosetVector_def, Finset.sum_set_coe, Finsupp.single_apply]

namespace HeckeBimodule

local notation "ev₁" f:arg => f (cosetVector k (1 : G))

lemma coeff_apply_one_mem_smul {h₁ : G} (hh₁ : h₁ ∈ H₁) {f : HeckeBimodule k H₁ H₂} (c : G ⧸ H₂) :
    (ev₁ f).coeff (h₁ • c) = (ev₁ f).coeff c := by
  rw [← inv_inv h₁, ← coeff_ofMulAction, ← IntertwiningMap.isIntertwining]
  simp [cosetVector_mem ⟨_, H₁.inv_mem hh₁⟩]

/-- The element of the Hecke bimodule attached to a double coset `x`, characterized by sending the
identity coset to `doubleCosetVector k x`. -/
noncomputable def mk (x : DoubleCoset₀ H₁ H₂) : HeckeBimodule k H₁ H₂ :=
  HeckeModule.invariantsEquiv ⟨doubleCosetVector k x, fun h₁ => by
    simpa [doubleCosetVector_def] using Equiv.sum_comp (MulAction.toPerm h₁)
      (fun i : x.leftDecomposition ↦ cosetVector k i.1)⟩

/-- The linear map sending Hecke bimodule elements to coordinates in the basis given by `mk`. -/
noncomputable def coeff :
    HeckeBimodule k H₁ H₂ →ₗ[k] (DoubleCoset₀ H₁ H₂ →₀ k) where
  toFun f := Finsupp.ofSupportFinite
    (fun x : DoubleCoset₀ H₁ H₂ => (ev₁ f).coeff x.rep)
    (by
      have : Function.Injective (fun x : DoubleCoset₀ H₁ H₂ ↦ (x.rep : G ⧸ H₂)) := by
        intro x y hxy
        rw [← DoubleCoset₀.mk_rep x, ← DoubleCoset₀.mk_rep y, DoubleCoset₀.mk_eq]
        exact ⟨1, H₁.one_mem, _, QuotientGroup.eq.mp hxy, by simp⟩
      exact Set.Finite.preimage this.injOn (ev₁ f).coeff.hasFiniteSupport)
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp]
lemma mk_apply (x : DoubleCoset₀ H₁ H₂) :
    ev₁ (mk x) = doubleCosetVector k x := by
  simp [mk]

lemma coeff_apply (f : HeckeBimodule k H₁ H₂) (x : DoubleCoset₀ H₁ H₂) :
    f.coeff x = (ev₁ f).coeff x.rep := rfl

lemma coeff_eq_coeff_mem {f : HeckeBimodule k H₁ H₂} {x : DoubleCoset₀ H₁ H₂} {c : G ⧸ H₂}
    (hc : c ∈ x.leftDecomposition) :
    f.coeff x = (ev₁ f).coeff c := by
  rw [← DoubleCoset₀.mk_rep x, coeff_apply]
  obtain ⟨h₁, hh₁, heq⟩ := mem_leftDecomposition_eq_smul (c := x.rep) (by simp) hc
  simpa [heq] using coeff_apply_one_mem_smul hh₁ c (k := k)

lemma coeff_doubleCosetMk (f : HeckeBimodule k H₁ H₂) (g : G) [IsLeftFinite H₁ H₂ g] :
    f.coeff (DoubleCoset₀.mk H₁ H₂ g) = (ev₁ f).coeff g :=
  coeff_eq_coeff_mem (mem_leftDecomposition_mk.mpr rfl)

@[simp]
lemma coeff_mk_eq_single (x : DoubleCoset₀ H₁ H₂) :
    (mk x).coeff = Finsupp.single x (1 : k) := by classical
  ext y
  rw [← DoubleCoset₀.mk_rep y, coeff_doubleCosetMk]
  by_cases h : x = y <;> simp [← Subtype.ext_iff, h, eq_comm]

lemma ext_coeff {x y : HeckeBimodule k H₁ H₂} (hxy : ∀ z, x.coeff z = y.coeff z) :
    x = y := by classical
  ext c
  by_cases hc : ∃ z : DoubleCoset₀ H₁ H₂, c ∈ z.leftDecomposition
  · obtain ⟨z, hcz⟩ := hc
    simpa [coeff_eq_coeff_mem hcz] using hxy z
  · have hzero (f : HeckeBimodule k H₁ H₂) : (ev₁ f).coeff c = 0 := by
      by_contra h
      have : IsLeftFinite H₁ H₂ c.out := by
        rw [isLeftFinite_iff_finite_leftDecomposition]
        have hsub : (DoubleCoset.mk H₁ H₂ c.out).leftDecomposition ⊆ (ev₁ f).coeff.support := by
          intro d hd
          obtain ⟨h₁, hh₁, heq⟩ := mem_leftDecomposition_eq_smul (c := c.out)
             (mem_leftDecomposition_mk.mpr rfl) hd
          rw [QuotientGroup.out_eq'] at heq
          simpa [heq, coeff_apply_one_mem_smul hh₁] using h
        exact Set.Finite.subset (Finset.finite_toSet _) hsub
      rw [← QuotientGroup.out_eq' c] at hc
      exact hc ⟨DoubleCoset₀.mk H₁ H₂ c.out, mem_leftDecomposition_mk.mpr rfl⟩
    rw [hzero, hzero]

/-- The linear equivalence from `DoubleCoset₀ H₁ H₂ →₀ k` to the Hecke bimodule, sending
`single x 1` to `mk x`. Its inverse is `coeff`. -/
noncomputable def mkLinearEquiv :
    (DoubleCoset₀ H₁ H₂ →₀ k) ≃ₗ[k] HeckeBimodule k H₁ H₂ where
  toLinearMap := Finsupp.lift _ k _ (fun x ↦ mk x)
  invFun f := f.coeff
  left_inv f := by classical ext; simp [map_finsuppSum]
  right_inv x := by classical apply ext_coeff; simp [map_finsuppSum]

@[simp]
lemma mkLinearEquiv_apply_single (x : DoubleCoset₀ H₁ H₂) (r : k) :
    mkLinearEquiv (.single x r) = r • mk x := by
  simp [mkLinearEquiv]

@[simp]
lemma mkLinearEquiv_symm_apply (f : HeckeBimodule k H₁ H₂) :
    mkLinearEquiv.symm f = f.coeff :=
  rfl

lemma inductionOn (f : HeckeBimodule k H₁ H₂) {p : HeckeBimodule k H₁ H₂ → Prop}
    (zero : p 0)
    (mk' : ∀ (g : DoubleCoset₀ H₁ H₂), p (mk g))
    (smul : ∀ (r : k) (x : HeckeBimodule k H₁ H₂), p x → p (r • x))
    (add : ∀ x y, p x → p y → p (x + y)) : p f := by
  rw [← mkLinearEquiv.apply_symm_apply f]
  refine Finsupp.induction_linear (mkLinearEquiv.symm f) ?_ ?_ ?_
  · simp [zero]
  · exact fun x y hx hy => by simpa using add (mkLinearEquiv x) (mkLinearEquiv y) hx hy
  · exact fun x r => by simpa using smul r (mk x) (mk' x)

end HeckeBimodule

end Representation
