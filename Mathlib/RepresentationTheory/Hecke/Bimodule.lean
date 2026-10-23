/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.Hecke.Basic
public import Mathlib.RepresentationTheory.Hecke.LeftFiniteDoubleCoset
public import Mathlib.RepresentationTheory.Hecke.StructureConst

/-!
# Hecke bimodules and Hecke algebras

This file introduces the Hecke bimodule `Hom_G(k[G ⧸ H₁], k[G ⧸ H₂])`, which naturally can be viewed
as an `(End_G(k[G ⧸ H₁])ᵒᵖ, End_G(k[G ⧸ H₂]))`-bimodule. We identify this intertwining space with
the free module over double cosets admitting finite left-coset decomposition.
-/

@[expose] public section

variable {k : Type*} [CommRing k] {G : Type*} [Group G] {H H₁ H₂ H₃ : Subgroup G}
variable {V : Type*} [AddCommGroup V] [Module k V] {ρ : Representation k G V}

open DoubleCoset MonoidAlgebra

namespace Representation

variable (k H₁ H₂) in
/-- The intertwining space `Hom_G(k[G ⧸ H₁], k[G ⧸ H₂])`, which naturally can be viewed as an
`(End_G(k[G ⧸ H₁])ᵒᵖ, End_G(k[G ⧸ H₂]))`-bimodule. -/
abbrev HeckeBimodule := HeckeModule H₁ (ofMulAction k G (G ⧸ H₂))

variable (k) in
/-- The characteristic vector of a double coset. -/
noncomputable def doubleCosetVector : DoubleCoset₀ H₁ H₂ → k[G ⧸ H₂] :=
  fun x => ∑ (i : x.leftDecomposition), cosetVector k i

lemma doubleCosetVector_def (x : DoubleCoset₀ H₁ H₂) :
    doubleCosetVector k x = ∑ (i : x.leftDecomposition), cosetVector k i := rfl

@[simp]
lemma coeff_doubleCosetVector_of_mem {x : DoubleCoset₀ H₁ H₂} {c : G ⧸ H₂}
    (hc : c ∈ x.leftDecomposition) :
    (doubleCosetVector k x).coeff c = (1 : k) := by classical
  simp [doubleCosetVector_def, Finset.sum_set_coe, Finsupp.single_apply, hc]

@[simp]
lemma coeff_doubleCosetVector_of_not_mem {x : DoubleCoset₀ H₁ H₂} {c : G ⧸ H₂}
    (hc : c ∉ x.leftDecomposition) :
    (doubleCosetVector k x).coeff c = (0 : k) := by classical
  simp [doubleCosetVector_def, Finset.sum_set_coe, Finsupp.single_apply, hc]

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

lemma coeff_def (f : HeckeBimodule k H₁ H₂) (x : DoubleCoset₀ H₁ H₂) :
    f.coeff x = (ev₁ f).coeff x.rep := rfl

@[simp]
lemma coeff_mk_apply_of_eq {x : DoubleCoset₀ H₂ H₃} {c : G ⧸ H₂} {d : G ⧸ H₃}
    (h : relPosition c d = x.val) :
    ((mk x) (cosetVector k c)).coeff d = (1 : k) := by
  nth_rw 1 [← QuotientGroup.out_eq' c, ← mul_one c.out, ← smul_eq_mul, ← MulAction.Quotient.smul_mk,
    ← ofMulAction_apply_cosetVector, IntertwiningMap.isIntertwining, mk_apply, coeff_ofMulAction]
  simp [h, ← relPosition_mk_eq_iff]

@[simp]
lemma coeff_mk_apply_of_ne {x : DoubleCoset₀ H₂ H₃} {c : G ⧸ H₂} {d : G ⧸ H₃}
    (h : relPosition c d ≠ x) :
    ((mk x) (cosetVector k c)).coeff d = (0 : k) := by
  nth_rw 1 [← QuotientGroup.out_eq' c, ← mul_one c.out, ← smul_eq_mul, ← MulAction.Quotient.smul_mk,
    ← ofMulAction_apply_cosetVector, IntertwiningMap.isIntertwining, mk_apply, coeff_ofMulAction]
  simp [h, ← relPosition_mk_eq_iff]

lemma coeff_mk_apply {x : DoubleCoset₀ H₂ H₃} {c : G ⧸ H₂} {d : G ⧸ H₃}
    [Decidable (relPosition c d = x)] :
    ((mk x) (cosetVector k c)).coeff d = if relPosition c d = x then (1 : k) else 0 := by
  by_cases h : relPosition c d = x <;> simp [h]

lemma coeff_eq_coeff_mem {f : HeckeBimodule k H₁ H₂} {x : DoubleCoset₀ H₁ H₂} {c : G ⧸ H₂}
    (hc : c ∈ x.leftDecomposition) :
    f.coeff x = (ev₁ f).coeff c := by
  rw [← DoubleCoset₀.mk_rep x, coeff_def]
  obtain ⟨h₁, hh₁, heq⟩ := mem_leftDecomposition_eq_smul (c := x.rep) (by simp) hc
  simpa [heq] using coeff_apply_one_mem_smul hh₁ c (k := k)

lemma coeff_doubleCosetMk (f : HeckeBimodule k H₁ H₂) (g : G) [IsLeftFinite H₁ H₂ g] :
    f.coeff (DoubleCoset₀.mk H₁ H₂ g) = (ev₁ f).coeff g :=
  coeff_eq_coeff_mem (mem_leftDecomposition_mk.mpr rfl)

@[simp]
lemma coeff_mk_self (x : DoubleCoset₀ H₁ H₂) : (mk x).coeff x = (1 : k) := by
  simp [coeff]

@[simp]
lemma coeff_mk_of_ne {x y : DoubleCoset₀ H₁ H₂} (h : x ≠ y) : (mk x).coeff y = (0 : k) := by
  have : (y.rep : G ⧸ H₂) ∉ x.leftDecomposition := by
    by_contra
    simp_all [eq_comm, ← Subtype.ext_iff]
  simp [coeff, this]

lemma coeff_mk (x : DoubleCoset₀ H₁ H₂) :
    (mk x).coeff = .single x (1 : k) := by
  ext y; by_cases h : x = y <;> simp [h]

lemma ext_coeff {x y : HeckeBimodule k H₁ H₂} (hxy : ∀ z, x.coeff z = y.coeff z) :
    x = y := by
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

@[simp]
lemma coeff_sum (f : DoubleCoset₀ H₁ H₂ →₀ k) (x : DoubleCoset₀ H₁ H₂) :
    (f.sum fun y r ↦ r • mk y).coeff x (k := k) = f x := by
  simp [map_finsuppSum, coeff_mk]

@[simp]
lemma sum_mk (f : HeckeBimodule k H₁ H₂) :
    f.coeff.sum (fun x a ↦ a • mk x) = f :=
  ext_coeff (by simp)

/-- The linearization of `mk` gives a linear equivalence from `DoubleCoset₀ H₁ H₂ →₀ k` to the
Hecke bimodule `Hom_G(k[G ⧸ H₁], k[G ⧸ H₂])`. -/
@[simps! -isSimp apply symm_apply]
noncomputable def mkLinearEquiv :
    (DoubleCoset₀ H₁ H₂ →₀ k) ≃ₗ[k] HeckeBimodule k H₁ H₂ where
  toLinearMap := Finsupp.lift _ k _ mk
  invFun f := f.coeff
  left_inv f := by ext; simp
  right_inv x := by exact sum_mk x

@[simp]
lemma mkLinearEquiv_apply_single (x : DoubleCoset₀ H₁ H₂) (r : k) :
    mkLinearEquiv (.single x r) = r • mk x := by
  simp [mkLinearEquiv]

@[simp]
lemma mkLinearEquiv_symm_apply_mk (x : DoubleCoset₀ H₁ H₂) :
    mkLinearEquiv.symm (mk x) = .single x (1 : k) :=
  (mkLinearEquiv (k := k)).injective (by simp)

lemma inductionOn (f : HeckeBimodule k H₁ H₂) {p : HeckeBimodule k H₁ H₂ → Prop}
    (zero : p 0)
    (mk' : ∀ (g : DoubleCoset₀ H₁ H₂), p (mk g))
    (smul : ∀ (r : k) (x : HeckeBimodule k H₁ H₂), p x → p (r • x))
    (add : ∀ x y, p x → p y → p (x + y)) : p f := by
  rw [← mkLinearEquiv.apply_symm_apply f]
  refine Finsupp.induction_linear (mkLinearEquiv.symm f) (by simp [zero]) ?_ ?_
  · exact fun x y hx hy => by simpa using add (mkLinearEquiv x) (mkLinearEquiv y) hx hy
  · exact fun x r => by simpa using smul r (mk x) (mk' x)

section Action

/-- The action of `f ∈ Hom_G(k[G ⧸ H₁], k[G ⧸ H₂])` is given by precomposition
`· ∘ f : HeckeModule H₂ ρ → HeckeModule H₁ ρ`. -/
noncomputable def action : HeckeBimodule k H₁ H₂ →ₗ[k] HeckeModule H₂ ρ →ₗ[k] HeckeModule H₁ ρ :=
  (IntertwiningMap.llcomp (ofMulAction k G (G ⧸ H₁)) (ofMulAction k G (G ⧸ H₂)) ρ).flip

lemma action_eq_comp (x : HeckeBimodule k H₁ H₂) (v : HeckeModule H₂ ρ) :
    x.action v = v.comp x := rfl

lemma action_assoc (x : HeckeBimodule k H₁ H₂) (y : HeckeBimodule k H₂ H₃) (v : HeckeModule H₃ ρ) :
    action (x.action y) v = x.action (y.action v) := rfl

lemma action.diag_mul_eq (x y : HeckeBimodule k H H) :
    (y * x).action (k := k) (ρ := ρ) = x.action * y.action := rfl

lemma action_mk_apply (x : DoubleCoset₀ H₁ H₂) (v : HeckeModule H₂ ρ) :
    (mk x).action v (cosetVector k (1 : G)) =  ∑ y : x.leftDecomposition, v (cosetVector k y) := by
  rw [action_eq_comp, IntertwiningMap.comp_apply, mk_apply, doubleCosetVector_def, map_sum]

theorem action_mk_mk (x : DoubleCoset₀ H₁ H₂) (y : DoubleCoset₀ H₂ H₃) :
    (mk x).action (mk y) (k := k) = (x.structureConst y).sum fun w n => (n : k) • (mk w) := by
  refine ext_coeff fun z => calc
  _ = (x.structureConst y z : k) := by
    rw [← DoubleCoset₀.mk_rep z, DoubleCoset₀.structureConst_coe, DoubleCoset₀.val_mk,
      structureConst_mk, coeff_def]
    classical simp [action_mk_apply, coeff_mk_apply]
  _ = _ := by
    classical simpa [map_finsuppSum, Finsupp.single_apply, coeff_mk] using fun h => by simp [h]

end Action

section BaseChange

/-- The isomorphism between `Hom_G(k[G ⧸ H₁], k[G ⧸ H₂])` and `k ⨂ Hom_G(ℤ[G ⧸ H₁], ℤ[G ⧸ H₂])`. -/
noncomputable def baseChange :
    HeckeBimodule k H₁ H₂ ≃ₗ[k] TensorProduct ℤ k (HeckeBimodule ℤ H₁ H₂) :=
  open scoped Classical in mkLinearEquiv.symm.trans <|
    (TensorProduct.finsuppScalarRight ℤ k k (DoubleCoset₀ H₁ H₂)).symm.trans <|
    LinearEquiv.baseChange ℤ k _ _ mkLinearEquiv

@[simp]
lemma baseChange_mk (x : DoubleCoset₀ H H) :
    baseChange (mk x) = (1 : k) ⊗ₜ mk x := by
  simp [baseChange]

@[simp]
lemma baseChang_symm_mk (r : k) (x : DoubleCoset₀ H H) :
    baseChange.symm (r ⊗ₜ mk x) = r • mk x :=
  baseChange.injective (by simp [TensorProduct.smul_tmul'])

end BaseChange

section global

/-- The linearization of `mk` gives a linear equivalence from `k[H₁\G/H₂]` to the
Hecke bimodule `Hom_G(k[G ⧸ H₁], k[G ⧸ H₂])`, provided global `IsLeftFinite` instance. -/
noncomputable def mkLinearEquiv₀ [h : ∀ g, IsLeftFinite H₁ H₂ g] :
    (Quotient (H₁ : Set G) (H₂ : Set G) →₀ k) ≃ₗ[k] HeckeBimodule k H₁ H₂ :=
  (Finsupp.mapDomain.linearEquiv k k DoubleCoset.Quotient.equiv₀).trans mkLinearEquiv

@[simp]
lemma mkLinearEquiv₀_apply_single [∀ g, IsLeftFinite H₁ H₂ g] (r : k)
    (x : Quotient (H₁ : Set G) (H₂ : Set G)) :
    mkLinearEquiv₀ (.single x r) = r • mk x.equiv₀ := by
  simp [mkLinearEquiv₀]

@[simp]
lemma mkLinearEquiv₀_symm_apply_mk [∀ g, IsLeftFinite H₁ H₂ g]
    (x : Quotient (H₁ : Set G) (H₂ : Set G)) :
    mkLinearEquiv₀.symm (mk x.equiv₀) = .single x (1 : k) := by
  simp [mkLinearEquiv₀]

end global

end Representation.HeckeBimodule
