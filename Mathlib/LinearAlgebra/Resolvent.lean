/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Resolvent of partially defined linear maps

This file defines the resolvent set and the resolvent as a linear map for partially defined linear
maps.

Since `E →ₗ.[R] E` is not an algebra, we cannot use the abstract theory. However, we prove that for
everywhere defined linear maps, the abstract definitions coincide with the ones for `E →ₗ.[R] E`.

## Main definitions

- `LinearPMap.resolventSet`: the set of points `z : R` where `z - f` is bijective.
- `LinearPMap.resolventLM`: the inverse of `z - f` as a linear map if `z` is in the resolvent set
  and `0` otherwise.

## Main statements

- `LinearPMap.resolventLM_apply_eq`: the fundamental property of the resolvent
- `LinearPMap.resolventLM_sub_resolventLM`: the first resolvent identity
- `LinearPMap.resolventLM_sub_resolventLM'`: the second resolvent identity

-/

@[expose] public section

namespace LinearPMap

variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

section resolvent

variable {f : E →ₗ.[R] E} {z : R}

/-- The resolvent set of a `LinearPMap`.

This definition only agrees with the conventional one only if `f` is closed, but if that is not
the case, then the conventional definition yields that `f.resolventSet = univ`
We use this definition for convenience and since it makes fewer assumptions. -/
protected def resolventSet (f : E →ₗ.[R] E) : Set R :=
  { z | Function.Bijective (z • LinearMap.id (R := R) (M := E) +ᵥ -f : E →ₗ.[R] E) }

@[simp]
theorem mem_resolventSet_iff (f : E →ₗ.[R] E) (z : R) : z ∈ f.resolventSet ↔
    Function.Bijective (z • LinearMap.id (R := R) (M := E) +ᵥ -f : E →ₗ.[R] E) := by rfl

@[simp, grind .]
theorem _root_.LinearMap.resolventSet_toPMap (g : E →ₗ[R] E) :
    (g.toPMap ⊤).resolventSet = resolventSet R g := by
  ext z
  rw [spectrum.mem_resolventSet_iff, mem_resolventSet_iff, Module.End.isUnit_iff]
  simp only [vadd_domain, neg_domain, LinearMap.toPMap_domain, coe_vadd]
  rw [← EquivLike.bijective_comp Submodule.topEquiv.symm]
  congrm Function.Bijective ?_
  ext x
  simp [sub_eq_add_neg]

open Classical in
/-- The resolvent of a `LinearPMap` as a `LinearMap`.

This definition is only used to deduce algebraic properties, which hold without any reference to
the topology. In particular, we prove the first and second resolvent identity.
-/
noncomputable def resolventLM (f : E →ₗ.[R] E) (z : R) : E →ₗ[R] E :=
    if hz : z ∈ f.resolventSet then
      (z • LinearMap.id +ᵥ -f : E →ₗ.[R] E).inverseLM hz.2
    else 0

theorem resolventLM_apply_apply (hz : z ∈ f.resolventSet) :
    f.resolventLM z = (z • LinearMap.id +ᵥ -f : E →ₗ.[R] E).inverseLM hz.2 := by
  simp [resolventLM, hz]

theorem resolventLM_apply_eq (hz : z ∈ f.resolventSet) {x y : E} (hx : x ∈ f.domain)
    (hxy : z • x - f ⟨x, hx⟩ = y) :
    f.resolventLM z y = x := by
  rw [resolventLM_apply_apply hz]
  apply inverseLM_apply_eq (by simpa using hz)
  simpa [sub_eq_add_neg] using hxy

@[simp, grind .]
theorem resolventLM_of_notMem_resolventSet (hz : z ∉ f.resolventSet) :
    f.resolventLM z = 0 := by
  simp [resolventLM, hz]

@[simp]
theorem _root_.LinearMap.resolventLM_toPMap_eq_resolvent (g : E →ₗ[R] E) :
    (g.toPMap ⊤).resolventLM = resolvent (R := R) g := by
  ext z : 1
  by_cases h : z ∈ resolventSet R g
  · symm
    rw [spectrum.resolvent_eq_iff_mul_right_eq_one h]
    ext x
    exact resolventLM_apply_eq (by simpa) (by simp) (by simp)
  · rw [spectrum.resolvent_zero_of_mem_spectrum h]
    grind

/-- The range of the resolvent `R(f, z)` is equal to the domain of `f` for any `z` in the resolvent
set. -/
@[simp, grind .]
theorem range_resolventLM (hz : z ∈ f.resolventSet) :
    (f.resolventLM z).range = f.domain := by
  simp [resolventLM, hz, range_inverseLM hz]

/-- The first resolvent identity. -/
theorem resolventLM_sub_resolventLM {z₁ z₂ : R} (hz₁ : z₁ ∈ f.resolventSet)
    (hz₂ : z₂ ∈ f.resolventSet) :
    f.resolventLM z₁ - f.resolventLM z₂ = (z₂ - z₁) • f.resolventLM z₁ ∘ₗ f.resolventLM z₂ := by
  rw [resolventLM_apply_apply hz₁, resolventLM_apply_apply hz₂,
    inverseLM_sub_inverseLM_eq hz₁ hz₂ (by simp), ← LinearMap.comp_smul]
  congr 1
  ext x
  rw [LinearMap.smul_apply, compLinearMap_apply (by simp [range_inverseLM hz₂, sub_domain])]
  simp [sub_apply, vadd_apply, vadd_apply, ← sub_smul]

theorem resolventLM_comm [IsCancelMulZero R] [Module.IsTorsionFree R E]
    {z₁ z₂ : R} (hz₁ : z₁ ∈ f.resolventSet) (hz₂ : z₂ ∈ f.resolventSet) :
    f.resolventLM z₁ ∘ₗ f.resolventLM z₂ = f.resolventLM z₂ ∘ₗ f.resolventLM z₁ := by
  by_cases hz : z₁ = z₂
  · rw [hz]
  have h₁ := resolventLM_sub_resolventLM hz₁ hz₂
  have h₂ := resolventLM_sub_resolventLM hz₂ hz₁
  have : (z₁ - z₂) • f.resolventLM z₂ ∘ₗ f.resolventLM z₁ =
      -((z₂ - z₁) • f.resolventLM z₁ ∘ₗ f.resolventLM z₂) := by grind
  rw [← neg_smul, neg_sub] at this
  grind [smul_cancel_of_non_zero_divisor, smul_eq_zero_iff_right]

/-- The second resolvent identity -/
theorem resolventLM_sub_resolventLM' {f g : E →ₗ.[R] E} {z : R} (hz₁ : z ∈ f.resolventSet)
    (hz₂ : z ∈ g.resolventSet) (hfg : g.domain ≤ f.domain) :
    f.resolventLM z - g.resolventLM z =
      f.resolventLM z ∘ₗ ((f - g).compLinearMap (g.resolventLM z)) := by
  rw [resolventLM_apply_apply hz₁, resolventLM_apply_apply hz₂,
    inverseLM_sub_inverseLM_eq hz₁ hz₂ (by simpa)]
  congr 2
  ext x hf hg : 1
  · simpa [sub_domain] using inf_comm g.domain f.domain
  · simpa [sub_apply] using neg_add_eq_sub _ _

end resolvent

end LinearPMap
