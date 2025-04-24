/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Exact

/-!
# The five lemma in terms of modules

The five lemma for all abelian categories is proven in
`CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`. But for universe generality
and ease of application in the unbundled setting, we reprove them here.

## Main results

- `LinearMap.surjective_of_surjective_of_surjective_of_injective`: a four lemma
- `LinearMap.injective_of_surjective_of_injective_of_injective`: another four lemma
- `LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective`: the five lemma

## Explanation of the variables

In this file we always consider the following commutative diagram of additive groups (resp. modules)

```
M₁ --f₁--> M₂ --f₂--> M₃ --f₃--> M₄ --f₄--> M₅
|          |          |          |          |
i₁         i₂         i₃         i₄         i₅
|          |          |          |          |
v          v          v          v          v
N₁ --g₁--> N₂ --g₂--> N₃ --g₃--> N₄ --g₄--> N₅
```

with exact rows.

## Implementation details

In theory, we could prove these in the multiplicative version and let `to_additive` prove
the additive variants. But `Function.Exact` currently has no multiplicative analogue (yet).
-/

namespace AddMonoidHom

variable {M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅ : Type*}
variable [AddGroup M₁] [AddGroup M₂] [AddGroup M₃] [AddGroup M₄] [AddGroup M₅]
variable [AddGroup N₁] [AddGroup N₂] [AddGroup N₃] [AddGroup N₄] [AddGroup N₅]
variable (f₁ : M₁ →+ M₂) (f₂ : M₂ →+ M₃) (f₃ : M₃ →+ M₄) (f₄ : M₄ →+ M₅)
variable (g₁ : N₁ →+ N₂) (g₂ : N₂ →+ N₃) (g₃ : N₃ →+ N₄) (g₄ : N₄ →+ N₅)
variable (i₁ : M₁ →+ N₁) (i₂ : M₂ →+ N₂) (i₃ : M₃ →+ N₃) (i₄ : M₄ →+ N₄)
  (i₅ : M₅ →+ N₅)
variable (hc₁ : g₁.comp i₁ = i₂.comp f₁) (hc₂ : g₂.comp i₂ = i₃.comp f₂)
  (hc₃ : g₃.comp i₃ = i₄.comp f₃) (hc₄ : g₄.comp i₄ = i₅.comp f₄)
variable (hf₁ : Function.Exact f₁ f₂) (hf₂ : Function.Exact f₂ f₃) (hf₃ : Function.Exact f₃ f₄)
variable (hg₁ : Function.Exact g₁ g₂) (hg₂ : Function.Exact g₂ g₃) (hg₃ : Function.Exact g₃ g₄)

include hf₂ hg₁ hg₂ hc₁ hc₂ hc₃ in
/-- One four lemma in terms of (additive) groups. For a diagram explaining the variables,
see the module docstring. -/
lemma surjective_of_surjective_of_surjective_of_injective (hi₁ : Function.Surjective i₁)
    (hi₃ : Function.Surjective i₃) (hi₄ : Function.Injective i₄) :
    Function.Surjective i₂ := by
  intro x
  obtain ⟨y, hy⟩ := hi₃ (g₂ x)
  obtain ⟨a, rfl⟩ : y ∈ Set.range f₂ := (hf₂ _).mp <| by
    simpa [hy, hg₂.apply_apply_eq_zero, map_eq_zero_iff _ hi₄] using (DFunLike.congr_fun hc₃ y).symm
  obtain ⟨b, hb⟩ : x - i₂ a ∈ Set.range g₁ := (hg₁ _).mp <| by
    simp [← hy, show g₂ (i₂ a) = i₃ (f₂ a) by simpa using DFunLike.congr_fun hc₂ a]
  obtain ⟨o, rfl⟩ := hi₁ b
  use f₁ o + a
  simp [← show g₁ (i₁ o) = i₂ (f₁ o) by simpa using DFunLike.congr_fun hc₁ o, hb]

include hf₁ hf₂ hg₁ hc₁ hc₂ hc₃ in
/-- One four lemma in terms of (additive) groups. For a diagram explaining the variables,
see the module docstring. -/
lemma injective_of_surjective_of_injective_of_injective (hi₁ : Function.Surjective i₁)
    (hi₂ : Function.Injective i₂) (hi₄ : Function.Injective i₄) : Function.Injective i₃ := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨x, rfl⟩ := (hf₂ m).mp <| by
    suffices h : i₄ (f₃ m) = 0 by rwa [map_eq_zero_iff _ hi₄] at h
    simp [← show g₃ (i₃ m) = i₄ (f₃ m) by simpa using DFunLike.congr_fun hc₃ m, hm]
  obtain ⟨y, hy⟩ := (hg₁ _).mp <| by
    rwa [show g₂ (i₂ x) = i₃ (f₂ x) by simpa using DFunLike.congr_fun hc₂ x]
  obtain ⟨a, rfl⟩ := hi₁ y
  rw [show g₁ (i₁ a) = i₂ (f₁ a) by simpa using DFunLike.congr_fun hc₁ a] at hy
  apply hi₂ at hy
  subst hy
  rw [hf₁.apply_apply_eq_zero]

include hf₁ hf₂ hf₃ hg₁ hg₂ hg₃ hc₁ hc₂ hc₃ hc₄ in
/-- The five lemma in terms of (additive) groups. For a diagram explaining the variables,
see the module docstring. -/
lemma bijective_of_surjective_of_bijective_of_bijective_of_injective (hi₁ : Function.Surjective i₁)
    (hi₂ : Function.Bijective i₂) (hi₄ : Function.Bijective i₄) (hi₅ : Function.Injective i₅) :
    Function.Bijective i₃ :=
  ⟨injective_of_surjective_of_injective_of_injective f₁ f₂ f₃ g₁ g₂ g₃ i₁ i₂ i₃ i₄
      hc₁ hc₂ hc₃ hf₁ hf₂ hg₁ hi₁ hi₂.1 hi₄.1,
    surjective_of_surjective_of_surjective_of_injective f₂ f₃ f₄ g₂ g₃ g₄ i₂ i₃ i₄ i₅
      hc₂ hc₃ hc₄ hf₃ hg₂ hg₃ hi₂.2 hi₄.2 hi₅⟩

end AddMonoidHom

namespace LinearMap

variable {R : Type*} [CommRing R]
variable {M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅ : Type*}
variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄] [AddCommGroup M₅]
variable [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Module R M₅]
variable [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [AddCommGroup N₄] [AddCommGroup N₅]
variable [Module R N₁] [Module R N₂] [Module R N₃] [Module R N₄] [Module R N₅]
variable (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃) (f₃ : M₃ →ₗ[R] M₄) (f₄ : M₄ →ₗ[R] M₅)
variable (g₁ : N₁ →ₗ[R] N₂) (g₂ : N₂ →ₗ[R] N₃) (g₃ : N₃ →ₗ[R] N₄) (g₄ : N₄ →ₗ[R] N₅)
variable (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂) (i₃ : M₃ →ₗ[R] N₃) (i₄ : M₄ →ₗ[R] N₄)
  (i₅ : M₅ →ₗ[R] N₅)
variable (hc₁ : g₁.comp i₁ = i₂.comp f₁) (hc₂ : g₂.comp i₂ = i₃.comp f₂)
  (hc₃ : g₃.comp i₃ = i₄.comp f₃) (hc₄ : g₄.comp i₄ = i₅.comp f₄)
variable (hf₁ : Function.Exact f₁ f₂) (hf₂ : Function.Exact f₂ f₃) (hf₃ : Function.Exact f₃ f₄)
variable (hg₁ : Function.Exact g₁ g₂) (hg₂ : Function.Exact g₂ g₃) (hg₃ : Function.Exact g₃ g₄)

include hf₂ hg₁ hg₂ hc₁ hc₂ hc₃ in
/-- One four lemma in terms of modules. For a diagram explaining the variables,
see the module docstring. -/
lemma surjective_of_surjective_of_surjective_of_injective (hi₁ : Function.Surjective i₁)
    (hi₃ : Function.Surjective i₃) (hi₄ : Function.Injective i₄) :
    Function.Surjective i₂ :=
  AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
    f₁.toAddMonoidHom f₂.toAddMonoidHom f₃.toAddMonoidHom g₁.toAddMonoidHom g₂.toAddMonoidHom
    g₃.toAddMonoidHom i₁.toAddMonoidHom i₂.toAddMonoidHom i₃.toAddMonoidHom i₄.toAddMonoidHom
    (AddMonoidHom.ext fun x ↦ DFunLike.congr_fun hc₁ x)
    (AddMonoidHom.ext fun x ↦ DFunLike.congr_fun hc₂ x)
    (AddMonoidHom.ext fun x ↦ DFunLike.congr_fun hc₃ x) hf₂ hg₁ hg₂ hi₁ hi₃ hi₄

include hf₁ hf₂ hg₁ hc₁ hc₂ hc₃ in
/-- One four lemma in terms of modules. For a diagram explaining the variables,
see the module docstring. -/
lemma injective_of_surjective_of_injective_of_injective (hi₁ : Function.Surjective i₁)
    (hi₂ : Function.Injective i₂) (hi₄ : Function.Injective i₄) :
    Function.Injective i₃ :=
  AddMonoidHom.injective_of_surjective_of_injective_of_injective
    f₁.toAddMonoidHom f₂.toAddMonoidHom f₃.toAddMonoidHom g₁.toAddMonoidHom g₂.toAddMonoidHom
    g₃.toAddMonoidHom i₁.toAddMonoidHom i₂.toAddMonoidHom i₃.toAddMonoidHom i₄.toAddMonoidHom
    (AddMonoidHom.ext fun x ↦ DFunLike.congr_fun hc₁ x)
    (AddMonoidHom.ext fun x ↦ DFunLike.congr_fun hc₂ x)
    (AddMonoidHom.ext fun x ↦ DFunLike.congr_fun hc₃ x) hf₁ hf₂ hg₁ hi₁ hi₂ hi₄

include hf₁ hf₂ hf₃ hg₁ hg₂ hg₃ hc₁ hc₂ hc₃ hc₄ in
/-- The five lemma in terms of modules. For a diagram explaining the variables,
see the module docstring. -/
lemma bijective_of_surjective_of_bijective_of_bijective_of_injective (hi₁ : Function.Surjective i₁)
    (hi₂ : Function.Bijective i₂) (hi₄ : Function.Bijective i₄) (hi₅ : Function.Injective i₅) :
    Function.Bijective i₃ :=
  ⟨injective_of_surjective_of_injective_of_injective f₁ f₂ f₃ g₁ g₂ g₃ i₁ i₂ i₃ i₄
      hc₁ hc₂ hc₃ hf₁ hf₂ hg₁ hi₁ hi₂.1 hi₄.1,
    surjective_of_surjective_of_surjective_of_injective f₂ f₃ f₄ g₂ g₃ g₄ i₂ i₃ i₄ i₅
      hc₂ hc₃ hc₄ hf₃ hg₂ hg₃ hi₂.2 hi₄.2 hi₅⟩

end LinearMap
