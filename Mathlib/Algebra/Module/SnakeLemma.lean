/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Exact

/-!

# The snake lemma in terms of modules

The snake lemma is proven in `Mathlib/Algebra/Homology/ShortComplex/SnakeLemma.lean` for all abelian
categories, but for definitional equality and universe issues we reprove them here for modules.

## Main results
- `SnakeLemma.δ`: The connecting homomorphism guaranteed by the snake lemma.
- `SnakeLemma.exact_δ_left`: The connecting homomorphism is exact on the right.
- `SnakeLemma.exact_δ_right`: The connecting homomorphism is exact on the left.

-/

open LinearMap hiding id
open Function

/-!
Suppose we have an exact commutative diagram
```
        K₂ -F-→ K₃
        |       |
        ι₂      ι₃
        ↓       ↓
M₁ -f₁→ M₂ -f₂→ M₃
|       |       |
i₁      i₂      i₃
↓       ↓       ↓
N₁ -g₁→ N₂ -g₂→ N₃
|       |
π₁      π₂
↓       ↓
C₁ -G-→ C₂

```
such that `f₂` is surjective with a (set-theoretic) section `σ`, `g₁` is injective with a
(set-theoretic) retraction `ρ`, and that `ι₃` is injective and `π₁` is surjective.
-/

variable {R} [CommRing R] {M₁ M₂ M₃ N₁ N₂ N₃}
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
  [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃] [Module R N₃]
  (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂) (i₃ : M₃ →ₗ[R] N₃)
  (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃) (hf : Exact f₁ f₂)
  (g₁ : N₁ →ₗ[R] N₂) (g₂ : N₂ →ₗ[R] N₃) (hg : Exact g₁ g₂)
  (h₁ : g₁.comp i₁ = i₂.comp f₁) (h₂ : g₂.comp i₂ = i₃.comp f₂)
  (σ : M₃ → M₂) (hσ : f₂ ∘ σ = id) (ρ : N₂ → N₁) (hρ : ρ ∘ g₁ = id)
  {K₂ K₃ C₁ C₂} [AddCommGroup K₂] [Module R K₂] [AddCommGroup K₃] [Module R K₃]
  [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂]
  (ι₂ : K₂ →ₗ[R] M₂) (hι₂ : Exact ι₂ i₂) (ι₃ : K₃ →ₗ[R] M₃) (hι₃ : Exact ι₃ i₃)
  (π₁ : N₁ →ₗ[R] C₁) (hπ₁ : Exact i₁ π₁) (π₂ : N₂ →ₗ[R] C₂) (hπ₂ : Exact i₂ π₂)

include hg hρ h₂ hσ hι₃ in
lemma SnakeLemma.δ_aux (x : K₃) : g₁ (ρ (i₂ (σ (ι₃ x)))) = i₂ (σ (ι₃ x)) := by
  obtain ⟨d, hd⟩ : i₂ (σ (ι₃ x)) ∈ range g₁ := by
    rw [← hg.linearMap_ker_eq, mem_ker, show g₂ (i₂ _) = i₃ (f₂ _) from DFunLike.congr_fun h₂ _,
      ← @comp_apply _ _ _ f₂ σ, hσ, id_eq, ← i₃.comp_apply,
      hι₃.linearMap_comp_eq_zero, zero_apply]
  rw [← hd, ← ρ.comp_apply, hρ, id_eq]

include hf h₁ hρ hπ₁ in
lemma SnakeLemma.eq_of_eq (x : K₃)
    (y₁) (hy₁ : f₂ y₁ = ι₃ x) (z₁) (hz₁ : g₁ z₁ = i₂ y₁)
    (y₂) (hy₂ : f₂ y₂ = ι₃ x) (z₂) (hz₂ : g₁ z₂ = i₂ y₂) : π₁ z₁ = π₁ z₂ := by
  have := sub_eq_zero.mpr (hy₁.trans hy₂.symm)
  rw [← map_sub, hf] at this
  obtain ⟨d, hd⟩ := this
  rw [← eq_sub_iff_add_eq.mp hd, map_add, ← hz₂, ← sub_eq_iff_eq_add, ← map_sub,
    ← i₂.comp_apply, ← h₁, LinearMap.comp_apply,
    (HasLeftInverse.injective ⟨ρ, congr_fun hρ⟩).eq_iff] at hz₁
  rw [← sub_eq_zero, ← map_sub, hz₁, hπ₁]
  exact ⟨_, rfl⟩

/--
**Snake Lemma**
Suppose we have an exact commutative diagram
```
                K₃
                |
                ι₃
                ↓
M₁ -f₁→ M₂ -f₂→ M₃
|       |       |
i₁      i₂      i₃
↓       ↓       ↓
N₁ -g₁→ N₂ -g₂→ N₃
|
π₁
↓
C₁

```
such that `f₂` is surjective with a (set-theoretic) section `σ`, `g₁` is injective with a
(set-theoretic) retraction `ρ`,
then the map `π₁ ∘ ρ ∘ i₂ ∘ σ ∘ ι₃` is a linear map from `K₃` to `C₁`.

Also see `SnakeLemma.δ'` for a noncomputable version
that does not require an explicit section and retraction.
-/
def SnakeLemma.δ : K₃ →ₗ[R] C₁ :=
  haveI H₁ : ∀ x, f₂ (σ x) = x := congr_fun hσ
  haveI H₂ := δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃
  { toFun := fun x ↦ π₁ (ρ (i₂ (σ (ι₃ x))))
    map_add' := fun x y ↦ by
      rw [← map_add]
      exact eq_of_eq i₁ i₂ f₁ f₂ hf g₁ h₁ ρ hρ ι₃ π₁ hπ₁ (x + y) _ (H₁ _) _ (H₂ _)
        (σ (ι₃ x) + σ (ι₃ y)) (by simp only [map_add, H₁]) _ (by simp only [map_add, H₂])
    map_smul' := fun r x ↦ by
      simp only [← map_smul, RingHom.id_apply]
      apply eq_of_eq i₁ i₂ f₁ f₂ hf g₁ h₁ ρ hρ ι₃ π₁ hπ₁ (r • x) _ (H₁ _) _ (H₂ _)
        (r • σ (ι₃ x)) (by simp only [map_smul, H₁]) _ (by simp only [map_smul, H₂]) }

lemma SnakeLemma.δ_eq (x : K₃) (y) (hy : f₂ y = ι₃ x) (z) (hz : g₁ z = i₂ y) :
    δ i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ σ hσ ρ hρ ι₃ hι₃ π₁ hπ₁ x = π₁ z :=
  eq_of_eq i₁ i₂ f₁ f₂ hf g₁ h₁ ρ hρ ι₃ π₁ hπ₁ x _ (congr_fun hσ _) _
    (δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃ _) y hy z hz

include hι₂ in
/--
Suppose we have an exact commutative diagram
```
        K₂ -F-→ K₃
        |       |
        ι₂      ι₃
        ↓       ↓
M₁ -f₁→ M₂ -f₂→ M₃
|       |       |
i₁      i₂      i₃
↓       ↓       ↓
N₁ -g₁→ N₂ -g₂→ N₃
|
π₁
↓
C₁

```
such that `f₂` is surjective with a (set-theoretic) section `σ`, `g₁` is injective with a
(set-theoretic) retraction `ρ`, and `ι₃` is injective, then `K₂ -F→ K₃ -δ→ C₁` is exact.
-/
lemma SnakeLemma.exact_δ_right (F : K₂ →ₗ[R] K₃) (hF : f₂.comp ι₂ = ι₃.comp F)
    (h : Injective ι₃) :
    Exact F (δ i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ σ hσ ρ hρ ι₃ hι₃ π₁ hπ₁) := by
  haveI H₁ : ∀ x, f₂ (σ x) = x := congr_fun hσ
  haveI H₂ := δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃
  intro x
  constructor
  · intro H
    obtain ⟨y, hy⟩ := (hπ₁ _).mp H
    obtain ⟨k, hk⟩ : σ (ι₃ x) - f₁ y ∈ Set.range ι₂ := by
      rw [← hι₂, map_sub, ← H₂, ← hy, sub_eq_zero]; exact congr($h₁ y)
    refine ⟨k, h ?_⟩
    rw [← ι₃.comp_apply, ← hF, f₂.comp_apply, hk, map_sub, H₁, hf.apply_apply_eq_zero, sub_zero]
  · rintro ⟨y, rfl⟩
    exact (δ_eq i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ σ hσ ρ hρ ι₃ hι₃ π₁ hπ₁ _ (ι₂ y) congr($hF y)
      _ (by rw [map_zero, hι₂.apply_apply_eq_zero])).trans π₁.map_zero

include hπ₂ in
/--
Suppose we have an exact commutative diagram
```
                K₃
                |
                ι₃
                ↓
M₁ -f₁→ M₂ -f₂→ M₃
|       |       |
i₁      i₂      i₃
↓       ↓       ↓
N₁ -g₁→ N₂ -g₂→ N₃
|       |
π₁      π₂
↓       ↓
C₁ -G-→ C₂

```
such that `f₂` is surjective with a (set-theoretic) section `σ`, `g₁` is injective with a
(set-theoretic) retraction `ρ`, and `π₁` is surjective, then `K₃ -δ→ C₁ -G→ C₂` is exact.
-/
lemma SnakeLemma.exact_δ_left (G : C₁ →ₗ[R] C₂) (hF : G.comp π₁ = π₂.comp g₁) (h : Surjective π₁) :
    Exact (δ i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ σ hσ ρ hρ ι₃ hι₃ π₁ hπ₁) G := by
  haveI H₁ : ∀ x, f₂ (σ x) = x := congr_fun hσ
  haveI H₂ := δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃
  intro x
  constructor
  · intro H
    obtain ⟨x, rfl⟩ := h x
    obtain ⟨y, hy⟩ := (hπ₂ (g₁ x)).mp (by simpa only [← LinearMap.comp_apply, hF] using H)
    obtain ⟨z, hz⟩ : f₂ y ∈ range ι₃ := (hι₃ (f₂ y)).mp (by rw [← i₃.comp_apply, ← h₂,
      g₂.comp_apply, hy, hg.apply_apply_eq_zero])
    exact ⟨z, δ_eq i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ σ hσ ρ hρ ι₃ hι₃ π₁ hπ₁ _ _ hz.symm _ hy.symm⟩
  · rintro ⟨x, rfl⟩
    simp only [δ, coe_mk, AddHom.coe_mk]
    rw [← G.comp_apply, hF, π₂.comp_apply, H₂, hπ₂.apply_apply_eq_zero]

/--
Suppose we have an exact commutative diagram
```
                K₃
                |
                ι₃
                ↓
M₁ -f₁→ M₂ -f₂→ M₃
|       |       |
i₁      i₂      i₃
↓       ↓       ↓
N₁ -g₁→ N₂ -g₂→ N₃
|
π₁
↓
C₁

```
such that `f₂` is surjective and `g₁` is injective,
then this is the linear map `K₃ → C₁` given by the snake lemma.

Also see `SnakeLemma.δ` for a computable version.
-/
noncomputable def SnakeLemma.δ' (hf₂ : Surjective f₂) (hg₁ : Injective g₁) : K₃ →ₗ[R] C₁ :=
  δ i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ _ (funext (surjInv_eq hf₂)) _ (invFun_comp hg₁) ι₃ hι₃ π₁ hπ₁

lemma SnakeLemma.δ'_eq (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
    (x : K₃) (y) (hy : f₂ y = ι₃ x) (z) (hz : g₁ z = i₂ y) :
    δ' i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ ι₃ hι₃ π₁ hπ₁ hf₂ hg₁ x = π₁ z :=
  SnakeLemma.δ_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› ‹_› _ ‹_›

include hι₂ in
/--
Suppose we have an exact commutative diagram
```
        K₂ -F-→ K₃
        |       |
        ι₂      ι₃
        ↓       ↓
M₁ -f₁→ M₂ -f₂→ M₃
|       |       |
i₁      i₂      i₃
↓       ↓       ↓
N₁ -g₁→ N₂ -g₂→ N₃
|
π₁
↓
C₁

```
such that `f₂` is surjective, `g₁` is injective, and `ι₃` is injective,
then `K₂ -F→ K₃ -δ→ C₁` is exact.
-/
lemma SnakeLemma.exact_δ'_right (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
    (F : K₂ →ₗ[R] K₃) (hF : f₂.comp ι₂ = ι₃.comp F) (h : Injective ι₃) :
    Exact F (δ' i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ ι₃ hι₃ π₁ hπ₁ hf₂ hg₁) :=
  SnakeLemma.exact_δ_right _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› _ _ _ _ _ ‹_› ‹_›

include hπ₂ in
/--
Suppose we have an exact commutative diagram
```
                K₃
                |
                ι₃
                ↓
M₁ -f₁→ M₂ -f₂→ M₃
|       |       |
i₁      i₂      i₃
↓       ↓       ↓
N₁ -g₁→ N₂ -g₂→ N₃
|       |
π₁      π₂
↓       ↓
C₁ -G-→ C₂

```
such that `f₂` is surjective, `g₁` is injective, and `π₁` is surjective,
then `K₃ -δ→ C₁ -G→ C₂` is exact.
-/
lemma SnakeLemma.exact_δ'_left (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
    (G : C₁ →ₗ[R] C₂) (hF : G.comp π₁ = π₂.comp g₁) (h : Surjective π₁) :
    Exact (δ' i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ ι₃ hι₃ π₁ hπ₁ hf₂ hg₁) G :=
  SnakeLemma.exact_δ_left _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› _ ‹_› ‹_›
