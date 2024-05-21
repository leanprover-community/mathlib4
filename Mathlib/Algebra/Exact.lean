/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Prod


/-! # Exactness of a pair

* For two maps `f : M → N` and `g : N → P`, with `Zero P`,
`Function.AddExact f g` says that `Set.range f = Set.preimage {0}

* For two maps `f : M → N` and `g : N → P`, with `One P`,
`Function.Exact f g` says that `Set.range f = Set.preimage {1}

* For linear maps `f : M →ₗ[R] N`  and `g : N →ₗ[R] P`,
`Exact f g` says that `range f = ker g``

## TODO :

* add the cases of `AddMonoidHom`

* add the multiplicative case (`Function.Exact` will become `Function.AddExact`?)
-/


namespace Function

variable {M N P : Type*}

section Function

variable (f : M → N) (g : N → P)

/-- The maps `f` and `g` form an exact pair :
  `g y = 0` iff `y` belongs to the image of `f` -/
def Exact [Zero P] : Prop := ∀ y, g y = 0 ↔ y ∈ Set.range f

variable {f g}

lemma Exact.comp_eq_zero [Zero P] (h : Exact f g) : g.comp f = 0 :=
  funext fun _ => (h _).mpr <| Set.mem_range_self _

lemma Exact.apply_eq_zero [Zero P] (h : Exact f g) (x) : g (f x) = 0 := congr_fun h.comp_eq_zero x

end Function

section LinearMap

open LinearMap

variable {R : Type*} [Semiring R]

section

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R N] [Module R P]

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

lemma Exact.linearMap_ker_eq (hfg : Exact f g) : ker g = range f :=
  SetLike.ext hfg

lemma LinearMap.exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap.range f :=
  Iff.symm <| SetLike.ext_iff

lemma Exact.linearMap_comp_eq_zero (h : Exact f g) : g.comp f = 0 :=
  DFunLike.coe_injective h.comp_eq_zero

end

section split

variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

open LinearMap

/-- Given an exact sequence `0 → M → N → P`, giving a section `P → N` is equivalent to giving a
splitting `N ≃ M × P`. -/
noncomputable
def Exact.splitSurjectiveEquiv (h : Function.Exact f g) (hf : Function.Injective f) :
    { l // g ∘ₗ l = .id } ≃
      { e : N ≃ₗ[R] M × P // f = e.symm ∘ₗ inl R M P ∧ g = snd R M P ∘ₗ e } := by
  refine
  { toFun := fun l ↦ ⟨(LinearEquiv.ofBijective (f ∘ₗ fst R M P + l.1 ∘ₗ snd R M P) ?_).symm, ?_⟩
    invFun := fun e ↦ ⟨e.1.symm ∘ₗ inr R M P, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h₁ : ∀ x, g (l.1 x) = x := LinearMap.congr_fun l.2
    have h₂ : ∀ x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · intros x y e
      simp only [add_apply, coe_comp, comp_apply, fst_apply, snd_apply] at e
      suffices x.2 = y.2 from Prod.ext (hf (by rwa [this, add_left_inj] at e)) this
      simpa [h₁, h₂] using DFunLike.congr_arg g e
    · intro x
      obtain ⟨y, hy⟩ := (h (x - l.1 (g x))).mp (by simp [h₁, g.map_sub])
      exact ⟨⟨y, g x⟩, by simp [hy]⟩
  · have h₁ : ∀ x, g (l.1 x) = x := LinearMap.congr_fun l.2
    have h₂ : ∀ x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · ext; simp
    · rw [LinearEquiv.eq_comp_toLinearMap_symm]
      ext <;> simp [h₁, h₂]
  · rw [← LinearMap.comp_assoc, (LinearEquiv.eq_comp_toLinearMap_symm _ _).mp e.2.2]; rfl
  · intro; ext; simp
  · rintro ⟨e, rfl, rfl⟩
    ext1
    apply LinearEquiv.symm_bijective.injective
    ext
    apply e.injective
    ext <;> simp

/-- Given an exact sequence `M → N → P → 0`, giving a retraction `N → M` is equivalent to giving a
splitting `N ≃ M × P`. -/
noncomputable
def Exact.splitInjectiveEquiv
    {R M N P} [Semiring R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) (hg : Function.Surjective g) :
    { l // l ∘ₗ f = .id } ≃
      { e : N ≃ₗ[R] M × P // f = e.symm ∘ₗ inl R M P ∧ g = snd R M P ∘ₗ e } := by
  refine
  { toFun := fun l ↦ ⟨(LinearEquiv.ofBijective (l.1.prod g) ?_), ?_⟩
    invFun := fun e ↦ ⟨fst R M P ∘ₗ e.1, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h₁ : ∀ x, l.1 (f x) = x := LinearMap.congr_fun l.2
    have h₂ : ∀ x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · intros x y e
      simp only [prod_apply, Pi.prod, Prod.mk.injEq] at e
      obtain ⟨z, hz⟩ := (h (x - y)).mp (by simpa [sub_eq_zero] using e.2)
      suffices z = 0 by rw [← sub_eq_zero, ← hz, this, map_zero]
      rw [← h₁ z, hz, map_sub, e.1, sub_self]
    · rintro ⟨x, y⟩
      obtain ⟨y, rfl⟩ := hg y
      refine ⟨f x + y - f (l.1 y), by ext <;> simp [h₁, h₂]⟩
  · have h₁ : ∀ x, l.1 (f x) = x := LinearMap.congr_fun l.2
    have h₂ : ∀ x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · rw [LinearEquiv.eq_toLinearMap_symm_comp]
      ext <;> simp [h₁, h₂]
    · ext; simp
  · rw [LinearMap.comp_assoc, (LinearEquiv.eq_toLinearMap_symm_comp _ _).mp e.2.1]; rfl
  · intro; ext; simp
  · rintro ⟨e, rfl, rfl⟩
    ext x <;> simp

theorem Exact.split_tfae' (h : Function.Exact f g) :
    List.TFAE [
      Function.Injective f ∧ ∃ l, g ∘ₗ l = LinearMap.id,
      Function.Surjective g ∧ ∃ l, l ∘ₗ f = LinearMap.id,
      ∃ e : N ≃ₗ[R] M × P, f = e.symm ∘ₗ LinearMap.inl R M P ∧ g = LinearMap.snd R M P ∘ₗ e] := by
  tfae_have 1 → 3
  · rintro ⟨hf, l, hl⟩
    exact ⟨_, (h.splitSurjectiveEquiv hf ⟨l, hl⟩).2⟩
  tfae_have 2 → 3
  · rintro ⟨hg, l, hl⟩
    exact ⟨_, (h.splitInjectiveEquiv hg ⟨l, hl⟩).2⟩
  tfae_have 3 → 1
  · rintro ⟨e, e₁, e₂⟩
    have : Function.Injective f := e₁ ▸ e.symm.injective.comp LinearMap.inl_injective
    refine ⟨this, ⟨_, ((h.splitSurjectiveEquiv this).symm ⟨e, e₁, e₂⟩).2⟩⟩
  tfae_have 3 → 2
  · rintro ⟨e, e₁, e₂⟩
    have : Function.Surjective g := e₂ ▸ Prod.snd_surjective.comp e.surjective
    refine ⟨this, ⟨_, ((h.splitInjectiveEquiv this).symm ⟨e, e₁, e₂⟩).2⟩⟩
  tfae_finish

/-- Equivalent characterizations of split exact sequences. Also known as the **Splitting lemma**. -/
theorem Exact.split_tfae
    {R M N P} [Semiring R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    List.TFAE [
      ∃ l, g ∘ₗ l = LinearMap.id,
      ∃ l, l ∘ₗ f = LinearMap.id,
      ∃ e : N ≃ₗ[R] M × P, f = e.symm ∘ₗ LinearMap.inl R M P ∧ g = LinearMap.snd R M P ∘ₗ e] := by
  tfae_have 1 ↔ 3
  · simpa using (h.splitSurjectiveEquiv hf).nonempty_congr
  tfae_have 2 ↔ 3
  · simpa using (h.splitInjectiveEquiv hg).nonempty_congr
  tfae_finish

end split

end LinearMap

end Function
