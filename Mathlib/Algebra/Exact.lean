/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Exactness of a pair

* For two maps `f : M → N` and `g : N → P`, with `Zero P`,
  `Function.Exact f g` says that `Set.range f = Set.preimage g {0}`

* For additive maps `f : M →+ N`  and `g : N →+ P`,
  `Exact f g` says that `range f = ker g`

* For linear maps `f : M →ₗ[R] N`  and `g : N →ₗ[R] P`,
  `Exact f g` says that `range f = ker g`

## TODO :

* generalize to `SemilinearMap`, even `SemilinearMapClass`

* add the multiplicative case (`Function.Exact` will become `Function.AddExact`?)
-/



variable {R M M' N N' P P' : Type*}

namespace Function

variable (f : M → N) (g : N → P) (g' : P → P')

/-- The maps `f` and `g` form an exact pair :
  `g y = 0` iff `y` belongs to the image of `f` -/
def Exact [Zero P] : Prop := ∀ y, g y = 0 ↔ y ∈ Set.range f

variable {f g}

namespace Exact

lemma apply_apply_eq_zero [Zero P] (h : Exact f g) (x : M) :
    g (f x) = 0 := (h _).mpr <| Set.mem_range_self _

lemma comp_eq_zero [Zero P] (h : Exact f g) : g.comp f = 0 :=
  funext h.apply_apply_eq_zero

lemma of_comp_of_mem_range [Zero P] (h1 : g ∘ f = 0)
    (h2 : ∀ x, g x = 0 → x ∈ Set.range f) : Exact f g :=
  fun y => Iff.intro (h2 y) <|
    Exists.rec ((forall_apply_eq_imp_iff (p := (g · = 0))).mpr (congrFun h1) y)

lemma comp_injective [Zero P] [Zero P'] (exact : Exact f g)
    (inj : Function.Injective g') (h0 : g' 0 = 0) :
    Exact f (g' ∘ g) := by
  intro x
  refine ⟨fun H => exact x |>.mp <| inj <| h0 ▸ H, ?_⟩
  intro H
  rw [Function.comp_apply, exact x |>.mpr H, h0]

lemma of_comp_eq_zero_of_ker_in_range [Zero P] (hc : g.comp f = 0)
    (hr : ∀ y, g y = 0 → y ∈ Set.range f) :
    Exact f g :=
  fun y ↦ ⟨hr y, fun ⟨x, hx⟩ ↦ hx ▸ congrFun hc x⟩

/-- Two maps `f : M → N` and `g : N → P` are exact if and only if the induced maps
`Set.range f → N → Set.range g` are exact.

Note that if you already have an instance `[Zero (Set.range g)]` (which is unlikely) this lemma
may not apply if the zero of `Set.range g` is not definitionally equal to `⟨0, hg⟩`. -/
lemma iff_rangeFactorization [Zero P] (hg : 0 ∈ Set.range g) :
    letI : Zero (Set.range g) := ⟨⟨0, hg⟩⟩
    Exact f g ↔ Exact ((↑) : Set.range f → N) (Set.rangeFactorization g) := by
  letI : Zero (Set.range g) := ⟨⟨0, hg⟩⟩
  have : ((0 : Set.range g) : P) = 0 := rfl
  simp [Exact, Set.rangeFactorization, Subtype.ext_iff, this]

/-- If two maps `f : M → N` and `g : N → P` are exact, then the induced maps
`Set.range f → N → Set.range g` are exact.

Note that if you already have an instance `[Zero (Set.range g)]` (which is unlikely) this lemma
may not apply if the zero of `Set.range g` is not definitionally equal to `⟨0, hg⟩`. -/
lemma rangeFactorization [Zero P] (h : Exact f g) (hg : 0 ∈ Set.range g) :
    letI : Zero (Set.range g) := ⟨⟨0, hg⟩⟩
    Exact ((↑) : Set.range f → N) (Set.rangeFactorization g) :=
  (iff_rangeFactorization hg).1 h

end Exact

end Function

section AddMonoidHom

variable [AddGroup M] [AddGroup N] [AddGroup P] {f : M →+ N} {g : N →+ P}

namespace AddMonoidHom

open Function

lemma exact_iff :
    Exact f g ↔ ker g = range f :=
  Iff.symm SetLike.ext_iff

lemma exact_of_comp_eq_zero_of_ker_le_range
    (h1 : g.comp f = 0) (h2 : ker g ≤ range f) : Exact f g :=
  Exact.of_comp_of_mem_range (congrArg DFunLike.coe h1) h2

lemma exact_of_comp_of_mem_range
    (h1 : g.comp f = 0) (h2 : ∀ x, g x = 0 → x ∈ range f) : Exact f g :=
  exact_of_comp_eq_zero_of_ker_le_range h1 h2

/-- When we have a commutative diagram from a sequence of two maps to another,
such that the left vertical map is surjective, the middle vertical map is bijective and the right
vertical map is injective, then the upper row is exact iff the lower row is.
See `ShortComplex.exact_iff_of_epi_of_isIso_of_mono` in the file
`Mathlib/Algebra/Homology/ShortComplex/Exact.lean` for the categorical version of this result. -/
lemma exact_iff_of_surjective_of_bijective_of_injective
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
    (f : M₁ →+ M₂) (g : M₂ →+ M₃) (f' : N₁ →+ N₂) (g' : N₂ →+ N₃)
    (τ₁ : M₁ →+ N₁) (τ₂ : M₂ →+ N₂) (τ₃ : M₃ →+ N₃)
    (comm₁₂ : f'.comp τ₁ = τ₂.comp f)
    (comm₂₃ : g'.comp τ₂ = τ₃.comp g)
    (h₁ : Function.Surjective τ₁) (h₂ : Function.Bijective τ₂) (h₃ : Function.Injective τ₃) :
    Exact f g ↔ Exact f' g' := by
  replace comm₁₂ := DFunLike.congr_fun comm₁₂
  replace comm₂₃ := DFunLike.congr_fun comm₂₃
  dsimp at comm₁₂ comm₂₃
  constructor
  · intro h y₂
    obtain ⟨x₂, rfl⟩ := h₂.2 y₂
    constructor
    · intro hx₂
      obtain ⟨x₁, rfl⟩ := (h x₂).1 (h₃ (by simpa only [map_zero, comm₂₃] using hx₂))
      exact ⟨τ₁ x₁, by simp only [comm₁₂]⟩
    · rintro ⟨y₁, hy₁⟩
      obtain ⟨x₁, rfl⟩ := h₁ y₁
      rw [comm₂₃, (h x₂).2 _, map_zero]
      exact ⟨x₁, h₂.1 (by simpa only [comm₁₂] using hy₁)⟩
  · intro h x₂
    constructor
    · intro hx₂
      obtain ⟨y₁, hy₁⟩ := (h (τ₂ x₂)).1 (by simp only [comm₂₃, hx₂, map_zero])
      obtain ⟨x₁, rfl⟩ := h₁ y₁
      exact ⟨x₁, h₂.1 (by simpa only [comm₁₂] using hy₁)⟩
    · rintro ⟨x₁, rfl⟩
      apply h₃
      simp only [← comm₁₂, ← comm₂₃, h.apply_apply_eq_zero (τ₁ x₁), map_zero]

end AddMonoidHom

namespace Function.Exact

open AddMonoidHom

lemma addMonoidHom_ker_eq (hfg : Exact f g) :
    ker g = range f :=
  SetLike.ext hfg

lemma addMonoidHom_comp_eq_zero (h : Exact f g) : g.comp f = 0 :=
  DFunLike.coe_injective h.comp_eq_zero

section

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [AddCommMonoid X₁] [AddCommMonoid X₂] [AddCommMonoid X₃]
  [AddCommMonoid Y₁] [AddCommMonoid Y₂] [AddCommMonoid Y₃]
  (e₁ : X₁ ≃+ Y₁) (e₂ : X₂ ≃+ Y₂) (e₃ : X₃ ≃+ Y₃)
  {f₁₂ : X₁ →+ X₂} {f₂₃ : X₂ →+ X₃} {g₁₂ : Y₁ →+ Y₂} {g₂₃ : Y₂ →+ Y₃}

lemma iff_of_ladder_addEquiv (comm₁₂ : g₁₂.comp e₁ = AddMonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = AddMonoidHom.comp e₃ f₂₃) : Exact g₁₂ g₂₃ ↔ Exact f₁₂ f₂₃ :=
  (exact_iff_of_surjective_of_bijective_of_injective _ _ _ _ e₁ e₂ e₃ comm₁₂ comm₂₃
    e₁.surjective e₂.bijective e₃.injective).symm

lemma of_ladder_addEquiv_of_exact (comm₁₂ : g₁₂.comp e₁ = AddMonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = AddMonoidHom.comp e₃ f₂₃) (H : Exact f₁₂ f₂₃) : Exact g₁₂ g₂₃ :=
  (iff_of_ladder_addEquiv _ _ _ comm₁₂ comm₂₃).2 H

lemma of_ladder_addEquiv_of_exact' (comm₁₂ : g₁₂.comp e₁ = AddMonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = AddMonoidHom.comp e₃ f₂₃) (H : Exact g₁₂ g₂₃) : Exact f₁₂ f₂₃ :=
  (iff_of_ladder_addEquiv _ _ _ comm₁₂ comm₂₃).1 H

end

/-- Two maps `f : M →+ N` and `g : N →+ P` are exact if and only if the induced maps
`AddMonoidHom.range f → N → AddMonoidHom.range g` are exact. -/
lemma iff_addMonoidHom_rangeRestrict :
    Exact f g ↔ Exact f.range.subtype g.rangeRestrict :=
  iff_rangeFactorization (zero_mem g.range)

alias ⟨addMonoidHom_rangeRestrict, _⟩ := iff_addMonoidHom_rangeRestrict

end Function.Exact

end AddMonoidHom

section LinearMap

open Function

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
  [AddCommMonoid N'] [AddCommMonoid P] [AddCommMonoid P'] [Module R M]
  [Module R M'] [Module R N] [Module R N'] [Module R P] [Module R P']

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

namespace LinearMap

lemma exact_iff :
    Exact f g ↔ LinearMap.ker g = LinearMap.range f :=
  Iff.symm SetLike.ext_iff

lemma exact_of_comp_eq_zero_of_ker_le_range
    (h1 : g ∘ₗ f = 0) (h2 : ker g ≤ range f) : Exact f g :=
  Exact.of_comp_of_mem_range (congrArg DFunLike.coe h1) h2

lemma exact_of_comp_of_mem_range
    (h1 : g ∘ₗ f = 0) (h2 : ∀ x, g x = 0 → x ∈ range f) : Exact f g :=
  exact_of_comp_eq_zero_of_ker_le_range h1 h2

section Ring

variable {R M N P : Type*} [Ring R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]

lemma exact_subtype_mkQ (Q : Submodule R N) :
    Exact (Submodule.subtype Q) (Submodule.mkQ Q) := by
  rw [exact_iff, Submodule.ker_mkQ, Submodule.range_subtype Q]

lemma exact_map_mkQ_range (f : M →ₗ[R] N) :
    Exact f (Submodule.mkQ (range f)) :=
  exact_iff.mpr <| Submodule.ker_mkQ _

lemma exact_subtype_ker_map (g : N →ₗ[R] P) :
    Exact (Submodule.subtype (ker g)) g :=
  exact_iff.mpr <| (Submodule.range_subtype _).symm

@[simp]
lemma exact_zero_iff_injective {M N : Type*} (P : Type*)
    [AddCommGroup M] [AddCommGroup N] [AddCommMonoid P] [Module R N] [Module R M]
    [Module R P] (f : M →ₗ[R] N) :
    Function.Exact (0 : P →ₗ[R] M) f ↔ Function.Injective f := by
  simp [← ker_eq_bot, exact_iff]

end Ring

@[simp]
lemma exact_zero_iff_surjective {M N : Type*} (P : Type*)
    [AddCommGroup M] [AddCommGroup N] [AddCommMonoid P] [Module R N] [Module R M]
    [Module R P] (f : M →ₗ[R] N) :
    Function.Exact f (0 : N →ₗ[R] P) ↔ Function.Surjective f := by
  simp [← range_eq_top, exact_iff, eq_comm]

end LinearMap

variable (f g) in
lemma LinearEquiv.conj_exact_iff_exact (e : N ≃ₗ[R] N') :
    Function.Exact (e ∘ₗ f) (g ∘ₗ (e.symm : N' →ₗ[R] N)) ↔ Exact f g := by
  simp_rw [LinearMap.exact_iff, LinearMap.ker_comp, ← Submodule.map_equiv_eq_comap_symm,
    LinearMap.range_comp]
  exact (Submodule.map_injective_of_injective e.injective).eq_iff

namespace Function

open LinearMap

lemma Exact.linearMap_ker_eq (hfg : Exact f g) : ker g = range f :=
  SetLike.ext hfg

lemma Exact.linearMap_comp_eq_zero (h : Exact f g) : g.comp f = 0 :=
  DFunLike.coe_injective h.comp_eq_zero

lemma Surjective.comp_exact_iff_exact {p : M' →ₗ[R] M} (h : Surjective p) :
    Exact (f ∘ₗ p) g ↔ Exact f g :=
  iff_of_eq <| forall_congr fun x =>
    congrArg (g x = 0 ↔ x ∈ ·) (h.range_comp f)

lemma Injective.comp_exact_iff_exact {i : P →ₗ[R] P'} (h : Injective i) :
    Exact f (i ∘ₗ g) ↔ Exact f g :=
  forall_congr' fun _ => iff_congr (LinearMap.map_eq_zero_iff _ h) Iff.rfl

namespace Exact

variable
    {f₁₂ : M →ₗ[R] N} {f₂₃ : N →ₗ[R] P} {g₁₂ : M' →ₗ[R] N'}
    {g₂₃ : N' →ₗ[R] P'} {e₁ : M ≃ₗ[R] M'} {e₂ : N ≃ₗ[R] N'} {e₃ : P ≃ₗ[R] P'}

lemma iff_of_ladder_linearEquiv
    (h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃) :
    Exact g₁₂ g₂₃ ↔ Exact f₁₂ f₂₃ :=
  iff_of_ladder_addEquiv e₁.toAddEquiv e₂.toAddEquiv e₃.toAddEquiv
    (f₁₂ := f₁₂) (f₂₃ := f₂₃) (g₁₂ := g₁₂) (g₂₃ := g₂₃)
    (congr_arg LinearMap.toAddMonoidHom h₁₂) (congr_arg LinearMap.toAddMonoidHom h₂₃)

lemma of_ladder_linearEquiv_of_exact
    (h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃)
    (H : Exact f₁₂ f₂₃) : Exact g₁₂ g₂₃ := by
  rwa [iff_of_ladder_linearEquiv h₁₂ h₂₃]

/-- Two maps `f : M →ₗ[R] N` and `g : N →ₗ[R] P` are exact if and only if the induced maps
`LinearMap.range f → N → LinearMap.range g` are exact. -/
lemma iff_linearMap_rangeRestrict :
    Exact f g ↔ Exact (LinearMap.range f).subtype g.rangeRestrict :=
  iff_rangeFactorization (zero_mem (LinearMap.range g))

alias ⟨linearMap_rangeRestrict, _⟩ := iff_linearMap_rangeRestrict

end Exact

end Function

end LinearMap

namespace Function

section split

variable [Semiring R]
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
  | ⟨hf, l, hl⟩ => ⟨_, (h.splitSurjectiveEquiv hf ⟨l, hl⟩).2⟩
  tfae_have 2 → 3
  | ⟨hg, l, hl⟩ => ⟨_, (h.splitInjectiveEquiv hg ⟨l, hl⟩).2⟩
  tfae_have 3 → 1
  | ⟨e, e₁, e₂⟩ => by
    have : Function.Injective f := e₁ ▸ e.symm.injective.comp LinearMap.inl_injective
    exact ⟨this, ⟨_, ((h.splitSurjectiveEquiv this).symm ⟨e, e₁, e₂⟩).2⟩⟩
  tfae_have 3 → 2
  | ⟨e, e₁, e₂⟩ => by
    have : Function.Surjective g := e₂ ▸ Prod.snd_surjective.comp e.surjective
    exact ⟨this, ⟨_, ((h.splitInjectiveEquiv this).symm ⟨e, e₁, e₂⟩).2⟩⟩
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
  tfae_have 1 ↔ 3 := by
    simpa using (h.splitSurjectiveEquiv hf).nonempty_congr
  tfae_have 2 ↔ 3 := by
    simpa using (h.splitInjectiveEquiv hg).nonempty_congr
  tfae_finish

end split

section Prod

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

lemma Exact.inr_fst : Function.Exact (LinearMap.inr R M N) (LinearMap.fst R M N) := by
  rintro ⟨x, y⟩
  simp only [LinearMap.fst_apply, @eq_comm _ x, LinearMap.coe_inr, Set.mem_range, Prod.mk.injEq,
    exists_eq_right]

lemma Exact.inl_snd : Function.Exact (LinearMap.inl R M N) (LinearMap.snd R M N) := by
  rintro ⟨x, y⟩
  simp only [LinearMap.snd_apply, @eq_comm _ y, LinearMap.coe_inl, Set.mem_range, Prod.mk.injEq,
    exists_eq_left]

end Prod

end Function

section Ring

open LinearMap Submodule

variable [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}

namespace Function

/-- A necessary and sufficient condition for an exact sequence to descend to a quotient. -/
lemma Exact.exact_mapQ_iff
    (hfg : Exact f g) {p q r} (hpq : p ≤ comap f q) (hqr : q ≤ comap g r) :
    Exact (mapQ p q f hpq) (mapQ q r g hqr) ↔ range g ⊓ r ≤ map g q := by
  rw [exact_iff, ← (comap_injective_of_surjective (mkQ_surjective _)).eq_iff]
  dsimp only [mapQ]
  rw [← ker_comp, range_liftQ, liftQ_mkQ, ker_comp, range_comp, comap_map_eq,
    ker_mkQ, ker_mkQ, ← hfg.linearMap_ker_eq, sup_comm,
    ← (sup_le hqr (ker_le_comap g)).ge_iff_eq',
    ← comap_map_eq, ← map_le_iff_le_comap, map_comap_eq]

end Function

namespace LinearMap

/-- When we have a commutative diagram from a sequence of two linear maps to another,
such that the left vertical map is surjective, the middle vertical map is bijective and the right
vertical map is injective, then the upper row is exact iff the lower row is.
See `ShortComplex.exact_iff_of_epi_of_isIso_of_mono` in the file
`Mathlib/Algebra/Homology/ShortComplex/Exact.lean` for the categorical version of this result. -/
lemma exact_iff_of_surjective_of_bijective_of_injective
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    [Module R N₁] [Module R N₂] [Module R N₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (f' : N₁ →ₗ[R] N₂) (g' : N₂ →ₗ[R] N₃)
    (τ₁ : M₁ →ₗ[R] N₁) (τ₂ : M₂ →ₗ[R] N₂) (τ₃ : M₃ →ₗ[R] N₃)
    (comm₁₂ : f'.comp τ₁ = τ₂.comp f) (comm₂₃ : g'.comp τ₂ = τ₃.comp g)
    (h₁ : Function.Surjective τ₁) (h₂ : Function.Bijective τ₂) (h₃ : Function.Injective τ₃) :
    Function.Exact f g ↔ Function.Exact f' g' :=
  AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    f.toAddMonoidHom g.toAddMonoidHom f'.toAddMonoidHom g'.toAddMonoidHom
    τ₁.toAddMonoidHom τ₂.toAddMonoidHom τ₃.toAddMonoidHom
    (by ext; apply DFunLike.congr_fun comm₁₂) (by ext; apply DFunLike.congr_fun comm₂₃) h₁ h₂ h₃

lemma surjective_range_liftQ (h : range f ≤ ker g) (hg : Function.Surjective g) :
    Function.Surjective ((range f).liftQ g h) := by
  intro x₃
  obtain ⟨x₂, rfl⟩ := hg x₃
  exact ⟨Submodule.Quotient.mk x₂, rfl⟩

lemma ker_eq_bot_range_liftQ_iff (h : range f ≤ ker g) :
    ker ((range f).liftQ g h) = ⊥ ↔ ker g = range f := by
  simp only [Submodule.ext_iff, mem_ker, Submodule.mem_bot, mem_range]
  constructor
  · intro hfg x
    simpa using hfg (Submodule.Quotient.mk x)
  · intro hfg x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simpa using hfg x

lemma injective_range_liftQ_of_exact (h : Function.Exact f g) :
    Function.Injective ((range f).liftQ g (h · |>.mpr)) := by
  simpa only [← LinearMap.ker_eq_bot, ker_eq_bot_range_liftQ_iff, exact_iff] using h

end LinearMap

/-- The linear equivalence `(N ⧸ LinearMap.range f) ≃ₗ[A] P` associated to
an exact sequence `M → N → P → 0` of `R`-modules. -/
@[simps! apply]
noncomputable def Function.Exact.linearEquivOfSurjective (h : Function.Exact f g)
    (hg : Function.Surjective g) : (N ⧸ LinearMap.range f) ≃ₗ[R] P :=
  LinearEquiv.ofBijective ((LinearMap.range f).liftQ g (h · |>.mpr))
    ⟨LinearMap.injective_range_liftQ_of_exact h, LinearMap.surjective_range_liftQ _ hg⟩

end Ring
