/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Nakayama
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Finite modules over local rings

This file gathers various results about finite modules over a local ring `(R, 𝔪, k)`.

## Main results
- `LocalRing.subsingleton_tensorProduct`: If `M` is finitely generated, `k ⊗ M = 0 ↔ M = 0`.
- `Module.free_of_maximalIdeal_rTensor_injective`:
  If `M` is a finitely presented module such that `m ⊗ M → M` is injective
  (for example when `M` is flat), then `M` is free.
- `Module.free_of_lTensor_residueField_injective`: If `N → M → P → 0` is a presentation of `P` with
  `N` finite and `M` finite free, then injectivity of `k ⊗ N → k ⊗ M` implies that `P` is free.
- `LocalRing.split_injective_iff_lTensor_residueField_injective`:
  Given an `R`-linear map `l : M → N` with `M` finite and `N` finite free,
  `l` is a split injection if and only if `k ⊗ l` is a (split) injection.
-/

variable {R S} [CommRing R] [CommRing S] [Algebra R S]

section

variable {M N} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

open Function (Injective Surjective Exact)
open LocalRing TensorProduct

local notation "k" => ResidueField R
local notation "𝔪" => maximalIdeal R

variable {P} [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)

namespace LocalRing

variable [LocalRing R]

theorem map_mkQ_eq {N₁ N₂ : Submodule R M} (h : N₁ ≤ N₂) (h' : N₂.FG) :
    N₁.map (Submodule.mkQ (𝔪 • N₂)) = N₂.map (Submodule.mkQ (𝔪 • N₂)) ↔ N₁ = N₂ := by
  constructor
  · intro hN
    have : N₂ ≤ 𝔪 • N₂ ⊔ N₁ := by
      simpa using Submodule.comap_mono (f := Submodule.mkQ (𝔪 • N₂)) hN.ge
    rw [sup_comm] at this
    exact h.antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot h'
      (by rw [jacobson_eq_maximalIdeal]; exact bot_ne_top) this)
  · rintro rfl; simp

theorem map_mkQ_eq_top {N : Submodule R M} [Module.Finite R M] :
    N.map (Submodule.mkQ (𝔪 • ⊤)) = ⊤ ↔ N = ⊤ := by
  rw [← map_mkQ_eq (N₁ := N) le_top Module.Finite.out, Submodule.map_top, Submodule.range_mkQ]

theorem map_tensorProduct_mk_eq_top {N : Submodule R M} [Module.Finite R M] :
    N.map (TensorProduct.mk R k M 1) = ⊤ ↔ N = ⊤ := by
  constructor
  · intro hN
    letI : Module k (M ⧸ (𝔪 • ⊤ : Submodule R M)) :=
      inferInstanceAs (Module (R ⧸ 𝔪) (M ⧸ 𝔪 • (⊤ : Submodule R M)))
    letI : IsScalarTower R k (M ⧸ (𝔪 • ⊤ : Submodule R M)) :=
      inferInstanceAs (IsScalarTower R (R ⧸ 𝔪) (M ⧸ 𝔪 • (⊤ : Submodule R M)))
    let f := AlgebraTensorModule.lift (((LinearMap.ringLmapEquivSelf k k _).symm
      (Submodule.mkQ (𝔪 • ⊤ : Submodule R M))).restrictScalars R)
    have : f.comp (TensorProduct.mk R k M 1) = Submodule.mkQ (𝔪 • ⊤) := by ext; simp [f]
    have hf : Function.Surjective f := by
      intro x; obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
      rw [← this, LinearMap.comp_apply]; exact ⟨_, rfl⟩
    apply_fun Submodule.map f at hN
    rwa [← Submodule.map_comp, this, Submodule.map_top, LinearMap.range_eq_top.mpr hf,
      map_mkQ_eq_top] at hN
  · rintro rfl; rw [Submodule.map_top, LinearMap.range_eq_top]
    exact TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective

theorem subsingleton_tensorProduct [Module.Finite R M] :
    Subsingleton (k ⊗[R] M) ↔ Subsingleton M := by
  rw [← Submodule.subsingleton_iff R, ← subsingleton_iff_bot_eq_top,
    ← Submodule.subsingleton_iff R, ← subsingleton_iff_bot_eq_top,
    ← map_tensorProduct_mk_eq_top (M := M), Submodule.map_bot]

theorem span_eq_top_of_tmul_eq_basis [Module.Finite R M] {ι}
    (f : ι → M) (b : Basis ι k (k ⊗[R] M))
    (hb : ∀ i, 1 ⊗ₜ f i = b i) : Submodule.span R (Set.range f) = ⊤ := by
  rw [← map_tensorProduct_mk_eq_top, Submodule.map_span, ← Submodule.restrictScalars_span R k
    Ideal.Quotient.mk_surjective, Submodule.restrictScalars_eq_top_iff,
    ← b.span_eq, ← Set.range_comp]
  simp only [Function.comp, mk_apply, hb, Basis.span_eq]

end LocalRing

open Function in
/--
Given `M₁ → M₂ → M₃ → 0` and `N₁ → N₂ → N₃ → 0`,
if `M₁ ⊗ N₃ → M₂ ⊗ N₃` and `M₂ ⊗ N₁ → M₂ ⊗ N₂` are both injective,
then `M₃ ⊗ N₁ → M₃ ⊗ N₂` is also injective.
-/
theorem lTensor_injective_of_exact_of_exact_of_rTensor_injective
    {M₁ M₂ M₃ N₁ N₂ N₃}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃] [Module R N₃]
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃}
    (hfexact : Exact f₁ f₂) (hfsurj : Surjective f₂)
    (hgexact : Exact g₁ g₂) (hgsurj : Surjective g₂)
    (hfinj : Injective (f₁.rTensor N₃)) (hginj : Injective (g₁.lTensor M₂)) :
    Injective (g₁.lTensor M₃) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := f₂.rTensor_surjective N₁ hfsurj x
  have : f₂.rTensor N₂ (g₁.lTensor M₂ x) = 0 := by
    rw [← hx, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      LinearMap.lTensor_comp_rTensor]
  obtain ⟨y, hy⟩ := (rTensor_exact N₂ hfexact hfsurj _).mp this
  have : g₂.lTensor M₁ y = 0 := by
    apply hfinj
    trans g₂.lTensor M₂ (g₁.lTensor M₂ x)
    · rw [← hy, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        LinearMap.lTensor_comp_rTensor]
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hgexact.linearMap_comp_eq_zero]
    simp
  obtain ⟨z, rfl⟩ := (lTensor_exact _ hgexact hgsurj _).mp this
  obtain rfl : f₁.rTensor N₁ z = x := by
    apply hginj
    simp only [← hy, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hfexact.linearMap_comp_eq_zero]
  simp

namespace Module

variable [LocalRing R]

/--
If `M` is a finitely presented module over a local ring `(R, 𝔪)` such that `m ⊗ M → M` is
injective, then `M` is free.
-/
theorem free_of_maximalIdeal_rTensor_injective [Module.FinitePresentation R M]
    (H : Function.Injective ((𝔪).subtype.rTensor M)) :
    Module.Free R M := by
  let I := Module.Free.ChooseBasisIndex k (k ⊗[R] M)
  -- Let `b : I → k ⊗ M` be a `k`-basis.
  let b : Basis I k _ := Module.Free.chooseBasis k (k ⊗[R] M)
  letI : IsNoetherian k (k ⊗[R] (I →₀ R)) :=
    isNoetherian_of_isNoetherianRing_of_finite k (k ⊗[R] (I →₀ R))
  choose f hf using TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective
  -- By choosing an arbitrary lift of `b` to `I → M`, we get a surjection `i : Rᴵ → M`.
  let i := Finsupp.linearCombination R (f ∘ b)
  have hi : Surjective i := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact LocalRing.span_eq_top_of_tmul_eq_basis (R := R) (f := f ∘ b) b (fun _ ↦ hf _)
  have : Module.Finite R (LinearMap.ker i) := by
    constructor
    exact (Submodule.fg_top _).mpr (Module.FinitePresentation.fg_ker i hi)
  -- We claim that `i` is actually a bijection,
  -- hence an isomorphism exhibing `M` as the free module `Rᴵ`
  refine Module.Free.of_equiv (LinearEquiv.ofBijective i ⟨?_, hi⟩)
  -- By Nakayama's lemma, it suffices to show that `k ⊗ ker(i) = 0`.
  rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot,
    ← LocalRing.subsingleton_tensorProduct (R := R), subsingleton_iff_forall_eq 0]
  have : Function.Surjective (i.baseChange k) := i.lTensor_surjective _ hi
  -- By construction, `k ⊗ i : kᴵ → k ⊗ M` is bijective.
  have hi' : Function.Bijective (i.baseChange k) := by
    refine ⟨?_, this⟩
    rw [← LinearMap.ker_eq_bot (M := k ⊗[R] (I →₀ R)) (f := i.baseChange k),
      ← Submodule.finrank_eq_zero (R := k) (M := k ⊗[R] (I →₀ R)),
      ← Nat.add_right_inj (n := FiniteDimensional.finrank k (LinearMap.range <| i.baseChange k)),
      LinearMap.finrank_range_add_finrank_ker (V := k ⊗[R] (I →₀ R)),
      LinearMap.range_eq_top.mpr this, finrank_top]
    simp only [FiniteDimensional.finrank_tensorProduct, FiniteDimensional.finrank_self,
      FiniteDimensional.finrank_finsupp_self, one_mul, add_zero]
    rw [FiniteDimensional.finrank_eq_card_chooseBasisIndex]
  -- On the other hand, `m ⊗ M → M` injective => `Tor₁(k, M) = 0` => `k ⊗ ker(i) → kᴵ` injective.
  have := @lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (N₁ := LinearMap.ker i) (N₂ := I →₀ R) (N₃ := M)
    (f₁ := (𝔪).subtype) (f₂ := Submodule.mkQ 𝔪) inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
  intro x
  apply @this (LinearMap.ker i).subtype i (LinearMap.exact_subtype_mkQ 𝔪)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_ker_map i) hi H
    (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
  apply hi'.injective
  rw [LinearMap.baseChange_eq_ltensor]
  erw [← LinearMap.comp_apply (i.lTensor k), ← LinearMap.lTensor_comp]
  rw [(LinearMap.exact_subtype_ker_map i).linearMap_comp_eq_zero]
  simp only [LinearMap.lTensor_zero, LinearMap.zero_apply, map_zero]

-- TODO: Generalise this to finite free modules.
theorem free_of_flat_of_localRing [Module.FinitePresentation R P] [Module.Flat R P] :
    Module.Free R P :=
  free_of_maximalIdeal_rTensor_injective
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)

/--
If `M → N → P → 0` is a presentation of `P` over a local ring `(R, 𝔪, k)` with
`M` finite and `N` finite free, then injectivity of `k ⊗ M → k ⊗ N` implies that `P` is free.
-/
theorem free_of_lTensor_residueField_injective (hg : Surjective g) (h : Exact f g)
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N]
    (hf : Function.Injective (f.lTensor k)) :
    Module.Free R P := by
  have := Module.finitePresentation_of_free_of_surjective g hg
    (by rw [h.linearMap_ker_eq, LinearMap.range_eq_map]; exact (Module.Finite.out).map f)
  apply free_of_maximalIdeal_rTensor_injective
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  apply lTensor_injective_of_exact_of_exact_of_rTensor_injective
    h hg (LinearMap.exact_subtype_mkQ 𝔪) (Submodule.mkQ_surjective _)
    ((LinearMap.lTensor_inj_iff_rTensor_inj _ _).mp hf)
    (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)

end Module

/--
Given a linear map `l : M → N` over a local ring `(R, 𝔪, k)`
with `M` finite and `N` finite free,
`l` is a split injection if and only if `k ⊗ l` is a (split) injection.
-/
theorem LocalRing.split_injective_iff_lTensor_residueField_injective [LocalRing R]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N] (l : M →ₗ[R] N) :
    (∃ l', l' ∘ₗ l = LinearMap.id) ↔ Function.Injective (l.lTensor (ResidueField R)) := by
  constructor
  · intro ⟨l', hl⟩
    have : l'.lTensor (ResidueField R) ∘ₗ l.lTensor (ResidueField R) = .id := by
      rw [← LinearMap.lTensor_comp, hl, LinearMap.lTensor_id]
    exact Function.HasLeftInverse.injective ⟨_, LinearMap.congr_fun this⟩
  · intro h
    -- By `Module.free_of_lTensor_residueField_injective`, `k ⊗ l` injective => `N ⧸ l(M)` free.
    have := Module.free_of_lTensor_residueField_injective l (LinearMap.range l).mkQ
      (Submodule.mkQ_surjective _) l.exact_map_mkQ_range h
    -- Hence `l(M)` is projective because `0 → l(M) → N → N ⧸ l(M) → 0` splits.
    have : Module.Projective R (LinearMap.range l) := by
      have := (Exact.split_tfae (LinearMap.exact_subtype_mkQ (LinearMap.range l))
        Subtype.val_injective (Submodule.mkQ_surjective _)).out 0 1
      obtain ⟨l', hl'⟩ := this.mp
         (Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _))
      exact Module.Projective.of_split _ _ hl'
    -- Then `0 → ker l → M → l(M) → 0` splits.
    obtain ⟨l', hl'⟩ : ∃ l', l' ∘ₗ (LinearMap.ker l).subtype = LinearMap.id := by
      have : Function.Exact (LinearMap.ker l).subtype
          (l.codRestrict (LinearMap.range l) (LinearMap.mem_range_self l)) := by
        rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
      have := (Exact.split_tfae this
        Subtype.val_injective (fun ⟨x, y, e⟩ ↦ ⟨y, Subtype.ext e⟩)).out 0 1
      exact this.mp (Module.projective_lifting_property _ _ (fun ⟨x, y, e⟩ ↦ ⟨y, Subtype.ext e⟩))
    have : Module.Finite R (LinearMap.ker l) := by
      refine Module.Finite.of_surjective l' ?_
      exact Function.HasRightInverse.surjective ⟨_, DFunLike.congr_fun hl'⟩
    -- And tensoring with `k` preserves the injectivity of the first arrow.
    -- That is, `k ⊗ ker l → k ⊗ M` is also injective.
    have H : Function.Injective ((LinearMap.ker l).subtype.lTensor k) := by
      apply_fun (LinearMap.lTensor k) at hl'
      rw [LinearMap.lTensor_comp, LinearMap.lTensor_id] at hl'
      exact Function.HasLeftInverse.injective ⟨l'.lTensor k, DFunLike.congr_fun hl'⟩
    -- But by assumption `k ⊗ M → k ⊗ l(M)` is already injective, so `k ⊗ ker l = 0`.
    have : Subsingleton (k ⊗[R] LinearMap.ker l) := by
      refine (subsingleton_iff_forall_eq 0).mpr fun y ↦ H (h ?_)
      rw [map_zero, map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
        l.exact_subtype_ker_map.linearMap_comp_eq_zero, LinearMap.lTensor_zero,
        LinearMap.zero_apply]
    -- By Nakayama's lemma, `l` is injective.
    have : Function.Injective l := by
      rwa [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot,
        ← LocalRing.subsingleton_tensorProduct (R := R)]
    -- Whence `M ≃ l(M)` is projective and the result follows.
    have := (Exact.split_tfae l.exact_map_mkQ_range this (Submodule.mkQ_surjective _)).out 0 1
    rw [← this]
    exact Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _)

end
