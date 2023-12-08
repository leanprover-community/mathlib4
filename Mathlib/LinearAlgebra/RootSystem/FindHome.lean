/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Contraction

/-!
# Tidy up and relocate all lemmas here and then delete this file.
-/

open Set Function Pointwise
open Module hiding Finite
open Submodule (span)

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

@[simp] lemma LinearEquiv.coe_one : ↑(1 : M ≃ₗ[R] M) = id := rfl

@[simp] lemma LinearEquiv.coe_one' : (↑(1 : M ≃ₗ[R] M) : M →ₗ[R] M) = LinearMap.id := rfl

@[simp]
lemma LinearEquiv.coe_mul {e₁ e₂ : M ≃ₗ[R] M} :
    (↑(e₁ * e₂) : M →ₗ[R] M) = (e₁ : M →ₗ[R] M) * (e₂ : M →ₗ[R] M) := by
  rfl

@[simp]
lemma eq_zero_or_zero_of_dualTensorHom_tmul_eq_zero
    {f : Dual R M} {x : M} [NoZeroSMulDivisors R M] :
    dualTensorHom R M M (f ⊗ₜ x) = 0 ↔ f = 0 ∨ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases eq_or_ne x 0 with rfl | hx; simp
    left
    ext v
    simp only [LinearMap.zero_apply]
    replace h : f v • x = 0 :=
      by simpa only [dualTensorHom_apply, LinearMap.zero_apply] using LinearMap.congr_fun h v
    rw [smul_eq_zero] at h
    tauto
  · rcases h with rfl | rfl <;> simp

theorem Set.Finite.bijOn_of_mapsTo_of_surjOn {α : Type*} {s : Set α} {f : α → α}
    (hf : s.Finite) (hm : MapsTo f s s) (hi : SurjOn f s s) : BijOn f s s := by
  refine ⟨hm, ?_, hi⟩
  have : Finite s := by exact finite_coe_iff.mpr hf
  let f' : s → s := hm.restrict
  have hf' : Surjective f' := (MapsTo.restrict_surjective_iff hm).mpr hi
  have : Injective f' := Finite.injective_iff_surjective.mpr hf'
  exact (MapsTo.restrict_inj hm).mp this

theorem Set.MapsTo.coe_iterate_restrict {α : Type*} {s : Set α} (f : α → α) {x : α} (hx : x ∈ s)
    (hfs : MapsTo f s s) (k : ℕ) :
    (hfs.restrict^[k] ⟨x, hx⟩ : α) = f^[k] x := by
  induction' k with k ih; simp
  simp only [iterate_succ', comp_apply, val_restrict_apply, ih]

lemma _root_.Function.Injective.isOfFinOrder_iff
    {G H : Type*} [Monoid G] [Monoid H] {f : G →* H} (hf : Injective f) {x : G} :
    IsOfFinOrder (f x) ↔ IsOfFinOrder x := by
  rw [← orderOf_pos_iff, orderOf_injective f hf x, ← orderOf_pos_iff]

@[simp]
lemma span_setOf_mem_eq_top {s : Set M} :
    span R {x : span R s | (x : M) ∈ s} = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun ⟨z, hz⟩ ↦ ?_
  rw [Finsupp.mem_span_iff_total] at hz ⊢
  obtain ⟨l, rfl⟩ := hz
  let f : s ↪ {x : span R s | (x : M) ∈ s} :=
    ⟨fun x ↦ ⟨inclusion (Submodule.subset_span) x, x.property⟩, fun x y ↦ by simp⟩
  use l.embDomain f
  rw [Finsupp.total_embDomain, Subtype.ext_iff, ← Submodule.coeSubtype, Finsupp.apply_total]
  congr

lemma isOfFinOrder_of_finite_of_span_eq_top_of_image_eq
    {Φ : Set M} (hΦ₁ : Φ.Finite) (hΦ₂ : span R Φ = ⊤) {u : M →ₗ[R] M} (hu : u '' Φ = Φ) :
    IsOfFinOrder u := by
  -- TODO Should `hu` be `BijOn u Φ Φ`? Should we have a def to turn `u '' Φ = Φ` into this
  -- for finite sets? Could even use language of `IsFixedPt`.
  have hu' : BijOn u Φ Φ := hΦ₁.bijOn_of_mapsTo_of_surjOn
    ((mapsTo_image u Φ).mono_right hu.subset)
    ((surjOn_image u Φ).mono (subset_refl _) hu.symm.subset)
  let u' := hu'.equiv
  have : Finite Φ := finite_coe_iff.mpr hΦ₁
  obtain ⟨k, hk₀, hk⟩ := isOfFinOrder_of_finite u'
  refine ⟨k, hk₀, ?_⟩
  ext m
  simp only [mul_left_iterate, mul_one, LinearMap.one_apply]
  have hm : m ∈ span R Φ := hΦ₂ ▸ Submodule.mem_top
  apply Submodule.span_induction (p := fun x ↦ (u ^ k) x = x) hm
  · intro x hx
    replace hk : (u') ^ k = 1 := by simpa [IsPeriodicPt, IsFixedPt] using hk
    replace hk := Equiv.congr_fun hk ⟨x, hx⟩
    simp only [Equiv.Perm.coe_one, id_eq, Subtype.ext_iff] at hk
    change (u' ^ k) _ = x at hk
    rw [Equiv.Perm.coe_pow] at hk
    erw [hu'.1.coe_iterate_restrict] at hk
    rw [LinearMap.pow_apply]
    exact hk
  · simp
  · intro x y hx hy; simp [map_add, hx, hy]
  · intro t x hx; simp [map_smul, hx]

-- Will I need this?
@[simp]
lemma Int.zmultiples_one : AddSubgroup.zmultiples (1 : ℤ) = ⊤ := by
  ext z
  simp only [AddSubgroup.mem_top, iff_true]
  exact ⟨z, by simp⟩

-- Surprised this is missing.
lemma image_iterate {α : Type*} {f : α → α} {n : ℕ} :
    image (f^[n]) = (image f)^[n] := by
  ext1 s -- TODO Add missing `simp` lemmas so can prove this without extensionality
  induction' n with n ih; simp
  simpa only [iterate_succ', comp_apply, ← ih] using image_comp f (f^[n]) s

variable (R M) in
/-- TODO weaken typeclass etc. Can this really be missing!? -/
lemma NoZeroSMulDivisors.IntOfCharZero [CharZero R] [NoZeroSMulDivisors R M] :
    NoZeroSMulDivisors ℤ M := by
  refine ⟨fun {z x} h ↦ ?_⟩
  rw [← smul_one_smul R z x] at h
  simpa using h

-- How can this not exist?
instance [NoZeroSMulDivisors ℤ M] : NoZeroSMulDivisors ℕ M := by
  refine ⟨fun {c x} hcx ↦ ?_⟩
  rwa [nsmul_eq_smul_cast ℤ c x, smul_eq_zero, Nat.cast_eq_zero] at hcx

-- This should probably be a def somewhere
example [Nontrivial M] [NoZeroSMulDivisors ℤ M] [NoZeroSMulDivisors R M] : CharZero R := by
  refine ⟨fun {n m h} ↦ ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  replace h : (n : ℤ) • x = (m : ℤ) • x := by simp [zsmul_eq_smul_cast R, h]
  replace h := smul_left_injective ℤ hx h
  simpa using h

lemma Set.Finite.equiv_image_eq_iff_subset {α : Type*} (e : α ≃ α) (s : Set α) (hs : s.Finite) :
    e '' s = s ↔ e '' s ⊆ s := by
  refine ⟨fun h ↦ by rw [h], fun h ↦ ?_⟩
  -- There must be a better proof than the below (or else we have giant holes in our API).
  have : Fintype s := hs.fintype
  have : Fintype (e '' s) := Fintype.ofFinite (e '' s)
  apply eq_of_subset_of_card_le h
  rw [Fintype.card_congr (e.image s).symm]

lemma Set.image_mono {α β : Type*} {f : α → β} {s t : Set α} (h : s ⊆ t) :
    f '' s ⊆ f '' t := by
  rintro - ⟨a, ha, rfl⟩; exact mem_image_of_mem f (h ha)
