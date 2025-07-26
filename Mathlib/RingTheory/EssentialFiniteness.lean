/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Essentially of finite type algebras

## Main results
- `Algebra.EssFiniteType`: The class of essentially of finite type algebras. An `R`-algebra is
  essentially of finite type if it is the localization of an algebra of finite type.
- `Algebra.EssFiniteType.algHom_ext`: The algebra homomorphisms out from an algebra essentially of
  finite type is determined by its values on a finite set.

-/

open scoped TensorProduct

namespace Algebra

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/--
An `R`-algebra is essentially of finite type if
it is the localization of an algebra of finite type.
See `essFiniteType_iff_exists_subalgebra`.
-/
class EssFiniteType : Prop where
  cond : ∃ s : Finset S,
    IsLocalization ((IsUnit.submonoid S).comap (algebraMap (adjoin R (s : Set S)) S)) S

/-- Let `S` be an `R`-algebra essentially of finite type, this is a choice of a finset `s ⊆ S`
such that `S` is the localization of `R[s]`. -/
noncomputable
def EssFiniteType.finset [h : EssFiniteType R S] : Finset S := h.cond.choose

/-- A choice of a subalgebra of finite type in an essentially of finite type algebra, such that
its localization is the whole ring. -/
noncomputable
abbrev EssFiniteType.subalgebra [EssFiniteType R S] : Subalgebra R S :=
  Algebra.adjoin R (finset R S : Set S)

lemma EssFiniteType.adjoin_mem_finset [EssFiniteType R S] :
    adjoin R { x : subalgebra R S | x.1 ∈ finset R S } = ⊤ := adjoin_adjoin_coe_preimage

instance [EssFiniteType R S] : Algebra.FiniteType R (EssFiniteType.subalgebra R S) := by
  constructor
  rw [Subalgebra.fg_top, EssFiniteType.subalgebra]
  exact ⟨_, rfl⟩

/-- A submonoid of `EssFiniteType.subalgebra R S`, whose localization is the whole algebra `S`. -/
noncomputable
def EssFiniteType.submonoid [EssFiniteType R S] : Submonoid (EssFiniteType.subalgebra R S) :=
  ((IsUnit.submonoid S).comap (algebraMap (EssFiniteType.subalgebra R S) S))

instance EssFiniteType.isLocalization [h : EssFiniteType R S] :
    IsLocalization (EssFiniteType.submonoid R S) S :=
  h.cond.choose_spec

lemma essFiniteType_cond_iff (σ : Finset S) :
    IsLocalization ((IsUnit.submonoid S).comap (algebraMap (adjoin R (σ : Set S)) S)) S ↔
    (∀ s : S, ∃ t ∈ Algebra.adjoin R (σ : Set S),
      IsUnit t ∧ s * t ∈ Algebra.adjoin R (σ : Set S)) := by
  constructor <;> intro hσ
  · intro s
    obtain ⟨⟨⟨x, hx⟩, ⟨t, ht⟩, ht'⟩, h⟩ := hσ.2 s
    exact ⟨t, ht, ht', h ▸ hx⟩
  · constructor
    · exact fun y ↦ y.prop
    · intro s
      obtain ⟨t, ht, ht', h⟩ := hσ s
      exact ⟨⟨⟨_, h⟩, ⟨t, ht⟩, ht'⟩, rfl⟩
    · intros x y e
      exact ⟨1, by simpa using Subtype.ext e⟩

lemma essFiniteType_iff :
    EssFiniteType R S ↔ ∃ (σ : Finset S),
      (∀ s : S, ∃ t ∈ Algebra.adjoin R (σ : Set S),
        IsUnit t ∧ s * t ∈ Algebra.adjoin R (σ : Set S)) := by
  simp_rw [← essFiniteType_cond_iff]
  constructor <;> exact fun ⟨a, b⟩ ↦ ⟨a, b⟩

instance EssFiniteType.of_finiteType [FiniteType R S] : EssFiniteType R S := by
  obtain ⟨s, hs⟩ := ‹FiniteType R S›
  rw [essFiniteType_iff]
  exact ⟨s, fun _ ↦ by simpa only [hs, mem_top, and_true, true_and] using ⟨1, isUnit_one⟩⟩

variable {R} in
lemma EssFiniteType.of_isLocalization (M : Submonoid R) [IsLocalization M S] :
    EssFiniteType R S := by
  rw [essFiniteType_iff]
  use ∅
  simp only [Finset.coe_empty, Algebra.adjoin_empty, Algebra.mem_bot,
    Set.mem_range, exists_exists_eq_and]
  intro s
  obtain ⟨⟨x, t⟩, e⟩ := IsLocalization.surj M s
  exact ⟨_, IsLocalization.map_units S t, x, e.symm⟩

lemma EssFiniteType.of_id : EssFiniteType R R := inferInstance

section
variable [Algebra S T] [IsScalarTower R S T]

lemma EssFiniteType.aux (σ : Subalgebra R S)
    (hσ : ∀ s : S, ∃ t ∈ σ, IsUnit t ∧ s * t ∈ σ)
    (τ : Set T) (t : T) (ht : t ∈ Algebra.adjoin S τ) :
    ∃ s ∈ σ, IsUnit s ∧ s • t ∈ σ.map (IsScalarTower.toAlgHom R S T) ⊔ Algebra.adjoin R τ := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ht
  · intro t ht
    exact ⟨1, Subalgebra.one_mem _, isUnit_one,
      (one_smul S t).symm ▸ Algebra.mem_sup_right (Algebra.subset_adjoin ht)⟩
  · intro s
    obtain ⟨s', hs₁, hs₂, hs₃⟩ := hσ s
    refine ⟨_, hs₁, hs₂, Algebra.mem_sup_left ?_⟩
    rw [Algebra.smul_def, ← map_mul, mul_comm]
    exact ⟨_, hs₃, rfl⟩
  · rintro x y - - ⟨sx, hsx, hsx', hsx''⟩ ⟨sy, hsy, hsy', hsy''⟩
    refine ⟨_, σ.mul_mem hsx hsy, hsx'.mul hsy', ?_⟩
    rw [smul_add, mul_smul, mul_smul, Algebra.smul_def sx (sy • y), smul_comm,
      Algebra.smul_def sy (sx • x)]
    apply add_mem (mul_mem _ hsx'') (mul_mem _ hsy'') <;>
      exact Algebra.mem_sup_left ⟨_, ‹_›, rfl⟩
  · rintro x y - - ⟨sx, hsx, hsx', hsx''⟩ ⟨sy, hsy, hsy', hsy''⟩
    refine ⟨_, σ.mul_mem hsx hsy, hsx'.mul hsy', ?_⟩
    rw [mul_smul, ← smul_eq_mul, smul_comm sy x, ← smul_assoc, smul_eq_mul]
    exact mul_mem hsx'' hsy''

lemma EssFiniteType.comp [h₁ : EssFiniteType R S] [h₂ : EssFiniteType S T] :
    EssFiniteType R T := by
  rw [essFiniteType_iff] at h₁ h₂ ⊢
  classical
  obtain ⟨s, hs⟩ := h₁
  obtain ⟨t, ht⟩ := h₂
  use s.image (IsScalarTower.toAlgHom R S T) ∪ t
  simp only [Finset.coe_union, Finset.coe_image, Algebra.adjoin_union, Algebra.adjoin_image]
  intro x
  obtain ⟨y, hy₁, hy₂, hy₃⟩ := ht x
  obtain ⟨t₁, h₁, h₂, h₃⟩ := EssFiniteType.aux _ _ _ _ hs _ y hy₁
  obtain ⟨t₂, h₄, h₅, h₆⟩ := EssFiniteType.aux _ _ _ _ hs _ _ hy₃
  refine ⟨t₂ • t₁ • y, ?_, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact mul_mem (Algebra.mem_sup_left ⟨_, h₄, rfl⟩) h₃
  · rw [Algebra.smul_def, Algebra.smul_def]
    exact (h₅.map _).mul ((h₂.map _).mul hy₂)
  · rw [← mul_smul, mul_comm, smul_mul_assoc, mul_comm, mul_comm y, mul_smul, Algebra.smul_def]
    exact mul_mem (Algebra.mem_sup_left ⟨_, h₁, rfl⟩) h₆

open EssFiniteType in
lemma essFiniteType_iff_exists_subalgebra : EssFiniteType R S ↔
    ∃ (S₀ : Subalgebra R S) (M : Submonoid S₀), FiniteType R S₀ ∧ IsLocalization M S := by
  refine ⟨fun h ↦ ⟨subalgebra R S, submonoid R S, inferInstance, inferInstance⟩, ?_⟩
  rintro ⟨S₀, M, _, _⟩
  letI := of_isLocalization S M
  exact comp R S₀ S

instance EssFiniteType.baseChange [h : EssFiniteType R S] : EssFiniteType T (T ⊗[R] S) := by
  classical
  rw [essFiniteType_iff] at h ⊢
  obtain ⟨σ, hσ⟩ := h
  use σ.image Algebra.TensorProduct.includeRight
  intro s
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, isUnit_one, by simp⟩
  | tmul x y =>
    obtain ⟨t, h₁, h₂, h₃⟩ := hσ y
    have H (x : S) (hx : x ∈ Algebra.adjoin R (σ : Set S)) :
        1 ⊗ₜ[R] x ∈ Algebra.adjoin T
          ((σ.image Algebra.TensorProduct.includeRight : Finset (T ⊗[R] S)) : Set (T ⊗[R] S)) := by
      have : Algebra.TensorProduct.includeRight x ∈
          (Algebra.adjoin R (σ : Set S)).map (Algebra.TensorProduct.includeRight (A := T)) :=
        Subalgebra.mem_map.mpr ⟨_, hx, rfl⟩
      rw [← Algebra.adjoin_adjoin_of_tower R]
      apply Algebra.subset_adjoin
      simpa [← Algebra.adjoin_image] using this
    refine ⟨Algebra.TensorProduct.includeRight t, H _ h₁, h₂.map _, ?_⟩
    simp only [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one]
    rw [← mul_one x, ← smul_eq_mul, ← TensorProduct.smul_tmul']
    apply Subalgebra.smul_mem
    exact H _ h₃
  | add x y hx hy =>
    obtain ⟨tx, hx₁, hx₂, hx₃⟩ := hx
    obtain ⟨ty, hy₁, hy₂, hy₃⟩ := hy
    refine ⟨_, mul_mem hx₁ hy₁, hx₂.mul hy₂, ?_⟩
    rw [add_mul, ← mul_assoc, mul_comm tx ty, ← mul_assoc]
    exact add_mem (mul_mem hx₃ hy₁) (mul_mem hy₃ hx₁)

lemma EssFiniteType.of_comp [h : EssFiniteType R T] : EssFiniteType S T := by
  rw [essFiniteType_iff] at h ⊢
  classical
  obtain ⟨σ, hσ⟩ := h
  use σ
  intro x
  obtain ⟨y, hy₁, hy₂, hy₃⟩ := hσ x
  simp_rw [← Algebra.adjoin_adjoin_of_tower R (S := S) (σ : Set T)]
  exact ⟨y, Algebra.subset_adjoin hy₁, hy₂, Algebra.subset_adjoin hy₃⟩

lemma EssFiniteType.comp_iff [EssFiniteType R S] :
    EssFiniteType R T ↔ EssFiniteType S T :=
  ⟨fun _ ↦ of_comp R S T, fun _ ↦ comp R S T⟩

instance [EssFiniteType R S] (I : Ideal S) : EssFiniteType R (S ⧸ I) :=
  .comp R S _

instance [EssFiniteType R S] (M : Submonoid S) : EssFiniteType R (Localization M) :=
  have : EssFiniteType S (Localization M) := .of_isLocalization _ M
  .comp R S _

end

variable {R S} in
lemma EssFiniteType.algHom_ext [EssFiniteType R S]
    (f g : S →ₐ[R] T) (H : ∀ s ∈ finset R S, f s = g s) : f = g := by
  suffices f.toRingHom = g.toRingHom by ext; exact RingHom.congr_fun this _
  apply IsLocalization.ringHom_ext (EssFiniteType.submonoid R S)
  suffices f.comp (IsScalarTower.toAlgHom R _ S) = g.comp (IsScalarTower.toAlgHom R _ S) by
    ext; exact AlgHom.congr_fun this _
  apply AlgHom.ext_of_adjoin_eq_top (s := { x | x.1 ∈ finset R S })
  · exact adjoin_mem_finset R S
  · rintro ⟨x, hx⟩ hx'; exact H x hx'

end Algebra

namespace RingHom

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {f : R →+* S}

/-- A ring hom is essentially of finite type if it is the composition of a localization map
and a ring hom of finite type. See `Algebra.EssFiniteType`. -/
@[algebraize Algebra.EssFiniteType]
def EssFiniteType (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.EssFiniteType R S

/-- A choice of "essential generators" for a ring hom essentially of finite type.
See `Algebra.EssFiniteType.ext`. -/
noncomputable
def EssFiniteType.finset (hf : f.EssFiniteType) : Finset S :=
  letI := f.toAlgebra
  haveI : Algebra.EssFiniteType R S := hf
  Algebra.EssFiniteType.finset R S

lemma FiniteType.essFiniteType (hf : f.FiniteType) : f.EssFiniteType := by
  algebraize [f]
  change Algebra.EssFiniteType R S
  infer_instance

lemma EssFiniteType.ext (hf : f.EssFiniteType) {g₁ g₂ : S →+* T}
    (h₁ : g₁.comp f = g₂.comp f) (h₂ : ∀ x ∈ hf.finset, g₁ x = g₂ x) : g₁ = g₂ := by
  algebraize [f, g₁.comp f]
  ext x
  exact DFunLike.congr_fun (Algebra.EssFiniteType.algHom_ext T
    ⟨g₁, fun _ ↦ rfl⟩ ⟨g₂, DFunLike.congr_fun h₁.symm⟩ h₂) x

end RingHom
