/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.RingTheory.Noetherian

#align_import algebra.lie.subalgebra from "leanprover-community/mathlib"@"6d584f1709bedbed9175bd9350df46599bdd7213"

/-!
# Lie subalgebras

This file defines Lie subalgebras of a Lie algebra and provides basic related definitions and
results.

## Main definitions

  * `LieSubalgebra`
  * `LieSubalgebra.incl`
  * `LieSubalgebra.map`
  * `LieHom.range`
  * `LieEquiv.ofInjective`
  * `LieEquiv.ofEq`
  * `LieEquiv.ofSubalgebras`

## Tags

lie algebra, lie subalgebra
-/


universe u v w w₁ w₂

section LieSubalgebra

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A Lie subalgebra of a Lie algebra is submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie algebra. -/
structure LieSubalgebra extends Submodule R L where
  /-- A Lie subalgebra is closed under Lie bracket. -/
  lie_mem' : ∀ {x y}, x ∈ carrier → y ∈ carrier → ⁅x, y⁆ ∈ carrier
#align lie_subalgebra LieSubalgebra

/-- The zero algebra is a subalgebra of any Lie algebra. -/
instance : Zero (LieSubalgebra R L) :=
  ⟨⟨0, @fun x y hx _hy ↦ by
    rw [(Submodule.mem_bot R).1 hx, zero_lie]
    -- ⊢ 0 ∈ 0.carrier
    exact Submodule.zero_mem 0⟩⟩
    -- 🎉 no goals

instance : Inhabited (LieSubalgebra R L) :=
  ⟨0⟩

instance : Coe (LieSubalgebra R L) (Submodule R L) :=
  ⟨LieSubalgebra.toSubmodule⟩

namespace LieSubalgebra

instance : SetLike (LieSubalgebra R L) L
    where
  coe L' := L'.carrier
  coe_injective' L' L'' h := by
    rcases L' with ⟨⟨⟩⟩
    -- ⊢ { toSubmodule := { toAddSubmonoid := toAddSubmonoid✝, smul_mem' := smul_mem' …
    rcases L'' with ⟨⟨⟩⟩
    -- ⊢ { toSubmodule := { toAddSubmonoid := toAddSubmonoid✝¹, smul_mem' := smul_mem …
    congr
    -- ⊢ toAddSubmonoid✝¹ = toAddSubmonoid✝
    exact SetLike.coe_injective' h
    -- 🎉 no goals

instance : AddSubgroupClass (LieSubalgebra R L) L
    where
  add_mem := Submodule.add_mem _
  zero_mem L' := L'.zero_mem'
  neg_mem {L'} x hx := show -x ∈ (L' : Submodule R L) from neg_mem hx

/-- A Lie subalgebra forms a new Lie ring. -/
instance lieRing (L' : LieSubalgebra R L) : LieRing L'
    where
  bracket x y := ⟨⁅x.val, y.val⁆, L'.lie_mem' x.property y.property⟩
  lie_add := by
    intros
    -- ⊢ ⁅x✝, y✝ + z✝⁆ = ⁅x✝, y✝⁆ + ⁅x✝, z✝⁆
    apply SetCoe.ext
    -- ⊢ ↑⁅x✝, y✝ + z✝⁆ = ↑(⁅x✝, y✝⁆ + ⁅x✝, z✝⁆)
    apply lie_add
    -- ⊢ ⁅x✝ + y✝, z✝⁆ = ⁅x✝, z✝⁆ + ⁅y✝, z✝⁆
    -- 🎉 no goals
    -- ⊢ ↑⁅x✝ + y✝, z✝⁆ = ↑(⁅x✝, z✝⁆ + ⁅y✝, z✝⁆)
  add_lie := by
    -- 🎉 no goals
    intros
    apply SetCoe.ext
    apply add_lie
  lie_self := by
    intros
    -- ⊢ ⁅x✝, x✝⁆ = 0
    apply SetCoe.ext
    -- ⊢ ↑⁅x✝, x✝⁆ = ↑0
    apply lie_self
    -- 🎉 no goals
  leibniz_lie := by
    intros
    -- ⊢ ⁅x✝, ⁅y✝, z✝⁆⁆ = ⁅⁅x✝, y✝⁆, z✝⁆ + ⁅y✝, ⁅x✝, z✝⁆⁆
    apply SetCoe.ext
    -- ⊢ ↑⁅x✝, ⁅y✝, z✝⁆⁆ = ↑(⁅⁅x✝, y✝⁆, z✝⁆ + ⁅y✝, ⁅x✝, z✝⁆⁆)
    apply leibniz_lie
    -- 🎉 no goals

section

variable {R₁ : Type*} [Semiring R₁]

/-- A Lie subalgebra inherits module structures from `L`. -/
instance [SMul R₁ R] [Module R₁ L] [IsScalarTower R₁ R L] (L' : LieSubalgebra R L) : Module R₁ L' :=
  L'.toSubmodule.module'

instance [SMul R₁ R] [SMul R₁ᵐᵒᵖ R] [Module R₁ L] [Module R₁ᵐᵒᵖ L] [IsScalarTower R₁ R L]
    [IsScalarTower R₁ᵐᵒᵖ R L] [IsCentralScalar R₁ L] (L' : LieSubalgebra R L) :
    IsCentralScalar R₁ L' :=
  L'.toSubmodule.isCentralScalar

instance [SMul R₁ R] [Module R₁ L] [IsScalarTower R₁ R L] (L' : LieSubalgebra R L) :
    IsScalarTower R₁ R L' :=
  L'.toSubmodule.isScalarTower

instance (L' : LieSubalgebra R L) [IsNoetherian R L] : IsNoetherian R L' :=
  isNoetherian_submodule' _

end

/-- A Lie subalgebra forms a new Lie algebra. -/
instance lieAlgebra (L' : LieSubalgebra R L) : LieAlgebra R L'
    where lie_smul := by
    { intros
      apply SetCoe.ext
      apply lie_smul }

variable {R L}
variable (L' : LieSubalgebra R L)

@[simp]
protected theorem zero_mem : (0 : L) ∈ L' :=
  zero_mem L'
#align lie_subalgebra.zero_mem LieSubalgebra.zero_mem

protected theorem add_mem {x y : L} : x ∈ L' → y ∈ L' → (x + y : L) ∈ L' :=
  add_mem
#align lie_subalgebra.add_mem LieSubalgebra.add_mem

protected theorem sub_mem {x y : L} : x ∈ L' → y ∈ L' → (x - y : L) ∈ L' :=
  sub_mem
#align lie_subalgebra.sub_mem LieSubalgebra.sub_mem

theorem smul_mem (t : R) {x : L} (h : x ∈ L') : t • x ∈ L' :=
  (L' : Submodule R L).smul_mem t h
#align lie_subalgebra.smul_mem LieSubalgebra.smul_mem

theorem lie_mem {x y : L} (hx : x ∈ L') (hy : y ∈ L') : (⁅x, y⁆ : L) ∈ L' :=
  L'.lie_mem' hx hy
#align lie_subalgebra.lie_mem LieSubalgebra.lie_mem

theorem mem_carrier {x : L} : x ∈ L'.carrier ↔ x ∈ (L' : Set L) :=
  Iff.rfl
#align lie_subalgebra.mem_carrier LieSubalgebra.mem_carrier

@[simp]
theorem mem_mk_iff (S : Set L) (h₁ h₂ h₃ h₄) {x : L} :
    x ∈ (⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieSubalgebra R L) ↔ x ∈ S :=
  Iff.rfl
#align lie_subalgebra.mem_mk_iff LieSubalgebra.mem_mk_iff

@[simp]
theorem mem_coe_submodule {x : L} : x ∈ (L' : Submodule R L) ↔ x ∈ L' :=
  Iff.rfl
#align lie_subalgebra.mem_coe_submodule LieSubalgebra.mem_coe_submodule

theorem mem_coe {x : L} : x ∈ (L' : Set L) ↔ x ∈ L' :=
  Iff.rfl
#align lie_subalgebra.mem_coe LieSubalgebra.mem_coe

@[simp, norm_cast]
theorem coe_bracket (x y : L') : (↑⁅x, y⁆ : L) = ⁅(↑x : L), ↑y⁆ :=
  rfl
#align lie_subalgebra.coe_bracket LieSubalgebra.coe_bracket

theorem ext_iff (x y : L') : x = y ↔ (x : L) = y :=
  Subtype.ext_iff
#align lie_subalgebra.ext_iff LieSubalgebra.ext_iff

theorem coe_zero_iff_zero (x : L') : (x : L) = 0 ↔ x = 0 :=
  (ext_iff L' x 0).symm
#align lie_subalgebra.coe_zero_iff_zero LieSubalgebra.coe_zero_iff_zero

@[ext]
theorem ext (L₁' L₂' : LieSubalgebra R L) (h : ∀ x, x ∈ L₁' ↔ x ∈ L₂') : L₁' = L₂' :=
  SetLike.ext h
#align lie_subalgebra.ext LieSubalgebra.ext

theorem ext_iff' (L₁' L₂' : LieSubalgebra R L) : L₁' = L₂' ↔ ∀ x, x ∈ L₁' ↔ x ∈ L₂' :=
  SetLike.ext_iff
#align lie_subalgebra.ext_iff' LieSubalgebra.ext_iff'

@[simp]
theorem mk_coe (S : Set L) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieSubalgebra R L) : Set L) = S :=
  rfl
#align lie_subalgebra.mk_coe LieSubalgebra.mk_coe

@[simp]
theorem coe_to_submodule_mk (p : Submodule R L) (h) :
    (({ p with lie_mem' := h } : LieSubalgebra R L) : Submodule R L) = p := by
  cases p
  -- ⊢ { toSubmodule := { toAddSubmonoid := { toAddSubmonoid := toAddSubmonoid✝, sm …
  rfl
  -- 🎉 no goals
#align lie_subalgebra.coe_to_submodule_mk LieSubalgebra.coe_to_submodule_mk

theorem coe_injective : Function.Injective ((↑) : LieSubalgebra R L → Set L) :=
  SetLike.coe_injective
#align lie_subalgebra.coe_injective LieSubalgebra.coe_injective

@[norm_cast]
theorem coe_set_eq (L₁' L₂' : LieSubalgebra R L) : (L₁' : Set L) = L₂' ↔ L₁' = L₂' :=
  SetLike.coe_set_eq
#align lie_subalgebra.coe_set_eq LieSubalgebra.coe_set_eq

theorem to_submodule_injective : Function.Injective ((↑) : LieSubalgebra R L → Submodule R L) :=
  fun L₁' L₂' h ↦ by
  rw [SetLike.ext'_iff] at h
  -- ⊢ L₁' = L₂'
  rw [← coe_set_eq]
  -- ⊢ ↑L₁' = ↑L₂'
  exact h
  -- 🎉 no goals
#align lie_subalgebra.to_submodule_injective LieSubalgebra.to_submodule_injective

@[simp]
theorem coe_to_submodule_eq_iff (L₁' L₂' : LieSubalgebra R L) :
    (L₁' : Submodule R L) = (L₂' : Submodule R L) ↔ L₁' = L₂' :=
  to_submodule_injective.eq_iff
#align lie_subalgebra.coe_to_submodule_eq_iff LieSubalgebra.coe_to_submodule_eq_iff

theorem coe_to_submodule : ((L' : Submodule R L) : Set L) = L' :=
  rfl
#align lie_subalgebra.coe_to_submodule LieSubalgebra.coe_to_submodule

section LieModule

variable {M : Type w} [AddCommGroup M] [LieRingModule L M]

variable {N : Type w₁} [AddCommGroup N] [LieRingModule L N] [Module R N] [LieModule R L N]

/-- Given a Lie algebra `L` containing a Lie subalgebra `L' ⊆ L`, together with a Lie ring module
`M` of `L`, we may regard `M` as a Lie ring module of `L'` by restriction. -/
instance lieRingModule : LieRingModule L' M where
  bracket x m := ⁅(x : L), m⁆
  add_lie x y m := add_lie (x : L) y m
  lie_add x y m := lie_add (x : L) y m
  leibniz_lie x y m := leibniz_lie (x : L) y m

@[simp]
theorem coe_bracket_of_module (x : L') (m : M) : ⁅x, m⁆ = ⁅(x : L), m⁆ :=
  rfl
#align lie_subalgebra.coe_bracket_of_module LieSubalgebra.coe_bracket_of_module

variable [Module R M] [LieModule R L M]

/-- Given a Lie algebra `L` containing a Lie subalgebra `L' ⊆ L`, together with a Lie module `M` of
`L`, we may regard `M` as a Lie module of `L'` by restriction. -/
instance lieModule : LieModule R L' M
    where
  smul_lie t x m := by simp only [coe_bracket_of_module, smul_lie, Submodule.coe_smul_of_tower]
                       -- 🎉 no goals
  lie_smul t x m := by simp only [coe_bracket_of_module, lie_smul]
                       -- 🎉 no goals

/-- An `L`-equivariant map of Lie modules `M → N` is `L'`-equivariant for any Lie subalgebra
`L' ⊆ L`. -/
def _root_.LieModuleHom.restrictLie (f : M →ₗ⁅R,L⁆ N) (L' : LieSubalgebra R L) : M →ₗ⁅R,L'⁆ N :=
  { (f : M →ₗ[R] N) with map_lie' := @fun x m ↦ f.map_lie (↑x) m }
#align lie_module_hom.restrict_lie LieModuleHom.restrictLie

@[simp]
theorem _root_.LieModuleHom.coe_restrictLie (f : M →ₗ⁅R,L⁆ N) : ⇑(f.restrictLie L') = f :=
  rfl
#align lie_module_hom.coe_restrict_lie LieModuleHom.coe_restrictLie

end LieModule

/-- The embedding of a Lie subalgebra into the ambient space as a morphism of Lie algebras. -/
def incl : L' →ₗ⁅R⁆ L :=
  { (L' : Submodule R L).subtype with
    map_lie' := rfl }
#align lie_subalgebra.incl LieSubalgebra.incl

@[simp]
theorem coe_incl : ⇑L'.incl = ((↑) : L' → L) :=
  rfl
#align lie_subalgebra.coe_incl LieSubalgebra.coe_incl

/-- The embedding of a Lie subalgebra into the ambient space as a morphism of Lie modules. -/
def incl' : L' →ₗ⁅R,L'⁆ L :=
  { (L' : Submodule R L).subtype with
    map_lie' := rfl }
#align lie_subalgebra.incl' LieSubalgebra.incl'

@[simp]
theorem coe_incl' : ⇑L'.incl' = ((↑) : L' → L) :=
  rfl
#align lie_subalgebra.coe_incl' LieSubalgebra.coe_incl'

end LieSubalgebra

variable {R L}
variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]
variable (f : L →ₗ⁅R⁆ L₂)

namespace LieHom

/-- The range of a morphism of Lie algebras is a Lie subalgebra. -/
def range : LieSubalgebra R L₂ :=
  { LinearMap.range (f : L →ₗ[R] L₂) with
      lie_mem' := by
        rintro - - ⟨x, rfl⟩ ⟨y, rfl⟩
        -- ⊢ ⁅↑↑f x, ↑↑f y⁆ ∈ { toAddSubmonoid := src✝.toAddSubmonoid, smul_mem' := (_ :  …
        exact ⟨⁅x, y⁆, f.map_lie x y⟩ }
        -- 🎉 no goals
#align lie_hom.range LieHom.range

@[simp]
theorem range_coe : (f.range : Set L₂) = Set.range f :=
  LinearMap.range_coe (f : L →ₗ[R] L₂)
#align lie_hom.range_coe LieHom.range_coe

@[simp]
theorem mem_range (x : L₂) : x ∈ f.range ↔ ∃ y : L, f y = x :=
  LinearMap.mem_range
#align lie_hom.mem_range LieHom.mem_range

theorem mem_range_self (x : L) : f x ∈ f.range :=
  LinearMap.mem_range_self (f : L →ₗ[R] L₂) x
#align lie_hom.mem_range_self LieHom.mem_range_self

/-- We can restrict a morphism to a (surjective) map to its range. -/
def rangeRestrict : L →ₗ⁅R⁆ f.range :=
  { (f : L →ₗ[R] L₂).rangeRestrict with
    map_lie' := @fun x y ↦ by
      apply Subtype.ext
      -- ⊢ ↑(AddHom.toFun { toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R) (x : …
      exact f.map_lie x y }
      -- 🎉 no goals
#align lie_hom.range_restrict LieHom.rangeRestrict

@[simp]
theorem rangeRestrict_apply (x : L) : f.rangeRestrict x = ⟨f x, f.mem_range_self x⟩ :=
  rfl
#align lie_hom.range_restrict_apply LieHom.rangeRestrict_apply

theorem surjective_rangeRestrict : Function.Surjective f.rangeRestrict := by
  rintro ⟨y, hy⟩
  -- ⊢ ∃ a, ↑(rangeRestrict f) a = { val := y, property := hy }
  erw [mem_range] at hy; obtain ⟨x, rfl⟩ := hy
  -- ⊢ ∃ a, ↑(rangeRestrict f) a = { val := y, property := hy✝ }
                         -- ⊢ ∃ a, ↑(rangeRestrict f) a = { val := ↑f x, property := hy }
  use x
  -- ⊢ ↑(rangeRestrict f) x = { val := ↑f x, property := hy }
  simp only [Subtype.mk_eq_mk, rangeRestrict_apply]
  -- 🎉 no goals
#align lie_hom.surjective_range_restrict LieHom.surjective_rangeRestrict

/-- A Lie algebra is equivalent to its range under an injective Lie algebra morphism. -/
noncomputable def equivRangeOfInjective (h : Function.Injective f) : L ≃ₗ⁅R⁆ f.range :=
  LieEquiv.ofBijective f.rangeRestrict
    ⟨fun x y hxy ↦ by
      simp only [Subtype.mk_eq_mk, rangeRestrict_apply] at hxy
      -- ⊢ x = y
      exact h hxy, f.surjective_rangeRestrict⟩
      -- 🎉 no goals
#align lie_hom.equiv_range_of_injective LieHom.equivRangeOfInjective

@[simp]
theorem equivRangeOfInjective_apply (h : Function.Injective f) (x : L) :
    f.equivRangeOfInjective h x = ⟨f x, mem_range_self f x⟩ :=
  rfl
#align lie_hom.equiv_range_of_injective_apply LieHom.equivRangeOfInjective_apply

end LieHom

theorem Submodule.exists_lieSubalgebra_coe_eq_iff (p : Submodule R L) :
    (∃ K : LieSubalgebra R L, ↑K = p) ↔ ∀ x y : L, x ∈ p → y ∈ p → ⁅x, y⁆ ∈ p := by
  constructor
  -- ⊢ (∃ K, K.toSubmodule = p) → ∀ (x y : L), x ∈ p → y ∈ p → ⁅x, y⁆ ∈ p
  · rintro ⟨K, rfl⟩ _ _
    -- ⊢ x✝ ∈ K.toSubmodule → y✝ ∈ K.toSubmodule → ⁅x✝, y✝⁆ ∈ K.toSubmodule
    exact K.lie_mem'
    -- 🎉 no goals
  · intro h
    -- ⊢ ∃ K, K.toSubmodule = p
    use { p with lie_mem' := h _ _ }
    -- 🎉 no goals
#align submodule.exists_lie_subalgebra_coe_eq_iff Submodule.exists_lieSubalgebra_coe_eq_iff

namespace LieSubalgebra

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

@[simp]
theorem incl_range : K.incl.range = K := by
  rw [← coe_to_submodule_eq_iff]
  -- ⊢ (LieHom.range (incl K)).toSubmodule = K.toSubmodule
  exact (K : Submodule R L).range_subtype
  -- 🎉 no goals
#align lie_subalgebra.incl_range LieSubalgebra.incl_range

/-- The image of a Lie subalgebra under a Lie algebra morphism is a Lie subalgebra of the
codomain. -/
def map : LieSubalgebra R L₂ :=
  { (K : Submodule R L).map (f : L →ₗ[R] L₂) with
    lie_mem' := @fun x y hx hy ↦ by
      erw [Submodule.mem_map] at hx
      -- ⊢ ⁅x, y⁆ ∈ { toAddSubmonoid := src✝.toAddSubmonoid, smul_mem' := (_ : ∀ (c : R …
      rcases hx with ⟨x', hx', hx⟩
      -- ⊢ ⁅x, y⁆ ∈ { toAddSubmonoid := src✝.toAddSubmonoid, smul_mem' := (_ : ∀ (c : R …
      rw [← hx]
      -- ⊢ ⁅↑↑f x', y⁆ ∈ { toAddSubmonoid := src✝.toAddSubmonoid, smul_mem' := (_ : ∀ ( …
      erw [Submodule.mem_map] at hy
      -- ⊢ ⁅↑↑f x', y⁆ ∈ { toAddSubmonoid := src✝.toAddSubmonoid, smul_mem' := (_ : ∀ ( …
      rcases hy with ⟨y', hy', hy⟩
      -- ⊢ ⁅↑↑f x', y⁆ ∈ { toAddSubmonoid := src✝.toAddSubmonoid, smul_mem' := (_ : ∀ ( …
      rw [← hy]
      -- ⊢ ⁅↑↑f x', ↑↑f y'⁆ ∈ { toAddSubmonoid := src✝.toAddSubmonoid, smul_mem' := (_  …
      erw [Submodule.mem_map]
      -- ⊢ ∃ y, y ∈ K.toSubmodule ∧ ↑↑f y = ⁅↑↑f x', ↑↑f y'⁆
      exact ⟨⁅x', y'⁆, K.lie_mem hx' hy', f.map_lie x' y'⟩ }
      -- 🎉 no goals
#align lie_subalgebra.map LieSubalgebra.map

@[simp]
theorem mem_map (x : L₂) : x ∈ K.map f ↔ ∃ y : L, y ∈ K ∧ f y = x :=
  Submodule.mem_map
#align lie_subalgebra.mem_map LieSubalgebra.mem_map

-- TODO Rename and state for homs instead of equivs.
theorem mem_map_submodule (e : L ≃ₗ⁅R⁆ L₂) (x : L₂) :
    x ∈ K.map (e : L →ₗ⁅R⁆ L₂) ↔ x ∈ (K : Submodule R L).map (e : L →ₗ[R] L₂) :=
  Iff.rfl
#align lie_subalgebra.mem_map_submodule LieSubalgebra.mem_map_submodule

/-- The preimage of a Lie subalgebra under a Lie algebra morphism is a Lie subalgebra of the
domain. -/
def comap : LieSubalgebra R L :=
  { (K₂ : Submodule R L₂).comap (f : L →ₗ[R] L₂) with
    lie_mem' := @fun x y hx hy ↦ by
      suffices ⁅f x, f y⁆ ∈ K₂ by simp [this]
      -- ⊢ ⁅↑f x, ↑f y⁆ ∈ K₂
      exact K₂.lie_mem hx hy }
      -- 🎉 no goals
#align lie_subalgebra.comap LieSubalgebra.comap

section LatticeStructure

open Set

instance : PartialOrder (LieSubalgebra R L) :=
  { PartialOrder.lift ((↑) : LieSubalgebra R L → Set L) coe_injective with
    le := fun N N' ↦ ∀ ⦃x⦄, x ∈ N → x ∈ N' }

theorem le_def : K ≤ K' ↔ (K : Set L) ⊆ K' :=
  Iff.rfl
#align lie_subalgebra.le_def LieSubalgebra.le_def

@[simp]
theorem coe_submodule_le_coe_submodule : (K : Submodule R L) ≤ K' ↔ K ≤ K' :=
  Iff.rfl
#align lie_subalgebra.coe_submodule_le_coe_submodule LieSubalgebra.coe_submodule_le_coe_submodule

instance : Bot (LieSubalgebra R L) :=
  ⟨0⟩

@[simp]
theorem bot_coe : ((⊥ : LieSubalgebra R L) : Set L) = {0} :=
  rfl
#align lie_subalgebra.bot_coe LieSubalgebra.bot_coe

@[simp]
theorem bot_coe_submodule : ((⊥ : LieSubalgebra R L) : Submodule R L) = ⊥ :=
  rfl
#align lie_subalgebra.bot_coe_submodule LieSubalgebra.bot_coe_submodule

@[simp]
theorem mem_bot (x : L) : x ∈ (⊥ : LieSubalgebra R L) ↔ x = 0 :=
  mem_singleton_iff
#align lie_subalgebra.mem_bot LieSubalgebra.mem_bot

instance : Top (LieSubalgebra R L) :=
  ⟨{ (⊤ : Submodule R L) with lie_mem' := @fun x y _ _ ↦ mem_univ ⁅x, y⁆ }⟩

@[simp]
theorem top_coe : ((⊤ : LieSubalgebra R L) : Set L) = univ :=
  rfl
#align lie_subalgebra.top_coe LieSubalgebra.top_coe

@[simp]
theorem top_coe_submodule : ((⊤ : LieSubalgebra R L) : Submodule R L) = ⊤ :=
  rfl
#align lie_subalgebra.top_coe_submodule LieSubalgebra.top_coe_submodule

@[simp]
theorem mem_top (x : L) : x ∈ (⊤ : LieSubalgebra R L) :=
  mem_univ x
#align lie_subalgebra.mem_top LieSubalgebra.mem_top

theorem _root_.LieHom.range_eq_map : f.range = map f ⊤ := by
  ext
  -- ⊢ x✝ ∈ LieHom.range f ↔ x✝ ∈ map f ⊤
  simp
  -- 🎉 no goals
#align lie_hom.range_eq_map LieHom.range_eq_map

instance : Inf (LieSubalgebra R L) :=
  ⟨fun K K' ↦
    { (K ⊓ K' : Submodule R L) with
      lie_mem' := fun hx hy ↦ mem_inter (K.lie_mem hx.1 hy.1) (K'.lie_mem hx.2 hy.2) }⟩

instance : InfSet (LieSubalgebra R L) :=
  ⟨fun S ↦
    { sInf {(s : Submodule R L) | s ∈ S} with
      lie_mem' := @fun x y hx hy ↦ by
        simp only [Submodule.mem_carrier, mem_iInter, Submodule.sInf_coe, mem_setOf_eq,
          forall_apply_eq_imp_iff₂, exists_imp, and_imp] at hx hy ⊢
        intro K hK
        -- ⊢ ⁅x, y⁆ ∈ ↑K.toSubmodule
        exact K.lie_mem (hx K hK) (hy K hK) }⟩
        -- 🎉 no goals

@[simp]
theorem inf_coe : (↑(K ⊓ K') : Set L) = (K : Set L) ∩ (K' : Set L) :=
  rfl
#align lie_subalgebra.inf_coe LieSubalgebra.inf_coe

@[simp]
theorem sInf_coe_to_submodule (S : Set (LieSubalgebra R L)) :
    (↑(sInf S) : Submodule R L) = sInf {(s : Submodule R L) | s ∈ S} :=
  rfl
#align lie_subalgebra.Inf_coe_to_submodule LieSubalgebra.sInf_coe_to_submodule

@[simp]
theorem sInf_coe (S : Set (LieSubalgebra R L)) : (↑(sInf S) : Set L) = ⋂ s ∈ S, (s : Set L) := by
  rw [← coe_to_submodule, sInf_coe_to_submodule, Submodule.sInf_coe]
  -- ⊢ ⋂ (p : Submodule R L) (_ : p ∈ {x | ∃ s, s ∈ S ∧ s.toSubmodule = x}), ↑p = ⋂ …
  ext x
  -- ⊢ x ∈ ⋂ (p : Submodule R L) (_ : p ∈ {x | ∃ s, s ∈ S ∧ s.toSubmodule = x}), ↑p …
  simp
  -- 🎉 no goals
#align lie_subalgebra.Inf_coe LieSubalgebra.sInf_coe

theorem sInf_glb (S : Set (LieSubalgebra R L)) : IsGLB S (sInf S) := by
  have h : ∀ K K' : LieSubalgebra R L, (K : Set L) ≤ K' ↔ K ≤ K' := by
    intros
    exact Iff.rfl
  apply IsGLB.of_image @h
  -- ⊢ IsGLB ((fun x => ↑x) '' S) ↑(sInf S)
  simp only [sInf_coe]
  -- ⊢ IsGLB ((fun x => ↑x) '' S) (⋂ (s : LieSubalgebra R L) (_ : s ∈ S), ↑s)
  exact isGLB_biInf
  -- 🎉 no goals
#align lie_subalgebra.Inf_glb LieSubalgebra.sInf_glb

/-- The set of Lie subalgebras of a Lie algebra form a complete lattice.

We provide explicit values for the fields `bot`, `top`, `inf` to get more convenient definitions
than we would otherwise obtain from `completeLatticeOfInf`. -/
instance completeLattice : CompleteLattice (LieSubalgebra R L) :=
  { completeLatticeOfInf _ sInf_glb with
    bot := ⊥
    bot_le := fun N _ h ↦ by
      rw [mem_bot] at h
      -- ⊢ x✝ ∈ N
      rw [h]
      -- ⊢ 0 ∈ N
      exact N.zero_mem'
      -- 🎉 no goals
    top := ⊤
    le_top := fun _ _ _ ↦ trivial
    inf := (· ⊓ ·)
    le_inf := fun N₁ N₂ N₃ h₁₂ h₁₃ m hm ↦ ⟨h₁₂ hm, h₁₃ hm⟩
    inf_le_left := fun _ _ _ ↦ And.left
    inf_le_right := fun _ _ _ ↦ And.right }

instance addCommMonoid : AddCommMonoid (LieSubalgebra R L)
    where
  add := (· ⊔ ·)
  add_assoc _ _ _ := sup_assoc
  zero := ⊥
  zero_add _ := bot_sup_eq
  add_zero _ := sup_bot_eq
  add_comm _ _ := sup_comm

instance : CanonicallyOrderedAddMonoid (LieSubalgebra R L) :=
  { LieSubalgebra.addCommMonoid,
    LieSubalgebra.completeLattice with
    add_le_add_left := fun _a _b ↦ sup_le_sup_left
    exists_add_of_le := @fun _a b h ↦ ⟨b, (sup_eq_right.2 h).symm⟩
    le_self_add := fun _a _b ↦ le_sup_left }

@[simp]
theorem add_eq_sup : K + K' = K ⊔ K' :=
  rfl
#align lie_subalgebra.add_eq_sup LieSubalgebra.add_eq_sup

@[simp]
theorem inf_coe_to_submodule :
    (↑(K ⊓ K') : Submodule R L) = (K : Submodule R L) ⊓ (K' : Submodule R L) :=
  rfl
#align lie_subalgebra.inf_coe_to_submodule LieSubalgebra.inf_coe_to_submodule

@[simp]
theorem mem_inf (x : L) : x ∈ K ⊓ K' ↔ x ∈ K ∧ x ∈ K' := by
  rw [← mem_coe_submodule, ← mem_coe_submodule, ← mem_coe_submodule, inf_coe_to_submodule,
    Submodule.mem_inf]
#align lie_subalgebra.mem_inf LieSubalgebra.mem_inf

theorem eq_bot_iff : K = ⊥ ↔ ∀ x : L, x ∈ K → x = 0 := by
  rw [_root_.eq_bot_iff]
  -- ⊢ K ≤ ⊥ ↔ ∀ (x : L), x ∈ K → x = 0
  exact Iff.rfl
  -- 🎉 no goals
#align lie_subalgebra.eq_bot_iff LieSubalgebra.eq_bot_iff

instance subsingleton_of_bot : Subsingleton (LieSubalgebra R (⊥ : LieSubalgebra R L)) := by
  apply subsingleton_of_bot_eq_top
  -- ⊢ ⊥ = ⊤
  ext ⟨x, hx⟩; change x ∈ ⊥ at hx; rw [LieSubalgebra.mem_bot] at hx; subst hx
  -- ⊢ { val := x, property := hx } ∈ ⊥ ↔ { val := x, property := hx } ∈ ⊤
               -- ⊢ { val := x, property := hx } ∈ ⊥ ↔ { val := x, property := hx } ∈ ⊤
                                   -- ⊢ { val := x, property := hx✝ } ∈ ⊥ ↔ { val := x, property := hx✝ } ∈ ⊤
                                                                     -- ⊢ { val := 0, property := hx } ∈ ⊥ ↔ { val := 0, property := hx } ∈ ⊤
  simp only [true_iff_iff, eq_self_iff_true, Submodule.mk_eq_zero, mem_bot, mem_top]
  -- 🎉 no goals
#align lie_subalgebra.subsingleton_of_bot LieSubalgebra.subsingleton_of_bot

theorem subsingleton_bot : Subsingleton (⊥ : LieSubalgebra R L) :=
  show Subsingleton ((⊥ : LieSubalgebra R L) : Set L) by simp
                                                         -- 🎉 no goals
#align lie_subalgebra.subsingleton_bot LieSubalgebra.subsingleton_bot

variable (R L)

theorem wellFounded_of_noetherian [IsNoetherian R L] :
    WellFounded ((· > ·) : LieSubalgebra R L → LieSubalgebra R L → Prop) :=
  let f :
    ((· > ·) : LieSubalgebra R L → LieSubalgebra R L → Prop) →r
      ((· > ·) : Submodule R L → Submodule R L → Prop) :=
    { toFun := (↑)
      map_rel' := @fun _ _ h ↦ h }
  RelHomClass.wellFounded f (isNoetherian_iff_wellFounded.mp inferInstance)
#align lie_subalgebra.well_founded_of_noetherian LieSubalgebra.wellFounded_of_noetherian

variable {R L K K' f}

section NestedSubalgebras

variable (h : K ≤ K')

/-- Given two nested Lie subalgebras `K ⊆ K'`, the inclusion `K ↪ K'` is a morphism of Lie
algebras. -/
def homOfLe : K →ₗ⁅R⁆ K' :=
  { Submodule.ofLe h with map_lie' := @fun _ _ ↦ rfl }
#align lie_subalgebra.hom_of_le LieSubalgebra.homOfLe

@[simp]
theorem coe_homOfLe (x : K) : (homOfLe h x : L) = x :=
  rfl
#align lie_subalgebra.coe_hom_of_le LieSubalgebra.coe_homOfLe

theorem homOfLe_apply (x : K) : homOfLe h x = ⟨x.1, h x.2⟩ :=
  rfl
#align lie_subalgebra.hom_of_le_apply LieSubalgebra.homOfLe_apply

theorem homOfLe_injective : Function.Injective (homOfLe h) := fun x y ↦ by
  simp only [homOfLe_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]
  -- 🎉 no goals
#align lie_subalgebra.hom_of_le_injective LieSubalgebra.homOfLe_injective

/-- Given two nested Lie subalgebras `K ⊆ K'`, we can view `K` as a Lie subalgebra of `K'`,
regarded as Lie algebra in its own right. -/
def ofLe : LieSubalgebra R K' :=
  (homOfLe h).range
#align lie_subalgebra.of_le LieSubalgebra.ofLe

@[simp]
theorem mem_ofLe (x : K') : x ∈ ofLe h ↔ (x : L) ∈ K := by
  simp only [ofLe, homOfLe_apply, LieHom.mem_range]
  -- ⊢ (∃ y, { val := ↑y, property := (_ : ↑y ∈ K') } = x) ↔ ↑x ∈ K
  constructor
  -- ⊢ (∃ y, { val := ↑y, property := (_ : ↑y ∈ K') } = x) → ↑x ∈ K
  · rintro ⟨y, rfl⟩
    -- ⊢ ↑{ val := ↑y, property := (_ : ↑y ∈ K') } ∈ K
    exact y.property
    -- 🎉 no goals
  · intro h
    -- ⊢ ∃ y, { val := ↑y, property := (_ : ↑y ∈ K') } = x
    use ⟨(x : L), h⟩
    -- 🎉 no goals
#align lie_subalgebra.mem_of_le LieSubalgebra.mem_ofLe

theorem ofLe_eq_comap_incl : ofLe h = K.comap K'.incl := by
  ext
  -- ⊢ x✝ ∈ ofLe h ↔ x✝ ∈ comap (incl K') K
  rw [mem_ofLe]
  -- ⊢ ↑x✝ ∈ K ↔ x✝ ∈ comap (incl K') K
  rfl
  -- 🎉 no goals
#align lie_subalgebra.of_le_eq_comap_incl LieSubalgebra.ofLe_eq_comap_incl

@[simp]
theorem coe_ofLe : (ofLe h : Submodule R K') = LinearMap.range (Submodule.ofLe h) :=
  rfl
#align lie_subalgebra.coe_of_le LieSubalgebra.coe_ofLe

/-- Given nested Lie subalgebras `K ⊆ K'`, there is a natural equivalence from `K` to its image in
`K'`.  -/
noncomputable def equivOfLe : K ≃ₗ⁅R⁆ ofLe h :=
  (homOfLe h).equivRangeOfInjective (homOfLe_injective h)
#align lie_subalgebra.equiv_of_le LieSubalgebra.equivOfLe

@[simp]
theorem equivOfLe_apply (x : K) : equivOfLe h x = ⟨homOfLe h x, (homOfLe h).mem_range_self x⟩ :=
  rfl
#align lie_subalgebra.equiv_of_le_apply LieSubalgebra.equivOfLe_apply

end NestedSubalgebras

theorem map_le_iff_le_comap {K : LieSubalgebra R L} {K' : LieSubalgebra R L₂} :
    map f K ≤ K' ↔ K ≤ comap f K' :=
  Set.image_subset_iff
#align lie_subalgebra.map_le_iff_le_comap LieSubalgebra.map_le_iff_le_comap

theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ ↦ map_le_iff_le_comap
#align lie_subalgebra.gc_map_comap LieSubalgebra.gc_map_comap

end LatticeStructure

section LieSpan

variable (R L) (s : Set L)

/-- The Lie subalgebra of a Lie algebra `L` generated by a subset `s ⊆ L`. -/
def lieSpan : LieSubalgebra R L :=
  sInf { N | s ⊆ N }
#align lie_subalgebra.lie_span LieSubalgebra.lieSpan

variable {R L s}

theorem mem_lieSpan {x : L} : x ∈ lieSpan R L s ↔ ∀ K : LieSubalgebra R L, s ⊆ K → x ∈ K := by
  change x ∈ (lieSpan R L s : Set L) ↔ _
  -- ⊢ x ∈ ↑(lieSpan R L s) ↔ ∀ (K : LieSubalgebra R L), s ⊆ ↑K → x ∈ K
  erw [sInf_coe]
  -- ⊢ x ∈ ⋂ (s_1 : LieSubalgebra R L) (_ : s_1 ∈ {N | s ⊆ ↑N}), ↑s_1 ↔ ∀ (K : LieS …
  exact Set.mem_iInter₂
  -- 🎉 no goals
#align lie_subalgebra.mem_lie_span LieSubalgebra.mem_lieSpan

theorem subset_lieSpan : s ⊆ lieSpan R L s := by
  intro m hm
  -- ⊢ m ∈ ↑(lieSpan R L s)
  erw [mem_lieSpan]
  -- ⊢ ∀ (K : LieSubalgebra R L), s ⊆ ↑K → m ∈ K
  intro K hK
  -- ⊢ m ∈ K
  exact hK hm
  -- 🎉 no goals
#align lie_subalgebra.subset_lie_span LieSubalgebra.subset_lieSpan

theorem submodule_span_le_lieSpan : Submodule.span R s ≤ lieSpan R L s := by
  rw [Submodule.span_le]
  -- ⊢ s ⊆ ↑(lieSpan R L s).toSubmodule
  apply subset_lieSpan
  -- 🎉 no goals
#align lie_subalgebra.submodule_span_le_lie_span LieSubalgebra.submodule_span_le_lieSpan

theorem lieSpan_le {K} : lieSpan R L s ≤ K ↔ s ⊆ K := by
  constructor
  -- ⊢ lieSpan R L s ≤ K → s ⊆ ↑K
  · exact Set.Subset.trans subset_lieSpan
    -- 🎉 no goals
  · intro hs m hm
    -- ⊢ m ∈ K
    rw [mem_lieSpan] at hm
    -- ⊢ m ∈ K
    exact hm _ hs
    -- 🎉 no goals
#align lie_subalgebra.lie_span_le LieSubalgebra.lieSpan_le

theorem lieSpan_mono {t : Set L} (h : s ⊆ t) : lieSpan R L s ≤ lieSpan R L t := by
  rw [lieSpan_le]
  -- ⊢ s ⊆ ↑(lieSpan R L t)
  exact Set.Subset.trans h subset_lieSpan
  -- 🎉 no goals
#align lie_subalgebra.lie_span_mono LieSubalgebra.lieSpan_mono

theorem lieSpan_eq : lieSpan R L (K : Set L) = K :=
  le_antisymm (lieSpan_le.mpr rfl.subset) subset_lieSpan
#align lie_subalgebra.lie_span_eq LieSubalgebra.lieSpan_eq

theorem coe_lieSpan_submodule_eq_iff {p : Submodule R L} :
    (lieSpan R L (p : Set L) : Submodule R L) = p ↔ ∃ K : LieSubalgebra R L, ↑K = p := by
  rw [p.exists_lieSubalgebra_coe_eq_iff]; constructor <;> intro h
  -- ⊢ (lieSpan R L ↑p).toSubmodule = p ↔ ∀ (x y : L), x ∈ p → y ∈ p → ⁅x, y⁆ ∈ p
                                          -- ⊢ (lieSpan R L ↑p).toSubmodule = p → ∀ (x y : L), x ∈ p → y ∈ p → ⁅x, y⁆ ∈ p
                                                          -- ⊢ ∀ (x y : L), x ∈ p → y ∈ p → ⁅x, y⁆ ∈ p
                                                          -- ⊢ (lieSpan R L ↑p).toSubmodule = p
  · intro x m hm
    -- ⊢ m ∈ p → ⁅x, m⁆ ∈ p
    rw [← h, mem_coe_submodule]
    -- ⊢ m ∈ lieSpan R L ↑p → ⁅x, m⁆ ∈ (lieSpan R L ↑p).toSubmodule
    exact lie_mem _ (subset_lieSpan hm)
    -- 🎉 no goals
  · rw [← coe_to_submodule_mk p @h, coe_to_submodule, coe_to_submodule_eq_iff, lieSpan_eq]
    -- 🎉 no goals
#align lie_subalgebra.coe_lie_span_submodule_eq_iff LieSubalgebra.coe_lieSpan_submodule_eq_iff

variable (R L)

/-- `lieSpan` forms a Galois insertion with the coercion from `LieSubalgebra` to `Set`. -/
protected def gi : GaloisInsertion (lieSpan R L : Set L → LieSubalgebra R L) (↑)
    where
  choice s _ := lieSpan R L s
  gc _ _ := lieSpan_le
  le_l_u _ := subset_lieSpan
  choice_eq _ _ := rfl
#align lie_subalgebra.gi LieSubalgebra.gi

@[simp]
theorem span_empty : lieSpan R L (∅ : Set L) = ⊥ :=
  (LieSubalgebra.gi R L).gc.l_bot
#align lie_subalgebra.span_empty LieSubalgebra.span_empty

@[simp]
theorem span_univ : lieSpan R L (Set.univ : Set L) = ⊤ :=
  eq_top_iff.2 <| SetLike.le_def.2 <| subset_lieSpan
#align lie_subalgebra.span_univ LieSubalgebra.span_univ

variable {L}

theorem span_union (s t : Set L) : lieSpan R L (s ∪ t) = lieSpan R L s ⊔ lieSpan R L t :=
  (LieSubalgebra.gi R L).gc.l_sup
#align lie_subalgebra.span_union LieSubalgebra.span_union

theorem span_iUnion {ι} (s : ι → Set L) : lieSpan R L (⋃ i, s i) = ⨆ i, lieSpan R L (s i) :=
  (LieSubalgebra.gi R L).gc.l_iSup
#align lie_subalgebra.span_Union LieSubalgebra.span_iUnion

end LieSpan

end LieSubalgebra

end LieSubalgebra

namespace LieEquiv

variable {R : Type u} {L₁ : Type v} {L₂ : Type w}

variable [CommRing R] [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂]

/-- An injective Lie algebra morphism is an equivalence onto its range. -/
noncomputable def ofInjective (f : L₁ →ₗ⁅R⁆ L₂) (h : Function.Injective f) : L₁ ≃ₗ⁅R⁆ f.range :=
  { LinearEquiv.ofInjective (f : L₁ →ₗ[R] L₂) <| by rwa [LieHom.coe_toLinearMap] with
                                                    -- 🎉 no goals
    map_lie' := @fun x y ↦ SetCoe.ext $ f.map_lie x y }
#align lie_equiv.of_injective LieEquiv.ofInjective

@[simp]
theorem ofInjective_apply (f : L₁ →ₗ⁅R⁆ L₂) (h : Function.Injective f) (x : L₁) :
    ↑(ofInjective f h x) = f x :=
  rfl
#align lie_equiv.of_injective_apply LieEquiv.ofInjective_apply

variable (L₁' L₁'' : LieSubalgebra R L₁) (L₂' : LieSubalgebra R L₂)

/-- Lie subalgebras that are equal as sets are equivalent as Lie algebras. -/
def ofEq (h : (L₁' : Set L₁) = L₁'') : L₁' ≃ₗ⁅R⁆ L₁'' :=
  { LinearEquiv.ofEq (L₁' : Submodule R L₁) (L₁'' : Submodule R L₁) (by
      ext x
      -- ⊢ x ∈ L₁'.toSubmodule ↔ x ∈ L₁''.toSubmodule
      change x ∈ (L₁' : Set L₁) ↔ x ∈ (L₁'' : Set L₁)
      -- ⊢ x ∈ ↑L₁' ↔ x ∈ ↑L₁''
      rw [h]) with
      -- 🎉 no goals
    map_lie' := @fun x y ↦ rfl }
#align lie_equiv.of_eq LieEquiv.ofEq

@[simp]
theorem ofEq_apply (L L' : LieSubalgebra R L₁) (h : (L : Set L₁) = L') (x : L) :
    (↑(ofEq L L' h x) : L₁) = x :=
  rfl
#align lie_equiv.of_eq_apply LieEquiv.ofEq_apply

variable (e : L₁ ≃ₗ⁅R⁆ L₂)

/-- An equivalence of Lie algebras restricts to an equivalence from any Lie subalgebra onto its
image. -/
def lieSubalgebraMap : L₁'' ≃ₗ⁅R⁆ (L₁''.map e : LieSubalgebra R L₂) :=
  { LinearEquiv.submoduleMap (e : L₁ ≃ₗ[R] L₂) ↑L₁'' with
    map_lie' := @fun x y ↦ by
      apply SetCoe.ext
      -- ⊢ ↑(AddHom.toFun src✝.toAddHom ⁅x, y⁆) = ↑⁅AddHom.toFun src✝.toAddHom x, AddHo …
      exact LieHom.map_lie (↑e : L₁ →ₗ⁅R⁆ L₂) ↑x ↑y }
      -- 🎉 no goals
#align lie_equiv.lie_subalgebra_map LieEquiv.lieSubalgebraMap

@[simp]
theorem lieSubalgebraMap_apply (x : L₁'') : ↑(e.lieSubalgebraMap _ x) = e x :=
  rfl
#align lie_equiv.lie_subalgebra_map_apply LieEquiv.lieSubalgebraMap_apply

/-- An equivalence of Lie algebras restricts to an equivalence from any Lie subalgebra onto its
image. -/
def ofSubalgebras (h : L₁'.map ↑e = L₂') : L₁' ≃ₗ⁅R⁆ L₂' :=
  { LinearEquiv.ofSubmodules (e : L₁ ≃ₗ[R] L₂) (↑L₁') (↑L₂') (by
      rw [← h]
      -- ⊢ Submodule.map (↑(toLinearEquiv e)) L₁'.toSubmodule = (LieSubalgebra.map e.to …
      rfl) with
      -- 🎉 no goals
    map_lie' := @fun x y ↦ by
      apply SetCoe.ext
      -- ⊢ ↑(AddHom.toFun src✝.toAddHom ⁅x, y⁆) = ↑⁅AddHom.toFun src✝.toAddHom x, AddHo …
      exact LieHom.map_lie (↑e : L₁ →ₗ⁅R⁆ L₂) ↑x ↑y }
      -- 🎉 no goals
#align lie_equiv.of_subalgebras LieEquiv.ofSubalgebras

@[simp]
theorem ofSubalgebras_apply (h : L₁'.map ↑e = L₂') (x : L₁') : ↑(e.ofSubalgebras _ _ h x) = e x :=
  rfl
#align lie_equiv.of_subalgebras_apply LieEquiv.ofSubalgebras_apply

@[simp]
theorem ofSubalgebras_symm_apply (h : L₁'.map ↑e = L₂') (x : L₂') :
    ↑((e.ofSubalgebras _ _ h).symm x) = e.symm x :=
  rfl
#align lie_equiv.of_subalgebras_symm_apply LieEquiv.ofSubalgebras_symm_apply

end LieEquiv
