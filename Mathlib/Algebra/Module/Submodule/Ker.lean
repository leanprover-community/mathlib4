/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import Mathlib.Algebra.Module.Submodule.Map

#align_import linear_algebra.basic from "leanprover-community/mathlib"@"9d684a893c52e1d6692a504a118bfccbae04feeb"

/-!
# Kernel of a linear map

This file defines the kernel of a linear map.

## Main definitions

* `LinearMap.ker`: the kernel of a linear map as a submodule of the domain

## Notations

* We continue to use the notations `M →ₛₗ[σ] M₂` and `M →ₗ[R] M₂` for the type of semilinear
  (resp. linear) maps from `M` to `M₂` over the ring homomorphism `σ` (resp. over the ring `R`).

## Tags
linear algebra, vector space, module

-/

open Function

open Pointwise

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable {K : Type*}
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable {V : Type*} {V₂ : Type*}

/-! ### Properties of linear maps -/


namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

open Submodule

variable {σ₂₁ : R₂ →+* R} {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]

/-- The kernel of a linear map `f : M → M₂` is defined to be `comap f ⊥`. This is equivalent to the
set of `x : M` such that `f x = 0`. The kernel is a submodule of `M`. -/
def ker (f : F) : Submodule R M :=
  comap f ⊥
#align linear_map.ker LinearMap.ker

@[simp]
theorem mem_ker {f : F} {y} : y ∈ ker f ↔ f y = 0 :=
  mem_bot R₂
#align linear_map.mem_ker LinearMap.mem_ker

@[simp]
theorem ker_id : ker (LinearMap.id : M →ₗ[R] M) = ⊥ :=
  rfl
#align linear_map.ker_id LinearMap.ker_id

@[simp]
theorem map_coe_ker (f : F) (x : ker f) : f x = 0 :=
  mem_ker.1 x.2
#align linear_map.map_coe_ker LinearMap.map_coe_ker

theorem ker_toAddSubmonoid (f : M →ₛₗ[τ₁₂] M₂) : f.ker.toAddSubmonoid = (AddMonoidHom.mker f) :=
  rfl
#align linear_map.ker_to_add_submonoid LinearMap.ker_toAddSubmonoid

theorem comp_ker_subtype (f : M →ₛₗ[τ₁₂] M₂) : f.comp f.ker.subtype = 0 :=
  LinearMap.ext fun x => mem_ker.1 x.2
#align linear_map.comp_ker_subtype LinearMap.comp_ker_subtype

theorem ker_comp (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) :
    ker (g.comp f : M →ₛₗ[τ₁₃] M₃) = comap f (ker g) :=
  rfl
#align linear_map.ker_comp LinearMap.ker_comp

theorem ker_le_ker_comp (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) :
    ker f ≤ ker (g.comp f : M →ₛₗ[τ₁₃] M₃) := by rw [ker_comp]; exact comap_mono bot_le
#align linear_map.ker_le_ker_comp LinearMap.ker_le_ker_comp

theorem ker_sup_ker_le_ker_comp_of_commute {f g : M →ₗ[R] M} (h : Commute f g) :
    ker f ⊔ ker g ≤ ker (f ∘ₗ g) := by
  refine sup_le_iff.mpr ⟨?_, ker_le_ker_comp g f⟩
  rw [← mul_eq_comp, h.eq, mul_eq_comp]
  exact ker_le_ker_comp f g

@[simp]
theorem ker_le_comap {p : Submodule R₂ M₂} (f : M →ₛₗ[τ₁₂] M₂) :
    ker f ≤ p.comap f :=
  fun x hx ↦ by simp [mem_ker.mp hx]

theorem disjoint_ker {f : F} {p : Submodule R M} :
    Disjoint p (ker f) ↔ ∀ x ∈ p, f x = 0 → x = 0 := by
  simp [disjoint_def]
#align linear_map.disjoint_ker LinearMap.disjoint_ker

theorem ker_eq_bot' {f : F} : ker f = ⊥ ↔ ∀ m, f m = 0 → m = 0 := by
  simpa [disjoint_iff_inf_le] using disjoint_ker (f := f) (p := ⊤)
#align linear_map.ker_eq_bot' LinearMap.ker_eq_bot'

theorem ker_eq_bot_of_inverse {τ₂₁ : R₂ →+* R} [RingHomInvPair τ₁₂ τ₂₁] {f : M →ₛₗ[τ₁₂] M₂}
    {g : M₂ →ₛₗ[τ₂₁] M} (h : (g.comp f : M →ₗ[R] M) = id) : ker f = ⊥ :=
  ker_eq_bot'.2 fun m hm => by rw [← id_apply (R := R) m, ← h, comp_apply, hm, g.map_zero]
#align linear_map.ker_eq_bot_of_inverse LinearMap.ker_eq_bot_of_inverse

theorem le_ker_iff_map [RingHomSurjective τ₁₂] {f : F} {p : Submodule R M} :
    p ≤ ker f ↔ map f p = ⊥ := by rw [ker, eq_bot_iff, map_le_iff_le_comap]
#align linear_map.le_ker_iff_map LinearMap.le_ker_iff_map

theorem ker_codRestrict {τ₂₁ : R₂ →+* R} (p : Submodule R M) (f : M₂ →ₛₗ[τ₂₁] M) (hf) :
    ker (codRestrict p f hf) = ker f := by rw [ker, comap_codRestrict, Submodule.map_bot]; rfl
#align linear_map.ker_cod_restrict LinearMap.ker_codRestrict

theorem ker_restrict [AddCommMonoid M₁] [Module R M₁] {p : Submodule R M} {q : Submodule R M₁}
    {f : M →ₗ[R] M₁} (hf : ∀ x : M, x ∈ p → f x ∈ q) :
    ker (f.restrict hf) = LinearMap.ker (f.domRestrict p) := by
  rw [restrict_eq_codRestrict_domRestrict, ker_codRestrict]
#align linear_map.ker_restrict LinearMap.ker_restrict

@[simp]
theorem ker_zero : ker (0 : M →ₛₗ[τ₁₂] M₂) = ⊤ :=
  eq_top_iff'.2 fun x => by simp
#align linear_map.ker_zero LinearMap.ker_zero

theorem ker_eq_top {f : M →ₛₗ[τ₁₂] M₂} : ker f = ⊤ ↔ f = 0 :=
  ⟨fun h => ext fun _ => mem_ker.1 <| h.symm ▸ trivial, fun h => h.symm ▸ ker_zero⟩
#align linear_map.ker_eq_top LinearMap.ker_eq_top

@[simp]
theorem _root_.AddMonoidHom.coe_toIntLinearMap_ker {M M₂ : Type*} [AddCommGroup M] [AddCommGroup M₂]
    (f : M →+ M₂) : LinearMap.ker f.toIntLinearMap = AddSubgroup.toIntSubmodule f.ker := rfl

theorem ker_eq_bot_of_injective {f : F} (hf : Injective f) : ker f = ⊥ := by
  have : Disjoint ⊤ (ker f) := by
    -- Porting note: `← map_zero f` should work here, but it needs to be directly applied to H.
    rw [disjoint_ker]
    intros _ _ H
    rw [← map_zero f] at H
    exact hf H
  simpa [disjoint_iff_inf_le]
#align linear_map.ker_eq_bot_of_injective LinearMap.ker_eq_bot_of_injective

/-- The increasing sequence of submodules consisting of the kernels of the iterates of a linear map.
-/
@[simps]
def iterateKer (f : M →ₗ[R] M) : ℕ →o Submodule R M where
  toFun n := ker (f ^ n)
  monotone' n m w x h := by
    obtain ⟨c, rfl⟩ := le_iff_exists_add.mp w
    rw [LinearMap.mem_ker] at h
    rw [LinearMap.mem_ker, add_comm, pow_add, LinearMap.mul_apply, h, LinearMap.map_zero]
#align linear_map.iterate_ker LinearMap.iterateKer

end AddCommMonoid

section Ring

variable [Ring R] [Ring R₂] [Ring R₃]
variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]
variable {f : F}

open Submodule

theorem ker_toAddSubgroup (f : M →ₛₗ[τ₁₂] M₂) : (ker f).toAddSubgroup = f.toAddMonoidHom.ker :=
  rfl
#align linear_map.ker_to_add_subgroup LinearMap.ker_toAddSubgroup

theorem sub_mem_ker_iff {x y} : x - y ∈ ker f ↔ f x = f y := by rw [mem_ker, map_sub, sub_eq_zero]
#align linear_map.sub_mem_ker_iff LinearMap.sub_mem_ker_iff

theorem disjoint_ker' {p : Submodule R M} :
    Disjoint p (ker f) ↔ ∀ x ∈ p, ∀ y ∈ p, f x = f y → x = y :=
  disjoint_ker.trans
    ⟨fun H x hx y hy h => eq_of_sub_eq_zero <| H _ (sub_mem hx hy) (by simp [h]),
     fun H x h₁ h₂ => H x h₁ 0 (zero_mem _) (by simpa using h₂)⟩
#align linear_map.disjoint_ker' LinearMap.disjoint_ker'

theorem injOn_of_disjoint_ker {p : Submodule R M} {s : Set M} (h : s ⊆ p)
    (hd : Disjoint p (ker f)) : Set.InjOn f s := fun _ hx _ hy =>
  disjoint_ker'.1 hd _ (h hx) _ (h hy)
#align linear_map.inj_on_of_disjoint_ker LinearMap.injOn_of_disjoint_ker

variable (F)

theorem _root_.LinearMapClass.ker_eq_bot : ker f = ⊥ ↔ Injective f := by
  simpa [disjoint_iff_inf_le] using disjoint_ker' (f := f) (p := ⊤)
#align linear_map_class.ker_eq_bot LinearMapClass.ker_eq_bot

variable {F}

theorem ker_eq_bot {f : M →ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Injective f :=
  LinearMapClass.ker_eq_bot _
#align linear_map.ker_eq_bot LinearMap.ker_eq_bot

@[simp] lemma injective_domRestrict_iff {f : M →ₛₗ[τ₁₂] M₂} {S : Submodule R M} :
    Injective (f.domRestrict S) ↔ S ⊓ LinearMap.ker f = ⊥ := by
  rw [← LinearMap.ker_eq_bot]
  refine ⟨fun h ↦ le_bot_iff.1 ?_, fun h ↦ le_bot_iff.1 ?_⟩
  · intro x ⟨hx, h'x⟩
    have : ⟨x, hx⟩ ∈ LinearMap.ker (LinearMap.domRestrict f S) := by simpa using h'x
    rw [h] at this
    simpa using this
  · rintro ⟨x, hx⟩ h'x
    have : x ∈ S ⊓ LinearMap.ker f := ⟨hx, h'x⟩
    rw [h] at this
    simpa using this

@[simp] theorem injective_restrict_iff_disjoint {p : Submodule R M} {f : M →ₗ[R] M}
    (hf : ∀ x ∈ p, f x ∈ p) :
    Injective (f.restrict hf) ↔ Disjoint p (ker f) := by
  rw [← ker_eq_bot, ker_restrict hf, ker_eq_bot, injective_domRestrict_iff, disjoint_iff]

end Ring

section Semifield

variable [Semifield K]
variable [AddCommMonoid V] [Module K V]
variable [AddCommMonoid V₂] [Module K V₂]

theorem ker_smul (f : V →ₗ[K] V₂) (a : K) (h : a ≠ 0) : ker (a • f) = ker f :=
  Submodule.comap_smul f _ a h
#align linear_map.ker_smul LinearMap.ker_smul

theorem ker_smul' (f : V →ₗ[K] V₂) (a : K) : ker (a • f) = ⨅ _ : a ≠ 0, ker f :=
  Submodule.comap_smul' f _ a
#align linear_map.ker_smul' LinearMap.ker_smul'

end Semifield

end LinearMap

namespace Submodule

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable (p p' : Submodule R M) (q : Submodule R₂ M₂)
variable {τ₁₂ : R →+* R₂}
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]

open LinearMap

@[simp]
theorem comap_bot (f : F) : comap f ⊥ = ker f :=
  rfl
#align submodule.comap_bot Submodule.comap_bot

@[simp]
theorem ker_subtype : ker p.subtype = ⊥ :=
  ker_eq_bot_of_injective fun _ _ => Subtype.ext_val
#align submodule.ker_subtype Submodule.ker_subtype

@[simp]
theorem ker_inclusion (p p' : Submodule R M) (h : p ≤ p') : ker (inclusion h) = ⊥ := by
  rw [inclusion, ker_codRestrict, ker_subtype]
#align submodule.ker_of_le Submodule.ker_inclusion

end AddCommMonoid

end Submodule

namespace LinearMap

section Semiring

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

theorem ker_comp_of_ker_eq_bot (f : M →ₛₗ[τ₁₂] M₂) {g : M₂ →ₛₗ[τ₂₃] M₃} (hg : ker g = ⊥) :
    ker (g.comp f : M →ₛₗ[τ₁₃] M₃) = ker f := by rw [ker_comp, hg, Submodule.comap_bot]
#align linear_map.ker_comp_of_ker_eq_bot LinearMap.ker_comp_of_ker_eq_bot

end Semiring

end LinearMap

/-! ### Linear equivalences -/


namespace LinearEquiv

section AddCommMonoid

section

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable {module_M : Module R M} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}
variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
variable {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable {σ₃₂ : R₃ →+* R₂}
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
variable {re₂₃ : RingHomInvPair σ₂₃ σ₃₂} {re₃₂ : RingHomInvPair σ₃₂ σ₂₃}
variable (e : M ≃ₛₗ[σ₁₂] M₂) (e'' : M₂ ≃ₛₗ[σ₂₃] M₃)

@[simp]
protected theorem ker : LinearMap.ker (e : M →ₛₗ[σ₁₂] M₂) = ⊥ :=
  LinearMap.ker_eq_bot_of_injective e.toEquiv.injective
#align linear_equiv.ker LinearEquiv.ker

@[simp]
theorem ker_comp (l : M →ₛₗ[σ₁₂] M₂) :
    LinearMap.ker (((e'' : M₂ →ₛₗ[σ₂₃] M₃).comp l : M →ₛₗ[σ₁₃] M₃) : M →ₛₗ[σ₁₃] M₃) =
    LinearMap.ker l :=
  LinearMap.ker_comp_of_ker_eq_bot _ e''.ker
#align linear_equiv.ker_comp LinearEquiv.ker_comp

end

end AddCommMonoid

end LinearEquiv
