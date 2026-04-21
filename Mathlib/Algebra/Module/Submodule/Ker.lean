/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-!
# Kernel of a linear map

This file defines the kernel of a linear map.

## Main definitions

* `LinearMap.ker`: the kernel of a linear map as a submodule of the domain

## Notation

* We continue to use the notations `M →ₛₗ[σ] M₂` and `M →ₗ[R] M₂` for the type of semilinear
  (resp. linear) maps from `M` to `M₂` over the ring homomorphism `σ` (resp. over the ring `R`).

## Tags
linear algebra, vector space, module

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open Function

open Pointwise

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}
variable {K : Type*}
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable {V : Type*} {V₂ : Type*}

/-! ### Properties of linear maps -/


namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

open Submodule

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

/-- The kernel of a linear map `f : M → M₂` is defined to be `comap f ⊥`. This is equivalent to the
set of `x : M` such that `f x = 0`. The kernel is a submodule of `M`. -/
def ker (f : M →ₛₗ[τ₁₂] M₂) : Submodule R M :=
  comap f ⊥

@[simp]
theorem mem_ker {f : M →ₛₗ[τ₁₂] M₂} {y} : y ∈ ker f ↔ f y = 0 :=
  mem_bot R₂

@[simp]
theorem ker_id : ker (LinearMap.id : M →ₗ[R] M) = ⊥ :=
  rfl

@[simp]
theorem map_coe_ker (f : M →ₛₗ[τ₁₂] M₂) (x : ker f) : f x = 0 :=
  mem_ker.1 x.2

theorem ker_toAddSubmonoid (f : M →ₛₗ[τ₁₂] M₂) : (ker f).toAddSubmonoid = (AddMonoidHom.mker f) :=
  rfl

theorem le_ker_iff_comp_subtype_eq_zero {N : Submodule R M} {f : M →ₛₗ[τ₁₂] M₂} :
    N ≤ ker f ↔ f ∘ₛₗ N.subtype = 0 := by
  rw [SetLike.le_def, LinearMap.ext_iff, Subtype.forall]; rfl

theorem comp_ker_subtype (f : M →ₛₗ[τ₁₂] M₂) : f.comp (ker f).subtype = 0 :=
  LinearMap.ext fun x => mem_ker.1 x.2

theorem ker_comp (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) :
    ker (g.comp f : M →ₛₗ[τ₁₃] M₃) = comap f (ker g) :=
  rfl

theorem ker_le_ker_comp (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) :
    ker f ≤ ker (g.comp f : M →ₛₗ[τ₁₃] M₃) := by rw [ker_comp]; exact comap_mono bot_le

theorem ker_sup_ker_le_ker_comp_of_commute {f g : M →ₗ[R] M} (h : Commute f g) :
    ker f ⊔ ker g ≤ ker (f ∘ₗ g) := by
  refine sup_le_iff.mpr ⟨?_, ker_le_ker_comp g f⟩
  rw [← Module.End.mul_eq_comp, h.eq, Module.End.mul_eq_comp]
  exact ker_le_ker_comp f g

@[simp]
theorem ker_le_comap {p : Submodule R₂ M₂} (f : M →ₛₗ[τ₁₂] M₂) :
    ker f ≤ p.comap f :=
  fun x hx ↦ by simp [mem_ker.mp hx]

theorem disjoint_ker {f : M →ₛₗ[τ₁₂] M₂} {p : Submodule R M} :
    Disjoint p (ker f) ↔ ∀ x ∈ p, f x = 0 → x = 0 := by
  simp [disjoint_def]

theorem ker_eq_bot' {f : M →ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ ∀ m, f m = 0 → m = 0 := by
  simpa [disjoint_iff_inf_le] using disjoint_ker (f := f) (p := ⊤)

theorem ker_eq_bot_of_inverse {τ₂₁ : R₂ →+* R} [RingHomInvPair τ₁₂ τ₂₁] {f : M →ₛₗ[τ₁₂] M₂}
    {g : M₂ →ₛₗ[τ₂₁] M} (h : (g.comp f : M →ₗ[R] M) = id) : ker f = ⊥ :=
  ker_eq_bot'.2 fun m hm => by rw [← id_apply (R := R) m, ← h, comp_apply, hm, g.map_zero]

theorem le_ker_iff_map [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {p : Submodule R M} :
    p ≤ ker f ↔ map f p = ⊥ := by rw [ker, eq_bot_iff, map_le_iff_le_comap]

theorem ker_codRestrict {τ₂₁ : R₂ →+* R} (p : Submodule R M) (f : M₂ →ₛₗ[τ₂₁] M) (hf) :
    ker (codRestrict p f hf) = ker f := by rw [ker, comap_codRestrict, Submodule.map_bot]; rfl

lemma ker_domRestrict [AddCommMonoid M₁] [Module R M₁] (p : Submodule R M) (f : M →ₗ[R] M₁) :
    ker (domRestrict f p) = (ker f).comap p.subtype := ker_comp ..

theorem ker_restrict [AddCommMonoid M₁] [Module R M₁] {p : Submodule R M} {q : Submodule R M₁}
    {f : M →ₗ[R] M₁} (hf : ∀ x : M, x ∈ p → f x ∈ q) :
    ker (f.restrict hf) = (ker f).comap p.subtype := by
  rw [restrict_eq_codRestrict_domRestrict, ker_codRestrict, ker_domRestrict]

@[simp]
theorem ker_zero : ker (0 : M →ₛₗ[τ₁₂] M₂) = ⊤ :=
  eq_top_iff'.2 fun x => by simp

@[simp]
theorem ker_eq_top {f : M →ₛₗ[τ₁₂] M₂} : ker f = ⊤ ↔ f = 0 :=
  ⟨fun h => ext fun _ => mem_ker.1 <| h.symm ▸ trivial, fun h => h.symm ▸ ker_zero⟩

theorem exists_ne_zero_of_sSup_eq_top {f : M →ₛₗ[τ₁₂] M₂} (h : f ≠ 0) (s : Set (Submodule R M))
    (hs : sSup s = ⊤) : ∃ m ∈ s, f ∘ₛₗ m.subtype ≠ 0 := by
  contrapose! h
  simp_rw [← ker_eq_top, eq_top_iff, ← hs, sSup_le_iff, le_ker_iff_comp_subtype_eq_zero]
  exact h

@[simp]
theorem _root_.AddMonoidHom.coe_toIntLinearMap_ker {M M₂ : Type*} [AddCommGroup M] [AddCommGroup M₂]
    (f : M →+ M₂) : LinearMap.ker f.toIntLinearMap = AddSubgroup.toIntSubmodule f.ker := rfl

theorem ker_eq_bot_of_injective {f : M →ₛₗ[τ₁₂] M₂} (hf : Injective f) : ker f = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  simpa only [mem_ker, mem_bot, ← map_zero f, hf.eq_iff] using hx

/-- The increasing sequence of submodules consisting of the kernels of the iterates of a linear map.
-/
@[simps]
def iterateKer (f : M →ₗ[R] M) : ℕ →o Submodule R M where
  toFun n := ker (f ^ n)
  monotone' n m w x h := by
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le w
    rw [LinearMap.mem_ker] at h
    rw [LinearMap.mem_ker, add_comm, pow_add, Module.End.mul_apply, h, map_zero]

end AddCommMonoid

section Ring

variable [Ring R] [Ring R₂]
variable [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂}
variable {f : M →ₛₗ[τ₁₂] M₂}

open Submodule

theorem ker_toAddSubgroup (f : M →ₛₗ[τ₁₂] M₂) : (ker f).toAddSubgroup = f.toAddMonoidHom.ker :=
  rfl

theorem sub_mem_ker_iff {x y} : x - y ∈ ker f ↔ f x = f y := by rw [mem_ker, map_sub, sub_eq_zero]

theorem disjoint_ker_iff_injOn {p : Submodule R M} :
    Disjoint p (LinearMap.ker f) ↔ Set.InjOn f p := by
  rw [disjoint_ker, Set.injOn_iff_map_eq_zero]

@[deprecated disjoint_ker_iff_injOn (since := "2025-11-07")]
theorem disjoint_ker' {p : Submodule R M} :
    Disjoint p (ker f) ↔ ∀ x ∈ p, ∀ y ∈ p, f x = f y → x = y := by
  simp [disjoint_ker_iff_injOn, Set.InjOn]

theorem injOn_of_disjoint_ker {p : Submodule R M} {s : Set M} (h : s ⊆ p)
    (hd : Disjoint p (ker f)) : Set.InjOn f s :=
  disjoint_ker_iff_injOn.mp hd |>.mono h

theorem ker_eq_bot {f : M →ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Injective f := by
  simpa [disjoint_iff_inf_le] using disjoint_ker_iff_injOn (f := f) (p := ⊤)

@[deprecated (since := "2025-12-23")]
alias _root_.LinearMapClass.ker_eq_bot := ker_eq_bot

@[simp] lemma injective_domRestrict_iff {f : M →ₛₗ[τ₁₂] M₂} {S : Submodule R M} :
    Injective (f.domRestrict S) ↔ S ⊓ LinearMap.ker f = ⊥ := by
  rw [← LinearMap.ker_eq_bot]
  refine ⟨fun h ↦ le_bot_iff.1 ?_, fun h ↦ le_bot_iff.1 ?_⟩
  · intro x ⟨hx, h'x⟩
    have : ⟨x, hx⟩ ∈ LinearMap.ker (LinearMap.domRestrict f S) := by simpa using h'x
    rw [h] at this
    simpa [mk_eq_zero] using this
  · rintro ⟨x, hx⟩ h'x
    have : x ∈ S ⊓ LinearMap.ker f := ⟨hx, h'x⟩
    rw [h] at this
    simpa [mk_eq_zero] using this

@[simp] theorem injective_restrict_iff_disjoint {p : Submodule R M} {f : M →ₗ[R] M}
    (hf : ∀ x ∈ p, f x ∈ p) :
    Injective (f.restrict hf) ↔ Disjoint p (ker f) := by
  rw [← ker_eq_bot, ker_restrict hf, ← ker_domRestrict, ker_eq_bot, injective_domRestrict_iff,
    disjoint_iff]

end Ring

section Semifield

variable [Semifield K]
variable [AddCommMonoid V] [Module K V]
variable [AddCommMonoid V₂] [Module K V₂]

theorem ker_smul (f : V →ₗ[K] V₂) (a : K) (h : a ≠ 0) : ker (a • f) = ker f :=
  Submodule.comap_smul f _ a h

theorem ker_smul' (f : V →ₗ[K] V₂) (a : K) : ker (a • f) = ⨅ _ : a ≠ 0, ker f :=
  Submodule.comap_smul' f _ a

end Semifield

end LinearMap

namespace Submodule

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable (p : Submodule R M)
variable {τ₁₂ : R →+* R₂}

open LinearMap

@[simp]
theorem comap_bot (f : M →ₛₗ[τ₁₂] M₂) : comap f ⊥ = ker f :=
  rfl

@[simp]
theorem ker_subtype : ker p.subtype = ⊥ :=
  ker_eq_bot_of_injective fun _ _ => Subtype.ext

@[simp]
theorem ker_inclusion (p p' : Submodule R M) (h : p ≤ p') : ker (inclusion h) = ⊥ := by
  rw [inclusion, ker_codRestrict, ker_subtype]

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

end Semiring

section RestrictScalars

variable (R : Type*) {S M N : Type*} [Semiring R] [Semiring S] [SMul R S]
variable [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

@[simp]
theorem ker_restrictScalars (f : M →ₗ[S] N) :
    ker (f.restrictScalars R) = (ker f).restrictScalars R :=
  rfl

end RestrictScalars

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

@[simp]
theorem ker_comp (l : M →ₛₗ[σ₁₂] M₂) :
    LinearMap.ker (((e'' : M₂ →ₛₗ[σ₂₃] M₃).comp l : M →ₛₗ[σ₁₃] M₃) : M →ₛₗ[σ₁₃] M₃) =
    LinearMap.ker l :=
  LinearMap.ker_comp_of_ker_eq_bot _ e''.ker

end

end AddCommMonoid

end LinearEquiv
