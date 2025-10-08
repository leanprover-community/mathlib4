/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.IdealOperations

/-!
# Trivial Lie modules and Abelian Lie algebras

The action of a Lie algebra `L` on a module `M` is trivial if `⁅x, m⁆ = 0` for all `x ∈ L` and
`m ∈ M`. In the special case that `M = L` with the adjoint action, triviality corresponds to the
concept of an Abelian Lie algebra.

In this file we define these concepts and provide some related definitions and results.

## Main definitions

  * `LieModule.IsTrivial`
  * `IsLieAbelian`
  * `commutative_ring_iff_abelian_lie_ring`
  * `LieModule.ker`
  * `LieModule.maxTrivSubmodule`
  * `LieAlgebra.center`

## Tags

lie algebra, abelian, commutative, center
-/


universe u v w w₁ w₂

/-- A Lie (ring) module is trivial iff all brackets vanish. -/
class LieModule.IsTrivial (L : Type v) (M : Type w) [Bracket L M] [Zero M] : Prop where
  trivial : ∀ (x : L) (m : M), ⁅x, m⁆ = 0

@[simp]
theorem trivial_lie_zero (L : Type v) (M : Type w) [Bracket L M] [Zero M] [LieModule.IsTrivial L M]
    (x : L) (m : M) : ⁅x, m⁆ = 0 :=
  LieModule.IsTrivial.trivial x m

instance LieModule.instIsTrivialOfSubsingleton {L M : Type*}
    [LieRing L] [AddCommGroup M] [LieRingModule L M] [Subsingleton L] : LieModule.IsTrivial L M :=
  ⟨fun x m ↦ by rw [Subsingleton.eq_zero x, zero_lie]⟩

instance LieModule.instIsTrivialOfSubsingleton' {L M : Type*}
    [LieRing L] [AddCommGroup M] [LieRingModule L M] [Subsingleton M] : LieModule.IsTrivial L M :=
  ⟨fun x m ↦ by simp_rw [Subsingleton.eq_zero m, lie_zero]⟩

/-- A Lie algebra is Abelian iff it is trivial as a Lie module over itself. -/
abbrev IsLieAbelian (L : Type v) [Bracket L L] [Zero L] : Prop :=
  LieModule.IsTrivial L L

instance LieIdeal.isLieAbelian_of_trivial (R : Type u) (L : Type v) [CommRing R] [LieRing L]
    [LieAlgebra R L] (I : LieIdeal R L) [h : LieModule.IsTrivial L I] : IsLieAbelian I where
  trivial x y := by apply h.trivial

theorem Function.Injective.isLieAbelian {R : Type u} {L₁ : Type v} {L₂ : Type w} [CommRing R]
    [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂] {f : L₁ →ₗ⁅R⁆ L₂}
    (h₁ : Function.Injective f) (_ : IsLieAbelian L₂) : IsLieAbelian L₁ :=
  { trivial := fun x y => h₁ <|
      calc
        f ⁅x, y⁆ = ⁅f x, f y⁆ := LieHom.map_lie f x y
        _ = 0 := trivial_lie_zero _ _ _ _
        _ = f 0 := f.map_zero.symm}

theorem Function.Surjective.isLieAbelian {R : Type u} {L₁ : Type v} {L₂ : Type w} [CommRing R]
    [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂] {f : L₁ →ₗ⁅R⁆ L₂}
    (h₁ : Function.Surjective f) (h₂ : IsLieAbelian L₁) : IsLieAbelian L₂ :=
  { trivial := fun x y => by
      obtain ⟨u, rfl⟩ := h₁ x
      obtain ⟨v, rfl⟩ := h₁ y
      rw [← LieHom.map_lie, trivial_lie_zero, LieHom.map_zero] }

theorem lie_abelian_iff_equiv_lie_abelian {R : Type u} {L₁ : Type v} {L₂ : Type w} [CommRing R]
    [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂] (e : L₁ ≃ₗ⁅R⁆ L₂) :
    IsLieAbelian L₁ ↔ IsLieAbelian L₂ :=
  ⟨e.symm.injective.isLieAbelian, e.injective.isLieAbelian⟩

theorem commutative_ring_iff_abelian_lie_ring {A : Type v} [Ring A] :
    Std.Commutative (α := A) (· * ·) ↔ IsLieAbelian A := by
  have h₁ : Std.Commutative (α := A) (· * ·) ↔ ∀ a b : A, a * b = b * a :=
    ⟨fun h => h.1, fun h => ⟨h⟩⟩
  have h₂ : IsLieAbelian A ↔ ∀ a b : A, ⁅a, b⁆ = 0 := ⟨fun h => h.1, fun h => ⟨h⟩⟩
  simp only [h₁, h₂, LieRing.of_associative_ring_bracket, sub_eq_zero]

@[simp] theorem LieSubalgebra.isLieAbelian_lieSpan_iff
    {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {s : Set L} :
    IsLieAbelian (lieSpan R L s) ↔ ∀ᵉ (x ∈ s) (y ∈ s), ⁅x, y⁆ = 0 := by
  refine ⟨fun h x hx y hy ↦ ?_, fun h ↦ ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ?_⟩⟩
  · let x' : lieSpan R L s := ⟨x, subset_lieSpan hx⟩
    let y' : lieSpan R L s := ⟨y, subset_lieSpan hy⟩
    suffices ⁅x', y'⁆ = 0 by simpa [x', y', Subtype.ext_iff, -trivial_lie_zero] using this
    simp
  · induction hx using lieSpan_induction with
    | mem w hw =>
      induction hy using lieSpan_induction with
      | mem u hu => simpa [Subtype.ext_iff] using h w hw u hu
      | zero => simp [Subtype.ext_iff]
      | add u v _ _ hu hv =>
        simp only [Subtype.ext_iff, coe_bracket, ZeroMemClass.coe_zero, lie_add] at hu hv ⊢
        simp [hu, hv]
      | smul t u _ hu =>
        simp only [Subtype.ext_iff, coe_bracket, ZeroMemClass.coe_zero] at hu
        simp [Subtype.ext_iff, hu]
      | lie u v _ _ hu hv =>
        simp only [Subtype.ext_iff, coe_bracket, ZeroMemClass.coe_zero] at hu hv ⊢
        rw [leibniz_lie]
        simp [hu, hv]
    | zero => simp [Subtype.ext_iff]
    | add u v _ _ hu hv =>
      simp only [Subtype.ext_iff, coe_bracket, ZeroMemClass.coe_zero, add_lie] at hu hv ⊢
      simp [hu, hv]
    | smul t u _ hu =>
      simp only [Subtype.ext_iff, coe_bracket, ZeroMemClass.coe_zero] at hu
      simp [Subtype.ext_iff, hu]
    | lie u v _ _ hu hv =>
      simp only [Subtype.ext_iff, coe_bracket, ZeroMemClass.coe_zero] at hu hv ⊢
      simp [hu, hv]

section Center

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

namespace LieModule

/-- The kernel of the action of a Lie algebra `L` on a Lie module `M` as a Lie ideal in `L`. -/
protected def ker : LieIdeal R L :=
  (toEnd R L M).ker

@[simp]
protected theorem mem_ker (x : L) : x ∈ LieModule.ker R L M ↔ ∀ m : M, ⁅x, m⁆ = 0 := by
  simp only [LieModule.ker, LieHom.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
    toEnd_apply_apply]

lemma isFaithful_iff_ker_eq_bot : IsFaithful R L M ↔ LieModule.ker R L M = ⊥ := by
  rw [isFaithful_iff', LieSubmodule.ext_iff]
  aesop

@[simp] lemma ker_eq_bot [IsFaithful R L M] :
    LieModule.ker R L M = ⊥ :=
  (isFaithful_iff_ker_eq_bot R L M).mp inferInstance

/-- The largest submodule of a Lie module `M` on which the Lie algebra `L` acts trivially. -/
def maxTrivSubmodule : LieSubmodule R L M where
  carrier := { m | ∀ x : L, ⁅x, m⁆ = 0 }
  zero_mem' x := lie_zero x
  add_mem' {x y} hx hy z := by rw [lie_add, hx, hy, add_zero]
  smul_mem' c x hx y := by rw [lie_smul, hx, smul_zero]
  lie_mem {x m} hm y := by rw [hm, lie_zero]

@[simp]
theorem mem_maxTrivSubmodule (m : M) : m ∈ maxTrivSubmodule R L M ↔ ∀ x : L, ⁅x, m⁆ = 0 :=
  Iff.rfl

instance : IsTrivial L (maxTrivSubmodule R L M) where trivial x m := Subtype.ext (m.property x)

@[simp]
theorem ideal_oper_maxTrivSubmodule_eq_bot (I : LieIdeal R L) :
    ⁅I, maxTrivSubmodule R L M⁆ = ⊥ := by
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.lieIdeal_oper_eq_linear_span,
    LieSubmodule.bot_toSubmodule, Submodule.span_eq_bot]
  rintro m ⟨⟨x, hx⟩, ⟨⟨m, hm⟩, rfl⟩⟩
  exact hm x

theorem le_max_triv_iff_bracket_eq_bot {N : LieSubmodule R L M} :
    N ≤ maxTrivSubmodule R L M ↔ ⁅(⊤ : LieIdeal R L), N⁆ = ⊥ := by
  refine ⟨fun h => ?_, fun h m hm => ?_⟩
  · rw [← le_bot_iff, ← ideal_oper_maxTrivSubmodule_eq_bot R L M ⊤]
    exact LieSubmodule.mono_lie_right ⊤ h
  · rw [mem_maxTrivSubmodule]
    rw [LieSubmodule.lie_eq_bot_iff] at h
    exact fun x => h x (LieSubmodule.mem_top x) m hm

theorem trivial_iff_le_maximal_trivial (N : LieSubmodule R L M) :
    IsTrivial L N ↔ N ≤ maxTrivSubmodule R L M :=
  ⟨fun h m hm x => IsTrivial.casesOn h fun h => Subtype.ext_iff.mp (h x ⟨m, hm⟩), fun h =>
    { trivial := fun x m => Subtype.ext (h m.2 x) }⟩

theorem isTrivial_iff_max_triv_eq_top : IsTrivial L M ↔ maxTrivSubmodule R L M = ⊤ := by
  constructor
  · rintro ⟨h⟩; ext; simp only [mem_maxTrivSubmodule, h, forall_const, LieSubmodule.mem_top]
  · intro h; constructor; intro x m; revert x
    rw [← mem_maxTrivSubmodule R L M, h]; exact LieSubmodule.mem_top m

variable {R L M N}

/-- `maxTrivSubmodule` is functorial. -/
def maxTrivHom (f : M →ₗ⁅R,L⁆ N) : maxTrivSubmodule R L M →ₗ⁅R,L⁆ maxTrivSubmodule R L N where
  toFun m := ⟨f m, fun x =>
    (LieModuleHom.map_lie _ _ _).symm.trans <|
      (congr_arg f (m.property x)).trans (LieModuleHom.map_zero _)⟩
  map_add' m n := by ext; simp
  map_smul' t m := by ext; simp
  map_lie' {x m} := by simp

@[norm_cast, simp]
theorem coe_maxTrivHom_apply (f : M →ₗ⁅R,L⁆ N) (m : maxTrivSubmodule R L M) :
    (maxTrivHom f m : N) = f m :=
  rfl

/-- The maximal trivial submodules of Lie-equivalent Lie modules are Lie-equivalent. -/
def maxTrivEquiv (e : M ≃ₗ⁅R,L⁆ N) : maxTrivSubmodule R L M ≃ₗ⁅R,L⁆ maxTrivSubmodule R L N :=
  { maxTrivHom (e : M →ₗ⁅R,L⁆ N) with
    toFun := maxTrivHom (e : M →ₗ⁅R,L⁆ N)
    invFun := maxTrivHom (e.symm : N →ₗ⁅R,L⁆ M)
    left_inv := fun m => by ext; simp
    right_inv := fun n => by ext; simp }

@[norm_cast, simp]
theorem coe_maxTrivEquiv_apply (e : M ≃ₗ⁅R,L⁆ N) (m : maxTrivSubmodule R L M) :
    (maxTrivEquiv e m : N) = e ↑m :=
  rfl

@[simp]
theorem maxTrivEquiv_of_refl_eq_refl :
    maxTrivEquiv (LieModuleEquiv.refl : M ≃ₗ⁅R,L⁆ M) = LieModuleEquiv.refl := by
  ext; simp only [coe_maxTrivEquiv_apply, LieModuleEquiv.refl_apply]

@[simp]
theorem maxTrivEquiv_of_equiv_symm_eq_symm (e : M ≃ₗ⁅R,L⁆ N) :
    (maxTrivEquiv e).symm = maxTrivEquiv e.symm :=
  rfl

/-- A linear map between two Lie modules is a morphism of Lie modules iff the Lie algebra action
on it is trivial. -/
def maxTrivLinearMapEquivLieModuleHom : maxTrivSubmodule R L (M →ₗ[R] N) ≃ₗ[R] M →ₗ⁅R,L⁆ N where
  toFun f :=
    { toLinearMap := f.val
      map_lie' := fun {x m} => by
        have hf : ⁅x, f.val⁆ m = 0 := by rw [f.property x, LinearMap.zero_apply]
        rw [LieHom.lie_apply, sub_eq_zero, ← LinearMap.toFun_eq_coe] at hf; exact hf.symm}
  map_add' f g := by ext; simp
  map_smul' F G := by ext; simp
  invFun F := ⟨F, fun x => by ext; simp⟩
  left_inv f := by simp
  right_inv F := by simp

@[simp]
theorem coe_maxTrivLinearMapEquivLieModuleHom (f : maxTrivSubmodule R L (M →ₗ[R] N)) :
    (maxTrivLinearMapEquivLieModuleHom (M := M) (N := N) f : M → N) = f := by ext; rfl

@[simp]
theorem coe_maxTrivLinearMapEquivLieModuleHom_symm (f : M →ₗ⁅R,L⁆ N) :
    (maxTrivLinearMapEquivLieModuleHom (M := M) (N := N) |>.symm f : M → N) = f :=
  rfl

@[simp]
theorem toLinearMap_maxTrivLinearMapEquivLieModuleHom (f : maxTrivSubmodule R L (M →ₗ[R] N)) :
    (maxTrivLinearMapEquivLieModuleHom (M := M) (N := N) f : M →ₗ[R] N) = (f : M →ₗ[R] N) := by
  ext; rfl

@[simp]
theorem toLinearMap_maxTrivLinearMapEquivLieModuleHom_symm (f : M →ₗ⁅R,L⁆ N) :
    (maxTrivLinearMapEquivLieModuleHom (M := M) (N := N) |>.symm f : M →ₗ[R] N) = (f : M →ₗ[R] N) :=
  rfl

end LieModule

namespace LieAlgebra

/-- The center of a Lie algebra is the set of elements that commute with everything. It can
be viewed as the maximal trivial submodule of the Lie algebra as a Lie module over itself via the
adjoint representation. -/
abbrev center : LieIdeal R L :=
  LieModule.maxTrivSubmodule R L L

instance : IsLieAbelian (center R L) :=
  inferInstance

@[simp]
theorem ad_ker_eq_self_module_ker : (ad R L).ker = LieModule.ker R L L :=
  rfl

@[simp]
theorem self_module_ker_eq_center : LieModule.ker R L L = center R L := by
  ext y
  simp only [LieModule.mem_maxTrivSubmodule, LieModule.mem_ker, ← lie_skew _ y, neg_eq_zero]

theorem abelian_of_le_center (I : LieIdeal R L) (h : I ≤ center R L) : IsLieAbelian I :=
  haveI : LieModule.IsTrivial L I := (LieModule.trivial_iff_le_maximal_trivial R L L I).mpr h
  LieIdeal.isLieAbelian_of_trivial R L I

theorem isLieAbelian_iff_center_eq_top : IsLieAbelian L ↔ center R L = ⊤ :=
  LieModule.isTrivial_iff_max_triv_eq_top R L L

theorem isFaithful_self_iff : LieModule.IsFaithful R L L ↔ center R L = ⊥ := by
  rw [LieModule.isFaithful_iff_ker_eq_bot, self_module_ker_eq_center]

@[simp]
theorem center_eq_bot [LieModule.IsFaithful R L L] :
    center R L = ⊥ :=
  (isFaithful_self_iff R L).mp inferInstance

end LieAlgebra

namespace LieModule

variable {R L}
variable {x : L} (hx : x ∈ LieAlgebra.center R L) (y : L)
include hx

lemma commute_toEnd_of_mem_center_left :
    Commute (toEnd R L M x) (toEnd R L M y) := by
  rw [Commute.symm_iff, commute_iff_lie_eq, ← LieHom.map_lie, hx y, LieHom.map_zero]

lemma commute_toEnd_of_mem_center_right :
    Commute (toEnd R L M y) (toEnd R L M x) :=
  (LieModule.commute_toEnd_of_mem_center_left M hx y).symm

end LieModule

end Center

section IdealOperations

open LieSubmodule LieSubalgebra

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M] (N N' : LieSubmodule R L M) (I J : LieIdeal R L)

@[simp]
theorem LieSubmodule.trivial_lie_oper_zero [LieModule.IsTrivial L M] : ⁅I, N⁆ = ⊥ := by
  suffices ⁅I, N⁆ ≤ ⊥ from le_bot_iff.mp this
  rw [lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le]
  rintro m ⟨x, n, h⟩; rw [trivial_lie_zero] at h; simp [← h]

theorem LieSubmodule.lie_abelian_iff_lie_self_eq_bot : IsLieAbelian I ↔ ⁅I, I⁆ = ⊥ := by
  simp only [_root_.eq_bot_iff, lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le,
    LieSubmodule.bot_coe, Set.subset_singleton_iff, Set.mem_setOf_eq, exists_imp]
  refine
    ⟨fun h z x y hz =>
      hz.symm.trans
        (((I : LieSubalgebra R L).coe_bracket x y).symm.trans
          ((coe_zero_iff_zero _ _).mpr (by apply h.trivial))),
      fun h => ⟨fun x y => ((I : LieSubalgebra R L).coe_zero_iff_zero _).mp (h _ x y rfl)⟩⟩

variable {I N} in
lemma lie_eq_self_of_isAtom_of_ne_bot (hN : IsAtom N) (h : ⁅I, N⁆ ≠ ⊥) : ⁅I, N⁆ = N :=
  (hN.le_iff_eq h).mp <| LieSubmodule.lie_le_right N I

-- TODO: introduce typeclass for perfect Lie algebras and use it here in the conclusion
lemma lie_eq_self_of_isAtom_of_nonabelian {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) (hI : IsAtom I) (h : ¬IsLieAbelian I) :
    ⁅I, I⁆ = I :=
  lie_eq_self_of_isAtom_of_ne_bot hI <| not_imp_not.mpr (lie_abelian_iff_lie_self_eq_bot I).mpr h

end IdealOperations

section TrivialLieModule

set_option linter.unusedVariables false in
/-- A type synonym for an `R`-module to have a trivial Lie module structure. -/
@[nolint unusedArguments]
def TrivialLieModule (R L M : Type*) := M

namespace TrivialLieModule

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

instance : AddCommGroup (TrivialLieModule R L M) := inferInstanceAs (AddCommGroup M)

instance : Module R (TrivialLieModule R L M) := inferInstanceAs (Module R M)

/-- The linear equivalence between a trivial Lie module and its underlying `R`-module. -/
def equiv : (TrivialLieModule R L M) ≃ₗ[R] M := LinearEquiv.refl R M

instance : LieRingModule L (TrivialLieModule R L M) where
  bracket x m := 0
  add_lie := by simp
  lie_add := by simp
  leibniz_lie := by simp

instance : LieModule.IsTrivial L (TrivialLieModule R L M) where
  trivial _ _ := rfl

instance : LieModule R L (TrivialLieModule R L M) where
  smul_lie := by simp
  lie_smul := by simp

end TrivialLieModule

end TrivialLieModule
