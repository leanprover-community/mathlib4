/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Isomorphisms

#align_import algebra.lie.quotient from "leanprover-community/mathlib"@"3d7987cda72abc473c7cdbbb075170e9ac620042"

/-!
# Quotients of Lie algebras and Lie modules

Given a Lie submodule of a Lie module, the quotient carries a natural Lie module structure. In the
special case that the Lie module is the Lie algebra itself via the adjoint action, the submodule
is a Lie ideal and the quotient carries a natural Lie algebra structure.

We define these quotient structures here. A notable omission at the time of writing (February 2021)
is a statement and proof of the universal property of these quotients.

## Main definitions

  * `LieSubmodule.Quotient.lieQuotientLieModule`
  * `LieSubmodule.Quotient.lieQuotientLieAlgebra`

## Tags

lie algebra, quotient
-/


universe u v w w₁ w₂

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M] [LieModule R L M]
variable (N N' : LieSubmodule R L M) (I J : LieIdeal R L)

/-- The quotient of a Lie module by a Lie submodule. It is a Lie module. -/
instance : HasQuotient M (LieSubmodule R L M) :=
  ⟨fun N => M ⧸ N.toSubmodule⟩

namespace Quotient

variable {N I}

instance addCommGroup : AddCommGroup (M ⧸ N) :=
  Submodule.Quotient.addCommGroup _
#align lie_submodule.quotient.add_comm_group LieSubmodule.Quotient.addCommGroup

instance module' {S : Type*} [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] :
    Module S (M ⧸ N) :=
  Submodule.Quotient.module' _
#align lie_submodule.quotient.module' LieSubmodule.Quotient.module'

instance module : Module R (M ⧸ N) :=
  Submodule.Quotient.module _
#align lie_submodule.quotient.module LieSubmodule.Quotient.module

instance isCentralScalar {S : Type*} [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    [SMul Sᵐᵒᵖ R] [Module Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] :
    IsCentralScalar S (M ⧸ N) :=
  Submodule.Quotient.isCentralScalar _
#align lie_submodule.quotient.is_central_scalar LieSubmodule.Quotient.isCentralScalar

instance inhabited : Inhabited (M ⧸ N) :=
  ⟨0⟩
#align lie_submodule.quotient.inhabited LieSubmodule.Quotient.inhabited

/-- Map sending an element of `M` to the corresponding element of `M/N`, when `N` is a
lie_submodule of the lie_module `N`. -/
abbrev mk : M → M ⧸ N :=
  Submodule.Quotient.mk
#align lie_submodule.quotient.mk LieSubmodule.Quotient.mk

theorem is_quotient_mk (m : M) : Quotient.mk'' m = (mk m : M ⧸ N) :=
  rfl
#align lie_submodule.quotient.is_quotient_mk LieSubmodule.Quotient.is_quotient_mk

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural linear map from `L` to the endomorphisms of `M` leaving `N` invariant. -/
def lieSubmoduleInvariant : L →ₗ[R] Submodule.compatibleMaps N.toSubmodule N.toSubmodule :=
  LinearMap.codRestrict _ (LieModule.toEndomorphism R L M) fun _ _ => N.lie_mem
#align lie_submodule.quotient.lie_submodule_invariant LieSubmodule.Quotient.lieSubmoduleInvariant

variable (N)

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural Lie algebra morphism from `L` to the linear endomorphism of the quotient `M/N`. -/
def actionAsEndoMap : L →ₗ⁅R⁆ Module.End R (M ⧸ N) :=
  { LinearMap.comp (Submodule.mapQLinear (N : Submodule R M) (N : Submodule R M))
      lieSubmoduleInvariant with
    map_lie' := fun {_ _} =>
      Submodule.linearMap_qext _ <| LinearMap.ext fun _ => congr_arg mk <| lie_lie _ _ _ }
#align lie_submodule.quotient.action_as_endo_map LieSubmodule.Quotient.actionAsEndoMap

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there is
a natural bracket action of `L` on the quotient `M/N`. -/
instance actionAsEndoMapBracket : Bracket L (M ⧸ N) :=
  ⟨fun x n => actionAsEndoMap N x n⟩
#align lie_submodule.quotient.action_as_endo_map_bracket LieSubmodule.Quotient.actionAsEndoMapBracket

instance lieQuotientLieRingModule : LieRingModule L (M ⧸ N) :=
  { LieRingModule.compLieHom _ (actionAsEndoMap N) with bracket := Bracket.bracket }
#align lie_submodule.quotient.lie_quotient_lie_ring_module LieSubmodule.Quotient.lieQuotientLieRingModule

/-- The quotient of a Lie module by a Lie submodule, is a Lie module. -/
instance lieQuotientLieModule : LieModule R L (M ⧸ N) :=
  LieModule.compLieHom _ (actionAsEndoMap N)
#align lie_submodule.quotient.lie_quotient_lie_module LieSubmodule.Quotient.lieQuotientLieModule

instance lieQuotientHasBracket : Bracket (L ⧸ I) (L ⧸ I) :=
  ⟨by
    intro x y
    apply Quotient.liftOn₂' x y fun x' y' => mk ⁅x', y'⁆
    intro x₁ x₂ y₁ y₂ h₁ h₂
    apply (Submodule.Quotient.eq I.toSubmodule).2
    rw [Submodule.quotientRel_r_def] at h₁ h₂
    have h : ⁅x₁, x₂⁆ - ⁅y₁, y₂⁆ = ⁅x₁, x₂ - y₂⁆ + ⁅x₁ - y₁, y₂⁆ := by
      simp [-lie_skew, sub_eq_add_neg, add_assoc]
    rw [h]
    apply Submodule.add_mem
    · apply lie_mem_right R L I x₁ (x₂ - y₂) h₂
    · apply lie_mem_left R L I (x₁ - y₁) y₂ h₁⟩
#align lie_submodule.quotient.lie_quotient_has_bracket LieSubmodule.Quotient.lieQuotientHasBracket

@[simp]
theorem mk_bracket (x y : L) : mk ⁅x, y⁆ = ⁅(mk x : L ⧸ I), (mk y : L ⧸ I)⁆ :=
  rfl
#align lie_submodule.quotient.mk_bracket LieSubmodule.Quotient.mk_bracket

instance lieQuotientLieRing : LieRing (L ⧸ I) where
  add_lie := by
    intro x' y' z'; refine Quotient.inductionOn₃' x' y' z' ?_; intro x y z
    repeat'
      first
      | rw [is_quotient_mk]
      | rw [← mk_bracket]
      | rw [← Submodule.Quotient.mk_add (R := R) (M := L)]
    apply congr_arg; apply add_lie
  lie_add := by
    intro x' y' z'; refine Quotient.inductionOn₃' x' y' z' ?_; intro x y z
    repeat'
      first
      | rw [is_quotient_mk]
      | rw [← mk_bracket]
      | rw [← Submodule.Quotient.mk_add (R := R) (M := L)]
    apply congr_arg; apply lie_add
  lie_self := by
    intro x'; refine Quotient.inductionOn' x' ?_; intro x
    rw [is_quotient_mk, ← mk_bracket]
    apply congr_arg; apply lie_self
  leibniz_lie := by
    intro x' y' z'; refine Quotient.inductionOn₃' x' y' z' ?_; intro x y z
    repeat'
      first
      | rw [is_quotient_mk]
      | rw [← mk_bracket]
      | rw [← Submodule.Quotient.mk_add (R := R) (M := L)]
    apply congr_arg; apply leibniz_lie
#align lie_submodule.quotient.lie_quotient_lie_ring LieSubmodule.Quotient.lieQuotientLieRing

instance lieQuotientLieAlgebra : LieAlgebra R (L ⧸ I) where
  lie_smul := by
    intro t x' y'; refine Quotient.inductionOn₂' x' y' ?_; intro x y
    repeat'
      first
      | rw [is_quotient_mk]
      | rw [← mk_bracket]
      | rw [← Submodule.Quotient.mk_smul (R := R) (M := L)]
    apply congr_arg; apply lie_smul
#align lie_submodule.quotient.lie_quotient_lie_algebra LieSubmodule.Quotient.lieQuotientLieAlgebra

/-- `LieSubmodule.Quotient.mk` as a `LieModuleHom`. -/
@[simps]
def mk' : M →ₗ⁅R,L⁆ M ⧸ N :=
  { N.toSubmodule.mkQ with
    toFun := mk
    map_lie' := fun {_ _} => rfl }
#align lie_submodule.quotient.mk' LieSubmodule.Quotient.mk'

@[simp]
theorem surjective_mk' : Function.Surjective (mk' N) := surjective_quot_mk _

@[simp]
theorem range_mk' : LieModuleHom.range (mk' N) = ⊤ := by simp [LieModuleHom.range_eq_top]

instance isNoetherian [IsNoetherian R M] : IsNoetherian R (M ⧸ N) :=
  Submodule.Quotient.isNoetherian (N : Submodule R M)

-- Porting note: LHS simplifies @[simp]
theorem mk_eq_zero {m : M} : mk' N m = 0 ↔ m ∈ N :=
  Submodule.Quotient.mk_eq_zero N.toSubmodule
#align lie_submodule.quotient.mk_eq_zero LieSubmodule.Quotient.mk_eq_zero

-- Porting note: added to replace `mk_eq_zero` as simp lemma.
@[simp]
theorem mk_eq_zero' {m : M} : mk (N := N) m = 0 ↔ m ∈ N :=
  Submodule.Quotient.mk_eq_zero N.toSubmodule

@[simp]
theorem mk'_ker : (mk' N).ker = N := by ext; simp
#align lie_submodule.quotient.mk'_ker LieSubmodule.Quotient.mk'_ker

@[simp]
theorem map_mk'_eq_bot_le : map (mk' N) N' = ⊥ ↔ N' ≤ N := by
  rw [← LieModuleHom.le_ker_iff_map, mk'_ker]
#align lie_submodule.quotient.map_mk'_eq_bot_le LieSubmodule.Quotient.map_mk'_eq_bot_le

/-- Two `LieModuleHom`s from a quotient lie module are equal if their compositions with
`LieSubmodule.Quotient.mk'` are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem lieModuleHom_ext ⦃f g : M ⧸ N →ₗ⁅R,L⁆ M⦄ (h : f.comp (mk' N) = g.comp (mk' N)) : f = g :=
  LieModuleHom.ext fun x => Quotient.inductionOn' x <| LieModuleHom.congr_fun h
#align lie_submodule.quotient.lie_module_hom_ext LieSubmodule.Quotient.lieModuleHom_ext

lemma toEndomorphism_comp_mk' (x : L) :
    LieModule.toEndomorphism R L (M ⧸ N) x ∘ₗ mk' N = mk' N ∘ₗ LieModule.toEndomorphism R L M x :=
  rfl

end Quotient

end LieSubmodule

namespace LieHom

variable {R L L' : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
variable (f : L →ₗ⁅R⁆ L')

/-- The first isomorphism theorem for morphisms of Lie algebras. -/
@[simps]
noncomputable def quotKerEquivRange : (L ⧸ f.ker) ≃ₗ⁅R⁆ f.range :=
  { (f : L →ₗ[R] L').quotKerEquivRange with
    toFun := (f : L →ₗ[R] L').quotKerEquivRange
    map_lie' := by
      rintro ⟨x⟩ ⟨y⟩
      rw [← SetLike.coe_eq_coe, LieSubalgebra.coe_bracket]
      simp only [Submodule.Quotient.quot_mk_eq_mk, LinearMap.quotKerEquivRange_apply_mk, ←
        LieSubmodule.Quotient.mk_bracket, coe_toLinearMap, map_lie] }
#align lie_hom.quot_ker_equiv_range LieHom.quotKerEquivRange

end LieHom
