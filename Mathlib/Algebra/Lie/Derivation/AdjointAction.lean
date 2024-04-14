/-
Copyright © 2024 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Adjoint action of a Lie algebra on itself

This file defines the *adjoint action* of a Lie algebra on itself, and establishes basic properties.

## Main definitions

- `LieDerivation.ad`: The adjoint action of a Lie algebra `L` on itself, seen as a morphism of Lie
algebras from `L` to the Lie algebra of its derivations. The adjoint action is also defined in the
`Mathlib.Algebra.Lie.OfAssociative.lean` file, under the name `LieAlgebra.ad`, as the morphism with
values in the endormophisms of `L`.

## Main statements

- `LieDerivation.ad_eq_ad`: when seen as endomorphisms, both definitions coincide,
- `LieDerivation.ad_ker_eq_center`: the kernel of the adjoint action is the center of `L`,
- `LieDerivation.lie_der_ad_eq_ad_der`: the commutator of a derivation `D` and `ad(x)` is `ad(D x)`,
- `LieDerivation.imageAd`: the image of the adjoint action is an ideal of the derivations.
-/

namespace LieDerivation

section AdjointAction

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The adjoint action of a Lie algebra `L` on itself, seen as a morphism of Lie algebras from
`L` to its derivations.
Note the minus sign: this is chosen to so that `ad(⁅x, y⁆) = ⁅ad(x), ad(y)⁆)`. -/
def ad : L →ₗ⁅R⁆ LieDerivation R L L :=
  { __ := - inner R L L
    map_lie' := by
      intro x y
      ext z
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.neg_apply, coe_neg,
        Pi.neg_apply, inner_apply_apply, commutator_apply]
      rw [leibniz_lie, neg_lie, neg_lie, ← lie_skew x]
      abel }

variable {R L}

lemma ad_zero : ad R L 0 = 0 := LieHom.map_zero (ad R L)

@[simp]
lemma ad_apply (x y : L) : ad R L x y = ⁅x, y⁆ := by
  rw [ad, LieHom.coe_mk, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.neg_apply, coe_neg,
    Pi.neg_apply, inner_apply_apply, lie_skew]

lemma ad_lie (x y z : L) : ad R L x ⁅y, z⁆ = ⁅y, ad R L x z⁆ + ⁅ad R L x y, z⁆ := by
  rw [apply_lie_eq_add]

/-- For every `x` in the Lie algebra `L`, the derivation `ad(x)` defined in this file, is equal,
when seen as an endomorphism of `L`, to the one defined in `LieAlgebra.ad`. -/
@[simp]
lemma ad_eq_ad (x : L) : ad R L x = LieAlgebra.ad R L x := by
  ext y
  rw [coeFn_coe, ad_apply, LieAlgebra.ad_apply]

/-- The kernel of the adjoint action on a Lie algebra is equal to the kernel of its action on
itself. -/
lemma ad_ker_eq_self_module_ker : (ad R L).ker = LieModule.ker R L L := by
  ext x
  rw [LieHom.mem_ker, LieModule.mem_ker, DFunLike.ext_iff]
  simp_rw [ad_apply, zero_apply]

/-- The kernel of the adjoint action on a Lie algebra is equal to its center. -/
lemma ad_ker_eq_center : (ad R L).ker = LieAlgebra.center R L := by
  ext x
  rw [ad_ker_eq_self_module_ker, LieAlgebra.self_module_ker_eq_center]

/-- The commutator of a derivation `D` and a derivation of the form `ad(x)` is `ad(D x)`. -/
lemma lie_der_ad_eq_ad_der (D : LieDerivation R L L) (x : L) : ⁅D, ad R L x⁆ = ad R L (D x) := by
  ext a
  rw [commutator_apply, ad_apply, ad_apply, ad_apply, apply_lie_eq_add, add_sub_cancel_left]

variable (R L) in
/-- The image of the adjoint action homomorphism from a Lie algebra `L` to the Lie algebra of its
derivations is an ideal of the latter. -/
def imageAd : LieIdeal R (LieDerivation R L L) where
  __ := Submodule.map (ad R L).toLinearMap (⊤ : Submodule R L)
  carrier := Submodule.map (ad R L).toLinearMap (⊤ : Submodule R L)
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' := SMulMemClass.smul_mem
  lie_mem := by
    intro D Dx hDx
    obtain ⟨x, hx⟩ := Set.mem_range_of_mem_image (ad R L) Set.univ hDx
    rw [← hx, lie_der_ad_eq_ad_der D x]
    exact Set.mem_image_of_mem (ad R L) trivial

/-- For every `x` in the Lie algebra `L`, `ad(x)` is in the image of the adjoint action. -/
lemma ad_mem_imageAd (x : L) : ad R L x ∈ imageAd R L := Exists.intro x ⟨trivial, rfl⟩

/-- A derivation `D` belongs to the image of the adjoint action iff it is of the form `ad(x)` for
some `x` in the Lie algebra `L`. -/
lemma mem_imageAd_iff {D : LieDerivation R L L} : D ∈ imageAd R L ↔ ∃ x : L, D = ad R L x := by
  constructor
  · intro ⟨y, _⟩; use y; tauto
  · intro ⟨x, hx⟩; rw [hx]; exact ad_mem_imageAd x

end AdjointAction

end LieDerivation
