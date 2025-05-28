/-
Copyright (c) 2025 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Group.Semiconj.Units

/-!
# Units of monoid products.

Theorems, functions, homomorphisms and equivalences about the (additive)
unit of (additive) monoid products.
-/

variable {M : Type*} {N : Type*} [Monoid M] [Monoid N]

namespace Prod

@[to_additive]
lemma isUnit_iff {x : M × N} : IsUnit x ↔ IsUnit x.1 ∧ IsUnit x.2 := by
    simp_rw [isUnit_iff_exists, Prod.exists, Prod.mul_def,
      Prod.mk_eq_one, and_and_and_comm, exists_and_left, exists_and_right]

end Prod

namespace Units

/-- The first element of the units of the product of two monoids. -/
@[to_additive (attr := simps!) "The first element of the additive units of the
  product of two additive monoids."]
def fst : (M × N)ˣ →* Mˣ := map (.fst _ _)

/-- The second element of the units of the product of two monoids. -/
@[to_additive (attr := simps!) "The second element of the additive units of the
  product of two additive monoids."]
def snd : (M × N)ˣ →* Nˣ := map (.snd _ _)

/-- The inclusion homomorphism from the units of a monoid to the
  units of its product on the right with another. -/
@[to_additive (attr := simps!) "The inclusion homomorphism from the additive units of an additive
  monoid to the additive units of its product on the right with another."]
def inl : Mˣ →* (M × N)ˣ := map (.inl _ _)

/-- The inclusion homomorphism from the units of a monoid to the
  units of its product on the left with another. -/
@[to_additive (attr := simps!) "The inclusion homomorphism from the additive units of an additive
  monoid to the additive units of its product on the left with another."]
def inr : Nˣ →* (M × N)ˣ := map (.inr _ _)

@[to_additive (attr := simp)]
theorem fst_comp_inl : fst.comp (inl (N := N)) = MonoidHom.id Mˣ :=
  (Units.map_comp _ _).symm.trans (Eq.trans (congrArg _ MonoidHom.fst_comp_inl) (Units.map_id _))
@[to_additive (attr := simp)]
theorem snd_comp_inl : snd.comp inl = (1 : Mˣ →* Nˣ) := rfl
@[to_additive (attr := simp)]
theorem fst_comp_inr : fst.comp inr = (1 : Nˣ →* Mˣ) := rfl
@[to_additive (attr := simp)]
theorem snd_comp_inr : snd.comp (inr (M := M)) = MonoidHom.id Nˣ := rfl

@[to_additive (attr := simp)]
theorem fst_inl (u : Mˣ) : fst (inl (N := N) u) = u := rfl
@[to_additive (attr := simp)]
theorem snd_inl (u : Mˣ) : snd (inl (N := N) u) = 1 := rfl
@[to_additive (attr := simp)]
theorem fst_inr (u : Nˣ) : fst (inr (M := M) u) = 1 := rfl
@[to_additive (attr := simp)]
theorem snd_inr (u : Nˣ) : snd (inr (M := M) u) = u := rfl

@[to_additive]
theorem val_inl_mul_inr (u : Mˣ) (v : Nˣ) : (inl u * inr v).val = (u.val, v.val) := by
  simp_rw [val_mul, val_inl_apply, val_inr_apply, Prod.mk_mul_mk, mul_one, one_mul]

@[to_additive]
theorem val_inr_mul_inl (u : Mˣ) (v : Nˣ) : (inr v * inl u).val = (u.val, v.val) := by
  simp_rw [val_mul, val_inl_apply, val_inr_apply, Prod.mk_mul_mk, mul_one, one_mul]

@[to_additive]
theorem commute_inl_inr (m : Mˣ) (n : Nˣ) : Commute (inl m) (inr n) := by
  simp_rw [commute_iff_eq, Units.ext_iff, val_inl_mul_inr, val_inr_mul_inl]

/-- A map from the product of the units of two monoids to the units of their product. -/
@[to_additive prod "A map from the product of the additive units of two
    additive monoids to the additive units of their product."]
def prod : Mˣ × Nˣ →* (M × N)ˣ := ((coeHom _).prodMap (coeHom _)).toHomUnits

@[to_additive (attr := simp) val_prod_apply]
theorem val_prod_apply (g : Mˣ × Nˣ) : (prod g).val = (g.1.val, g.2.val) := rfl
@[to_additive (attr := simp) val_inv_prod_apply]
theorem val_inv_prod_apply (g : Mˣ × Nˣ) : (prod g)⁻¹.val = (g.1⁻¹.val, g.2⁻¹.val) := rfl

@[to_additive (attr := simp) fst_prod]
theorem fst_prod (g : Mˣ × Nˣ) : (prod g).fst = g.1 := rfl
@[to_additive (attr := simp) snd_prod]
theorem snd_prod (g : Mˣ × Nˣ) : (prod g).snd = g.2 := rfl

@[to_additive (attr := simp) prod_fst_snd]
theorem prod_fst_snd (g : (M × N)ˣ) : prod (fst g, snd g) = g := rfl

/-- The monoid equivalence between units of a product of two monoids, and the product of the
    units of each monoid. -/
@[to_additive prodAddEquiv
      "The additive monoid equivalence between additive units of a product
      of two additive monoids, and the product of the additive units of each additive monoid."]
def prodEquiv : (M × N)ˣ ≃* Mˣ × Nˣ := (fst.prod snd).toMulEquiv prod rfl rfl

@[to_additive (attr := simp) val_fst_prodEquiv_apply]
theorem val_fst_prodEquiv_apply (g : (M × N)ˣ) :
    (prodEquiv g).1.val = g.val.1 := rfl
@[to_additive (attr := simp) val_snd_prodEquiv_apply]
theorem val_snd_prodEquiv_apply (g : (M × N)ˣ) :
    (prodEquiv g).2.val = g.val.2 := rfl
@[to_additive (attr := simp) val_prodEquiv_symm_apply]
theorem val_prodEquiv_symm_apply (g : Mˣ × Nˣ) :
    (prodEquiv.symm g).val = (g.1.val, g.2.val) := rfl
@[to_additive (attr := simp) val_inv_prodEquiv_symm_apply]
theorem val_inv_prodEquiv_symm_apply (g : Mˣ × Nˣ) :
    (prodEquiv.symm g)⁻¹.val = (g.1⁻¹.val, g.2⁻¹.val) := rfl

@[deprecated (since := "2025-05-22")]
alias _root_.MulEquiv.prodEquiv := Units.prodEquiv

@[deprecated (since := "2025-05-22")]
alias _root_.MulEquiv.prodAddUnits := AddUnits.prodAddEquiv

@[to_additive (attr := simp) toMonoidHom_prodEquiv_eq_fst_prod_snd]
theorem toMonoidHom_prodEquiv_eq_fst_prod_snd :
    (prodEquiv (M := M) (N := N)).toMonoidHom = fst.prod snd := rfl

@[to_additive (attr := simp) toMonoidHom_prodEquiv_symm_eq_prod]
theorem toMonoidHom_prodEquiv_symm_eq_prod :
    (prodEquiv (M := M) (N := N)).symm.toMonoidHom = prod := rfl

section

open MulOpposite

/-- Canonical homomorphism of monoids from `αˣ` into `α × αᵐᵒᵖ`.
Used mainly to define the natural topology of `αˣ`. -/
@[to_additive (attr := simps)
      "Canonical homomorphism of additive monoids from `AddUnits α` into `α × αᵃᵒᵖ`.
      Used mainly to define the natural topology of `AddUnits α`."]
def embedProduct (α : Type*) [Monoid α] : αˣ →* α × αᵐᵒᵖ where
  toFun x := ⟨x, op ↑x⁻¹⟩
  map_one' := by
    simp_rw [inv_one, Units.val_one, op_one, Prod.mk_eq_one, and_true]
  map_mul' x y := by simp_rw [mul_inv_rev, Units.val_mul, op_mul, Prod.mk_mul_mk]

@[to_additive]
theorem embedProduct_injective (α : Type*) [Monoid α] : Function.Injective (embedProduct α) :=
  fun _ _ h => Units.ext <| (congr_arg Prod.fst h :)

end

end Units

@[to_additive AddSemiconjBy.prod_units]
theorem SemiconjBy.prod_units {x y z : (M × N)ˣ}
    (hm : SemiconjBy x.fst y.fst z.fst) (hn : SemiconjBy x.snd y.snd z.snd) : SemiconjBy x y z :=
  (SemiconjBy.prod hm.units_val hn.units_val).units_of_val

@[to_additive]
theorem Prod.semiconjBy_units_iff {x y z : (M × N)ˣ} :
    SemiconjBy x y z ↔ SemiconjBy x.fst y.fst z.fst ∧ SemiconjBy x.snd y.snd z.snd := by
  simp_rw [SemiconjBy.units_val_iff, semiconjBy_iff, Units.val_fst_apply, Units.val_snd_apply]

@[to_additive AddCommute.prod_units]
theorem Commute.prod_units {x y : (M × N)ˣ} (hm : Commute x.fst y.fst) (hn : Commute x.snd y.snd) :
    Commute x y := SemiconjBy.prod_units hm hn

@[to_additive]
theorem Prod.commute_units_iff {x y : (M × N)ˣ} :
    Commute x y ↔ Commute x.fst y.fst ∧ Commute x.snd y.snd := semiconjBy_units_iff
