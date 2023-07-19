/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir, Yury Kudryashov
-/
import Mathlib.Order.Filter.Ultrafilter
import Mathlib.Order.Filter.Germ

#align_import order.filter.filter_product from "leanprover-community/mathlib"@"2738d2ca56cbc63be80c3bd48e9ed90ad94e947d"

/-!
# Ultraproducts

If `φ` is an ultrafilter, then the space of germs of functions `f : α → β` at `φ` is called
the *ultraproduct*. In this file we prove properties of ultraproducts that rely on `φ` being an
ultrafilter. Definitions and properties that work for any filter should go to `Order.Filter.Germ`.

## Tags

ultrafilter, ultraproduct
-/


universe u v

variable {α : Type u} {β : Type v} {φ : Ultrafilter α}

open Classical

namespace Filter

local notation3 "∀* "(...)", "r:(scoped p => Filter.Eventually p (Ultrafilter.toFilter φ)) => r

namespace Germ

open Ultrafilter

local notation "β*" => Germ (φ : Filter α) β

instance divisionSemiring [DivisionSemiring β] : DivisionSemiring β* :=
  { Germ.semiring, Germ.divInvMonoid,
    Germ.nontrivial with
    mul_inv_cancel := fun f =>
      inductionOn f fun f hf =>
        coe_eq.2 <|
          (φ.em fun y => f y = 0).elim (fun H => (hf <| coe_eq.2 H).elim) fun H =>
            H.mono fun x => mul_inv_cancel
    inv_zero := coe_eq.2 <| by
       simp only [Function.comp, inv_zero]
       exact EventuallyEq.refl _ fun _ => 0}

instance divisionRing [DivisionRing β] : DivisionRing β* :=
  { Germ.ring, Germ.divisionSemiring with }

instance semifield [Semifield β] : Semifield β* :=
  { Germ.commSemiring, Germ.divisionSemiring with }

instance field [Field β] : Field β* :=
  { Germ.commRing, Germ.divisionRing with }

theorem coe_lt [Preorder β] {f g : α → β} : (f : β*) < g ↔ ∀* x, f x < g x := by
  simp only [lt_iff_le_not_le, eventually_and, coe_le, eventually_not, EventuallyLE]
#align filter.germ.coe_lt Filter.Germ.coe_lt

theorem coe_pos [Preorder β] [Zero β] {f : α → β} : 0 < (f : β*) ↔ ∀* x, 0 < f x :=
  coe_lt
#align filter.germ.coe_pos Filter.Germ.coe_pos

theorem const_lt [Preorder β] {x y : β} : x < y → (↑x : β*) < ↑y :=
  coe_lt.mpr ∘ liftRel_const
#align filter.germ.const_lt Filter.Germ.const_lt

@[simp, norm_cast]
theorem const_lt_iff [Preorder β] {x y : β} : (↑x : β*) < ↑y ↔ x < y :=
  coe_lt.trans liftRel_const_iff
#align filter.germ.const_lt_iff Filter.Germ.const_lt_iff

theorem lt_def [Preorder β] : ((· < ·) : β* → β* → Prop) = LiftRel (· < ·) := by
  ext ⟨f⟩ ⟨g⟩
  exact coe_lt
#align filter.germ.lt_def Filter.Germ.lt_def

instance sup [Sup β] : Sup β* :=
  ⟨map₂ (· ⊔ ·)⟩

instance inf [Inf β] : Inf β* :=
  ⟨map₂ (· ⊓ ·)⟩

@[simp, norm_cast]
theorem const_sup [Sup β] (a b : β) : ↑(a ⊔ b) = (↑a ⊔ ↑b : β*) :=
  rfl
#align filter.germ.const_sup Filter.Germ.const_sup

@[simp, norm_cast]
theorem const_inf [Inf β] (a b : β) : ↑(a ⊓ b) = (↑a ⊓ ↑b : β*) :=
  rfl
#align filter.germ.const_inf Filter.Germ.const_inf

instance semilatticeSup [SemilatticeSup β] : SemilatticeSup β* :=
  { Germ.partialOrder with
    sup := (· ⊔ ·)
    le_sup_left := fun f g =>
        inductionOn₂ f g fun _f _g => eventually_of_forall fun _x => le_sup_left
    le_sup_right := fun f g =>
      inductionOn₂ f g fun _f _g => eventually_of_forall fun _x => le_sup_right
    sup_le := fun f₁ f₂ g =>
      inductionOn₃ f₁ f₂ g fun _f₁ _f₂ _g h₁ h₂ => h₂.mp <| h₁.mono fun _x => sup_le }

instance semilatticeInf [SemilatticeInf β] : SemilatticeInf β* :=
  { Germ.partialOrder with
    inf := (· ⊓ ·)
    inf_le_left := fun f g =>
        inductionOn₂ f g fun _f _g => eventually_of_forall fun _x => inf_le_left
    inf_le_right := fun f g =>
      inductionOn₂ f g fun _f _g => eventually_of_forall fun _x => inf_le_right
    le_inf := fun f₁ f₂ g =>
      inductionOn₃ f₁ f₂ g fun _f₁ _f₂ _g h₁ h₂ => h₂.mp <| h₁.mono fun _x => le_inf }

instance lattice [Lattice β] : Lattice β* :=
  { Germ.semilatticeSup, Germ.semilatticeInf with }

instance distribLattice [DistribLattice β] : DistribLattice β* :=
  { Germ.semilatticeSup, Germ.semilatticeInf with
    le_sup_inf := fun f g h =>
      inductionOn₃ f g h fun _f _g _h => eventually_of_forall fun _ => le_sup_inf }

instance isTotal [LE β] [IsTotal β (· ≤ ·)] : IsTotal β* (· ≤ ·) :=
  ⟨fun f g =>
    inductionOn₂ f g fun _f _g => eventually_or.1 <| eventually_of_forall fun _x => total_of _ _ _⟩

/-- If `φ` is an ultrafilter then the ultraproduct is a linear order. -/
noncomputable instance linearOrder [LinearOrder β] : LinearOrder β* :=
  Lattice.toLinearOrder _

@[to_additive]
instance orderedCommMonoid [OrderedCommMonoid β] : OrderedCommMonoid β* :=
  { Germ.partialOrder, Germ.commMonoid with
    mul_le_mul_left := fun f g =>
      inductionOn₂ f g fun _f _g H h =>
        inductionOn h fun _h => H.mono fun _x H => mul_le_mul_left' H _ }

@[to_additive]
instance orderedCancelCommMonoid [OrderedCancelCommMonoid β]  :
    OrderedCancelCommMonoid β* :=
  { Germ.orderedCommMonoid with
    le_of_mul_le_mul_left := fun f g h =>
      inductionOn₃ f g h fun _f _g _h H => H.mono fun _x => le_of_mul_le_mul_left' }

@[to_additive]
instance orderedCommGroup [OrderedCommGroup β] : OrderedCommGroup β* :=
  { Germ.orderedCancelCommMonoid, Germ.commGroup with }

@[to_additive]
noncomputable instance linearOrderedCommGroup [LinearOrderedCommGroup β] :
    LinearOrderedCommGroup β* :=
  { Germ.orderedCommGroup, Germ.linearOrder with }

instance orderedSemiring [OrderedSemiring β] : OrderedSemiring β* :=
  { Germ.semiring,
    Germ.orderedAddCommMonoid with
    zero_le_one := const_le zero_le_one
    mul_le_mul_of_nonneg_left := fun x y z =>
      inductionOn₃ x y z fun _f _g _h hfg hh =>
          hh.mp <| hfg.mono fun _a => mul_le_mul_of_nonneg_left
    mul_le_mul_of_nonneg_right := fun x y z =>
      inductionOn₃ x y z fun _f _g _h hfg hh =>
          hh.mp <| hfg.mono fun _a => mul_le_mul_of_nonneg_right }

instance orderedCommSemiring [OrderedCommSemiring β] : OrderedCommSemiring β* :=
  { Germ.orderedSemiring, Germ.commSemiring with }

instance orderedRing [OrderedRing β] : OrderedRing β* :=
  { Germ.ring,
    Germ.orderedAddCommGroup with
    zero_le_one := const_le zero_le_one
    mul_nonneg := fun x y =>
      inductionOn₂ x y fun _f _g hf hg => hg.mp <| hf.mono fun _a => mul_nonneg }

instance orderedCommRing [OrderedCommRing β] : OrderedCommRing β* :=
  { Germ.orderedRing, Germ.orderedCommSemiring with }

instance strictOrderedSemiring [StrictOrderedSemiring β] : StrictOrderedSemiring β* :=
  { Germ.orderedSemiring, Germ.orderedAddCancelCommMonoid,
    Germ.nontrivial with
    mul_lt_mul_of_pos_left := fun x y z =>
      inductionOn₃ x y z fun _f _g _h hfg hh =>
        coe_lt.2 <| (coe_lt.1 hh).mp <| (coe_lt.1 hfg).mono fun _a => mul_lt_mul_of_pos_left
    mul_lt_mul_of_pos_right := fun x y z =>
      inductionOn₃ x y z fun _f _g _h hfg hh =>
        coe_lt.2 <| (coe_lt.1 hh).mp <| (coe_lt.1 hfg).mono fun _a => mul_lt_mul_of_pos_right }

instance strictOrderedCommSemiring [StrictOrderedCommSemiring β] : StrictOrderedCommSemiring β* :=
  { Germ.strictOrderedSemiring, Germ.orderedCommSemiring with }

instance strictOrderedRing [StrictOrderedRing β] : StrictOrderedRing β* :=
  { Germ.ring,
    Germ.strictOrderedSemiring with
    zero_le_one := const_le zero_le_one
    mul_pos := fun x y =>
      inductionOn₂ x y fun _f _g hf hg =>
        coe_pos.2 <| (coe_pos.1 hg).mp <| (coe_pos.1 hf).mono fun _x => mul_pos }

instance strictOrderedCommRing [StrictOrderedCommRing β] : StrictOrderedCommRing β* :=
  { Germ.strictOrderedRing, Germ.orderedCommRing with }

noncomputable instance linearOrderedRing [LinearOrderedRing β] : LinearOrderedRing β* :=
  { Germ.strictOrderedRing, Germ.linearOrder with }

noncomputable instance linearOrderedField [LinearOrderedField β] : LinearOrderedField β* :=
  { Germ.linearOrderedRing, Germ.field with }

noncomputable instance linearOrderedCommRing [LinearOrderedCommRing β] : LinearOrderedCommRing β* :=
  { Germ.linearOrderedRing, Germ.commMonoid with }

theorem max_def [LinearOrder β] (x y : β*) : max x y = map₂ max x y :=
  inductionOn₂ x y fun a b => by
    cases' le_total (a : β*) b with h h
    · rw [max_eq_right h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (max_eq_right hi).symm
    · rw [max_eq_left h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (max_eq_left hi).symm
#align filter.germ.max_def Filter.Germ.max_def

theorem min_def [K : LinearOrder β] (x y : β*) : min x y = map₂ min x y :=
  inductionOn₂ x y fun a b => by
    cases' le_total (a : β*) b with h h
    · rw [min_eq_left h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (min_eq_left hi).symm
    · rw [min_eq_right h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (min_eq_right hi).symm
#align filter.germ.min_def Filter.Germ.min_def

theorem abs_def [LinearOrderedAddCommGroup β] (x : β*) : |x| = map abs x :=
  inductionOn x fun _a => rfl
#align filter.germ.abs_def Filter.Germ.abs_def

@[simp]
theorem const_max [LinearOrder β] (x y : β) : (↑(max x y : β) : β*) = max ↑x ↑y := by
  rw [max_def, map₂_const]
#align filter.germ.const_max Filter.Germ.const_max

@[simp]
theorem const_min [LinearOrder β] (x y : β) : (↑(min x y : β) : β*) = min ↑x ↑y := by
  rw [min_def, map₂_const]
#align filter.germ.const_min Filter.Germ.const_min

@[simp]
theorem const_abs [LinearOrderedAddCommGroup β] (x : β) : (↑|x| : β*) = |↑x| := by
  rw [abs_def, map_const]
#align filter.germ.const_abs Filter.Germ.const_abs

end Germ

end Filter
