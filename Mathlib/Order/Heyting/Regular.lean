/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.GaloisConnection.Basic

/-!
# Heyting regular elements

This file defines Heyting regular elements, elements of a Heyting algebra that are their own double
complement, and proves that they form a boolean algebra.

From a logic standpoint, this means that we can perform classical logic within intuitionistic logic
by simply double-negating all propositions. This is practical for synthetic computability theory.

## Main declarations

* `IsRegular`: `a` is Heyting-regular if `aᶜᶜ = a`.
* `Regular`: The subtype of Heyting-regular elements.
* `Regular.BooleanAlgebra`: Heyting-regular elements form a boolean algebra.

## References

* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]
-/


open Function

variable {α : Type*}

namespace Heyting

section HasCompl

variable [HasCompl α] {a : α}

/-- An element of a Heyting algebra is regular if its double complement is itself. -/
def IsRegular (a : α) : Prop :=
  aᶜᶜ = a

protected theorem IsRegular.eq : IsRegular a → aᶜᶜ = a :=
  id

instance IsRegular.decidablePred [DecidableEq α] : @DecidablePred α IsRegular := fun _ =>
  ‹DecidableEq α› _ _

end HasCompl

section HeytingAlgebra

variable [HeytingAlgebra α] {a b : α}

theorem isRegular_bot : IsRegular (⊥ : α) := by rw [IsRegular, compl_bot, compl_top]

theorem isRegular_top : IsRegular (⊤ : α) := by rw [IsRegular, compl_top, compl_bot]

theorem IsRegular.inf (ha : IsRegular a) (hb : IsRegular b) : IsRegular (a ⊓ b) := by
  rw [IsRegular, compl_compl_inf_distrib, ha.eq, hb.eq]

theorem IsRegular.himp (ha : IsRegular a) (hb : IsRegular b) : IsRegular (a ⇨ b) := by
  rw [IsRegular, compl_compl_himp_distrib, ha.eq, hb.eq]

theorem isRegular_compl (a : α) : IsRegular aᶜ :=
  compl_compl_compl _

protected theorem IsRegular.disjoint_compl_left_iff (ha : IsRegular a) :
    Disjoint aᶜ b ↔ b ≤ a := by rw [← le_compl_iff_disjoint_left, ha.eq]

protected theorem IsRegular.disjoint_compl_right_iff (hb : IsRegular b) :
    Disjoint a bᶜ ↔ a ≤ b := by rw [← le_compl_iff_disjoint_right, hb.eq]

-- See note [reducible non-instances]
/-- A Heyting algebra with regular excluded middle is a boolean algebra. -/
abbrev _root_.BooleanAlgebra.ofRegular (h : ∀ a : α, IsRegular (a ⊔ aᶜ)) : BooleanAlgebra α :=
  have : ∀ a : α, IsCompl a aᶜ := fun a =>
    ⟨disjoint_compl_right,
      codisjoint_iff.2 <| by rw [← (h a), compl_sup, inf_compl_eq_bot, compl_bot]⟩
  { ‹HeytingAlgebra α›,
    GeneralizedHeytingAlgebra.toDistribLattice with
    himp_eq := fun _ _ =>
      eq_of_forall_le_iff fun _ => le_himp_iff.trans (this _).le_sup_right_iff_inf_left_le.symm
    inf_compl_le_bot := fun _ => (this _).1.le_bot
    top_le_sup_compl := fun _ => (this _).2.top_le }

variable (α)

/-- The boolean algebra of Heyting regular elements. -/
def Regular : Type _ :=
  { a : α // IsRegular a }

variable {α}

namespace Regular

/-- The coercion `Regular α → α` -/
@[coe] def val : Regular α → α :=
  Subtype.val

theorem prop : ∀ a : Regular α, IsRegular a.val := Subtype.prop

instance : CoeOut (Regular α) α := ⟨Regular.val⟩

theorem coe_injective : Injective ((↑) : Regular α → α) :=
  Subtype.coe_injective

@[simp]
theorem coe_inj {a b : Regular α} : (a : α) = b ↔ a = b :=
  Subtype.coe_inj

instance top : Top (Regular α) :=
  ⟨⟨⊤, isRegular_top⟩⟩

instance bot : Bot (Regular α) :=
  ⟨⟨⊥, isRegular_bot⟩⟩

instance inf : Min (Regular α) :=
  ⟨fun a b => ⟨a ⊓ b, a.2.inf b.2⟩⟩

instance himp : HImp (Regular α) :=
  ⟨fun a b => ⟨a ⇨ b, a.2.himp b.2⟩⟩

instance hasCompl : HasCompl (Regular α) :=
  ⟨fun a => ⟨aᶜ, isRegular_compl _⟩⟩

@[simp, norm_cast]
theorem coe_top : ((⊤ : Regular α) : α) = ⊤ :=
  rfl

@[simp, norm_cast]
theorem coe_bot : ((⊥ : Regular α) : α) = ⊥ :=
  rfl

@[simp, norm_cast]
theorem coe_inf (a b : Regular α) : (↑(a ⊓ b) : α) = (a : α) ⊓ b :=
  rfl

@[simp, norm_cast]
theorem coe_himp (a b : Regular α) : (↑(a ⇨ b) : α) = (a : α) ⇨ b :=
  rfl

@[simp, norm_cast]
theorem coe_compl (a : Regular α) : (↑aᶜ : α) = (a : α)ᶜ :=
  rfl

instance : Inhabited (Regular α) :=
  ⟨⊥⟩

instance : SemilatticeInf (Regular α) :=
  coe_injective.semilatticeInf _ coe_inf

instance boundedOrder : BoundedOrder (Regular α) :=
  BoundedOrder.lift ((↑) : Regular α → α) (fun _ _ => id) coe_top coe_bot

@[simp, norm_cast]
theorem coe_le_coe {a b : Regular α} : (a : α) ≤ b ↔ a ≤ b :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_lt_coe {a b : Regular α} : (a : α) < b ↔ a < b :=
  Iff.rfl

/-- **Regularization** of `a`. The smallest regular element greater than `a`. -/
def toRegular : α →o Regular α :=
  ⟨fun a => ⟨aᶜᶜ, isRegular_compl _⟩, fun _ _ h =>
    coe_le_coe.1 <| compl_le_compl <| compl_le_compl h⟩

@[simp, norm_cast]
theorem coe_toRegular (a : α) : (toRegular a : α) = aᶜᶜ :=
  rfl

@[simp]
theorem toRegular_coe (a : Regular α) : toRegular (a : α) = a :=
  coe_injective a.2

/-- The Galois insertion between `Regular.toRegular` and `coe`. -/
def gi : GaloisInsertion toRegular ((↑) : Regular α → α) where
  choice a ha := ⟨a, ha.antisymm le_compl_compl⟩
  gc _ b :=
    coe_le_coe.symm.trans <|
      ⟨le_compl_compl.trans, fun h => (compl_anti <| compl_anti h).trans_eq b.2⟩
  le_l_u _ := le_compl_compl
  choice_eq _ ha := coe_injective <| le_compl_compl.antisymm ha

instance lattice : Lattice (Regular α) :=
  gi.liftLattice

@[simp, norm_cast]
theorem coe_sup (a b : Regular α) : (↑(a ⊔ b) : α) = ((a : α) ⊔ b)ᶜᶜ :=
  rfl

instance : BooleanAlgebra (Regular α) :=
  { Regular.lattice, Regular.boundedOrder, Regular.himp,
    Regular.hasCompl with
    le_sup_inf := fun a b c =>
      coe_le_coe.1 <| by
        dsimp
        rw [sup_inf_left, compl_compl_inf_distrib]
    inf_compl_le_bot := fun _ => coe_le_coe.1 <| disjoint_iff_inf_le.1 disjoint_compl_right
    top_le_sup_compl := fun a =>
      coe_le_coe.1 <| by
        dsimp
        rw [compl_sup, inf_compl_eq_bot, compl_bot]
    himp_eq := fun a b =>
      coe_injective
        (by
          dsimp
          rw [compl_sup, a.prop.eq]
          refine eq_of_forall_le_iff fun c => le_himp_iff.trans ?_
          rw [le_compl_iff_disjoint_right, disjoint_left_comm]
          rw [b.prop.disjoint_compl_left_iff]) }

@[simp, norm_cast]
theorem coe_sdiff (a b : Regular α) : (↑(a \ b) : α) = (a : α) ⊓ bᶜ :=
  rfl

end Regular

end HeytingAlgebra

variable [BooleanAlgebra α]

theorem isRegular_of_boolean : ∀ a : α, IsRegular a :=
  compl_compl

/-- A decidable proposition is intuitionistically Heyting-regular. -/
theorem isRegular_of_decidable (p : Prop) [Decidable p] : IsRegular p :=
  propext <| Decidable.not_not

end Heyting
