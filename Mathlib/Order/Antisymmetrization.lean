/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Hom.Basic
import Mathbin.Logic.Relation

/-!
# Turning a preorder into a partial order

This file allows to make a preorder into a partial order by quotienting out the elements `a`, `b`
such that `a ≤ b` and `b ≤ a`.

`antisymmetrization` is a functor from `Preorder` to `PartialOrder`. See `Preorder_to_PartialOrder`.

## Main declarations

* `antisymm_rel`: The antisymmetrization relation. `antisymm_rel r a b` means that `a` and `b` are
  related both ways by `r`.
* `antisymmetrization α r`: The quotient of `α` by `antisymm_rel r`. Even when `r` is just a
  preorder, `antisymmetrization α` is a partial order.
-/


open Function OrderDual

variable {α β : Type _}

section Relation

variable (r : α → α → Prop)

/-- The antisymmetrization relation. -/
def AntisymmRel (a b : α) : Prop :=
  r a b ∧ r b a
#align antisymm_rel AntisymmRel

theorem antisymm_rel_swap : AntisymmRel (swap r) = AntisymmRel r :=
  funext fun _ => funext fun _ => propext and_comm
#align antisymm_rel_swap antisymm_rel_swap

@[refl]
theorem antisymm_rel_refl [IsRefl α r] (a : α) : AntisymmRel r a a :=
  ⟨refl _, refl _⟩
#align antisymm_rel_refl antisymm_rel_refl

variable {r}

@[symm]
theorem AntisymmRel.symm {a b : α} : AntisymmRel r a b → AntisymmRel r b a :=
  And.symm
#align antisymm_rel.symm AntisymmRel.symm

@[trans]
theorem AntisymmRel.trans [IsTrans α r] {a b c : α} (hab : AntisymmRel r a b)
    (hbc : AntisymmRel r b c) : AntisymmRel r a c :=
  ⟨trans hab.1 hbc.1, trans hbc.2 hab.2⟩
#align antisymm_rel.trans AntisymmRel.trans

instance AntisymmRel.decidableRel [DecidableRel r] : DecidableRel (AntisymmRel r) := fun _ _ =>
  And.decidable
#align antisymm_rel.decidable_rel AntisymmRel.decidableRel

@[simp]
theorem antisymm_rel_iff_eq [IsRefl α r] [IsAntisymm α r] {a b : α} : AntisymmRel r a b ↔ a = b :=
  antisymm_iff
#align antisymm_rel_iff_eq antisymm_rel_iff_eq

alias antisymm_rel_iff_eq ↔ AntisymmRel.eq _

end Relation

section IsPreorder

variable (α) (r : α → α → Prop) [IsPreorder α r]

/-- The antisymmetrization relation as an equivalence relation. -/
@[simps]
def AntisymmRel.setoid : Setoid α :=
  ⟨AntisymmRel r, antisymm_rel_refl _, fun _ _ => AntisymmRel.symm, fun _ _ _ => AntisymmRel.trans⟩
#align antisymm_rel.setoid AntisymmRel.setoid

/-- The partial order derived from a preorder by making pairwise comparable elements equal. This is
the quotient by `λ a b, a ≤ b ∧ b ≤ a`. -/
def Antisymmetrization : Type _ :=
  Quotient <| AntisymmRel.setoid α r
#align antisymmetrization Antisymmetrization

variable {α}

/-- Turn an element into its antisymmetrization. -/
def toAntisymmetrization : α → Antisymmetrization α r :=
  Quotient.mk'
#align to_antisymmetrization toAntisymmetrization

/-- Get a representative from the antisymmetrization. -/
noncomputable def ofAntisymmetrization : Antisymmetrization α r → α :=
  Quotient.out'
#align of_antisymmetrization ofAntisymmetrization

instance [Inhabited α] : Inhabited (Antisymmetrization α r) :=
  Quotient.inhabited _

@[elab_as_elim]
protected theorem Antisymmetrization.ind {p : Antisymmetrization α r → Prop} :
    (∀ a, p <| toAntisymmetrization r a) → ∀ q, p q :=
  Quot.ind
#align antisymmetrization.ind Antisymmetrization.ind

@[elab_as_elim]
protected theorem Antisymmetrization.induction_on {p : Antisymmetrization α r → Prop}
    (a : Antisymmetrization α r) (h : ∀ a, p <| toAntisymmetrization r a) : p a :=
  Quotient.inductionOn' a h
#align antisymmetrization.induction_on Antisymmetrization.induction_on

@[simp]
theorem to_antisymmetrization_of_antisymmetrization (a : Antisymmetrization α r) :
    toAntisymmetrization r (ofAntisymmetrization r a) = a :=
  Quotient.out_eq' _
#align to_antisymmetrization_of_antisymmetrization to_antisymmetrization_of_antisymmetrization

end IsPreorder

section Preorder

variable {α} [Preorder α] [Preorder β] {a b : α}

theorem AntisymmRel.image {a b : α} (h : AntisymmRel (· ≤ ·) a b) {f : α → β} (hf : Monotone f) :
    AntisymmRel (· ≤ ·) (f a) (f b) :=
  ⟨hf h.1, hf h.2⟩
#align antisymm_rel.image AntisymmRel.image

instance :
    PartialOrder
      (Antisymmetrization α
        (· ≤
          ·)) where
  le a b :=
    (Quotient.liftOn₂' a b (· ≤ ·)) fun (a₁ a₂ b₁ b₂ : α) h₁ h₂ =>
      propext ⟨fun h => h₁.2.trans <| h.trans h₂.1, fun h => h₁.1.trans <| h.trans h₂.2⟩
  lt a b :=
    (Quotient.liftOn₂' a b (· < ·)) fun (a₁ a₂ b₁ b₂ : α) h₁ h₂ =>
      propext ⟨fun h => h₁.2.trans_lt <| h.trans_le h₂.1, fun h => h₁.1.trans_lt <| h.trans_le h₂.2⟩
  le_refl a := Quotient.inductionOn' a <| le_refl
  le_trans a b c := (Quotient.inductionOn₃' a b c) fun a b c => le_trans
  lt_iff_le_not_le a b := (Quotient.inductionOn₂' a b) fun a b => lt_iff_le_not_le
  le_antisymm a b := (Quotient.inductionOn₂' a b) fun a b hab hba => Quotient.sound' ⟨hab, hba⟩

theorem antisymmetrization_fibration :
    Relation.Fibration (· < ·) (· < ·) (@toAntisymmetrization α (· ≤ ·) _) := by
  rintro a ⟨b⟩ h
  exact ⟨b, h, rfl⟩
#align antisymmetrization_fibration antisymmetrization_fibration

theorem acc_antisymmetrization_iff : Acc (· < ·) (toAntisymmetrization (· ≤ ·) a) ↔ Acc (· < ·) a :=
  ⟨fun h =>
    haveI := InvImage.accessible _ h
    this,
    Acc.of_fibration _ antisymmetrization_fibration⟩
#align acc_antisymmetrization_iff acc_antisymmetrization_iff

theorem well_founded_antisymmetrization_iff :
    WellFounded (@LT.lt (Antisymmetrization α (· ≤ ·)) _) ↔ WellFounded (@LT.lt α _) :=
  ⟨fun h => ⟨fun a => acc_antisymmetrization_iff.1 <| h.apply _⟩, fun h =>
    ⟨by
      rintro ⟨a⟩
      exact acc_antisymmetrization_iff.2 (h.apply a)⟩⟩
#align well_founded_antisymmetrization_iff well_founded_antisymmetrization_iff

instance [WellFoundedLt α] : WellFoundedLt (Antisymmetrization α (· ≤ ·)) :=
  ⟨well_founded_antisymmetrization_iff.2 IsWellFounded.wf⟩

instance [@DecidableRel α (· ≤ ·)] [@DecidableRel α (· < ·)] [IsTotal α (· ≤ ·)] :
    LinearOrder (Antisymmetrization α (· ≤ ·)) :=
  { Antisymmetrization.partialOrder with
    le_total := fun a b => Quotient.inductionOn₂' a b <| total_of (· ≤ ·),
    DecidableEq := @Quotient.decidableEq _ (AntisymmRel.setoid _ (· ≤ ·)) AntisymmRel.decidableRel,
    decidableLe := fun _ _ => Quotient.liftOn₂'.decidable _ _ _ _,
    decidableLt := fun _ _ => Quotient.liftOn₂'.decidable _ _ _ _ }

@[simp]
theorem to_antisymmetrization_le_to_antisymmetrization_iff :
    toAntisymmetrization (· ≤ ·) a ≤ toAntisymmetrization (· ≤ ·) b ↔ a ≤ b :=
  Iff.rfl
#align
  to_antisymmetrization_le_to_antisymmetrization_iff to_antisymmetrization_le_to_antisymmetrization_iff

@[simp]
theorem to_antisymmetrization_lt_to_antisymmetrization_iff :
    toAntisymmetrization (· ≤ ·) a < toAntisymmetrization (· ≤ ·) b ↔ a < b :=
  Iff.rfl
#align
  to_antisymmetrization_lt_to_antisymmetrization_iff to_antisymmetrization_lt_to_antisymmetrization_iff

@[simp]
theorem of_antisymmetrization_le_of_antisymmetrization_iff {a b : Antisymmetrization α (· ≤ ·)} :
    ofAntisymmetrization (· ≤ ·) a ≤ ofAntisymmetrization (· ≤ ·) b ↔ a ≤ b := by
  convert to_antisymmetrization_le_to_antisymmetrization_iff.symm <;>
    exact (to_antisymmetrization_of_antisymmetrization _ _).symm
#align
  of_antisymmetrization_le_of_antisymmetrization_iff of_antisymmetrization_le_of_antisymmetrization_iff

@[simp]
theorem of_antisymmetrization_lt_of_antisymmetrization_iff {a b : Antisymmetrization α (· ≤ ·)} :
    ofAntisymmetrization (· ≤ ·) a < ofAntisymmetrization (· ≤ ·) b ↔ a < b := by
  convert to_antisymmetrization_lt_to_antisymmetrization_iff.symm <;>
    exact (to_antisymmetrization_of_antisymmetrization _ _).symm
#align
  of_antisymmetrization_lt_of_antisymmetrization_iff of_antisymmetrization_lt_of_antisymmetrization_iff

@[mono]
theorem to_antisymmetrization_mono : Monotone (@toAntisymmetrization α (· ≤ ·) _) := fun a b => id
#align to_antisymmetrization_mono to_antisymmetrization_mono

/-- `to_antisymmetrization` as an order homomorphism. -/
@[simps]
def OrderHom.toAntisymmetrization : α →o Antisymmetrization α (· ≤ ·) :=
  ⟨toAntisymmetrization (· ≤ ·), fun a b => id⟩
#align order_hom.to_antisymmetrization OrderHom.toAntisymmetrization

private theorem lift_fun_antisymm_rel (f : α →o β) :
    ((AntisymmRel.setoid α (· ≤ ·)).R ⇒ (AntisymmRel.setoid β (· ≤ ·)).R) f f := fun a b h =>
  ⟨f.mono h.1, f.mono h.2⟩
#align lift_fun_antisymm_rel lift_fun_antisymm_rel

/-- Turns an order homomorphism from `α` to `β` into one from `antisymmetrization α` to
`antisymmetrization β`. `antisymmetrization` is actually a functor. See `Preorder_to_PartialOrder`.
-/
protected def OrderHom.antisymmetrization (f : α →o β) :
    Antisymmetrization α (· ≤ ·) →o Antisymmetrization β (· ≤ ·) :=
  ⟨Quotient.map' f <| lift_fun_antisymm_rel f, fun a b => Quotient.inductionOn₂' a b <| f.mono⟩
#align order_hom.antisymmetrization OrderHom.antisymmetrization

@[simp]
theorem OrderHom.coe_antisymmetrization (f : α →o β) :
    ⇑f.Antisymmetrization = Quotient.map' f (lift_fun_antisymm_rel f) :=
  rfl
#align order_hom.coe_antisymmetrization OrderHom.coe_antisymmetrization

@[simp]
theorem OrderHom.antisymmetrization_apply (f : α →o β) (a : Antisymmetrization α (· ≤ ·)) :
    f.Antisymmetrization a = Quotient.map' f (lift_fun_antisymm_rel f) a :=
  rfl
#align order_hom.antisymmetrization_apply OrderHom.antisymmetrization_apply

@[simp]
theorem OrderHom.antisymmetrization_apply_mk (f : α →o β) (a : α) :
    f.Antisymmetrization (toAntisymmetrization _ a) = toAntisymmetrization _ (f a) :=
  Quotient.map'_mk' f (lift_fun_antisymm_rel f) _
#align order_hom.antisymmetrization_apply_mk OrderHom.antisymmetrization_apply_mk

variable (α)

/-- `of_antisymmetrization` as an order embedding. -/
@[simps]
noncomputable def OrderEmbedding.ofAntisymmetrization :
    Antisymmetrization α (· ≤ ·) ↪o
      α where
  toFun := ofAntisymmetrization _
  inj' _ _ := Quotient.out_inj.1
  map_rel_iff' a b := of_antisymmetrization_le_of_antisymmetrization_iff
#align order_embedding.of_antisymmetrization OrderEmbedding.ofAntisymmetrization

/-- `antisymmetrization` and `order_dual` commute. -/
def OrderIso.dualAntisymmetrization :
    (Antisymmetrization α (· ≤ ·))ᵒᵈ ≃o
      Antisymmetrization αᵒᵈ
        (· ≤ ·) where
  toFun := (Quotient.map' id) fun _ _ => And.symm
  invFun := (Quotient.map' id) fun _ _ => And.symm
  left_inv a := (Quotient.inductionOn' a) fun a => by simp_rw [Quotient.map'_mk', id]
  right_inv a := (Quotient.inductionOn' a) fun a => by simp_rw [Quotient.map'_mk', id]
  map_rel_iff' a b := (Quotient.inductionOn₂' a b) fun a b => Iff.rfl
#align order_iso.dual_antisymmetrization OrderIso.dualAntisymmetrization

@[simp]
theorem OrderIso.dual_antisymmetrization_apply (a : α) :
    OrderIso.dualAntisymmetrization _ (to_dual <| toAntisymmetrization _ a) =
      toAntisymmetrization _ (toDual a) :=
  rfl
#align order_iso.dual_antisymmetrization_apply OrderIso.dual_antisymmetrization_apply

@[simp]
theorem OrderIso.dual_antisymmetrization_symm_apply (a : α) :
    (OrderIso.dualAntisymmetrization _).symm (toAntisymmetrization _ <| toDual a) =
      toDual (toAntisymmetrization _ a) :=
  rfl
#align order_iso.dual_antisymmetrization_symm_apply OrderIso.dual_antisymmetrization_symm_apply

end Preorder
