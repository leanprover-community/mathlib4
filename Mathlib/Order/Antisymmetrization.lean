/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Hom.Basic
import Mathlib.Logic.Relation

/-!
# Turning a preorder into a partial order

This file allows to make a preorder into a partial order by quotienting out the elements `a`, `b`
such that `a ≤ b` and `b ≤ a`.

`Antisymmetrization` is a functor from `Preorder` to `PartialOrder`. See `Preorder_to_PartialOrder`.

## Main declarations

* `AntisymmRel`: The antisymmetrization relation. `AntisymmRel r a b` means that `a` and `b` are
  related both ways by `r`.
* `Antisymmetrization α r`: The quotient of `α` by `AntisymmRel r`. Even when `r` is just a
  preorder, `Antisymmetrization α` is a partial order.
-/

/- Porting note: There are many changes from `toAntisymmetrization (· ≤ ·)` to
`@toAntisymmetrization α (· ≤ ·) _` -/

open Function OrderDual

variable {α β : Type*}

section Relation

variable (r : α → α → Prop)

/-- The antisymmetrization relation. -/
def AntisymmRel (a b : α) : Prop :=
  r a b ∧ r b a

theorem antisymmRel_swap : AntisymmRel (swap r) = AntisymmRel r :=
  funext fun _ => funext fun _ => propext and_comm

@[refl]
theorem antisymmRel_refl [IsRefl α r] (a : α) : AntisymmRel r a a :=
  ⟨refl _, refl _⟩

variable {r}

@[symm]
theorem AntisymmRel.symm {a b : α} : AntisymmRel r a b → AntisymmRel r b a :=
  And.symm

@[trans]
theorem AntisymmRel.trans [IsTrans α r] {a b c : α} (hab : AntisymmRel r a b)
    (hbc : AntisymmRel r b c) : AntisymmRel r a c :=
  ⟨_root_.trans hab.1 hbc.1, _root_.trans hbc.2 hab.2⟩

instance AntisymmRel.decidableRel [DecidableRel r] : DecidableRel (AntisymmRel r) := fun _ _ =>
  instDecidableAnd

@[simp]
theorem antisymmRel_iff_eq [IsRefl α r] [IsAntisymm α r] {a b : α} : AntisymmRel r a b ↔ a = b :=
  antisymm_iff

alias ⟨AntisymmRel.eq, _⟩ := antisymmRel_iff_eq

end Relation

section IsPreorder

variable (α) (r : α → α → Prop) [IsPreorder α r]

/-- The antisymmetrization relation as an equivalence relation. -/
@[simps]
def AntisymmRel.setoid : Setoid α :=
  ⟨AntisymmRel r, antisymmRel_refl _, AntisymmRel.symm, AntisymmRel.trans⟩

/-- The partial order derived from a preorder by making pairwise comparable elements equal. This is
the quotient by `fun a b => a ≤ b ∧ b ≤ a`. -/
def Antisymmetrization : Type _ :=
  Quotient <| AntisymmRel.setoid α r

variable {α}

/-- Turn an element into its antisymmetrization. -/
def toAntisymmetrization : α → Antisymmetrization α r :=
  Quotient.mk _

/-- Get a representative from the antisymmetrization. -/
noncomputable def ofAntisymmetrization : Antisymmetrization α r → α :=
  Quotient.out'

instance [Inhabited α] : Inhabited (Antisymmetrization α r) := by
  unfold Antisymmetrization; infer_instance

@[elab_as_elim]
protected theorem Antisymmetrization.ind {p : Antisymmetrization α r → Prop} :
    (∀ a, p <| toAntisymmetrization r a) → ∀ q, p q :=
  Quot.ind

@[elab_as_elim]
protected theorem Antisymmetrization.induction_on {p : Antisymmetrization α r → Prop}
    (a : Antisymmetrization α r) (h : ∀ a, p <| toAntisymmetrization r a) : p a :=
  Quotient.inductionOn' a h

@[simp]
theorem toAntisymmetrization_ofAntisymmetrization (a : Antisymmetrization α r) :
    toAntisymmetrization r (ofAntisymmetrization r a) = a :=
  Quotient.out_eq' _

end IsPreorder

section Preorder

variable [Preorder α] [Preorder β] {a b : α}

theorem AntisymmRel.image {a b : α} (h : AntisymmRel (· ≤ ·) a b) {f : α → β} (hf : Monotone f) :
    AntisymmRel (· ≤ ·) (f a) (f b) :=
  ⟨hf h.1, hf h.2⟩

instance instPartialOrderAntisymmetrization : PartialOrder (Antisymmetrization α (· ≤ ·)) where
  le a b :=
    (Quotient.liftOn₂' a b (· ≤ ·)) fun (_ _ _ _ : α) h₁ h₂ =>
      propext ⟨fun h => h₁.2.trans <| h.trans h₂.1, fun h => h₁.1.trans <| h.trans h₂.2⟩
  lt a b :=
    (Quotient.liftOn₂' a b (· < ·)) fun (_ _ _ _ : α) h₁ h₂ =>
      propext ⟨fun h => h₁.2.trans_lt <| h.trans_le h₂.1, fun h =>
                h₁.1.trans_lt <| h.trans_le h₂.2⟩
  le_refl a := Quotient.inductionOn' a <| le_refl
  le_trans a b c := Quotient.inductionOn₃' a b c fun _ _ _ => le_trans
  lt_iff_le_not_le a b := Quotient.inductionOn₂' a b fun _ _ => lt_iff_le_not_le
  le_antisymm a b := Quotient.inductionOn₂' a b fun _ _ hab hba => Quotient.sound' ⟨hab, hba⟩

theorem antisymmetrization_fibration :
    Relation.Fibration (· < ·) (· < ·) (@toAntisymmetrization α (· ≤ ·) _) := by
  rintro a ⟨b⟩ h
  exact ⟨b, h, rfl⟩

theorem acc_antisymmetrization_iff : Acc (· < ·)
    (@toAntisymmetrization α (· ≤ ·) _ a) ↔ Acc (· < ·) a :=
  acc_liftOn₂'_iff

theorem wellFounded_antisymmetrization_iff :
    WellFounded (@LT.lt (Antisymmetrization α (· ≤ ·)) _) ↔ WellFounded (@LT.lt α _) :=
  wellFounded_liftOn₂'_iff

instance [WellFoundedLT α] : WellFoundedLT (Antisymmetrization α (· ≤ ·)) :=
  ⟨wellFounded_antisymmetrization_iff.2 IsWellFounded.wf⟩

instance [@DecidableRel α (· ≤ ·)] [@DecidableRel α (· < ·)] [IsTotal α (· ≤ ·)] :
    LinearOrder (Antisymmetrization α (· ≤ ·)) :=
  { instPartialOrderAntisymmetrization with
    le_total := fun a b => Quotient.inductionOn₂' a b <| total_of (· ≤ ·),
    decidableLE := fun _ _ => show Decidable (Quotient.liftOn₂' _ _ _ _) from inferInstance,
    decidableLT := fun _ _ => show Decidable (Quotient.liftOn₂' _ _ _ _) from inferInstance }

@[simp]
theorem toAntisymmetrization_le_toAntisymmetrization_iff :
    @toAntisymmetrization α (· ≤ ·) _ a ≤ @toAntisymmetrization α (· ≤ ·) _ b ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem toAntisymmetrization_lt_toAntisymmetrization_iff :
    @toAntisymmetrization α (· ≤ ·) _ a < @toAntisymmetrization α (· ≤ ·) _ b ↔ a < b :=
  Iff.rfl

@[simp]
theorem ofAntisymmetrization_le_ofAntisymmetrization_iff {a b : Antisymmetrization α (· ≤ ·)} :
    ofAntisymmetrization (· ≤ ·) a ≤ ofAntisymmetrization (· ≤ ·) b ↔ a ≤ b :=
  (Quotient.out'RelEmbedding _).map_rel_iff

@[simp]
theorem ofAntisymmetrization_lt_ofAntisymmetrization_iff {a b : Antisymmetrization α (· ≤ ·)} :
    ofAntisymmetrization (· ≤ ·) a < ofAntisymmetrization (· ≤ ·) b ↔ a < b :=
  (Quotient.out'RelEmbedding _).map_rel_iff

@[mono]
theorem toAntisymmetrization_mono : Monotone (@toAntisymmetrization α (· ≤ ·) _) := fun _ _ => id

private theorem liftFun_antisymmRel (f : α →o β) :
    ((AntisymmRel.setoid α (· ≤ ·)).r ⇒ (AntisymmRel.setoid β (· ≤ ·)).r) f f := fun _ _ h =>
  ⟨f.mono h.1, f.mono h.2⟩

/-- Turns an order homomorphism from `α` to `β` into one from `Antisymmetrization α` to
`Antisymmetrization β`. `Antisymmetrization` is actually a functor. See `Preorder_to_PartialOrder`.
-/
protected def OrderHom.antisymmetrization (f : α →o β) :
    Antisymmetrization α (· ≤ ·) →o Antisymmetrization β (· ≤ ·) :=
  ⟨Quotient.map' f <| liftFun_antisymmRel f, fun a b => Quotient.inductionOn₂' a b <| f.mono⟩

@[simp]
theorem OrderHom.coe_antisymmetrization (f : α →o β) :
    ⇑f.antisymmetrization = Quotient.map' f (liftFun_antisymmRel f) :=
  rfl

/- Porting note: Removed @[simp] attribute. With this `simp` lemma the LHS of
`OrderHom.antisymmetrization_apply_mk` is not in normal-form -/
theorem OrderHom.antisymmetrization_apply (f : α →o β) (a : Antisymmetrization α (· ≤ ·)) :
    f.antisymmetrization a = Quotient.map' f (liftFun_antisymmRel f) a :=
  rfl

@[simp]
theorem OrderHom.antisymmetrization_apply_mk (f : α →o β) (a : α) :
    f.antisymmetrization (toAntisymmetrization _ a) = toAntisymmetrization _ (f a) :=
  @Quotient.map_mk _ _ (_root_.id _) (_root_.id _) f (liftFun_antisymmRel f) _

variable (α)

/-- `ofAntisymmetrization` as an order embedding. -/
@[simps]
noncomputable def OrderEmbedding.ofAntisymmetrization : Antisymmetrization α (· ≤ ·) ↪o α :=
  { Quotient.out'RelEmbedding _ with toFun := _root_.ofAntisymmetrization _ }

/-- `Antisymmetrization` and `orderDual` commute. -/
def OrderIso.dualAntisymmetrization :
    (Antisymmetrization α (· ≤ ·))ᵒᵈ ≃o Antisymmetrization αᵒᵈ (· ≤ ·) where
  toFun := (Quotient.map' id) fun _ _ => And.symm
  invFun := (Quotient.map' id) fun _ _ => And.symm
  left_inv a := Quotient.inductionOn' a fun a => by simp_rw [Quotient.map'_mk'', id]
  right_inv a := Quotient.inductionOn' a fun a => by simp_rw [Quotient.map'_mk'', id]
  map_rel_iff' := @fun a b => Quotient.inductionOn₂' a b fun a b => Iff.rfl

@[simp]
theorem OrderIso.dualAntisymmetrization_apply (a : α) :
    OrderIso.dualAntisymmetrization _ (toDual <| toAntisymmetrization _ a) =
      toAntisymmetrization _ (toDual a) :=
  rfl

@[simp]
theorem OrderIso.dualAntisymmetrization_symm_apply (a : α) :
    (OrderIso.dualAntisymmetrization _).symm (toAntisymmetrization _ <| toDual a) =
      toDual (toAntisymmetrization _ a) :=
  rfl

end Preorder
