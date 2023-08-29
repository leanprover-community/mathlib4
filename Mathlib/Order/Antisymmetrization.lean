/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Hom.Basic
import Mathlib.Logic.Relation

#align_import order.antisymmetrization from "leanprover-community/mathlib"@"3353f661228bd27f632c600cd1a58b874d847c90"

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

/- Porting Notes: There are many changes from `toAntisymmetrization (· ≤ ·)` to
`@toAntisymmetrization α (· ≤ ·) _` -/

open Function OrderDual

variable {α β : Type*}

section Relation

variable (r : α → α → Prop)

/-- The antisymmetrization relation. -/
def AntisymmRel (a b : α) : Prop :=
  r a b ∧ r b a
#align antisymm_rel AntisymmRel

theorem antisymmRel_swap : AntisymmRel (swap r) = AntisymmRel r :=
  funext fun _ => funext fun _ => propext and_comm
#align antisymm_rel_swap antisymmRel_swap

@[refl]
theorem antisymmRel_refl [IsRefl α r] (a : α) : AntisymmRel r a a :=
  ⟨refl _, refl _⟩
#align antisymm_rel_refl antisymmRel_refl

variable {r}

@[symm]
theorem AntisymmRel.symm {a b : α} : AntisymmRel r a b → AntisymmRel r b a :=
  And.symm
#align antisymm_rel.symm AntisymmRel.symm

@[trans]
theorem AntisymmRel.trans [IsTrans α r] {a b c : α} (hab : AntisymmRel r a b)
    (hbc : AntisymmRel r b c) : AntisymmRel r a c :=
  ⟨_root_.trans hab.1 hbc.1, _root_.trans hbc.2 hab.2⟩
#align antisymm_rel.trans AntisymmRel.trans

instance AntisymmRel.decidableRel [DecidableRel r] : DecidableRel (AntisymmRel r) := fun _ _ =>
  instDecidableAnd
#align antisymm_rel.decidable_rel AntisymmRel.decidableRel

@[simp]
theorem antisymmRel_iff_eq [IsRefl α r] [IsAntisymm α r] {a b : α} : AntisymmRel r a b ↔ a = b :=
  antisymm_iff
#align antisymm_rel_iff_eq antisymmRel_iff_eq

alias ⟨AntisymmRel.eq, _⟩ := antisymmRel_iff_eq
#align antisymm_rel.eq AntisymmRel.eq

end Relation

section IsPreorder

variable (α) (r : α → α → Prop) [IsPreorder α r]

/-- The antisymmetrization relation as an equivalence relation. -/
@[simps]
def AntisymmRel.setoid : Setoid α :=
  ⟨AntisymmRel r, antisymmRel_refl _, AntisymmRel.symm, AntisymmRel.trans⟩
#align antisymm_rel.setoid AntisymmRel.setoid
#align antisymm_rel.setoid_r AntisymmRel.setoid_r

/-- The partial order derived from a preorder by making pairwise comparable elements equal. This is
the quotient by `fun a b => a ≤ b ∧ b ≤ a`. -/
def Antisymmetrization : Type _ :=
  Quotient <| AntisymmRel.setoid α r
#align antisymmetrization Antisymmetrization

variable {α}

/-- Turn an element into its antisymmetrization. -/
def toAntisymmetrization : α → Antisymmetrization α r :=
  Quotient.mk _
#align to_antisymmetrization toAntisymmetrization

/-- Get a representative from the antisymmetrization. -/
noncomputable def ofAntisymmetrization : Antisymmetrization α r → α :=
  Quotient.out'
#align of_antisymmetrization ofAntisymmetrization

instance [Inhabited α] : Inhabited (Antisymmetrization α r) :=
  by unfold Antisymmetrization; infer_instance
     -- ⊢ Inhabited (Quotient (AntisymmRel.setoid α r))
                                -- 🎉 no goals

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
theorem toAntisymmetrization_ofAntisymmetrization (a : Antisymmetrization α r) :
    toAntisymmetrization r (ofAntisymmetrization r a) = a :=
  Quotient.out_eq' _
#align to_antisymmetrization_of_antisymmetrization toAntisymmetrization_ofAntisymmetrization

end IsPreorder

section Preorder

variable [Preorder α] [Preorder β] {a b : α}

theorem AntisymmRel.image {a b : α} (h : AntisymmRel (· ≤ ·) a b) {f : α → β} (hf : Monotone f) :
    AntisymmRel (· ≤ ·) (f a) (f b) :=
  ⟨hf h.1, hf h.2⟩
#align antisymm_rel.image AntisymmRel.image

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
  -- ⊢ ∃ a', (fun x x_1 => x < x_1) a' a ∧ toAntisymmetrization (fun x x_1 => x ≤ x …
  exact ⟨b, h, rfl⟩
  -- 🎉 no goals
#align antisymmetrization_fibration antisymmetrization_fibration

theorem acc_antisymmetrization_iff : Acc (· < ·)
    (@toAntisymmetrization α (· ≤ ·) _ a) ↔ Acc (· < ·) a :=
  acc_liftOn₂'_iff
#align acc_antisymmetrization_iff acc_antisymmetrization_iff

theorem wellFounded_antisymmetrization_iff :
    WellFounded (@LT.lt (Antisymmetrization α (· ≤ ·)) _) ↔ WellFounded (@LT.lt α _) :=
  wellFounded_liftOn₂'_iff
#align well_founded_antisymmetrization_iff wellFounded_antisymmetrization_iff

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
#align to_antisymmetrization_le_to_antisymmetrization_iff toAntisymmetrization_le_toAntisymmetrization_iff

@[simp]
theorem toAntisymmetrization_lt_toAntisymmetrization_iff :
    @toAntisymmetrization α (· ≤ ·) _ a < @toAntisymmetrization α (· ≤ ·) _ b ↔ a < b :=
  Iff.rfl
#align to_antisymmetrization_lt_to_antisymmetrization_iff toAntisymmetrization_lt_toAntisymmetrization_iff

@[simp]
theorem ofAntisymmetrization_le_ofAntisymmetrization_iff {a b : Antisymmetrization α (· ≤ ·)} :
    ofAntisymmetrization (· ≤ ·) a ≤ ofAntisymmetrization (· ≤ ·) b ↔ a ≤ b :=
  (Quotient.out'RelEmbedding _).map_rel_iff
#align of_antisymmetrization_le_of_antisymmetrization_iff ofAntisymmetrization_le_ofAntisymmetrization_iff

@[simp]
theorem ofAntisymmetrization_lt_ofAntisymmetrization_iff {a b : Antisymmetrization α (· ≤ ·)} :
    ofAntisymmetrization (· ≤ ·) a < ofAntisymmetrization (· ≤ ·) b ↔ a < b :=
  (Quotient.out'RelEmbedding _).map_rel_iff
#align of_antisymmetrization_lt_of_antisymmetrization_iff ofAntisymmetrization_lt_ofAntisymmetrization_iff

@[mono]
theorem toAntisymmetrization_mono : Monotone (@toAntisymmetrization α (· ≤ ·) _) := fun _ _ => id
#align to_antisymmetrization_mono toAntisymmetrization_mono

private theorem liftFun_antisymmRel (f : α →o β) :
    ((AntisymmRel.setoid α (· ≤ ·)).r ⇒ (AntisymmRel.setoid β (· ≤ ·)).r) f f := fun _ _ h =>
  ⟨f.mono h.1, f.mono h.2⟩

/-- Turns an order homomorphism from `α` to `β` into one from `Antisymmetrization α` to
`Antisymmetrization β`. `Antisymmetrization` is actually a functor. See `Preorder_to_PartialOrder`.
-/
protected def OrderHom.antisymmetrization (f : α →o β) :
    Antisymmetrization α (· ≤ ·) →o Antisymmetrization β (· ≤ ·) :=
  ⟨Quotient.map' f <| liftFun_antisymmRel f, fun a b => Quotient.inductionOn₂' a b <| f.mono⟩
#align order_hom.antisymmetrization OrderHom.antisymmetrization

@[simp]
theorem OrderHom.coe_antisymmetrization (f : α →o β) :
    ⇑f.antisymmetrization = Quotient.map' f (liftFun_antisymmRel f) :=
  rfl
#align order_hom.coe_antisymmetrization OrderHom.coe_antisymmetrization

/- Porting notes: Removed @[simp] attribute. With this `simp` lemma the LHS of
`OrderHom.antisymmetrization_apply_mk` is not in normal-form -/
theorem OrderHom.antisymmetrization_apply (f : α →o β) (a : Antisymmetrization α (· ≤ ·)) :
    f.antisymmetrization a = Quotient.map' f (liftFun_antisymmRel f) a :=
  rfl
#align order_hom.antisymmetrization_apply OrderHom.antisymmetrization_apply

@[simp]
theorem OrderHom.antisymmetrization_apply_mk (f : α →o β) (a : α) :
    f.antisymmetrization (toAntisymmetrization _ a) = toAntisymmetrization _ (f a) :=
  @Quotient.map_mk _ _ (_root_.id _) (_root_.id _) f (liftFun_antisymmRel f) _
#align order_hom.antisymmetrization_apply_mk OrderHom.antisymmetrization_apply_mk

variable (α)

/-- `ofAntisymmetrization` as an order embedding. -/
@[simps]
noncomputable def OrderEmbedding.ofAntisymmetrization : Antisymmetrization α (· ≤ ·) ↪o α :=
  { Quotient.out'RelEmbedding _ with toFun := _root_.ofAntisymmetrization _ }
#align order_embedding.of_antisymmetrization OrderEmbedding.ofAntisymmetrization
#align order_embedding.of_antisymmetrization_apply OrderEmbedding.ofAntisymmetrization_apply

/-- `Antisymmetrization` and `orderDual` commute. -/
def OrderIso.dualAntisymmetrization :
    (Antisymmetrization α (· ≤ ·))ᵒᵈ ≃o Antisymmetrization αᵒᵈ (· ≤ ·) where
  toFun := (Quotient.map' id) fun _ _ => And.symm
  invFun := (Quotient.map' id) fun _ _ => And.symm
  left_inv a := Quotient.inductionOn' a fun a => by simp_rw [Quotient.map'_mk'', id]
                                                    -- 🎉 no goals
  right_inv a := Quotient.inductionOn' a fun a => by simp_rw [Quotient.map'_mk'', id]
                                                     -- 🎉 no goals
  map_rel_iff' := @fun a b => Quotient.inductionOn₂' a b fun a b => Iff.rfl
#align order_iso.dual_antisymmetrization OrderIso.dualAntisymmetrization

@[simp]
theorem OrderIso.dualAntisymmetrization_apply (a : α) :
    OrderIso.dualAntisymmetrization _ (toDual <| toAntisymmetrization _ a) =
      toAntisymmetrization _ (toDual a) :=
  rfl
#align order_iso.dual_antisymmetrization_apply OrderIso.dualAntisymmetrization_apply

@[simp]
theorem OrderIso.dualAntisymmetrization_symm_apply (a : α) :
    (OrderIso.dualAntisymmetrization _).symm (toAntisymmetrization _ <| toDual a) =
      toDual (toAntisymmetrization _ a) :=
  rfl
#align order_iso.dual_antisymmetrization_symm_apply OrderIso.dualAntisymmetrization_symm_apply

end Preorder
