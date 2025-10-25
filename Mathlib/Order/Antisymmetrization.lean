/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Logic.Relation
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic.Tauto

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

open Function OrderDual

variable {α β : Type*} {a b c d : α}

section Relation

variable (r : α → α → Prop)

/-- The antisymmetrization relation `AntisymmRel r` is defined so that
`AntisymmRel r a b ↔ r a b ∧ r b a`. -/
def AntisymmRel (a b : α) : Prop :=
  r a b ∧ r b a

theorem antisymmRel_swap : AntisymmRel (swap r) = AntisymmRel r :=
  funext₂ fun _ _ ↦ propext and_comm

theorem antisymmRel_swap_apply : AntisymmRel (swap r) a b ↔ AntisymmRel r a b :=
  and_comm

@[simp, refl]
theorem AntisymmRel.refl [IsRefl α r] (a : α) : AntisymmRel r a a :=
  ⟨_root_.refl _, _root_.refl _⟩

variable {r} in
lemma AntisymmRel.rfl [IsRefl α r] {a : α} : AntisymmRel r a a := .refl ..

instance [IsRefl α r] : IsRefl α (AntisymmRel r) where
  refl := .refl r

variable {r}

theorem AntisymmRel.of_eq [IsRefl α r] {a b : α} (h : a = b) : AntisymmRel r a b := h ▸ .rfl
alias Eq.antisymmRel := AntisymmRel.of_eq

@[symm]
theorem AntisymmRel.symm : AntisymmRel r a b → AntisymmRel r b a :=
  And.symm

instance : IsSymm α (AntisymmRel r) where
  symm _ _ := AntisymmRel.symm

theorem antisymmRel_comm : AntisymmRel r a b ↔ AntisymmRel r b a :=
  And.comm

@[trans]
theorem AntisymmRel.trans [IsTrans α r] (hab : AntisymmRel r a b) (hbc : AntisymmRel r b c) :
    AntisymmRel r a c :=
  ⟨_root_.trans hab.1 hbc.1, _root_.trans hbc.2 hab.2⟩

instance [IsTrans α r] : IsTrans α (AntisymmRel r) where
  trans _ _ _ := .trans

instance AntisymmRel.decidableRel [DecidableRel r] : DecidableRel (AntisymmRel r) :=
  fun _ _ ↦ instDecidableAnd

@[simp]
theorem antisymmRel_iff_eq [IsRefl α r] [IsAntisymm α r] : AntisymmRel r a b ↔ a = b :=
  antisymm_iff

alias ⟨AntisymmRel.eq, _⟩ := antisymmRel_iff_eq

namespace Mathlib.Tactic.GCongr

variable {α : Type*} {a b : α} {r : α → α → Prop}

lemma AntisymmRel.left (h : AntisymmRel r a b) : r a b := h.1
lemma AntisymmRel.right (h : AntisymmRel r a b) : r b a := h.2

/-- See if the term is `AntisymmRel r a b` and the goal is `r a b`. -/
@[gcongr_forward] def exactAntisymmRelLeft : ForwardExt where
  eval h goal := do goal.assignIfDefEq (← Lean.Meta.mkAppM ``AntisymmRel.left #[h])

/-- See if the term is `AntisymmRel r a b` and the goal is `r b a`. -/
@[gcongr_forward] def exactAntisymmRelRight : ForwardExt where
  eval h goal := do goal.assignIfDefEq (← Lean.Meta.mkAppM ``AntisymmRel.right #[h])

end Mathlib.Tactic.GCongr

end Relation

section LE

variable [LE α]

theorem AntisymmRel.le (h : AntisymmRel (· ≤ ·) a b) : a ≤ b := h.1
theorem AntisymmRel.ge (h : AntisymmRel (· ≤ ·) a b) : b ≤ a := h.2

end LE

section IsPreorder

variable (α) (r : α → α → Prop) [IsPreorder α r]

/-- The antisymmetrization relation as an equivalence relation. -/
@[simps]
def AntisymmRel.setoid : Setoid α :=
  ⟨AntisymmRel r, .refl r, .symm, .trans⟩

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
  Quotient.out

instance [Inhabited α] : Inhabited (Antisymmetrization α r) := by
  unfold Antisymmetrization; infer_instance

instance [Subsingleton α] : Subsingleton (Antisymmetrization α r) := by
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

variable [Preorder α] [Preorder β]

theorem le_iff_lt_or_antisymmRel : a ≤ b ↔ a < b ∨ AntisymmRel (· ≤ ·) a b := by
  rw [lt_iff_le_not_ge, AntisymmRel]
  tauto

theorem le_of_le_of_antisymmRel (h₁ : a ≤ b) (h₂ : AntisymmRel (· ≤ ·) b c) : a ≤ c :=
  h₁.trans h₂.le

theorem le_of_antisymmRel_of_le (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : b ≤ c) : a ≤ c :=
  h₁.le.trans h₂

theorem lt_of_lt_of_antisymmRel (h₁ : a < b) (h₂ : AntisymmRel (· ≤ ·) b c) : a < c :=
  h₁.trans_le h₂.le

theorem lt_of_antisymmRel_of_lt (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : b < c) : a < c :=
  h₁.le.trans_lt h₂

alias ⟨LE.le.lt_or_antisymmRel, _⟩ := le_iff_lt_or_antisymmRel
alias LE.le.trans_antisymmRel := le_of_le_of_antisymmRel
alias AntisymmRel.trans_le := le_of_antisymmRel_of_le
alias LT.lt.trans_antisymmRel := lt_of_lt_of_antisymmRel
alias AntisymmRel.trans_lt := lt_of_antisymmRel_of_lt

instance : @Trans α α α (· ≤ ·) (AntisymmRel (· ≤ ·)) (· ≤ ·) where
  trans := le_of_le_of_antisymmRel

instance : @Trans α α α (AntisymmRel (· ≤ ·)) (· ≤ ·) (· ≤ ·) where
  trans := le_of_antisymmRel_of_le

instance : @Trans α α α (· < ·) (AntisymmRel (· ≤ ·)) (· < ·) where
  trans := lt_of_lt_of_antisymmRel

instance : @Trans α α α (AntisymmRel (· ≤ ·)) (· < ·) (· < ·) where
  trans := lt_of_antisymmRel_of_lt

theorem AntisymmRel.le_congr (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : AntisymmRel (· ≤ ·) c d) :
    a ≤ c ↔ b ≤ d where
  mp h := (h₁.symm.trans_le h).trans_antisymmRel h₂
  mpr h := (h₁.trans_le h).trans_antisymmRel h₂.symm

theorem AntisymmRel.le_congr_left (h : AntisymmRel (· ≤ ·) a b) : a ≤ c ↔ b ≤ c :=
  h.le_congr .rfl

theorem AntisymmRel.le_congr_right (h : AntisymmRel (· ≤ ·) b c) : a ≤ b ↔ a ≤ c :=
  AntisymmRel.rfl.le_congr h

theorem AntisymmRel.lt_congr (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : AntisymmRel (· ≤ ·) c d) :
    a < c ↔ b < d where
  mp h := (h₁.symm.trans_lt h).trans_antisymmRel h₂
  mpr h := (h₁.trans_lt h).trans_antisymmRel h₂.symm

theorem AntisymmRel.lt_congr_left (h : AntisymmRel (· ≤ ·) a b) : a < c ↔ b < c :=
  h.lt_congr .rfl

theorem AntisymmRel.lt_congr_right (h : AntisymmRel (· ≤ ·) b c) : a < b ↔ a < c :=
  AntisymmRel.rfl.lt_congr h

theorem AntisymmRel.antisymmRel_congr
    (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : AntisymmRel (· ≤ ·) c d) :
    AntisymmRel (· ≤ ·) a c ↔ AntisymmRel (· ≤ ·) b d :=
  rel_congr h₁ h₂

theorem AntisymmRel.antisymmRel_congr_left (h : AntisymmRel (· ≤ ·) a b) :
    AntisymmRel (· ≤ ·) a c ↔ AntisymmRel (· ≤ ·) b c :=
  rel_congr_left h

theorem AntisymmRel.antisymmRel_congr_right (h : AntisymmRel (· ≤ ·) b c) :
    AntisymmRel (· ≤ ·) a b ↔ AntisymmRel (· ≤ ·) a c :=
  rel_congr_right h

theorem AntisymmRel.image (h : AntisymmRel (· ≤ ·) a b) {f : α → β} (hf : Monotone f) :
    AntisymmRel (· ≤ ·) (f a) (f b) :=
  ⟨hf h.1, hf h.2⟩

instance instPartialOrderAntisymmetrization : PartialOrder (Antisymmetrization α (· ≤ ·)) where
  le :=
    Quotient.lift₂ (· ≤ ·) fun (_ _ _ _ : α) h₁ h₂ =>
      propext ⟨fun h => h₁.2.trans <| h.trans h₂.1, fun h => h₁.1.trans <| h.trans h₂.2⟩
  lt :=
    Quotient.lift₂ (· < ·) fun (_ _ _ _ : α) h₁ h₂ =>
      propext ⟨fun h => h₁.2.trans_lt <| h.trans_le h₂.1, fun h =>
                h₁.1.trans_lt <| h.trans_le h₂.2⟩
  le_refl a := Quotient.inductionOn' a le_refl
  le_trans a b c := Quotient.inductionOn₃' a b c fun _ _ _ => le_trans
  lt_iff_le_not_ge a b := Quotient.inductionOn₂' a b fun _ _ => lt_iff_le_not_ge
  le_antisymm a b := Quotient.inductionOn₂' a b fun _ _ hab hba => Quotient.sound' ⟨hab, hba⟩

theorem antisymmetrization_fibration :
    Relation.Fibration (· < ·) (· < ·) (toAntisymmetrization (α := α) (· ≤ ·)) := by
  rintro a ⟨b⟩ h
  exact ⟨b, h, rfl⟩

theorem acc_antisymmetrization_iff : Acc (· < ·)
    (toAntisymmetrization (α := α) (· ≤ ·) a) ↔ Acc (· < ·) a :=
  acc_lift₂_iff

theorem wellFounded_antisymmetrization_iff :
    WellFounded (@LT.lt (Antisymmetrization α (· ≤ ·)) _) ↔ WellFounded (@LT.lt α _) :=
  wellFounded_lift₂_iff

theorem wellFoundedLT_antisymmetrization_iff :
    WellFoundedLT (Antisymmetrization α (· ≤ ·)) ↔ WellFoundedLT α := by
  simp_rw [isWellFounded_iff, wellFounded_antisymmetrization_iff]

theorem wellFoundedGT_antisymmetrization_iff :
    WellFoundedGT (Antisymmetrization α (· ≤ ·)) ↔ WellFoundedGT α := by
  simp_rw [isWellFounded_iff]
  convert wellFounded_liftOn₂'_iff with ⟨_⟩ ⟨_⟩
  exact fun _ _ _ _ h₁ h₂ ↦ propext
    ⟨fun h ↦ (h₂.2.trans_lt h).trans_le h₁.1, fun h ↦ (h₂.1.trans_lt h).trans_le h₁.2⟩

instance [WellFoundedLT α] : WellFoundedLT (Antisymmetrization α (· ≤ ·)) :=
  wellFoundedLT_antisymmetrization_iff.mpr ‹_›

instance [WellFoundedGT α] : WellFoundedGT (Antisymmetrization α (· ≤ ·)) :=
  wellFoundedGT_antisymmetrization_iff.mpr ‹_›

instance [DecidableLE α] [DecidableLT α] [Std.Total (α := α) (· ≤ ·)] :
    LinearOrder (Antisymmetrization α (· ≤ ·)) :=
  { instPartialOrderAntisymmetrization with
    le_total := fun a b => Quotient.inductionOn₂' a b <| Std.Total.total (r := (· ≤ ·)),
    toDecidableLE := fun _ _ => show Decidable (Quotient.liftOn₂' _ _ _ _) from inferInstance,
    toDecidableLT := fun _ _ => show Decidable (Quotient.liftOn₂' _ _ _ _) from inferInstance }

@[simp]
theorem toAntisymmetrization_le_toAntisymmetrization_iff :
    toAntisymmetrization (α := α) (· ≤ ·) a ≤ toAntisymmetrization (α := α) (· ≤ ·) b ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem toAntisymmetrization_lt_toAntisymmetrization_iff :
    toAntisymmetrization (α := α) (· ≤ ·) a < toAntisymmetrization (α := α) (· ≤ ·) b ↔ a < b :=
  Iff.rfl

@[simp]
theorem ofAntisymmetrization_le_ofAntisymmetrization_iff {a b : Antisymmetrization α (· ≤ ·)} :
    ofAntisymmetrization (· ≤ ·) a ≤ ofAntisymmetrization (· ≤ ·) b ↔ a ≤ b :=
  (Quotient.outRelEmbedding _).map_rel_iff

@[simp]
theorem ofAntisymmetrization_lt_ofAntisymmetrization_iff {a b : Antisymmetrization α (· ≤ ·)} :
    ofAntisymmetrization (· ≤ ·) a < ofAntisymmetrization (· ≤ ·) b ↔ a < b :=
  (Quotient.outRelEmbedding _).map_rel_iff

@[mono]
theorem toAntisymmetrization_mono : Monotone (toAntisymmetrization (α := α) (· ≤ ·)) :=
  fun _ _ => id

open scoped Relator in
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
  { Quotient.outRelEmbedding _ with toFun := _root_.ofAntisymmetrization _ }

/-- `Antisymmetrization` and `orderDual` commute. -/
def OrderIso.dualAntisymmetrization :
    (Antisymmetrization α (· ≤ ·))ᵒᵈ ≃o Antisymmetrization αᵒᵈ (· ≤ ·) where
  toFun := (Quotient.map' id) fun _ _ => And.symm
  invFun := (Quotient.map' id) fun _ _ => And.symm
  left_inv a := Quotient.inductionOn' a fun a => by simp_rw [Quotient.map'_mk'', id]
  right_inv a := Quotient.inductionOn' a fun a => by simp_rw [Quotient.map'_mk'', id]
  map_rel_iff' := @fun a b => Quotient.inductionOn₂' a b fun _ _ => Iff.rfl

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

section Prod

variable (α β) [Preorder α] [Preorder β]

namespace Antisymmetrization

/-- The antisymmetrization of a product preorder is order isomorphic
to the product of antisymmetrizations. -/
def prodEquiv : Antisymmetrization (α × β) (· ≤ ·) ≃o
    Antisymmetrization α (· ≤ ·) × Antisymmetrization β (· ≤ ·) where
  toFun := Quotient.lift (fun ab ↦ (⟦ab.1⟧, ⟦ab.2⟧)) fun ab₁ ab₂ h ↦
    Prod.ext (Quotient.sound ⟨h.1.1, h.2.1⟩) (Quotient.sound ⟨h.1.2, h.2.2⟩)
  invFun := Function.uncurry <| Quotient.lift₂ (fun a b ↦ ⟦(a, b)⟧)
    fun a₁ b₁ a₂ b₂ h₁ h₂ ↦ Quotient.sound ⟨⟨h₁.1, h₂.1⟩, h₁.2, h₂.2⟩
  left_inv := by rintro ⟨_⟩; rfl
  right_inv := by rintro ⟨⟨_⟩, ⟨_⟩⟩; rfl
  map_rel_iff' := by rintro ⟨_⟩ ⟨_⟩; rfl

@[simp] lemma prodEquiv_apply_mk {ab} : prodEquiv α β ⟦ab⟧ = (⟦ab.1⟧, ⟦ab.2⟧) := rfl
@[simp] lemma prodEquiv_symm_apply_mk {a b} : (prodEquiv α β).symm (⟦a⟧, ⟦b⟧) = ⟦(a, b)⟧ := rfl

end Antisymmetrization

attribute [local instance] Prod.wellFoundedLT' Prod.wellFoundedGT'

instance Prod.wellFoundedLT [WellFoundedLT α] [WellFoundedLT β] : WellFoundedLT (α × β) :=
  wellFoundedLT_antisymmetrization_iff.mp <|
    (Antisymmetrization.prodEquiv α β).strictMono.wellFoundedLT

instance Prod.wellFoundedGT [WellFoundedGT α] [WellFoundedGT β] : WellFoundedGT (α × β) :=
  wellFoundedGT_antisymmetrization_iff.mp <|
    (Antisymmetrization.prodEquiv α β).strictMono.wellFoundedGT

end Prod
