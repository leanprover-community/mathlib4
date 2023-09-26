/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Hom.Lattice

/-!
# Adding complements to a generalized Boolean algebra

This file embeds any generalized Boolean algebra into a Boolean algebra.

This concretely proves that any equation holding true in the theory of Boolean algebras that does
not reference `ᶜ` also holds true in the theory of generalized Boolean algebras. Put another way,
one does not need the existence of complements to prove something which does not talk about
complements.

## Main declarations

* `Booleanisation`: Boolean algebra containing a given generalised Boolean algebra as a sublattice.
* `Booleanisation.inlLatticeHom`: Boolean algebra containing a given generalised Boolean algebra as a sublattice.
-/

open Function

variable {α : Type*}

/-- Boolean algebra containing a given generalised Boolean algebra `α` as a sublattice. -/
def Booleanisation (α : Type*) := α ⊕ α

namespace Booleanisation

instance instDecidableEq [DecidableEq α] : DecidableEq (Booleanisation α) := Sum.instDecidableEqSum

variable [GeneralizedBooleanAlgebra α] {x y : Booleanisation α} {a b : α}

@[match_pattern] abbrev inl : α → Booleanisation α := Sum.inl
@[match_pattern] abbrev inr : α → Booleanisation α := Sum.inr

protected inductive LE : Booleanisation α → Booleanisation α → Prop
  | protected inl {a b} : a ≤ b → Booleanisation.LE (inl a) (inl b)
  | protected inr {a b} : a ≤ b → Booleanisation.LE (inr b) (inr a)
  | protected sep {a b} : Disjoint a b → Booleanisation.LE (inl a) (inr b)

protected inductive LT : Booleanisation α → Booleanisation α → Prop
  | protected inl {a b} : a < b → Booleanisation.LT (inl a) (inl b)
  | protected inr {a b} : a < b → Booleanisation.LT (inr b) (inr a)
  | protected sep {a b} : Disjoint a b → Booleanisation.LT (inl a) (inr b)

instance instLE : LE (Booleanisation α) where
  le := Booleanisation.LE

instance instLT : LT (Booleanisation α) where
  lt := Booleanisation.LT

instance instSup : Sup (Booleanisation α) where
  sup x y := match x, y with
    | inl a, inl b => inl (a ⊔ b)
    | inl a, inr b => inr (b \ a)
    | inr a, inl b => inr (a \ b)
    | inr a, inr b => inr (a ⊓ b)

instance instInf : Inf (Booleanisation α) where
  inf x y := match x, y with
    | inl a, inl b => inl (a ⊓ b)
    | inl a, inr b => inl (a \ b)
    | inr a, inl b => inl (b \ a)
    | inr a, inr b => inr (a ⊔ b)

instance instBot : Bot (Booleanisation α) where
  bot := inl ⊥

instance instTop : Top (Booleanisation α) where
  top := inr ⊥

instance instCompl : HasCompl (Booleanisation α) where
  compl x := match x with
    | inl a => inr a
    | inr a => inl a

instance instSDiff : SDiff (Booleanisation α) where
  sdiff x y  := match x, y with
    | inl a, inl b => inl (a \ b)
    | inl a, inr b => inl (a ⊓ b)
    | inr a, inl b => inr (a ⊔ b)
    | inr a, inr b => inl (b \ a)

@[simp] lemma inl_le_inl : inl a ≤ inl b ↔ a ≤ b := ⟨by rintro ⟨_⟩; assumption, LE.inl⟩
@[simp] lemma inr_le_inr : inr a ≤ inr b ↔ b ≤ a := ⟨by rintro ⟨_⟩; assumption, LE.inr⟩
@[simp] lemma inl_le_inr : inl a ≤ inr b ↔ Disjoint a b := ⟨by rintro ⟨_⟩; assumption, LE.sep⟩
@[simp] lemma not_inr_le_inl : ¬ inr a ≤ inl b := λ h ↦ nomatch h

@[simp] lemma inl_lt_inl : inl a < inl b ↔ a < b := ⟨by rintro ⟨_⟩; assumption, LT.inl⟩
@[simp] lemma inr_lt_inr : inr a < inr b ↔ b < a := ⟨by rintro ⟨_⟩; assumption, LT.inr⟩
@[simp] lemma inl_lt_inr : inl a < inr b ↔ Disjoint a b := ⟨by rintro ⟨_⟩; assumption, LT.sep⟩
@[simp] lemma not_inr_lt_inl : ¬ inr a < inl b := λ h ↦ nomatch h

@[simp] lemma inl_sup_inl (a b : α) : inl a ⊔ inl b = inl (a ⊔ b) := rfl
@[simp] lemma inl_sup_inr (a b : α) : inl a ⊔ inr b = inr (b \ a) := rfl
@[simp] lemma inr_sup_inl (a b : α) : inr a ⊔ inl b = inr (a \ b) := rfl
@[simp] lemma inr_sup_inr (a b : α) : inr a ⊔ inr b = inr (a ⊓ b) := rfl

@[simp] lemma inl_inf_inl (a b : α) : inl a ⊓ inl b = inl (a ⊓ b) := rfl
@[simp] lemma inl_inf_inr (a b : α) : inl a ⊓ inr b = inl (a \ b) := rfl
@[simp] lemma inr_inf_inl (a b : α) : inr a ⊓ inl b = inl (b \ a) := rfl
@[simp] lemma inr_inf_inr (a b : α) : inr a ⊓ inr b = inr (a ⊔ b) := rfl

@[simp] lemma inl_bot : inl (⊥ : α) = ⊥ := rfl
@[simp] lemma inr_bot : inr (⊥ : α) = ⊤ := rfl

@[simp] lemma compl_inl (a : α) : (inl a)ᶜ = inr a := rfl
@[simp] lemma compl_inr (a : α) : (inr a)ᶜ = inl a := rfl

@[simp] lemma inl_sdiff_inl (a b : α) : inl a \ inl b = inl (a \ b) := rfl
@[simp] lemma inl_sdiff_inr (a b : α) : inl a \ inr b = inl (a ⊓ b) := rfl
@[simp] lemma inr_sdiff_inl (a b : α) : inr a \ inl b = inr (a ⊔ b) := rfl
@[simp] lemma inr_sdiff_inr (a b : α) : inr a \ inr b = inl (b \ a) := rfl

instance instPreorder : Preorder (Booleanisation α) where
  lt := (· < ·)
  lt_iff_le_not_le x y := match x, y with
    | inl a, inl b => by simp [lt_iff_le_not_le]
    | inl a, inr b => by simp
    | inr a, inl b => by simp
    | inr a, inr b => by simp [lt_iff_le_not_le]
  le_refl x := match x with
    | inl a => LE.inl le_rfl
    | inr a => LE.inr le_rfl
  le_trans x y z hxy hyz := match x, y, z, hxy, hyz with
    | inl a, inl b, inl c, LE.inl hab, LE.inl hbc => LE.inl $ hab.trans hbc
    | inl a, inl b, inr c, LE.inl hab, LE.sep hbc => LE.sep $ hbc.mono_left hab
    | inl a, inr b, inr c, LE.sep hab, LE.inr hcb => LE.sep $ hab.mono_right hcb
    | inr a, inr b, inr c, LE.inr hba, LE.inr hcb => LE.inr $ hcb.trans hba

instance instPartialOrder : PartialOrder (Booleanisation α) where
  le_antisymm x y hxy hyx := match x, y, hxy, hyx with
    | inl a, inl b, LE.inl hab, LE.inl hba => by rw [hab.antisymm hba]
    | inr a, inr b, LE.inr hab, LE.inr hba => by rw [hab.antisymm hba]

-- The linter significantly hinders readability here.
set_option linter.unusedVariables false in
instance instSemilatticeSup : SemilatticeSup (Booleanisation α) where
  le_sup_left x y := match x, y with
    | inl a, inl b => LE.inl le_sup_left
    | inl a, inr b => LE.sep disjoint_sdiff_self_right
    | inr a, inl b => LE.inr sdiff_le
    | inr a, inr b => LE.inr inf_le_left
  le_sup_right x y := match x, y with
    | inl a, inl b => LE.inl le_sup_right
    | inl a, inr b => LE.inr sdiff_le
    | inr a, inl b => LE.sep disjoint_sdiff_self_right
    | inr a, inr b => LE.inr inf_le_right
  sup_le x y z hxz hyz := match x, y, z, hxz, hyz with
    | inl a, inl b, inl c, LE.inl hac, LE.inl hbc => LE.inl $ sup_le hac hbc
    | inl a, inl b, inr c, LE.sep hac, LE.sep hbc => LE.sep $ hac.sup_left hbc
    | inl a, inr b, inr c, LE.sep hac, LE.inr hcb => LE.inr $ le_sdiff.2 ⟨hcb, hac.symm⟩
    | inr a, inl b, inr c, LE.inr hca, LE.sep hbc => LE.inr $ le_sdiff.2 ⟨hca, hbc.symm⟩
    | inr a, inr b, inr c, LE.inr hca, LE.inr hcb => LE.inr $ le_inf hca hcb

-- The linter significantly hinders readability here.
set_option linter.unusedVariables false in
instance instSemilatticeInf : SemilatticeInf (Booleanisation α) where
  inf_le_left x y := match x, y with
    | inl a, inl b => LE.inl inf_le_left
    | inl a, inr b => LE.inl sdiff_le
    | inr a, inl b => LE.sep disjoint_sdiff_self_left
    | inr a, inr b => LE.inr le_sup_left
  inf_le_right x y := match x, y with
    | inl a, inl b => LE.inl inf_le_right
    | inl a, inr b => LE.sep disjoint_sdiff_self_left
    | inr a, inl b => LE.inl sdiff_le
    | inr a, inr b => LE.inr le_sup_right
  le_inf x y z hxz hyz := match x, y, z, hxz, hyz with
    | inl a, inl b, inl c, LE.inl hab, LE.inl hac => LE.inl $ le_inf hab hac
    | inl a, inl b, inr c, LE.inl hab, LE.sep hac => LE.inl $ le_sdiff.2 ⟨hab, hac⟩
    | inl a, inr b, inl c, LE.sep hab, LE.inl hac => LE.inl $ le_sdiff.2 ⟨hac, hab⟩
    | inl a, inr b, inr c, LE.sep hab, LE.sep hac => LE.sep $ hab.sup_right hac
    | inr a, inr b, inr c, LE.inr hba, LE.inr hca => LE.inr $ sup_le hba hca

instance instDistribLattice : DistribLattice (Booleanisation α) where
  inf_le_left _ _ := inf_le_left
  inf_le_right _ _ := inf_le_right
  le_inf _ _ _ := le_inf
  le_sup_inf x y z := match x, y, z with
    | inl a, inl b, inl c => LE.inl le_sup_inf
    | inl a, inl b, inr c => LE.inl $ by simp [sup_left_comm, sup_comm]
    | inl a, inr b, inl c => LE.inl $ by simp [sup_left_comm, sup_comm (a := b \ a)]
    | inl a, inr b, inr c => LE.inr $ by rw [sup_sdiff]
    | inr a, inl b, inl c => LE.inr $ by rw [sdiff_inf]
    | inr a, inl b, inr c => LE.inr $ by rw [sdiff_sdiff_right']
    | inr a, inr b, inl c => LE.inr $ by rw [sdiff_sdiff_right', sup_comm]
    | inr a, inr b, inr c => LE.inr inf_sup_left.le

-- The linter significantly hinders readability here.
set_option linter.unusedVariables false in
instance instBoundedOrder : BoundedOrder (Booleanisation α) where
  le_top x := match x with
    | inl a => LE.sep disjoint_bot_right
    | inr a => LE.inr bot_le
  bot_le x := match x with
    | inl a => LE.inl bot_le
    | inr a => LE.sep disjoint_bot_left

instance instBooleanAlgebra : BooleanAlgebra (Booleanisation α) where
  le_top _ := le_top
  bot_le _ := bot_le
  inf_compl_le_bot x := match x with
    | inl a => by simp
    | inr a => by simp
  top_le_sup_compl x := match x with
    | inl a => by simp
    | inr a => by simp
  sdiff_eq x y := match x, y with
    | inl a, inl b => by simp
    | inl a, inr b => by simp
    | inr a, inl b => by simp
    | inr a, inr b => by simp

/-- The embedding from a generalised Boolean algebra to its generated Boolean algebra. -/
def inlLatticeHom : LatticeHom α (Booleanisation α) where
  toFun := inl
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

lemma inlLatticeHom_injective : Injective (inlLatticeHom (α := α)) := Sum.inl_injective

end Booleanisation
