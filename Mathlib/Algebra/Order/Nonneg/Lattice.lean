/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.Nonneg.Order
public import Mathlib.Order.CompleteLatticeIntervals

/-!
# Lattice structures on the type of nonnegative elements

This file endows `Nonneg M` with the lattice structure inherited from `M`, up to and including the
`ConditionallyCompleteLinearOrderBot` structure.
-/

@[expose] public section
assert_not_exists Ring
assert_not_exists IsOrderedMonoid

open Set

variable {M : Type*}

namespace Nonneg
variable [Zero M]

theorem coe_image [LE M] {s : Set (Nonneg M)} :
    val '' s = {x : M | ∃ h : 0 ≤ x, ⟨x, h⟩ ∈ s} := by
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  exact ⟨by rintro ⟨⟨y, hy⟩, h, rfl⟩; exact ⟨hy, h⟩, fun ⟨h, hs⟩ ↦ ⟨⟨x, h⟩, hs, rfl⟩⟩

section Preorder
variable [Preorder M]

lemma monotone_val : Monotone (val : Nonneg M → M) := fun _ _ ↦ id

lemma strictMono_val : StrictMono (val : Nonneg M → M) := fun _ _ ↦ id

/-- The coercion `Nonneg M → M` as an order homomorphism. -/
@[simps] def valOrderHom : Nonneg M →o M := ⟨val, monotone_val⟩

/-- `Nonneg M` is order-isomorphic to the interval `Set.Ici 0` of `M`. -/
@[simps] def orderIsoIci : Nonneg M ≃o Ici (0 : M) where
  toFun a := ⟨a.val, a.val_nonneg⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := .rfl

@[simp] lemma range_val : Set.range (val : Nonneg M → M) = Ici 0 :=
  Set.ext fun _ ↦ ⟨fun ⟨a, ha⟩ ↦ ha ▸ a.val_nonneg, fun hx ↦ ⟨⟨_, hx⟩, rfl⟩⟩

instance orderBot : OrderBot (Nonneg M) where
  bot := ⟨0, le_rfl⟩
  bot_le a := a.val_nonneg

@[simp] theorem coe_bot : ((⊥ : Nonneg M) : M) = 0 := rfl

theorem bot_eq : (⊥ : Nonneg M) = ⟨0, le_rfl⟩ := rfl

instance instDenselyOrdered [DenselyOrdered M] : DenselyOrdered (Nonneg M) where
  dense a _ h := by
    obtain ⟨c, hac, hcb⟩ := exists_between (coe_lt_coe.2 h)
    exact ⟨⟨c, a.val_nonneg.trans hac.le⟩, hac, hcb⟩

end Preorder

instance noMaxOrder [PartialOrder M] [NoMaxOrder M] : NoMaxOrder (Nonneg M) where
  exists_gt a := let ⟨b, hb⟩ := exists_gt a.val; ⟨⟨b, a.val_nonneg.trans hb.le⟩, hb⟩

section SemilatticeSup
variable [SemilatticeSup M]

instance instMax : Max (Nonneg M) where
  max a b := ⟨a.val ⊔ b.val, le_sup_of_le_left a.val_nonneg⟩

@[simp, norm_cast]
theorem coe_sup (a b : Nonneg M) : ((a ⊔ b : Nonneg M) : M) = (a : M) ⊔ (b : M) := rfl

instance semilatticeSup : SemilatticeSup (Nonneg M) :=
  fast_instance% val_injective.semilatticeSup _ .rfl .rfl fun _ _ ↦ rfl

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf M]

instance instMin : Min (Nonneg M) where
  min a b := ⟨a.val ⊓ b.val, le_inf a.val_nonneg b.val_nonneg⟩

@[simp, norm_cast]
theorem coe_inf (a b : Nonneg M) : ((a ⊓ b : Nonneg M) : M) = (a : M) ⊓ (b : M) := rfl

instance semilatticeInf : SemilatticeInf (Nonneg M) :=
  fast_instance% val_injective.semilatticeInf _ .rfl .rfl fun _ _ ↦ rfl

end SemilatticeInf

instance lattice [Lattice M] : Lattice (Nonneg M) :=
  fast_instance% val_injective.lattice _ .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance distribLattice [DistribLattice M] : DistribLattice (Nonneg M) :=
  fast_instance% val_injective.distribLattice _ .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

section ConditionallyCompleteLinearOrder
variable [ConditionallyCompleteLinearOrder M] {s : Set (Nonneg M)}

open scoped Classical in
/-- The `sSup` of a set of nonnegative elements is its supremum in `M` when that supremum is a
nonnegative element, and `⊥` otherwise. This junk value is what makes `Nonneg M` a
`ConditionallyCompleteLinearOrderBot`. -/
noncomputable instance instSupSet : SupSet (Nonneg M) where
  sSup s := if h : s.Nonempty ∧ BddAbove s ∧ 0 ≤ sSup (val '' s) then ⟨_, h.2.2⟩ else ⊥

open scoped Classical in
/-- The `sInf` of a set of nonnegative elements is its infimum in `M` when that infimum is a
nonnegative element, and `⊥` otherwise. This junk value is what makes `Nonneg M` a
`ConditionallyCompleteLinearOrderBot`. -/
noncomputable instance instInfSet : InfSet (Nonneg M) where
  sInf s := if h : s.Nonempty ∧ BddBelow s ∧ 0 ≤ sInf (val '' s) then ⟨_, h.2.2⟩ else ⊥

private lemma zero_le_sSup_image (hs : s.Nonempty) (hb : BddAbove s) : 0 ≤ sSup (val '' s) :=
  let ⟨a, ha⟩ := hs
  a.val_nonneg.trans <| le_csSup (monotone_val.map_bddAbove hb) ⟨a, ha, rfl⟩

private lemma zero_le_sInf_image (hs : s.Nonempty) : 0 ≤ sInf (val '' s) :=
  le_csInf (hs.image _) <| by rintro _ ⟨a, -, rfl⟩; exact a.val_nonneg

@[simp, norm_cast]
lemma coe_sSup (hs : s.Nonempty) (hb : BddAbove s) :
    ((sSup s : Nonneg M) : M) = sSup (val '' s) :=
  congrArg val <| dite_eq_left (c := _) ⟨hs, hb, zero_le_sSup_image hs hb⟩

@[simp, norm_cast]
lemma coe_sInf (hs : s.Nonempty) (hb : BddBelow s) :
    ((sInf s : Nonneg M) : M) = sInf (val '' s) :=
  congrArg val <| dite_eq_left (c := _) ⟨hs, hb, zero_le_sInf_image hs⟩

lemma sSup_of_not_bddAbove (hb : ¬BddAbove s) : sSup s = ⊥ :=
  dite_eq_right fun h ↦ absurd h.2.1 hb

lemma sInf_of_not_bddBelow (hb : ¬BddBelow s) : sInf s = ⊥ :=
  dite_eq_right fun h ↦ absurd h.2.1 hb

lemma sSup_empty : sSup (∅ : Set (Nonneg M)) = ⊥ :=
  dite_eq_right fun h ↦ absurd rfl h.1.ne_empty

@[simp] lemma sInf_empty : sInf (∅ : Set (Nonneg M)) = ⊥ :=
  dite_eq_right fun h ↦ absurd rfl h.1.ne_empty

noncomputable instance conditionallyCompleteLinearOrderBot :
    ConditionallyCompleteLinearOrderBot (Nonneg M) := fast_instance%
  { instSupSet, instInfSet, DistribLattice.toLattice, orderBot, instLinearOrder with
    isLUB_csSup s hs hb := .of_image coe_le_coe <| by
      rw [coe_sSup hs hb]; exact isLUB_csSup (hs.image _) (monotone_val.map_bddAbove hb)
    isGLB_csInf s hs hb := .of_image coe_le_coe <| by
      rw [coe_sInf hs hb]; exact isGLB_csInf (hs.image _) (monotone_val.map_bddBelow hb)
    csSup_of_not_bddAbove _ hb := by rw [sSup_of_not_bddAbove hb, sSup_empty]
    csInf_of_not_bddBelow _ hb := absurd (OrderBot.bddBelow _) hb
    csSup_empty := sSup_empty }

end ConditionallyCompleteLinearOrder

end Nonneg
