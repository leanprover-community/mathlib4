/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Junyan Xu
-/
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Data.DFinsupp.Order
import Mathlib.Data.DFinsupp.NeLocus
import Mathlib.Order.WellFoundedSet

/-!
# Lexicographic order on finitely supported dependent functions

This file defines the lexicographic order on `DFinsupp`.
-/


variable {ι : Type*} {α : ι → Type*}

namespace DFinsupp

section Zero

variable [∀ i, Zero (α i)]

/-- `DFinsupp.Lex r s` is the lexicographic relation on `Π₀ i, α i`, where `ι` is ordered by `r`,
and `α i` is ordered by `s i`.
The type synonym `Lex (Π₀ i, α i)` has an order given by `DFinsupp.Lex (· < ·) (· < ·)`.
-/
protected def Lex (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop) (x y : Π₀ i, α i) : Prop :=
  Pi.Lex r (s _) x y

-- Porting note: Added `_root_` to match more closely with Lean 3. Also updated `s`'s type.
theorem _root_.Pi.lex_eq_dfinsupp_lex {r : ι → ι → Prop} {s : ∀ i, α i → α i → Prop}
    (a b : Π₀ i, α i) : Pi.Lex r (s _) (a : ∀ i, α i) b = DFinsupp.Lex r s a b :=
  rfl

-- Porting note: Updated `s`'s type.
theorem lex_def {r : ι → ι → Prop} {s : ∀ i, α i → α i → Prop} {a b : Π₀ i, α i} :
    DFinsupp.Lex r s a b ↔ ∃ j, (∀ d, r d j → a d = b d) ∧ s j (a j) (b j) :=
  Iff.rfl

instance [LT ι] [∀ i, LT (α i)] : LT (Lex (Π₀ i, α i)) :=
  ⟨fun f g ↦ DFinsupp.Lex (· < ·) (fun _ ↦ (· < ·)) (ofLex f) (ofLex g)⟩

theorem lex_lt_of_lt_of_preorder [∀ i, Preorder (α i)] (r) [IsStrictOrder ι r] {x y : Π₀ i, α i}
    (hlt : x < y) : ∃ i, (∀ j, r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i := by
  obtain ⟨hle, j, hlt⟩ := Pi.lt_def.1 hlt
  classical
  have : (x.neLocus y : Set ι).WellFoundedOn r := (x.neLocus y).finite_toSet.wellFoundedOn
  obtain ⟨i, hi, hl⟩ := this.has_min { i | x i < y i } ⟨⟨j, mem_neLocus.2 hlt.ne⟩, hlt⟩
  refine ⟨i, fun k hk ↦ ⟨hle k, ?_⟩, hi⟩
  exact of_not_not fun h ↦ hl ⟨k, mem_neLocus.2 (ne_of_not_le h).symm⟩ ((hle k).lt_of_not_le h) hk

theorem lex_lt_of_lt [∀ i, PartialOrder (α i)] (r) [IsStrictOrder ι r] {x y : Π₀ i, α i}
    (hlt : x < y) : Pi.Lex r (· < ·) x y := by
  simp_rw [Pi.Lex, le_antisymm_iff]
  exact lex_lt_of_lt_of_preorder r hlt

variable [LinearOrder ι]

instance Lex.isStrictOrder [∀ i, PartialOrder (α i)] :
    IsStrictOrder (Lex (Π₀ i, α i)) (· < ·) where
  irrefl _ := lt_irrefl (α := Lex (∀ i, α i)) _
  trans _ _ _ := lt_trans (α := Lex (∀ i, α i))

/-- The partial order on `DFinsupp`s obtained by the lexicographic ordering.
See `DFinsupp.Lex.linearOrder` for a proof that this partial order is in fact linear. -/
instance Lex.partialOrder [∀ i, PartialOrder (α i)] : PartialOrder (Lex (Π₀ i, α i)) where
  lt := (· < ·)
  le x y := ⇑(ofLex x) = ⇑(ofLex y) ∨ x < y
  __ := PartialOrder.lift (fun x : Lex (Π₀ i, α i) ↦ toLex (⇑(ofLex x)))
    (DFunLike.coe_injective (F := DFinsupp α))

section LinearOrder

variable [∀ i, LinearOrder (α i)]

/-- Auxiliary helper to case split computably. There is no need for this to be public, as it
can be written with `Or.by_cases` on `lt_trichotomy` once the instances below are constructed. -/
private def lt_trichotomy_rec {P : Lex (Π₀ i, α i) → Lex (Π₀ i, α i) → Sort*}
    (h_lt : ∀ {f g}, toLex f < toLex g → P (toLex f) (toLex g))
    (h_eq : ∀ {f g}, toLex f = toLex g → P (toLex f) (toLex g))
    (h_gt : ∀ {f g}, toLex g < toLex f → P (toLex f) (toLex g)) : ∀ f g, P f g :=
  Lex.rec fun f ↦ Lex.rec fun g ↦ match (motive := ∀ y, (f.neLocus g).min = y → _) _, rfl with
  | ⊤, h => h_eq (neLocus_eq_empty.mp <| Finset.min_eq_top.mp h)
  | (wit : ι), h => by
    apply (mem_neLocus.mp <| Finset.mem_of_min h).lt_or_lt.by_cases <;> intro hwit
    · exact h_lt ⟨wit, fun j hj ↦ not_mem_neLocus.mp (Finset.not_mem_of_lt_min hj h), hwit⟩
    · exact h_gt ⟨wit, fun j hj ↦
        not_mem_neLocus.mp (Finset.not_mem_of_lt_min hj <| by rwa [neLocus_comm]), hwit⟩

/-- The less-or-equal relation for the lexicographic ordering is decidable. -/
irreducible_def Lex.decidableLE : DecidableRel (α := Lex (Π₀ i, α i)) (· ≤ ·) :=
  lt_trichotomy_rec (fun h ↦ isTrue <| Or.inr h)
    (fun h ↦ isTrue <| Or.inl <| congr_arg _ h)
    fun h ↦ isFalse fun h' ↦ lt_irrefl _ (h.trans_le h')

/-- The less-than relation for the lexicographic ordering is decidable. -/
irreducible_def Lex.decidableLT : DecidableRel (α := Lex (Π₀ i, α i)) (· < ·) :=
  lt_trichotomy_rec (fun h ↦ isTrue h) (fun h ↦ isFalse h.not_lt) fun h ↦ isFalse h.asymm

-- Porting note: Added `DecidableEq` for `LinearOrder`.
instance : DecidableEq (Lex (Π₀ i, α i)) :=
  lt_trichotomy_rec (fun h ↦ isFalse fun h' ↦ h'.not_lt h) isTrue
    fun h ↦ isFalse fun h' ↦ h'.symm.not_lt h

/-- The linear order on `DFinsupp`s obtained by the lexicographic ordering. -/
instance Lex.linearOrder : LinearOrder (Lex (Π₀ i, α i)) where
  __ := Lex.partialOrder
  le_total := lt_trichotomy_rec (fun h ↦ Or.inl h.le) (fun h ↦ Or.inl h.le) fun h ↦ Or.inr h.le
  decidableLT := decidableLT
  decidableLE := decidableLE
  decidableEq := inferInstance

end LinearOrder

variable [∀ i, PartialOrder (α i)]

theorem toLex_monotone : Monotone (@toLex (Π₀ i, α i)) := by
  intro a b h
  refine le_of_lt_or_eq (or_iff_not_imp_right.2 fun hne ↦ ?_)
  classical
  exact ⟨Finset.min' _ (nonempty_neLocus_iff.2 hne),
    fun j hj ↦ not_mem_neLocus.1 fun h ↦ (Finset.min'_le _ _ h).not_lt hj,
    (h _).lt_of_ne (mem_neLocus.1 <| Finset.min'_mem _ _)⟩

theorem lt_of_forall_lt_of_lt (a b : Lex (Π₀ i, α i)) (i : ι) :
    (∀ j < i, ofLex a j = ofLex b j) → ofLex a i < ofLex b i → a < b :=
  fun h1 h2 ↦ ⟨i, h1, h2⟩

end Zero

section Covariants

variable [LinearOrder ι] [∀ i, AddMonoid (α i)] [∀ i, LinearOrder (α i)]

/-!  We are about to sneak in a hypothesis that might appear to be too strong.
We assume `AddLeftStrictMono` (covariant with *strict* inequality `<`) also when proving the one
with the *weak* inequality `≤`. This is actually necessary: addition on `Lex (Π₀ i, α i)` may fail
to be monotone, when it is "just" monotone on `α i`. -/


section Left

variable [∀ i, AddLeftStrictMono (α i)]

instance Lex.addLeftStrictMono : AddLeftStrictMono (Lex (Π₀ i, α i)) :=
  ⟨fun _ _ _ ⟨a, lta, ha⟩ ↦ ⟨a, fun j ja ↦ congr_arg _ (lta j ja), add_lt_add_left ha _⟩⟩

instance Lex.addLeftMono : AddLeftMono (Lex (Π₀ i, α i)) :=
  addLeftMono_of_addLeftStrictMono _

end Left

section Right

variable [∀ i, AddRightStrictMono (α i)]

instance Lex.addRightStrictMono : AddRightStrictMono (Lex (Π₀ i, α i)) :=
  ⟨fun f _ _ ⟨a, lta, ha⟩ ↦
    ⟨a, fun j ja ↦ congr_arg (· + ofLex f j) (lta j ja), add_lt_add_right ha _⟩⟩

instance Lex.addRightMono : AddRightMono (Lex (Π₀ i, α i)) :=
  addRightMono_of_addRightStrictMono _

end Right

end Covariants

section OrderedAddMonoid

variable [LinearOrder ι]

instance Lex.orderBot [∀ i, CanonicallyOrderedAddCommMonoid (α i)] :
    OrderBot (Lex (Π₀ i, α i)) where
  bot := 0
  bot_le _ := DFinsupp.toLex_monotone bot_le

instance Lex.orderedAddCancelCommMonoid [∀ i, OrderedCancelAddCommMonoid (α i)] :
    OrderedCancelAddCommMonoid (Lex (Π₀ i, α i)) where
  add_le_add_left _ _ h _ := add_le_add_left (α := Lex (∀ i, α i)) h _
  le_of_add_le_add_left _ _ _ := le_of_add_le_add_left (α := Lex (∀ i, α i))

instance Lex.orderedAddCommGroup [∀ i, OrderedAddCommGroup (α i)] :
    OrderedAddCommGroup (Lex (Π₀ i, α i)) where
  add_le_add_left _ _ := add_le_add_left

instance Lex.linearOrderedCancelAddCommMonoid
    [∀ i, LinearOrderedCancelAddCommMonoid (α i)] :
    LinearOrderedCancelAddCommMonoid (Lex (Π₀ i, α i)) where
  __ : LinearOrder (Lex (Π₀ i, α i)) := inferInstance
  __ : OrderedCancelAddCommMonoid (Lex (Π₀ i, α i)) := inferInstance

instance Lex.linearOrderedAddCommGroup [∀ i, LinearOrderedAddCommGroup (α i)] :
    LinearOrderedAddCommGroup (Lex (Π₀ i, α i)) where
  __ : LinearOrder (Lex (Π₀ i, α i)) := inferInstance
  add_le_add_left _ _ := add_le_add_left

end OrderedAddMonoid

end DFinsupp
