/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.PropInstances
public import Mathlib.Order.GaloisConnection.Defs

/-!
# Heyting algebras

This file defines Heyting, co-Heyting and bi-Heyting algebras.

A Heyting algebra is a bounded distributive lattice with an implication operation `⇨` such that
`a ≤ b ⇨ c ↔ a ⊓ b ≤ c`. It also comes with a pseudo-complement `ᶜ`, such that `aᶜ = a ⇨ ⊥`.

Co-Heyting algebras are dual to Heyting algebras. They have a difference `\` and a negation `￢`
such that `a \ b ≤ c ↔ a ≤ b ⊔ c` and `￢a = ⊤ \ a`.

Bi-Heyting algebras are Heyting algebras that are also co-Heyting algebras.

From a logic standpoint, Heyting algebras precisely model intuitionistic logic, whereas Boolean
algebras model classical logic.

Heyting algebras are the order-theoretic equivalent of Cartesian closed categories.

## Main declarations

* `GeneralizedHeytingAlgebra`: Heyting algebra without a top element (nor negation).
* `GeneralizedCoheytingAlgebra`: Co-Heyting algebra without a bottom element (nor complement).
* `HeytingAlgebra`: Heyting algebra.
* `CoheytingAlgebra`: Co-Heyting algebra.
* `BiheytingAlgebra`: Bi-Heyting algebra.

## References

* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]

## Tags

Heyting, Brouwer, algebra, implication, negation, intuitionistic
-/

@[expose] public section

assert_not_exists RelIso

open Function OrderDual

universe u

variable {ι α β : Type*}

/-! ### Notation -/

section
variable (α β)

instance Prod.instHImp [HImp α] [HImp β] : HImp (α × β) :=
  ⟨fun a b => (a.1 ⇨ b.1, a.2 ⇨ b.2)⟩

@[to_dual]
instance Prod.instHNot [HNot α] [HNot β] : HNot (α × β) :=
  ⟨fun a => (￢a.1, ￢a.2)⟩

@[to_dual existing]
instance Prod.instSDiff [SDiff α] [SDiff β] : SDiff (α × β) :=
  ⟨fun a b => (a.1 \ b.1, a.2 \ b.2)⟩

end

@[to_dual (attr := simp)]
theorem fst_himp [HImp α] [HImp β] (a b : α × β) : (a ⇨ b).1 = a.1 ⇨ b.1 :=
  rfl

@[to_dual (attr := simp)]
theorem snd_himp [HImp α] [HImp β] (a b : α × β) : (a ⇨ b).2 = a.2 ⇨ b.2 :=
  rfl

@[to_dual (attr := simp)]
theorem fst_hnot [HNot α] [HNot β] (a : α × β) : (￢a).1 = ￢a.1 :=
  rfl

@[to_dual (attr := simp)]
theorem snd_hnot [HNot α] [HNot β] (a : α × β) : (￢a).2 = ￢a.2 :=
  rfl

/-- A generalized Heyting algebra is a lattice with an additional binary operation `⇨` called
Heyting implication such that `(a ⇨ ·)` is right adjoint to `(a ⊓ ·)`.

This generalizes `HeytingAlgebra` by not requiring a bottom element. -/
class GeneralizedHeytingAlgebra (α : Type*) extends Lattice α, OrderTop α, HImp α where
  /-- `(a ⇨ ·)` is right adjoint to `(a ⊓ ·)` -/
  le_himp_iff (a b c : α) : a ≤ b ⇨ c ↔ a ⊓ b ≤ c

/-- A generalized co-Heyting algebra is a lattice with an additional binary
difference operation `\` such that `(· \ a)` is left adjoint to `(· ⊔ a)`.

This generalizes `CoheytingAlgebra` by not requiring a top element. -/
@[to_dual]
class GeneralizedCoheytingAlgebra (α : Type*) extends Lattice α, OrderBot α, SDiff α where
  /-- `(· \ a)` is left adjoint to `(· ⊔ a)` -/
  sdiff_le_iff (a b c : α) : a \ b ≤ c ↔ a ≤ b ⊔ c

/-- A Heyting algebra is a bounded lattice with an additional binary operation `⇨` called Heyting
implication such that `(a ⇨ ·)` is right adjoint to `(a ⊓ ·)`. -/
class HeytingAlgebra (α : Type*) extends GeneralizedHeytingAlgebra α, OrderBot α, Compl α where
  /-- `aᶜ` is defined as `a ⇨ ⊥` -/
  himp_bot (a : α) : a ⇨ ⊥ = aᶜ

/-- A co-Heyting algebra is a bounded lattice with an additional binary difference operation `\`
such that `(· \ a)` is left adjoint to `(· ⊔ a)`. -/
@[to_dual]
class CoheytingAlgebra (α : Type*) extends GeneralizedCoheytingAlgebra α, OrderTop α, HNot α where
  /-- `⊤ \ a` is `￢a` -/
  top_sdiff (a : α) : ⊤ \ a = ￢a

/-- A bi-Heyting algebra is a Heyting algebra that is also a co-Heyting algebra. -/
class BiheytingAlgebra (α : Type*) extends HeytingAlgebra α, CoheytingAlgebra α where

attribute [to_dual existing] BiheytingAlgebra.toHeytingAlgebra

-- See note [lower instance priority]
attribute [instance 100] GeneralizedHeytingAlgebra.toOrderTop
attribute [instance 100] GeneralizedCoheytingAlgebra.toOrderBot

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) HeytingAlgebra.toBoundedOrder [HeytingAlgebra α] : BoundedOrder α where

-- See note [reducible non-instances]
/-- Construct a Heyting algebra from the lattice structure and Heyting implication alone. -/
abbrev HeytingAlgebra.ofHImp [DistribLattice α] [BoundedOrder α] (himp : α → α → α)
    (le_himp_iff : ∀ a b c, a ≤ himp b c ↔ a ⊓ b ≤ c) : HeytingAlgebra α :=
  { ‹DistribLattice α›, ‹BoundedOrder α› with
    himp,
    compl := fun a => himp a ⊥,
    le_himp_iff,
    himp_bot := fun _ => rfl }

-- See note [reducible non-instances]
/-- Construct a Heyting algebra from the lattice structure and complement operator alone. -/
abbrev HeytingAlgebra.ofCompl [DistribLattice α] [BoundedOrder α] (compl : α → α)
    (le_himp_iff : ∀ a b c, a ≤ compl b ⊔ c ↔ a ⊓ b ≤ c) : HeytingAlgebra α where
  himp := (compl · ⊔ ·)
  compl := compl
  le_himp_iff := le_himp_iff
  himp_bot _ := sup_bot_eq _

-- See note [reducible non-instances]
/-- Construct a co-Heyting algebra from the lattice structure and the difference alone. -/
abbrev CoheytingAlgebra.ofSDiff [DistribLattice α] [BoundedOrder α] (sdiff : α → α → α)
    (sdiff_le_iff : ∀ a b c, sdiff a b ≤ c ↔ a ≤ b ⊔ c) : CoheytingAlgebra α :=
  { ‹DistribLattice α›, ‹BoundedOrder α› with
    sdiff,
    hnot := fun a => sdiff ⊤ a,
    sdiff_le_iff,
    top_sdiff := fun _ => rfl }

-- See note [reducible non-instances]
/-- Construct a co-Heyting algebra from the difference and Heyting negation alone. -/
abbrev CoheytingAlgebra.ofHNot [DistribLattice α] [BoundedOrder α] (hnot : α → α)
    (sdiff_le_iff : ∀ a b c, a ⊓ hnot b ≤ c ↔ a ≤ b ⊔ c) : CoheytingAlgebra α where
  sdiff a b := a ⊓ hnot b
  hnot := hnot
  sdiff_le_iff := sdiff_le_iff
  top_sdiff _ := top_inf_eq _

/-! In this section, we'll give interpretations of these results in the Heyting algebra model of
intuitionistic logic,- where `≤` can be interpreted as "validates", `⇨` as "implies", `⊓` as "and",
`⊔` as "or", `⊥` as "false" and `⊤` as "true". Note that we confuse `→` and `⊢` because those are
the same in this logic.

See also `Prop.heytingAlgebra`. -/
section GeneralizedHeytingAlgebra

@[simp]
theorem sdiff_le_iff [GeneralizedCoheytingAlgebra α] {a b c : α} : a \ b ≤ c ↔ a ≤ b ⊔ c :=
  GeneralizedCoheytingAlgebra.sdiff_le_iff _ _ _

theorem sdiff_le_iff' [GeneralizedCoheytingAlgebra α] {a b c : α} : a \ b ≤ c ↔ a ≤ c ⊔ b := by
  rw [sdiff_le_iff, sup_comm]

variable [GeneralizedHeytingAlgebra α] {a b c d : α}

/-- `p → q → r ↔ p ∧ q → r` -/
@[to_dual existing sdiff_le_iff', simp]
theorem le_himp_iff : a ≤ b ⇨ c ↔ a ⊓ b ≤ c :=
  GeneralizedHeytingAlgebra.le_himp_iff _ _ _

/-- `p → q → r ↔ q ∧ p → r` -/
@[to_dual existing sdiff_le_iff]
theorem le_himp_iff' : a ≤ b ⇨ c ↔ b ⊓ a ≤ c := by rw [le_himp_iff, inf_comm]

/-- `p → q → r ↔ q → p → r` -/
@[to_dual sdiff_le_comm]
theorem le_himp_comm : a ≤ b ⇨ c ↔ b ≤ a ⇨ c := by rw [le_himp_iff, le_himp_iff']

/-- `p → q → p` -/
@[to_dual sdiff_le]
theorem le_himp : a ≤ b ⇨ a :=
  le_himp_iff.2 inf_le_left

/-- `p → p → q ↔ p → q` -/
@[to_dual sdiff_le_iff_left]
theorem le_himp_iff_left : a ≤ a ⇨ b ↔ a ≤ b := by rw [le_himp_iff, inf_idem]

/-- `p → p` -/
@[to_dual (attr := simp)]
theorem himp_self : a ⇨ a = ⊤ :=
  top_le_iff.1 <| le_himp_iff.2 inf_le_right

/-- `(p → q) ∧ p → q` -/
@[to_dual le_sdiff_sup]
theorem himp_inf_le : (a ⇨ b) ⊓ a ≤ b :=
  le_himp_iff.1 le_rfl

/-- `p ∧ (p → q) → q` -/
@[to_dual le_sup_sdiff]
theorem inf_himp_le : a ⊓ (a ⇨ b) ≤ b := by rw [inf_comm, ← le_himp_iff]

/-- `p ∧ (p → q) ↔ p ∧ q` -/
@[to_dual (attr := simp) sup_sdiff_self]
-- TODO: Should this be renamed to `inf_himp_self`?
theorem inf_himp (a b : α) : a ⊓ (a ⇨ b) = a ⊓ b :=
  le_antisymm (le_inf inf_le_left <| by rw [inf_comm, ← le_himp_iff]) <| inf_le_inf_left _ le_himp

/-- `(p → q) ∧ p ↔ q ∧ p` -/
@[to_dual (attr := simp)]
theorem himp_inf_self (a b : α) : (a ⇨ b) ⊓ a = b ⊓ a := by rw [inf_comm, inf_himp, inf_comm]

/-- The **deduction theorem** in the Heyting algebra model of intuitionistic logic:
an implication holds iff the conclusion follows from the hypothesis. -/
@[to_dual (attr := simp)]
theorem himp_eq_top_iff : a ⇨ b = ⊤ ↔ a ≤ b := by rw [← top_le_iff, le_himp_iff, top_inf_eq]

/-- `p → true` -/
@[to_dual (attr := simp) bot_sdiff]
theorem himp_top : a ⇨ ⊤ = ⊤ :=
  himp_eq_top_iff.2 le_top

/-- `true → p ↔ p` -/
@[to_dual (attr := simp) sdiff_bot]
theorem top_himp : ⊤ ⇨ a = a :=
  eq_of_forall_le_iff fun b => by rw [le_himp_iff, inf_top_eq]

/-- `p → q → r ↔ p ∧ q → r` -/
@[to_dual none]
theorem himp_himp (a b c : α) : a ⇨ b ⇨ c = a ⊓ b ⇨ c :=
  eq_of_forall_le_iff fun d => by simp_rw [le_himp_iff, inf_assoc]

/-- `(q → r) → (p → q) → q → r` -/
@[to_dual none]
theorem himp_le_himp_himp_himp : b ⇨ c ≤ (a ⇨ b) ⇨ a ⇨ c := by
  rw [le_himp_iff, le_himp_iff, inf_assoc, himp_inf_self, ← inf_assoc, himp_inf_self, inf_assoc]
  exact inf_le_left

@[simp, to_dual none]
theorem himp_inf_himp_inf_le : (b ⇨ c) ⊓ (a ⇨ b) ⊓ a ≤ c := by
  simpa using @himp_le_himp_himp_himp

/-- `p → q → r ↔ q → p → r` -/
@[to_dual (reorder := a c) sdiff_right_comm]
theorem himp_left_comm (a b c : α) : a ⇨ b ⇨ c = b ⇨ a ⇨ c := by simp_rw [himp_himp, inf_comm]

@[to_dual (attr := simp)]
theorem himp_idem : b ⇨ b ⇨ a = b ⇨ a := by rw [himp_himp, inf_idem]

@[to_dual sup_sdiff_distrib]
theorem himp_inf_distrib (a b c : α) : a ⇨ b ⊓ c = (a ⇨ b) ⊓ (a ⇨ c) :=
  eq_of_forall_le_iff fun d => by simp_rw [le_himp_iff, le_inf_iff, le_himp_iff]

@[to_dual sdiff_inf_distrib]
theorem sup_himp_distrib (a b c : α) : a ⊔ b ⇨ c = (a ⇨ c) ⊓ (b ⇨ c) :=
  eq_of_forall_le_iff fun d => by
    rw [le_inf_iff, le_himp_comm, sup_le_iff]
    simp_rw [le_himp_comm]

@[to_dual sdiff_le_sdiff_right]
theorem himp_le_himp_left (h : a ≤ b) : c ⇨ a ≤ c ⇨ b :=
  le_himp_iff.2 <| himp_inf_le.trans h

@[to_dual sdiff_le_sdiff_left]
theorem himp_le_himp_right (h : a ≤ b) : b ⇨ c ≤ a ⇨ c :=
  le_himp_iff.2 <| (inf_le_inf_left _ h).trans himp_inf_le

@[to_dual (attr := gcongr)]
theorem himp_le_himp (hab : a ≤ b) (hcd : c ≤ d) : b ⇨ c ≤ a ⇨ d :=
  (himp_le_himp_right hab).trans <| himp_le_himp_left hcd

@[to_dual (attr := simp) sdiff_inf_self_left]
theorem sup_himp_self_left (a b : α) : a ⊔ b ⇨ a = b ⇨ a := by
  rw [sup_himp_distrib, himp_self, top_inf_eq]

@[to_dual (attr := simp) sdiff_inf_self_right]
theorem sup_himp_self_right (a b : α) : a ⊔ b ⇨ b = a ⇨ b := by
  rw [sup_himp_distrib, himp_self, inf_top_eq]

@[to_dual sdiff_eq_left]
theorem Codisjoint.himp_eq_right (h : Codisjoint a b) : b ⇨ a = a := by
  conv_rhs => rw [← @top_himp _ _ a]
  rw [← h.eq_top, sup_himp_self_left]

@[to_dual sdiff_eq_right]
theorem Codisjoint.himp_eq_left (h : Codisjoint a b) : a ⇨ b = b :=
  h.symm.himp_eq_right

@[to_dual sup_sdiff_cancel_right]
theorem Codisjoint.himp_inf_cancel_right (h : Codisjoint a b) : a ⇨ a ⊓ b = b := by
  rw [himp_inf_distrib, himp_self, top_inf_eq, h.himp_eq_left]

@[to_dual sup_sdiff_cancel_left]
theorem Codisjoint.himp_inf_cancel_left (h : Codisjoint a b) : b ⇨ a ⊓ b = a := by
  rw [himp_inf_distrib, himp_self, inf_top_eq, h.himp_eq_right]

/-- See `himp_le` for a stronger version in Boolean algebras. -/
@[to_dual le_sdiff_of_le_left
/-- See `le_sdiff` for a stronger version in generalised Boolean algebras. -/]
theorem Codisjoint.himp_le_of_right_le (hac : Codisjoint a c) (hba : b ≤ a) : c ⇨ b ≤ a :=
  (himp_le_himp_left hba).trans_eq hac.himp_eq_right

@[to_dual sdiff_sdiff_le]
theorem le_himp_himp : a ≤ (a ⇨ b) ⇨ b :=
  le_himp_iff.2 inf_himp_le

@[to_dual (attr := simp)]
lemma himp_eq_himp_iff : b ⇨ a = a ⇨ b ↔ a = b := by simp [le_antisymm_iff]

@[to_dual]
lemma himp_ne_himp_iff : b ⇨ a ≠ a ⇨ b ↔ a ≠ b := himp_eq_himp_iff.not

@[to_dual none]
theorem himp_triangle (a b c : α) : (a ⇨ b) ⊓ (b ⇨ c) ≤ a ⇨ c := by
  rw [le_himp_iff, inf_right_comm, ← le_himp_iff]
  exact himp_inf_le.trans le_himp_himp

@[to_dual none]
theorem himp_inf_himp_cancel (hba : b ≤ a) (hcb : c ≤ b) : (a ⇨ b) ⊓ (b ⇨ c) = a ⇨ c :=
  (himp_triangle _ _ _).antisymm <| le_inf (himp_le_himp_left hcb) (himp_le_himp_right hba)

-- @[to_dual gc_sdiff_sup]
theorem gc_inf_himp : GaloisConnection (a ⊓ ·) (a ⇨ ·) :=
  fun _ _ ↦ Iff.symm le_himp_iff'

-- See note [lower instance priority]
instance (priority := 100) GeneralizedHeytingAlgebra.toDistribLattice : DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => by
    simp_rw [inf_comm a, ← le_himp_iff, sup_le_iff, le_himp_iff, ← sup_le_iff]; rfl

instance OrderDual.instGeneralizedCoheytingAlgebra : GeneralizedCoheytingAlgebra αᵒᵈ where
  sdiff a b := toDual (ofDual b ⇨ ofDual a)
  sdiff_le_iff a b c := by rw [sup_comm]; exact le_himp_iff

instance Prod.instGeneralizedHeytingAlgebra [GeneralizedHeytingAlgebra β] :
    GeneralizedHeytingAlgebra (α × β) where
  le_himp_iff _ _ _ := and_congr le_himp_iff le_himp_iff

instance Pi.instGeneralizedHeytingAlgebra {α : ι → Type*} [∀ i, GeneralizedHeytingAlgebra (α i)] :
    GeneralizedHeytingAlgebra (∀ i, α i) where
  le_himp_iff i := by simp [le_def]

end GeneralizedHeytingAlgebra

section GeneralizedCoheytingAlgebra

variable [GeneralizedCoheytingAlgebra α] {a b c d : α}

@[to_dual none]
theorem Disjoint.disjoint_sdiff_left (h : Disjoint a b) : Disjoint (a \ c) b :=
  h.mono_left sdiff_le

@[to_dual none]
theorem Disjoint.disjoint_sdiff_right (h : Disjoint a b) : Disjoint a (b \ c) :=
  h.mono_right sdiff_le

@[to_dual none]
theorem sup_sdiff_left : a ⊔ a \ b = a :=
  sup_of_le_left sdiff_le

@[to_dual none]
theorem sup_sdiff_right : a \ b ⊔ a = a :=
  sup_of_le_right sdiff_le

@[to_dual none]
theorem inf_sdiff_left : a \ b ⊓ a = a \ b :=
  inf_of_le_left sdiff_le

@[to_dual none]
theorem inf_sdiff_right : a ⊓ a \ b = a \ b :=
  inf_of_le_right sdiff_le

@[to_dual none]
alias sup_sdiff_self_left := sdiff_sup_self

@[to_dual none]
alias sup_sdiff_self_right := sup_sdiff_self

@[to_dual none]
theorem sup_sdiff_eq_sup (h : c ≤ a) : a ⊔ b \ c = a ⊔ b :=
  sup_congr_left (sdiff_le.trans le_sup_right) <| le_sup_sdiff.trans <| sup_le_sup_right h _

-- cf. `Set.union_diff_cancel'`
@[to_dual none]
theorem sup_sdiff_cancel' (hab : a ≤ b) (hbc : b ≤ c) : b ⊔ c \ a = c := by
  rw [sup_sdiff_eq_sup hab, sup_of_le_right hbc]

@[to_dual none]
theorem sup_sdiff_cancel_right (h : a ≤ b) : a ⊔ b \ a = b :=
  sup_sdiff_cancel' le_rfl h

@[to_dual none]
theorem sdiff_sup_cancel (h : b ≤ a) : a \ b ⊔ b = a := by rw [sup_comm, sup_sdiff_cancel_right h]

@[to_dual none]
theorem sup_le_of_le_sdiff_left (h : b ≤ c \ a) (hac : a ≤ c) : a ⊔ b ≤ c :=
  sup_le hac <| h.trans sdiff_le

@[to_dual none]
theorem sup_le_of_le_sdiff_right (h : a ≤ c \ b) (hbc : b ≤ c) : a ⊔ b ≤ c :=
  sup_le (h.trans sdiff_le) hbc

@[to_dual none]
theorem sdiff_sdiff_sdiff_le_sdiff : (a \ b) \ (a \ c) ≤ c \ b := by
  rw [sdiff_le_iff, sdiff_le_iff, sup_left_comm, sup_sdiff_self, sup_left_comm, sdiff_sup_self,
    sup_left_comm]
  exact le_sup_left

@[simp, to_dual none]
theorem le_sup_sdiff_sup_sdiff : a ≤ b ⊔ (a \ c ⊔ c \ b) := by
  simpa using @sdiff_sdiff_sdiff_le_sdiff

@[to_dual none]
theorem sdiff_sdiff (a b c : α) : (a \ b) \ c = a \ (b ⊔ c) :=
  eq_of_forall_ge_iff fun d => by simp_rw [sdiff_le_iff, sup_assoc]

@[to_dual none]
theorem sdiff_sdiff_left : (a \ b) \ c = a \ (b ⊔ c) :=
  sdiff_sdiff _ _ _

@[to_dual none]
theorem sdiff_sdiff_comm : (a \ b) \ c = (a \ c) \ b :=
  sdiff_right_comm _ _ _

@[simp, to_dual none]
theorem sdiff_sdiff_self : (a \ b) \ a = ⊥ := by rw [sdiff_sdiff_comm, sdiff_self, bot_sdiff]

@[to_dual none]
theorem sup_sdiff : (a ⊔ b) \ c = a \ c ⊔ b \ c :=
  sup_sdiff_distrib _ _ _

@[simp, to_dual none]
theorem sup_sdiff_right_self : (a ⊔ b) \ b = a \ b := by rw [sup_sdiff, sdiff_self, sup_bot_eq]

@[simp, to_dual none]
theorem sup_sdiff_left_self : (a ⊔ b) \ a = b \ a := by rw [sup_comm, sup_sdiff_right_self]

-- cf. `IsCompl.inf_sup`
@[to_dual none]
theorem sdiff_inf : a \ (b ⊓ c) = a \ b ⊔ a \ c :=
  sdiff_inf_distrib _ _ _

@[to_dual none]
theorem sdiff_triangle (a b c : α) : a \ c ≤ a \ b ⊔ b \ c := by
  rw [sdiff_le_iff, sup_left_comm, ← sdiff_le_iff]
  exact sdiff_sdiff_le.trans le_sup_sdiff

@[to_dual none]
theorem sdiff_sup_sdiff_cancel (hba : b ≤ a) (hcb : c ≤ b) : a \ b ⊔ b \ c = a \ c :=
  (sdiff_triangle _ _ _).antisymm' <| sup_le (sdiff_le_sdiff_left hcb) (sdiff_le_sdiff_right hba)

/-- a version of `sdiff_sup_sdiff_cancel` with more general hypotheses. -/
@[to_dual none]
theorem sdiff_sup_sdiff_cancel' (hinf : a ⊓ c ≤ b) (hsup : b ≤ a ⊔ c) :
    a \ b ⊔ b \ c = a \ c := by
  refine (sdiff_triangle ..).antisymm' <| sup_le ?_ <| by simpa [sup_comm]
  rw [← sdiff_inf_self_left (b := c)]
  exact sdiff_le_sdiff_left hinf

@[to_dual none]
theorem sdiff_le_sdiff_of_sup_le_sup_left (h : c ⊔ a ≤ c ⊔ b) : a \ c ≤ b \ c := by
  rw [← sup_sdiff_left_self, ← @sup_sdiff_left_self _ _ _ b]
  exact sdiff_le_sdiff_right h

@[to_dual none]
theorem sdiff_le_sdiff_of_sup_le_sup_right (h : a ⊔ c ≤ b ⊔ c) : a \ c ≤ b \ c := by
  rw [← sup_sdiff_right_self, ← @sup_sdiff_right_self _ _ b]
  exact sdiff_le_sdiff_right h

@[simp, to_dual none]
theorem inf_sdiff_sup_left : a \ c ⊓ (a ⊔ b) = a \ c :=
  inf_of_le_left <| sdiff_le.trans le_sup_left

@[simp, to_dual none]
theorem inf_sdiff_sup_right : a \ c ⊓ (b ⊔ a) = a \ c :=
  inf_of_le_left <| sdiff_le.trans le_sup_right

theorem gc_sdiff_sup : GaloisConnection (· \ a) (a ⊔ ·) :=
  fun _ _ ↦ sdiff_le_iff

-- See note [lower instance priority]
@[to_dual existing]
instance (priority := 100) GeneralizedCoheytingAlgebra.toDistribLattice : DistribLattice α :=
  { ‹GeneralizedCoheytingAlgebra α› with
    le_sup_inf :=
      fun a b c => by simp_rw [← sdiff_le_iff, le_inf_iff, sdiff_le_iff, ← le_inf_iff]; rfl }

@[to_dual existing]
instance OrderDual.instGeneralizedHeytingAlgebra : GeneralizedHeytingAlgebra αᵒᵈ where
  himp := fun a b => toDual (ofDual b \ ofDual a)
  le_himp_iff := fun a b c => by rw [inf_comm]; exact sdiff_le_iff

@[to_dual existing]
instance Prod.instGeneralizedCoheytingAlgebra [GeneralizedCoheytingAlgebra β] :
    GeneralizedCoheytingAlgebra (α × β) where
  sdiff_le_iff _ _ _ := and_congr sdiff_le_iff sdiff_le_iff

@[to_dual existing]
instance Pi.instGeneralizedCoheytingAlgebra {α : ι → Type*}
    [∀ i, GeneralizedCoheytingAlgebra (α i)] : GeneralizedCoheytingAlgebra (∀ i, α i) where
  sdiff_le_iff i := by simp [le_def]

end GeneralizedCoheytingAlgebra

section HeytingAlgebra

variable [HeytingAlgebra α] {a b : α}

@[to_dual (attr := simp) top_sdiff']
theorem himp_bot (a : α) : a ⇨ ⊥ = aᶜ :=
  HeytingAlgebra.himp_bot _

@[to_dual (attr := simp) sdiff_top]
theorem bot_himp (a : α) : ⊥ ⇨ a = ⊤ :=
  himp_eq_top_iff.2 bot_le

@[to_dual]
theorem compl_sup_distrib (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ := by
  simp_rw [← himp_bot, sup_himp_distrib]

@[to_dual (attr := simp)]
theorem compl_sup : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ :=
  compl_sup_distrib _ _

@[to_dual sdiff_le_hnot]
theorem compl_le_himp : aᶜ ≤ a ⇨ b :=
  (himp_bot _).ge.trans <| himp_le_himp_left bot_le

@[to_dual none]
theorem compl_sup_le_himp : aᶜ ⊔ b ≤ a ⇨ b :=
  sup_le compl_le_himp le_himp

@[to_dual sdiff_le_inf_hnot]
theorem sup_compl_le_himp : b ⊔ aᶜ ≤ a ⇨ b :=
  sup_le le_himp compl_le_himp

-- `p → ¬ p ↔ ¬ p`
@[to_dual (attr := simp) hnot_sdiff]
theorem himp_compl (a : α) : a ⇨ aᶜ = aᶜ := by rw [← himp_bot, himp_himp, inf_idem]

-- `p → ¬ q ↔ q → ¬ p`
@[to_dual (reorder := a b) hnot_sdiff_comm]
theorem himp_compl_comm (a b : α) : a ⇨ bᶜ = b ⇨ aᶜ := by simp_rw [← himp_bot, himp_left_comm]

@[to_dual hnot_le_iff_codisjoint_left]
theorem le_compl_iff_disjoint_right : a ≤ bᶜ ↔ Disjoint a b := by
  rw [← himp_bot, le_himp_iff, disjoint_iff_inf_le]

@[to_dual hnot_le_iff_codisjoint_right]
theorem le_compl_iff_disjoint_left : a ≤ bᶜ ↔ Disjoint b a :=
  le_compl_iff_disjoint_right.trans disjoint_comm

@[to_dual hnot_le_comm]
theorem le_compl_comm : a ≤ bᶜ ↔ b ≤ aᶜ := by
  rw [le_compl_iff_disjoint_right, le_compl_iff_disjoint_left]

@[to_dual hnot_le_left]
alias ⟨_, Disjoint.le_compl_right⟩ := le_compl_iff_disjoint_right

@[to_dual hnot_le_right]
alias ⟨_, Disjoint.le_compl_left⟩ := le_compl_iff_disjoint_left

@[to_dual hnot_le_iff_hnot_le]
alias le_compl_iff_le_compl := le_compl_comm

@[to_dual hnot_le_of_hnot_le]
alias ⟨le_compl_of_le_compl, _⟩ := le_compl_comm

@[to_dual]
theorem disjoint_compl_left : Disjoint aᶜ a :=
  disjoint_iff_inf_le.mpr <| le_himp_iff.1 (himp_bot _).ge

@[to_dual]
theorem disjoint_compl_right : Disjoint a aᶜ :=
  disjoint_compl_left.symm

@[to_dual]
theorem LE.le.disjoint_compl_left (h : b ≤ a) : Disjoint aᶜ b :=
  _root_.disjoint_compl_left.mono_right h

@[to_dual]
theorem LE.le.disjoint_compl_right (h : a ≤ b) : Disjoint a bᶜ :=
  _root_.disjoint_compl_right.mono_left h

@[to_dual]
theorem IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b :=
  h.1.le_compl_left.antisymm' <| Disjoint.le_of_codisjoint disjoint_compl_left h.2

@[to_dual]
theorem IsCompl.eq_compl (h : IsCompl a b) : a = bᶜ :=
  h.1.le_compl_right.antisymm <| Disjoint.le_of_codisjoint disjoint_compl_left h.2.symm

@[to_dual none]
theorem compl_unique (h₀ : a ⊓ b = ⊥) (h₁ : a ⊔ b = ⊤) : aᶜ = b :=
  (IsCompl.of_eq h₀ h₁).compl_eq

@[to_dual (attr := simp)]
theorem inf_compl_self (a : α) : a ⊓ aᶜ = ⊥ :=
  disjoint_compl_right.eq_bot

@[to_dual (attr := simp)]
theorem compl_inf_self (a : α) : aᶜ ⊓ a = ⊥ :=
  disjoint_compl_left.eq_bot

@[to_dual]
theorem inf_compl_eq_bot : a ⊓ aᶜ = ⊥ :=
  inf_compl_self _

@[to_dual]
theorem compl_inf_eq_bot : aᶜ ⊓ a = ⊥ :=
  compl_inf_self _

@[to_dual (attr := simp)]
theorem compl_top : (⊤ : α)ᶜ = ⊥ :=
  eq_of_forall_le_iff fun a => by rw [le_compl_iff_disjoint_right, disjoint_top, le_bot_iff]

@[to_dual (attr := simp)]
theorem compl_bot : (⊥ : α)ᶜ = ⊤ := by rw [← himp_bot, himp_self]

@[to_dual (attr := simp)]
theorem le_compl_self : a ≤ aᶜ ↔ a = ⊥ := by
  rw [le_compl_iff_disjoint_left, disjoint_self]

@[to_dual (attr := simp)]
theorem ne_compl_self [Nontrivial α] : a ≠ aᶜ := by
  intro h
  cases le_compl_self.1 (le_of_eq h)
  simp at h

@[to_dual (attr := simp)]
theorem compl_ne_self [Nontrivial α] : aᶜ ≠ a :=
  ne_comm.1 ne_compl_self

@[to_dual (attr := simp)]
theorem lt_compl_self [Nontrivial α] : a < aᶜ ↔ a = ⊥ := by
  rw [lt_iff_le_and_ne]; simp

@[to_dual hnot_hnot_le]
theorem le_compl_compl : a ≤ aᶜᶜ :=
  disjoint_compl_right.le_compl_right

-- @[to_dual]
theorem compl_anti : Antitone (compl : α → α) := fun _ _ h =>
  le_compl_comm.1 <| h.trans le_compl_compl

@[gcongr]
theorem compl_le_compl (h : a ≤ b) : bᶜ ≤ aᶜ :=
  compl_anti h

@[simp]
theorem compl_compl_compl (a : α) : aᶜᶜᶜ = aᶜ :=
  (compl_anti le_compl_compl).antisymm le_compl_compl

@[simp]
theorem disjoint_compl_compl_left_iff : Disjoint aᶜᶜ b ↔ Disjoint a b := by
  simp_rw [← le_compl_iff_disjoint_left, compl_compl_compl]

@[simp]
theorem disjoint_compl_compl_right_iff : Disjoint a bᶜᶜ ↔ Disjoint a b := by
  simp_rw [← le_compl_iff_disjoint_right, compl_compl_compl]

theorem compl_sup_compl_le : aᶜ ⊔ bᶜ ≤ (a ⊓ b)ᶜ :=
  sup_le (compl_anti inf_le_left) <| compl_anti inf_le_right

theorem compl_compl_inf_distrib (a b : α) : (a ⊓ b)ᶜᶜ = aᶜᶜ ⊓ bᶜᶜ := by
  refine ((compl_anti compl_sup_compl_le).trans (compl_sup_distrib _ _).le).antisymm ?_
  rw [le_compl_iff_disjoint_right, disjoint_assoc, disjoint_compl_compl_left_iff,
    disjoint_left_comm, disjoint_compl_compl_left_iff, ← disjoint_assoc, inf_comm]
  exact disjoint_compl_right

theorem compl_compl_himp_distrib (a b : α) : (a ⇨ b)ᶜᶜ = aᶜᶜ ⇨ bᶜᶜ := by
  apply le_antisymm
  · rw [le_himp_iff, ← compl_compl_inf_distrib]
    exact compl_anti (compl_anti himp_inf_le)
  · refine le_compl_comm.1 ((compl_anti compl_sup_le_himp).trans ?_)
    rw [compl_sup_distrib, le_compl_iff_disjoint_right, disjoint_right_comm, ←
      le_compl_iff_disjoint_right]
    exact inf_himp_le

instance OrderDual.instCoheytingAlgebra : CoheytingAlgebra αᵒᵈ where
  hnot := toDual ∘ compl ∘ ofDual
  sdiff a b := toDual (ofDual b ⇨ ofDual a)
  sdiff_le_iff a b c := by rw [sup_comm]; exact le_himp_iff
  top_sdiff := @himp_bot α _

@[to_dual existing]
instance OrderDual.instHeytingAlgebra {α : Type u_2} [CoheytingAlgebra α] : HeytingAlgebra αᵒᵈ where
  compl := toDual ∘ hnot ∘ ofDual
  himp a b := toDual (ofDual b \ ofDual a)
  le_himp_iff a b c := by rw [inf_comm]; exact sdiff_le_iff
  himp_bot := @top_sdiff' α _

@[to_dual (attr := simp)]
theorem ofDual_hnot (a : αᵒᵈ) : ofDual (￢a) = (ofDual a)ᶜ :=
  rfl

@[to_dual (attr := simp)]
theorem ofDual_sdiff (a b : αᵒᵈ) : ofDual (a \ b) = ofDual b ⇨ ofDual a :=
  rfl
@[to_dual (attr := simp)]
theorem toDual_compl (a : α) : toDual aᶜ = ￢toDual a :=
  rfl

@[to_dual (attr := simp)]
theorem toDual_himp (a b : α) : toDual (a ⇨ b) = toDual b \ toDual a :=
  rfl

instance Prod.instHeytingAlgebra [HeytingAlgebra β] : HeytingAlgebra (α × β) where
    himp_bot a := Prod.ext_iff.2 ⟨himp_bot a.1, himp_bot a.2⟩

instance Pi.instHeytingAlgebra {α : ι → Type*} [∀ i, HeytingAlgebra (α i)] :
    HeytingAlgebra (∀ i, α i) where
  himp_bot f := funext fun i ↦ himp_bot (f i)

end HeytingAlgebra

section CoheytingAlgebra

variable [CoheytingAlgebra α] {a b : α}

@[to_dual existing]
theorem hnot_anti : Antitone (hnot : α → α) := fun _ _ h => hnot_le_comm.1 <| hnot_hnot_le.trans h

@[to_dual existing]
theorem hnot_le_hnot (h : a ≤ b) : ￢b ≤ ￢a :=
  hnot_anti h

@[to_dual existing, simp]
theorem hnot_hnot_hnot (a : α) : ￢￢￢a = ￢a :=
  hnot_hnot_le.antisymm <| hnot_anti hnot_hnot_le

@[to_dual existing, simp]
theorem codisjoint_hnot_hnot_left_iff : Codisjoint (￢￢a) b ↔ Codisjoint a b := by
  simp_rw [← hnot_le_iff_codisjoint_right, hnot_hnot_hnot]

@[to_dual existing, simp]
theorem codisjoint_hnot_hnot_right_iff : Codisjoint a (￢￢b) ↔ Codisjoint a b := by
  simp_rw [← hnot_le_iff_codisjoint_left, hnot_hnot_hnot]

@[to_dual existing compl_sup_compl_le]
theorem le_hnot_inf_hnot : ￢(a ⊔ b) ≤ ￢a ⊓ ￢b :=
  le_inf (hnot_anti le_sup_left) <| hnot_anti le_sup_right

@[to_dual existing]
theorem hnot_hnot_sup_distrib (a b : α) : ￢￢(a ⊔ b) = ￢￢a ⊔ ￢￢b := by
  refine ((hnot_inf_distrib _ _).ge.trans <| hnot_anti le_hnot_inf_hnot).antisymm' ?_
  rw [hnot_le_iff_codisjoint_left, codisjoint_assoc, codisjoint_hnot_hnot_left_iff,
    codisjoint_left_comm, codisjoint_hnot_hnot_left_iff, ← codisjoint_assoc, sup_comm]
  exact codisjoint_hnot_right

@[to_dual existing]
theorem hnot_hnot_sdiff_distrib (a b : α) : ￢￢(a \ b) = ￢￢a \ ￢￢b := by
  apply le_antisymm
  · refine hnot_le_comm.1 ((hnot_anti sdiff_le_inf_hnot).trans' ?_)
    rw [hnot_inf_distrib, hnot_le_iff_codisjoint_right, codisjoint_left_comm, ←
      hnot_le_iff_codisjoint_right]
    exact le_sdiff_sup
  · rw [sdiff_le_iff, ← hnot_hnot_sup_distrib]
    exact hnot_anti (hnot_anti le_sup_sdiff)

@[to_dual existing]
instance Prod.instCoheytingAlgebra [CoheytingAlgebra β] : CoheytingAlgebra (α × β) where
  sdiff_le_iff _ _ _ := and_congr sdiff_le_iff sdiff_le_iff
  top_sdiff a := Prod.ext_iff.2 ⟨top_sdiff' a.1, top_sdiff' a.2⟩

@[to_dual existing]
instance Pi.instCoheytingAlgebra {α : ι → Type*} [∀ i, CoheytingAlgebra (α i)] :
    CoheytingAlgebra (∀ i, α i) where
  top_sdiff f := funext fun i ↦ top_sdiff' (f i)

end CoheytingAlgebra

section BiheytingAlgebra

variable [BiheytingAlgebra α] {a : α}

theorem compl_le_hnot : aᶜ ≤ ￢a :=
  (disjoint_compl_left : Disjoint _ a).le_of_codisjoint codisjoint_hnot_right

end BiheytingAlgebra

/-- Propositions form a Heyting algebra with implication as Heyting implication and negation as
complement. -/
instance Prop.instHeytingAlgebra : HeytingAlgebra Prop :=
  { Prop.instDistribLattice, Prop.instBoundedOrder with
    himp := (· → ·),
    le_himp_iff := fun _ _ _ => and_imp.symm, himp_bot := fun _ => rfl }

@[simp]
theorem himp_iff_imp (p q : Prop) : p ⇨ q ↔ p → q :=
  Iff.rfl

@[simp]
theorem compl_iff_not (p : Prop) : pᶜ ↔ ¬p :=
  Iff.rfl

variable (α) in
-- See note [reducible non-instances]
/-- A bounded linear order is a bi-Heyting algebra by setting
* `a ⇨ b = ⊤` if `a ≤ b` and `a ⇨ b = b` otherwise.
* `a \ b = ⊥` if `a ≤ b` and `a \ b = a` otherwise. -/
abbrev LinearOrder.toBiheytingAlgebra [LinearOrder α] [BoundedOrder α] : BiheytingAlgebra α :=
  { LinearOrder.toLattice, ‹BoundedOrder α› with
    himp := fun a b => if a ≤ b then ⊤ else b,
    compl := fun a => if a = ⊥ then ⊤ else ⊥,
    le_himp_iff := fun a b c => by
      split_ifs with h
      · exact iff_of_true le_top (inf_le_of_right_le h)
      · rw [inf_le_iff, or_iff_left h],
    himp_bot := fun _ => if_congr le_bot_iff rfl rfl, sdiff := fun a b => if a ≤ b then ⊥ else a,
    hnot := fun a => if a = ⊤ then ⊥ else ⊤,
    sdiff_le_iff := fun a b c => by
      split_ifs with h
      · exact iff_of_true bot_le (le_sup_of_le_left h)
      · rw [le_sup_iff, or_iff_right h],
    top_sdiff := fun _ => if_congr top_le_iff rfl rfl }

instance OrderDual.instBiheytingAlgebra [BiheytingAlgebra α] : BiheytingAlgebra αᵒᵈ where
  __ := instHeytingAlgebra
  __ := instCoheytingAlgebra

instance Prod.instBiheytingAlgebra [BiheytingAlgebra α] [BiheytingAlgebra β] :
    BiheytingAlgebra (α × β) where
  __ := instHeytingAlgebra
  __ := instCoheytingAlgebra

instance Pi.instBiheytingAlgebra {α : ι → Type*} [∀ i, BiheytingAlgebra (α i)] :
    BiheytingAlgebra (∀ i, α i) where
  __ := instHeytingAlgebra
  __ := instCoheytingAlgebra

section lift

-- `to_dual` cannot yet reorder arguments of arguments
-- See note [reducible non-instances]
/-- Pullback a `GeneralizedHeytingAlgebra` along an injection. -/
protected abbrev Function.Injective.generalizedHeytingAlgebra [Max α] [Min α] [Top α]
    [HImp α] [GeneralizedHeytingAlgebra β] (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b) : GeneralizedHeytingAlgebra α :=
  { __ := hf.lattice f map_sup map_inf
    __ := ‹Top α›
    __ := ‹HImp α›
    le_top := fun a => by
      change f _ ≤ _
      rw [map_top]
      exact le_top,
    le_himp_iff := fun a b c => by
      change f _ ≤ _ ↔ f _ ≤ _
      rw [map_himp, map_inf, le_himp_iff] }

-- See note [reducible non-instances]
/-- Pullback a `GeneralizedCoheytingAlgebra` along an injection. -/
protected abbrev Function.Injective.generalizedCoheytingAlgebra [Max α] [Min α] [Bot α]
    [SDiff α] [GeneralizedCoheytingAlgebra β] (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_bot : f ⊥ = ⊥) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    GeneralizedCoheytingAlgebra α :=
  { __ := hf.lattice f map_sup map_inf
    __ := ‹Bot α›
    __ := ‹SDiff α›
    bot_le := fun a => by
      change f _ ≤ _
      rw [map_bot]
      exact bot_le,
    sdiff_le_iff := fun a b c => by
      change f _ ≤ _ ↔ f _ ≤ _
      rw [map_sdiff, map_sup, sdiff_le_iff] }

-- See note [reducible non-instances]
/-- Pullback a `HeytingAlgebra` along an injection. -/
protected abbrev Function.Injective.heytingAlgebra [Max α] [Min α] [Top α] [Bot α]
    [Compl α] [HImp α] [HeytingAlgebra β] (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : ∀ a, f aᶜ = (f a)ᶜ)
    (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b) : HeytingAlgebra α :=
  { __ := hf.generalizedHeytingAlgebra f map_sup map_inf map_top map_himp
    __ := ‹Bot α›
    __ := ‹Compl α›
    bot_le := fun a => by
      change f _ ≤ _
      rw [map_bot]
      exact bot_le,
    himp_bot := fun a => hf <| by rw [map_himp, map_compl, map_bot, himp_bot] }

-- See note [reducible non-instances]
/-- Pullback a `CoheytingAlgebra` along an injection. -/
protected abbrev Function.Injective.coheytingAlgebra [Max α] [Min α] [Top α] [Bot α]
    [HNot α] [SDiff α] [CoheytingAlgebra β] (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_hnot : ∀ a, f (￢a) = ￢f a)
    (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) : CoheytingAlgebra α :=
  { __ := hf.generalizedCoheytingAlgebra f map_sup map_inf map_bot map_sdiff
    __ := ‹Top α›
    __ := ‹HNot α›
    le_top := fun a => by
      change f _ ≤ _
      rw [map_top]
      exact le_top,
    top_sdiff := fun a => hf <| by rw [map_sdiff, map_hnot, map_top, top_sdiff'] }

-- See note [reducible non-instances]
/-- Pullback a `BiheytingAlgebra` along an injection. -/
protected abbrev Function.Injective.biheytingAlgebra [Max α] [Min α] [Top α] [Bot α]
    [Compl α] [HNot α] [HImp α] [SDiff α] [BiheytingAlgebra β] (f : α → β)
    (hf : Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_hnot : ∀ a, f (￢a) = ￢f a)
    (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    BiheytingAlgebra α :=
  { hf.heytingAlgebra f map_sup map_inf map_top map_bot map_compl map_himp,
    hf.coheytingAlgebra f map_sup map_inf map_top map_bot map_hnot map_sdiff with }

end lift

namespace PUnit

variable (a b : PUnit.{u + 1})

instance instBiheytingAlgebra : BiheytingAlgebra PUnit.{u + 1} :=
  { PUnit.instLinearOrder.{u} with
    top := unit,
    bot := unit,
    sup := fun _ _ => unit,
    inf := fun _ _ => unit,
    compl := fun _ => unit,
    sdiff := fun _ _ => unit,
    hnot := fun _ => unit,
    himp := fun _ _ => unit,
    le_top := fun _ => trivial,
    le_sup_left := fun _ _ => trivial,
    le_sup_right := fun _ _ => trivial,
    sup_le := fun _ _ _ _ _ => trivial,
    inf_le_left := fun _ _ => trivial,
    inf_le_right := fun _ _ => trivial,
    le_inf := fun _ _ _ _ _ => trivial,
    bot_le := fun _ => trivial,
    le_himp_iff := fun _ _ _ => Iff.rfl,
    himp_bot := fun _ => rfl,
    top_sdiff := fun _ => rfl,
    sdiff_le_iff := fun _ _ _ => Iff.rfl }

@[to_dual (attr := simp)]
theorem top_eq : (⊤ : PUnit) = unit :=
  rfl

@[to_dual (attr := simp)]
theorem sup_eq : a ⊔ b = unit :=
  rfl

@[to_dual (attr := simp)]
theorem compl_eq : aᶜ = unit :=
  rfl

@[to_dual (attr := simp)]
theorem sdiff_eq : a \ b = unit :=
  rfl

end PUnit
