/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.PropInstances

#align_import order.heyting.basic from "leanprover-community/mathlib"@"9ac7c0c8c4d7a535ec3e5b34b8859aab9233b2f4"

/-!
# Heyting algebras

This file defines Heyting, co-Heyting and bi-Heyting algebras.

A Heyting algebra is a bounded distributive lattice with an implication operation `⇨` such that
`a ≤ b ⇨ c ↔ a ⊓ b ≤ c`. It also comes with a pseudo-complement `ᶜ`, such that `aᶜ = a ⇨ ⊥`.

Co-Heyting algebras are dual to Heyting algebras. They have a difference `\` and a negation `￢`
such that `a \ b ≤ c ↔ a ≤ b ⊔ c` and `￢a = ⊤ \ a`.

Bi-Heyting algebras are Heyting algebras that are also co-Heyting algebras.

From a logic standpoint, Heyting algebras precisely model intuitionistic logic, whereas boolean
algebras model classical logic.

Heyting algebras are the order theoretic equivalent of cartesian-closed categories.

## Main declarations

* `GeneralizedHeytingAlgebra`: Heyting algebra without a top element (nor negation).
* `GeneralizedCoheytingAlgebra`: Co-Heyting algebra without a bottom element (nor complement).
* `HeytingAlgebra`: Heyting algebra.
* `CoheytingAlgebra`: Co-Heyting algebra.
* `BiheytingAlgebra`: bi-Heyting algebra.

## Notation

* `⇨`: Heyting implication
* `\`: Difference
* `￢`: Heyting negation
* `ᶜ`: (Pseudo-)complement

## References

* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]

## Tags

Heyting, Brouwer, algebra, implication, negation, intuitionistic
-/

open Function OrderDual

universe u

variable {ι α β : Type*}

/-! ### Notation -/


/-- Syntax typeclass for Heyting implication `⇨`. -/
@[notation_class]
class HImp (α : Type*) where
  /-- Heyting implication `⇨` -/
  himp : α → α → α
#align has_himp HImp

/-- Syntax typeclass for Heyting negation `￢`.

The difference between `HasCompl` and `HNot` is that the former belongs to Heyting algebras,
while the latter belongs to co-Heyting algebras. They are both pseudo-complements, but `compl`
underestimates while `HNot` overestimates. In boolean algebras, they are equal.
See `hnot_eq_compl`.
-/
@[notation_class]
class HNot (α : Type*) where
  /-- Heyting negation `￢` -/
  hnot : α → α
#align has_hnot HNot

export HImp (himp)
export SDiff (sdiff)
export HNot (hnot)

/-- Heyting implication -/
infixr:60 " ⇨ " => himp

/-- Heyting negation -/
prefix:72 "￢" => hnot

section
variable (α β)

instance Prod.himp [HImp α] [HImp β] : HImp (α × β) :=
  ⟨fun a b => (a.1 ⇨ b.1, a.2 ⇨ b.2)⟩

instance Prod.hnot [HNot α] [HNot β] : HNot (α × β) :=
  ⟨fun a => (￢a.1, ￢a.2)⟩

instance Prod.sdiff [SDiff α] [SDiff β] : SDiff (α × β) :=
  ⟨fun a b => (a.1 \ b.1, a.2 \ b.2)⟩

instance Prod.hasCompl [HasCompl α] [HasCompl β] : HasCompl (α × β) :=
  ⟨fun a => (a.1ᶜ, a.2ᶜ)⟩

end

@[simp]
theorem fst_himp [HImp α] [HImp β] (a b : α × β) : (a ⇨ b).1 = a.1 ⇨ b.1 :=
  rfl
#align fst_himp fst_himp

@[simp]
theorem snd_himp [HImp α] [HImp β] (a b : α × β) : (a ⇨ b).2 = a.2 ⇨ b.2 :=
  rfl
#align snd_himp snd_himp

@[simp]
theorem fst_hnot [HNot α] [HNot β] (a : α × β) : (￢a).1 = ￢a.1 :=
  rfl
#align fst_hnot fst_hnot

@[simp]
theorem snd_hnot [HNot α] [HNot β] (a : α × β) : (￢a).2 = ￢a.2 :=
  rfl
#align snd_hnot snd_hnot

@[simp]
theorem fst_sdiff [SDiff α] [SDiff β] (a b : α × β) : (a \ b).1 = a.1 \ b.1 :=
  rfl
#align fst_sdiff fst_sdiff

@[simp]
theorem snd_sdiff [SDiff α] [SDiff β] (a b : α × β) : (a \ b).2 = a.2 \ b.2 :=
  rfl
#align snd_sdiff snd_sdiff

@[simp]
theorem fst_compl [HasCompl α] [HasCompl β] (a : α × β) : aᶜ.1 = a.1ᶜ :=
  rfl
#align fst_compl fst_compl

@[simp]
theorem snd_compl [HasCompl α] [HasCompl β] (a : α × β) : aᶜ.2 = a.2ᶜ :=
  rfl
#align snd_compl snd_compl

namespace Pi

variable {π : ι → Type*}

instance [∀ i, HImp (π i)] : HImp (∀ i, π i) :=
  ⟨fun a b i => a i ⇨ b i⟩

instance [∀ i, HNot (π i)] : HNot (∀ i, π i) :=
  ⟨fun a i => ￢a i⟩

theorem himp_def [∀ i, HImp (π i)] (a b : ∀ i, π i) : a ⇨ b = fun i => a i ⇨ b i :=
  rfl
#align pi.himp_def Pi.himp_def

theorem hnot_def [∀ i, HNot (π i)] (a : ∀ i, π i) : ￢a = fun i => ￢a i :=
  rfl
#align pi.hnot_def Pi.hnot_def

@[simp]
theorem himp_apply [∀ i, HImp (π i)] (a b : ∀ i, π i) (i : ι) : (a ⇨ b) i = a i ⇨ b i :=
  rfl
#align pi.himp_apply Pi.himp_apply

@[simp]
theorem hnot_apply [∀ i, HNot (π i)] (a : ∀ i, π i) (i : ι) : (￢a) i = ￢a i :=
  rfl
#align pi.hnot_apply Pi.hnot_apply

end Pi

/-- A generalized Heyting algebra is a lattice with an additional binary operation `⇨` called
Heyting implication such that `a ⇨` is right adjoint to `a ⊓`.

 This generalizes `HeytingAlgebra` by not requiring a bottom element. -/
class GeneralizedHeytingAlgebra (α : Type*) extends Lattice α, Top α, HImp α where
  /-- `⊤` is a greatest element -/
  le_top : ∀ a : α, a ≤ ⊤
  /-- `a ⇨` is right adjoint to `a ⊓` -/
  le_himp_iff (a b c : α) : a ≤ b ⇨ c ↔ a ⊓ b ≤ c
#align generalized_heyting_algebra GeneralizedHeytingAlgebra

/-- A generalized co-Heyting algebra is a lattice with an additional binary
difference operation `\` such that `\ a` is right adjoint to `⊔ a`.

This generalizes `CoheytingAlgebra` by not requiring a top element. -/
class GeneralizedCoheytingAlgebra (α : Type*) extends Lattice α, Bot α, SDiff α where
  /-- `⊥` is a least element -/
  bot_le : ∀ a : α, ⊥ ≤ a
  /-- `\ a` is right adjoint to `⊔ a` -/
  sdiff_le_iff (a b c : α) : a \ b ≤ c ↔ a ≤ b ⊔ c
#align generalized_coheyting_algebra GeneralizedCoheytingAlgebra

/-- A Heyting algebra is a bounded lattice with an additional binary operation `⇨` called Heyting
implication such that `a ⇨` is right adjoint to `a ⊓`. -/
class HeytingAlgebra (α : Type*) extends GeneralizedHeytingAlgebra α, Bot α, HasCompl α where
  /-- `⊥` is a least element -/
  bot_le : ∀ a : α, ⊥ ≤ a
  /-- `a ⇨` is right adjoint to `a ⊓` -/
  himp_bot (a : α) : a ⇨ ⊥ = aᶜ
#align heyting_algebra HeytingAlgebra

/-- A co-Heyting algebra is a bounded lattice with an additional binary difference operation `\`
such that `\ a` is right adjoint to `⊔ a`. -/
class CoheytingAlgebra (α : Type*) extends GeneralizedCoheytingAlgebra α, Top α, HNot α where
  /-- `⊤` is a greatest element -/
  le_top : ∀ a : α, a ≤ ⊤
  /-- `⊤ \ a` is `￢a` -/
  top_sdiff (a : α) : ⊤ \ a = ￢a
#align coheyting_algebra CoheytingAlgebra

/-- A bi-Heyting algebra is a Heyting algebra that is also a co-Heyting algebra. -/
class BiheytingAlgebra (α : Type*) extends HeytingAlgebra α, SDiff α, HNot α where
  /-- `\ a` is right adjoint to `⊔ a` -/
  sdiff_le_iff (a b c : α) : a \ b ≤ c ↔ a ≤ b ⊔ c
  /-- `⊤ \ a` is `￢a` -/
  top_sdiff (a : α) : ⊤ \ a = ￢a
#align biheyting_algebra BiheytingAlgebra

-- See note [lower instance priority]
instance (priority := 100) GeneralizedHeytingAlgebra.toOrderTop [GeneralizedHeytingAlgebra α] :
    OrderTop α :=
  { ‹GeneralizedHeytingAlgebra α› with }
#align generalized_heyting_algebra.to_order_top GeneralizedHeytingAlgebra.toOrderTop

-- See note [lower instance priority]
instance (priority := 100) GeneralizedCoheytingAlgebra.toOrderBot [GeneralizedCoheytingAlgebra α] :
    OrderBot α :=
  { ‹GeneralizedCoheytingAlgebra α› with }
#align generalized_coheyting_algebra.to_order_bot GeneralizedCoheytingAlgebra.toOrderBot

-- See note [lower instance priority]
instance (priority := 100) HeytingAlgebra.toBoundedOrder [HeytingAlgebra α] : BoundedOrder α :=
  { bot_le := ‹HeytingAlgebra α›.bot_le }
--#align heyting_algebra.to_bounded_order HeytingAlgebra.toBoundedOrder

-- See note [lower instance priority]
instance (priority := 100) CoheytingAlgebra.toBoundedOrder [CoheytingAlgebra α] : BoundedOrder α :=
  { ‹CoheytingAlgebra α› with }
#align coheyting_algebra.to_bounded_order CoheytingAlgebra.toBoundedOrder

-- See note [lower instance priority]
instance (priority := 100) BiheytingAlgebra.toCoheytingAlgebra [BiheytingAlgebra α] :
    CoheytingAlgebra α :=
  { ‹BiheytingAlgebra α› with }
#align biheyting_algebra.to_coheyting_algebra BiheytingAlgebra.toCoheytingAlgebra

-- See note [reducible non-instances]
/-- Construct a Heyting algebra from the lattice structure and Heyting implication alone. -/
@[reducible]
def HeytingAlgebra.ofHImp [DistribLattice α] [BoundedOrder α] (himp : α → α → α)
    (le_himp_iff : ∀ a b c, a ≤ himp b c ↔ a ⊓ b ≤ c) : HeytingAlgebra α :=
  { ‹DistribLattice α›, ‹BoundedOrder α› with
    himp,
    compl := fun a => himp a ⊥,
    le_himp_iff,
    himp_bot := fun a => rfl }
#align heyting_algebra.of_himp HeytingAlgebra.ofHImp

-- See note [reducible non-instances]
/-- Construct a Heyting algebra from the lattice structure and complement operator alone. -/
@[reducible]
def HeytingAlgebra.ofCompl [DistribLattice α] [BoundedOrder α] (compl : α → α)
    (le_himp_iff : ∀ a b c, a ≤ compl b ⊔ c ↔ a ⊓ b ≤ c) : HeytingAlgebra α :=
  { ‹DistribLattice α›, ‹BoundedOrder α› with
    himp := fun a => (· ⊔ ·) (compl a),
    compl,
    le_himp_iff,
    himp_bot := fun a => sup_bot_eq }
#align heyting_algebra.of_compl HeytingAlgebra.ofCompl

-- See note [reducible non-instances]
/-- Construct a co-Heyting algebra from the lattice structure and the difference alone. -/
@[reducible]
def CoheytingAlgebra.ofSDiff [DistribLattice α] [BoundedOrder α] (sdiff : α → α → α)
    (sdiff_le_iff : ∀ a b c, sdiff a b ≤ c ↔ a ≤ b ⊔ c) : CoheytingAlgebra α :=
  { ‹DistribLattice α›, ‹BoundedOrder α› with
    sdiff,
    hnot := fun a => sdiff ⊤ a,
    sdiff_le_iff,
    top_sdiff := fun a => rfl }
#align coheyting_algebra.of_sdiff CoheytingAlgebra.ofSDiff

-- See note [reducible non-instances]
/-- Construct a co-Heyting algebra from the difference and Heyting negation alone. -/
@[reducible]
def CoheytingAlgebra.ofHNot [DistribLattice α] [BoundedOrder α] (hnot : α → α)
    (sdiff_le_iff : ∀ a b c, a ⊓ hnot b ≤ c ↔ a ≤ b ⊔ c) : CoheytingAlgebra α :=
  { ‹DistribLattice α›, ‹BoundedOrder α› with
    sdiff := fun a b => a ⊓ hnot b,
    hnot,
    sdiff_le_iff,
    top_sdiff := fun a => top_inf_eq }
#align coheyting_algebra.of_hnot CoheytingAlgebra.ofHNot

section GeneralizedHeytingAlgebra

variable [GeneralizedHeytingAlgebra α] {a b c d : α}

/- In this section, we'll give interpretations of these results in the Heyting algebra model of
intuitionistic logic,- where `≤` can be interpreted as "validates", `⇨` as "implies", `⊓` as "and",
`⊔` as "or", `⊥` as "false" and `⊤` as "true". Note that we confuse `→` and `⊢` because those are
the same in this logic.

See also `Prop.heytingAlgebra`. -/
-- `p → q → r ↔ p ∧ q → r`
@[simp]
theorem le_himp_iff : a ≤ b ⇨ c ↔ a ⊓ b ≤ c :=
  GeneralizedHeytingAlgebra.le_himp_iff _ _ _
#align le_himp_iff le_himp_iff

-- `p → q → r ↔ q ∧ p → r`
theorem le_himp_iff' : a ≤ b ⇨ c ↔ b ⊓ a ≤ c := by rw [le_himp_iff, inf_comm]
                                                   -- 🎉 no goals
#align le_himp_iff' le_himp_iff'

-- `p → q → r ↔ q → p → r`
theorem le_himp_comm : a ≤ b ⇨ c ↔ b ≤ a ⇨ c := by rw [le_himp_iff, le_himp_iff']
                                                   -- 🎉 no goals
#align le_himp_comm le_himp_comm

-- `p → q → p`
theorem le_himp : a ≤ b ⇨ a :=
  le_himp_iff.2 inf_le_left
#align le_himp le_himp

-- `p → p → q ↔ p → q`
theorem le_himp_iff_left : a ≤ a ⇨ b ↔ a ≤ b := by rw [le_himp_iff, inf_idem]
                                                   -- 🎉 no goals
#align le_himp_iff_left le_himp_iff_left

-- `p → p`
@[simp]
theorem himp_self : a ⇨ a = ⊤ :=
  top_le_iff.1 <| le_himp_iff.2 inf_le_right
#align himp_self himp_self

-- `(p → q) ∧ p → q`
theorem himp_inf_le : (a ⇨ b) ⊓ a ≤ b :=
  le_himp_iff.1 le_rfl
#align himp_inf_le himp_inf_le

-- `p ∧ (p → q) → q`
theorem inf_himp_le : a ⊓ (a ⇨ b) ≤ b := by rw [inf_comm, ← le_himp_iff]
                                            -- 🎉 no goals
#align inf_himp_le inf_himp_le

-- `p ∧ (p → q) ↔ p ∧ q`
@[simp]
theorem inf_himp (a b : α) : a ⊓ (a ⇨ b) = a ⊓ b :=
  le_antisymm (le_inf inf_le_left <| by rw [inf_comm, ← le_himp_iff]) <| inf_le_inf_left _ le_himp
                                        -- 🎉 no goals
#align inf_himp inf_himp

-- `(p → q) ∧ p ↔ q ∧ p`
@[simp]
theorem himp_inf_self (a b : α) : (a ⇨ b) ⊓ a = b ⊓ a := by rw [inf_comm, inf_himp, inf_comm]
                                                            -- 🎉 no goals
#align himp_inf_self himp_inf_self

/-- The **deduction theorem** in the Heyting algebra model of intuitionistic logic:
an implication holds iff the conclusion follows from the hypothesis. -/
@[simp]
theorem himp_eq_top_iff : a ⇨ b = ⊤ ↔ a ≤ b := by rw [← top_le_iff, le_himp_iff, top_inf_eq]
                                                  -- 🎉 no goals
#align himp_eq_top_iff himp_eq_top_iff

-- `p → true`, `true → p ↔ p`
@[simp]
theorem himp_top : a ⇨ ⊤ = ⊤ :=
  himp_eq_top_iff.2 le_top
#align himp_top himp_top

@[simp]
theorem top_himp : ⊤ ⇨ a = a :=
  eq_of_forall_le_iff fun b => by rw [le_himp_iff, inf_top_eq]
                                  -- 🎉 no goals
#align top_himp top_himp

-- `p → q → r ↔ p ∧ q → r`
theorem himp_himp (a b c : α) : a ⇨ b ⇨ c = a ⊓ b ⇨ c :=
  eq_of_forall_le_iff fun d => by simp_rw [le_himp_iff, inf_assoc]
                                  -- 🎉 no goals
#align himp_himp himp_himp

-- `(q → r) → (p → q) → q → r`
theorem himp_le_himp_himp_himp : b ⇨ c ≤ (a ⇨ b) ⇨ a ⇨ c := by
  rw [le_himp_iff, le_himp_iff, inf_assoc, himp_inf_self, ← inf_assoc, himp_inf_self, inf_assoc]
  -- ⊢ c ⊓ (b ⊓ a) ≤ c
  exact inf_le_left
  -- 🎉 no goals
#align himp_le_himp_himp_himp himp_le_himp_himp_himp

@[simp]
theorem himp_inf_himp_inf_le : (b ⇨ c) ⊓ (a ⇨ b) ⊓ a ≤ c := by
  simpa using @himp_le_himp_himp_himp
  -- 🎉 no goals

-- `p → q → r ↔ q → p → r`
theorem himp_left_comm (a b c : α) : a ⇨ b ⇨ c = b ⇨ a ⇨ c := by simp_rw [himp_himp, inf_comm]
                                                                 -- 🎉 no goals
#align himp_left_comm himp_left_comm

@[simp]
theorem himp_idem : b ⇨ b ⇨ a = b ⇨ a := by rw [himp_himp, inf_idem]
                                            -- 🎉 no goals
#align himp_idem himp_idem

theorem himp_inf_distrib (a b c : α) : a ⇨ b ⊓ c = (a ⇨ b) ⊓ (a ⇨ c) :=
  eq_of_forall_le_iff fun d => by simp_rw [le_himp_iff, le_inf_iff, le_himp_iff]
                                  -- 🎉 no goals
#align himp_inf_distrib himp_inf_distrib

theorem sup_himp_distrib (a b c : α) : a ⊔ b ⇨ c = (a ⇨ c) ⊓ (b ⇨ c) :=
  eq_of_forall_le_iff fun d => by
    rw [le_inf_iff, le_himp_comm, sup_le_iff]
    -- ⊢ a ≤ d ⇨ c ∧ b ≤ d ⇨ c ↔ d ≤ a ⇨ c ∧ d ≤ b ⇨ c
    simp_rw [le_himp_comm]
    -- 🎉 no goals
#align sup_himp_distrib sup_himp_distrib

theorem himp_le_himp_left (h : a ≤ b) : c ⇨ a ≤ c ⇨ b :=
  le_himp_iff.2 <| himp_inf_le.trans h
#align himp_le_himp_left himp_le_himp_left

theorem himp_le_himp_right (h : a ≤ b) : b ⇨ c ≤ a ⇨ c :=
  le_himp_iff.2 <| (inf_le_inf_left _ h).trans himp_inf_le
#align himp_le_himp_right himp_le_himp_right

theorem himp_le_himp (hab : a ≤ b) (hcd : c ≤ d) : b ⇨ c ≤ a ⇨ d :=
  (himp_le_himp_right hab).trans <| himp_le_himp_left hcd
#align himp_le_himp himp_le_himp

@[simp]
theorem sup_himp_self_left (a b : α) : a ⊔ b ⇨ a = b ⇨ a := by
  rw [sup_himp_distrib, himp_self, top_inf_eq]
  -- 🎉 no goals
#align sup_himp_self_left sup_himp_self_left

@[simp]
theorem sup_himp_self_right (a b : α) : a ⊔ b ⇨ b = a ⇨ b := by
  rw [sup_himp_distrib, himp_self, inf_top_eq]
  -- 🎉 no goals
#align sup_himp_self_right sup_himp_self_right

theorem Codisjoint.himp_eq_right (h : Codisjoint a b) : b ⇨ a = a := by
  conv_rhs => rw [← @top_himp _ _ a]
  -- ⊢ b ⇨ a = ⊤ ⇨ a
  rw [← h.eq_top, sup_himp_self_left]
  -- 🎉 no goals
#align codisjoint.himp_eq_right Codisjoint.himp_eq_right

theorem Codisjoint.himp_eq_left (h : Codisjoint a b) : a ⇨ b = b :=
  h.symm.himp_eq_right
#align codisjoint.himp_eq_left Codisjoint.himp_eq_left

theorem Codisjoint.himp_inf_cancel_right (h : Codisjoint a b) : a ⇨ a ⊓ b = b := by
  rw [himp_inf_distrib, himp_self, top_inf_eq, h.himp_eq_left]
  -- 🎉 no goals
#align codisjoint.himp_inf_cancel_right Codisjoint.himp_inf_cancel_right

theorem Codisjoint.himp_inf_cancel_left (h : Codisjoint a b) : b ⇨ a ⊓ b = a := by
  rw [himp_inf_distrib, himp_self, inf_top_eq, h.himp_eq_right]
  -- 🎉 no goals
#align codisjoint.himp_inf_cancel_left Codisjoint.himp_inf_cancel_left

/-- See `himp_le` for a stronger version in Boolean algebras. -/
theorem Codisjoint.himp_le_of_right_le (hac : Codisjoint a c) (hba : b ≤ a) : c ⇨ b ≤ a :=
  (himp_le_himp_left hba).trans_eq hac.himp_eq_right
#align codisjoint.himp_le_of_right_le Codisjoint.himp_le_of_right_le

theorem le_himp_himp : a ≤ (a ⇨ b) ⇨ b :=
  le_himp_iff.2 inf_himp_le
#align le_himp_himp le_himp_himp

theorem himp_triangle (a b c : α) : (a ⇨ b) ⊓ (b ⇨ c) ≤ a ⇨ c := by
  rw [le_himp_iff, inf_right_comm, ← le_himp_iff]
  -- ⊢ (a ⇨ b) ⊓ a ≤ (b ⇨ c) ⇨ c
  exact himp_inf_le.trans le_himp_himp
  -- 🎉 no goals
#align himp_triangle himp_triangle

theorem himp_inf_himp_cancel (hba : b ≤ a) (hcb : c ≤ b) : (a ⇨ b) ⊓ (b ⇨ c) = a ⇨ c :=
  (himp_triangle _ _ _).antisymm <| le_inf (himp_le_himp_left hcb) (himp_le_himp_right hba)
#align himp_inf_himp_cancel himp_inf_himp_cancel

-- See note [lower instance priority]
instance (priority := 100) GeneralizedHeytingAlgebra.toDistribLattice : DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => by
    simp_rw [@inf_comm _ _ a, ← le_himp_iff, sup_le_iff, le_himp_iff, ← sup_le_iff]; rfl
    -- ⊢ b ⊓ a ⊔ c ⊓ a ≤ b ⊓ a ⊔ c ⊓ a
                                                                                     -- 🎉 no goals
#align generalized_heyting_algebra.to_distrib_lattice GeneralizedHeytingAlgebra.toDistribLattice

instance : GeneralizedCoheytingAlgebra αᵒᵈ :=
  { OrderDual.lattice α, OrderDual.orderBot α with
    sdiff := fun a b => toDual (ofDual b ⇨ ofDual a),
    sdiff_le_iff := fun a b c => by
      rw [sup_comm]
      -- ⊢ a \ b ≤ c ↔ a ≤ c ⊔ b
      exact le_himp_iff }
      -- 🎉 no goals

instance Prod.generalizedHeytingAlgebra [GeneralizedHeytingAlgebra β] :
    GeneralizedHeytingAlgebra (α × β) :=
  { Prod.lattice α β, Prod.orderTop α β, Prod.himp α β with
    le_himp_iff := fun _ _ _ => and_congr le_himp_iff le_himp_iff }
#align prod.generalized_heyting_algebra Prod.generalizedHeytingAlgebra

instance Pi.generalizedHeytingAlgebra {α : ι → Type*} [∀ i, GeneralizedHeytingAlgebra (α i)] :
    GeneralizedHeytingAlgebra (∀ i, α i) :=
  { Pi.lattice, Pi.orderTop with
    le_himp_iff := fun i => by simp [le_def] }
                               -- 🎉 no goals
#align pi.generalized_heyting_algebra Pi.generalizedHeytingAlgebra

end GeneralizedHeytingAlgebra

section GeneralizedCoheytingAlgebra

variable [GeneralizedCoheytingAlgebra α] {a b c d : α}

@[simp]
theorem sdiff_le_iff : a \ b ≤ c ↔ a ≤ b ⊔ c :=
  GeneralizedCoheytingAlgebra.sdiff_le_iff _ _ _
#align sdiff_le_iff sdiff_le_iff

theorem sdiff_le_iff' : a \ b ≤ c ↔ a ≤ c ⊔ b := by rw [sdiff_le_iff, sup_comm]
                                                    -- 🎉 no goals
#align sdiff_le_iff' sdiff_le_iff'

theorem sdiff_le_comm : a \ b ≤ c ↔ a \ c ≤ b := by rw [sdiff_le_iff, sdiff_le_iff']
                                                    -- 🎉 no goals
#align sdiff_le_comm sdiff_le_comm

theorem sdiff_le : a \ b ≤ a :=
  sdiff_le_iff.2 le_sup_right
#align sdiff_le sdiff_le

theorem Disjoint.disjoint_sdiff_left (h : Disjoint a b) : Disjoint (a \ c) b :=
  h.mono_left sdiff_le
#align disjoint.disjoint_sdiff_left Disjoint.disjoint_sdiff_left

theorem Disjoint.disjoint_sdiff_right (h : Disjoint a b) : Disjoint a (b \ c) :=
  h.mono_right sdiff_le
#align disjoint.disjoint_sdiff_right Disjoint.disjoint_sdiff_right

theorem sdiff_le_iff_left : a \ b ≤ b ↔ a ≤ b := by rw [sdiff_le_iff, sup_idem]
                                                    -- 🎉 no goals
#align sdiff_le_iff_left sdiff_le_iff_left

@[simp]
theorem sdiff_self : a \ a = ⊥ :=
  le_bot_iff.1 <| sdiff_le_iff.2 le_sup_left
#align sdiff_self sdiff_self

theorem le_sup_sdiff : a ≤ b ⊔ a \ b :=
  sdiff_le_iff.1 le_rfl
#align le_sup_sdiff le_sup_sdiff

theorem le_sdiff_sup : a ≤ a \ b ⊔ b := by rw [sup_comm, ← sdiff_le_iff]
                                           -- 🎉 no goals
#align le_sdiff_sup le_sdiff_sup

theorem sup_sdiff_left : a ⊔ a \ b = a :=
  sup_of_le_left sdiff_le
#align sup_sdiff_left sup_sdiff_left

theorem sup_sdiff_right : a \ b ⊔ a = a :=
  sup_of_le_right sdiff_le
#align sup_sdiff_right sup_sdiff_right

theorem inf_sdiff_left : a \ b ⊓ a = a \ b :=
  inf_of_le_left sdiff_le
#align inf_sdiff_left inf_sdiff_left

theorem inf_sdiff_right : a ⊓ a \ b = a \ b :=
  inf_of_le_right sdiff_le
#align inf_sdiff_right inf_sdiff_right

@[simp]
theorem sup_sdiff_self (a b : α) : a ⊔ b \ a = a ⊔ b :=
  le_antisymm (sup_le_sup_left sdiff_le _) (sup_le le_sup_left le_sup_sdiff)
#align sup_sdiff_self sup_sdiff_self

@[simp]
theorem sdiff_sup_self (a b : α) : b \ a ⊔ a = b ⊔ a := by rw [sup_comm, sup_sdiff_self, sup_comm]
                                                           -- 🎉 no goals
#align sdiff_sup_self sdiff_sup_self

alias sup_sdiff_self_left := sdiff_sup_self
#align sup_sdiff_self_left sup_sdiff_self_left

alias sup_sdiff_self_right := sup_sdiff_self
#align sup_sdiff_self_right sup_sdiff_self_right

theorem sup_sdiff_eq_sup (h : c ≤ a) : a ⊔ b \ c = a ⊔ b :=
  sup_congr_left (sdiff_le.trans le_sup_right) <| le_sup_sdiff.trans <| sup_le_sup_right h _
#align sup_sdiff_eq_sup sup_sdiff_eq_sup

-- cf. `Set.union_diff_cancel'`
theorem sup_sdiff_cancel' (hab : a ≤ b) (hbc : b ≤ c) : b ⊔ c \ a = c := by
  rw [sup_sdiff_eq_sup hab, sup_of_le_right hbc]
  -- 🎉 no goals
#align sup_sdiff_cancel' sup_sdiff_cancel'

theorem sup_sdiff_cancel_right (h : a ≤ b) : a ⊔ b \ a = b :=
  sup_sdiff_cancel' le_rfl h
#align sup_sdiff_cancel_right sup_sdiff_cancel_right

theorem sdiff_sup_cancel (h : b ≤ a) : a \ b ⊔ b = a := by rw [sup_comm, sup_sdiff_cancel_right h]
                                                           -- 🎉 no goals
#align sdiff_sup_cancel sdiff_sup_cancel

theorem sup_le_of_le_sdiff_left (h : b ≤ c \ a) (hac : a ≤ c) : a ⊔ b ≤ c :=
  sup_le hac <| h.trans sdiff_le
#align sup_le_of_le_sdiff_left sup_le_of_le_sdiff_left

theorem sup_le_of_le_sdiff_right (h : a ≤ c \ b) (hbc : b ≤ c) : a ⊔ b ≤ c :=
  sup_le (h.trans sdiff_le) hbc
#align sup_le_of_le_sdiff_right sup_le_of_le_sdiff_right

@[simp]
theorem sdiff_eq_bot_iff : a \ b = ⊥ ↔ a ≤ b := by rw [← le_bot_iff, sdiff_le_iff, sup_bot_eq]
                                                   -- 🎉 no goals
#align sdiff_eq_bot_iff sdiff_eq_bot_iff

@[simp]
theorem sdiff_bot : a \ ⊥ = a :=
  eq_of_forall_ge_iff fun b => by rw [sdiff_le_iff, bot_sup_eq]
                                  -- 🎉 no goals
#align sdiff_bot sdiff_bot

@[simp]
theorem bot_sdiff : ⊥ \ a = ⊥ :=
  sdiff_eq_bot_iff.2 bot_le
#align bot_sdiff bot_sdiff

theorem sdiff_sdiff_sdiff_le_sdiff : (a \ b) \ (a \ c) ≤ c \ b := by
  rw [sdiff_le_iff, sdiff_le_iff, sup_left_comm, sup_sdiff_self, sup_left_comm, sdiff_sup_self,
    sup_left_comm]
  exact le_sup_left
  -- 🎉 no goals
#align sdiff_sdiff_sdiff_le_sdiff sdiff_sdiff_sdiff_le_sdiff

@[simp]
theorem le_sup_sdiff_sup_sdiff : a ≤ b ⊔ (a \ c ⊔ c \ b) :=
  by simpa using @sdiff_sdiff_sdiff_le_sdiff
     -- 🎉 no goals

theorem sdiff_sdiff (a b c : α) : (a \ b) \ c = a \ (b ⊔ c) :=
  eq_of_forall_ge_iff fun d => by simp_rw [sdiff_le_iff, sup_assoc]
                                  -- 🎉 no goals
#align sdiff_sdiff sdiff_sdiff

theorem sdiff_sdiff_left : (a \ b) \ c = a \ (b ⊔ c) :=
  sdiff_sdiff _ _ _
#align sdiff_sdiff_left sdiff_sdiff_left

theorem sdiff_right_comm (a b c : α) : (a \ b) \ c = (a \ c) \ b := by
  simp_rw [sdiff_sdiff, sup_comm]
  -- 🎉 no goals
#align sdiff_right_comm sdiff_right_comm

theorem sdiff_sdiff_comm : (a \ b) \ c = (a \ c) \ b :=
  sdiff_right_comm _ _ _
#align sdiff_sdiff_comm sdiff_sdiff_comm

@[simp]
theorem sdiff_idem : (a \ b) \ b = a \ b := by rw [sdiff_sdiff_left, sup_idem]
                                               -- 🎉 no goals
#align sdiff_idem sdiff_idem

@[simp]
theorem sdiff_sdiff_self : (a \ b) \ a = ⊥ := by rw [sdiff_sdiff_comm, sdiff_self, bot_sdiff]
                                                 -- 🎉 no goals
#align sdiff_sdiff_self sdiff_sdiff_self

theorem sup_sdiff_distrib (a b c : α) : (a ⊔ b) \ c = a \ c ⊔ b \ c :=
  eq_of_forall_ge_iff fun d => by simp_rw [sdiff_le_iff, sup_le_iff, sdiff_le_iff]
                                  -- 🎉 no goals
#align sup_sdiff_distrib sup_sdiff_distrib

theorem sdiff_inf_distrib (a b c : α) : a \ (b ⊓ c) = a \ b ⊔ a \ c :=
  eq_of_forall_ge_iff fun d => by
    rw [sup_le_iff, sdiff_le_comm, le_inf_iff]
    -- ⊢ a \ d ≤ b ∧ a \ d ≤ c ↔ a \ b ≤ d ∧ a \ c ≤ d
    simp_rw [sdiff_le_comm]
    -- 🎉 no goals
#align sdiff_inf_distrib sdiff_inf_distrib

theorem sup_sdiff : (a ⊔ b) \ c = a \ c ⊔ b \ c :=
  sup_sdiff_distrib _ _ _
#align sup_sdiff sup_sdiff

@[simp]
theorem sup_sdiff_right_self : (a ⊔ b) \ b = a \ b := by rw [sup_sdiff, sdiff_self, sup_bot_eq]
                                                         -- 🎉 no goals
#align sup_sdiff_right_self sup_sdiff_right_self

@[simp]
theorem sup_sdiff_left_self : (a ⊔ b) \ a = b \ a := by rw [sup_comm, sup_sdiff_right_self]
                                                        -- 🎉 no goals
#align sup_sdiff_left_self sup_sdiff_left_self

theorem sdiff_le_sdiff_right (h : a ≤ b) : a \ c ≤ b \ c :=
  sdiff_le_iff.2 <| h.trans <| le_sup_sdiff
#align sdiff_le_sdiff_right sdiff_le_sdiff_right

theorem sdiff_le_sdiff_left (h : a ≤ b) : c \ b ≤ c \ a :=
  sdiff_le_iff.2 <| le_sup_sdiff.trans <| sup_le_sup_right h _
#align sdiff_le_sdiff_left sdiff_le_sdiff_left

theorem sdiff_le_sdiff (hab : a ≤ b) (hcd : c ≤ d) : a \ d ≤ b \ c :=
  (sdiff_le_sdiff_right hab).trans <| sdiff_le_sdiff_left hcd
#align sdiff_le_sdiff sdiff_le_sdiff

-- cf. `IsCompl.inf_sup`
theorem sdiff_inf : a \ (b ⊓ c) = a \ b ⊔ a \ c :=
  sdiff_inf_distrib _ _ _
#align sdiff_inf sdiff_inf

@[simp]
theorem sdiff_inf_self_left (a b : α) : a \ (a ⊓ b) = a \ b := by
  rw [sdiff_inf, sdiff_self, bot_sup_eq]
  -- 🎉 no goals
#align sdiff_inf_self_left sdiff_inf_self_left

@[simp]
theorem sdiff_inf_self_right (a b : α) : b \ (a ⊓ b) = b \ a := by
  rw [sdiff_inf, sdiff_self, sup_bot_eq]
  -- 🎉 no goals
#align sdiff_inf_self_right sdiff_inf_self_right

theorem Disjoint.sdiff_eq_left (h : Disjoint a b) : a \ b = a := by
  conv_rhs => rw [← @sdiff_bot _ _ a]
  -- ⊢ a \ b = a \ ⊥
  rw [← h.eq_bot, sdiff_inf_self_left]
  -- 🎉 no goals
#align disjoint.sdiff_eq_left Disjoint.sdiff_eq_left

theorem Disjoint.sdiff_eq_right (h : Disjoint a b) : b \ a = b :=
  h.symm.sdiff_eq_left
#align disjoint.sdiff_eq_right Disjoint.sdiff_eq_right

theorem Disjoint.sup_sdiff_cancel_left (h : Disjoint a b) : (a ⊔ b) \ a = b := by
  rw [sup_sdiff, sdiff_self, bot_sup_eq, h.sdiff_eq_right]
  -- 🎉 no goals
#align disjoint.sup_sdiff_cancel_left Disjoint.sup_sdiff_cancel_left

theorem Disjoint.sup_sdiff_cancel_right (h : Disjoint a b) : (a ⊔ b) \ b = a := by
  rw [sup_sdiff, sdiff_self, sup_bot_eq, h.sdiff_eq_left]
  -- 🎉 no goals
#align disjoint.sup_sdiff_cancel_right Disjoint.sup_sdiff_cancel_right

/-- See `le_sdiff` for a stronger version in generalised Boolean algebras. -/
theorem Disjoint.le_sdiff_of_le_left (hac : Disjoint a c) (hab : a ≤ b) : a ≤ b \ c :=
  hac.sdiff_eq_left.ge.trans <| sdiff_le_sdiff_right hab
#align disjoint.le_sdiff_of_le_left Disjoint.le_sdiff_of_le_left

theorem sdiff_sdiff_le : a \ (a \ b) ≤ b :=
  sdiff_le_iff.2 le_sdiff_sup
#align sdiff_sdiff_le sdiff_sdiff_le

theorem sdiff_triangle (a b c : α) : a \ c ≤ a \ b ⊔ b \ c := by
  rw [sdiff_le_iff, sup_left_comm, ← sdiff_le_iff]
  -- ⊢ a \ (a \ b) ≤ c ⊔ b \ c
  exact sdiff_sdiff_le.trans le_sup_sdiff
  -- 🎉 no goals
#align sdiff_triangle sdiff_triangle

theorem sdiff_sup_sdiff_cancel (hba : b ≤ a) (hcb : c ≤ b) : a \ b ⊔ b \ c = a \ c :=
  (sdiff_triangle _ _ _).antisymm' <| sup_le (sdiff_le_sdiff_left hcb) (sdiff_le_sdiff_right hba)
#align sdiff_sup_sdiff_cancel sdiff_sup_sdiff_cancel

theorem sdiff_le_sdiff_of_sup_le_sup_left (h : c ⊔ a ≤ c ⊔ b) : a \ c ≤ b \ c := by
  rw [← sup_sdiff_left_self, ← @sup_sdiff_left_self _ _ _ b]
  -- ⊢ (c ⊔ a) \ c ≤ (c ⊔ b) \ c
  exact sdiff_le_sdiff_right h
  -- 🎉 no goals
#align sdiff_le_sdiff_of_sup_le_sup_left sdiff_le_sdiff_of_sup_le_sup_left

theorem sdiff_le_sdiff_of_sup_le_sup_right (h : a ⊔ c ≤ b ⊔ c) : a \ c ≤ b \ c := by
  rw [← sup_sdiff_right_self, ← @sup_sdiff_right_self _ _ b]
  -- ⊢ (a ⊔ c) \ c ≤ (b ⊔ c) \ c
  exact sdiff_le_sdiff_right h
  -- 🎉 no goals
#align sdiff_le_sdiff_of_sup_le_sup_right sdiff_le_sdiff_of_sup_le_sup_right

@[simp]
theorem inf_sdiff_sup_left : a \ c ⊓ (a ⊔ b) = a \ c :=
  inf_of_le_left <| sdiff_le.trans le_sup_left
#align inf_sdiff_sup_left inf_sdiff_sup_left

@[simp]
theorem inf_sdiff_sup_right : a \ c ⊓ (b ⊔ a) = a \ c :=
  inf_of_le_left <| sdiff_le.trans le_sup_right
#align inf_sdiff_sup_right inf_sdiff_sup_right

-- See note [lower instance priority]
instance (priority := 100) GeneralizedCoheytingAlgebra.toDistribLattice : DistribLattice α :=
  { ‹GeneralizedCoheytingAlgebra α› with
    le_sup_inf :=
      fun a b c => by simp_rw [← sdiff_le_iff, le_inf_iff, sdiff_le_iff, ← le_inf_iff]; rfl }
                      -- ⊢ (a ⊔ b) ⊓ (a ⊔ c) ≤ (a ⊔ b) ⊓ (a ⊔ c)
                                                                                        -- 🎉 no goals
#align generalized_coheyting_algebra.to_distrib_lattice GeneralizedCoheytingAlgebra.toDistribLattice

instance : GeneralizedHeytingAlgebra αᵒᵈ :=
  { OrderDual.lattice α, OrderDual.orderTop α with
    himp := fun a b => toDual (ofDual b \ ofDual a),
    le_himp_iff := fun a b c => by
      rw [inf_comm]
      -- ⊢ a ≤ b ⇨ c ↔ b ⊓ a ≤ c
      exact sdiff_le_iff }
      -- 🎉 no goals

instance Prod.generalizedCoheytingAlgebra [GeneralizedCoheytingAlgebra β] :
    GeneralizedCoheytingAlgebra (α × β) :=
  { Prod.lattice α β, Prod.orderBot α β, Prod.sdiff α β with
    sdiff_le_iff := fun _ _ _ => and_congr sdiff_le_iff sdiff_le_iff }
#align prod.generalized_coheyting_algebra Prod.generalizedCoheytingAlgebra

instance Pi.generalizedCoheytingAlgebra {α : ι → Type*} [∀ i, GeneralizedCoheytingAlgebra (α i)] :
    GeneralizedCoheytingAlgebra (∀ i, α i) :=
  { Pi.lattice, Pi.orderBot with
    sdiff_le_iff := fun i => by simp [le_def] }
                                -- 🎉 no goals
#align pi.generalized_coheyting_algebra Pi.generalizedCoheytingAlgebra

end GeneralizedCoheytingAlgebra

section HeytingAlgebra

variable [HeytingAlgebra α] {a b c : α}

@[simp]
theorem himp_bot (a : α) : a ⇨ ⊥ = aᶜ :=
  HeytingAlgebra.himp_bot _
#align himp_bot himp_bot

@[simp]
theorem bot_himp (a : α) : ⊥ ⇨ a = ⊤ :=
  himp_eq_top_iff.2 bot_le
#align bot_himp bot_himp

theorem compl_sup_distrib (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ := by
  simp_rw [← himp_bot, sup_himp_distrib]
  -- 🎉 no goals
#align compl_sup_distrib compl_sup_distrib

@[simp]
theorem compl_sup : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ :=
  compl_sup_distrib _ _
#align compl_sup compl_sup

theorem compl_le_himp : aᶜ ≤ a ⇨ b :=
  (himp_bot _).ge.trans <| himp_le_himp_left bot_le
#align compl_le_himp compl_le_himp

theorem compl_sup_le_himp : aᶜ ⊔ b ≤ a ⇨ b :=
  sup_le compl_le_himp le_himp
#align compl_sup_le_himp compl_sup_le_himp

theorem sup_compl_le_himp : b ⊔ aᶜ ≤ a ⇨ b :=
  sup_le le_himp compl_le_himp
#align sup_compl_le_himp sup_compl_le_himp

-- `p → ¬ p ↔ ¬ p`
@[simp]
theorem himp_compl (a : α) : a ⇨ aᶜ = aᶜ := by rw [← himp_bot, himp_himp, inf_idem]
                                               -- 🎉 no goals
#align himp_compl himp_compl

-- `p → ¬ q ↔ q → ¬ p`
theorem himp_compl_comm (a b : α) : a ⇨ bᶜ = b ⇨ aᶜ := by simp_rw [← himp_bot, himp_left_comm]
                                                          -- 🎉 no goals
#align himp_compl_comm himp_compl_comm

theorem le_compl_iff_disjoint_right : a ≤ bᶜ ↔ Disjoint a b := by
  rw [← himp_bot, le_himp_iff, disjoint_iff_inf_le]
  -- 🎉 no goals
#align le_compl_iff_disjoint_right le_compl_iff_disjoint_right

theorem le_compl_iff_disjoint_left : a ≤ bᶜ ↔ Disjoint b a :=
  le_compl_iff_disjoint_right.trans disjoint_comm
#align le_compl_iff_disjoint_left le_compl_iff_disjoint_left

theorem le_compl_comm : a ≤ bᶜ ↔ b ≤ aᶜ := by
  rw [le_compl_iff_disjoint_right, le_compl_iff_disjoint_left]
  -- 🎉 no goals
#align le_compl_comm le_compl_comm

alias ⟨_, Disjoint.le_compl_right⟩ := le_compl_iff_disjoint_right
#align disjoint.le_compl_right Disjoint.le_compl_right

alias ⟨_, Disjoint.le_compl_left⟩ := le_compl_iff_disjoint_left
#align disjoint.le_compl_left Disjoint.le_compl_left

alias le_compl_iff_le_compl := le_compl_comm
#align le_compl_iff_le_compl le_compl_iff_le_compl

alias ⟨le_compl_of_le_compl, _⟩ := le_compl_comm
#align le_compl_of_le_compl le_compl_of_le_compl

theorem disjoint_compl_left : Disjoint aᶜ a :=
  disjoint_iff_inf_le.mpr <| le_himp_iff.1 (himp_bot _).ge
#align disjoint_compl_left disjoint_compl_left

theorem disjoint_compl_right : Disjoint a aᶜ :=
  disjoint_compl_left.symm
#align disjoint_compl_right disjoint_compl_right

theorem LE.le.disjoint_compl_left (h : b ≤ a) : Disjoint aᶜ b :=
  disjoint_compl_left.mono_right h
#align has_le.le.disjoint_compl_left LE.le.disjoint_compl_left

theorem LE.le.disjoint_compl_right (h : a ≤ b) : Disjoint a bᶜ :=
  disjoint_compl_right.mono_left h
#align has_le.le.disjoint_compl_right LE.le.disjoint_compl_right

theorem IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b :=
  h.1.le_compl_left.antisymm' <| Disjoint.le_of_codisjoint disjoint_compl_left h.2
#align is_compl.compl_eq IsCompl.compl_eq

theorem IsCompl.eq_compl (h : IsCompl a b) : a = bᶜ :=
  h.1.le_compl_right.antisymm <| Disjoint.le_of_codisjoint disjoint_compl_left h.2.symm
#align is_compl.eq_compl IsCompl.eq_compl

theorem compl_unique (h₀ : a ⊓ b = ⊥) (h₁ : a ⊔ b = ⊤) : aᶜ = b :=
  (IsCompl.of_eq h₀ h₁).compl_eq
#align compl_unique compl_unique

@[simp]
theorem inf_compl_self (a : α) : a ⊓ aᶜ = ⊥ :=
  disjoint_compl_right.eq_bot
#align inf_compl_self inf_compl_self

@[simp]
theorem compl_inf_self (a : α) : aᶜ ⊓ a = ⊥ :=
  disjoint_compl_left.eq_bot
#align compl_inf_self compl_inf_self

theorem inf_compl_eq_bot : a ⊓ aᶜ = ⊥ :=
  inf_compl_self _
#align inf_compl_eq_bot inf_compl_eq_bot

theorem compl_inf_eq_bot : aᶜ ⊓ a = ⊥ :=
  compl_inf_self _
#align compl_inf_eq_bot compl_inf_eq_bot

@[simp]
theorem compl_top : (⊤ : α)ᶜ = ⊥ :=
  eq_of_forall_le_iff fun a => by rw [le_compl_iff_disjoint_right, disjoint_top, le_bot_iff]
                                  -- 🎉 no goals
#align compl_top compl_top

@[simp]
theorem compl_bot : (⊥ : α)ᶜ = ⊤ := by rw [← himp_bot, himp_self]
                                       -- 🎉 no goals
#align compl_bot compl_bot

@[simp] theorem le_compl_self : a ≤ aᶜ ↔ a = ⊥ := by
  rw [le_compl_iff_disjoint_left, disjoint_self]
  -- 🎉 no goals

@[simp] theorem ne_compl_self [Nontrivial α] : a ≠ aᶜ := by
  intro h
  -- ⊢ False
  cases le_compl_self.1 (le_of_eq h)
  -- ⊢ False
  simp at h
  -- 🎉 no goals

@[simp] theorem compl_ne_self [Nontrivial α] : aᶜ ≠ a :=
  ne_comm.1 ne_compl_self

@[simp] theorem lt_compl_self [Nontrivial α] : a < aᶜ ↔ a = ⊥ := by
  rw [lt_iff_le_and_ne]; simp
  -- ⊢ a ≤ aᶜ ∧ a ≠ aᶜ ↔ a = ⊥
                         -- 🎉 no goals

theorem le_compl_compl : a ≤ aᶜᶜ :=
  disjoint_compl_right.le_compl_right
#align le_compl_compl le_compl_compl

theorem compl_anti : Antitone (compl : α → α) := fun _ _ h =>
  le_compl_comm.1 <| h.trans le_compl_compl
#align compl_anti compl_anti

@[gcongr]
theorem compl_le_compl (h : a ≤ b) : bᶜ ≤ aᶜ :=
  compl_anti h
#align compl_le_compl compl_le_compl

@[simp]
theorem compl_compl_compl (a : α) : aᶜᶜᶜ = aᶜ :=
  (compl_anti le_compl_compl).antisymm le_compl_compl
#align compl_compl_compl compl_compl_compl

@[simp]
theorem disjoint_compl_compl_left_iff : Disjoint aᶜᶜ b ↔ Disjoint a b := by
  simp_rw [← le_compl_iff_disjoint_left, compl_compl_compl]
  -- 🎉 no goals
#align disjoint_compl_compl_left_iff disjoint_compl_compl_left_iff

@[simp]
theorem disjoint_compl_compl_right_iff : Disjoint a bᶜᶜ ↔ Disjoint a b := by
  simp_rw [← le_compl_iff_disjoint_right, compl_compl_compl]
  -- 🎉 no goals
#align disjoint_compl_compl_right_iff disjoint_compl_compl_right_iff

theorem compl_sup_compl_le : aᶜ ⊔ bᶜ ≤ (a ⊓ b)ᶜ :=
  sup_le (compl_anti inf_le_left) <| compl_anti inf_le_right
#align compl_sup_compl_le compl_sup_compl_le

theorem compl_compl_inf_distrib (a b : α) : (a ⊓ b)ᶜᶜ = aᶜᶜ ⊓ bᶜᶜ := by
  refine' ((compl_anti compl_sup_compl_le).trans (compl_sup_distrib _ _).le).antisymm _
  -- ⊢ aᶜᶜ ⊓ bᶜᶜ ≤ (a ⊓ b)ᶜᶜ
  rw [le_compl_iff_disjoint_right, disjoint_assoc, disjoint_compl_compl_left_iff,
    disjoint_left_comm, disjoint_compl_compl_left_iff, ← disjoint_assoc, inf_comm]
  exact disjoint_compl_right
  -- 🎉 no goals
#align compl_compl_inf_distrib compl_compl_inf_distrib

theorem compl_compl_himp_distrib (a b : α) : (a ⇨ b)ᶜᶜ = aᶜᶜ ⇨ bᶜᶜ := by
  refine' le_antisymm _ _
  -- ⊢ (a ⇨ b)ᶜᶜ ≤ aᶜᶜ ⇨ bᶜᶜ
  · rw [le_himp_iff, ← compl_compl_inf_distrib]
    -- ⊢ ((a ⇨ b) ⊓ a)ᶜᶜ ≤ bᶜᶜ
    exact compl_anti (compl_anti himp_inf_le)
    -- 🎉 no goals
  · refine' le_compl_comm.1 ((compl_anti compl_sup_le_himp).trans _)
    -- ⊢ (aᶜ ⊔ b)ᶜ ≤ (aᶜᶜ ⇨ bᶜᶜ)ᶜ
    rw [compl_sup_distrib, le_compl_iff_disjoint_right, disjoint_right_comm, ←
      le_compl_iff_disjoint_right]
    exact inf_himp_le
    -- 🎉 no goals
#align compl_compl_himp_distrib compl_compl_himp_distrib

instance : CoheytingAlgebra αᵒᵈ :=
  { OrderDual.lattice α, OrderDual.boundedOrder α with
    hnot := toDual ∘ compl ∘ ofDual,
    sdiff := fun a b => toDual (ofDual b ⇨ ofDual a),
    sdiff_le_iff := fun a b c => by
      rw [sup_comm]
      -- ⊢ a \ b ≤ c ↔ a ≤ c ⊔ b
      exact le_himp_iff,
      -- 🎉 no goals
    top_sdiff := @himp_bot α _ }

@[simp]
theorem ofDual_hnot (a : αᵒᵈ) : ofDual (￢a) = (ofDual a)ᶜ :=
  rfl
#align of_dual_hnot ofDual_hnot

@[simp]
theorem toDual_compl (a : α) : toDual aᶜ = ￢toDual a :=
  rfl
#align to_dual_compl toDual_compl

instance Prod.heytingAlgebra [HeytingAlgebra β] : HeytingAlgebra (α × β) :=
  { Prod.generalizedHeytingAlgebra, Prod.boundedOrder α β, Prod.hasCompl α β with
     himp_bot := fun a => Prod.ext_iff.2 ⟨himp_bot a.1, himp_bot a.2⟩ }
#align prod.heyting_algebra Prod.heytingAlgebra

instance Pi.heytingAlgebra {α : ι → Type*} [∀ i, HeytingAlgebra (α i)] :
    HeytingAlgebra (∀ i, α i) :=
  { Pi.orderBot, Pi.generalizedHeytingAlgebra with
    himp_bot := fun f => funext fun i => himp_bot (f i) }
#align pi.heyting_algebra Pi.heytingAlgebra

end HeytingAlgebra

section CoheytingAlgebra

variable [CoheytingAlgebra α] {a b c : α}

@[simp]
theorem top_sdiff' (a : α) : ⊤ \ a = ￢a :=
  CoheytingAlgebra.top_sdiff _
#align top_sdiff' top_sdiff'

@[simp]
theorem sdiff_top (a : α) : a \ ⊤ = ⊥ :=
  sdiff_eq_bot_iff.2 le_top
#align sdiff_top sdiff_top

theorem hnot_inf_distrib (a b : α) : ￢(a ⊓ b) = ￢a ⊔ ￢b := by
  simp_rw [← top_sdiff', sdiff_inf_distrib]
  -- 🎉 no goals
#align hnot_inf_distrib hnot_inf_distrib

theorem sdiff_le_hnot : a \ b ≤ ￢b :=
  (sdiff_le_sdiff_right le_top).trans_eq <| top_sdiff' _
#align sdiff_le_hnot sdiff_le_hnot

theorem sdiff_le_inf_hnot : a \ b ≤ a ⊓ ￢b :=
  le_inf sdiff_le sdiff_le_hnot
#align sdiff_le_inf_hnot sdiff_le_inf_hnot

-- See note [lower instance priority]
instance (priority := 100) CoheytingAlgebra.toDistribLattice : DistribLattice α :=
  { ‹CoheytingAlgebra α› with
    le_sup_inf :=
      fun a b c => by simp_rw [← sdiff_le_iff, le_inf_iff, sdiff_le_iff, ← le_inf_iff]; rfl }
                      -- ⊢ (a ⊔ b) ⊓ (a ⊔ c) ≤ (a ⊔ b) ⊓ (a ⊔ c)
                                                                                        -- 🎉 no goals
#align coheyting_algebra.to_distrib_lattice CoheytingAlgebra.toDistribLattice

@[simp]
theorem hnot_sdiff (a : α) : ￢a \ a = ￢a := by rw [← top_sdiff', sdiff_sdiff, sup_idem]
                                               -- 🎉 no goals
#align hnot_sdiff hnot_sdiff

theorem hnot_sdiff_comm (a b : α) : ￢a \ b = ￢b \ a := by simp_rw [← top_sdiff', sdiff_right_comm]
                                                          -- 🎉 no goals
#align hnot_sdiff_comm hnot_sdiff_comm

theorem hnot_le_iff_codisjoint_right : ￢a ≤ b ↔ Codisjoint a b := by
  rw [← top_sdiff', sdiff_le_iff, codisjoint_iff_le_sup]
  -- 🎉 no goals
#align hnot_le_iff_codisjoint_right hnot_le_iff_codisjoint_right

theorem hnot_le_iff_codisjoint_left : ￢a ≤ b ↔ Codisjoint b a :=
  hnot_le_iff_codisjoint_right.trans Codisjoint_comm
#align hnot_le_iff_codisjoint_left hnot_le_iff_codisjoint_left

theorem hnot_le_comm : ￢a ≤ b ↔ ￢b ≤ a := by
  rw [hnot_le_iff_codisjoint_right, hnot_le_iff_codisjoint_left]
  -- 🎉 no goals
#align hnot_le_comm hnot_le_comm

alias ⟨_, Codisjoint.hnot_le_right⟩ := hnot_le_iff_codisjoint_right
#align codisjoint.hnot_le_right Codisjoint.hnot_le_right

alias ⟨_, Codisjoint.hnot_le_left⟩ := hnot_le_iff_codisjoint_left
#align codisjoint.hnot_le_left Codisjoint.hnot_le_left

theorem codisjoint_hnot_right : Codisjoint a (￢a) :=
  codisjoint_iff_le_sup.2 <| sdiff_le_iff.1 (top_sdiff' _).le
#align codisjoint_hnot_right codisjoint_hnot_right

theorem codisjoint_hnot_left : Codisjoint (￢a) a :=
  codisjoint_hnot_right.symm
#align codisjoint_hnot_left codisjoint_hnot_left

theorem LE.le.codisjoint_hnot_left (h : a ≤ b) : Codisjoint (￢a) b :=
  codisjoint_hnot_left.mono_right h
#align has_le.le.codisjoint_hnot_left LE.le.codisjoint_hnot_left

theorem LE.le.codisjoint_hnot_right (h : b ≤ a) : Codisjoint a (￢b) :=
  codisjoint_hnot_right.mono_left h
#align has_le.le.codisjoint_hnot_right LE.le.codisjoint_hnot_right

theorem IsCompl.hnot_eq (h : IsCompl a b) : ￢a = b :=
  h.2.hnot_le_right.antisymm <| Disjoint.le_of_codisjoint h.1.symm codisjoint_hnot_right
#align is_compl.hnot_eq IsCompl.hnot_eq

theorem IsCompl.eq_hnot (h : IsCompl a b) : a = ￢b :=
  h.2.hnot_le_left.antisymm' <| Disjoint.le_of_codisjoint h.1 codisjoint_hnot_right
#align is_compl.eq_hnot IsCompl.eq_hnot

@[simp]
theorem sup_hnot_self (a : α) : a ⊔ ￢a = ⊤ :=
  Codisjoint.eq_top codisjoint_hnot_right
#align sup_hnot_self sup_hnot_self

@[simp]
theorem hnot_sup_self (a : α) : ￢a ⊔ a = ⊤ :=
  Codisjoint.eq_top codisjoint_hnot_left
#align hnot_sup_self hnot_sup_self

@[simp]
theorem hnot_bot : ￢(⊥ : α) = ⊤ :=
  eq_of_forall_ge_iff fun a => by rw [hnot_le_iff_codisjoint_left, codisjoint_bot, top_le_iff]
                                  -- 🎉 no goals
#align hnot_bot hnot_bot

@[simp]
theorem hnot_top : ￢(⊤ : α) = ⊥ := by rw [← top_sdiff', sdiff_self]
                                      -- 🎉 no goals
#align hnot_top hnot_top

theorem hnot_hnot_le : ￢￢a ≤ a :=
  codisjoint_hnot_right.hnot_le_left
#align hnot_hnot_le hnot_hnot_le

theorem hnot_anti : Antitone (hnot : α → α) := fun _ _ h => hnot_le_comm.1 <| hnot_hnot_le.trans h
#align hnot_anti hnot_anti

theorem hnot_le_hnot (h : a ≤ b) : ￢b ≤ ￢a :=
  hnot_anti h
#align hnot_le_hnot hnot_le_hnot

@[simp]
theorem hnot_hnot_hnot (a : α) : ￢￢￢a = ￢a :=
  hnot_hnot_le.antisymm <| hnot_anti hnot_hnot_le
#align hnot_hnot_hnot hnot_hnot_hnot

@[simp]
theorem codisjoint_hnot_hnot_left_iff : Codisjoint (￢￢a) b ↔ Codisjoint a b := by
  simp_rw [← hnot_le_iff_codisjoint_right, hnot_hnot_hnot]
  -- 🎉 no goals
#align codisjoint_hnot_hnot_left_iff codisjoint_hnot_hnot_left_iff

@[simp]
theorem codisjoint_hnot_hnot_right_iff : Codisjoint a (￢￢b) ↔ Codisjoint a b := by
  simp_rw [← hnot_le_iff_codisjoint_left, hnot_hnot_hnot]
  -- 🎉 no goals
#align codisjoint_hnot_hnot_right_iff codisjoint_hnot_hnot_right_iff

theorem le_hnot_inf_hnot : ￢(a ⊔ b) ≤ ￢a ⊓ ￢b :=
  le_inf (hnot_anti le_sup_left) <| hnot_anti le_sup_right
#align le_hnot_inf_hnot le_hnot_inf_hnot

theorem hnot_hnot_sup_distrib (a b : α) : ￢￢(a ⊔ b) = ￢￢a ⊔ ￢￢b := by
  refine' ((hnot_inf_distrib _ _).ge.trans <| hnot_anti le_hnot_inf_hnot).antisymm' _
  -- ⊢ ￢￢(a ⊔ b) ≤ ￢￢a ⊔ ￢￢b
  rw [hnot_le_iff_codisjoint_left, codisjoint_assoc, codisjoint_hnot_hnot_left_iff,
    codisjoint_left_comm, codisjoint_hnot_hnot_left_iff, ← codisjoint_assoc, sup_comm]
  exact codisjoint_hnot_right
  -- 🎉 no goals
#align hnot_hnot_sup_distrib hnot_hnot_sup_distrib

theorem hnot_hnot_sdiff_distrib (a b : α) : ￢￢(a \ b) = ￢￢a \ ￢￢b := by
  refine' le_antisymm _ _
  -- ⊢ ￢￢(a \ b) ≤ ￢￢a \ ￢￢b
  · refine' hnot_le_comm.1 ((hnot_anti sdiff_le_inf_hnot).trans' _)
    -- ⊢ ￢(￢￢a \ ￢￢b) ≤ ￢(a ⊓ ￢b)
    rw [hnot_inf_distrib, hnot_le_iff_codisjoint_right, codisjoint_left_comm, ←
      hnot_le_iff_codisjoint_right]
    exact le_sdiff_sup
    -- 🎉 no goals
  · rw [sdiff_le_iff, ← hnot_hnot_sup_distrib]
    -- ⊢ ￢￢a ≤ ￢￢(b ⊔ a \ b)
    exact hnot_anti (hnot_anti le_sup_sdiff)
    -- 🎉 no goals
#align hnot_hnot_sdiff_distrib hnot_hnot_sdiff_distrib

instance : HeytingAlgebra αᵒᵈ :=
  { OrderDual.lattice α, OrderDual.boundedOrder α with
    compl := toDual ∘ hnot ∘ ofDual,
    himp := fun a b => toDual (ofDual b \ ofDual a),
    le_himp_iff := fun a b c => by
      rw [inf_comm]
      -- ⊢ a ≤ b ⇨ c ↔ b ⊓ a ≤ c
      exact sdiff_le_iff,
      -- 🎉 no goals
    himp_bot := @top_sdiff' α _ }

@[simp]
theorem ofDual_compl (a : αᵒᵈ) : ofDual aᶜ = ￢ofDual a :=
  rfl
#align of_dual_compl ofDual_compl

@[simp]
theorem ofDual_himp (a b : αᵒᵈ) : ofDual (a ⇨ b) = ofDual b \ ofDual a :=
  rfl
#align of_dual_himp ofDual_himp

@[simp]
theorem toDual_hnot (a : α) : toDual (￢a) = (toDual a)ᶜ :=
  rfl
#align to_dual_hnot toDual_hnot

@[simp]
theorem toDual_sdiff (a b : α) : toDual (a \ b) = toDual b ⇨ toDual a :=
  rfl
#align to_dual_sdiff toDual_sdiff

instance Prod.coheytingAlgebra [CoheytingAlgebra β] : CoheytingAlgebra (α × β) :=
  { Prod.lattice α β, Prod.boundedOrder α β, Prod.sdiff α β, Prod.hnot α β with
    sdiff_le_iff := fun _ _ _ => and_congr sdiff_le_iff sdiff_le_iff,
    top_sdiff := fun a => Prod.ext_iff.2 ⟨top_sdiff' a.1, top_sdiff' a.2⟩ }
#align prod.coheyting_algebra Prod.coheytingAlgebra

instance Pi.coheytingAlgebra {α : ι → Type*} [∀ i, CoheytingAlgebra (α i)] :
    CoheytingAlgebra (∀ i, α i) :=
  { Pi.orderTop, Pi.generalizedCoheytingAlgebra with
    top_sdiff := fun f => funext fun i => top_sdiff' (f i) }
#align pi.coheyting_algebra Pi.coheytingAlgebra

end CoheytingAlgebra

section BiheytingAlgebra

variable [BiheytingAlgebra α] {a : α}

theorem compl_le_hnot : aᶜ ≤ ￢a :=
  (disjoint_compl_left : Disjoint _ a).le_of_codisjoint codisjoint_hnot_right
#align compl_le_hnot compl_le_hnot

end BiheytingAlgebra

/-- Propositions form a Heyting algebra with implication as Heyting implication and negation as
complement. -/
instance Prop.heytingAlgebra : HeytingAlgebra Prop :=
  { Prop.distribLattice, Prop.boundedOrder with
    himp := (· → ·),
    le_himp_iff := fun _ _ _ => and_imp.symm, himp_bot := fun _ => rfl }
#align Prop.heyting_algebra Prop.heytingAlgebra

@[simp]
theorem himp_iff_imp (p q : Prop) : p ⇨ q ↔ p → q :=
  Iff.rfl
#align himp_iff_imp himp_iff_imp

@[simp]
theorem compl_iff_not (p : Prop) : pᶜ ↔ ¬p :=
  Iff.rfl
#align compl_iff_not compl_iff_not

-- See note [reducible non-instances]
/-- A bounded linear order is a bi-Heyting algebra by setting
* `a ⇨ b = ⊤` if `a ≤ b` and `a ⇨ b = b` otherwise.
* `a \ b = ⊥` if `a ≤ b` and `a \ b = a` otherwise. -/
@[reducible]
def LinearOrder.toBiheytingAlgebra [LinearOrder α] [BoundedOrder α] : BiheytingAlgebra α :=
  { LinearOrder.toLattice, ‹BoundedOrder α› with
    himp := fun a b => if a ≤ b then ⊤ else b,
    compl := fun a => if a = ⊥ then ⊤ else ⊥,
    le_himp_iff := fun a b c => by
      change _ ≤ ite _ _ _ ↔ _
      -- ⊢ (a ≤ if b ≤ c then ⊤ else c) ↔ a ⊓ b ≤ c
      split_ifs with h
      -- ⊢ a ≤ ⊤ ↔ a ⊓ b ≤ c
      · exact iff_of_true le_top (inf_le_of_right_le h)
        -- 🎉 no goals
      · rw [inf_le_iff, or_iff_left h],
        -- 🎉 no goals
    himp_bot := fun a => if_congr le_bot_iff rfl rfl, sdiff := fun a b => if a ≤ b then ⊥ else a,
    hnot := fun a => if a = ⊤ then ⊥ else ⊤,
    sdiff_le_iff := fun a b c => by
      change ite _ _ _ ≤ _ ↔ _
      -- ⊢ (if a ≤ b then ⊥ else a) ≤ c ↔ a ≤ b ⊔ c
      split_ifs with h
      -- ⊢ ⊥ ≤ c ↔ a ≤ b ⊔ c
      · exact iff_of_true bot_le (le_sup_of_le_left h)
        -- 🎉 no goals
      · rw [le_sup_iff, or_iff_right h],
        -- 🎉 no goals
    top_sdiff := fun a => if_congr top_le_iff rfl rfl }
#align linear_order.to_biheyting_algebra LinearOrder.toBiheytingAlgebra

section lift

-- See note [reducible non-instances]
/-- Pullback a `GeneralizedHeytingAlgebra` along an injection. -/
@[reducible]
protected def Function.Injective.generalizedHeytingAlgebra [Sup α] [Inf α] [Top α]
    [HImp α] [GeneralizedHeytingAlgebra β] (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b) : GeneralizedHeytingAlgebra α :=
  { hf.lattice f map_sup map_inf, ‹Top α›, ‹HImp α› with
    le_top := fun a => by
      change f _ ≤ _
      -- ⊢ f a ≤ f ⊤
      rw [map_top]
      -- ⊢ f a ≤ ⊤
      exact le_top,
      -- 🎉 no goals
    le_himp_iff := fun a b c => by
      change f _ ≤ _ ↔ f _ ≤ _
      -- ⊢ f a ≤ f (b ⇨ c) ↔ f (a ⊓ b) ≤ f c
      erw [map_himp, map_inf, le_himp_iff] }
      -- 🎉 no goals
#align function.injective.generalized_heyting_algebra Function.Injective.generalizedHeytingAlgebra

-- See note [reducible non-instances]
/-- Pullback a `GeneralizedCoheytingAlgebra` along an injection. -/
@[reducible]
protected def Function.Injective.generalizedCoheytingAlgebra [Sup α] [Inf α] [Bot α]
    [SDiff α] [GeneralizedCoheytingAlgebra β] (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_bot : f ⊥ = ⊥) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    GeneralizedCoheytingAlgebra α :=
  { hf.lattice f map_sup map_inf, ‹Bot α›, ‹SDiff α› with
    bot_le := fun a => by
      change f _ ≤ _
      -- ⊢ f ⊥ ≤ f a
      rw [map_bot]
      -- ⊢ ⊥ ≤ f a
      exact bot_le,
      -- 🎉 no goals
    sdiff_le_iff := fun a b c => by
      change f _ ≤ _ ↔ f _ ≤ _
      -- ⊢ f (a \ b) ≤ f c ↔ f a ≤ f (b ⊔ c)
      erw [map_sdiff, map_sup, sdiff_le_iff] }
      -- 🎉 no goals
#align function.injective.generalized_coheyting_algebra Function.Injective.generalizedCoheytingAlgebra

-- See note [reducible non-instances]
/-- Pullback a `HeytingAlgebra` along an injection. -/
@[reducible]
protected def Function.Injective.heytingAlgebra [Sup α] [Inf α] [Top α] [Bot α]
    [HasCompl α] [HImp α] [HeytingAlgebra β] (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : ∀ a, f aᶜ = (f a)ᶜ)
    (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b) : HeytingAlgebra α :=
  { hf.generalizedHeytingAlgebra f map_sup map_inf map_top map_himp, ‹Bot α›, ‹HasCompl α› with
    bot_le := fun a => by
      change f _ ≤ _
      -- ⊢ f ⊥ ≤ f a
      rw [map_bot]
      -- ⊢ ⊥ ≤ f a
      exact bot_le,
      -- 🎉 no goals
    himp_bot := fun a => hf <| by erw [map_himp, map_compl, map_bot, himp_bot] }
                                  -- 🎉 no goals
#align function.injective.heyting_algebra Function.Injective.heytingAlgebra

-- See note [reducible non-instances]
/-- Pullback a `CoheytingAlgebra` along an injection. -/
@[reducible]
protected def Function.Injective.coheytingAlgebra [Sup α] [Inf α] [Top α] [Bot α]
    [HNot α] [SDiff α] [CoheytingAlgebra β] (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_hnot : ∀ a, f (￢a) = ￢f a)
    (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) : CoheytingAlgebra α :=
  { hf.generalizedCoheytingAlgebra f map_sup map_inf map_bot map_sdiff, ‹Top α›, ‹HNot α› with
    le_top := fun a => by
      change f _ ≤ _
      -- ⊢ f a ≤ f ⊤
      rw [map_top]
      -- ⊢ f a ≤ ⊤
      exact le_top,
      -- 🎉 no goals
    top_sdiff := fun a => hf <| by erw [map_sdiff, map_hnot, map_top, top_sdiff'] }
                                   -- 🎉 no goals
#align function.injective.coheyting_algebra Function.Injective.coheytingAlgebra

-- See note [reducible non-instances]
/-- Pullback a `BiheytingAlgebra` along an injection. -/
@[reducible]
protected def Function.Injective.biheytingAlgebra [Sup α] [Inf α] [Top α] [Bot α]
    [HasCompl α] [HNot α] [HImp α] [SDiff α] [BiheytingAlgebra β] (f : α → β)
    (hf : Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_hnot : ∀ a, f (￢a) = ￢f a)
    (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    BiheytingAlgebra α :=
  { hf.heytingAlgebra f map_sup map_inf map_top map_bot map_compl map_himp,
    hf.coheytingAlgebra f map_sup map_inf map_top map_bot map_hnot map_sdiff with }
#align function.injective.biheyting_algebra Function.Injective.biheytingAlgebra

end lift

namespace PUnit

variable (a b : PUnit.{u + 1})

instance biheytingAlgebra : BiheytingAlgebra PUnit.{u+1} :=
  { PUnit.linearOrder.{u} with
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

@[simp]
theorem top_eq : (⊤ : PUnit) = unit :=
  rfl
#align punit.top_eq PUnit.top_eq

@[simp]
theorem bot_eq : (⊥ : PUnit) = unit :=
  rfl
#align punit.bot_eq PUnit.bot_eq

@[simp, nolint simpNF]
theorem sup_eq : a ⊔ b = unit :=
  rfl
#align punit.sup_eq PUnit.sup_eq

@[simp, nolint simpNF]
theorem inf_eq : a ⊓ b = unit :=
  rfl
#align punit.inf_eq PUnit.inf_eq

@[simp]
theorem compl_eq : aᶜ = unit :=
  rfl
#align punit.compl_eq PUnit.compl_eq

@[simp, nolint simpNF]
theorem sdiff_eq : a \ b = unit :=
  rfl
#align punit.sdiff_eq PUnit.sdiff_eq

@[simp, nolint simpNF]
theorem hnot_eq : ￢a = unit :=
  rfl
#align punit.hnot_eq PUnit.hnot_eq

-- eligible for `dsimp`
@[simp, nolint simpNF]
theorem himp_eq : a ⇨ b = unit :=
  rfl
#align punit.himp_eq PUnit.himp_eq

end PUnit
