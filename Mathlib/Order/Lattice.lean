/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Bool.Basic
import Mathlib.Init.Order.Defs
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.ULift
import Mathlib.Tactic.GCongr.Core

#align_import order.lattice from "leanprover-community/mathlib"@"3ba15165bd6927679be7c22d6091a87337e3cd0c"

/-!
# (Semi-)lattices

Semilattices are partially ordered sets with join (least upper bound, or `sup`) or meet (greatest
lower bound, or `inf`) operations. Lattices are posets that are both join-semilattices and
meet-semilattices.

Distributive lattices are lattices which satisfy any of four equivalent distributivity properties,
of `sup` over `inf`, on the left or on the right.

## Main declarations

* `SemilatticeSup`: a type class for join semilattices
* `SemilatticeSup.mk'`: an alternative constructor for `SemilatticeSup` via proofs that `⊔` is
  commutative, associative and idempotent.
* `SemilatticeInf`: a type class for meet semilattices
* `SemilatticeSup.mk'`: an alternative constructor for `SemilatticeInf` via proofs that `⊓` is
  commutative, associative and idempotent.

* `Lattice`: a type class for lattices
* `Lattice.mk'`: an alternative constructor for `Lattice` via proofs that `⊔` and `⊓` are
  commutative, associative and satisfy a pair of "absorption laws".

* `DistribLattice`: a type class for distributive lattices.

## Notations

* `a ⊔ b`: the supremum or join of `a` and `b`
* `a ⊓ b`: the infimum or meet of `a` and `b`

## TODO

* (Semi-)lattice homomorphisms
* Alternative constructors for distributive lattices from the other distributive properties

## Tags

semilattice, lattice

-/

/-- See if the term is `a ⊂ b` and the goal is `a ⊆ b`. -/
@[gcongr_forward] def exactSubsetOfSSubset : Mathlib.Tactic.GCongr.ForwardExt where
  eval h goal := do goal.assignIfDefeq (← Lean.Meta.mkAppM ``subset_of_ssubset #[h])

universe u v w

variable {α : Type u} {β : Type v}

#align le_antisymm' le_antisymm

/-!
### Join-semilattices
-/

-- TODO: automatic construction of dual definitions / theorems
/-- A `SemilatticeSup` is a join-semilattice, that is, a partial order
  with a join (a.k.a. lub / least upper bound, sup / supremum) operation
  `⊔` which is the least element larger than both factors. -/
class SemilatticeSup (α : Type u) extends Sup α, PartialOrder α where
  /-- The supremum is an upper bound on the first argument -/
  protected le_sup_left : ∀ a b : α, a ≤ a ⊔ b
  /-- The supremum is an upper bound on the second argument -/
  protected le_sup_right : ∀ a b : α, b ≤ a ⊔ b
  /-- The supremum is the *least* upper bound -/
  protected sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c
#align semilattice_sup SemilatticeSup

/--
A type with a commutative, associative and idempotent binary `sup` operation has the structure of a
join-semilattice.

The partial order is defined so that `a ≤ b` unfolds to `a ⊔ b = b`; cf. `sup_eq_right`.
-/
def SemilatticeSup.mk' {α : Type*} [Sup α] (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a)
    (sup_assoc : ∀ a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c)) (sup_idem : ∀ a : α, a ⊔ a = a) :
    SemilatticeSup α where
  sup := (· ⊔ ·)
  le a b := a ⊔ b = b
  le_refl := sup_idem
  le_trans a b c hab hbc := by dsimp; rw [← hbc, ← sup_assoc, hab]
  le_antisymm a b hab hba := by rwa [← hba, sup_comm]
  le_sup_left a b := by dsimp; rw [← sup_assoc, sup_idem]
  le_sup_right a b := by dsimp; rw [sup_comm, sup_assoc, sup_idem]
  sup_le a b c hac hbc := by dsimp; rwa [sup_assoc, hbc]
#align semilattice_sup.mk' SemilatticeSup.mk'

instance OrderDual.instSup (α : Type*) [Inf α] : Sup αᵒᵈ :=
  ⟨((· ⊓ ·) : α → α → α)⟩

instance OrderDual.instInf (α : Type*) [Sup α] : Inf αᵒᵈ :=
  ⟨((· ⊔ ·) : α → α → α)⟩

section SemilatticeSup

variable [SemilatticeSup α] {a b c d : α}

@[simp]
theorem le_sup_left : a ≤ a ⊔ b :=
  SemilatticeSup.le_sup_left a b
#align le_sup_left le_sup_left

theorem le_sup_left' : a ≤ a ⊔ b :=
  le_sup_left
#align le_sup_left' le_sup_left'

@[simp]
theorem le_sup_right : b ≤ a ⊔ b :=
  SemilatticeSup.le_sup_right a b
#align le_sup_right le_sup_right

theorem le_sup_right' : b ≤ a ⊔ b :=
  le_sup_right
#align le_sup_right' le_sup_right'

theorem le_sup_of_le_left (h : c ≤ a) : c ≤ a ⊔ b :=
  le_trans h le_sup_left
#align le_sup_of_le_left le_sup_of_le_left

theorem le_sup_of_le_right (h : c ≤ b) : c ≤ a ⊔ b :=
  le_trans h le_sup_right
#align le_sup_of_le_right le_sup_of_le_right

theorem lt_sup_of_lt_left (h : c < a) : c < a ⊔ b :=
  h.trans_le le_sup_left
#align lt_sup_of_lt_left lt_sup_of_lt_left

theorem lt_sup_of_lt_right (h : c < b) : c < a ⊔ b :=
  h.trans_le le_sup_right
#align lt_sup_of_lt_right lt_sup_of_lt_right

theorem sup_le : a ≤ c → b ≤ c → a ⊔ b ≤ c :=
  SemilatticeSup.sup_le a b c
#align sup_le sup_le

@[simp]
theorem sup_le_iff : a ⊔ b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  ⟨fun h : a ⊔ b ≤ c => ⟨le_trans le_sup_left h, le_trans le_sup_right h⟩,
   fun ⟨h₁, h₂⟩ => sup_le h₁ h₂⟩
#align sup_le_iff sup_le_iff

@[simp]
theorem sup_eq_left : a ⊔ b = a ↔ b ≤ a :=
  le_antisymm_iff.trans <| by simp [le_rfl]
#align sup_eq_left sup_eq_left

@[simp]
theorem sup_eq_right : a ⊔ b = b ↔ a ≤ b :=
  le_antisymm_iff.trans <| by simp [le_rfl]
#align sup_eq_right sup_eq_right

@[simp]
theorem left_eq_sup : a = a ⊔ b ↔ b ≤ a :=
  eq_comm.trans sup_eq_left
#align left_eq_sup left_eq_sup

@[simp]
theorem right_eq_sup : b = a ⊔ b ↔ a ≤ b :=
  eq_comm.trans sup_eq_right
#align right_eq_sup right_eq_sup

alias ⟨_, sup_of_le_left⟩ := sup_eq_left
#align sup_of_le_left sup_of_le_left

alias ⟨le_of_sup_eq, sup_of_le_right⟩ := sup_eq_right
#align sup_of_le_right sup_of_le_right
#align le_of_sup_eq le_of_sup_eq

attribute [simp] sup_of_le_left sup_of_le_right

@[simp]
theorem left_lt_sup : a < a ⊔ b ↔ ¬b ≤ a :=
  le_sup_left.lt_iff_ne.trans <| not_congr left_eq_sup
#align left_lt_sup left_lt_sup

@[simp]
theorem right_lt_sup : b < a ⊔ b ↔ ¬a ≤ b :=
  le_sup_right.lt_iff_ne.trans <| not_congr right_eq_sup
#align right_lt_sup right_lt_sup

theorem left_or_right_lt_sup (h : a ≠ b) : a < a ⊔ b ∨ b < a ⊔ b :=
  h.not_le_or_not_le.symm.imp left_lt_sup.2 right_lt_sup.2
#align left_or_right_lt_sup left_or_right_lt_sup

theorem le_iff_exists_sup : a ≤ b ↔ ∃ c, b = a ⊔ c := by
  constructor
  · intro h
    exact ⟨b, (sup_eq_right.mpr h).symm⟩
  · rintro ⟨c, rfl : _ = _ ⊔ _⟩
    exact le_sup_left
#align le_iff_exists_sup le_iff_exists_sup

@[gcongr]
theorem sup_le_sup (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊔ c ≤ b ⊔ d :=
  sup_le (le_sup_of_le_left h₁) (le_sup_of_le_right h₂)
#align sup_le_sup sup_le_sup

@[gcongr]
theorem sup_le_sup_left (h₁ : a ≤ b) (c) : c ⊔ a ≤ c ⊔ b :=
  sup_le_sup le_rfl h₁
#align sup_le_sup_left sup_le_sup_left

@[gcongr]
theorem sup_le_sup_right (h₁ : a ≤ b) (c) : a ⊔ c ≤ b ⊔ c :=
  sup_le_sup h₁ le_rfl
#align sup_le_sup_right sup_le_sup_right

theorem sup_idem (a : α) : a ⊔ a = a := by simp
#align sup_idem sup_idem

instance : Std.IdempotentOp (α := α) (· ⊔ ·) := ⟨sup_idem⟩

theorem sup_comm (a b : α) : a ⊔ b = b ⊔ a := by apply le_antisymm <;> simp
#align sup_comm sup_comm

instance : Std.Commutative (α := α) (· ⊔ ·) := ⟨sup_comm⟩

theorem sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) :=
  eq_of_forall_ge_iff fun x => by simp only [sup_le_iff]; rw [and_assoc]
#align sup_assoc sup_assoc

instance : Std.Associative (α := α)  (· ⊔ ·) := ⟨sup_assoc⟩

theorem sup_left_right_swap (a b c : α) : a ⊔ b ⊔ c = c ⊔ b ⊔ a := by
  rw [sup_comm, sup_comm a, sup_assoc]
#align sup_left_right_swap sup_left_right_swap

theorem sup_left_idem (a b : α) : a ⊔ (a ⊔ b) = a ⊔ b := by simp
#align sup_left_idem sup_left_idem

theorem sup_right_idem (a b : α) : a ⊔ b ⊔ b = a ⊔ b := by simp
#align sup_right_idem sup_right_idem

theorem sup_left_comm (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c) := by
  rw [← sup_assoc, ← sup_assoc, @sup_comm α _ a]
#align sup_left_comm sup_left_comm

theorem sup_right_comm (a b c : α) : a ⊔ b ⊔ c = a ⊔ c ⊔ b := by
  rw [sup_assoc, sup_assoc, sup_comm b]
#align sup_right_comm sup_right_comm

theorem sup_sup_sup_comm (a b c d : α) : a ⊔ b ⊔ (c ⊔ d) = a ⊔ c ⊔ (b ⊔ d) := by
  rw [sup_assoc, sup_left_comm b, ← sup_assoc]
#align sup_sup_sup_comm sup_sup_sup_comm

theorem sup_sup_distrib_left (a b c : α) : a ⊔ (b ⊔ c) = a ⊔ b ⊔ (a ⊔ c) := by
  rw [sup_sup_sup_comm, sup_idem]
#align sup_sup_distrib_left sup_sup_distrib_left

theorem sup_sup_distrib_right (a b c : α) : a ⊔ b ⊔ c = a ⊔ c ⊔ (b ⊔ c) := by
  rw [sup_sup_sup_comm, sup_idem]
#align sup_sup_distrib_right sup_sup_distrib_right

theorem sup_congr_left (hb : b ≤ a ⊔ c) (hc : c ≤ a ⊔ b) : a ⊔ b = a ⊔ c :=
  (sup_le le_sup_left hb).antisymm <| sup_le le_sup_left hc
#align sup_congr_left sup_congr_left

theorem sup_congr_right (ha : a ≤ b ⊔ c) (hb : b ≤ a ⊔ c) : a ⊔ c = b ⊔ c :=
  (sup_le ha le_sup_right).antisymm <| sup_le hb le_sup_right
#align sup_congr_right sup_congr_right

theorem sup_eq_sup_iff_left : a ⊔ b = a ⊔ c ↔ b ≤ a ⊔ c ∧ c ≤ a ⊔ b :=
  ⟨fun h => ⟨h ▸ le_sup_right, h.symm ▸ le_sup_right⟩, fun h => sup_congr_left h.1 h.2⟩
#align sup_eq_sup_iff_left sup_eq_sup_iff_left

theorem sup_eq_sup_iff_right : a ⊔ c = b ⊔ c ↔ a ≤ b ⊔ c ∧ b ≤ a ⊔ c :=
  ⟨fun h => ⟨h ▸ le_sup_left, h.symm ▸ le_sup_left⟩, fun h => sup_congr_right h.1 h.2⟩
#align sup_eq_sup_iff_right sup_eq_sup_iff_right

theorem Ne.lt_sup_or_lt_sup (hab : a ≠ b) : a < a ⊔ b ∨ b < a ⊔ b :=
  hab.symm.not_le_or_not_le.imp left_lt_sup.2 right_lt_sup.2
#align ne.lt_sup_or_lt_sup Ne.lt_sup_or_lt_sup

/-- If `f` is monotone, `g` is antitone, and `f ≤ g`, then for all `a`, `b` we have `f a ≤ g b`. -/
theorem Monotone.forall_le_of_antitone {β : Type*} [Preorder β] {f g : α → β} (hf : Monotone f)
    (hg : Antitone g) (h : f ≤ g) (m n : α) : f m ≤ g n :=
  calc
    f m ≤ f (m ⊔ n) := hf le_sup_left
    _ ≤ g (m ⊔ n) := h _
    _ ≤ g n := hg le_sup_right
#align monotone.forall_le_of_antitone Monotone.forall_le_of_antitone

theorem SemilatticeSup.ext_sup {α} {A B : SemilatticeSup α}
    (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y)
    (x y : α) :
    (haveI := A; x ⊔ y) = x ⊔ y :=
  eq_of_forall_ge_iff fun c => by simp only [sup_le_iff]; rw [← H, @sup_le_iff α A, H, H]
#align semilattice_sup.ext_sup SemilatticeSup.ext_sup

theorem SemilatticeSup.ext {α} {A B : SemilatticeSup α}
    (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) :
    A = B := by
  have ss : A.toSup = B.toSup := by ext; apply SemilatticeSup.ext_sup H
  cases A
  cases B
  cases PartialOrder.ext H
  congr
#align semilattice_sup.ext SemilatticeSup.ext

theorem ite_le_sup (s s' : α) (P : Prop) [Decidable P] : ite P s s' ≤ s ⊔ s' :=
  if h : P then (if_pos h).trans_le le_sup_left else (if_neg h).trans_le le_sup_right
#align ite_le_sup ite_le_sup

end SemilatticeSup

/-!
### Meet-semilattices
-/


/-- A `SemilatticeInf` is a meet-semilattice, that is, a partial order
  with a meet (a.k.a. glb / greatest lower bound, inf / infimum) operation
  `⊓` which is the greatest element smaller than both factors. -/
class SemilatticeInf (α : Type u) extends Inf α, PartialOrder α where
  /-- The infimum is a lower bound on the first argument -/
  protected inf_le_left : ∀ a b : α, a ⊓ b ≤ a
  /-- The infimum is a lower bound on the second argument -/
  protected inf_le_right : ∀ a b : α, a ⊓ b ≤ b
  /-- The infimum is the *greatest* lower bound -/
  protected le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c
#align semilattice_inf SemilatticeInf

instance OrderDual.instSemilatticeSup (α) [SemilatticeInf α] : SemilatticeSup αᵒᵈ where
  __ := inferInstanceAs (PartialOrder αᵒᵈ)
  __ := inferInstanceAs (Sup αᵒᵈ)
  le_sup_left := @SemilatticeInf.inf_le_left α _
  le_sup_right := @SemilatticeInf.inf_le_right α _
  sup_le := fun _ _ _ hca hcb => @SemilatticeInf.le_inf α _ _ _ _ hca hcb

instance OrderDual.instSemilatticeInf (α) [SemilatticeSup α] : SemilatticeInf αᵒᵈ where
  __ := inferInstanceAs (PartialOrder αᵒᵈ)
  __ := inferInstanceAs (Inf αᵒᵈ)
  inf_le_left := @le_sup_left α _
  inf_le_right := @le_sup_right α _
  le_inf := fun _ _ _ hca hcb => @sup_le α _ _ _ _ hca hcb

theorem SemilatticeSup.dual_dual (α : Type*) [H : SemilatticeSup α] :
    OrderDual.instSemilatticeSup αᵒᵈ = H :=
  SemilatticeSup.ext fun _ _ => Iff.rfl
#align semilattice_sup.dual_dual SemilatticeSup.dual_dual

section SemilatticeInf

variable [SemilatticeInf α] {a b c d : α}

@[simp]
theorem inf_le_left : a ⊓ b ≤ a :=
  SemilatticeInf.inf_le_left a b
#align inf_le_left inf_le_left

theorem inf_le_left' : a ⊓ b ≤ a :=
  SemilatticeInf.inf_le_left a b
#align inf_le_left' inf_le_left'

@[simp]
theorem inf_le_right : a ⊓ b ≤ b :=
  SemilatticeInf.inf_le_right a b
#align inf_le_right inf_le_right

theorem inf_le_right' : a ⊓ b ≤ b :=
  SemilatticeInf.inf_le_right a b
#align inf_le_right' inf_le_right'

theorem le_inf : a ≤ b → a ≤ c → a ≤ b ⊓ c :=
  SemilatticeInf.le_inf a b c
#align le_inf le_inf

theorem inf_le_of_left_le (h : a ≤ c) : a ⊓ b ≤ c :=
  le_trans inf_le_left h
#align inf_le_of_left_le inf_le_of_left_le

theorem inf_le_of_right_le (h : b ≤ c) : a ⊓ b ≤ c :=
  le_trans inf_le_right h
#align inf_le_of_right_le inf_le_of_right_le

theorem inf_lt_of_left_lt (h : a < c) : a ⊓ b < c :=
  lt_of_le_of_lt inf_le_left h
#align inf_lt_of_left_lt inf_lt_of_left_lt

theorem inf_lt_of_right_lt (h : b < c) : a ⊓ b < c :=
  lt_of_le_of_lt inf_le_right h
#align inf_lt_of_right_lt inf_lt_of_right_lt

@[simp]
theorem le_inf_iff : a ≤ b ⊓ c ↔ a ≤ b ∧ a ≤ c :=
  @sup_le_iff αᵒᵈ _ _ _ _
#align le_inf_iff le_inf_iff

@[simp]
theorem inf_eq_left : a ⊓ b = a ↔ a ≤ b :=
  le_antisymm_iff.trans <| by simp [le_rfl]
#align inf_eq_left inf_eq_left

@[simp]
theorem inf_eq_right : a ⊓ b = b ↔ b ≤ a :=
  le_antisymm_iff.trans <| by simp [le_rfl]
#align inf_eq_right inf_eq_right

@[simp]
theorem left_eq_inf : a = a ⊓ b ↔ a ≤ b :=
  eq_comm.trans inf_eq_left
#align left_eq_inf left_eq_inf

@[simp]
theorem right_eq_inf : b = a ⊓ b ↔ b ≤ a :=
  eq_comm.trans inf_eq_right
#align right_eq_inf right_eq_inf

alias ⟨le_of_inf_eq, inf_of_le_left⟩ := inf_eq_left
#align inf_of_le_left inf_of_le_left
#align le_of_inf_eq le_of_inf_eq

alias ⟨_, inf_of_le_right⟩ := inf_eq_right
#align inf_of_le_right inf_of_le_right

attribute [simp] inf_of_le_left inf_of_le_right

@[simp]
theorem inf_lt_left : a ⊓ b < a ↔ ¬a ≤ b :=
  @left_lt_sup αᵒᵈ _ _ _
#align inf_lt_left inf_lt_left

@[simp]
theorem inf_lt_right : a ⊓ b < b ↔ ¬b ≤ a :=
  @right_lt_sup αᵒᵈ _ _ _
#align inf_lt_right inf_lt_right

theorem inf_lt_left_or_right (h : a ≠ b) : a ⊓ b < a ∨ a ⊓ b < b :=
  @left_or_right_lt_sup αᵒᵈ _ _ _ h
#align inf_lt_left_or_right inf_lt_left_or_right

@[gcongr]
theorem inf_le_inf (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊓ c ≤ b ⊓ d :=
  @sup_le_sup αᵒᵈ _ _ _ _ _ h₁ h₂
#align inf_le_inf inf_le_inf

@[gcongr]
theorem inf_le_inf_right (a : α) {b c : α} (h : b ≤ c) : b ⊓ a ≤ c ⊓ a :=
  inf_le_inf h le_rfl
#align inf_le_inf_right inf_le_inf_right

@[gcongr]
theorem inf_le_inf_left (a : α) {b c : α} (h : b ≤ c) : a ⊓ b ≤ a ⊓ c :=
  inf_le_inf le_rfl h
#align inf_le_inf_left inf_le_inf_left

theorem inf_idem (a : α) : a ⊓ a = a := by simp
#align inf_idem inf_idem

instance : Std.IdempotentOp (α := α) (· ⊓ ·) := ⟨inf_idem⟩

theorem inf_comm (a b : α) : a ⊓ b = b ⊓ a := @sup_comm αᵒᵈ _ _ _
#align inf_comm inf_comm

instance : Std.Commutative (α := α) (· ⊓ ·) := ⟨inf_comm⟩

theorem inf_assoc (a b c : α) : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) := @sup_assoc αᵒᵈ _ _ _ _
#align inf_assoc inf_assoc

instance : Std.Associative (α := α) (· ⊓ ·) := ⟨inf_assoc⟩

theorem inf_left_right_swap (a b c : α) : a ⊓ b ⊓ c = c ⊓ b ⊓ a :=
  @sup_left_right_swap αᵒᵈ _ _ _ _
#align inf_left_right_swap inf_left_right_swap

theorem inf_left_idem (a b : α) : a ⊓ (a ⊓ b) = a ⊓ b := by simp
#align inf_left_idem inf_left_idem

theorem inf_right_idem (a b : α) : a ⊓ b ⊓ b = a ⊓ b := by simp
#align inf_right_idem inf_right_idem

theorem inf_left_comm (a b c : α) : a ⊓ (b ⊓ c) = b ⊓ (a ⊓ c) :=
  @sup_left_comm αᵒᵈ _ a b c
#align inf_left_comm inf_left_comm

theorem inf_right_comm (a b c : α) : a ⊓ b ⊓ c = a ⊓ c ⊓ b :=
  @sup_right_comm αᵒᵈ _ a b c
#align inf_right_comm inf_right_comm

theorem inf_inf_inf_comm (a b c d : α) : a ⊓ b ⊓ (c ⊓ d) = a ⊓ c ⊓ (b ⊓ d) :=
  @sup_sup_sup_comm αᵒᵈ _ _ _ _ _
#align inf_inf_inf_comm inf_inf_inf_comm

theorem inf_inf_distrib_left (a b c : α) : a ⊓ (b ⊓ c) = a ⊓ b ⊓ (a ⊓ c) :=
  @sup_sup_distrib_left αᵒᵈ _ _ _ _
#align inf_inf_distrib_left inf_inf_distrib_left

theorem inf_inf_distrib_right (a b c : α) : a ⊓ b ⊓ c = a ⊓ c ⊓ (b ⊓ c) :=
  @sup_sup_distrib_right αᵒᵈ _ _ _ _
#align inf_inf_distrib_right inf_inf_distrib_right

theorem inf_congr_left (hb : a ⊓ c ≤ b) (hc : a ⊓ b ≤ c) : a ⊓ b = a ⊓ c :=
  @sup_congr_left αᵒᵈ _ _ _ _ hb hc
#align inf_congr_left inf_congr_left

theorem inf_congr_right (h1 : b ⊓ c ≤ a) (h2 : a ⊓ c ≤ b) : a ⊓ c = b ⊓ c :=
  @sup_congr_right αᵒᵈ _ _ _ _ h1 h2
#align inf_congr_right inf_congr_right

theorem inf_eq_inf_iff_left : a ⊓ b = a ⊓ c ↔ a ⊓ c ≤ b ∧ a ⊓ b ≤ c :=
  @sup_eq_sup_iff_left αᵒᵈ _ _ _ _
#align inf_eq_inf_iff_left inf_eq_inf_iff_left

theorem inf_eq_inf_iff_right : a ⊓ c = b ⊓ c ↔ b ⊓ c ≤ a ∧ a ⊓ c ≤ b :=
  @sup_eq_sup_iff_right αᵒᵈ _ _ _ _
#align inf_eq_inf_iff_right inf_eq_inf_iff_right

theorem Ne.inf_lt_or_inf_lt : a ≠ b → a ⊓ b < a ∨ a ⊓ b < b :=
  @Ne.lt_sup_or_lt_sup αᵒᵈ _ _ _
#align ne.inf_lt_or_inf_lt Ne.inf_lt_or_inf_lt

theorem SemilatticeInf.ext_inf {α} {A B : SemilatticeInf α}
    (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y)
    (x y : α) :
    (haveI := A; x ⊓ y) = x ⊓ y :=
  eq_of_forall_le_iff fun c => by simp only [le_inf_iff]; rw [← H, @le_inf_iff α A, H, H]
#align semilattice_inf.ext_inf SemilatticeInf.ext_inf

theorem SemilatticeInf.ext {α} {A B : SemilatticeInf α}
    (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) :
    A = B := by
  have ss : A.toInf = B.toInf := by ext; apply SemilatticeInf.ext_inf H
  cases A
  cases B
  cases PartialOrder.ext H
  congr
#align semilattice_inf.ext SemilatticeInf.ext

theorem SemilatticeInf.dual_dual (α : Type*) [H : SemilatticeInf α] :
    OrderDual.instSemilatticeInf αᵒᵈ = H :=
  SemilatticeInf.ext fun _ _ => Iff.rfl
#align semilattice_inf.dual_dual SemilatticeInf.dual_dual

theorem inf_le_ite (s s' : α) (P : Prop) [Decidable P] : s ⊓ s' ≤ ite P s s' :=
  @ite_le_sup αᵒᵈ _ _ _ _ _
#align inf_le_ite inf_le_ite

end SemilatticeInf

/--
A type with a commutative, associative and idempotent binary `inf` operation has the structure of a
meet-semilattice.

The partial order is defined so that `a ≤ b` unfolds to `b ⊓ a = a`; cf. `inf_eq_right`.
-/
def SemilatticeInf.mk' {α : Type*} [Inf α] (inf_comm : ∀ a b : α, a ⊓ b = b ⊓ a)
    (inf_assoc : ∀ a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (inf_idem : ∀ a : α, a ⊓ a = a) :
    SemilatticeInf α := by
  haveI : SemilatticeSup αᵒᵈ := SemilatticeSup.mk' inf_comm inf_assoc inf_idem
  haveI i := OrderDual.instSemilatticeInf αᵒᵈ
  exact i
#align semilattice_inf.mk' SemilatticeInf.mk'

/-!
### Lattices
-/


/-- A lattice is a join-semilattice which is also a meet-semilattice. -/
class Lattice (α : Type u) extends SemilatticeSup α, SemilatticeInf α
#align lattice Lattice

instance OrderDual.instLattice (α) [Lattice α] : Lattice αᵒᵈ where
  __ := OrderDual.instSemilatticeSup α
  __ := OrderDual.instSemilatticeInf α

/-- The partial orders from `SemilatticeSup_mk'` and `SemilatticeInf_mk'` agree
if `sup` and `inf` satisfy the lattice absorption laws `sup_inf_self` (`a ⊔ a ⊓ b = a`)
and `inf_sup_self` (`a ⊓ (a ⊔ b) = a`). -/
theorem semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder
    {α : Type*} [Sup α] [Inf α]
    (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a) (sup_assoc : ∀ a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c))
    (sup_idem : ∀ a : α, a ⊔ a = a) (inf_comm : ∀ a b : α, a ⊓ b = b ⊓ a)
    (inf_assoc : ∀ a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (inf_idem : ∀ a : α, a ⊓ a = a)
    (sup_inf_self : ∀ a b : α, a ⊔ a ⊓ b = a) (inf_sup_self : ∀ a b : α, a ⊓ (a ⊔ b) = a) :
    @SemilatticeSup.toPartialOrder _ (SemilatticeSup.mk' sup_comm sup_assoc sup_idem) =
      @SemilatticeInf.toPartialOrder _ (SemilatticeInf.mk' inf_comm inf_assoc inf_idem) :=
  PartialOrder.ext fun a b =>
    show a ⊔ b = b ↔ b ⊓ a = a from
      ⟨fun h => by rw [← h, inf_comm, inf_sup_self], fun h => by rw [← h, sup_comm, sup_inf_self]⟩
#align semilattice_sup_mk'_partial_order_eq_semilattice_inf_mk'_partial_order semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder

/-- A type with a pair of commutative and associative binary operations which satisfy two absorption
laws relating the two operations has the structure of a lattice.

The partial order is defined so that `a ≤ b` unfolds to `a ⊔ b = b`; cf. `sup_eq_right`.
-/
def Lattice.mk' {α : Type*} [Sup α] [Inf α] (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a)
    (sup_assoc : ∀ a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c)) (inf_comm : ∀ a b : α, a ⊓ b = b ⊓ a)
    (inf_assoc : ∀ a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (sup_inf_self : ∀ a b : α, a ⊔ a ⊓ b = a)
    (inf_sup_self : ∀ a b : α, a ⊓ (a ⊔ b) = a) : Lattice α :=
  have sup_idem : ∀ b : α, b ⊔ b = b := fun b =>
    calc
      b ⊔ b = b ⊔ b ⊓ (b ⊔ b) := by rw [inf_sup_self]
      _ = b := by rw [sup_inf_self]

  have inf_idem : ∀ b : α, b ⊓ b = b := fun b =>
    calc
      b ⊓ b = b ⊓ (b ⊔ b ⊓ b) := by rw [sup_inf_self]
      _ = b := by rw [inf_sup_self]

  let semilatt_inf_inst := SemilatticeInf.mk' inf_comm inf_assoc inf_idem
  let semilatt_sup_inst := SemilatticeSup.mk' sup_comm sup_assoc sup_idem
  have partial_order_eq : @SemilatticeSup.toPartialOrder _ semilatt_sup_inst =
                          @SemilatticeInf.toPartialOrder _ semilatt_inf_inst :=
    semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder _ _ _ _ _ _
      sup_inf_self inf_sup_self
  { semilatt_sup_inst, semilatt_inf_inst with
    inf_le_left := fun a b => by
      rw [partial_order_eq]
      apply inf_le_left,
    inf_le_right := fun a b => by
      rw [partial_order_eq]
      apply inf_le_right,
    le_inf := fun a b c => by
      rw [partial_order_eq]
      apply le_inf }
#align lattice.mk' Lattice.mk'

section Lattice

variable [Lattice α] {a b c d : α}

theorem inf_le_sup : a ⊓ b ≤ a ⊔ b :=
  inf_le_left.trans le_sup_left
#align inf_le_sup inf_le_sup

theorem sup_le_inf : a ⊔ b ≤ a ⊓ b ↔ a = b := by simp [le_antisymm_iff, and_comm]
#align sup_le_inf sup_le_inf

@[simp] lemma inf_eq_sup : a ⊓ b = a ⊔ b ↔ a = b := by rw [← inf_le_sup.ge_iff_eq, sup_le_inf]
#align inf_eq_sup inf_eq_sup
@[simp] lemma sup_eq_inf : a ⊔ b = a ⊓ b ↔ a = b := eq_comm.trans inf_eq_sup
#align sup_eq_inf sup_eq_inf
@[simp] lemma inf_lt_sup : a ⊓ b < a ⊔ b ↔ a ≠ b := by rw [inf_le_sup.lt_iff_ne, Ne, inf_eq_sup]
#align inf_lt_sup inf_lt_sup

lemma inf_eq_and_sup_eq_iff : a ⊓ b = c ∧ a ⊔ b = c ↔ a = c ∧ b = c := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain rfl := sup_eq_inf.1 (h.2.trans h.1.symm)
    simpa using h
  · rintro ⟨rfl, rfl⟩
    exact ⟨inf_idem _, sup_idem _⟩
#align inf_eq_and_sup_eq_iff inf_eq_and_sup_eq_iff

/-!
#### Distributivity laws
-/


-- TODO: better names?
theorem sup_inf_le : a ⊔ b ⊓ c ≤ (a ⊔ b) ⊓ (a ⊔ c) :=
  le_inf (sup_le_sup_left inf_le_left _) (sup_le_sup_left inf_le_right _)
#align sup_inf_le sup_inf_le

theorem le_inf_sup : a ⊓ b ⊔ a ⊓ c ≤ a ⊓ (b ⊔ c) :=
  sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
#align le_inf_sup le_inf_sup

theorem inf_sup_self : a ⊓ (a ⊔ b) = a := by simp
#align inf_sup_self inf_sup_self

theorem sup_inf_self : a ⊔ a ⊓ b = a := by simp
#align sup_inf_self sup_inf_self

theorem sup_eq_iff_inf_eq : a ⊔ b = b ↔ a ⊓ b = a := by rw [sup_eq_right, ← inf_eq_left]
#align sup_eq_iff_inf_eq sup_eq_iff_inf_eq

theorem Lattice.ext {α} {A B : Lattice α} (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) :
    A = B := by
  cases A
  cases B
  cases SemilatticeSup.ext H
  cases SemilatticeInf.ext H
  congr
#align lattice.ext Lattice.ext

end Lattice

/-!
### Distributive lattices
-/


/-- A distributive lattice is a lattice that satisfies any of four
equivalent distributive properties (of `sup` over `inf` or `inf` over `sup`,
on the left or right).

The definition here chooses `le_sup_inf`: `(x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z)`. To prove distributivity
from the dual law, use `DistribLattice.of_inf_sup_le`.

A classic example of a distributive lattice
is the lattice of subsets of a set, and in fact this example is
generic in the sense that every distributive lattice is realizable
as a sublattice of a powerset lattice. -/
class DistribLattice (α) extends Lattice α where
  /-- The infimum distributes over the supremum -/
  protected le_sup_inf : ∀ x y z : α, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z
#align distrib_lattice DistribLattice

section DistribLattice

variable [DistribLattice α] {x y z : α}

theorem le_sup_inf : ∀ {x y z : α}, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z :=
  fun {x y z} => DistribLattice.le_sup_inf x y z
#align le_sup_inf le_sup_inf

theorem sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) :=
  le_antisymm sup_inf_le le_sup_inf
#align sup_inf_left sup_inf_left

theorem sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) := by
  simp only [sup_inf_left, sup_comm _ c, eq_self_iff_true]
#align sup_inf_right sup_inf_right

theorem inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c :=
  calc
    a ⊓ (b ⊔ c) = a ⊓ (a ⊔ c) ⊓ (b ⊔ c) := by rw [inf_sup_self]
    _ = a ⊓ (a ⊓ b ⊔ c) := by simp only [inf_assoc, sup_inf_right, eq_self_iff_true]
    _ = (a ⊔ a ⊓ b) ⊓ (a ⊓ b ⊔ c) := by rw [sup_inf_self]
    _ = (a ⊓ b ⊔ a) ⊓ (a ⊓ b ⊔ c) := by rw [sup_comm]
    _ = a ⊓ b ⊔ a ⊓ c := by rw [sup_inf_left]
#align inf_sup_left inf_sup_left

instance OrderDual.instDistribLattice (α : Type*) [DistribLattice α] : DistribLattice αᵒᵈ where
  __ := inferInstanceAs (Lattice αᵒᵈ)
  le_sup_inf _ _ _ := (inf_sup_left _ _ _).le

theorem inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c := by
  simp only [inf_sup_left, inf_comm _ c, eq_self_iff_true]
#align inf_sup_right inf_sup_right

theorem le_of_inf_le_sup_le (h₁ : x ⊓ z ≤ y ⊓ z) (h₂ : x ⊔ z ≤ y ⊔ z) : x ≤ y :=
  calc
    x ≤ y ⊓ z ⊔ x := le_sup_right
    _ = (y ⊔ x) ⊓ (x ⊔ z) := by rw [sup_inf_right, sup_comm x]
    _ ≤ (y ⊔ x) ⊓ (y ⊔ z) := inf_le_inf_left _ h₂
    _ = y ⊔ x ⊓ z := by rw [← sup_inf_left]
    _ ≤ y ⊔ y ⊓ z := sup_le_sup_left h₁ _
    _ ≤ _ := sup_le (le_refl y) inf_le_left
#align le_of_inf_le_sup_le le_of_inf_le_sup_le

theorem eq_of_inf_eq_sup_eq {a b c : α} (h₁ : b ⊓ a = c ⊓ a) (h₂ : b ⊔ a = c ⊔ a) : b = c :=
  le_antisymm (le_of_inf_le_sup_le (le_of_eq h₁) (le_of_eq h₂))
    (le_of_inf_le_sup_le (le_of_eq h₁.symm) (le_of_eq h₂.symm))
#align eq_of_inf_eq_sup_eq eq_of_inf_eq_sup_eq

end DistribLattice

-- See note [reducible non-instances]
/-- Prove distributivity of an existing lattice from the dual distributive law. -/
abbrev DistribLattice.ofInfSupLe
    [Lattice α] (inf_sup_le : ∀ a b c : α, a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c) : DistribLattice α where
  le_sup_inf := (@OrderDual.instDistribLattice αᵒᵈ {inferInstanceAs (Lattice αᵒᵈ) with
      le_sup_inf := inf_sup_le}).le_sup_inf
#align distrib_lattice.of_inf_sup_le DistribLattice.ofInfSupLe

/-!
### Lattices derived from linear orders
-/


-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.toLattice {α : Type u} [o : LinearOrder α] : Lattice α where
  __ := o
  sup := max
  le_sup_left := le_max_left; le_sup_right := le_max_right; sup_le _ _ _ := max_le
  inf := min
  inf_le_left := min_le_left; inf_le_right := min_le_right; le_inf _ _ _ := le_min

section LinearOrder

variable [LinearOrder α] {a b c d : α}

theorem sup_eq_max : a ⊔ b = max a b :=
  rfl
#align sup_eq_max sup_eq_max

theorem inf_eq_min : a ⊓ b = min a b :=
  rfl
#align inf_eq_min inf_eq_min

theorem sup_ind (a b : α) {p : α → Prop} (ha : p a) (hb : p b) : p (a ⊔ b) :=
  (IsTotal.total a b).elim (fun h : a ≤ b => by rwa [sup_eq_right.2 h]) fun h => by
  rwa [sup_eq_left.2 h]
#align sup_ind sup_ind

@[simp]
theorem le_sup_iff : a ≤ b ⊔ c ↔ a ≤ b ∨ a ≤ c := by
  exact ⟨fun h =>
    (le_total c b).imp
      (fun bc => by rwa [sup_eq_left.2 bc] at h)
      (fun bc => by rwa [sup_eq_right.2 bc] at h),
    fun h => h.elim le_sup_of_le_left le_sup_of_le_right⟩
#align le_sup_iff le_sup_iff

@[simp]
theorem lt_sup_iff : a < b ⊔ c ↔ a < b ∨ a < c := by
  exact ⟨fun h =>
    (le_total c b).imp
      (fun bc => by rwa [sup_eq_left.2 bc] at h)
      (fun bc => by rwa [sup_eq_right.2 bc] at h),
    fun h => h.elim lt_sup_of_lt_left lt_sup_of_lt_right⟩
#align lt_sup_iff lt_sup_iff

@[simp]
theorem sup_lt_iff : b ⊔ c < a ↔ b < a ∧ c < a :=
  ⟨fun h => ⟨le_sup_left.trans_lt h, le_sup_right.trans_lt h⟩,
   fun h => sup_ind (p := (· < a)) b c h.1 h.2⟩
#align sup_lt_iff sup_lt_iff

theorem inf_ind (a b : α) {p : α → Prop} : p a → p b → p (a ⊓ b) :=
  @sup_ind αᵒᵈ _ _ _ _
#align inf_ind inf_ind

@[simp]
theorem inf_le_iff : b ⊓ c ≤ a ↔ b ≤ a ∨ c ≤ a :=
  @le_sup_iff αᵒᵈ _ _ _ _
#align inf_le_iff inf_le_iff

@[simp]
theorem inf_lt_iff : b ⊓ c < a ↔ b < a ∨ c < a :=
  @lt_sup_iff αᵒᵈ _ _ _ _
#align inf_lt_iff inf_lt_iff

@[simp]
theorem lt_inf_iff : a < b ⊓ c ↔ a < b ∧ a < c :=
  @sup_lt_iff αᵒᵈ _ _ _ _
#align lt_inf_iff lt_inf_iff

variable (a b c d)

theorem max_max_max_comm : max (max a b) (max c d) = max (max a c) (max b d) :=
  sup_sup_sup_comm _ _ _ _
#align max_max_max_comm max_max_max_comm

theorem min_min_min_comm : min (min a b) (min c d) = min (min a c) (min b d) :=
  inf_inf_inf_comm _ _ _ _
#align min_min_min_comm min_min_min_comm

end LinearOrder

theorem sup_eq_maxDefault [SemilatticeSup α] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    [IsTotal α (· ≤ ·)] :
    (· ⊔ ·) = (maxDefault : α → α → α) := by
  ext x y
  unfold maxDefault
  split_ifs with h'
  exacts [sup_of_le_right h', sup_of_le_left <| (total_of (· ≤ ·) x y).resolve_left h']
#align sup_eq_max_default sup_eq_maxDefault

theorem inf_eq_minDefault [SemilatticeInf α] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    [IsTotal α (· ≤ ·)] :
    (· ⊓ ·) = (minDefault : α → α → α) := by
  ext x y
  unfold minDefault
  split_ifs with h'
  exacts [inf_of_le_left h', inf_of_le_right <| (total_of (· ≤ ·) x y).resolve_left h']
#align inf_eq_min_default inf_eq_minDefault

/-- A lattice with total order is a linear order.

See note [reducible non-instances]. -/
abbrev Lattice.toLinearOrder (α : Type u) [Lattice α] [DecidableEq α]
    [DecidableRel ((· ≤ ·) : α → α → Prop)]
    [DecidableRel ((· < ·) : α → α → Prop)] [IsTotal α (· ≤ ·)] : LinearOrder α where
  __ := ‹Lattice α›
  decidableLE := ‹_›
  decidableEq := ‹_›
  decidableLT := ‹_›
  le_total := total_of (· ≤ ·)
  max := (· ⊔ ·)
  max_def := by exact congr_fun₂ sup_eq_maxDefault
  min := (· ⊓ ·)
  min_def := by exact congr_fun₂ inf_eq_minDefault
#align lattice.to_linear_order Lattice.toLinearOrder

-- see Note [lower instance priority]
instance (priority := 100) {α : Type u} [LinearOrder α] : DistribLattice α where
  __ := inferInstanceAs (Lattice α)
  le_sup_inf _ b c :=
    match le_total b c with
    | Or.inl h => inf_le_of_left_le <| sup_le_sup_left (le_inf (le_refl b) h) _
    | Or.inr h => inf_le_of_right_le <| sup_le_sup_left (le_inf h (le_refl c)) _

instance : DistribLattice ℕ := inferInstance
instance : Lattice ℤ := inferInstance

/-! ### Dual order -/


open OrderDual

@[simp]
theorem ofDual_inf [Sup α] (a b : αᵒᵈ) : ofDual (a ⊓ b) = ofDual a ⊔ ofDual b :=
  rfl
#align of_dual_inf ofDual_inf

@[simp]
theorem ofDual_sup [Inf α] (a b : αᵒᵈ) : ofDual (a ⊔ b) = ofDual a ⊓ ofDual b :=
  rfl
#align of_dual_sup ofDual_sup

@[simp]
theorem toDual_inf [Inf α] (a b : α) : toDual (a ⊓ b) = toDual a ⊔ toDual b :=
  rfl
#align to_dual_inf toDual_inf

@[simp]
theorem toDual_sup [Sup α] (a b : α) : toDual (a ⊔ b) = toDual a ⊓ toDual b :=
  rfl
#align to_dual_sup toDual_sup

section LinearOrder

variable [LinearOrder α]

@[simp]
theorem ofDual_min (a b : αᵒᵈ) : ofDual (min a b) = max (ofDual a) (ofDual b) :=
  rfl
#align of_dual_min ofDual_min

@[simp]
theorem ofDual_max (a b : αᵒᵈ) : ofDual (max a b) = min (ofDual a) (ofDual b) :=
  rfl
#align of_dual_max ofDual_max

@[simp]
theorem toDual_min (a b : α) : toDual (min a b) = max (toDual a) (toDual b) :=
  rfl
#align to_dual_min toDual_min

@[simp]
theorem toDual_max (a b : α) : toDual (max a b) = min (toDual a) (toDual b) :=
  rfl
#align to_dual_max toDual_max

end LinearOrder

/-! ### Function lattices -/


namespace Pi

variable {ι : Type*} {α' : ι → Type*}

instance [∀ i, Sup (α' i)] : Sup (∀ i, α' i) :=
  ⟨fun f g i => f i ⊔ g i⟩

@[simp]
theorem sup_apply [∀ i, Sup (α' i)] (f g : ∀ i, α' i) (i : ι) : (f ⊔ g) i = f i ⊔ g i :=
  rfl
#align pi.sup_apply Pi.sup_apply

theorem sup_def [∀ i, Sup (α' i)] (f g : ∀ i, α' i) : f ⊔ g = fun i => f i ⊔ g i :=
  rfl
#align pi.sup_def Pi.sup_def

instance [∀ i, Inf (α' i)] : Inf (∀ i, α' i) :=
  ⟨fun f g i => f i ⊓ g i⟩

@[simp]
theorem inf_apply [∀ i, Inf (α' i)] (f g : ∀ i, α' i) (i : ι) : (f ⊓ g) i = f i ⊓ g i :=
  rfl
#align pi.inf_apply Pi.inf_apply

theorem inf_def [∀ i, Inf (α' i)] (f g : ∀ i, α' i) : f ⊓ g = fun i => f i ⊓ g i :=
  rfl
#align pi.inf_def Pi.inf_def

instance instSemilatticeSup [∀ i, SemilatticeSup (α' i)] : SemilatticeSup (∀ i, α' i) where
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ ac bc i := sup_le (ac i) (bc i)

instance instSemilatticeInf [∀ i, SemilatticeInf (α' i)] : SemilatticeInf (∀ i, α' i) where
  inf_le_left _ _ _ := inf_le_left
  inf_le_right _ _ _ := inf_le_right
  le_inf _ _ _ ac bc i := le_inf (ac i) (bc i)

instance instLattice [∀ i, Lattice (α' i)] : Lattice (∀ i, α' i) where
  __ := inferInstanceAs (SemilatticeSup (∀ i, α' i))
  __ := inferInstanceAs (SemilatticeInf (∀ i, α' i))

instance instDistribLattice [∀ i, DistribLattice (α' i)] : DistribLattice (∀ i, α' i) where
  le_sup_inf _ _ _ _ := le_sup_inf

end Pi

namespace Function

variable {ι : Type*} {π : ι → Type*} [DecidableEq ι]

-- Porting note: Dot notation on `Function.update` broke
theorem update_sup [∀ i, SemilatticeSup (π i)] (f : ∀ i, π i) (i : ι) (a b : π i) :
    update f i (a ⊔ b) = update f i a ⊔ update f i b :=
  funext fun j => by obtain rfl | hji := eq_or_ne j i <;> simp [update_noteq, *]
#align function.update_sup Function.update_sup

theorem update_inf [∀ i, SemilatticeInf (π i)] (f : ∀ i, π i) (i : ι) (a b : π i) :
    update f i (a ⊓ b) = update f i a ⊓ update f i b :=
  funext fun j => by obtain rfl | hji := eq_or_ne j i <;> simp [update_noteq, *]
#align function.update_inf Function.update_inf

end Function

/-!
### Monotone functions and lattices
-/


namespace Monotone

/-- Pointwise supremum of two monotone functions is a monotone function. -/
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α → β} (hf : Monotone f)
    (hg : Monotone g) :
    Monotone (f ⊔ g) := fun _ _ h => sup_le_sup (hf h) (hg h)
#align monotone.sup Monotone.sup

/-- Pointwise infimum of two monotone functions is a monotone function. -/
protected theorem inf [Preorder α] [SemilatticeInf β] {f g : α → β} (hf : Monotone f)
    (hg : Monotone g) :
    Monotone (f ⊓ g) := fun _ _ h => inf_le_inf (hf h) (hg h)
#align monotone.inf Monotone.inf

/-- Pointwise maximum of two monotone functions is a monotone function. -/
protected theorem max [Preorder α] [LinearOrder β] {f g : α → β} (hf : Monotone f)
    (hg : Monotone g) :
    Monotone fun x => max (f x) (g x) :=
  hf.sup hg
#align monotone.max Monotone.max

/-- Pointwise minimum of two monotone functions is a monotone function. -/
protected theorem min [Preorder α] [LinearOrder β] {f g : α → β} (hf : Monotone f)
    (hg : Monotone g) :
    Monotone fun x => min (f x) (g x) :=
  hf.inf hg
#align monotone.min Monotone.min

theorem le_map_sup [SemilatticeSup α] [SemilatticeSup β] {f : α → β} (h : Monotone f) (x y : α) :
    f x ⊔ f y ≤ f (x ⊔ y) :=
  sup_le (h le_sup_left) (h le_sup_right)
#align monotone.le_map_sup Monotone.le_map_sup

theorem map_inf_le [SemilatticeInf α] [SemilatticeInf β] {f : α → β} (h : Monotone f) (x y : α) :
    f (x ⊓ y) ≤ f x ⊓ f y :=
  le_inf (h inf_le_left) (h inf_le_right)
#align monotone.map_inf_le Monotone.map_inf_le

theorem of_map_inf [SemilatticeInf α] [SemilatticeInf β] {f : α → β}
    (h : ∀ x y, f (x ⊓ y) = f x ⊓ f y) : Monotone f :=
  fun x y hxy => inf_eq_left.1 <| by rw [← h, inf_eq_left.2 hxy]
#align monotone.of_map_inf Monotone.of_map_inf

theorem of_map_sup [SemilatticeSup α] [SemilatticeSup β] {f : α → β}
    (h : ∀ x y, f (x ⊔ y) = f x ⊔ f y) : Monotone f :=
  (@of_map_inf (OrderDual α) (OrderDual β) _ _ _ h).dual
#align monotone.of_map_sup Monotone.of_map_sup

variable [LinearOrder α]

theorem map_sup [SemilatticeSup β] {f : α → β} (hf : Monotone f) (x y : α) :
    f (x ⊔ y) = f x ⊔ f y :=
  (IsTotal.total x y).elim (fun h : x ≤ y => by simp only [h, hf h, sup_of_le_right]) fun h => by
    simp only [h, hf h, sup_of_le_left]
#align monotone.map_sup Monotone.map_sup

theorem map_inf [SemilatticeInf β] {f : α → β} (hf : Monotone f) (x y : α) :
    f (x ⊓ y) = f x ⊓ f y :=
  hf.dual.map_sup _ _
#align monotone.map_inf Monotone.map_inf

end Monotone

namespace MonotoneOn
variable {f : α → β} {s : Set α} {x y : α}

/-- Pointwise supremum of two monotone functions is a monotone function. -/
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α → β} {s : Set α}
    (hf : MonotoneOn f s) (hg : MonotoneOn g s) : MonotoneOn (f ⊔ g) s :=
  fun _ hx _ hy h => sup_le_sup (hf hx hy h) (hg hx hy h)
#align monotone_on.sup MonotoneOn.sup

/-- Pointwise infimum of two monotone functions is a monotone function. -/
protected theorem inf [Preorder α] [SemilatticeInf β] {f g : α → β} {s : Set α}
    (hf : MonotoneOn f s) (hg : MonotoneOn g s) : MonotoneOn (f ⊓ g) s :=
  (hf.dual.sup hg.dual).dual
#align monotone_on.inf MonotoneOn.inf

/-- Pointwise maximum of two monotone functions is a monotone function. -/
protected theorem max [Preorder α] [LinearOrder β] {f g : α → β} {s : Set α} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (fun x => max (f x) (g x)) s :=
  hf.sup hg
#align monotone_on.max MonotoneOn.max

/-- Pointwise minimum of two monotone functions is a monotone function. -/
protected theorem min [Preorder α] [LinearOrder β] {f g : α → β} {s : Set α} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (fun x => min (f x) (g x)) s :=
  hf.inf hg
#align monotone_on.min MonotoneOn.min

theorem of_map_inf [SemilatticeInf α] [SemilatticeInf β]
    (h : ∀ x ∈ s, ∀ y ∈ s, f (x ⊓ y) = f x ⊓ f y) : MonotoneOn f s := fun x hx y hy hxy =>
  inf_eq_left.1 <| by rw [← h _ hx _ hy, inf_eq_left.2 hxy]
#align monotone_on.of_map_inf MonotoneOn.of_map_inf

theorem of_map_sup [SemilatticeSup α] [SemilatticeSup β]
    (h : ∀ x ∈ s, ∀ y ∈ s, f (x ⊔ y) = f x ⊔ f y) : MonotoneOn f s :=
  (@of_map_inf αᵒᵈ βᵒᵈ _ _ _ _ h).dual
#align monotone_on.of_map_sup MonotoneOn.of_map_sup

variable [LinearOrder α]

theorem map_sup [SemilatticeSup β] (hf : MonotoneOn f s) (hx : x ∈ s) (hy : y ∈ s) :
    f (x ⊔ y) = f x ⊔ f y := by
  cases le_total x y <;> have := hf ?_ ?_ ‹_› <;>
    first
    | assumption
    | simp only [*, sup_of_le_left, sup_of_le_right]
#align monotone_on.map_sup MonotoneOn.map_sup

theorem map_inf [SemilatticeInf β] (hf : MonotoneOn f s) (hx : x ∈ s) (hy : y ∈ s) :
    f (x ⊓ y) = f x ⊓ f y :=
  hf.dual.map_sup hx hy
#align monotone_on.map_inf MonotoneOn.map_inf

end MonotoneOn

namespace Antitone

/-- Pointwise supremum of two monotone functions is a monotone function. -/
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α → β} (hf : Antitone f)
    (hg : Antitone g) :
    Antitone (f ⊔ g) := fun _ _ h => sup_le_sup (hf h) (hg h)
#align antitone.sup Antitone.sup

/-- Pointwise infimum of two monotone functions is a monotone function. -/
protected theorem inf [Preorder α] [SemilatticeInf β] {f g : α → β} (hf : Antitone f)
    (hg : Antitone g) :
    Antitone (f ⊓ g) := fun _ _ h => inf_le_inf (hf h) (hg h)
#align antitone.inf Antitone.inf

/-- Pointwise maximum of two monotone functions is a monotone function. -/
protected theorem max [Preorder α] [LinearOrder β] {f g : α → β} (hf : Antitone f)
    (hg : Antitone g) :
    Antitone fun x => max (f x) (g x) :=
  hf.sup hg
#align antitone.max Antitone.max

/-- Pointwise minimum of two monotone functions is a monotone function. -/
protected theorem min [Preorder α] [LinearOrder β] {f g : α → β} (hf : Antitone f)
    (hg : Antitone g) :
    Antitone fun x => min (f x) (g x) :=
  hf.inf hg
#align antitone.min Antitone.min

theorem map_sup_le [SemilatticeSup α] [SemilatticeInf β] {f : α → β} (h : Antitone f) (x y : α) :
    f (x ⊔ y) ≤ f x ⊓ f y :=
  h.dual_right.le_map_sup x y
#align antitone.map_sup_le Antitone.map_sup_le

theorem le_map_inf [SemilatticeInf α] [SemilatticeSup β] {f : α → β} (h : Antitone f) (x y : α) :
    f x ⊔ f y ≤ f (x ⊓ y) :=
  h.dual_right.map_inf_le x y
#align antitone.le_map_inf Antitone.le_map_inf

variable [LinearOrder α]

theorem map_sup [SemilatticeInf β] {f : α → β} (hf : Antitone f) (x y : α) :
    f (x ⊔ y) = f x ⊓ f y :=
  hf.dual_right.map_sup x y
#align antitone.map_sup Antitone.map_sup

theorem map_inf [SemilatticeSup β] {f : α → β} (hf : Antitone f) (x y : α) :
    f (x ⊓ y) = f x ⊔ f y :=
  hf.dual_right.map_inf x y
#align antitone.map_inf Antitone.map_inf

end Antitone

namespace AntitoneOn
variable {f : α → β} {s : Set α} {x y : α}

/-- Pointwise supremum of two antitone functions is an antitone function. -/
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α → β} {s : Set α}
    (hf : AntitoneOn f s) (hg : AntitoneOn g s) : AntitoneOn (f ⊔ g) s :=
  fun _ hx _ hy h => sup_le_sup (hf hx hy h) (hg hx hy h)
#align antitone_on.sup AntitoneOn.sup

/-- Pointwise infimum of two antitone functions is an antitone function. -/
protected theorem inf [Preorder α] [SemilatticeInf β] {f g : α → β} {s : Set α}
    (hf : AntitoneOn f s) (hg : AntitoneOn g s) : AntitoneOn (f ⊓ g) s :=
  (hf.dual.sup hg.dual).dual
#align antitone_on.inf AntitoneOn.inf

/-- Pointwise maximum of two antitone functions is an antitone function. -/
protected theorem max [Preorder α] [LinearOrder β] {f g : α → β} {s : Set α} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => max (f x) (g x)) s :=
  hf.sup hg
#align antitone_on.max AntitoneOn.max

/-- Pointwise minimum of two antitone functions is an antitone function. -/
protected theorem min [Preorder α] [LinearOrder β] {f g : α → β} {s : Set α} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => min (f x) (g x)) s :=
  hf.inf hg
#align antitone_on.min AntitoneOn.min

theorem of_map_inf [SemilatticeInf α] [SemilatticeSup β]
    (h : ∀ x ∈ s, ∀ y ∈ s, f (x ⊓ y) = f x ⊔ f y) : AntitoneOn f s := fun x hx y hy hxy =>
  sup_eq_left.1 <| by rw [← h _ hx _ hy, inf_eq_left.2 hxy]
#align antitone_on.of_map_inf AntitoneOn.of_map_inf

theorem of_map_sup [SemilatticeSup α] [SemilatticeInf β]
    (h : ∀ x ∈ s, ∀ y ∈ s, f (x ⊔ y) = f x ⊓ f y) : AntitoneOn f s :=
  (@of_map_inf αᵒᵈ βᵒᵈ _ _ _ _ h).dual
#align antitone_on.of_map_sup AntitoneOn.of_map_sup

variable [LinearOrder α]

theorem map_sup [SemilatticeInf β] (hf : AntitoneOn f s) (hx : x ∈ s) (hy : y ∈ s) :
    f (x ⊔ y) = f x ⊓ f y := by
  cases le_total x y <;> have := hf ?_ ?_ ‹_› <;>
    first
    | assumption
    | simp only [*, sup_of_le_left, sup_of_le_right, inf_of_le_left, inf_of_le_right]
#align antitone_on.map_sup AntitoneOn.map_sup

theorem map_inf [SemilatticeSup β] (hf : AntitoneOn f s) (hx : x ∈ s) (hy : y ∈ s) :
    f (x ⊓ y) = f x ⊔ f y :=
  hf.dual.map_sup hx hy
#align antitone_on.map_inf AntitoneOn.map_inf

end AntitoneOn

/-!
### Products of (semi-)lattices
-/


namespace Prod

variable (α β)

instance [Sup α] [Sup β] : Sup (α × β) :=
  ⟨fun p q => ⟨p.1 ⊔ q.1, p.2 ⊔ q.2⟩⟩

instance [Inf α] [Inf β] : Inf (α × β) :=
  ⟨fun p q => ⟨p.1 ⊓ q.1, p.2 ⊓ q.2⟩⟩

@[simp]
theorem mk_sup_mk [Sup α] [Sup β] (a₁ a₂ : α) (b₁ b₂ : β) :
    (a₁, b₁) ⊔ (a₂, b₂) = (a₁ ⊔ a₂, b₁ ⊔ b₂) :=
  rfl
#align prod.mk_sup_mk Prod.mk_sup_mk

@[simp]
theorem mk_inf_mk [Inf α] [Inf β] (a₁ a₂ : α) (b₁ b₂ : β) :
    (a₁, b₁) ⊓ (a₂, b₂) = (a₁ ⊓ a₂, b₁ ⊓ b₂) :=
  rfl
#align prod.mk_inf_mk Prod.mk_inf_mk

@[simp]
theorem fst_sup [Sup α] [Sup β] (p q : α × β) : (p ⊔ q).fst = p.fst ⊔ q.fst :=
  rfl
#align prod.fst_sup Prod.fst_sup

@[simp]
theorem fst_inf [Inf α] [Inf β] (p q : α × β) : (p ⊓ q).fst = p.fst ⊓ q.fst :=
  rfl
#align prod.fst_inf Prod.fst_inf

@[simp]
theorem snd_sup [Sup α] [Sup β] (p q : α × β) : (p ⊔ q).snd = p.snd ⊔ q.snd :=
  rfl
#align prod.snd_sup Prod.snd_sup

@[simp]
theorem snd_inf [Inf α] [Inf β] (p q : α × β) : (p ⊓ q).snd = p.snd ⊓ q.snd :=
  rfl
#align prod.snd_inf Prod.snd_inf

@[simp]
theorem swap_sup [Sup α] [Sup β] (p q : α × β) : (p ⊔ q).swap = p.swap ⊔ q.swap :=
  rfl
#align prod.swap_sup Prod.swap_sup

@[simp]
theorem swap_inf [Inf α] [Inf β] (p q : α × β) : (p ⊓ q).swap = p.swap ⊓ q.swap :=
  rfl
#align prod.swap_inf Prod.swap_inf

theorem sup_def [Sup α] [Sup β] (p q : α × β) : p ⊔ q = (p.fst ⊔ q.fst, p.snd ⊔ q.snd) :=
  rfl
#align prod.sup_def Prod.sup_def

theorem inf_def [Inf α] [Inf β] (p q : α × β) : p ⊓ q = (p.fst ⊓ q.fst, p.snd ⊓ q.snd) :=
  rfl
#align prod.inf_def Prod.inf_def

instance instSemilatticeSup [SemilatticeSup α] [SemilatticeSup β] : SemilatticeSup (α × β) where
  __ := inferInstanceAs (PartialOrder (α × β))
  __ := inferInstanceAs (Sup (α × β))
  sup_le _ _ _ h₁ h₂ := ⟨sup_le h₁.1 h₂.1, sup_le h₁.2 h₂.2⟩
  le_sup_left _ _ := ⟨le_sup_left, le_sup_left⟩
  le_sup_right _ _ := ⟨le_sup_right, le_sup_right⟩

instance instSemilatticeInf [SemilatticeInf α] [SemilatticeInf β] : SemilatticeInf (α × β) where
  __ := inferInstanceAs (PartialOrder (α × β))
  __ := inferInstanceAs (Inf (α × β))
  le_inf _ _ _ h₁ h₂ := ⟨le_inf h₁.1 h₂.1, le_inf h₁.2 h₂.2⟩
  inf_le_left _ _ := ⟨inf_le_left, inf_le_left⟩
  inf_le_right _ _ := ⟨inf_le_right, inf_le_right⟩

instance instLattice [Lattice α] [Lattice β] : Lattice (α × β) where
  __ := inferInstanceAs (SemilatticeSup (α × β))
  __ := inferInstanceAs (SemilatticeInf (α × β))

instance instDistribLattice [DistribLattice α] [DistribLattice β] : DistribLattice (α × β) where
  __ := inferInstanceAs (Lattice (α × β))
  le_sup_inf _ _ _ := ⟨le_sup_inf, le_sup_inf⟩

end Prod

/-!
### Subtypes of (semi-)lattices
-/


namespace Subtype

/-- A subtype forms a `⊔`-semilattice if `⊔` preserves the property.
See note [reducible non-instances]. -/
protected abbrev semilatticeSup [SemilatticeSup α] {P : α → Prop}
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) :
    SemilatticeSup { x : α // P x } where
  sup x y := ⟨x.1 ⊔ y.1, Psup x.2 y.2⟩
  le_sup_left _ _ := le_sup_left
  le_sup_right _ _ := le_sup_right
  sup_le _ _ _ h1 h2 := sup_le h1 h2
#align subtype.semilattice_sup Subtype.semilatticeSup

/-- A subtype forms a `⊓`-semilattice if `⊓` preserves the property.
See note [reducible non-instances]. -/
protected abbrev semilatticeInf [SemilatticeInf α] {P : α → Prop}
    (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) :
    SemilatticeInf { x : α // P x } where
  inf x y := ⟨x.1 ⊓ y.1, Pinf x.2 y.2⟩
  inf_le_left _ _ := inf_le_left
  inf_le_right _ _ := inf_le_right
  le_inf _ _ _ h1 h2 := le_inf h1 h2
#align subtype.semilattice_inf Subtype.semilatticeInf

/-- A subtype forms a lattice if `⊔` and `⊓` preserve the property.
See note [reducible non-instances]. -/
protected abbrev lattice [Lattice α] {P : α → Prop} (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y))
    (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) : Lattice { x : α // P x } where
  __ := Subtype.semilatticeInf Pinf
  __ := Subtype.semilatticeSup Psup
#align subtype.lattice Subtype.lattice

@[simp, norm_cast]
theorem coe_sup [SemilatticeSup α] {P : α → Prop}
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) (x y : Subtype P) :
    (haveI := Subtype.semilatticeSup Psup; (x ⊔ y : Subtype P) : α) = (x ⊔ y : α) :=
  rfl
#align subtype.coe_sup Subtype.coe_sup

@[simp, norm_cast]
theorem coe_inf [SemilatticeInf α] {P : α → Prop}
    (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) (x y : Subtype P) :
    (haveI := Subtype.semilatticeInf Pinf; (x ⊓ y : Subtype P) : α) = (x ⊓ y : α) :=
  rfl
#align subtype.coe_inf Subtype.coe_inf

@[simp]
theorem mk_sup_mk [SemilatticeSup α] {P : α → Prop}
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) {x y : α} (hx : P x) (hy : P y) :
    (haveI := Subtype.semilatticeSup Psup; (⟨x, hx⟩ ⊔ ⟨y, hy⟩ : Subtype P)) =
      ⟨x ⊔ y, Psup hx hy⟩ :=
  rfl
#align subtype.mk_sup_mk Subtype.mk_sup_mk

@[simp]
theorem mk_inf_mk [SemilatticeInf α] {P : α → Prop}
    (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) {x y : α} (hx : P x) (hy : P y) :
    (haveI := Subtype.semilatticeInf Pinf; (⟨x, hx⟩ ⊓ ⟨y, hy⟩ : Subtype P)) =
      ⟨x ⊓ y, Pinf hx hy⟩ :=
  rfl
#align subtype.mk_inf_mk Subtype.mk_inf_mk

end Subtype

section lift

/-- A type endowed with `⊔` is a `SemilatticeSup`, if it admits an injective map that
preserves `⊔` to a `SemilatticeSup`.
See note [reducible non-instances]. -/
protected abbrev Function.Injective.semilatticeSup [Sup α] [SemilatticeSup β] (f : α → β)
    (hf_inj : Function.Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) :
    SemilatticeSup α where
  __ := PartialOrder.lift f hf_inj
  sup := Sup.sup
  le_sup_left a b := by
    change f a ≤ f (a ⊔ b)
    rw [map_sup]
    exact le_sup_left
  le_sup_right a b := by
    change f b ≤ f (a ⊔ b)
    rw [map_sup]
    exact le_sup_right
  sup_le a b c ha hb := by
    change f (a ⊔ b) ≤ f c
    rw [map_sup]
    exact sup_le ha hb
#align function.injective.semilattice_sup Function.Injective.semilatticeSup

/-- A type endowed with `⊓` is a `SemilatticeInf`, if it admits an injective map that
preserves `⊓` to a `SemilatticeInf`.
See note [reducible non-instances]. -/
protected abbrev Function.Injective.semilatticeInf [Inf α] [SemilatticeInf β] (f : α → β)
    (hf_inj : Function.Injective f) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) :
    SemilatticeInf α where
  __ := PartialOrder.lift f hf_inj
  inf := Inf.inf
  inf_le_left a b := by
    change f (a ⊓ b) ≤ f a
    rw [map_inf]
    exact inf_le_left
  inf_le_right a b := by
    change f (a ⊓ b) ≤ f b
    rw [map_inf]
    exact inf_le_right
  le_inf a b c ha hb := by
    change f a ≤ f (b ⊓ c)
    rw [map_inf]
    exact le_inf ha hb
#align function.injective.semilattice_inf Function.Injective.semilatticeInf

/-- A type endowed with `⊔` and `⊓` is a `Lattice`, if it admits an injective map that
preserves `⊔` and `⊓` to a `Lattice`.
See note [reducible non-instances]. -/
protected abbrev Function.Injective.lattice [Sup α] [Inf α] [Lattice β] (f : α → β)
    (hf_inj : Function.Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) :
    Lattice α where
  __ := hf_inj.semilatticeSup f map_sup
  __ := hf_inj.semilatticeInf f map_inf
#align function.injective.lattice Function.Injective.lattice

/-- A type endowed with `⊔` and `⊓` is a `DistribLattice`, if it admits an injective map that
preserves `⊔` and `⊓` to a `DistribLattice`.
See note [reducible non-instances]. -/
protected abbrev Function.Injective.distribLattice [Sup α] [Inf α] [DistribLattice β] (f : α → β)
    (hf_inj : Function.Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) :
    DistribLattice α where
  __ := hf_inj.lattice f map_sup map_inf
  le_sup_inf a b c := by
    change f ((a ⊔ b) ⊓ (a ⊔ c)) ≤ f (a ⊔ b ⊓ c)
    rw [map_inf, map_sup, map_sup, map_sup, map_inf]
    exact le_sup_inf
#align function.injective.distrib_lattice Function.Injective.distribLattice

end lift

namespace ULift

instance [SemilatticeSup α] : SemilatticeSup (ULift.{v} α) :=
  ULift.down_injective.semilatticeSup _ down_sup

instance [SemilatticeInf α] : SemilatticeInf (ULift.{v} α) :=
  ULift.down_injective.semilatticeInf _ down_inf

instance [Lattice α] : Lattice (ULift.{v} α) :=
  ULift.down_injective.lattice _ down_sup down_inf

instance [DistribLattice α] : DistribLattice (ULift.{v} α) :=
  ULift.down_injective.distribLattice _ down_sup down_inf

instance [LinearOrder α] : LinearOrder (ULift.{v} α) :=
  LinearOrder.liftWithOrd ULift.down ULift.down_injective down_sup down_inf
    fun _x _y => (down_compare _ _).symm

end ULift

--To avoid noncomputability poisoning from `Bool.completeBooleanAlgebra`
instance Bool.instDistribLattice : DistribLattice Bool :=
  inferInstance
