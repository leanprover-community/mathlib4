/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Order.Monotone
import Mathbin.Tactic.Simps
import Mathbin.Tactic.PiInstances

/-!
# (Semi-)lattices

Semilattices are partially ordered sets with join (greatest lower bound, or `sup`) or
meet (least upper bound, or `inf`) operations. Lattices are posets that are both
join-semilattices and meet-semilattices.

Distributive lattices are lattices which satisfy any of four equivalent distributivity properties,
of `sup` over `inf`, on the left or on the right.

## Main declarations

* `semilattice_sup`: a type class for join semilattices
* `semilattice_sup.mk'`: an alternative constructor for `semilattice_sup` via proofs that `⊔` is
  commutative, associative and idempotent.
* `semilattice_inf`: a type class for meet semilattices
* `semilattice_sup.mk'`: an alternative constructor for `semilattice_inf` via proofs that `⊓` is
  commutative, associative and idempotent.

* `lattice`: a type class for lattices
* `lattice.mk'`: an alternative constructor for `lattice` via profs that `⊔` and `⊓` are
  commutative, associative and satisfy a pair of "absorption laws".

* `distrib_lattice`: a type class for distributive lattices.

## Notations

* `a ⊔ b`: the supremum or join of `a` and `b`
* `a ⊓ b`: the infimum or meet of `a` and `b`

## TODO

* (Semi-)lattice homomorphisms
* Alternative constructors for distributive lattices from the other distributive properties

## Tags

semilattice, lattice

-/


universe u v w

variable {α : Type u} {β : Type v}

-- TODO: move this eventually, if we decide to use them
attribute [ematch] le_trans lt_of_le_of_lt lt_of_lt_of_le lt_trans

section

-- TODO: this seems crazy, but it also seems to work reasonably well
@[ematch]
theorem le_antisymm' [PartialOrder α] : ∀ {a b : α}, a ≤ b → b ≤ a → a = b :=
  @le_antisymm _ _
#align le_antisymm' le_antisymm'

end

/-!
### Join-semilattices
-/


-- TODO: automatic construction of dual definitions / theorems
/-- A `semilattice_sup` is a join-semilattice, that is, a partial order
  with a join (a.k.a. lub / least upper bound, sup / supremum) operation
  `⊔` which is the least element larger than both factors. -/
@[protect_proj]
class SemilatticeSup (α : Type u) extends HasSup α, PartialOrder α where
  le_sup_left : ∀ a b : α, a ≤ a ⊔ b
  le_sup_right : ∀ a b : α, b ≤ a ⊔ b
  sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c
#align semilattice_sup SemilatticeSup

/-- A type with a commutative, associative and idempotent binary `sup` operation has the structure of a
join-semilattice.

The partial order is defined so that `a ≤ b` unfolds to `a ⊔ b = b`; cf. `sup_eq_right`.
-/
def SemilatticeSup.mk' {α : Type _} [HasSup α] (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a)
    (sup_assoc : ∀ a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c)) (sup_idem : ∀ a : α, a ⊔ a = a) : SemilatticeSup α where
  sup := (· ⊔ ·)
  le a b := a ⊔ b = b
  le_refl := sup_idem
  le_trans a b c hab hbc := by
    dsimp only [(· ≤ ·)] at *
    rwa [← hbc, ← sup_assoc, hab]
  le_antisymm a b hab hba := by
    dsimp only [(· ≤ ·)] at *
    rwa [← hba, sup_comm]
  le_sup_left a b := show a ⊔ (a ⊔ b) = a ⊔ b by rw [← sup_assoc, sup_idem]
  le_sup_right a b := show b ⊔ (a ⊔ b) = a ⊔ b by rw [sup_comm, sup_assoc, sup_idem]
  sup_le a b c hac hbc := by
    dsimp only [(· ≤ ·), Preorder.Le] at *
    rwa [sup_assoc, hbc]
#align semilattice_sup.mk' SemilatticeSup.mk'

instance (α : Type _) [HasInf α] : HasSup αᵒᵈ :=
  ⟨((· ⊓ ·) : α → α → α)⟩

instance (α : Type _) [HasSup α] : HasInf αᵒᵈ :=
  ⟨((· ⊔ ·) : α → α → α)⟩

section SemilatticeSup

variable [SemilatticeSup α] {a b c d : α}

@[simp]
theorem le_sup_left : a ≤ a ⊔ b :=
  SemilatticeSup.le_sup_left a b
#align le_sup_left le_sup_left

@[ematch]
theorem le_sup_left' : a ≤ a ⊔ b :=
  le_sup_left
#align le_sup_left' le_sup_left'

@[simp]
theorem le_sup_right : b ≤ a ⊔ b :=
  SemilatticeSup.le_sup_right a b
#align le_sup_right le_sup_right

@[ematch]
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
  ⟨fun h : a ⊔ b ≤ c => ⟨le_trans le_sup_left h, le_trans le_sup_right h⟩, fun ⟨h₁, h₂⟩ => sup_le h₁ h₂⟩
#align sup_le_iff sup_le_iff

@[simp]
theorem sup_eq_left : a ⊔ b = a ↔ b ≤ a :=
  le_antisymm_iff.trans $ by simp [le_rfl]
#align sup_eq_left sup_eq_left

@[simp]
theorem sup_eq_right : a ⊔ b = b ↔ a ≤ b :=
  le_antisymm_iff.trans $ by simp [le_rfl]
#align sup_eq_right sup_eq_right

@[simp]
theorem left_eq_sup : a = a ⊔ b ↔ b ≤ a :=
  eq_comm.trans sup_eq_left
#align left_eq_sup left_eq_sup

@[simp]
theorem right_eq_sup : b = a ⊔ b ↔ a ≤ b :=
  eq_comm.trans sup_eq_right
#align right_eq_sup right_eq_sup

alias sup_eq_left ↔ _ sup_of_le_left

alias sup_eq_right ↔ le_of_sup_eq sup_of_le_right

attribute [simp] sup_of_le_left sup_of_le_right

@[simp]
theorem left_lt_sup : a < a ⊔ b ↔ ¬b ≤ a :=
  le_sup_left.lt_iff_ne.trans $ not_congr left_eq_sup
#align left_lt_sup left_lt_sup

@[simp]
theorem right_lt_sup : b < a ⊔ b ↔ ¬a ≤ b :=
  le_sup_right.lt_iff_ne.trans $ not_congr right_eq_sup
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

theorem sup_le_sup (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊔ c ≤ b ⊔ d :=
  sup_le (le_sup_of_le_left h₁) (le_sup_of_le_right h₂)
#align sup_le_sup sup_le_sup

theorem sup_le_sup_left (h₁ : a ≤ b) (c) : c ⊔ a ≤ c ⊔ b :=
  sup_le_sup le_rfl h₁
#align sup_le_sup_left sup_le_sup_left

theorem sup_le_sup_right (h₁ : a ≤ b) (c) : a ⊔ c ≤ b ⊔ c :=
  sup_le_sup h₁ le_rfl
#align sup_le_sup_right sup_le_sup_right

@[simp]
theorem sup_idem : a ⊔ a = a := by apply le_antisymm <;> simp
#align sup_idem sup_idem

instance sup_is_idempotent : IsIdempotent α (· ⊔ ·) :=
  ⟨@sup_idem _ _⟩
#align sup_is_idempotent sup_is_idempotent

theorem sup_comm : a ⊔ b = b ⊔ a := by apply le_antisymm <;> simp
#align sup_comm sup_comm

instance sup_is_commutative : IsCommutative α (· ⊔ ·) :=
  ⟨@sup_comm _ _⟩
#align sup_is_commutative sup_is_commutative

theorem sup_assoc : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) :=
  eq_of_forall_ge_iff $ fun x => by simp only [sup_le_iff, and_assoc']
#align sup_assoc sup_assoc

instance sup_is_associative : IsAssociative α (· ⊔ ·) :=
  ⟨@sup_assoc _ _⟩
#align sup_is_associative sup_is_associative

theorem sup_left_right_swap (a b c : α) : a ⊔ b ⊔ c = c ⊔ b ⊔ a := by rw [sup_comm, @sup_comm _ _ a, sup_assoc]
#align sup_left_right_swap sup_left_right_swap

@[simp]
theorem sup_left_idem : a ⊔ (a ⊔ b) = a ⊔ b := by rw [← sup_assoc, sup_idem]
#align sup_left_idem sup_left_idem

@[simp]
theorem sup_right_idem : a ⊔ b ⊔ b = a ⊔ b := by rw [sup_assoc, sup_idem]
#align sup_right_idem sup_right_idem

theorem sup_left_comm (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c) := by rw [← sup_assoc, ← sup_assoc, @sup_comm α _ a]
#align sup_left_comm sup_left_comm

theorem sup_right_comm (a b c : α) : a ⊔ b ⊔ c = a ⊔ c ⊔ b := by rw [sup_assoc, sup_assoc, @sup_comm _ _ b]
#align sup_right_comm sup_right_comm

theorem sup_sup_sup_comm (a b c d : α) : a ⊔ b ⊔ (c ⊔ d) = a ⊔ c ⊔ (b ⊔ d) := by
  rw [sup_assoc, sup_left_comm b, ← sup_assoc]
#align sup_sup_sup_comm sup_sup_sup_comm

theorem sup_sup_distrib_left (a b c : α) : a ⊔ (b ⊔ c) = a ⊔ b ⊔ (a ⊔ c) := by rw [sup_sup_sup_comm, sup_idem]
#align sup_sup_distrib_left sup_sup_distrib_left

theorem sup_sup_distrib_right (a b c : α) : a ⊔ b ⊔ c = a ⊔ c ⊔ (b ⊔ c) := by rw [sup_sup_sup_comm, sup_idem]
#align sup_sup_distrib_right sup_sup_distrib_right

theorem sup_congr_left (hb : b ≤ a ⊔ c) (hc : c ≤ a ⊔ b) : a ⊔ b = a ⊔ c :=
  (sup_le le_sup_left hb).antisymm $ sup_le le_sup_left hc
#align sup_congr_left sup_congr_left

theorem sup_congr_right (ha : a ≤ b ⊔ c) (hb : b ≤ a ⊔ c) : a ⊔ c = b ⊔ c :=
  (sup_le ha le_sup_right).antisymm $ sup_le hb le_sup_right
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
theorem Monotone.forall_le_of_antitone {β : Type _} [Preorder β] {f g : α → β} (hf : Monotone f) (hg : Antitone g)
    (h : f ≤ g) (m n : α) : f m ≤ g n :=
  calc
    f m ≤ f (m ⊔ n) := hf le_sup_left
    _ ≤ g (m ⊔ n) := h _
    _ ≤ g n := hg le_sup_right
    
#align monotone.forall_le_of_antitone Monotone.forall_le_of_antitone

theorem SemilatticeSup.ext_sup {α} {A B : SemilatticeSup α}
    (H :
      ∀ x y : α,
        (haveI := A
          x ≤ y) ↔
          x ≤ y)
    (x y : α) :
    (haveI := A
      x ⊔ y) =
      x ⊔ y :=
  eq_of_forall_ge_iff $ fun c => by simp only [sup_le_iff] <;> rw [← H, @sup_le_iff α A, H, H]
#align semilattice_sup.ext_sup SemilatticeSup.ext_sup

theorem SemilatticeSup.ext {α} {A B : SemilatticeSup α}
    (H :
      ∀ x y : α,
        (haveI := A
          x ≤ y) ↔
          x ≤ y) :
    A = B := by
  have := PartialOrder.ext H
  have ss := funext fun x => funext $ SemilatticeSup.ext_sup H x
  cases A
  cases B
  injection this <;> congr
#align semilattice_sup.ext SemilatticeSup.ext

theorem ite_le_sup (s s' : α) (P : Prop) [Decidable P] : ite P s s' ≤ s ⊔ s' :=
  if h : P then (if_pos h).trans_le le_sup_left else (if_neg h).trans_le le_sup_right
#align ite_le_sup ite_le_sup

end SemilatticeSup

/-!
### Meet-semilattices
-/


/-- A `semilattice_inf` is a meet-semilattice, that is, a partial order
  with a meet (a.k.a. glb / greatest lower bound, inf / infimum) operation
  `⊓` which is the greatest element smaller than both factors. -/
@[protect_proj]
class SemilatticeInf (α : Type u) extends HasInf α, PartialOrder α where
  inf_le_left : ∀ a b : α, a ⊓ b ≤ a
  inf_le_right : ∀ a b : α, a ⊓ b ≤ b
  le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c
#align semilattice_inf SemilatticeInf

instance (α) [SemilatticeInf α] : SemilatticeSup αᵒᵈ :=
  { OrderDual.partialOrder α, OrderDual.hasSup α with le_sup_left := SemilatticeInf.inf_le_left,
    le_sup_right := SemilatticeInf.inf_le_right,
    sup_le := fun a b c hca hcb => @SemilatticeInf.le_inf α _ _ _ _ hca hcb }

instance (α) [SemilatticeSup α] : SemilatticeInf αᵒᵈ :=
  { OrderDual.partialOrder α, OrderDual.hasInf α with inf_le_left := @le_sup_left α _,
    inf_le_right := @le_sup_right α _, le_inf := fun a b c hca hcb => @sup_le α _ _ _ _ hca hcb }

theorem SemilatticeSup.dual_dual (α : Type _) [H : SemilatticeSup α] : OrderDual.semilatticeSup αᵒᵈ = H :=
  SemilatticeSup.ext $ fun _ _ => Iff.rfl
#align semilattice_sup.dual_dual SemilatticeSup.dual_dual

section SemilatticeInf

variable [SemilatticeInf α] {a b c d : α}

@[simp]
theorem inf_le_left : a ⊓ b ≤ a :=
  SemilatticeInf.inf_le_left a b
#align inf_le_left inf_le_left

@[ematch]
theorem inf_le_left' : a ⊓ b ≤ a :=
  SemilatticeInf.inf_le_left a b
#align inf_le_left' inf_le_left'

@[simp]
theorem inf_le_right : a ⊓ b ≤ b :=
  SemilatticeInf.inf_le_right a b
#align inf_le_right inf_le_right

@[ematch]
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
  le_antisymm_iff.trans $ by simp [le_rfl]
#align inf_eq_left inf_eq_left

@[simp]
theorem inf_eq_right : a ⊓ b = b ↔ b ≤ a :=
  le_antisymm_iff.trans $ by simp [le_rfl]
#align inf_eq_right inf_eq_right

@[simp]
theorem left_eq_inf : a = a ⊓ b ↔ a ≤ b :=
  eq_comm.trans inf_eq_left
#align left_eq_inf left_eq_inf

@[simp]
theorem right_eq_inf : b = a ⊓ b ↔ b ≤ a :=
  eq_comm.trans inf_eq_right
#align right_eq_inf right_eq_inf

alias inf_eq_left ↔ le_of_inf_eq inf_of_le_left

alias inf_eq_right ↔ _ inf_of_le_right

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

theorem inf_le_inf (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊓ c ≤ b ⊓ d :=
  @sup_le_sup αᵒᵈ _ _ _ _ _ h₁ h₂
#align inf_le_inf inf_le_inf

theorem inf_le_inf_right (a : α) {b c : α} (h : b ≤ c) : b ⊓ a ≤ c ⊓ a :=
  inf_le_inf h le_rfl
#align inf_le_inf_right inf_le_inf_right

theorem inf_le_inf_left (a : α) {b c : α} (h : b ≤ c) : a ⊓ b ≤ a ⊓ c :=
  inf_le_inf le_rfl h
#align inf_le_inf_left inf_le_inf_left

@[simp]
theorem inf_idem : a ⊓ a = a :=
  @sup_idem αᵒᵈ _ _
#align inf_idem inf_idem

instance inf_is_idempotent : IsIdempotent α (· ⊓ ·) :=
  ⟨@inf_idem _ _⟩
#align inf_is_idempotent inf_is_idempotent

theorem inf_comm : a ⊓ b = b ⊓ a :=
  @sup_comm αᵒᵈ _ _ _
#align inf_comm inf_comm

instance inf_is_commutative : IsCommutative α (· ⊓ ·) :=
  ⟨@inf_comm _ _⟩
#align inf_is_commutative inf_is_commutative

theorem inf_assoc : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) :=
  @sup_assoc αᵒᵈ _ a b c
#align inf_assoc inf_assoc

instance inf_is_associative : IsAssociative α (· ⊓ ·) :=
  ⟨@inf_assoc _ _⟩
#align inf_is_associative inf_is_associative

theorem inf_left_right_swap (a b c : α) : a ⊓ b ⊓ c = c ⊓ b ⊓ a :=
  @sup_left_right_swap αᵒᵈ _ _ _ _
#align inf_left_right_swap inf_left_right_swap

@[simp]
theorem inf_left_idem : a ⊓ (a ⊓ b) = a ⊓ b :=
  @sup_left_idem αᵒᵈ _ a b
#align inf_left_idem inf_left_idem

@[simp]
theorem inf_right_idem : a ⊓ b ⊓ b = a ⊓ b :=
  @sup_right_idem αᵒᵈ _ a b
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
    (H :
      ∀ x y : α,
        (haveI := A
          x ≤ y) ↔
          x ≤ y)
    (x y : α) :
    (haveI := A
      x ⊓ y) =
      x ⊓ y :=
  eq_of_forall_le_iff $ fun c => by simp only [le_inf_iff] <;> rw [← H, @le_inf_iff α A, H, H]
#align semilattice_inf.ext_inf SemilatticeInf.ext_inf

theorem SemilatticeInf.ext {α} {A B : SemilatticeInf α}
    (H :
      ∀ x y : α,
        (haveI := A
          x ≤ y) ↔
          x ≤ y) :
    A = B := by
  have := PartialOrder.ext H
  have ss := funext fun x => funext $ SemilatticeInf.ext_inf H x
  cases A
  cases B
  injection this <;> congr
#align semilattice_inf.ext SemilatticeInf.ext

theorem SemilatticeInf.dual_dual (α : Type _) [H : SemilatticeInf α] : OrderDual.semilatticeInf αᵒᵈ = H :=
  SemilatticeInf.ext $ fun _ _ => Iff.rfl
#align semilattice_inf.dual_dual SemilatticeInf.dual_dual

theorem inf_le_ite (s s' : α) (P : Prop) [Decidable P] : s ⊓ s' ≤ ite P s s' :=
  @ite_le_sup αᵒᵈ _ _ _ _ _
#align inf_le_ite inf_le_ite

end SemilatticeInf

/-- A type with a commutative, associative and idempotent binary `inf` operation has the structure of a
meet-semilattice.

The partial order is defined so that `a ≤ b` unfolds to `b ⊓ a = a`; cf. `inf_eq_right`.
-/
def SemilatticeInf.mk' {α : Type _} [HasInf α] (inf_comm : ∀ a b : α, a ⊓ b = b ⊓ a)
    (inf_assoc : ∀ a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (inf_idem : ∀ a : α, a ⊓ a = a) : SemilatticeInf α := by
  haveI : SemilatticeSup αᵒᵈ := SemilatticeSup.mk' inf_comm inf_assoc inf_idem
  haveI i := OrderDual.semilatticeInf αᵒᵈ
  exact i
#align semilattice_inf.mk' SemilatticeInf.mk'

/-!
### Lattices
-/


/-- A lattice is a join-semilattice which is also a meet-semilattice. -/
@[protect_proj]
class Lattice (α : Type u) extends SemilatticeSup α, SemilatticeInf α
#align lattice Lattice

instance (α) [Lattice α] : Lattice αᵒᵈ :=
  { OrderDual.semilatticeSup α, OrderDual.semilatticeInf α with }

/-- The partial orders from `semilattice_sup_mk'` and `semilattice_inf_mk'` agree
if `sup` and `inf` satisfy the lattice absorption laws `sup_inf_self` (`a ⊔ a ⊓ b = a`)
and `inf_sup_self` (`a ⊓ (a ⊔ b) = a`). -/
theorem semilattice_sup_mk'_partial_order_eq_semilattice_inf_mk'_partial_order {α : Type _} [HasSup α] [HasInf α]
    (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a) (sup_assoc : ∀ a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c))
    (sup_idem : ∀ a : α, a ⊔ a = a) (inf_comm : ∀ a b : α, a ⊓ b = b ⊓ a)
    (inf_assoc : ∀ a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (inf_idem : ∀ a : α, a ⊓ a = a)
    (sup_inf_self : ∀ a b : α, a ⊔ a ⊓ b = a) (inf_sup_self : ∀ a b : α, a ⊓ (a ⊔ b) = a) :
    @SemilatticeSup.toPartialOrder _ (SemilatticeSup.mk' sup_comm sup_assoc sup_idem) =
      @SemilatticeInf.toPartialOrder _ (SemilatticeInf.mk' inf_comm inf_assoc inf_idem) :=
  PartialOrder.ext $ fun a b =>
    show a ⊔ b = b ↔ b ⊓ a = a from
      ⟨fun h => by rw [← h, inf_comm, inf_sup_self], fun h => by rw [← h, sup_comm, sup_inf_self]⟩
#align
  semilattice_sup_mk'_partial_order_eq_semilattice_inf_mk'_partial_order semilattice_sup_mk'_partial_order_eq_semilattice_inf_mk'_partial_order

/-- A type with a pair of commutative and associative binary operations which satisfy two absorption
laws relating the two operations has the structure of a lattice.

The partial order is defined so that `a ≤ b` unfolds to `a ⊔ b = b`; cf. `sup_eq_right`.
-/
def Lattice.mk' {α : Type _} [HasSup α] [HasInf α] (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a)
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
  let
    partial_order_inst :=-- here we help Lean to see that the two partial orders are equal
      @SemilatticeSup.toPartialOrder
      _ semilatt_sup_inst
  have partial_order_eq : partial_order_inst = @SemilatticeInf.toPartialOrder _ semilatt_inf_inst :=
    semilattice_sup_mk'_partial_order_eq_semilattice_inf_mk'_partial_order _ _ _ _ _ _ sup_inf_self inf_sup_self
  { partial_order_inst, semilatt_sup_inst, semilatt_inf_inst with
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

@[simp]
theorem inf_lt_sup : a ⊓ b < a ⊔ b ↔ a ≠ b := by
  constructor
  · rintro H rfl
    simpa using H
    
  · refine' fun Hne => lt_iff_le_and_ne.2 ⟨inf_le_sup, fun Heq => Hne _⟩
    refine' le_antisymm _ _
    exacts[le_sup_left.trans (Heq.symm.trans_le inf_le_right), le_sup_right.trans (Heq.symm.trans_le inf_le_left)]
    
#align inf_lt_sup inf_lt_sup

@[simp]
theorem sup_le_inf : a ⊔ b ≤ a ⊓ b ↔ a = b :=
  ⟨fun h => le_antisymm (le_sup_left.trans $ h.trans inf_le_right) (le_sup_right.trans $ h.trans inf_le_left), by
    rintro rfl
    simp⟩
#align sup_le_inf sup_le_inf

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

theorem Lattice.ext {α} {A B : Lattice α}
    (H :
      ∀ x y : α,
        (haveI := A
          x ≤ y) ↔
          x ≤ y) :
    A = B := by
  have SS : @Lattice.toSemilatticeSup α A = @Lattice.toSemilatticeSup α B := SemilatticeSup.ext H
  have II := SemilatticeInf.ext H
  cases A
  cases B
  injection SS <;> injection II <;> congr
#align lattice.ext Lattice.ext

end Lattice

/-!
### Distributive lattices
-/


/-- A distributive lattice is a lattice that satisfies any of four
equivalent distributive properties (of `sup` over `inf` or `inf` over `sup`,
on the left or right).

The definition here chooses `le_sup_inf`: `(x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z)`. To prove distributivity
from the dual law, use `distrib_lattice.of_inf_sup_le`.

A classic example of a distributive lattice
is the lattice of subsets of a set, and in fact this example is
generic in the sense that every distributive lattice is realizable
as a sublattice of a powerset lattice. -/
@[protect_proj]
class DistribLattice (α) extends Lattice α where
  le_sup_inf : ∀ x y z : α, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z
#align distrib_lattice DistribLattice

section DistribLattice

variable [DistribLattice α] {x y z : α}

theorem le_sup_inf : ∀ {x y z : α}, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z :=
  DistribLattice.le_sup_inf
#align le_sup_inf le_sup_inf

theorem sup_inf_left : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z) :=
  le_antisymm sup_inf_le le_sup_inf
#align sup_inf_left sup_inf_left

theorem sup_inf_right : y ⊓ z ⊔ x = (y ⊔ x) ⊓ (z ⊔ x) := by
  simp only [sup_inf_left, fun y : α => @sup_comm α _ y x, eq_self_iff_true]
#align sup_inf_right sup_inf_right

theorem inf_sup_left : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z :=
  calc
    x ⊓ (y ⊔ z) = x ⊓ (x ⊔ z) ⊓ (y ⊔ z) := by rw [inf_sup_self]
    _ = x ⊓ (x ⊓ y ⊔ z) := by simp only [inf_assoc, sup_inf_right, eq_self_iff_true]
    _ = (x ⊔ x ⊓ y) ⊓ (x ⊓ y ⊔ z) := by rw [sup_inf_self]
    _ = (x ⊓ y ⊔ x) ⊓ (x ⊓ y ⊔ z) := by rw [sup_comm]
    _ = x ⊓ y ⊔ x ⊓ z := by rw [sup_inf_left]
    
#align inf_sup_left inf_sup_left

instance (α : Type _) [DistribLattice α] : DistribLattice αᵒᵈ :=
  { OrderDual.lattice α with le_sup_inf := fun x y z => le_of_eq inf_sup_left.symm }

theorem inf_sup_right : (y ⊔ z) ⊓ x = y ⊓ x ⊔ z ⊓ x := by
  simp only [inf_sup_left, fun y : α => @inf_comm α _ y x, eq_self_iff_true]
#align inf_sup_right inf_sup_right

theorem le_of_inf_le_sup_le (h₁ : x ⊓ z ≤ y ⊓ z) (h₂ : x ⊔ z ≤ y ⊔ z) : x ≤ y :=
  calc
    x ≤ y ⊓ z ⊔ x := le_sup_right
    _ = (y ⊔ x) ⊓ (x ⊔ z) := by rw [sup_inf_right, @sup_comm _ _ x]
    _ ≤ (y ⊔ x) ⊓ (y ⊔ z) := inf_le_inf_left _ h₂
    _ = y ⊔ x ⊓ z := sup_inf_left.symm
    _ ≤ y ⊔ y ⊓ z := sup_le_sup_left h₁ _
    _ ≤ _ := sup_le (le_refl y) inf_le_left
    
#align le_of_inf_le_sup_le le_of_inf_le_sup_le

theorem eq_of_inf_eq_sup_eq {α : Type u} [DistribLattice α] {a b c : α} (h₁ : b ⊓ a = c ⊓ a) (h₂ : b ⊔ a = c ⊔ a) :
    b = c :=
  le_antisymm (le_of_inf_le_sup_le (le_of_eq h₁) (le_of_eq h₂))
    (le_of_inf_le_sup_le (le_of_eq h₁.symm) (le_of_eq h₂.symm))
#align eq_of_inf_eq_sup_eq eq_of_inf_eq_sup_eq

end DistribLattice

-- See note [reducible non-instances]
/-- Prove distributivity of an existing lattice from the dual distributive law. -/
@[reducible]
def DistribLattice.ofInfSupLe [Lattice α] (inf_sup_le : ∀ a b c : α, a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c) : DistribLattice α :=
  { ‹Lattice α›, @OrderDual.distribLattice αᵒᵈ { OrderDual.lattice _ with le_sup_inf := inf_sup_le } with }
#align distrib_lattice.of_inf_sup_le DistribLattice.ofInfSupLe

/-!
### Lattices derived from linear orders
-/


-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.toLattice {α : Type u} [o : LinearOrder α] : Lattice α :=
  { o with sup := max, le_sup_left := le_max_left, le_sup_right := le_max_right, sup_le := fun a b c => max_le,
    inf := min, inf_le_left := min_le_left, inf_le_right := min_le_right, le_inf := fun a b c => le_min }
#align linear_order.to_lattice LinearOrder.toLattice

section LinearOrder

variable [LinearOrder α] {a b c d : α}

theorem sup_eq_max : a ⊔ b = max a b :=
  rfl
#align sup_eq_max sup_eq_max

theorem inf_eq_min : a ⊓ b = min a b :=
  rfl
#align inf_eq_min inf_eq_min

theorem sup_ind (a b : α) {p : α → Prop} (ha : p a) (hb : p b) : p (a ⊔ b) :=
  (IsTotal.total a b).elim (fun h : a ≤ b => by rwa [sup_eq_right.2 h]) fun h => by rwa [sup_eq_left.2 h]
#align sup_ind sup_ind

@[simp]
theorem le_sup_iff : a ≤ b ⊔ c ↔ a ≤ b ∨ a ≤ c :=
  ⟨fun h =>
    (total_of (· ≤ ·) c b).imp (fun bc => by rwa [sup_eq_left.2 bc] at h) fun bc => by rwa [sup_eq_right.2 bc] at h,
    fun h => h.elim le_sup_of_le_left le_sup_of_le_right⟩
#align le_sup_iff le_sup_iff

@[simp]
theorem lt_sup_iff : a < b ⊔ c ↔ a < b ∨ a < c :=
  ⟨fun h =>
    (total_of (· ≤ ·) c b).imp (fun bc => by rwa [sup_eq_left.2 bc] at h) fun bc => by rwa [sup_eq_right.2 bc] at h,
    fun h => h.elim lt_sup_of_lt_left lt_sup_of_lt_right⟩
#align lt_sup_iff lt_sup_iff

@[simp]
theorem sup_lt_iff : b ⊔ c < a ↔ b < a ∧ c < a :=
  ⟨fun h => ⟨le_sup_left.trans_lt h, le_sup_right.trans_lt h⟩, fun h => sup_ind b c h.1 h.2⟩
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

theorem sup_eq_max_default [SemilatticeSup α] [DecidableRel ((· ≤ ·) : α → α → Prop)] [IsTotal α (· ≤ ·)] :
    (· ⊔ ·) = (maxDefault : α → α → α) := by
  ext (x y)
  dsimp only [maxDefault]
  split_ifs with h'
  exacts[sup_of_le_right h', sup_of_le_left $ (total_of (· ≤ ·) x y).resolve_left h']
#align sup_eq_max_default sup_eq_max_default

theorem inf_eq_min_default [SemilatticeInf α] [DecidableRel ((· ≤ ·) : α → α → Prop)] [IsTotal α (· ≤ ·)] :
    (· ⊓ ·) = (minDefault : α → α → α) := by
  ext (x y)
  dsimp only [minDefault]
  split_ifs with h'
  exacts[inf_of_le_left h', inf_of_le_right $ (total_of (· ≤ ·) x y).resolve_left h']
#align inf_eq_min_default inf_eq_min_default

/-- A lattice with total order is a linear order.

See note [reducible non-instances]. -/
@[reducible]
def Lattice.toLinearOrder (α : Type u) [Lattice α] [DecidableEq α] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    [DecidableRel ((· < ·) : α → α → Prop)] [IsTotal α (· ≤ ·)] : LinearOrder α :=
  { ‹Lattice α› with decidableLe := ‹_›, DecidableEq := ‹_›, decidableLt := ‹_›, le_total := total_of (· ≤ ·),
    max := (· ⊔ ·), max_def := sup_eq_max_default, min := (· ⊓ ·), min_def := inf_eq_min_default }
#align lattice.to_linear_order Lattice.toLinearOrder

-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.toDistribLattice {α : Type u} [o : LinearOrder α] : DistribLattice α :=
  { LinearOrder.toLattice with
    le_sup_inf := fun a b c =>
      match le_total b c with
      | Or.inl h => inf_le_of_left_le $ sup_le_sup_left (le_inf (le_refl b) h) _
      | Or.inr h => inf_le_of_right_le $ sup_le_sup_left (le_inf h (le_refl c)) _ }
#align linear_order.to_distrib_lattice LinearOrder.toDistribLattice

instance Nat.distribLattice : DistribLattice ℕ := by infer_instance
#align nat.distrib_lattice Nat.distribLattice

/-! ### Dual order -/


open OrderDual

@[simp]
theorem of_dual_inf [HasSup α] (a b : αᵒᵈ) : ofDual (a ⊓ b) = ofDual a ⊔ ofDual b :=
  rfl
#align of_dual_inf of_dual_inf

@[simp]
theorem of_dual_sup [HasInf α] (a b : αᵒᵈ) : ofDual (a ⊔ b) = ofDual a ⊓ ofDual b :=
  rfl
#align of_dual_sup of_dual_sup

@[simp]
theorem to_dual_inf [HasInf α] (a b : α) : toDual (a ⊓ b) = toDual a ⊔ toDual b :=
  rfl
#align to_dual_inf to_dual_inf

@[simp]
theorem to_dual_sup [HasSup α] (a b : α) : toDual (a ⊔ b) = toDual a ⊓ toDual b :=
  rfl
#align to_dual_sup to_dual_sup

section LinearOrder

variable [LinearOrder α]

@[simp]
theorem of_dual_min (a b : αᵒᵈ) : ofDual (min a b) = max (ofDual a) (ofDual b) :=
  rfl
#align of_dual_min of_dual_min

@[simp]
theorem of_dual_max (a b : αᵒᵈ) : ofDual (max a b) = min (ofDual a) (ofDual b) :=
  rfl
#align of_dual_max of_dual_max

@[simp]
theorem to_dual_min (a b : α) : toDual (min a b) = max (toDual a) (toDual b) :=
  rfl
#align to_dual_min to_dual_min

@[simp]
theorem to_dual_max (a b : α) : toDual (max a b) = min (toDual a) (toDual b) :=
  rfl
#align to_dual_max to_dual_max

end LinearOrder

/-! ### Function lattices -/


namespace Pi

variable {ι : Type _} {α' : ι → Type _}

instance [∀ i, HasSup (α' i)] : HasSup (∀ i, α' i) :=
  ⟨fun f g i => f i ⊔ g i⟩

@[simp]
theorem sup_apply [∀ i, HasSup (α' i)] (f g : ∀ i, α' i) (i : ι) : (f ⊔ g) i = f i ⊔ g i :=
  rfl
#align pi.sup_apply Pi.sup_apply

theorem sup_def [∀ i, HasSup (α' i)] (f g : ∀ i, α' i) : f ⊔ g = fun i => f i ⊔ g i :=
  rfl
#align pi.sup_def Pi.sup_def

instance [∀ i, HasInf (α' i)] : HasInf (∀ i, α' i) :=
  ⟨fun f g i => f i ⊓ g i⟩

@[simp]
theorem inf_apply [∀ i, HasInf (α' i)] (f g : ∀ i, α' i) (i : ι) : (f ⊓ g) i = f i ⊓ g i :=
  rfl
#align pi.inf_apply Pi.inf_apply

theorem inf_def [∀ i, HasInf (α' i)] (f g : ∀ i, α' i) : f ⊓ g = fun i => f i ⊓ g i :=
  rfl
#align pi.inf_def Pi.inf_def

instance [∀ i, SemilatticeSup (α' i)] : SemilatticeSup (∀ i, α' i) := by
  refine_struct { Pi.partialOrder with sup := (· ⊔ ·) } <;> pi_instance_derive_field

instance [∀ i, SemilatticeInf (α' i)] : SemilatticeInf (∀ i, α' i) := by
  refine_struct { Pi.partialOrder with inf := (· ⊓ ·) } <;> pi_instance_derive_field

instance [∀ i, Lattice (α' i)] : Lattice (∀ i, α' i) :=
  { Pi.semilatticeSup, Pi.semilatticeInf with }

instance [∀ i, DistribLattice (α' i)] : DistribLattice (∀ i, α' i) := by
  refine_struct { Pi.lattice with } <;> pi_instance_derive_field

end Pi

/-!
### Monotone functions and lattices
-/


namespace Monotone

/-- Pointwise supremum of two monotone functions is a monotone function. -/
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α → β} (hf : Monotone f) (hg : Monotone g) :
    Monotone (f ⊔ g) := fun x y h => sup_le_sup (hf h) (hg h)
#align monotone.sup Monotone.sup

/-- Pointwise infimum of two monotone functions is a monotone function. -/
protected theorem inf [Preorder α] [SemilatticeInf β] {f g : α → β} (hf : Monotone f) (hg : Monotone g) :
    Monotone (f ⊓ g) := fun x y h => inf_le_inf (hf h) (hg h)
#align monotone.inf Monotone.inf

/-- Pointwise maximum of two monotone functions is a monotone function. -/
protected theorem max [Preorder α] [LinearOrder β] {f g : α → β} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => max (f x) (g x) :=
  hf.sup hg
#align monotone.max Monotone.max

/-- Pointwise minimum of two monotone functions is a monotone function. -/
protected theorem min [Preorder α] [LinearOrder β] {f g : α → β} (hf : Monotone f) (hg : Monotone g) :
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

theorem of_map_inf [SemilatticeInf α] [SemilatticeInf β] {f : α → β} (h : ∀ x y, f (x ⊓ y) = f x ⊓ f y) : Monotone f :=
  fun x y hxy => inf_eq_left.1 $ by rw [← h, inf_eq_left.2 hxy]
#align monotone.of_map_inf Monotone.of_map_inf

theorem of_map_sup [SemilatticeSup α] [SemilatticeSup β] {f : α → β} (h : ∀ x y, f (x ⊔ y) = f x ⊔ f y) : Monotone f :=
  (@of_map_inf (OrderDual α) (OrderDual β) _ _ _ h).dual
#align monotone.of_map_sup Monotone.of_map_sup

variable [LinearOrder α]

theorem map_sup [SemilatticeSup β] {f : α → β} (hf : Monotone f) (x y : α) : f (x ⊔ y) = f x ⊔ f y :=
  (IsTotal.total x y).elim (fun h : x ≤ y => by simp only [h, hf h, sup_of_le_right]) fun h => by
    simp only [h, hf h, sup_of_le_left]
#align monotone.map_sup Monotone.map_sup

theorem map_inf [SemilatticeInf β] {f : α → β} (hf : Monotone f) (x y : α) : f (x ⊓ y) = f x ⊓ f y :=
  hf.dual.map_sup _ _
#align monotone.map_inf Monotone.map_inf

end Monotone

namespace MonotoneOn

/-- Pointwise supremum of two monotone functions is a monotone function. -/
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α → β} {s : Set α} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (f ⊔ g) s := fun x hx y hy h => sup_le_sup (hf hx hy h) (hg hx hy h)
#align monotone_on.sup MonotoneOn.sup

/-- Pointwise infimum of two monotone functions is a monotone function. -/
protected theorem inf [Preorder α] [SemilatticeInf β] {f g : α → β} {s : Set α} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (f ⊓ g) s :=
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

end MonotoneOn

namespace Antitone

/-- Pointwise supremum of two monotone functions is a monotone function. -/
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α → β} (hf : Antitone f) (hg : Antitone g) :
    Antitone (f ⊔ g) := fun x y h => sup_le_sup (hf h) (hg h)
#align antitone.sup Antitone.sup

/-- Pointwise infimum of two monotone functions is a monotone function. -/
protected theorem inf [Preorder α] [SemilatticeInf β] {f g : α → β} (hf : Antitone f) (hg : Antitone g) :
    Antitone (f ⊓ g) := fun x y h => inf_le_inf (hf h) (hg h)
#align antitone.inf Antitone.inf

/-- Pointwise maximum of two monotone functions is a monotone function. -/
protected theorem max [Preorder α] [LinearOrder β] {f g : α → β} (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => max (f x) (g x) :=
  hf.sup hg
#align antitone.max Antitone.max

/-- Pointwise minimum of two monotone functions is a monotone function. -/
protected theorem min [Preorder α] [LinearOrder β] {f g : α → β} (hf : Antitone f) (hg : Antitone g) :
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

theorem map_sup [SemilatticeInf β] {f : α → β} (hf : Antitone f) (x y : α) : f (x ⊔ y) = f x ⊓ f y :=
  hf.dual_right.map_sup x y
#align antitone.map_sup Antitone.map_sup

theorem map_inf [SemilatticeSup β] {f : α → β} (hf : Antitone f) (x y : α) : f (x ⊓ y) = f x ⊔ f y :=
  hf.dual_right.map_inf x y
#align antitone.map_inf Antitone.map_inf

end Antitone

namespace AntitoneOn

/-- Pointwise supremum of two antitone functions is a antitone function. -/
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α → β} {s : Set α} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (f ⊔ g) s := fun x hx y hy h => sup_le_sup (hf hx hy h) (hg hx hy h)
#align antitone_on.sup AntitoneOn.sup

/-- Pointwise infimum of two antitone functions is a antitone function. -/
protected theorem inf [Preorder α] [SemilatticeInf β] {f g : α → β} {s : Set α} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (f ⊓ g) s :=
  (hf.dual.sup hg.dual).dual
#align antitone_on.inf AntitoneOn.inf

/-- Pointwise maximum of two antitone functions is a antitone function. -/
protected theorem max [Preorder α] [LinearOrder β] {f g : α → β} {s : Set α} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => max (f x) (g x)) s :=
  hf.sup hg
#align antitone_on.max AntitoneOn.max

/-- Pointwise minimum of two antitone functions is a antitone function. -/
protected theorem min [Preorder α] [LinearOrder β] {f g : α → β} {s : Set α} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => min (f x) (g x)) s :=
  hf.inf hg
#align antitone_on.min AntitoneOn.min

end AntitoneOn

/-!
### Products of (semi-)lattices
-/


namespace Prod

variable (α β)

instance [HasSup α] [HasSup β] : HasSup (α × β) :=
  ⟨fun p q => ⟨p.1 ⊔ q.1, p.2 ⊔ q.2⟩⟩

instance [HasInf α] [HasInf β] : HasInf (α × β) :=
  ⟨fun p q => ⟨p.1 ⊓ q.1, p.2 ⊓ q.2⟩⟩

@[simp]
theorem mk_sup_mk [HasSup α] [HasSup β] (a₁ a₂ : α) (b₁ b₂ : β) : (a₁, b₁) ⊔ (a₂, b₂) = (a₁ ⊔ a₂, b₁ ⊔ b₂) :=
  rfl
#align prod.mk_sup_mk Prod.mk_sup_mk

@[simp]
theorem mk_inf_mk [HasInf α] [HasInf β] (a₁ a₂ : α) (b₁ b₂ : β) : (a₁, b₁) ⊓ (a₂, b₂) = (a₁ ⊓ a₂, b₁ ⊓ b₂) :=
  rfl
#align prod.mk_inf_mk Prod.mk_inf_mk

@[simp]
theorem fst_sup [HasSup α] [HasSup β] (p q : α × β) : (p ⊔ q).fst = p.fst ⊔ q.fst :=
  rfl
#align prod.fst_sup Prod.fst_sup

@[simp]
theorem fst_inf [HasInf α] [HasInf β] (p q : α × β) : (p ⊓ q).fst = p.fst ⊓ q.fst :=
  rfl
#align prod.fst_inf Prod.fst_inf

@[simp]
theorem snd_sup [HasSup α] [HasSup β] (p q : α × β) : (p ⊔ q).snd = p.snd ⊔ q.snd :=
  rfl
#align prod.snd_sup Prod.snd_sup

@[simp]
theorem snd_inf [HasInf α] [HasInf β] (p q : α × β) : (p ⊓ q).snd = p.snd ⊓ q.snd :=
  rfl
#align prod.snd_inf Prod.snd_inf

@[simp]
theorem swap_sup [HasSup α] [HasSup β] (p q : α × β) : (p ⊔ q).swap = p.swap ⊔ q.swap :=
  rfl
#align prod.swap_sup Prod.swap_sup

@[simp]
theorem swap_inf [HasInf α] [HasInf β] (p q : α × β) : (p ⊓ q).swap = p.swap ⊓ q.swap :=
  rfl
#align prod.swap_inf Prod.swap_inf

theorem sup_def [HasSup α] [HasSup β] (p q : α × β) : p ⊔ q = (p.fst ⊔ q.fst, p.snd ⊔ q.snd) :=
  rfl
#align prod.sup_def Prod.sup_def

theorem inf_def [HasInf α] [HasInf β] (p q : α × β) : p ⊓ q = (p.fst ⊓ q.fst, p.snd ⊓ q.snd) :=
  rfl
#align prod.inf_def Prod.inf_def

instance [SemilatticeSup α] [SemilatticeSup β] : SemilatticeSup (α × β) :=
  { Prod.partialOrder α β, Prod.hasSup α β with sup_le := fun a b c h₁ h₂ => ⟨sup_le h₁.1 h₂.1, sup_le h₁.2 h₂.2⟩,
    le_sup_left := fun a b => ⟨le_sup_left, le_sup_left⟩, le_sup_right := fun a b => ⟨le_sup_right, le_sup_right⟩ }

instance [SemilatticeInf α] [SemilatticeInf β] : SemilatticeInf (α × β) :=
  { Prod.partialOrder α β, Prod.hasInf α β with le_inf := fun a b c h₁ h₂ => ⟨le_inf h₁.1 h₂.1, le_inf h₁.2 h₂.2⟩,
    inf_le_left := fun a b => ⟨inf_le_left, inf_le_left⟩, inf_le_right := fun a b => ⟨inf_le_right, inf_le_right⟩ }

instance [Lattice α] [Lattice β] : Lattice (α × β) :=
  { Prod.semilatticeInf α β, Prod.semilatticeSup α β with }

instance [DistribLattice α] [DistribLattice β] : DistribLattice (α × β) :=
  { Prod.lattice α β with le_sup_inf := fun a b c => ⟨le_sup_inf, le_sup_inf⟩ }

end Prod

/-!
### Subtypes of (semi-)lattices
-/


namespace Subtype

/-- A subtype forms a `⊔`-semilattice if `⊔` preserves the property.
See note [reducible non-instances]. -/
@[reducible]
protected def semilatticeSup [SemilatticeSup α] {P : α → Prop} (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) :
    SemilatticeSup { x : α // P x } :=
  { Subtype.partialOrder P with sup := fun x y => ⟨x.1 ⊔ y.1, Psup x.2 y.2⟩,
    le_sup_left := fun x y => @le_sup_left _ _ (x : α) y, le_sup_right := fun x y => @le_sup_right _ _ (x : α) y,
    sup_le := fun x y z h1 h2 => @sup_le α _ _ _ _ h1 h2 }
#align subtype.semilattice_sup Subtype.semilatticeSup

/-- A subtype forms a `⊓`-semilattice if `⊓` preserves the property.
See note [reducible non-instances]. -/
@[reducible]
protected def semilatticeInf [SemilatticeInf α] {P : α → Prop} (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) :
    SemilatticeInf { x : α // P x } :=
  { Subtype.partialOrder P with inf := fun x y => ⟨x.1 ⊓ y.1, Pinf x.2 y.2⟩,
    inf_le_left := fun x y => @inf_le_left _ _ (x : α) y, inf_le_right := fun x y => @inf_le_right _ _ (x : α) y,
    le_inf := fun x y z h1 h2 => @le_inf α _ _ _ _ h1 h2 }
#align subtype.semilattice_inf Subtype.semilatticeInf

/-- A subtype forms a lattice if `⊔` and `⊓` preserve the property.
See note [reducible non-instances]. -/
@[reducible]
protected def lattice [Lattice α] {P : α → Prop} (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y))
    (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) : Lattice { x : α // P x } :=
  { Subtype.semilatticeInf Pinf, Subtype.semilatticeSup Psup with }
#align subtype.lattice Subtype.lattice

@[simp, norm_cast]
theorem coe_sup [SemilatticeSup α] {P : α → Prop} (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) (x y : Subtype P) :
    (haveI := Subtype.semilatticeSup Psup
        (x ⊔ y : Subtype P) :
        α) =
      x ⊔ y :=
  rfl
#align subtype.coe_sup Subtype.coe_sup

@[simp, norm_cast]
theorem coe_inf [SemilatticeInf α] {P : α → Prop} (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) (x y : Subtype P) :
    (haveI := Subtype.semilatticeInf Pinf
        (x ⊓ y : Subtype P) :
        α) =
      x ⊓ y :=
  rfl
#align subtype.coe_inf Subtype.coe_inf

@[simp]
theorem mk_sup_mk [SemilatticeSup α] {P : α → Prop} (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) {x y : α} (hx : P x)
    (hy : P y) :
    (haveI := Subtype.semilatticeSup Psup
      (⟨x, hx⟩ ⊔ ⟨y, hy⟩ : Subtype P)) =
      ⟨x ⊔ y, Psup hx hy⟩ :=
  rfl
#align subtype.mk_sup_mk Subtype.mk_sup_mk

@[simp]
theorem mk_inf_mk [SemilatticeInf α] {P : α → Prop} (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) {x y : α} (hx : P x)
    (hy : P y) :
    (haveI := Subtype.semilatticeInf Pinf
      (⟨x, hx⟩ ⊓ ⟨y, hy⟩ : Subtype P)) =
      ⟨x ⊓ y, Pinf hx hy⟩ :=
  rfl
#align subtype.mk_inf_mk Subtype.mk_inf_mk

end Subtype

section lift

/-- A type endowed with `⊔` is a `semilattice_sup`, if it admits an injective map that
preserves `⊔` to a `semilattice_sup`.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.semilatticeSup [HasSup α] [SemilatticeSup β] (f : α → β)
    (hf_inj : Function.Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) : SemilatticeSup α :=
  { PartialOrder.lift f hf_inj with sup := HasSup.sup,
    le_sup_left := fun a b => by
      change f a ≤ f (a ⊔ b)
      rw [map_sup]
      exact le_sup_left,
    le_sup_right := fun a b => by
      change f b ≤ f (a ⊔ b)
      rw [map_sup]
      exact le_sup_right,
    sup_le := fun a b c ha hb => by
      change f (a ⊔ b) ≤ f c
      rw [map_sup]
      exact sup_le ha hb }
#align function.injective.semilattice_sup Function.Injective.semilatticeSup

/-- A type endowed with `⊓` is a `semilattice_inf`, if it admits an injective map that
preserves `⊓` to a `semilattice_inf`.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.semilatticeInf [HasInf α] [SemilatticeInf β] (f : α → β)
    (hf_inj : Function.Injective f) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) : SemilatticeInf α :=
  { PartialOrder.lift f hf_inj with inf := HasInf.inf,
    inf_le_left := fun a b => by
      change f (a ⊓ b) ≤ f a
      rw [map_inf]
      exact inf_le_left,
    inf_le_right := fun a b => by
      change f (a ⊓ b) ≤ f b
      rw [map_inf]
      exact inf_le_right,
    le_inf := fun a b c ha hb => by
      change f a ≤ f (b ⊓ c)
      rw [map_inf]
      exact le_inf ha hb }
#align function.injective.semilattice_inf Function.Injective.semilatticeInf

/-- A type endowed with `⊔` and `⊓` is a `lattice`, if it admits an injective map that
preserves `⊔` and `⊓` to a `lattice`.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.lattice [HasSup α] [HasInf α] [Lattice β] (f : α → β) (hf_inj : Function.Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) : Lattice α :=
  { hf_inj.SemilatticeSup f map_sup, hf_inj.SemilatticeInf f map_inf with }
#align function.injective.lattice Function.Injective.lattice

/-- A type endowed with `⊔` and `⊓` is a `distrib_lattice`, if it admits an injective map that
preserves `⊔` and `⊓` to a `distrib_lattice`.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.distribLattice [HasSup α] [HasInf α] [DistribLattice β] (f : α → β)
    (hf_inj : Function.Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) :
    DistribLattice α :=
  { hf_inj.Lattice f map_sup map_inf with
    le_sup_inf := fun a b c => by
      change f ((a ⊔ b) ⊓ (a ⊔ c)) ≤ f (a ⊔ b ⊓ c)
      rw [map_inf, map_sup, map_sup, map_sup, map_inf]
      exact le_sup_inf }
#align function.injective.distrib_lattice Function.Injective.distribLattice

end lift

--To avoid noncomputability poisoning from `bool.complete_boolean_algebra`
instance : DistribLattice Bool :=
  LinearOrder.toDistribLattice

