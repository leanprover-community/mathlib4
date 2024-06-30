/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic.ApplyFun

#align_import data.sym.basic from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

/-!
# Symmetric powers

This file defines symmetric powers of a type.  The nth symmetric power
consists of homogeneous n-tuples modulo permutations by the symmetric
group.

The special case of 2-tuples is called the symmetric square, which is
addressed in more detail in `Data.Sym.Sym2`.

TODO: This was created as supporting material for `Sym2`; it
needs a fleshed-out interface.

## Tags

symmetric powers

-/

assert_not_exists MonoidWithZero

set_option autoImplicit true


open Function

/-- The nth symmetric power is n-tuples up to permutation.  We define it
as a subtype of `Multiset` since these are well developed in the
library.  We also give a definition `Sym.sym'` in terms of vectors, and we
show these are equivalent in `Sym.symEquivSym'`.
-/
def Sym (α : Type*) (n : ℕ) :=
  { s : Multiset α // Multiset.card s = n }
#align sym Sym

-- Porting note (#11445): new definition
/-- The canonical map to `Multiset α` that forgets that `s` has length `n` -/
@[coe] def Sym.toMultiset {α : Type*} {n : ℕ} (s : Sym α n) : Multiset α :=
  s.1

instance Sym.hasCoe (α : Type*) (n : ℕ) : CoeOut (Sym α n) (Multiset α) :=
  ⟨Sym.toMultiset⟩
#align sym.has_coe Sym.hasCoe

-- Porting note: instance needed for Data.Finset.Sym
instance [DecidableEq α] : DecidableEq (Sym α n) :=
  inferInstanceAs <| DecidableEq <| Subtype _

/-- This is the `List.Perm` setoid lifted to `Vector`.

See note [reducible non-instances].
-/
abbrev Vector.Perm.isSetoid (α : Type*) (n : ℕ) : Setoid (Vector α n) :=
  (List.isSetoid α).comap Subtype.val
#align vector.perm.is_setoid Vector.Perm.isSetoid

attribute [local instance] Vector.Perm.isSetoid

namespace Sym

variable {α β : Type*} {n n' m : ℕ} {s : Sym α n} {a b : α}

theorem coe_injective : Injective ((↑) : Sym α n → Multiset α) :=
  Subtype.coe_injective
#align sym.coe_injective Sym.coe_injective

@[simp, norm_cast]
theorem coe_inj {s₁ s₂ : Sym α n} : (s₁ : Multiset α) = s₂ ↔ s₁ = s₂ :=
  coe_injective.eq_iff
#align sym.coe_inj Sym.coe_inj

@[ext] theorem ext {s₁ s₂ : Sym α n} (h : (s₁ : Multiset α) = ↑s₂) : s₁ = s₂ :=
  coe_injective h

@[simp]
theorem val_eq_coe (s : Sym α n) : s.1 = ↑s :=
  rfl

/-- Construct an element of the `n`th symmetric power from a multiset of cardinality `n`.
-/
@[match_pattern] -- Porting note: removed `@[simps]`, generated bad lemma
abbrev mk (m : Multiset α) (h : Multiset.card m = n) : Sym α n :=
  ⟨m, h⟩
#align sym.mk Sym.mk

/-- The unique element in `Sym α 0`. -/
@[match_pattern]
def nil : Sym α 0 :=
  ⟨0, Multiset.card_zero⟩
#align sym.nil Sym.nil

@[simp]
theorem coe_nil : ↑(@Sym.nil α) = (0 : Multiset α) :=
  rfl
#align sym.coe_nil Sym.coe_nil

/-- Inserts an element into the term of `Sym α n`, increasing the length by one.
-/
@[match_pattern]
def cons (a : α) (s : Sym α n) : Sym α n.succ :=
  ⟨a ::ₘ s.1, by rw [Multiset.card_cons, s.2]⟩
#align sym.cons Sym.cons

@[inherit_doc]
infixr:67 " ::ₛ " => cons

@[simp]
theorem cons_inj_right (a : α) (s s' : Sym α n) : a ::ₛ s = a ::ₛ s' ↔ s = s' :=
  Subtype.ext_iff.trans <| (Multiset.cons_inj_right _).trans Subtype.ext_iff.symm
#align sym.cons_inj_right Sym.cons_inj_right

@[simp]
theorem cons_inj_left (a a' : α) (s : Sym α n) : a ::ₛ s = a' ::ₛ s ↔ a = a' :=
  Subtype.ext_iff.trans <| Multiset.cons_inj_left _
#align sym.cons_inj_left Sym.cons_inj_left

theorem cons_swap (a b : α) (s : Sym α n) : a ::ₛ b ::ₛ s = b ::ₛ a ::ₛ s :=
  Subtype.ext <| Multiset.cons_swap a b s.1
#align sym.cons_swap Sym.cons_swap

theorem coe_cons (s : Sym α n) (a : α) : (a ::ₛ s : Multiset α) = a ::ₘ s :=
  rfl
#align sym.coe_cons Sym.coe_cons

/-- This is the quotient map that takes a list of n elements as an n-tuple and produces an nth
symmetric power.
-/
def ofVector : Vector α n → Sym α n :=
  fun x => ⟨↑x.val, (Multiset.coe_card _).trans x.2⟩

/-- This is the quotient map that takes a list of n elements as an n-tuple and produces an nth
symmetric power.
-/
instance : Coe (Vector α n) (Sym α n) where coe x := ofVector x

@[simp]
theorem ofVector_nil : ↑(Vector.nil : Vector α 0) = (Sym.nil : Sym α 0) :=
  rfl
#align sym.of_vector_nil Sym.ofVector_nil

@[simp]
theorem ofVector_cons (a : α) (v : Vector α n) : ↑(Vector.cons a v) = a ::ₛ (↑v : Sym α n) := by
  cases v
  rfl
#align sym.of_vector_cons Sym.ofVector_cons

@[simp]
theorem card_coe : Multiset.card (s : Multiset α) = n := s.prop

/-- `α ∈ s` means that `a` appears as one of the factors in `s`.
-/
instance : Membership α (Sym α n) :=
  ⟨fun a s => a ∈ s.1⟩

instance decidableMem [DecidableEq α] (a : α) (s : Sym α n) : Decidable (a ∈ s) :=
  s.1.decidableMem _
#align sym.decidable_mem Sym.decidableMem

@[simp]
theorem mem_mk (a : α) (s : Multiset α) (h : Multiset.card s = n) : a ∈ mk s h ↔ a ∈ s :=
  Iff.rfl
#align sym.mem_mk Sym.mem_mk

@[simp]
theorem not_mem_nil (a : α) : ¬ a ∈ (nil : Sym α 0) :=
  Multiset.not_mem_zero a

@[simp]
theorem mem_cons : a ∈ b ::ₛ s ↔ a = b ∨ a ∈ s :=
  Multiset.mem_cons
#align sym.mem_cons Sym.mem_cons

@[simp]
theorem mem_coe : a ∈ (s : Multiset α) ↔ a ∈ s :=
  Iff.rfl
#align sym.mem_coe Sym.mem_coe

theorem mem_cons_of_mem (h : a ∈ s) : a ∈ b ::ₛ s :=
  Multiset.mem_cons_of_mem h
#align sym.mem_cons_of_mem Sym.mem_cons_of_mem

--@[simp] Porting note (#10618): simp can prove it
theorem mem_cons_self (a : α) (s : Sym α n) : a ∈ a ::ₛ s :=
  Multiset.mem_cons_self a s.1
#align sym.mem_cons_self Sym.mem_cons_self

theorem cons_of_coe_eq (a : α) (v : Vector α n) : a ::ₛ (↑v : Sym α n) = ↑(a ::ᵥ v) :=
  Subtype.ext <| by
    cases v
    rfl
#align sym.cons_of_coe_eq Sym.cons_of_coe_eq

open scoped List in
theorem sound {a b : Vector α n} (h : a.val ~ b.val) : (↑a : Sym α n) = ↑b :=
  Subtype.ext <| Quotient.sound h
#align sym.sound Sym.sound

/-- `erase s a h` is the sym that subtracts 1 from the
  multiplicity of `a` if a is present in the sym. -/
def erase [DecidableEq α] (s : Sym α (n + 1)) (a : α) (h : a ∈ s) : Sym α n :=
  ⟨s.val.erase a, (Multiset.card_erase_of_mem h).trans <| s.property.symm ▸ n.pred_succ⟩
#align sym.erase Sym.erase

@[simp]
theorem erase_mk [DecidableEq α] (m : Multiset α)
    (hc : Multiset.card m = n + 1) (a : α) (h : a ∈ m) :
    (mk m hc).erase a h =mk (m.erase a)
        (by rw [Multiset.card_erase_of_mem h, hc]; rfl) :=
  rfl
#align sym.erase_mk Sym.erase_mk

@[simp]
theorem coe_erase [DecidableEq α] {s : Sym α n.succ} {a : α} (h : a ∈ s) :
    (s.erase a h : Multiset α) = Multiset.erase s a :=
  rfl
#align sym.coe_erase Sym.coe_erase

@[simp]
theorem cons_erase [DecidableEq α] {s : Sym α n.succ} {a : α} (h : a ∈ s) : a ::ₛ s.erase a h = s :=
  coe_injective <| Multiset.cons_erase h
#align sym.cons_erase Sym.cons_erase

@[simp]
theorem erase_cons_head [DecidableEq α] (s : Sym α n) (a : α)
    (h : a ∈ a ::ₛ s := mem_cons_self a s) : (a ::ₛ s).erase a h = s :=
  coe_injective <| Multiset.erase_cons_head a s.1
#align sym.erase_cons_head Sym.erase_cons_head

/-- Another definition of the nth symmetric power, using vectors modulo permutations. (See `Sym`.)
-/
def Sym' (α : Type*) (n : ℕ) :=
  Quotient (Vector.Perm.isSetoid α n)
#align sym.sym' Sym.Sym'

/-- This is `cons` but for the alternative `Sym'` definition.
-/
def cons' {α : Type*} {n : ℕ} : α → Sym' α n → Sym' α (Nat.succ n) := fun a =>
  Quotient.map (Vector.cons a) fun ⟨_, _⟩ ⟨_, _⟩ h => List.Perm.cons _ h
#align sym.cons' Sym.cons'

@[inherit_doc]
scoped notation a " :: " b => cons' a b

/-- Multisets of cardinality n are equivalent to length-n vectors up to permutations.
-/
def symEquivSym' {α : Type*} {n : ℕ} : Sym α n ≃ Sym' α n :=
  Equiv.subtypeQuotientEquivQuotientSubtype _ _ (fun _ => by rfl) fun _ _ => by rfl
#align sym.sym_equiv_sym' Sym.symEquivSym'

theorem cons_equiv_eq_equiv_cons (α : Type*) (n : ℕ) (a : α) (s : Sym α n) :
    (a::symEquivSym' s) = symEquivSym' (a ::ₛ s) := by
  rcases s with ⟨⟨l⟩, _⟩
  rfl
#align sym.cons_equiv_eq_equiv_cons Sym.cons_equiv_eq_equiv_cons

instance instZeroSym : Zero (Sym α 0) :=
  ⟨⟨0, rfl⟩⟩

@[simp] theorem toMultiset_zero : toMultiset (0 : Sym α 0) = 0 := rfl

instance : EmptyCollection (Sym α 0) :=
  ⟨0⟩

theorem eq_nil_of_card_zero (s : Sym α 0) : s = nil :=
  Subtype.ext <| Multiset.card_eq_zero.1 s.2
#align sym.eq_nil_of_card_zero Sym.eq_nil_of_card_zero

instance uniqueZero : Unique (Sym α 0) :=
  ⟨⟨nil⟩, eq_nil_of_card_zero⟩
#align sym.unique_zero Sym.uniqueZero

/-- `replicate n a` is the sym containing only `a` with multiplicity `n`. -/
def replicate (n : ℕ) (a : α) : Sym α n :=
  ⟨Multiset.replicate n a, Multiset.card_replicate _ _⟩
#align sym.replicate Sym.replicate

theorem replicate_succ {a : α} {n : ℕ} : replicate n.succ a = a ::ₛ replicate n a :=
  rfl
#align sym.replicate_succ Sym.replicate_succ

theorem coe_replicate : (replicate n a : Multiset α) = Multiset.replicate n a :=
  rfl
#align sym.coe_replicate Sym.coe_replicate

@[simp]
theorem mem_replicate : b ∈ replicate n a ↔ n ≠ 0 ∧ b = a :=
  Multiset.mem_replicate
#align sym.mem_replicate Sym.mem_replicate

theorem eq_replicate_iff : s = replicate n a ↔ ∀ b ∈ s, b = a := by
  erw [Subtype.ext_iff, Multiset.eq_replicate]
  exact and_iff_right s.2
#align sym.eq_replicate_iff Sym.eq_replicate_iff

theorem exists_mem (s : Sym α n.succ) : ∃ a, a ∈ s :=
  Multiset.card_pos_iff_exists_mem.1 <| s.2.symm ▸ n.succ_pos
#align sym.exists_mem Sym.exists_mem

theorem exists_cons_of_mem {s : Sym α (n + 1)} {a : α} (h : a ∈ s) : ∃ t, s = a ::ₛ t := by
  obtain ⟨m, h⟩ := Multiset.exists_cons_of_mem h
  have : Multiset.card m = n := by
    apply_fun Multiset.card at h
    rw [s.2, Multiset.card_cons, add_left_inj] at h
    exact h.symm
  use ⟨m, this⟩
  apply Subtype.ext
  exact h

theorem exists_eq_cons_of_succ (s : Sym α n.succ) : ∃ (a : α) (s' : Sym α n), s = a ::ₛ s' := by
  obtain ⟨a, ha⟩ := exists_mem s
  classical exact ⟨a, s.erase a ha, (cons_erase ha).symm⟩
#align sym.exists_eq_cons_of_succ Sym.exists_eq_cons_of_succ

theorem eq_replicate {a : α} {n : ℕ} {s : Sym α n} : s = replicate n a ↔ ∀ b ∈ s, b = a :=
  Subtype.ext_iff.trans <| Multiset.eq_replicate.trans <| and_iff_right s.prop
#align sym.eq_replicate Sym.eq_replicate

theorem eq_replicate_of_subsingleton [Subsingleton α] (a : α) {n : ℕ} (s : Sym α n) :
    s = replicate n a :=
  eq_replicate.2 fun _ _ => Subsingleton.elim _ _
#align sym.eq_replicate_of_subsingleton Sym.eq_replicate_of_subsingleton

instance [Subsingleton α] (n : ℕ) : Subsingleton (Sym α n) :=
  ⟨by
    cases n
    · simp [eq_iff_true_of_subsingleton]
    · intro s s'
      obtain ⟨b, -⟩ := exists_mem s
      rw [eq_replicate_of_subsingleton b s', eq_replicate_of_subsingleton b s]⟩

instance inhabitedSym [Inhabited α] (n : ℕ) : Inhabited (Sym α n) :=
  ⟨replicate n default⟩
#align sym.inhabited_sym Sym.inhabitedSym

instance inhabitedSym' [Inhabited α] (n : ℕ) : Inhabited (Sym' α n) :=
  ⟨Quotient.mk' (Vector.replicate n default)⟩
#align sym.inhabited_sym' Sym.inhabitedSym'

instance (n : ℕ) [IsEmpty α] : IsEmpty (Sym α n.succ) :=
  ⟨fun s => by
    obtain ⟨a, -⟩ := exists_mem s
    exact isEmptyElim a⟩

instance (n : ℕ) [Unique α] : Unique (Sym α n) :=
  Unique.mk' _

theorem replicate_right_inj {a b : α} {n : ℕ} (h : n ≠ 0) : replicate n a = replicate n b ↔ a = b :=
  Subtype.ext_iff.trans (Multiset.replicate_right_inj h)
#align sym.replicate_right_inj Sym.replicate_right_inj

theorem replicate_right_injective {n : ℕ} (h : n ≠ 0) :
    Function.Injective (replicate n : α → Sym α n) := fun _ _ => (replicate_right_inj h).1
#align sym.replicate_right_injective Sym.replicate_right_injective

instance (n : ℕ) [Nontrivial α] : Nontrivial (Sym α (n + 1)) :=
  (replicate_right_injective n.succ_ne_zero).nontrivial

/-- A function `α → β` induces a function `Sym α n → Sym β n` by applying it to every element of
the underlying `n`-tuple. -/
def map {n : ℕ} (f : α → β) (x : Sym α n) : Sym β n :=
  ⟨x.val.map f, by simp⟩
#align sym.map Sym.map

@[simp]
theorem mem_map {n : ℕ} {f : α → β} {b : β} {l : Sym α n} :
    b ∈ Sym.map f l ↔ ∃ a, a ∈ l ∧ f a = b :=
  Multiset.mem_map
#align sym.mem_map Sym.mem_map

/-- Note: `Sym.map_id` is not simp-normal, as simp ends up unfolding `id` with `Sym.map_congr` -/
@[simp]
theorem map_id' {α : Type*} {n : ℕ} (s : Sym α n) : Sym.map (fun x : α => x) s = s := by
  ext; simp only [map, val_eq_coe, Multiset.map_id', coe_inj]; rfl
#align sym.map_id' Sym.map_id'

theorem map_id {α : Type*} {n : ℕ} (s : Sym α n) : Sym.map id s = s := by
  ext; simp only [map, val_eq_coe, id_eq, Multiset.map_id', coe_inj]; rfl
#align sym.map_id Sym.map_id

@[simp]
theorem map_map {α β γ : Type*} {n : ℕ} (g : β → γ) (f : α → β) (s : Sym α n) :
    Sym.map g (Sym.map f s) = Sym.map (g ∘ f) s :=
  Subtype.ext <| by dsimp only [Sym.map]; simp
#align sym.map_map Sym.map_map

@[simp]
theorem map_zero (f : α → β) : Sym.map f (0 : Sym α 0) = (0 : Sym β 0) :=
  rfl
#align sym.map_zero Sym.map_zero

@[simp]
theorem map_cons {n : ℕ} (f : α → β) (a : α) (s : Sym α n) : (a ::ₛ s).map f = f a ::ₛ s.map f :=
  ext <| Multiset.map_cons _ _ _
#align sym.map_cons Sym.map_cons

@[congr]
theorem map_congr {f g : α → β} {s : Sym α n} (h : ∀ x ∈ s, f x = g x) : map f s = map g s :=
  Subtype.ext <| Multiset.map_congr rfl h
#align sym.map_congr Sym.map_congr

@[simp]
theorem map_mk {f : α → β} {m : Multiset α} {hc : Multiset.card m = n} :
    map f (mk m hc) = mk (m.map f) (by simp [hc]) :=
  rfl
#align sym.map_mk Sym.map_mk

@[simp]
theorem coe_map (s : Sym α n) (f : α → β) : ↑(s.map f) = Multiset.map f s :=
  rfl
#align sym.coe_map Sym.coe_map

theorem map_injective {f : α → β} (hf : Injective f) (n : ℕ) :
    Injective (map f : Sym α n → Sym β n) := fun _ _ h =>
  coe_injective <| Multiset.map_injective hf <| coe_inj.2 h
#align sym.map_injective Sym.map_injective

/-- Mapping an equivalence `α ≃ β` using `Sym.map` gives an equivalence between `Sym α n` and
`Sym β n`. -/
@[simps]
def equivCongr (e : α ≃ β) : Sym α n ≃ Sym β n where
  toFun := map e
  invFun := map e.symm
  left_inv x := by rw [map_map, Equiv.symm_comp_self, map_id]
  right_inv x := by rw [map_map, Equiv.self_comp_symm, map_id]
#align sym.equiv_congr Sym.equivCongr
#align sym.equiv_congr_symm_apply Sym.equivCongr_symm_apply
#align sym.equiv_congr_apply Sym.equivCongr_apply

/-- "Attach" a proof that `a ∈ s` to each element `a` in `s` to produce
an element of the symmetric power on `{x // x ∈ s}`. -/
def attach (s : Sym α n) : Sym { x // x ∈ s } n :=
  ⟨s.val.attach, by (conv_rhs => rw [← s.2, ← Multiset.card_attach]); rfl⟩
#align sym.attach Sym.attach

@[simp]
theorem attach_mk {m : Multiset α} {hc : Multiset.card m = n} :
    attach (mk m hc) = mk m.attach (Multiset.card_attach.trans hc) :=
  rfl
#align sym.attach_mk Sym.attach_mk

@[simp]
theorem coe_attach (s : Sym α n) : (s.attach : Multiset { a // a ∈ s }) =
    Multiset.attach (s : Multiset α) :=
  rfl
#align sym.coe_attach Sym.coe_attach

theorem attach_map_coe (s : Sym α n) : s.attach.map (↑) = s :=
  coe_injective <| Multiset.attach_map_val _
#align sym.attach_map_coe Sym.attach_map_coe

@[simp]
theorem mem_attach (s : Sym α n) (x : { x // x ∈ s }) : x ∈ s.attach :=
  Multiset.mem_attach _ _
#align sym.mem_attach Sym.mem_attach

@[simp]
theorem attach_nil : (nil : Sym α 0).attach = nil :=
  rfl
#align sym.attach_nil Sym.attach_nil

@[simp]
theorem attach_cons (x : α) (s : Sym α n) :
    (cons x s).attach =
      cons ⟨x, mem_cons_self _ _⟩ (s.attach.map fun x => ⟨x, mem_cons_of_mem x.prop⟩) :=
  coe_injective <| Multiset.attach_cons _ _
#align sym.attach_cons Sym.attach_cons

/-- Change the length of a `Sym` using an equality.
The simp-normal form is for the `cast` to be pushed outward. -/
protected def cast {n m : ℕ} (h : n = m) : Sym α n ≃ Sym α m where
  toFun s := ⟨s.val, s.2.trans h⟩
  invFun s := ⟨s.val, s.2.trans h.symm⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
#align sym.cast Sym.cast

@[simp]
theorem cast_rfl : Sym.cast rfl s = s :=
  Subtype.ext rfl
#align sym.cast_rfl Sym.cast_rfl

@[simp]
theorem cast_cast {n'' : ℕ} (h : n = n') (h' : n' = n'') :
    Sym.cast h' (Sym.cast h s) = Sym.cast (h.trans h') s :=
  rfl
#align sym.cast_cast Sym.cast_cast

@[simp]
theorem coe_cast (h : n = m) : (Sym.cast h s : Multiset α) = s :=
  rfl
#align sym.coe_cast Sym.coe_cast

@[simp]
theorem mem_cast (h : n = m) : a ∈ Sym.cast h s ↔ a ∈ s :=
  Iff.rfl
#align sym.mem_cast Sym.mem_cast

/-- Append a pair of `Sym` terms. -/
def append (s : Sym α n) (s' : Sym α n') : Sym α (n + n') :=
  ⟨s.1 + s'.1, by rw [map_add, s.2, s'.2]⟩
#align sym.append Sym.append

@[simp]
theorem append_inj_right (s : Sym α n) {t t' : Sym α n'} : s.append t = s.append t' ↔ t = t' :=
  Subtype.ext_iff.trans <| (add_right_inj _).trans Subtype.ext_iff.symm
#align sym.append_inj_right Sym.append_inj_right

@[simp]
theorem append_inj_left {s s' : Sym α n} (t : Sym α n') : s.append t = s'.append t ↔ s = s' :=
  Subtype.ext_iff.trans <| (add_left_inj _).trans Subtype.ext_iff.symm
#align sym.append_inj_left Sym.append_inj_left

theorem append_comm (s : Sym α n') (s' : Sym α n') :
    s.append s' = Sym.cast (add_comm _ _) (s'.append s) := by
  ext
  simp [append, add_comm]
#align sym.append_comm Sym.append_comm

@[simp, norm_cast]
theorem coe_append (s : Sym α n) (s' : Sym α n') : (s.append s' : Multiset α) = s + s' :=
  rfl
#align sym.coe_append Sym.coe_append

theorem mem_append_iff {s' : Sym α m} : a ∈ s.append s' ↔ a ∈ s ∨ a ∈ s' :=
  Multiset.mem_add
#align sym.mem_append_iff Sym.mem_append_iff

/-- Fill a term `m : Sym α (n - i)` with `i` copies of `a` to obtain a term of `Sym α n`.
This is a convenience wrapper for `m.append (replicate i a)` that adjusts the term using
`Sym.cast`. -/
def fill (a : α) (i : Fin (n + 1)) (m : Sym α (n - i)) : Sym α n :=
  Sym.cast (Nat.sub_add_cancel i.is_le) (m.append (replicate i a))
#align sym.fill Sym.fill

theorem coe_fill {a : α} {i : Fin (n + 1)} {m : Sym α (n - i)} :
    (fill a i m : Multiset α) = m + replicate i a :=
  rfl
#align sym.coe_fill Sym.coe_fill

theorem mem_fill_iff {a b : α} {i : Fin (n + 1)} {s : Sym α (n - i)} :
    a ∈ Sym.fill b i s ↔ (i : ℕ) ≠ 0 ∧ a = b ∨ a ∈ s := by
  rw [fill, mem_cast, mem_append_iff, or_comm, mem_replicate]
#align sym.mem_fill_iff Sym.mem_fill_iff

open Multiset

/-- Remove every `a` from a given `Sym α n`.
Yields the number of copies `i` and a term of `Sym α (n - i)`. -/
def filterNe [DecidableEq α] (a : α) (m : Sym α n) : Σi : Fin (n + 1), Sym α (n - i) :=
  ⟨⟨m.1.count a, (count_le_card _ _).trans_lt <| by rw [m.2, Nat.lt_succ_iff]⟩,
    m.1.filter (a ≠ ·),
    Nat.eq_sub_of_add_eq <|
      Eq.trans
        (by
          rw [← countP_eq_card_filter, add_comm]
          simp only [eq_comm, Ne, count]
          rw [← card_eq_countP_add_countP _ _])
        m.2⟩
#align sym.filter_ne Sym.filterNe

theorem sigma_sub_ext {m₁ m₂ : Σi : Fin (n + 1), Sym α (n - i)} (h : (m₁.2 : Multiset α) = m₂.2) :
    m₁ = m₂ :=
  Sigma.subtype_ext
    (Fin.ext <| by
      rw [← Nat.sub_sub_self (Nat.le_of_lt_succ m₁.1.is_lt), ← m₁.2.2, val_eq_coe, h,
        ← val_eq_coe, m₂.2.2, Nat.sub_sub_self (Nat.le_of_lt_succ m₂.1.is_lt)])
    h
#align sym.sigma_sub_ext Sym.sigma_sub_ext

theorem fill_filterNe [DecidableEq α] (a : α) (m : Sym α n) :
    (m.filterNe a).2.fill a (m.filterNe a).1 = m :=
  Sym.ext
    (by
      rw [coe_fill, filterNe, ← val_eq_coe, Subtype.coe_mk, Fin.val_mk]
      ext b; dsimp
      rw [count_add, count_filter, Sym.coe_replicate, count_replicate]
      obtain rfl | h := eq_or_ne a b
      · rw [if_pos rfl, if_neg (not_not.2 rfl), zero_add]
      · rw [if_pos h, if_neg h.symm, add_zero])
#align sym.fill_filter_ne Sym.fill_filterNe

theorem filter_ne_fill [DecidableEq α] (a : α) (m : Σi : Fin (n + 1), Sym α (n - i)) (h : a ∉ m.2) :
    (m.2.fill a m.1).filterNe a = m :=
  sigma_sub_ext
    (by
      rw [filterNe, ← val_eq_coe, Subtype.coe_mk, val_eq_coe, coe_fill]
      rw [filter_add, filter_eq_self.2, add_right_eq_self, eq_zero_iff_forall_not_mem]
      · intro b hb
        rw [mem_filter, Sym.mem_coe, mem_replicate] at hb
        exact hb.2 hb.1.2.symm
      · exact fun a ha ha' => h <| ha'.symm ▸ ha)
#align sym.filter_ne_fill Sym.filter_ne_fill

theorem count_coe_fill_self_of_not_mem [DecidableEq α] {a : α} {i : Fin (n + 1)} {s : Sym α (n - i)}
    (hx : a ∉ s) :
    count a (fill a i s : Multiset α) = i := by
  simp [coe_fill, coe_replicate, hx]

theorem count_coe_fill_of_ne [DecidableEq α] {a x : α} {i : Fin (n + 1)} {s : Sym α (n - i)}
    (hx : x ≠ a) :
    count x (fill a i s : Multiset α) = count x s := by
  suffices x ∉ Multiset.replicate i a by simp [coe_fill, coe_replicate, this]
  simp [Multiset.mem_replicate, hx]

end Sym

section Equiv

/-! ### Combinatorial equivalences -/


variable {α : Type*} {n : ℕ}

open Sym

namespace SymOptionSuccEquiv

/-- Function from the symmetric product over `Option` splitting on whether or not
it contains a `none`. -/
def encode [DecidableEq α] (s : Sym (Option α) n.succ) : Sum (Sym (Option α) n) (Sym α n.succ) :=
  if h : none ∈ s then Sum.inl (s.erase none h)
  else
    Sum.inr
      (s.attach.map fun o =>
        o.1.get <| Option.ne_none_iff_isSome.1 <| ne_of_mem_of_not_mem o.2 h)
#align sym_option_succ_equiv.encode SymOptionSuccEquiv.encode

@[simp]
theorem encode_of_none_mem [DecidableEq α] (s : Sym (Option α) n.succ) (h : none ∈ s) :
    encode s = Sum.inl (s.erase none h) :=
  dif_pos h
#align sym_option_succ_equiv.encode_of_none_mem SymOptionSuccEquiv.encode_of_none_mem

@[simp]
theorem encode_of_not_none_mem [DecidableEq α] (s : Sym (Option α) n.succ) (h : ¬none ∈ s) :
    encode s =
      Sum.inr
        (s.attach.map fun o =>
          o.1.get <| Option.ne_none_iff_isSome.1 <| ne_of_mem_of_not_mem o.2 h) :=
  dif_neg h
#align sym_option_succ_equiv.encode_of_not_none_mem SymOptionSuccEquiv.encode_of_not_none_mem

/-- Inverse of `Sym_option_succ_equiv.decode`. -/
-- @[simp] Porting note: not a nice simp lemma, applies too often in Lean4
def decode : Sum (Sym (Option α) n) (Sym α n.succ) → Sym (Option α) n.succ
  | Sum.inl s => none ::ₛ s
  | Sum.inr s => s.map Embedding.some
#align sym_option_succ_equiv.decode SymOptionSuccEquiv.decode

@[simp]
theorem decode_inl (s : Sym (Option α) n) : decode (Sum.inl s) = none ::ₛ s :=
  rfl

@[simp]
theorem decode_inr (s : Sym α n.succ) : decode (Sum.inr s) = s.map Embedding.some :=
  rfl

@[simp]
theorem decode_encode [DecidableEq α] (s : Sym (Option α) n.succ) : decode (encode s) = s := by
  by_cases h : none ∈ s
  · simp [h]
  · simp only [decode, h, not_false_iff, encode_of_not_none_mem, Embedding.some_apply, map_map,
      comp_apply, Option.some_get]
    convert s.attach_map_coe
#align sym_option_succ_equiv.decode_encode SymOptionSuccEquiv.decode_encode

@[simp]
theorem encode_decode [DecidableEq α] (s : Sum (Sym (Option α) n) (Sym α n.succ)) :
    encode (decode s) = s := by
  obtain s | s := s
  · simp
  · unfold SymOptionSuccEquiv.encode
    split_ifs with h
    · obtain ⟨a, _, ha⟩ := Multiset.mem_map.mp h
      exact Option.some_ne_none _ ha
    · refine congr_arg Sum.inr ?_
      refine map_injective (Option.some_injective _) _ ?_
      refine Eq.trans ?_ (.trans (SymOptionSuccEquiv.decode (Sum.inr s)).attach_map_coe ?_) <;> simp
#align sym_option_succ_equiv.encode_decode SymOptionSuccEquiv.encode_decode

end SymOptionSuccEquiv

/-- The symmetric product over `Option` is a disjoint union over simpler symmetric products. -/
--@[simps]
def symOptionSuccEquiv [DecidableEq α] :
    Sym (Option α) n.succ ≃ Sum (Sym (Option α) n) (Sym α n.succ) where
  toFun := SymOptionSuccEquiv.encode
  invFun := SymOptionSuccEquiv.decode
  left_inv := SymOptionSuccEquiv.decode_encode
  right_inv := SymOptionSuccEquiv.encode_decode
#align sym_option_succ_equiv symOptionSuccEquiv

end Equiv
