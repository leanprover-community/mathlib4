/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module logic.denumerable
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Lattice
import Mathbin.Data.List.MinMax
import Mathbin.Data.Nat.Order.Lemmas
import Mathbin.Logic.Encodable.Basic

/-!
# Denumerable types

This file defines denumerable (countably infinite) types as a typeclass extending `encodable`. This
is used to provide explicit encode/decode functions from and to `ℕ`, with the information that those
functions are inverses of each other.

## Implementation notes

This property already has a name, namely `α ≃ ℕ`, but here we are interested in using it as a
typeclass.
-/


variable {α β : Type _}

/-- A denumerable type is (constructively) bijective with `ℕ`. Typeclass equivalent of `α ≃ ℕ`. -/
class Denumerable (α : Type _) extends Encodable α where
  decode_inv : ∀ n, ∃ a ∈ decode n, encode a = n
#align denumerable Denumerable

open Nat

namespace Denumerable

section

variable [Denumerable α] [Denumerable β]

open Encodable

theorem decode_is_some (α) [Denumerable α] (n : ℕ) : (decode α n).isSome :=
  Option.isSome_iff_exists.2 <| (decode_inv n).imp fun a => Exists.fst
#align denumerable.decode_is_some Denumerable.decode_is_some

/-- Returns the `n`-th element of `α` indexed by the decoding. -/
def ofNat (α) [f : Denumerable α] (n : ℕ) : α :=
  Option.get (decode_is_some α n)
#align denumerable.of_nat Denumerable.ofNat

@[simp]
theorem decode_eq_of_nat (α) [Denumerable α] (n : ℕ) : decode α n = some (ofNat α n) :=
  Option.eq_some_of_isSome _
#align denumerable.decode_eq_of_nat Denumerable.decode_eq_of_nat

@[simp]
theorem of_nat_of_decode {n b} (h : decode α n = some b) : ofNat α n = b :=
  Option.some.inj <| (decode_eq_of_nat _ _).symm.trans h
#align denumerable.of_nat_of_decode Denumerable.of_nat_of_decode

@[simp]
theorem encode_of_nat (n) : encode (ofNat α n) = n :=
  by
  let ⟨a, h, e⟩ := decode_inv n
  rwa [of_nat_of_decode h]
#align denumerable.encode_of_nat Denumerable.encode_of_nat

@[simp]
theorem of_nat_encode (a) : ofNat α (encode a) = a :=
  of_nat_of_decode (encodek _)
#align denumerable.of_nat_encode Denumerable.of_nat_encode

/-- A denumerable type is equivalent to `ℕ`. -/
def eqv (α) [Denumerable α] : α ≃ ℕ :=
  ⟨encode, ofNat α, of_nat_encode, encode_of_nat⟩
#align denumerable.eqv Denumerable.eqv

-- See Note [lower instance priority]
instance (priority := 100) : Infinite α :=
  Infinite.of_surjective _ (eqv α).Surjective

/-- A type equivalent to `ℕ` is denumerable. -/
def mk' {α} (e : α ≃ ℕ) : Denumerable α where
  encode := e
  decode := some ∘ e.symm
  encodek a := congr_arg some (e.symm_apply_apply _)
  decode_inv n := ⟨_, rfl, e.apply_symm_apply _⟩
#align denumerable.mk' Denumerable.mk'

/-- Denumerability is conserved by equivalences. This is transitivity of equivalence the denumerable
way. -/
def ofEquiv (α) {β} [Denumerable α] (e : β ≃ α) : Denumerable β :=
  { Encodable.ofEquiv _ e with decode_inv := fun n => by simp }
#align denumerable.of_equiv Denumerable.ofEquiv

@[simp]
theorem of_equiv_of_nat (α) {β} [Denumerable α] (e : β ≃ α) (n) :
    @ofNat β (ofEquiv _ e) n = e.symm (ofNat α n) := by
  apply of_nat_of_decode <;> show Option.map _ _ = _ <;> simp
#align denumerable.of_equiv_of_nat Denumerable.of_equiv_of_nat

/-- All denumerable types are equivalent. -/
def equiv₂ (α β) [Denumerable α] [Denumerable β] : α ≃ β :=
  (eqv α).trans (eqv β).symm
#align denumerable.equiv₂ Denumerable.equiv₂

instance nat : Denumerable ℕ :=
  ⟨fun n => ⟨_, rfl, rfl⟩⟩
#align denumerable.nat Denumerable.nat

@[simp]
theorem of_nat_nat (n) : ofNat ℕ n = n :=
  rfl
#align denumerable.of_nat_nat Denumerable.of_nat_nat

/-- If `α` is denumerable, then so is `option α`. -/
instance option : Denumerable (Option α) :=
  ⟨fun n => by
    cases n
    · refine' ⟨none, _, encode_none⟩
      rw [decode_option_zero, Option.mem_def]
    refine' ⟨some (of_nat α n), _, _⟩
    · rw [decode_option_succ, decode_eq_of_nat, Option.map_some', Option.mem_def]
    rw [encode_some, encode_of_nat]⟩
#align denumerable.option Denumerable.option

/-- If `α` and `β` are denumerable, then so is their sum. -/
instance sum : Denumerable (Sum α β) :=
  ⟨fun n =>
    by
    suffices ∃ a ∈ @decode_sum α β _ _ n, encode_sum a = bit (bodd n) (div2 n) by simpa [bit_decomp]
    simp [decode_sum] <;> cases bodd n <;> simp [decode_sum, bit, encode_sum]⟩
#align denumerable.sum Denumerable.sum

section Sigma

variable {γ : α → Type _} [∀ a, Denumerable (γ a)]

/-- A denumerable collection of denumerable types is denumerable. -/
instance sigma : Denumerable (Sigma γ) :=
  ⟨fun n => by simp [decode_sigma] <;> exact ⟨_, _, ⟨rfl, HEq.rfl⟩, by simp⟩⟩
#align denumerable.sigma Denumerable.sigma

@[simp]
theorem sigma_of_nat_val (n : ℕ) :
    ofNat (Sigma γ) n = ⟨ofNat α (unpair n).1, ofNat (γ _) (unpair n).2⟩ :=
  Option.some.inj <| by rw [← decode_eq_of_nat, decode_sigma_val] <;> simp <;> rfl
#align denumerable.sigma_of_nat_val Denumerable.sigma_of_nat_val

end Sigma

/-- If `α` and `β` are denumerable, then so is their product. -/
instance prod : Denumerable (α × β) :=
  ofEquiv _ (Equiv.sigmaEquivProd α β).symm
#align denumerable.prod Denumerable.prod

@[simp]
theorem prod_of_nat_val (n : ℕ) : ofNat (α × β) n = (ofNat α (unpair n).1, ofNat β (unpair n).2) :=
  by simp <;> rfl
#align denumerable.prod_of_nat_val Denumerable.prod_of_nat_val

@[simp]
theorem prod_nat_of_nat : ofNat (ℕ × ℕ) = unpair := by funext <;> simp
#align denumerable.prod_nat_of_nat Denumerable.prod_nat_of_nat

instance int : Denumerable ℤ :=
  Denumerable.mk' Equiv.intEquivNat
#align denumerable.int Denumerable.int

instance pnat : Denumerable ℕ+ :=
  Denumerable.mk' Equiv.pnatEquivNat
#align denumerable.pnat Denumerable.pnat

/-- The lift of a denumerable type is denumerable. -/
instance ulift : Denumerable (ULift α) :=
  ofEquiv _ Equiv.ulift
#align denumerable.ulift Denumerable.ulift

/-- The lift of a denumerable type is denumerable. -/
instance plift : Denumerable (PLift α) :=
  ofEquiv _ Equiv.plift
#align denumerable.plift Denumerable.plift

/-- If `α` is denumerable, then `α × α` and `α` are equivalent. -/
def pair : α × α ≃ α :=
  equiv₂ _ _
#align denumerable.pair Denumerable.pair

end

end Denumerable

namespace Nat.Subtype

open Function Encodable

/-! ### Subsets of `ℕ` -/


variable {s : Set ℕ} [Infinite s]

section Classical

open Classical

theorem exists_succ (x : s) : ∃ n, ↑x + n + 1 ∈ s :=
  by_contradiction fun h =>
    have : ∀ (a : ℕ) (ha : a ∈ s), a < succ x := fun a ha =>
      lt_of_not_ge fun hax => h ⟨a - (x + 1), by rwa [add_right_comm, add_tsub_cancel_of_le hax]⟩
    Fintype.false
      ⟨(((Multiset.range (succ x)).filter (· ∈ s)).pmap
            (fun (y : ℕ) (hy : y ∈ s) => Subtype.mk y hy)
            (by simp [-Multiset.range_succ])).toFinset,
        by simpa [Subtype.ext_iff_val, Multiset.mem_filter, -Multiset.range_succ] ⟩
#align nat.subtype.exists_succ Nat.Subtype.exists_succ

end Classical

variable [DecidablePred (· ∈ s)]

/-- Returns the next natural in a set, according to the usual ordering of `ℕ`. -/
def succ (x : s) : s :=
  have h : ∃ m, ↑x + m + 1 ∈ s := exists_succ x
  ⟨↑x + Nat.find h + 1, Nat.find_spec h⟩
#align nat.subtype.succ Nat.Subtype.succ

theorem succ_le_of_lt {x y : s} (h : y < x) : succ y ≤ x :=
  have hx : ∃ m, ↑y + m + 1 ∈ s := exists_succ _
  let ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
  have : Nat.find hx ≤ k := Nat.find_min' _ (hk ▸ x.2)
  show (y : ℕ) + Nat.find hx + 1 ≤ x by
    rw [hk] <;> exact add_le_add_right (add_le_add_left this _) _
#align nat.subtype.succ_le_of_lt Nat.Subtype.succ_le_of_lt

theorem le_succ_of_forall_lt_le {x y : s} (h : ∀ z < x, z ≤ y) : x ≤ succ y :=
  have hx : ∃ m, ↑y + m + 1 ∈ s := exists_succ _
  show ↑x ≤ ↑y + Nat.find hx + 1 from
    le_of_not_gt fun hxy =>
      (h ⟨_, Nat.find_spec hx⟩ hxy).not_lt <|
        calc
          ↑y ≤ ↑y + Nat.find hx := le_add_of_nonneg_right (Nat.zero_le _)
          _ < ↑y + Nat.find hx + 1 := Nat.lt_succ_self _
          
#align nat.subtype.le_succ_of_forall_lt_le Nat.Subtype.le_succ_of_forall_lt_le

theorem lt_succ_self (x : s) : x < succ x :=
  calc
    (x : ℕ) ≤ x + _ := le_self_add
    _ < succ x := Nat.lt_succ_self (x + _)
    
#align nat.subtype.lt_succ_self Nat.Subtype.lt_succ_self

theorem lt_succ_iff_le {x y : s} : x < succ y ↔ x ≤ y :=
  ⟨fun h => le_of_not_gt fun h' => not_le_of_gt h (succ_le_of_lt h'), fun h =>
    lt_of_le_of_lt h (lt_succ_self _)⟩
#align nat.subtype.lt_succ_iff_le Nat.Subtype.lt_succ_iff_le

/-- Returns the `n`-th element of a set, according to the usual ordering of `ℕ`. -/
def ofNat (s : Set ℕ) [DecidablePred (· ∈ s)] [Infinite s] : ℕ → s
  | 0 => ⊥
  | n + 1 => succ (of_nat n)
#align nat.subtype.of_nat Nat.Subtype.ofNat

theorem of_nat_surjective_aux : ∀ {x : ℕ} (hx : x ∈ s), ∃ n, ofNat s n = ⟨x, hx⟩
  | x => fun hx =>
    by
    let t : List s :=
      ((List.range x).filter fun y => y ∈ s).pmap (fun (y : ℕ) (hy : y ∈ s) => ⟨y, hy⟩) (by simp)
    have hmt : ∀ {y : s}, y ∈ t ↔ y < ⟨x, hx⟩ := by
      simp [List.mem_filter, Subtype.ext_iff_val, t] <;> intros <;> rfl
    have wf : ∀ m : s, List.maximum t = m → ↑m < x := fun m hmax => by
      simpa [hmt] using List.maximum_mem hmax
    cases' hmax : List.maximum t with m
    ·
      exact
        ⟨0,
          le_antisymm bot_le
            (le_of_not_gt fun h =>
              List.not_mem_nil (⊥ : s) <| by rw [← List.maximum_eq_none.1 hmax, hmt] <;> exact h)⟩
    cases' of_nat_surjective_aux m.2 with a ha
    exact
      ⟨a + 1,
        le_antisymm (by rw [of_nat] <;> exact succ_le_of_lt (by rw [ha] <;> exact wf _ hmax)) <| by
          rw [of_nat] <;>
            exact
              le_succ_of_forall_lt_le fun z hz => by
                rw [ha] <;> cases m <;> exact List.le_maximum_of_mem (hmt.2 hz) hmax⟩decreasing_by
  tauto
#align nat.subtype.of_nat_surjective_aux Nat.Subtype.of_nat_surjective_aux

theorem of_nat_surjective : Surjective (ofNat s) := fun ⟨x, hx⟩ => of_nat_surjective_aux hx
#align nat.subtype.of_nat_surjective Nat.Subtype.of_nat_surjective

@[simp]
theorem of_nat_range : Set.range (ofNat s) = Set.univ :=
  of_nat_surjective.range_eq
#align nat.subtype.of_nat_range Nat.Subtype.of_nat_range

@[simp]
theorem coe_comp_of_nat_range : Set.range (coe ∘ ofNat s : ℕ → ℕ) = s := by
  rw [Set.range_comp coe, of_nat_range, Set.image_univ, Subtype.range_coe]
#align nat.subtype.coe_comp_of_nat_range Nat.Subtype.coe_comp_of_nat_range

private def to_fun_aux (x : s) : ℕ :=
  (List.range x).countp (· ∈ s)
#align nat.subtype.to_fun_aux nat.subtype.to_fun_aux

private theorem to_fun_aux_eq (x : s) : toFunAux x = ((Finset.range x).filter (· ∈ s)).card := by
  rw [to_fun_aux, List.countp_eq_length_filter] <;> rfl
#align nat.subtype.to_fun_aux_eq nat.subtype.to_fun_aux_eq

open Finset

private theorem right_inverse_aux : ∀ n, toFunAux (ofNat s n) = n
  | 0 => by
    rw [to_fun_aux_eq, card_eq_zero, eq_empty_iff_forall_not_mem]
    rintro n hn
    rw [mem_filter, of_nat, mem_range] at hn
    exact bot_le.not_lt (show (⟨n, hn.2⟩ : s) < ⊥ from hn.1)
  | n + 1 => by
    have ih : toFunAux (ofNat s n) = n := right_inverse_aux n
    have h₁ : (ofNat s n : ℕ) ∉ (range (ofNat s n)).filter (· ∈ s) := by simp
    have h₂ :
      (range (succ (ofNat s n))).filter (· ∈ s) =
        insert (ofNat s n) ((range (ofNat s n)).filter (· ∈ s)) :=
      by
      simp only [Finset.ext_iff, mem_insert, mem_range, mem_filter]
      exact fun m =>
        ⟨fun h => by
          simp only [h.2, and_true_iff] <;>
            exact Or.symm (lt_or_eq_of_le ((@lt_succ_iff_le _ _ _ ⟨m, h.2⟩ _).1 h.1)),
          fun h =>
          h.elim (fun h => h.symm ▸ ⟨lt_succ_self _, (of_nat s n).Prop⟩) fun h =>
            ⟨h.1.trans (lt_succ_self _), h.2⟩⟩
    simp only [to_fun_aux_eq, of_nat, range_succ] at ih⊢
    conv =>
      rhs
      rw [← ih, ← card_insert_of_not_mem h₁, ← h₂]
#align nat.subtype.right_inverse_aux nat.subtype.right_inverse_aux

/-- Any infinite set of naturals is denumerable. -/
def denumerable (s : Set ℕ) [DecidablePred (· ∈ s)] [Infinite s] : Denumerable s :=
  Denumerable.ofEquiv ℕ
    { toFun := toFunAux
      invFun := ofNat s
      left_inv := leftInverse_of_surjective_of_rightInverse of_nat_surjective right_inverse_aux
      right_inv := right_inverse_aux }
#align nat.subtype.denumerable Nat.Subtype.denumerable

end Nat.Subtype

namespace Denumerable

open Encodable

/-- An infinite encodable type is denumerable. -/
def ofEncodableOfInfinite (α : Type _) [Encodable α] [Infinite α] : Denumerable α :=
  by
  letI := @decidable_range_encode α _ <;>
    letI : Infinite (Set.range (@encode α _)) :=
      Infinite.of_injective _ (Equiv.ofInjective _ encode_injective).Injective
  letI := Nat.Subtype.denumerable (Set.range (@encode α _))
  exact Denumerable.ofEquiv (Set.range (@encode α _)) (equiv_range_encode α)
#align denumerable.of_encodable_of_infinite Denumerable.ofEncodableOfInfinite

end Denumerable

/-- See also `nonempty_encodable`, `nonempty_fintype`. -/
theorem nonempty_denumerable (α : Type _) [Countable α] [Infinite α] : Nonempty (Denumerable α) :=
  (nonempty_encodable α).map fun h => Denumerable.ofEncodableOfInfinite _
#align nonempty_denumerable nonempty_denumerable

instance nonempty_equiv_of_countable [Countable α] [Infinite α] [Countable β] [Infinite β] :
    Nonempty (α ≃ β) := by
  cases nonempty_denumerable α
  cases nonempty_denumerable β
  exact ⟨(Denumerable.eqv _).trans (Denumerable.eqv _).symm⟩
#align nonempty_equiv_of_countable nonempty_equiv_of_countable

