/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Logic.Encodable.Basic

#align_import logic.denumerable from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

/-!
# Denumerable types

This file defines denumerable (countably infinite) types as a typeclass extending `Encodable`. This
is used to provide explicit encode/decode functions from and to `ℕ`, with the information that those
functions are inverses of each other.

## Implementation notes

This property already has a name, namely `α ≃ ℕ`, but here we are interested in using it as a
typeclass.
-/


variable {α β : Type*}

/-- A denumerable type is (constructively) bijective with `ℕ`. Typeclass equivalent of `α ≃ ℕ`. -/
class Denumerable (α : Type*) extends Encodable α where
  /-- `decode` and `encode` are inverses. -/
  decode_inv : ∀ n, ∃ a ∈ decode n, encode a = n
#align denumerable Denumerable

open Nat

namespace Denumerable

section

variable [Denumerable α] [Denumerable β]

open Encodable

theorem decode_isSome (α) [Denumerable α] (n : ℕ) : (decode (α := α) n).isSome :=
  Option.isSome_iff_exists.2 <| (decode_inv n).imp fun _ => And.left
#align denumerable.decode_is_some Denumerable.decode_isSome

/-- Returns the `n`-th element of `α` indexed by the decoding. -/
def ofNat (α) [Denumerable α] (n : ℕ) : α :=
  Option.get _ (decode_isSome α n)
#align denumerable.of_nat Denumerable.ofNat

@[simp]
theorem decode_eq_ofNat (α) [Denumerable α] (n : ℕ) : decode (α := α) n = some (ofNat α n) :=
  Option.eq_some_of_isSome _
#align denumerable.decode_eq_of_nat Denumerable.decode_eq_ofNat

@[simp]
theorem ofNat_of_decode {n b} (h : decode (α := α) n = some b) : ofNat (α := α) n = b :=
  Option.some.inj <| (decode_eq_ofNat _ _).symm.trans h
#align denumerable.of_nat_of_decode Denumerable.ofNat_of_decode

@[simp]
theorem encode_ofNat (n) : encode (ofNat α n) = n := by
  obtain ⟨a, h, e⟩ := decode_inv (α := α) n
  -- ⊢ encode (ofNat α n) = n
  rwa [ofNat_of_decode h]
  -- 🎉 no goals
#align denumerable.encode_of_nat Denumerable.encode_ofNat

@[simp]
theorem ofNat_encode (a) : ofNat α (encode a) = a :=
  ofNat_of_decode (encodek _)
#align denumerable.of_nat_encode Denumerable.ofNat_encode

/-- A denumerable type is equivalent to `ℕ`. -/
def eqv (α) [Denumerable α] : α ≃ ℕ :=
  ⟨encode, ofNat α, ofNat_encode, encode_ofNat⟩
#align denumerable.eqv Denumerable.eqv

-- See Note [lower instance priority]
instance (priority := 100) : Infinite α :=
  Infinite.of_surjective _ (eqv α).surjective

/-- A type equivalent to `ℕ` is denumerable. -/
def mk' {α} (e : α ≃ ℕ) : Denumerable α where
  encode := e
  decode := some ∘ e.symm
  encodek _ := congr_arg some (e.symm_apply_apply _)
  decode_inv _ := ⟨_, rfl, e.apply_symm_apply _⟩
#align denumerable.mk' Denumerable.mk'

/-- Denumerability is conserved by equivalences. This is transitivity of equivalence the denumerable
way. -/
def ofEquiv (α) {β} [Denumerable α] (e : β ≃ α) : Denumerable β :=
  { Encodable.ofEquiv _ e with
    decode_inv := fun n => by
      -- Porting note: replaced `simp`
      simp_rw [Option.mem_def, decode_ofEquiv e, encode_ofEquiv e, decode_eq_ofNat,
        Option.map_some', Option.some_inj, exists_eq_left', Equiv.apply_symm_apply,
        Denumerable.encode_ofNat] }
#align denumerable.of_equiv Denumerable.ofEquiv

@[simp]
theorem ofEquiv_ofNat (α) {β} [Denumerable α] (e : β ≃ α) (n) :
    @ofNat β (ofEquiv _ e) n = e.symm (ofNat α n) := by
  -- Porting note: added `letI`
  letI := ofEquiv _ e
  -- ⊢ ofNat β n = ↑e.symm (ofNat α n)
  refine ofNat_of_decode ?_
  -- ⊢ decode n = some (↑e.symm (ofNat α n))
  rw [decode_ofEquiv e]
  -- ⊢ Option.map (↑e.symm) (decode n) = some (↑e.symm (ofNat α n))
  simp
  -- 🎉 no goals
#align denumerable.of_equiv_of_nat Denumerable.ofEquiv_ofNat

/-- All denumerable types are equivalent. -/
def equiv₂ (α β) [Denumerable α] [Denumerable β] : α ≃ β :=
  (eqv α).trans (eqv β).symm
#align denumerable.equiv₂ Denumerable.equiv₂

instance nat : Denumerable ℕ :=
  ⟨fun _ => ⟨_, rfl, rfl⟩⟩
#align denumerable.nat Denumerable.nat

@[simp]
theorem ofNat_nat (n) : ofNat ℕ n = n :=
  rfl
#align denumerable.of_nat_nat Denumerable.ofNat_nat

/-- If `α` is denumerable, then so is `Option α`. -/
instance option : Denumerable (Option α) :=
  ⟨fun n => by
    cases n
    -- ⊢ ∃ a, a ∈ decode zero ∧ encode a = zero
    case zero =>
      refine' ⟨none, _, encode_none⟩
      rw [decode_option_zero, Option.mem_def]
    case succ n =>
      refine' ⟨some (ofNat α n), _, _⟩
      · rw [decode_option_succ, decode_eq_ofNat, Option.map_some', Option.mem_def]
      rw [encode_some, encode_ofNat]⟩
#align denumerable.option Denumerable.option

set_option linter.deprecated false in
/-- If `α` and `β` are denumerable, then so is their sum. -/
instance sum : Denumerable (Sum α β) :=
  ⟨fun n => by
    suffices ∃ a ∈ @decodeSum α β _ _ n, encodeSum a = bit (bodd n) (div2 n) by simpa [bit_decomp]
    -- ⊢ ∃ a, a ∈ decodeSum n ∧ encodeSum a = bit (bodd n) (div2 n)
    simp only [decodeSum, boddDiv2_eq, decode_eq_ofNat, Option.some.injEq, Option.map_some',
      Option.mem_def, Sum.exists]
    cases bodd n <;> simp [decodeSum, bit, encodeSum, bit0_eq_two_mul, bit1]⟩
                     -- 🎉 no goals
                     -- 🎉 no goals
#align denumerable.sum Denumerable.sum

section Sigma

variable {γ : α → Type*} [∀ a, Denumerable (γ a)]

/-- A denumerable collection of denumerable types is denumerable. -/
instance sigma : Denumerable (Sigma γ) :=
  ⟨fun n => by simp [decodeSigma]⟩
               -- 🎉 no goals
#align denumerable.sigma Denumerable.sigma

@[simp]
theorem sigma_ofNat_val (n : ℕ) :
    ofNat (Sigma γ) n = ⟨ofNat α (unpair n).1, ofNat (γ _) (unpair n).2⟩ :=
  Option.some.inj <| by rw [← decode_eq_ofNat, decode_sigma_val]; simp
                        -- ⊢ (Option.bind (decode (unpair n).fst) fun a => Option.map (Sigma.mk a) (decod …
                                                                  -- 🎉 no goals
#align denumerable.sigma_of_nat_val Denumerable.sigma_ofNat_val

end Sigma

/-- If `α` and `β` are denumerable, then so is their product. -/
instance prod : Denumerable (α × β) :=
  ofEquiv _ (Equiv.sigmaEquivProd α β).symm
#align denumerable.prod Denumerable.prod

-- Porting note: removed @[simp] - simp can prove it
theorem prod_ofNat_val (n : ℕ) : ofNat (α × β) n = (ofNat α (unpair n).1, ofNat β (unpair n).2) :=
  by simp
     -- 🎉 no goals
#align denumerable.prod_of_nat_val Denumerable.prod_ofNat_val

@[simp]
theorem prod_nat_ofNat : ofNat (ℕ × ℕ) = unpair := by funext; simp
                                                      -- ⊢ ofNat (ℕ × ℕ) x✝ = unpair x✝
                                                              -- 🎉 no goals
#align denumerable.prod_nat_of_nat Denumerable.prod_nat_ofNat

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

theorem exists_succ (x : s) : ∃ n, (x : ℕ) + n + 1 ∈ s :=
  _root_.by_contradiction fun h =>
    have : ∀ (a : ℕ) (_ : a ∈ s), a < succ x := fun a ha =>
      lt_of_not_ge fun hax => h ⟨a - (x + 1), by rwa [add_right_comm, add_tsub_cancel_of_le hax]⟩
                                                 -- 🎉 no goals
    Fintype.false
      ⟨(((Multiset.range (succ x)).filter (· ∈ s)).pmap
            (fun (y : ℕ) (hy : y ∈ s) => Subtype.mk y hy)
            (by simp [-Multiset.range_succ])).toFinset,
                -- 🎉 no goals
        by simpa [Subtype.ext_iff_val, Multiset.mem_filter, -Multiset.range_succ] ⟩
           -- 🎉 no goals
#align nat.subtype.exists_succ Nat.Subtype.exists_succ

end Classical

variable [DecidablePred (· ∈ s)]

/-- Returns the next natural in a set, according to the usual ordering of `ℕ`. -/
def succ (x : s) : s :=
  have h : ∃ m, (x : ℕ) + m + 1 ∈ s := exists_succ x
  ⟨↑x + Nat.find h + 1, Nat.find_spec h⟩
#align nat.subtype.succ Nat.Subtype.succ

theorem succ_le_of_lt {x y : s} (h : y < x) : succ y ≤ x :=
  have hx : ∃ m, (y : ℕ) + m + 1 ∈ s := exists_succ _
  let ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
  have : Nat.find hx ≤ k := Nat.find_min' _ (hk ▸ x.2)
  show (y : ℕ) + Nat.find hx + 1 ≤ x by
    rw [hk]
    -- ⊢ ↑y + Nat.find hx + 1 ≤ ↑y + k + 1
    exact add_le_add_right (add_le_add_left this _) _
    -- 🎉 no goals
#align nat.subtype.succ_le_of_lt Nat.Subtype.succ_le_of_lt

theorem le_succ_of_forall_lt_le {x y : s} (h : ∀ z < x, z ≤ y) : x ≤ succ y :=
  have hx : ∃ m, (y : ℕ) + m + 1 ∈ s := exists_succ _
  show (x : ℕ) ≤ (y : ℕ) + Nat.find hx + 1 from
    le_of_not_gt fun hxy =>
      (h ⟨_, Nat.find_spec hx⟩ hxy).not_lt <|
        calc
          (y : ℕ) ≤ (y : ℕ) + Nat.find hx := le_add_of_nonneg_right (Nat.zero_le _)
          _ < (y : ℕ) + Nat.find hx + 1 := Nat.lt_succ_self _
#align nat.subtype.le_succ_of_forall_lt_le Nat.Subtype.le_succ_of_forall_lt_le

theorem lt_succ_self (x : s) : x < succ x :=
  calc
    -- Porting note: replaced `x + _`, added type annotations
    (x : ℕ) ≤ (x + Nat.find (exists_succ x): ℕ) := le_self_add
    _ < (succ x : ℕ) := Nat.lt_succ_self (x + _)
#align nat.subtype.lt_succ_self Nat.Subtype.lt_succ_self

theorem lt_succ_iff_le {x y : s} : x < succ y ↔ x ≤ y :=
  ⟨fun h => le_of_not_gt fun h' => not_le_of_gt h (succ_le_of_lt h'), fun h =>
    lt_of_le_of_lt h (lt_succ_self _)⟩
#align nat.subtype.lt_succ_iff_le Nat.Subtype.lt_succ_iff_le

/-- Returns the `n`-th element of a set, according to the usual ordering of `ℕ`. -/
def ofNat (s : Set ℕ) [DecidablePred (· ∈ s)] [Infinite s] : ℕ → s
  | 0 => ⊥
  | n + 1 => succ (ofNat s n)
#align nat.subtype.of_nat Nat.Subtype.ofNat

theorem ofNat_surjective_aux : ∀ {x : ℕ} (hx : x ∈ s), ∃ n, ofNat s n = ⟨x, hx⟩
  | x => fun hx => by
    set t : List s :=
      ((List.range x).filter fun y => y ∈ s).pmap
        (fun (y : ℕ) (hy : y ∈ s) => ⟨y, hy⟩)
        (by intros a ha; simpa using (List.mem_filter.mp ha).2) with ht
    have hmt : ∀ {y : s}, y ∈ t ↔ y < ⟨x, hx⟩ := by
      simp [List.mem_filter, Subtype.ext_iff_val, ht]
    have wf : ∀ m : s, List.maximum t = m → ↑m < x := fun m hmax => by
      simpa using hmt.mp (List.maximum_mem hmax)
    cases' hmax : List.maximum t with m
    -- ⊢ ∃ n, ofNat s n = { val := x✝, property := hx }
    · refine ⟨0, le_antisymm bot_le (le_of_not_gt fun h => List.not_mem_nil (⊥ : s) ?_)⟩
      -- ⊢ ⊥ ∈ []
      rwa [← List.maximum_eq_none.1 hmax, hmt]
      -- 🎉 no goals
    cases' ofNat_surjective_aux m.2 with a ha
    -- ⊢ ∃ n, ofNat s n = { val := x✝, property := hx }
    refine ⟨a + 1, le_antisymm ?_ ?_⟩ <;> rw [ofNat]
    -- ⊢ ofNat s (a + 1) ≤ { val := x✝, property := hx }
                                          -- ⊢ succ (ofNat s a) ≤ { val := x✝, property := hx }
                                          -- ⊢ { val := x✝, property := hx } ≤ succ (ofNat s a)
    · refine succ_le_of_lt ?_
      -- ⊢ ofNat s a < { val := x✝, property := hx }
      rw [ha]
      -- ⊢ { val := ↑m, property := (_ : ↑m ∈ s) } < { val := x✝, property := hx }
      exact wf _ hmax
      -- 🎉 no goals
    · refine le_succ_of_forall_lt_le fun z hz => ?_
      -- ⊢ z ≤ ofNat s a
      rw [ha]
      -- ⊢ z ≤ { val := ↑m, property := (_ : ↑m ∈ s) }
      cases m
      -- ⊢ z ≤ { val := ↑{ val := val✝, property := property✝ }, property := (_ : ↑{ va …
      exact List.le_maximum_of_mem (hmt.2 hz) hmax
      -- 🎉 no goals
decreasing_by
  tauto
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
#align nat.subtype.of_nat_surjective_aux Nat.Subtype.ofNat_surjective_aux

theorem ofNat_surjective : Surjective (ofNat s) := fun ⟨_, hx⟩ => ofNat_surjective_aux hx
#align nat.subtype.of_nat_surjective Nat.Subtype.ofNat_surjective

@[simp]
theorem ofNat_range : Set.range (ofNat s) = Set.univ :=
  ofNat_surjective.range_eq
#align nat.subtype.of_nat_range Nat.Subtype.ofNat_range

@[simp]
theorem coe_comp_ofNat_range : Set.range ((↑) ∘ ofNat s : ℕ → ℕ) = s := by
  rw [Set.range_comp Subtype.val, ofNat_range, Set.image_univ, Subtype.range_coe]
  -- 🎉 no goals
#align nat.subtype.coe_comp_of_nat_range Nat.Subtype.coe_comp_ofNat_range

private def toFunAux (x : s) : ℕ :=
  (List.range x).countP (· ∈ s)

private theorem toFunAux_eq (x : s) : toFunAux x = ((Finset.range x).filter (· ∈ s)).card := by
  rw [toFunAux, List.countP_eq_length_filter]
  -- ⊢ List.length (List.filter (fun x => decide (x ∈ s)) (List.range ↑x)) = Finset …
  rfl
  -- 🎉 no goals

open Finset

private theorem right_inverse_aux : ∀ n, toFunAux (ofNat s n) = n
  | 0 => by
    rw [toFunAux_eq, card_eq_zero, eq_empty_iff_forall_not_mem]
    -- ⊢ ∀ (x : ℕ), ¬x ∈ filter (fun x => x ∈ s) (range ↑(ofNat s 0))
    rintro n hn
    -- ⊢ False
    rw [mem_filter, ofNat, mem_range] at hn
    -- ⊢ False
    exact bot_le.not_lt (show (⟨n, hn.2⟩ : s) < ⊥ from hn.1)
    -- 🎉 no goals
  | n + 1 => by
    have ih : toFunAux (ofNat s n) = n := right_inverse_aux n
    -- ⊢ Nat.Subtype.toFunAux (ofNat s (n + 1)) = n + 1
    have h₁ : (ofNat s n : ℕ) ∉ (range (ofNat s n)).filter (· ∈ s) := by simp
    -- ⊢ Nat.Subtype.toFunAux (ofNat s (n + 1)) = n + 1
    have h₂ : (range (succ (ofNat s n))).filter (· ∈ s) =
        insert ↑(ofNat s n) ((range (ofNat s n)).filter (· ∈ s)) := by
      simp only [Finset.ext_iff, mem_insert, mem_range, mem_filter]
      exact fun m =>
        ⟨fun h => by
          simp only [h.2, and_true_iff]
          exact Or.symm (lt_or_eq_of_le ((@lt_succ_iff_le _ _ _ ⟨m, h.2⟩ _).1 h.1)),
         fun h =>
          h.elim (fun h => h.symm ▸ ⟨lt_succ_self _, (ofNat s n).prop⟩) fun h =>
            ⟨h.1.trans (lt_succ_self _), h.2⟩⟩
    simp only [toFunAux_eq, ofNat, range_succ] at ih ⊢
    -- ⊢ card (filter (fun x => x ∈ s) (range ↑(succ (ofNat s (Nat.add n 0))))) = n + 1
    conv =>
      rhs
      rw [← ih, ← card_insert_of_not_mem h₁, ← h₂]

/-- Any infinite set of naturals is denumerable. -/
def denumerable (s : Set ℕ) [DecidablePred (· ∈ s)] [Infinite s] : Denumerable s :=
  Denumerable.ofEquiv ℕ
    { toFun := toFunAux
      invFun := ofNat s
      left_inv := leftInverse_of_surjective_of_rightInverse ofNat_surjective right_inverse_aux
      right_inv := right_inverse_aux }
#align nat.subtype.denumerable Nat.Subtype.denumerable

end Nat.Subtype

namespace Denumerable

open Encodable

/-- An infinite encodable type is denumerable. -/
def ofEncodableOfInfinite (α : Type*) [Encodable α] [Infinite α] : Denumerable α := by
  letI := @decidableRangeEncode α _
  -- ⊢ Denumerable α
  letI : Infinite (Set.range (@encode α _)) :=
    Infinite.of_injective _ (Equiv.ofInjective _ encode_injective).injective
  letI := Nat.Subtype.denumerable (Set.range (@encode α _))
  -- ⊢ Denumerable α
  exact Denumerable.ofEquiv (Set.range (@encode α _)) (equivRangeEncode α)
  -- 🎉 no goals
#align denumerable.of_encodable_of_infinite Denumerable.ofEncodableOfInfinite

end Denumerable

/-- See also `nonempty_encodable`, `nonempty_fintype`. -/
theorem nonempty_denumerable (α : Type*) [Countable α] [Infinite α] : Nonempty (Denumerable α) :=
  (nonempty_encodable α).map fun h => @Denumerable.ofEncodableOfInfinite _ h _
#align nonempty_denumerable nonempty_denumerable

theorem nonempty_denumerable_iff {α : Type*} :
    Nonempty (Denumerable α) ↔ Countable α ∧ Infinite α :=
  ⟨fun ⟨_⟩ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ nonempty_denumerable _⟩

instance nonempty_equiv_of_countable [Countable α] [Infinite α] [Countable β] [Infinite β] :
    Nonempty (α ≃ β) := by
  cases nonempty_denumerable α
  -- ⊢ Nonempty (α ≃ β)
  cases nonempty_denumerable β
  -- ⊢ Nonempty (α ≃ β)
  exact ⟨(Denumerable.eqv _).trans (Denumerable.eqv _).symm⟩
  -- 🎉 no goals
#align nonempty_equiv_of_countable nonempty_equiv_of_countable
