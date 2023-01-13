/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

! This file was ported from Lean 3 source module logic.encodable.basic
! leanprover-community/mathlib commit 7c523cb78f4153682c2929e3006c863bfef463d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Equiv.Nat
import Mathbin.Data.Pnat.Basic
import Mathbin.Order.Directed
import Mathbin.Data.Countable.Defs
import Mathbin.Order.RelIso.Basic
import Mathbin.Data.Fin.Basic

/-!
# Encodable types

This file defines encodable (constructively countable) types as a typeclass.
This is used to provide explicit encode/decode functions from and to `ℕ`, with the information that
those functions are inverses of each other.
The difference with `denumerable` is that finite types are encodable. For infinite types,
`encodable` and `denumerable` agree.

## Main declarations

* `encodable α`: States that there exists an explicit encoding function `encode : α → ℕ` with a
  partial inverse `decode : ℕ → option α`.
* `decode₂`: Version of `decode` that is equal to `none` outside of the range of `encode`. Useful as
  we do not require this in the definition of `decode`.
* `ulower α`: Any encodable type has an equivalent type living in the lowest universe, namely a
  subtype of `ℕ`. `ulower α` finds it.

## Implementation notes

The point of asking for an explicit partial inverse `decode : ℕ → option α` to `encode : α → ℕ` is
to make the range of `encode` decidable even when the finiteness of `α` is not.
-/


open Option List Nat Function

/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4: #[`decode] [] -/
/-- Constructively countable type. Made from an explicit injection `encode : α → ℕ` and a partial
inverse `decode : ℕ → option α`. Note that finite types *are* countable. See `denumerable` if you
wish to enforce infiniteness. -/
class Encodable (α : Type _) where
  encode : α → ℕ
  decode : ℕ → Option α
  encodek : ∀ a, decode (encode a) = some a
#align encodable Encodable

attribute [simp] Encodable.encodek

namespace Encodable

variable {α : Type _} {β : Type _}

universe u

theorem encode_injective [Encodable α] : Function.Injective (@encode α _)
  | x, y, e => Option.some.inj <| by rw [← encodek, e, encodek]
#align encodable.encode_injective Encodable.encode_injective

@[simp]
theorem encode_inj [Encodable α] {a b : α} : encode a = encode b ↔ a = b :=
  encode_injective.eq_iff
#align encodable.encode_inj Encodable.encode_inj

-- The priority of the instance below is less than the priorities of `subtype.countable`
-- and `quotient.countable`
instance (priority := 400) [Encodable α] : Countable α :=
  encode_injective.Countable

theorem surjective_decode_iget (α : Type _) [Encodable α] [Inhabited α] :
    Surjective fun n => (Encodable.decode α n).iget := fun x =>
  ⟨Encodable.encode x, by simp_rw [Encodable.encodek]⟩
#align encodable.surjective_decode_iget Encodable.surjective_decode_iget

/-- An encodable type has decidable equality. Not set as an instance because this is usually not the
best way to infer decidability. -/
def decidableEqOfEncodable (α) [Encodable α] : DecidableEq α
  | a, b => decidable_of_iff _ encode_inj
#align encodable.decidable_eq_of_encodable Encodable.decidableEqOfEncodable

/-- If `α` is encodable and there is an injection `f : β → α`, then `β` is encodable as well. -/
def ofLeftInjection [Encodable α] (f : β → α) (finv : α → Option β)
    (linv : ∀ b, finv (f b) = some b) : Encodable β :=
  ⟨fun b => encode (f b), fun n => (decode α n).bind finv, fun b => by
    simp [Encodable.encodek, linv]⟩
#align encodable.of_left_injection Encodable.ofLeftInjection

/-- If `α` is encodable and `f : β → α` is invertible, then `β` is encodable as well. -/
def ofLeftInverse [Encodable α] (f : β → α) (finv : α → β) (linv : ∀ b, finv (f b) = b) :
    Encodable β :=
  ofLeftInjection f (some ∘ finv) fun b => congr_arg some (linv b)
#align encodable.of_left_inverse Encodable.ofLeftInverse

/-- Encodability is preserved by equivalence. -/
def ofEquiv (α) [Encodable α] (e : β ≃ α) : Encodable β :=
  ofLeftInverse e e.symm e.left_inv
#align encodable.of_equiv Encodable.ofEquiv

@[simp]
theorem encode_of_equiv {α β} [Encodable α] (e : β ≃ α) (b : β) :
    @encode _ (ofEquiv _ e) b = encode (e b) :=
  rfl
#align encodable.encode_of_equiv Encodable.encode_of_equiv

@[simp]
theorem decode_of_equiv {α β} [Encodable α] (e : β ≃ α) (n : ℕ) :
    @decode _ (ofEquiv _ e) n = (decode α n).map e.symm :=
  rfl
#align encodable.decode_of_equiv Encodable.decode_of_equiv

instance Nat.encodable : Encodable ℕ :=
  ⟨id, some, fun a => rfl⟩
#align nat.encodable Nat.encodable

@[simp]
theorem encode_nat (n : ℕ) : encode n = n :=
  rfl
#align encodable.encode_nat Encodable.encode_nat

@[simp]
theorem decode_nat (n : ℕ) : decode ℕ n = some n :=
  rfl
#align encodable.decode_nat Encodable.decode_nat

instance (priority := 100) IsEmpty.toEncodable [IsEmpty α] : Encodable α :=
  ⟨isEmptyElim, fun n => none, isEmptyElim⟩
#align is_empty.to_encodable IsEmpty.toEncodable

instance PUnit.encodable : Encodable PUnit :=
  ⟨fun _ => 0, fun n => Nat.casesOn n (some PUnit.unit) fun _ => none, fun _ => by simp⟩
#align punit.encodable PUnit.encodable

@[simp]
theorem encode_star : encode PUnit.unit = 0 :=
  rfl
#align encodable.encode_star Encodable.encode_star

@[simp]
theorem decode_unit_zero : decode PUnit 0 = some PUnit.unit :=
  rfl
#align encodable.decode_unit_zero Encodable.decode_unit_zero

@[simp]
theorem decode_unit_succ (n) : decode PUnit (succ n) = none :=
  rfl
#align encodable.decode_unit_succ Encodable.decode_unit_succ

/-- If `α` is encodable, then so is `option α`. -/
instance Option.encodable {α : Type _} [h : Encodable α] : Encodable (Option α) :=
  ⟨fun o => Option.casesOn o Nat.zero fun a => succ (encode a), fun n =>
    Nat.casesOn n (some none) fun m => (decode α m).map some, fun o => by
    cases o <;> dsimp <;> simp [encodek, Nat.succ_ne_zero]⟩
#align option.encodable Option.encodable

@[simp]
theorem encode_none [Encodable α] : encode (@none α) = 0 :=
  rfl
#align encodable.encode_none Encodable.encode_none

@[simp]
theorem encode_some [Encodable α] (a : α) : encode (some a) = succ (encode a) :=
  rfl
#align encodable.encode_some Encodable.encode_some

@[simp]
theorem decode_option_zero [Encodable α] : decode (Option α) 0 = some none :=
  rfl
#align encodable.decode_option_zero Encodable.decode_option_zero

@[simp]
theorem decode_option_succ [Encodable α] (n) : decode (Option α) (succ n) = (decode α n).map some :=
  rfl
#align encodable.decode_option_succ Encodable.decode_option_succ

/-- Failsafe variant of `decode`. `decode₂ α n` returns the preimage of `n` under `encode` if it
exists, and returns `none` if it doesn't. This requirement could be imposed directly on `decode` but
is not to help make the definition easier to use. -/
def decode₂ (α) [Encodable α] (n : ℕ) : Option α :=
  (decode α n).bind (Option.guard fun a => encode a = n)
#align encodable.decode₂ Encodable.decode₂

theorem mem_decode₂' [Encodable α] {n : ℕ} {a : α} :
    a ∈ decode₂ α n ↔ a ∈ decode α n ∧ encode a = n := by
  simp [decode₂] <;> exact ⟨fun ⟨_, h₁, rfl, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨_, h₁, rfl, h₂⟩⟩
#align encodable.mem_decode₂' Encodable.mem_decode₂'

theorem mem_decode₂ [Encodable α] {n : ℕ} {a : α} : a ∈ decode₂ α n ↔ encode a = n :=
  mem_decode₂'.trans (and_iff_right_of_imp fun e => e ▸ encodek _)
#align encodable.mem_decode₂ Encodable.mem_decode₂

theorem decode₂_eq_some [Encodable α] {n : ℕ} {a : α} : decode₂ α n = some a ↔ encode a = n :=
  mem_decode₂
#align encodable.decode₂_eq_some Encodable.decode₂_eq_some

@[simp]
theorem decode₂_encode [Encodable α] (a : α) : decode₂ α (encode a) = some a :=
  by
  ext
  simp [mem_decode₂, eq_comm]
#align encodable.decode₂_encode Encodable.decode₂_encode

theorem decode₂_ne_none_iff [Encodable α] {n : ℕ} :
    decode₂ α n ≠ none ↔ n ∈ Set.range (encode : α → ℕ) := by
  simp_rw [Set.range, Set.mem_setOf_eq, Ne.def, Option.eq_none_iff_forall_not_mem,
    Encodable.mem_decode₂, not_forall, not_not]
#align encodable.decode₂_ne_none_iff Encodable.decode₂_ne_none_iff

theorem decode₂_is_partial_inv [Encodable α] : IsPartialInv encode (decode₂ α) := fun a n =>
  mem_decode₂
#align encodable.decode₂_is_partial_inv Encodable.decode₂_is_partial_inv

theorem decode₂_inj [Encodable α] {n : ℕ} {a₁ a₂ : α} (h₁ : a₁ ∈ decode₂ α n)
    (h₂ : a₂ ∈ decode₂ α n) : a₁ = a₂ :=
  encode_injective <| (mem_decode₂.1 h₁).trans (mem_decode₂.1 h₂).symm
#align encodable.decode₂_inj Encodable.decode₂_inj

theorem encodek₂ [Encodable α] (a : α) : decode₂ α (encode a) = some a :=
  mem_decode₂.2 rfl
#align encodable.encodek₂ Encodable.encodek₂

/-- The encoding function has decidable range. -/
def decidableRangeEncode (α : Type _) [Encodable α] : DecidablePred (· ∈ Set.range (@encode α _)) :=
  fun x =>
  decidable_of_iff (Option.isSome (decode₂ α x))
    ⟨fun h => ⟨Option.get h, by rw [← decode₂_is_partial_inv (Option.get h), Option.some_get]⟩,
      fun ⟨n, hn⟩ => by rw [← hn, encodek₂] <;> exact rfl⟩
#align encodable.decidable_range_encode Encodable.decidableRangeEncode

/-- An encodable type is equivalent to the range of its encoding function. -/
def equivRangeEncode (α : Type _) [Encodable α] : α ≃ Set.range (@encode α _)
    where
  toFun := fun a : α => ⟨encode a, Set.mem_range_self _⟩
  invFun n :=
    Option.get
      (show isSome (decode₂ α n.1) by cases' n.2 with x hx <;> rw [← hx, encodek₂] <;> exact rfl)
  left_inv a := by dsimp <;> rw [← Option.some_inj, Option.some_get, encodek₂]
  right_inv := fun ⟨n, x, hx⟩ => by
    apply Subtype.eq
    dsimp
    conv =>
      rhs
      rw [← hx]
    rw [encode_injective.eq_iff, ← Option.some_inj, Option.some_get, ← hx, encodek₂]
#align encodable.equiv_range_encode Encodable.equivRangeEncode

/-- A type with unique element is encodable. This is not an instance to avoid diamonds. -/
def Unique.encodable [Unique α] : Encodable α :=
  ⟨fun _ => 0, fun _ => some default, Unique.forall_iff.2 rfl⟩
#align unique.encodable Unique.encodable

section Sum

variable [Encodable α] [Encodable β]

/-- Explicit encoding function for the sum of two encodable types. -/
def encodeSum : Sum α β → ℕ
  | Sum.inl a => bit0 <| encode a
  | Sum.inr b => bit1 <| encode b
#align encodable.encode_sum Encodable.encodeSum

/-- Explicit decoding function for the sum of two encodable types. -/
def decodeSum (n : ℕ) : Option (Sum α β) :=
  match boddDiv2 n with
  | (ff, m) => (decode α m).map Sum.inl
  | (tt, m) => (decode β m).map Sum.inr
#align encodable.decode_sum Encodable.decodeSum

/-- If `α` and `β` are encodable, then so is their sum. -/
instance Sum.encodable : Encodable (Sum α β) :=
  ⟨encodeSum, decodeSum, fun s => by cases s <;> simp [encode_sum, decode_sum, encodek] <;> rfl⟩
#align sum.encodable Sum.encodable

@[simp]
theorem encode_inl (a : α) : @encode (Sum α β) _ (Sum.inl a) = bit0 (encode a) :=
  rfl
#align encodable.encode_inl Encodable.encode_inl

@[simp]
theorem encode_inr (b : β) : @encode (Sum α β) _ (Sum.inr b) = bit1 (encode b) :=
  rfl
#align encodable.encode_inr Encodable.encode_inr

@[simp]
theorem decode_sum_val (n : ℕ) : decode (Sum α β) n = decodeSum n :=
  rfl
#align encodable.decode_sum_val Encodable.decode_sum_val

end Sum

instance Bool.encodable : Encodable Bool :=
  ofEquiv (Sum Unit Unit) Equiv.boolEquivPUnitSumPUnit
#align bool.encodable Bool.encodable

@[simp]
theorem encode_tt : encode true = 1 :=
  rfl
#align encodable.encode_tt Encodable.encode_tt

@[simp]
theorem encode_ff : encode false = 0 :=
  rfl
#align encodable.encode_ff Encodable.encode_ff

@[simp]
theorem decode_zero : decode Bool 0 = some false :=
  rfl
#align encodable.decode_zero Encodable.decode_zero

@[simp]
theorem decode_one : decode Bool 1 = some true :=
  rfl
#align encodable.decode_one Encodable.decode_one

theorem decode_ge_two (n) (h : 2 ≤ n) : decode Bool n = none :=
  by
  suffices decode_sum n = none by
    change (decode_sum n).map _ = none
    rw [this]
    rfl
  have : 1 ≤ div2 n := by
    rw [div2_val, Nat.le_div_iff_mul_le]
    exacts[h, by decide]
  cases' exists_eq_succ_of_ne_zero (ne_of_gt this) with m e
  simp [decode_sum] <;> cases bodd n <;> simp [decode_sum] <;> rw [e] <;> rfl
#align encodable.decode_ge_two Encodable.decode_ge_two

noncomputable instance PropCat.encodable : Encodable Prop :=
  ofEquiv Bool Equiv.propEquivBool
#align Prop.encodable PropCat.encodable

section Sigma

variable {γ : α → Type _} [Encodable α] [∀ a, Encodable (γ a)]

/-- Explicit encoding function for `sigma γ` -/
def encodeSigma : Sigma γ → ℕ
  | ⟨a, b⟩ => mkpair (encode a) (encode b)
#align encodable.encode_sigma Encodable.encodeSigma

/-- Explicit decoding function for `sigma γ` -/
def decodeSigma (n : ℕ) : Option (Sigma γ) :=
  let (n₁, n₂) := unpair n
  (decode α n₁).bind fun a => (decode (γ a) n₂).map <| Sigma.mk a
#align encodable.decode_sigma Encodable.decodeSigma

instance Sigma.encodable : Encodable (Sigma γ) :=
  ⟨encodeSigma, decodeSigma, fun ⟨a, b⟩ => by
    simp [encode_sigma, decode_sigma, unpair_mkpair, encodek]⟩
#align sigma.encodable Sigma.encodable

@[simp]
theorem decode_sigma_val (n : ℕ) :
    decode (Sigma γ) n =
      (decode α n.unpair.1).bind fun a => (decode (γ a) n.unpair.2).map <| Sigma.mk a :=
  show DecodeSigma._match1 _ = _ by cases n.unpair <;> rfl
#align encodable.decode_sigma_val Encodable.decode_sigma_val

@[simp]
theorem encode_sigma_val (a b) : @encode (Sigma γ) _ ⟨a, b⟩ = mkpair (encode a) (encode b) :=
  rfl
#align encodable.encode_sigma_val Encodable.encode_sigma_val

end Sigma

section Prod

variable [Encodable α] [Encodable β]

/-- If `α` and `β` are encodable, then so is their product. -/
instance Prod.encodable : Encodable (α × β) :=
  ofEquiv _ (Equiv.sigmaEquivProd α β).symm
#align prod.encodable Prod.encodable

@[simp]
theorem decode_prod_val (n : ℕ) :
    decode (α × β) n = (decode α n.unpair.1).bind fun a => (decode β n.unpair.2).map <| Prod.mk a :=
  show (decode (Sigma fun _ => β) n).map (Equiv.sigmaEquivProd α β) = _ by
    simp <;> cases decode α n.unpair.1 <;> simp <;> cases decode β n.unpair.2 <;> rfl
#align encodable.decode_prod_val Encodable.decode_prod_val

@[simp]
theorem encode_prod_val (a b) : @encode (α × β) _ (a, b) = mkpair (encode a) (encode b) :=
  rfl
#align encodable.encode_prod_val Encodable.encode_prod_val

end Prod

section Subtype

open Subtype Decidable

variable {P : α → Prop} [encA : Encodable α] [decP : DecidablePred P]

include encA

/-- Explicit encoding function for a decidable subtype of an encodable type -/
def encodeSubtype : { a : α // P a } → ℕ
  | ⟨v, h⟩ => encode v
#align encodable.encode_subtype Encodable.encodeSubtype

include decP

/-- Explicit decoding function for a decidable subtype of an encodable type -/
def decodeSubtype (v : ℕ) : Option { a : α // P a } :=
  (decode α v).bind fun a => if h : P a then some ⟨a, h⟩ else none
#align encodable.decode_subtype Encodable.decodeSubtype

/-- A decidable subtype of an encodable type is encodable. -/
instance Subtype.encodable : Encodable { a : α // P a } :=
  ⟨encodeSubtype, decodeSubtype, fun ⟨v, h⟩ => by simp [encode_subtype, decode_subtype, encodek, h]⟩
#align subtype.encodable Subtype.encodable

theorem Subtype.encode_eq (a : Subtype P) : encode a = encode a.val := by cases a <;> rfl
#align encodable.subtype.encode_eq Encodable.Subtype.encode_eq

end Subtype

instance Fin.encodable (n) : Encodable (Fin n) :=
  ofEquiv _ Fin.equivSubtype
#align fin.encodable Fin.encodable

instance Int.encodable : Encodable ℤ :=
  ofEquiv _ Equiv.intEquivNat
#align int.encodable Int.encodable

instance PNat.encodable : Encodable ℕ+ :=
  ofEquiv _ Equiv.pnatEquivNat
#align pnat.encodable PNat.encodable

/-- The lift of an encodable type is encodable. -/
instance ULift.encodable [Encodable α] : Encodable (ULift α) :=
  ofEquiv _ Equiv.ulift
#align ulift.encodable ULift.encodable

/-- The lift of an encodable type is encodable. -/
instance PLift.encodable [Encodable α] : Encodable (PLift α) :=
  ofEquiv _ Equiv.plift
#align plift.encodable PLift.encodable

/-- If `β` is encodable and there is an injection `f : α → β`, then `α` is encodable as well. -/
noncomputable def ofInj [Encodable β] (f : α → β) (hf : Injective f) : Encodable α :=
  ofLeftInjection f (partialInv f) fun x => (partialInv_of_injective hf _ _).2 rfl
#align encodable.of_inj Encodable.ofInj

/-- If `α` is countable, then it has a (non-canonical) `encodable` structure. -/
noncomputable def ofCountable (α : Type _) [Countable α] : Encodable α :=
  Nonempty.some <|
    let ⟨f, hf⟩ := exists_injective_nat α
    ⟨ofInj f hf⟩
#align encodable.of_countable Encodable.ofCountable

@[simp]
theorem nonempty_encodable : Nonempty (Encodable α) ↔ Countable α :=
  ⟨fun ⟨h⟩ => @Encodable.countable α h, fun h => ⟨@ofCountable _ h⟩⟩
#align encodable.nonempty_encodable Encodable.nonempty_encodable

end Encodable

/-- See also `nonempty_fintype`, `nonempty_denumerable`. -/
theorem nonempty_encodable (α : Type _) [Countable α] : Nonempty (Encodable α) :=
  ⟨Encodable.ofCountable _⟩
#align nonempty_encodable nonempty_encodable

instance : Countable ℕ+ :=
  Subtype.countable

-- short-circuit instance search
section Ulower

attribute [local instance] Encodable.decidableRangeEncode

/-- `ulower α : Type` is an equivalent type in the lowest universe, given `encodable α`. -/
def Ulower (α : Type _) [Encodable α] : Type :=
  Set.range (Encodable.encode : α → ℕ)deriving DecidableEq, Encodable
#align ulower Ulower

end Ulower

namespace Ulower

variable (α : Type _) [Encodable α]

/-- The equivalence between the encodable type `α` and `ulower α : Type`. -/
def equiv : α ≃ Ulower α :=
  Encodable.equivRangeEncode α
#align ulower.equiv Ulower.equiv

variable {α}

/-- Lowers an `a : α` into `ulower α`. -/
def down (a : α) : Ulower α :=
  equiv α a
#align ulower.down Ulower.down

instance [Inhabited α] : Inhabited (Ulower α) :=
  ⟨down default⟩

/-- Lifts an `a : ulower α` into `α`. -/
def up (a : Ulower α) : α :=
  (equiv α).symm a
#align ulower.up Ulower.up

@[simp]
theorem down_up {a : Ulower α} : down a.up = a :=
  Equiv.right_inv _ _
#align ulower.down_up Ulower.down_up

@[simp]
theorem up_down {a : α} : (down a).up = a :=
  Equiv.left_inv _ _
#align ulower.up_down Ulower.up_down

@[simp]
theorem up_eq_up {a b : Ulower α} : a.up = b.up ↔ a = b :=
  Equiv.apply_eq_iff_eq _
#align ulower.up_eq_up Ulower.up_eq_up

@[simp]
theorem down_eq_down {a b : α} : down a = down b ↔ a = b :=
  Equiv.apply_eq_iff_eq _
#align ulower.down_eq_down Ulower.down_eq_down

@[ext]
protected theorem ext {a b : Ulower α} : a.up = b.up → a = b :=
  up_eq_up.1
#align ulower.ext Ulower.ext

end Ulower

/-
Choice function for encodable types and decidable predicates.
We provide the following API

choose      {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p] : (∃ x, p x) → α :=
choose_spec {α : Type*} {p : α → Prop} [c : encodable α] [d : decidable_pred p] (ex : ∃ x, p x) :
  p (choose ex) :=
-/
namespace Encodable

section FindA

variable {α : Type _} (p : α → Prop) [Encodable α] [DecidablePred p]

private def good : Option α → Prop
  | some a => p a
  | none => False
#align encodable.good encodable.good

private def decidable_good : DecidablePred (Good p)
  | n => by cases n <;> unfold good <;> infer_instance
#align encodable.decidable_good encodable.decidable_good

attribute [local instance] decidable_good

open Encodable

variable {p}

/-- Constructive choice function for a decidable subtype of an encodable type. -/
def chooseX (h : ∃ x, p x) : { a : α // p a } :=
  have : ∃ n, Good p (decode α n) :=
    let ⟨w, pw⟩ := h
    ⟨encode w, by simp [good, encodek, pw]⟩
  match (motive := ∀ o, Good p o → { a // p a }) _, Nat.find_spec this with
  | some a, h => ⟨a, h⟩
#align encodable.choose_x Encodable.chooseX

/-- Constructive choice function for a decidable predicate over an encodable type. -/
def choose (h : ∃ x, p x) : α :=
  (chooseX h).1
#align encodable.choose Encodable.choose

theorem choose_spec (h : ∃ x, p x) : p (choose h) :=
  (chooseX h).2
#align encodable.choose_spec Encodable.choose_spec

end FindA

/-- A constructive version of `classical.axiom_of_choice` for `encodable` types. -/
theorem axiom_of_choice {α : Type _} {β : α → Type _} {R : ∀ x, β x → Prop} [∀ a, Encodable (β a)]
    [∀ x y, Decidable (R x y)] (H : ∀ x, ∃ y, R x y) : ∃ f : ∀ a, β a, ∀ x, R x (f x) :=
  ⟨fun x => choose (H x), fun x => choose_spec (H x)⟩
#align encodable.axiom_of_choice Encodable.axiom_of_choice

/-- A constructive version of `classical.skolem` for `encodable` types. -/
theorem skolem {α : Type _} {β : α → Type _} {P : ∀ x, β x → Prop} [c : ∀ a, Encodable (β a)]
    [d : ∀ x y, Decidable (P x y)] : (∀ x, ∃ y, P x y) ↔ ∃ f : ∀ a, β a, ∀ x, P x (f x) :=
  ⟨axiom_of_choice, fun ⟨f, H⟩ x => ⟨_, H x⟩⟩
#align encodable.skolem Encodable.skolem

/-
There is a total ordering on the elements of an encodable type, induced by the map to ℕ.
-/
/-- The `encode` function, viewed as an embedding. -/
def encode' (α) [Encodable α] : α ↪ ℕ :=
  ⟨Encodable.encode, Encodable.encode_injective⟩
#align encodable.encode' Encodable.encode'

instance {α} [Encodable α] : IsTrans _ (encode' α ⁻¹'o (· ≤ ·)) :=
  (RelEmbedding.preimage _ _).IsTrans

instance {α} [Encodable α] : IsAntisymm _ (Encodable.encode' α ⁻¹'o (· ≤ ·)) :=
  (RelEmbedding.preimage _ _).IsAntisymm

instance {α} [Encodable α] : IsTotal _ (Encodable.encode' α ⁻¹'o (· ≤ ·)) :=
  (RelEmbedding.preimage _ _).IsTotal

end Encodable

namespace Directed

open Encodable

variable {α : Type _} {β : Type _} [Encodable α] [Inhabited α]

/-- Given a `directed r` function `f : α → β` defined on an encodable inhabited type,
construct a noncomputable sequence such that `r (f (x n)) (f (x (n + 1)))`
and `r (f a) (f (x (encode a + 1))`. -/
protected noncomputable def sequence {r : β → β → Prop} (f : α → β) (hf : Directed r f) : ℕ → α
  | 0 => default
  | n + 1 =>
    let p := sequence n
    match decode α n with
    | none => Classical.choose (hf p p)
    | some a => Classical.choose (hf p a)
#align directed.sequence Directed.sequence

theorem sequence_mono_nat {r : β → β → Prop} {f : α → β} (hf : Directed r f) (n : ℕ) :
    r (f (hf.sequence f n)) (f (hf.sequence f (n + 1))) :=
  by
  dsimp [Directed.sequence]
  generalize eq : hf.sequence f n = p
  cases' h : decode α n with a
  · exact (Classical.choose_spec (hf p p)).1
  · exact (Classical.choose_spec (hf p a)).1
#align directed.sequence_mono_nat Directed.sequence_mono_nat

theorem rel_sequence {r : β → β → Prop} {f : α → β} (hf : Directed r f) (a : α) :
    r (f a) (f (hf.sequence f (encode a + 1))) :=
  by
  simp only [Directed.sequence, encodek]
  exact (Classical.choose_spec (hf _ a)).2
#align directed.rel_sequence Directed.rel_sequence

variable [Preorder β] {f : α → β} (hf : Directed (· ≤ ·) f)

theorem sequence_mono : Monotone (f ∘ hf.sequence f) :=
  monotone_nat_of_le_succ <| hf.sequence_mono_nat
#align directed.sequence_mono Directed.sequence_mono

theorem le_sequence (a : α) : f a ≤ f (hf.sequence f (encode a + 1)) :=
  hf.rel_sequence a
#align directed.le_sequence Directed.le_sequence

end Directed

section Quotient

open Encodable Quotient

variable {α : Type _} {s : Setoid α} [@DecidableRel α (· ≈ ·)] [Encodable α]

/-- Representative of an equivalence class. This is a computable version of `quot.out` for a setoid
on an encodable type. -/
def Quotient.rep (q : Quotient s) : α :=
  choose (exists_rep q)
#align quotient.rep Quotient.rep

theorem Quotient.rep_spec (q : Quotient s) : ⟦q.rep⟧ = q :=
  choose_spec (exists_rep q)
#align quotient.rep_spec Quotient.rep_spec

/-- The quotient of an encodable space by a decidable equivalence relation is encodable. -/
def encodableQuotient : Encodable (Quotient s) :=
  ⟨fun q => encode q.rep, fun n => Quotient.mk'' <$> decode α n, by
    rintro ⟨l⟩ <;> rw [encodek] <;> exact congr_arg some ⟦l⟧.rep_spec⟩
#align encodable_quotient encodableQuotient

end Quotient

