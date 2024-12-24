/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Data.Seq.Seq
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.PNat.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Floor

/-!
# Basic Definitions/Theorems for Continued Fractions

## Summary

We define generalised, simple, and regular continued fractions and functions to evaluate their
convergents. We follow the naming conventions from Wikipedia and [wall2018analytic], Chapter 1.

## Main definitions

1. Generalised continued fractions (gcfs)
2. Simple continued fractions (scfs)
3. (Regular) continued fractions ((r)cfs)
4. Computation of convergents using the recurrence relation in `convs`.
5. Computation of convergents by directly evaluating the fraction described by the gcf in `convs'`.

## Implementation notes

1. The most commonly used kind of continued fractions in the literature are regular continued
fractions. We hence just call them `ContFract` in the library.
2. We use sequences from `Data.Seq` to encode potentially infinite sequences.

## References

- <https://en.wikipedia.org/wiki/Generalized_continued_fraction>
- [Wall, H.S., *Analytic Theory of Continued Fractions*][wall2018analytic]

## Tags

numerics, number theory, approximations, fractions
-/

-- Fix a carrier `α`.
variable (α : Type*)

/-!### Definitions -/

-- Porting note: Originally `protected structure GenContFract.Pair`
/-- We collect a partial numerator `aᵢ` and partial denominator `bᵢ` in a pair `⟨aᵢ, bᵢ⟩`. -/
structure GenContFract.Pair where
  /-- Partial numerator -/
  a : α
  /-- Partial denominator -/
  b : α
  deriving Inhabited

open GenContFract

/-! Interlude: define some expected coercions and instances. -/

namespace GenContFract.Pair

variable {α}

/-- Make a `GenContFract.Pair` printable. -/
instance [Repr α] : Repr (Pair α) :=
  ⟨fun p _ ↦ "(a : " ++ repr p.a ++ ", b : " ++ repr p.b ++ ")"⟩

/-- Maps a function `f` on both components of a given pair. -/
def map {β : Type*} (f : α → β) (gp : Pair α) : Pair β :=
  ⟨f gp.a, f gp.b⟩

section coe

-- Fix another type `β` which we will convert to.
variable {β : Type*} [Coe α β]

-- Porting note: added so we can add the `@[coe]` attribute
/-- The coercion between numerator-denominator pairs happens componentwise. -/
@[coe]
def coeFn : Pair α → Pair β := map (↑)

/-- Coerce a pair by elementwise coercion. -/
instance : Coe (Pair α) (Pair β) :=
  ⟨coeFn⟩

@[simp, norm_cast]
theorem coe_toPair {a b : α} : (↑(Pair.mk a b) : Pair β) = Pair.mk (a : β) (b : β) := rfl

end coe

end GenContFract.Pair

/-- A *generalised continued fraction* (gcf) is a potentially infinite expression of the form
$$
  h + \dfrac{a_0}
            {b_0 + \dfrac{a_1}
                         {b_1 + \dfrac{a_2}
                                      {b_2 + \dfrac{a_3}
                                                   {b_3 + \dots}}}}
$$
where `h` is called the *head term* or *integer part*, the `aᵢ` are called the
*partial numerators* and the `bᵢ` the *partial denominators* of the gcf.
We store the sequence of partial numerators and denominators in a sequence of `GenContFract.Pair`s
`s`.
For convenience, one often writes `[h; (a₀, b₀), (a₁, b₁), (a₂, b₂),...]`.
-/
@[ext]
structure GenContFract where
  /-- Head term -/
  h : α
  /-- Sequence of partial numerator and denominator pairs. -/
  s : Stream'.Seq <| Pair α

variable {α}

namespace GenContFract

/-- Constructs a generalized continued fraction without fractional part. -/
def ofInteger (a : α) : GenContFract α :=
  ⟨a, Stream'.Seq.nil⟩

instance [Inhabited α] : Inhabited (GenContFract α) :=
  ⟨ofInteger default⟩

/-- Returns the sequence of partial numerators `aᵢ` of `g`. -/
def partNums (g : GenContFract α) : Stream'.Seq α :=
  g.s.map Pair.a

/-- Returns the sequence of partial denominators `bᵢ` of `g`. -/
def partDens (g : GenContFract α) : Stream'.Seq α :=
  g.s.map Pair.b

/-- A gcf terminated at position `n` if its sequence terminates at position `n`. -/
def TerminatedAt (g : GenContFract α) (n : ℕ) : Prop :=
  g.s.TerminatedAt n

/-- It is decidable whether a gcf terminated at a given position. -/
instance terminatedAtDecidable (g : GenContFract α) (n : ℕ) :
    Decidable (g.TerminatedAt n) := by
  unfold TerminatedAt
  infer_instance

/-- A gcf terminates if its sequence terminates. -/
def Terminates (g : GenContFract α) : Prop :=
  g.s.Terminates

section coe

/-! Interlude: define some expected coercions. -/

-- Fix another type `β` which we will convert to.
variable {β : Type*} [Coe α β]

-- Porting note: Added to put `@[coe]` attr on it.
/-- The coercion between `GenContFract` happens on the head term
and all numerator-denominator pairs componentwise. -/
@[coe]
def coeFn : GenContFract α → GenContFract β :=
  fun g ↦ ⟨(g.h : β), (g.s.map (↑) : Stream'.Seq <| Pair β)⟩

/-- Coerce a gcf by elementwise coercion. -/
instance : Coe (GenContFract α) (GenContFract β) :=
  ⟨coeFn⟩

@[simp, norm_cast]
theorem coe_toGenContFract {g : GenContFract α} :
    (g : GenContFract β) =
      ⟨(g.h : β), (g.s.map (↑) : Stream'.Seq <| Pair β)⟩ := rfl

end coe

end GenContFract

/-- A generalized continued fraction is a *simple continued fraction* if all partial numerators are
equal to one.
$$
  h + \dfrac{1}
            {b_0 + \dfrac{1}
                         {b_1 + \dfrac{1}
                                      {b_2 + \dfrac{1}
                                                   {b_3 + \dots}}}}
$$
-/
def GenContFract.IsSimpContFract (g : GenContFract α)
    [One α] : Prop :=
  ∀ (n : ℕ) (aₙ : α), g.partNums.get? n = some aₙ → aₙ = 1

variable (α)

/-- A *simple continued fraction* (scf) is a generalized continued fraction (gcf) whose partial
numerators are equal to one.
$$
  h + \dfrac{1}
            {b_0 + \dfrac{1}
                         {b_1 + \dfrac{1}
                                      {b_2 + \dfrac{1}
                                                   {b_3 + \dots}}}}
$$
For convenience, one often writes `[h; b₀, b₁, b₂,...]`.
It is encoded as the subtype of gcfs that satisfy `GenContFract.IsSimpContFract`.
 -/
def SimpContFract [One α] :=
  { g : GenContFract α // g.IsSimpContFract }

variable {α}

-- Interlude: define some expected coercions.
namespace SimpContFract

variable [One α]

/-- Constructs a simple continued fraction without fractional part. -/
def ofInteger (a : α) : SimpContFract α :=
  ⟨GenContFract.ofInteger a, fun n aₙ h ↦ by cases h⟩

instance : Inhabited (SimpContFract α) :=
  ⟨ofInteger 1⟩

/-- Lift a scf to a gcf using the inclusion map. -/
instance : Coe (SimpContFract α) (GenContFract α) :=
  -- Porting note: originally `by unfold SimpContFract; infer_instance`
  ⟨Subtype.val⟩

-- Porting note: Syntactic tautology due to change in `Coe` above.
-- theorem coe_toGenContFract {s : SimpContFract α} :
--     (↑s : GenContFract α) = s.val := rfl

end SimpContFract

/--
A simple continued fraction is a *(regular) continued fraction* ((r)cf) if all partial denominators
`bᵢ` are positive, i.e. `0 < bᵢ`.
-/
def SimpContFract.IsRegContFract [One α] [Zero α] [LT α]
    (s : SimpContFract α) : Prop :=
  ∀ (n : ℕ) (bₙ : α),
    (↑s : GenContFract α).partDens.get? n = some bₙ → 0 < bₙ

variable (α)

/-- A *(regular) continued fraction* ((r)cf) is a simple continued fraction (scf) whose partial
denominators are all positive. It is the subtype of scfs that satisfy `SimpContFract.IsContFract`.
 -/
def RegContFract [One α] [Zero α] [LT α] :=
  { s : SimpContFract α // s.IsRegContFract }

variable {α}

/-! Interlude: define some expected coercions. -/

namespace RegContFract

variable [One α] [Zero α] [LT α]

/-- Constructs a continued fraction without fractional part. -/
def ofInteger (a : α) : RegContFract α :=
  ⟨SimpContFract.ofInteger a, fun n bₙ h ↦ by cases h⟩

instance : Inhabited (RegContFract α) :=
  ⟨ofInteger 0⟩

/-- Lift a cf to a scf using the inclusion map. -/
instance : Coe (RegContFract α) (SimpContFract α) :=
  -- Porting note: originally `by unfold ContFract; infer_instance`
  ⟨Subtype.val⟩

-- Porting note: Syntactic tautology due to change of `Coe` above.
-- theorem coe_to_simpleContFract {c : ContFract α} :
--     (↑c : SimpContFract α) = c.val := rfl

/-- Lift a cf to a scf using the inclusion map. -/
instance : Coe (RegContFract α) (GenContFract α) :=
  ⟨fun c ↦ c.val⟩
  -- Porting note: was `fun c ↦ ↑(↑c : SimpContFract α)`

-- Porting note: Syntactic tautology due to change of `Coe` above.
-- theorem coe_toGenContFract {c : ContFract α} :
--     (↑c : GenContFract α) = c.val := rfl

end RegContFract

@[ext]
structure ContFract where
  /-- Head term -/
  h : ℤ
  /-- Sequence of denominators. -/
  s : Stream'.Seq ℕ+
  /-- If the Sequence of denominators is finite, it does not end in one. -/
  one_not_mem_last : ∀ h : s.Terminates, 1 ∉ (s.toList h).getLast?

namespace ContFract

@[coe]
def toGenContFract [IntCast α] [NatCast α] [One α] : ContFract → (GenContFract α) :=
  fun ⟨h, s, _⟩ => ⟨h, s.map (fun n : ℕ+ => ⟨1, n⟩)⟩

instance [IntCast α] [NatCast α] [One α] : Coe ContFract (GenContFract α) :=
  ⟨toGenContFract⟩

theorem isSimpContFract [IntCast α] [NatCast α] [One α]
    (c : ContFract) : IsSimpContFract (c : GenContFract α) := by
  simp [IsSimpContFract, partNums, toGenContFract]

@[coe]
def toSimpContFract [IntCast α] [NatCast α] [One α] : ContFract → SimpContFract α :=
  fun c => ⟨c, c.isSimpContFract⟩

instance [IntCast α] [NatCast α] [One α] : Coe ContFract (SimpContFract α) :=
  ⟨toSimpContFract⟩

theorem isRegContFract [AddGroupWithOne α]
    [PartialOrder α] [AddLeftMono α] [ZeroLEOneClass α] [NeZero (1 : α)]
    (c : ContFract) : SimpContFract.IsRegContFract (c : SimpContFract α) := by
  simp [SimpContFract.IsRegContFract, partDens, toSimpContFract, toGenContFract]

@[coe]
def toRegContFract [AddGroupWithOne α]
    [PartialOrder α] [AddLeftMono α] [ZeroLEOneClass α] [NeZero (1 : α)] :
    ContFract → RegContFract α :=
  fun c => ⟨c, c.isRegContFract⟩

instance [AddGroupWithOne α]
    [PartialOrder α] [AddLeftMono α] [ZeroLEOneClass α] [NeZero (1 : α)] :
    Coe ContFract (RegContFract α) :=
  ⟨toRegContFract⟩

def Terminates (c : ContFract) : Prop :=
  c.s.Terminates

def TerminatedAt (c : ContFract) (n : ℕ) : Prop :=
  c.s.TerminatedAt n

theorem terminates_coe_iff [IntCast α] [NatCast α] [One α] {c : ContFract} :
    (c : GenContFract α).Terminates ↔ c.Terminates := by
  simp [GenContFract.Terminates, ContFract.Terminates, toGenContFract]

theorem terminatedAt_coe_iff [IntCast α] [NatCast α] [One α] {c : ContFract} {n : ℕ} :
    (c : GenContFract α).TerminatedAt n ↔ c.TerminatedAt n := by
  simp [GenContFract.TerminatedAt, ContFract.TerminatedAt, toGenContFract]

end ContFract

namespace GenContFract

/-!
### Computation of Convergents

We now define how to compute the convergents of a gcf. There are two standard ways to do this:
directly evaluating the (infinite) fraction described by the gcf or using a recurrence relation.
For (r)cfs, these computations are equivalent as shown in
`Algebra.ContinuedFractions.ConvergentsEquiv`.
-/

-- Fix a division ring for the computations.
variable {K : Type*} [DivisionRing K]

/-!
We start with the definition of the recurrence relation. Given a gcf `g`, for all `n ≥ 1`, we define
- `A₋₁ = 1,  A₀ = h,  Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, and
- `B₋₁ = 0,  B₀ = 1,  Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`.

`Aₙ, Bₙ` are called the *nth continuants*, `Aₙ` the *nth numerator*, and `Bₙ` the
*nth denominator* of `g`. The *nth convergent* of `g` is given by `Aₙ / Bₙ`.
-/

/-- Returns the next numerator `Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, where `predA` is `Aₙ₋₁`,
`ppredA` is `Aₙ₋₂`, `a` is `aₙ₋₁`, and `b` is `bₙ₋₁`.
-/
def nextNum (a b ppredA predA : K) : K :=
  b * predA + a * ppredA

/-- Returns the next denominator `Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`, where `predB` is `Bₙ₋₁` and
`ppredB` is `Bₙ₋₂`, `a` is `aₙ₋₁`, and `b` is `bₙ₋₁`.
-/
def nextDen (aₙ bₙ ppredB predB : K) : K :=
  bₙ * predB + aₙ * ppredB

/--
Returns the next continuants `⟨Aₙ, Bₙ⟩` using `nextNum` and `nextDen`, where `pred`
is `⟨Aₙ₋₁, Bₙ₋₁⟩`, `ppred` is `⟨Aₙ₋₂, Bₙ₋₂⟩`, `a` is `aₙ₋₁`, and `b` is `bₙ₋₁`.
-/
def nextConts (a b : K) (ppred pred : Pair K) : Pair K :=
  ⟨nextNum a b ppred.a pred.a, nextDen a b ppred.b pred.b⟩

/-- Returns the continuants `⟨Aₙ₋₁, Bₙ₋₁⟩` of `g`. -/
def contsAux (g : GenContFract K) : Stream' (Pair K)
  | 0 => ⟨1, 0⟩
  | 1 => ⟨g.h, 1⟩
  | n + 2 =>
    match g.s.get? n with
    | none => contsAux g (n + 1)
    | some gp => nextConts gp.a gp.b (contsAux g n) (contsAux g (n + 1))

/-- Returns the continuants `⟨Aₙ, Bₙ⟩` of `g`. -/
def conts (g : GenContFract K) : Stream' (Pair K) :=
  g.contsAux.tail

/-- Returns the numerators `Aₙ` of `g`. -/
def nums (g : GenContFract K) : Stream' K :=
  g.conts.map Pair.a

/-- Returns the denominators `Bₙ` of `g`. -/
def dens (g : GenContFract K) : Stream' K :=
  g.conts.map Pair.b

/-- Returns the convergents `Aₙ / Bₙ` of `g`, where `Aₙ, Bₙ` are the nth continuants of `g`. -/
def convs (g : GenContFract K) : Stream' K :=
  fun n : ℕ ↦ g.nums n / g.dens n

/--
Returns the approximation of the fraction described by the given sequence up to a given position n.
For example, `convs'Aux [(1, 2), (3, 4), (5, 6)] 2 = 1 / (2 + 3 / 4)` and
`convs'Aux [(1, 2), (3, 4), (5, 6)] 0 = 0`.
-/
def convs'Aux : Stream'.Seq (Pair K) → ℕ → K
  | _, 0 => 0
  | s, n + 1 =>
    match s.head with
    | none => 0
    | some gp => gp.a / (gp.b + convs'Aux s.tail n)

/-- Returns the convergents of `g` by evaluating the fraction described by `g` up to a given
position `n`. For example, `convs' [9; (1, 2), (3, 4), (5, 6)] 2 = 9 + 1 / (2 + 3 / 4)` and
`convs' [9; (1, 2), (3, 4), (5, 6)] 0 = 9`
-/
def convs' (g : GenContFract K) (n : ℕ) : K :=
  g.h + convs'Aux g.s n

end GenContFract

@[ext]
structure FiniteContFract where
  /-- Head term -/
  h : ℤ
  /-- List of denominators. -/
  s : List ℕ+
  /-- The last element in the list of denominators is not one -/
  last_ne_one : 1 ∉ s.getLast?
deriving DecidableEq

namespace FiniteContFract

variable {K : Type*} [DivisionRing K]

@[coe]
def toContFract (c : FiniteContFract) : ContFract :=
  ⟨c.h, c.s, fun _ => by simp [c.3]⟩

theorem terminatedAt_toContFract (c : FiniteContFract) :
    c.toContFract.s.TerminatedAt c.s.length :=
  Stream'.Seq.terminatedAt_ofList _

instance : Coe FiniteContFract ContFract :=
  ⟨toContFract⟩

def evalTail : List ℕ+ → ℚ
  | [] => 0
  | a::l => ((a : ℚ) + evalTail l)⁻¹

theorem evalTail_nonneg : ∀ (l : List ℕ+), 0 ≤ evalTail l
  | [] => le_rfl
  | _::_ => inv_nonneg.2 <| add_nonneg (Nat.cast_nonneg _) (evalTail_nonneg _)

private theorem evalTail_pos_and_lt_one : ∀ {l : List ℕ+}, l ≠ [] → 1 ∉ l.getLast? →
    0 < evalTail l ∧ evalTail l < 1
  | [a], _, h₂ => by
    rw [evalTail, evalTail, add_zero, inv_pos, Nat.cast_pos]
    refine ⟨a.2, ?_⟩
    apply inv_lt_one_of_one_lt₀
    rw [← Nat.cast_one, Nat.cast_lt]
    refine lt_of_le_of_ne a.one_le ?_
    simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at h₂
    rwa [Ne, Eq.comm, PNat.coe_eq_one_iff]
  | a::b::l, _, h₂ => by
    have ih := @evalTail_pos_and_lt_one (b::l) (by simp) (by simpa using h₂)
    unfold evalTail
    rw [inv_pos]
    refine ⟨add_pos (Nat.cast_pos.2 a.2) ih.1, ?_⟩
    apply inv_lt_one_of_one_lt₀
    refine lt_add_of_le_of_pos ?_ ih.1
    rw [← Nat.cast_one, Nat.cast_le]
    exact a.one_le

theorem evalTail_pos {l : List ℕ+} (h₁ : l ≠ []) (h₂ : 1 ∉ l.getLast?) : 0 < evalTail l :=
  (evalTail_pos_and_lt_one h₁ h₂).1

theorem evalTail_lt_one : ∀ {l : List ℕ+}, 1 ∉ l.getLast? → evalTail l < 1
  | [], _ => by simp [evalTail]
  | a::l, h => (evalTail_pos_and_lt_one (by simp) h).2

def eval (c : FiniteContFract) : ℚ :=
  c.h + evalTail c.s

theorem head_eq_floor_evalTail_inv (a : ℕ+) (l : List ℕ+) (hl : 1 ∉ l.getLast?) :
    (a : ℤ) = ⌊(evalTail (a::l))⁻¹⌋ := by
  rw [evalTail, inv_inv]
  refine le_antisymm ?_ ?_
  · simp only [Int.floor_nat_add, le_add_iff_nonneg_right, Int.floor_nonneg]
    exact evalTail_nonneg _
  · simp only [Int.floor_nat_add, add_le_iff_nonpos_right, Int.floor_le_iff, Int.cast_zero,
      zero_add]
    exact evalTail_lt_one hl

theorem evalTail_tail_eq_fract_evalTail_inv (a : ℕ+) (l : List ℕ+) (hl : 1 ∉ l.getLast?) :
    evalTail l = Int.fract ((evalTail (a::l))⁻¹) := by
  rw [Int.fract, ← head_eq_floor_evalTail_inv a l hl, evalTail, inv_inv]
  simp

theorem evalTail_injective : ∀ {l₁ l₂ : List ℕ+},
    1 ∉ l₁.getLast? → 1 ∉ l₂.getLast? → evalTail l₁ = evalTail l₂ → l₁ = l₂
  | [], [], _, _, _ => rfl
  | a::l, [], _, _, h₁₂ => by
    simp only [evalTail, inv_eq_zero] at h₁₂
    refine False.elim (ne_of_gt ?_ h₁₂)
    exact add_pos_of_pos_of_nonneg (Nat.cast_pos.2 a.pos) (evalTail_nonneg _)
  | [], a::l, _, _, h₁₂ => by
    simp only [evalTail, zero_eq_inv] at h₁₂
    refine False.elim (ne_of_lt ?_ h₁₂)
    exact add_pos_of_pos_of_nonneg (Nat.cast_pos.2 a.pos) (evalTail_nonneg _)
  | a₁::l₁, a₂::l₂, h₁, h₂, h₁₂ => by
    replace h₁ : 1 ∉ l₁.getLast? := by simp_all [Option.getD_eq_iff, List.getLast?_cons]
    replace h₂ : 1 ∉ l₂.getLast? := by simp_all [Option.getD_eq_iff, List.getLast?_cons]
    have hhead₁ := head_eq_floor_evalTail_inv a₁ l₁ h₁
    have hhead₂ := head_eq_floor_evalTail_inv a₂ l₂ h₂
    have htail₁ := evalTail_tail_eq_fract_evalTail_inv a₁ l₁ h₁
    have htail₂ := evalTail_tail_eq_fract_evalTail_inv a₂ l₂ h₂
    rw [h₁₂, ← hhead₂] at hhead₁
    norm_cast at hhead₁
    subst hhead₁
    rw [h₁₂, ← htail₂] at htail₁
    rw [evalTail_injective h₁ h₂ htail₁]

theorem h_eq_floor_eval (c : FiniteContFract) : c.h = ⌊c.eval⌋ :=
  le_antisymm (by
      rw [Int.le_floor, eval]
      exact le_add_of_nonneg_right (evalTail_nonneg _))
    (by
      rw [Int.floor_le_iff, eval]
      exact add_lt_add_left (evalTail_lt_one c.3) _)

theorem eval_injective : Function.Injective (eval : FiniteContFract → ℚ) := by
  intro c₁ c₂ h
  have : c₁.h = c₂.h := by rw [h_eq_floor_eval, h, h_eq_floor_eval]
  ext1
  · exact this
  · rw [eval, eval, this, add_left_cancel_iff] at h
    exact evalTail_injective c₁.3 c₂.3 h

theorem coe_eval_eq_convs'_coe_length [CharZero K] : ∀ (c : FiniteContFract),
    (c.eval : K) = (c : GenContFract K).convs' c.s.length
  | ⟨h, [], _⟩ => by
    simp [toContFract, ContFract.toGenContFract, eval, evalTail, convs', convs'Aux,
      ContFract.toSimpContFract]
  | ⟨h, a::l, hl⟩ => by
    simpa [toContFract, ContFract.toGenContFract, eval, convs', convs'Aux, evalTail,
      ContFract.toSimpContFract] using coe_eval_eq_convs'_coe_length ⟨a, l,
        fun h => by simp_all [Option.getD_eq_iff, List.getLast?_cons]⟩
  termination_by l => l.s.length

theorem eval_eq_convs'_coe_length (c : FiniteContFract) :
    c.eval = (c : GenContFract ℚ).convs' c.s.length := by
  erw [← coe_eval_eq_convs'_coe_length]
  simp

end FiniteContFract
