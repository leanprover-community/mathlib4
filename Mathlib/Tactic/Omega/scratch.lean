import Std.Data.Int.Basic
import Std.Data.Rat.Lemmas
import Std.Data.Fin.Lemmas
import Mathlib.Tactic.Use
import Std.Tactic.Simpa
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Rewrites
import Mathlib.Tactic.SplitIfs
import Mathlib.Util.Time
import Mathlib.Tactic.Convert
import Mathlib.Tactic.PermuteGoals

-- We follow "The Omega Test: a fast and practical integer programming algorithm for dependence analysis."

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[simp] theorem ite_some_none_eq_none [Decidable P] :
    (if P then some x else none) = none ↔ ¬ P := by
  split_ifs <;> simp_all

namespace Array

@[simp] theorem zipWith_data {A : Array α} {B : Array β} {f : α → β → γ} :
    (Array.zipWith A B f).data = List.zipWith f A.data B.data := by
  sorry

@[simp] theorem zip_data {A : Array α} {B : Array β} :
    (A.zip B).data = A.data.zip B.data := by
  simp [zip, List.zip]

@[simp] theorem map_mk (xs : List α) (f : α → β) :
    (Array.mk xs).map f = Array.mk (xs.map f) := by
  sorry

@[simp] theorem foldr_mk (xs : List α) (f : α → β → β) (b : β) {l : Nat} (w : l = xs.length) :
   Array.foldr f b { data := xs } l = xs.foldr f b := sorry

theorem foldr_map {xs : Array α} {f : α → β} {b : γ} {l : ℕ} (w : l = xs.size) :
    Array.foldr g b (xs.map f) l = Array.foldr (fun x a => g (f x) a) b xs l := by
  rcases xs with ⟨xs⟩
  subst w
  simp only [size_mk, foldr_mk]
  rw [Array.map_mk] -- Why did `simp` not use this?
  simp [List.foldr_map]

end Array

open Nat

instance (L : List (Option α)) : Decidable (none ∈ L) := sorry

def Array.natGCD (xs : Array Nat) : Nat := xs.foldr gcd 0
def Array.intGCD (xs : Array Int) : Nat := xs.foldr (fun a b => gcd a.natAbs b) 0

theorem Array.intGCD_eq (xs : Array Int) : xs.intGCD = (xs.map Int.natAbs).natGCD := by
  simp [Array.natGCD, Array.intGCD, Array.foldr_map]

theorem Nat.gcd_eq_iff (a b : Nat) :
    gcd a b = g ↔ g ∣ a ∧ g ∣ b ∧ (∀ c, c ∣ a → c ∣ b → c ∣ g) := by
  constructor
  · rintro rfl
    exact ⟨gcd_dvd_left _ _, gcd_dvd_right _ _, fun _ => Nat.dvd_gcd⟩
  · rintro ⟨ha, hb, hc⟩
    apply Nat.dvd_antisymm
    · apply hc
      · exact gcd_dvd_left a b
      · exact gcd_dvd_right a b
    · exact Nat.dvd_gcd ha hb

def List.natGCD (x : List Nat) : Nat := x.foldr gcd 0
def List.intGCD (x : List Int) : Nat := x.foldr (fun a b => gcd a.natAbs b) 0

@[simp] theorem List.natGCD_nil : ([] : List Nat).natGCD = 0 := rfl
@[simp] theorem List.natGCD_cons : (x :: xs : List Nat).natGCD = gcd x xs.natGCD := rfl

theorem List.natGCD_dvd (xs : List Nat) {a : Nat} (m : a ∈ xs) : xs.natGCD ∣ a := by
  induction m with
  | head =>
    simp only [natGCD_cons]
    apply gcd_dvd_left
  | tail b m ih =>   -- FIXME: why is the argument of tail implicit?
    simp only [natGCD_cons]
    exact Nat.dvd_trans (gcd_dvd_right _ _) ih

theorem List.dvd_natGCD (xs : List Nat) (c : Nat) (w : ∀ {a : Nat}, a ∈ xs → c ∣ a) :
    c ∣ xs.natGCD := by
  induction xs with
  | nil => simpa using Nat.dvd_zero c
  | cons x xs ih =>
    simp
    apply Nat.dvd_gcd
    · apply w
      simp
    · apply ih
      intro b m
      apply w
      exact mem_cons_of_mem x m

@[simp] theorem Array.natGCD_mk (x : List Nat) : (Array.mk x).natGCD = x.natGCD := sorry
@[simp] theorem Array.intGCD_mk (x : List Int) : (Array.mk x).intGCD = x.intGCD := sorry

theorem Array.natGCD_dvd (x : Array Nat) (i : Fin x.size) : x.natGCD ∣ x[i] := by
  rcases x with ⟨x⟩
  simp
  apply List.natGCD_dvd
  sorry

theorem Array.dvd_natGCD (x : Array Nat) (c : Nat) (w : ∀ i : Fin x.size, c ∣ x[i]) :
    c ∣ x.natGCD := by
  rcases x with ⟨x⟩
  simp
  apply List.dvd_natGCD
  intro a m
  sorry

theorem Array.natGCD_eq_iff (x : Array Nat) (g : Nat) :
    x.natGCD = g ↔ (∀ i : Fin x.size, g ∣ x[i]) ∧ (∀ c, (∀ i : Fin x.size, c ∣ x[i]) → c ∣ g) := by
  constructor
  · rintro rfl
    exact ⟨Array.natGCD_dvd _, fun _ => Array.dvd_natGCD _ _⟩
  · rintro ⟨hi, hg⟩
    apply Nat.dvd_antisymm
    · apply hg
      intro i
      exact Array.natGCD_dvd x i
    · exact Array.dvd_natGCD x g hi

theorem Array.intGCD_eq_iff (x : Array Int) (g : Nat) :
    x.intGCD = g ↔ (∀ i : Fin x.size, (g : Int) ∣ x[i]) ∧ (∀ (c : Nat), (∀ i : Fin x.size, (c : Int) ∣ x[i]) → c ∣ g) := by
  sorry

-- This is Nat.dvd_one in `Nat.dvd_one` in `Mathlib.Data.Nat.Order.Lemmas`.
@[simp] theorem Nat.dvd_one_iff : n ∣ 1 ↔ n = 1 := by sorry

theorem Array.natGCD_eq_one_iff (xs : Array Nat) :
    xs.natGCD = 1 ↔ (∀ c, (∀ i : Fin xs.size, c ∣ xs[i]) → c = 1) := by
  rw [Array.natGCD_eq_iff]
  have one_dvd : ∀ n, 1 ∣ n := fun n => sorry
  simp [one_dvd]

theorem Array.intGCD_eq_one_iff (xs : Array Int) :
    xs.intGCD = 1 ↔ (∀ c : Nat, (∀ i : Fin xs.size, (c : Int) ∣ xs[i]) → c = 1) := by
  rw [Array.intGCD_eq, Array.natGCD_eq_one_iff]
  simp
  sorry -- should be easy from here

#time example : Nat.gcd (17*19*101^2*1024) (17*19*101*4*39) = 130492 := rfl
#time example : Array.intGCD #[45, -15, 85] = 5 := rfl
#time example : Array.intGCD #[17*19*101*101*1024, -17*19*101*4*39, 17*19*39] = 323 := rfl

def Array.Nonzero (xs : Array Int) : Prop := ∃ i : Fin xs.size, xs[i] ≠ 0

theorem Array.intGCD_ne_zero_of_nonzero (xs : Array Int) (w : xs.Nonzero) : xs.intGCD ≠ 0 :=
  sorry

theorem Array.intGCD_div_intGCD (xs : Array Int) (w : xs.Nonzero) :
    (xs.map (fun x : Int => x / xs.intGCD)).intGCD = 1 := by
  rw [Array.intGCD_eq_one_iff]
  intro c w
  simp at w
  suffices xs.intGCD = c * xs.intGCD from sorry
  rw [Array.intGCD_eq_iff]
  constructor
  · intro i
    specialize w (Fin.cast (by simp) i)
    simp at w
    sorry

def Int.bmod (x : Int) (m : Nat) : Int :=
  let r := x % m
  if r < m / 2 then
    r
  else
    r - m

example : Int.bmod 12 7 = -2 := rfl

namespace Omega

structure LinearCombo where
  constantTerm : Int
  coefficients : Array Int
  gcd : Nat
  gcd_eq : gcd = Array.intGCD coefficients
  smallIdx : Fin coefficients.size
  -- coefficients[smallIdx] ≠ 0
  -- ∀ c ∈ coefficients, c = 0 ∨ c.natAbs ≥ coefficients[smallIdx].natAbs

structure Problem where
  impossible : Bool
  equalities : List LinearCombo
  inequalities : List LinearCombo

namespace LinearCombo

def eval (lc : LinearCombo) (values : Array Int) : Int :=
  (lc.coefficients.zip values).foldl (fun r ⟨c, x⟩ => r + c * x) lc.constantTerm
-- Perhaps we'd like to define this via:
-- ```
-- Id.run do
--   let mut r := lc.constantTerm
--   for c in lc.coefficients, x in values do
--     r := r + c * x
--   return r
-- ```
-- But at present this is far too hard to reason about.
-- See discussion at https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/proofs.20about.20for.20loops/near/390634764

def evalRat (lc : LinearCombo) (values : Array Rat) : Rat :=
  (lc.coefficients.zip values).foldl (fun r ⟨c, x⟩ => r + c * x) (lc.constantTerm : Rat)

theorem evalRat_cast (lc : LinearCombo) (values : Array Int) :
    lc.evalRat (values.map fun x : Int => (x : Rat)) = lc.eval values := by
  rw [eval, evalRat]
  simp [Array.foldl_eq_foldl_data]
  rcases lc with ⟨const, ⟨coeffs⟩, -, gcd_eq, smallIdx⟩
  rcases values with ⟨values⟩
  dsimp
  clear smallIdx gcd_eq
  induction coeffs generalizing const values with
  | nil => simp
  | cons c coeffs cih =>
    rcases values with _ | ⟨v, values⟩
    · simp
    · specialize cih (const + c * v) values
      dsimp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      convert cih
      simp

def satZero (lc : LinearCombo) : Prop :=
  ∃ values, lc.eval values = 0

def satRatZero (lc : LinearCombo) : Prop :=
  ∃ values, lc.evalRat values = 0

def satNonneg (lc : LinearCombo) : Prop :=
  ∃ values, lc.eval values ≥ 0

def satRatNoneg (lc : LinearCombo) : Prop :=
  ∃ values, lc.evalRat values ≥ 0

variable {lc : LinearCombo}

theorem satZero_of_satRatZero : lc.satZero → lc.satRatZero := by
  rintro ⟨values, w⟩
  use values.map fun x : Int => (x : Rat)
  rw [evalRat_cast, w]
  rfl

theorem satNoneg_of_satRatNonneg : lc.satNonneg → lc.satRatNoneg := by
  rintro ⟨values, w⟩
  use values.map fun x : Int => (x : Rat)
  rw [evalRat_cast]
  sorry

def normalizeEquality : LinearCombo → Option LinearCombo
  | {constantTerm, coefficients, gcd, gcd_eq, smallIdx} =>
    if constantTerm % gcd = 0 then
      some
      { constantTerm := constantTerm / gcd,
        coefficients := coefficients.map (· / gcd),
        gcd := 1,
        gcd_eq := by
          subst gcd_eq

        smallIdx := Fin.cast (by simp) smallIdx }
    else
      none

def normalizeInequality : LinearCombo → LinearCombo
  | {constantTerm, coefficients, gcd, gcd_eq, smallIdx} =>
    { -- Recall `Int.fdiv` is division with floor rounding.
      constantTerm := Int.fdiv constantTerm gcd
      coefficients := coefficients.map (· / gcd)
      gcd := 1,
      gcd_eq := sorry,
      smallIdx := Fin.cast (by simp) smallIdx }

theorem not_satZero_of_normalizeEquality_isNone {lc : LinearCombo} :
    normalizeEquality lc = none → ¬ lc.satZero := by
  intro w
  rcases lc with ⟨const, ⟨coeffs⟩, gcd, smallIdx⟩
  simp [normalizeEquality] at w
  simp [satZero]
  intro values
  simp [eval]

theorem satZero_iff_normalizeEquality_satZero {lc lc' : LinearCombo} :
    (lc' ∈ lc.normalizeEquality) → lc'.satZero ↔ lc.satZero := sorry
theorem satNonneg_iff_normalizeInequality_satNonneg {lc : LinearCombo} :
    lc.normalizeInequality.satNonneg ↔ lc.satNonneg := sorry

-- Do we need statements here about satisfiability over `Rat`?

end LinearCombo

open LinearCombo

namespace Problem

def bot : Problem := { impossible := true, equalities := [], inequalities := [] }

def sat (p : Problem) : Prop :=
  p.impossible = false ∧ (∀ lc ∈ p.equalities, lc.satZero) ∧ (∀ lc ∈ p.inequalities, lc.satNonneg)

@[simp] theorem not_bot_sat : ¬ bot.sat := by
  simp [bot, sat]

def normalize (p : Problem) : Problem :=
  if p.impossible then
     bot
  else
    let normalizedEqualities := p.equalities.map LinearCombo.normalizeEquality
    if none ∈ normalizedEqualities then
      bot
    else
      { impossible := false,
        equalities := normalizedEqualities.filterMap fun x => x
        inequalities := p.inequalities.map LinearCombo.normalizeInequality }

theorem normalize_sat_iff_sat {p : Problem} : p.normalize.sat ↔ p.sat := by
  rw [normalize]
  split_ifs with h₁
  · simp [sat, h₁]
  · simp only [List.mem_map]
    split_ifs with h₂
    · simp at h₂
      obtain ⟨e, m, w⟩ := h₂
      replace w := not_sat_of_normalizeEquality_isNone w
      simp only [sat, h₁]
      -- trivial from here
      simp
      intro w'
      specialize w' _ m
      apply False.elim
      exact w w'
    · simp only [sat, h₁]
      refine Iff.and (by trivial) (Iff.and ?_ ?_)
      · sorry
      · sorry




end Problem
