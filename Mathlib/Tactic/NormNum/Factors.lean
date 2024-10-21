import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.NormNum.Prime

/-!
# `simproc` for `Nat.primeFactorsList`

Note that since `norm_num` can only produce numerals, we can't use it here.
-/

open Nat

namespace Mathlib.Meta.NormNum

/-- A partial proof of `primeFactorsList`.
Asserts that `l` is a sorted list of primes, lower bounded by a prime `p`, which multiplies to
`n`. -/
def FactorsHelper (n p : ℕ) (l : List ℕ) : Prop :=
  p.Prime → List.Chain (· ≤ ·) p l ∧ (∀ a ∈ l, Nat.Prime a) ∧ List.prod l = n

theorem factorsHelper_nil (a : ℕ) : FactorsHelper 1 a [] := fun _ =>
  ⟨List.Chain.nil, by rintro _ ⟨⟩, List.prod_nil⟩

theorem factorsHelper_cons' (n m a b : ℕ) (l : List ℕ) (h₁ : IsNat (b * m) n) (h₂ : a ≤ b)
    (h₃ : minFac b = b) (H : FactorsHelper m b l) : FactorsHelper n a (b :: l) := fun pa =>
  have pb : b.Prime := Nat.prime_def_minFac.2 ⟨le_trans pa.two_le h₂, h₃⟩
  let ⟨f₁, f₂, f₃⟩ := H pb
  ⟨List.Chain.cons h₂ f₁,
    fun _ h => (List.eq_or_mem_of_mem_cons h).elim (fun e => e.symm ▸ pb) (f₂ _),
    by rw [List.prod_cons, f₃, h₁.out, cast_id]⟩

theorem factorsHelper_cons (n m a b : ℕ) (l : List ℕ) (h₁ : IsNat (b * m) n) (h₂ : a < b)
    (h₃ : minFac b = b) (H : FactorsHelper m b l) : FactorsHelper n a (b :: l) :=
  factorsHelper_cons' _ _ _ _ _ h₁ h₂.le h₃ H

theorem factorsHelper_sn (n a : ℕ) (h₁ : a < n) (h₂ : minFac n = n) : FactorsHelper n a [n] :=
  factorsHelper_cons _ _ _ _ _ ⟨mul_one _⟩ h₁ h₂ (factorsHelper_nil _)

theorem factorsHelper_same (n m a : ℕ) (l : List ℕ)
    (h : IsNat (a * m) n) (H : FactorsHelper m a l) :
    FactorsHelper n a (a :: l) := fun pa =>
  factorsHelper_cons' _ _ _ _ _ h le_rfl (Nat.prime_def_minFac.1 pa).2 H pa

theorem factorsHelper_same_sn (a : ℕ) : FactorsHelper a a [a] :=
  factorsHelper_same _ _ _ _ ⟨mul_one _⟩ (factorsHelper_nil _)

theorem factorsHelper_end (n : ℕ) (l : List ℕ) (H : FactorsHelper n 2 l) :
    Nat.primeFactorsList n = l :=
  let ⟨h₁, h₂, h₃⟩ := H Nat.prime_two
  have := List.chain'_iff_pairwise.1 (@List.Chain'.tail _ _ (_ :: _) h₁)
  (List.eq_of_perm_of_sorted
    (Nat.primeFactorsList_unique h₃ h₂) this (Nat.primeFactorsList_sorted _)).symm

open Lean Elab Tactic Qq

/-- Given `n` and `a` natural numerals, returns `(l, ⊢ factorsHelper n a l)`. -/
def prove_factors_aux {en n' : Q(ℕ)} {ea a' : Q(ℕ)} (hn : Q(IsNat $en $n')) (ha : Q(IsNat $ea $a')) :
  MetaM ((l : Q(List ℕ)) × Q(FactorsHelper $en $ea $l)) := do
  let n := n'.natLit!
  let a := a'.natLit!
  let b := n.minFac
  if b < n then
    have m := n / b
    have em : Q(ℕ) := mkRawNatLit m
    have hm : Q(IsNat $em $em) := q(⟨rfl⟩)
    if b = a then
      let hp₁ := q(isNat_mul rfl $ha $hm)
      let ⟨l, p₂⟩ ← prove_factors_aux hm ha
      pure ⟨q($ea :: $l), q(factorsHelper_same $en $em $ea $l $p₁ $p₂)⟩
    else
      have eb : Q(ℕ) := mkRawNatLit b
      have hb : Q(IsNat $eb $eb) := q(⟨rfl⟩)
      let hp₁ := q(isNat_mul rfl $hb $hm)
      let (p₂) ← prove_lt_nat ea eb
      let (_, p₃) ← prove_min_fac eb
      let ⟨l, p₄⟩ ← prove_factors_aux em eb m b
      pure ⟨q($eb :: $l), q(factorsHelper_cons $en $em $ea $eb $l $p₁ $p₂ $p₃ $p₄)⟩
  else if b = a then
    pure ⟨q([$ea]), q(factorsHelper_same_sn $ea)⟩
  else do
    let (p₁) ← prove_lt_nat ea en
    let (_, p₂) ← prove_min_fac en
    pure ⟨q([$en]), q(factorsHelper_sn $en $ea $p₁ $p₂)⟩

end Mathlib.Meta.NormNum

open Qq Mathlib.Meta.NormNum

simproc Nat.primeFactorsList_ofNat (Nat.primeFactorsList _) := fun e => do
  let ⟨1, ~q(List ℕ), ~q(Nat.primeFactorsList (OfNat.ofNat $e))⟩ ← inferTypeQ e | return .continue
  let n := e.natLit!
  let hn : Q(IsNat $e $e) := q(⟨rfl⟩) -- TODO: one `e` should include `ofNat`
  match n with
  | 0 => return .done { expr := q([] : List ℕ), proof? := q(Nat.primeFactorsList_zero) }
  | 1 => return .done { expr := q([] : List ℕ), proof? := q(Nat.primeFactorsList_one) }
  | _ => do
    let ⟨l, p⟩ ← Mathlib.Meta.NormNum.prove_factors_aux hn q(⟨Eq.refl 2⟩)
    return .done { expr := l, proof? := q(factorsHelper_end $e $l $p) }
