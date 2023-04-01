/-
Copyright (c) 2022 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster

! This file was ported from Lean 3 source module algebra.char_p.mixed_char_zero
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.LocalRing
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.Tactic.FieldSimp

/-!
# Equal and mixed characteristic

In commutative algebra, some statments are simpler when working over a `ℚ`-algebra `R`, in which
case one also says that the ring has "equal characteristic zero". A ring that is not a
`ℚ`-algebra has either positive characteristic or there exists a prime ideal `I ⊂ R` such that
the quotient `R ⧸ I` has positive characteristic `p > 0`. In this case one speaks of
"mixed characteristic `(0, p)`", where `p` is only unique if `R` is local.

Examples of mixed characteristic rings are `ℤ` or the `p`-adic integers/numbers.

This file provides the main theorem `split_by_characteristic` that splits any proposition `P` into
the following three cases:

1) Positive characteristic: `char_p R p` (where `p ≠ 0`)
2) Equal characteristic zero: `algebra ℚ R`
3) Mixed characteristic: `mixed_char_zero R p` (where `p` is prime)

## Main definitions

- `mixed_char_zero` : A ring has mixed characteristic `(0, p)` if it has characteristic zero
  and there exists an ideal such that the quotient `R ⧸ I` has characteristic `p`.

## Main results

- `split_equal_mixed_char` : Split a statement into equal/mixed characteristic zero.

This main theorem has the following three corollaries which include the positive
characteristic case for convenience:

- `split_by_characteristic` : Generally consider positive char `p ≠ 0`.
- `split_by_characteristic_domain` : In a domain we can assume that `p` is prime.
- `split_by_characteristic_local_ring` : In a local ring we can assume that `p` is a prime power.

## TODO

- Relate mixed characteristic in a local ring to p-adic numbers [number_theory.padics].

-/


variable (R : Type _) [CommRing R]

/-!
### Mixed characteristic
-/


/-- A ring of characteristic zero is of "mixed characteristic `(0, p)`" if there exists an ideal
such that the quotient `R ⧸ I` has caracteristic `p`.

**Remark:** For `p = 0`, `mixed_char R 0` is a meaningless definition as `R ⧸ ⊥ ≅ R` has by
definition always characteristic zero.
One could require `(I ≠ ⊥)` in the definition, but then `mixed_char R 0` would mean something
like `ℤ`-algebra of extension degree `≥ 1` and would be completely independent from
whether something is a `ℚ`-algebra or not (e.g. `ℚ[X]` would satisfy it but `ℚ` wouldn't).
-/
class MixedCharZero (p : ℕ) : Prop where
  [to_charZero : CharZero R]
  charP_quotient : ∃ I : Ideal R, I ≠ ⊤ ∧ CharP (R ⧸ I) p
#align mixed_char_zero MixedCharZero

namespace MixedCharZero

/-- Reduction to `p` prime: When proving any statement `P` about mixed characteristic rings we
can always assume that `p` is prime.
-/
theorem reduce_to_p_prime {P : Prop} :
    (∀ p > 0, MixedCharZero R p → P) ↔ ∀ p : ℕ, p.Prime → MixedCharZero R p → P := by
  constructor
  · intro h q q_prime q_mixed_char
    exact h q (Nat.Prime.pos q_prime) q_mixed_char
  · intro h q q_pos q_mixed_char
    rcases q_mixed_char.char_p_quotient with ⟨I, hI_ne_top, hI_char⟩
    -- Krull's Thm: There exists a prime ideal `P` such that `I ≤ P`
    rcases Ideal.exists_le_maximal I hI_ne_top with ⟨M, hM_max, h_IM⟩
    skip
    -- make `hI_char : char_p (R ⧸ I) q` an instance.
    let r := ringChar (R ⧸ M)
    have r_pos : r ≠ 0 := by
      have q_zero := congr_arg (Ideal.Quotient.factor I M h_IM) (CharP.cast_eq_zero (R ⧸ I) q)
      simp only [map_natCast, map_zero] at q_zero
      apply ne_zero_of_dvd_ne_zero (ne_of_gt q_pos)
      exact (CharP.cast_eq_zero_iff (R ⧸ M) r q).mp q_zero
    have r_prime : Nat.Prime r :=
      or_iff_not_imp_right.1 (CharP.char_is_prime_or_zero (R ⧸ M) r) r_pos
    apply h r r_prime
    haveI : CharZero R := q_mixed_char.to_char_zero
    exact ⟨⟨M, hM_max.ne_top, ringChar.of_eq rfl⟩⟩
#align mixed_char_zero.reduce_to_p_prime MixedCharZero.reduce_to_p_prime

/-- Reduction to `I` prime ideal: When proving statements about mixed characteristic rings,
after we reduced to `p` prime, we can assume that the ideal `I` in the definition is maximal.
-/
theorem reduce_to_maximal_ideal {p : ℕ} (hp : Nat.Prime p) :
    (∃ I : Ideal R, I ≠ ⊤ ∧ CharP (R ⧸ I) p) ↔ ∃ I : Ideal R, I.IsMaximal ∧ CharP (R ⧸ I) p := by
  constructor
  · intro g
    rcases g with ⟨I, ⟨hI_not_top, hI⟩⟩
    -- Krull's Thm: There exists a prime ideal `M` such that `I ≤ M`.
    rcases Ideal.exists_le_maximal I hI_not_top with ⟨M, ⟨hM_max, hM⟩⟩
    use M
    constructor
    exact hM_max
    · cases' CharP.exists (R ⧸ M) with r hr
      convert hr
      skip
      -- make `hr : char_p (R ⧸ M) r` an instance.
      have r_dvd_p : r ∣ p := by
        rw [← CharP.cast_eq_zero_iff (R ⧸ M) r p]
        convert congr_arg (Ideal.Quotient.factor I M hM) (CharP.cast_eq_zero (R ⧸ I) p)
      symm
      apply (Nat.Prime.eq_one_or_self_of_dvd hp r r_dvd_p).resolve_left
      exact CharP.char_ne_one (R ⧸ M) r
  · rintro ⟨I, hI_max, hI⟩
    use I
    exact ⟨Ideal.IsMaximal.ne_top hI_max, hI⟩
#align mixed_char_zero.reduce_to_maximal_ideal MixedCharZero.reduce_to_maximal_ideal

end MixedCharZero

/-!
### Equal characteristic zero

A commutative ring `R` has "equal characteristic zero" if it satisfies one of the following
equivalent properties:

1) `R` is a `ℚ`-algebra.
2) The quotient `R ⧸ I` has characteristic zero for any proper ideal `I ⊂ R`.
3) `R` has characteristic zero and does not have mixed characteristic for any prime `p`.

We show `(1) ↔ (2) ↔ (3)`, and most of the following is concerned with constructing
an explicit algebra map `ℚ →+* R` (given by `x ↦ (x.num : R) /ₚ ↑x.pnat_denom`)
for the direction `(1) ← (2)`.

Note: Property `(2)` is denoted as `equal_char_zero` in the statement names below.
-/


section EqualCharZero

-- argument `[nontrivial R]` is used in the first line of the proof.
/-- `ℚ`-algebra implies equal characteristic.
-/
@[nolint unused_arguments]
theorem Q_algebra_to_equal_charZero [Nontrivial R] [Algebra ℚ R] :
    ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
  haveI : CharZero R := algebraRat.charZero R
  intro I hI
  constructor
  intro a b h_ab
  contrapose! hI
  -- `↑a - ↑b` is a unit contained in `I`, which contradicts `I ≠ ⊤`.
  refine' I.eq_top_of_is_unit_mem _ (IsUnit.map (algebraMap ℚ R) (IsUnit.mk0 (a - b : ℚ) _))
  · simpa only [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_natCast]
  simpa only [Ne.def, sub_eq_zero] using (@Nat.cast_injective ℚ _ _).Ne hI
#align Q_algebra_to_equal_char_zero Q_algebra_to_equal_charZero

section ConstructionOfQAlgebra

/-- Internal: Not intended to be used outside this local construction. -/
theorem EqualCharZero.pNat_coe_isUnit [h : Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))]
    (n : ℕ+) : IsUnit (n : R) := by
  -- `n : R` is a unit iff `(n)` is not a proper ideal in `R`.
  rw [← Ideal.span_singleton_eq_top]
  -- So by contrapositive, we should show the quotient does not have characteristic zero.
  apply not_imp_comm.mp (h.elim (Ideal.span {n}))
  intro h_char_zero
  -- In particular, the image of `n` in the quotient should be nonzero.
  apply h_char_zero.cast_injective.Ne n.ne_zero
  -- But `n` generates the ideal, so its image is clearly zero.
  rw [← map_natCast (Ideal.Quotient.mk _), Nat.cast_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)
#align equal_char_zero.pnat_coe_is_unit EqualCharZero.pNat_coe_isUnit

/-- Internal: Not intended to be used outside this local construction. -/
noncomputable instance EqualCharZero.pnatHasCoeUnits
    [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] : CoeTC ℕ+ Rˣ :=
  ⟨fun n => (EqualCharZero.pNat_coe_isUnit R n).Unit⟩
#align equal_char_zero.pnat_has_coe_units EqualCharZero.pnatHasCoeUnits

/-- Internal: Not intended to be used outside this local construction. -/
theorem EqualCharZero.pNat_coe_units_eq_one [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] :
    ((1 : ℕ+) : Rˣ) = 1 := by
  apply Units.ext
  rw [Units.val_one]
  change ((EqualCharZero.pNat_coe_isUnit R 1).Unit : R) = 1
  rw [IsUnit.unit_spec (EqualCharZero.pNat_coe_isUnit R 1)]
  rw [coe_coe, PNat.one_coe, Nat.cast_one]
#align equal_char_zero.pnat_coe_units_eq_one EqualCharZero.pNat_coe_units_eq_one

/-- Internal: Not intended to be used outside this local construction. -/
theorem EqualCharZero.pNat_coe_units_coe_eq_coe [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))]
    (n : ℕ+) : ((n : Rˣ) : R) = ↑n := by
  change ((EqualCharZero.pNat_coe_isUnit R n).Unit : R) = ↑n
  simp only [IsUnit.unit_spec]
#align equal_char_zero.pnat_coe_units_coe_eq_coe EqualCharZero.pNat_coe_units_coe_eq_coe

/-- Equal characteristic implies `ℚ`-algebra.
-/
noncomputable def equalCharZeroToQAlgebra (h : ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) :
    Algebra ℚ R :=
  haveI : Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) := ⟨h⟩
  RingHom.toAlgebra
    { toFun := fun x => x.num /ₚ ↑x.pnatDen
      map_zero' := by simp [divp]
      map_one' := by simp [EqualCharZero.pNat_coe_units_eq_one]
      map_mul' := by
        intro a b
        field_simp
        repeat' rw [EqualCharZero.pNat_coe_units_coe_eq_coe R]
        trans (↑((a * b).num * a.denom * b.denom) : R)
        · simp_rw [Int.cast_mul, Int.cast_ofNat, coe_coe, Rat.coe_pnatDen]
          ring
        rw [Rat.mul_num_den' a b]
        simp
      map_add' := by
        intro a b
        field_simp
        repeat' rw [EqualCharZero.pNat_coe_units_coe_eq_coe R]
        trans (↑((a + b).num * a.denom * b.denom) : R)
        · simp_rw [Int.cast_mul, Int.cast_ofNat, coe_coe, Rat.coe_pnatDen]
          ring
        rw [Rat.add_num_den' a b]
        simp }
#align equal_char_zero_to_Q_algebra equalCharZeroToQAlgebra

end ConstructionOfQAlgebra

end EqualCharZero

/-- Not mixed characteristic implies equal characteristic.
-/
theorem not_mixed_char_to_equal_charZero [CharZero R] (h : ∀ p > 0, ¬MixedCharZero R p) :
    ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
  intro I hI_ne_top
  apply CharP.charP_to_charZero _
  cases' CharP.exists (R ⧸ I) with p hp
  cases p
  · exact hp
  · have h_mixed : MixedCharZero R p.succ := ⟨⟨I, ⟨hI_ne_top, hp⟩⟩⟩
    exact absurd h_mixed (h p.succ p.succ_pos)
#align not_mixed_char_to_equal_char_zero not_mixed_char_to_equal_charZero

/-- Equal characteristic implies not mixed characteristic.
-/
theorem equal_charZero_to_not_mixed_char (h : ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) :
    ∀ p > 0, ¬MixedCharZero R p := by
  intro p p_pos
  by_contra hp_mixed_char
  rcases hp_mixed_char.char_p_quotient with ⟨I, hI_ne_top, hI_p⟩
  replace hI_zero : CharP (R ⧸ I) 0 := @CharP.ofCharZero _ _ (h I hI_ne_top)
  exact absurd (CharP.eq (R ⧸ I) hI_p hI_zero) (ne_of_gt p_pos)
#align equal_char_zero_to_not_mixed_char equal_charZero_to_not_mixed_char

/-- A ring of characteristic zero has equal characteristic iff it does not
have mixed characteristic for any `p`.
-/
theorem equal_charZero_iff_not_mixed_char [CharZero R] :
    (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) ↔ ∀ p > 0, ¬MixedCharZero R p :=
  ⟨equal_charZero_to_not_mixed_char R, not_mixed_char_to_equal_charZero R⟩
#align equal_char_zero_iff_not_mixed_char equal_charZero_iff_not_mixed_char

/-- A ring is a `ℚ`-algebra iff it has equal characteristic zero.
-/
theorem Q_algebra_iff_equal_charZero [Nontrivial R] :
    Nonempty (Algebra ℚ R) ↔ ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
  constructor
  · intro h_alg
    haveI h_alg' : Algebra ℚ R := h_alg.some
    apply Q_algebra_to_equal_charZero
  · intro h
    apply Nonempty.intro
    exact equalCharZeroToQAlgebra R h
#align Q_algebra_iff_equal_char_zero Q_algebra_iff_equal_charZero

/-- A ring of characteristic zero is not a `ℚ`-algebra iff it has mixed characteristic for some `p`.
-/
theorem not_Q_algebra_iff_not_equal_charZero [CharZero R] :
    IsEmpty (Algebra ℚ R) ↔ ∃ p > 0, MixedCharZero R p := by
  rw [← not_iff_not]
  push_neg
  rw [not_isEmpty_iff, ← equal_charZero_iff_not_mixed_char]
  apply Q_algebra_iff_equal_charZero
#align not_Q_algebra_iff_not_equal_char_zero not_Q_algebra_iff_not_equal_charZero

/-!
# Splitting statements into different characteristic

Statements to split a proof by characteristic. There are 3 theorems here that are very
similar. They only differ in the assumptions we can make on the positive characteristic
case:
Generally we need to consider all `p ≠ 0`, but if `R` is a local ring, we can assume
that `p` is a prime power. And if `R` is a domain, we can even assume that `p` is prime.
-/


section MainStatements

variable {P : Prop}

/-- Split a `Prop` in characteristic zero into equal and mixed characteristic.
-/
theorem split_equal_mixed_char [CharZero R] (h_equal : Algebra ℚ R → P)
    (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  by_cases h : ∃ p > 0, MixedCharZero R p
  · rcases h with ⟨p, ⟨H, hp⟩⟩
    rw [← MixedCharZero.reduce_to_p_prime] at h_mixed
    exact h_mixed p H hp
  · apply h_equal
    rw [← not_Q_algebra_iff_not_equal_charZero, not_isEmpty_iff] at h
    exact h.some
#align split_equal_mixed_char split_equal_mixed_char

example (n : ℕ) (h : n ≠ 0) : 0 < n :=
  zero_lt_iff.mpr h

/-- Split any `Prop` over `R` into the three cases:
- positive characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
theorem split_by_characteristic (h_pos : ∀ p : ℕ, p ≠ 0 → CharP R p → P) (h_equal : Algebra ℚ R → P)
    (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  cases' CharP.exists R with p p_char
  by_cases p = 0
  · rw [h] at p_char
    skip
    -- make `p_char : char_p R 0` an instance.
    haveI h0 : CharZero R := CharP.charP_to_charZero R
    exact split_equal_mixed_char R h_equal h_mixed
  exact h_pos p h p_char
#align split_by_characteristic split_by_characteristic

/-- In a `is_domain R`, split any `Prop` over `R` into the three cases:
- *prime* characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
theorem split_by_characteristic_domain [IsDomain R] (h_pos : ∀ p : ℕ, Nat.Prime p → CharP R p → P)
    (h_equal : Algebra ℚ R → P) (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  refine' split_by_characteristic R _ h_equal h_mixed
  intro p p_pos p_char
  have p_prime : Nat.Prime p := or_iff_not_imp_right.mp (CharP.char_is_prime_or_zero R p) p_pos
  exact h_pos p p_prime p_char
#align split_by_characteristic_domain split_by_characteristic_domain

/-- In a `local_ring R`, split any `Prop` over `R` into the three cases:
- *prime power* characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
theorem split_by_characteristic_localRing [LocalRing R]
    (h_pos : ∀ p : ℕ, IsPrimePow p → CharP R p → P) (h_equal : Algebra ℚ R → P)
    (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  refine' split_by_characteristic R _ h_equal h_mixed
  intro p p_pos p_char
  have p_ppow : IsPrimePow (p : ℕ) := or_iff_not_imp_left.mp (charP_zero_or_prime_power R p) p_pos
  exact h_pos p p_ppow p_char
#align split_by_characteristic_local_ring split_by_characteristic_localRing

end MainStatements

