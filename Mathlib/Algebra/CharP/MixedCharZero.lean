/-
Copyright (c) 2022 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.LocalRing
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.Tactic.FieldSimp

#align_import algebra.char_p.mixed_char_zero from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Equal and mixed characteristic

In commutative algebra, some statements are simpler when working over a `ℚ`-algebra `R`, in which
case one also says that the ring has "equal characteristic zero". A ring that is not a
`ℚ`-algebra has either positive characteristic or there exists a prime ideal `I ⊂ R` such that
the quotient `R ⧸ I` has positive characteristic `p > 0`. In this case one speaks of
"mixed characteristic `(0, p)`", where `p` is only unique if `R` is local.

Examples of mixed characteristic rings are `ℤ` or the `p`-adic integers/numbers.

This file provides the main theorem `split_by_characteristic` that splits any proposition `P` into
the following three cases:

1) Positive characteristic: `CharP R p` (where `p ≠ 0`)
2) Equal characteristic zero: `Algebra ℚ R`
3) Mixed characteristic: `MixedCharZero R p` (where `p` is prime)

## Main definitions

- `MixedCharZero` : A ring has mixed characteristic `(0, p)` if it has characteristic zero
  and there exists an ideal such that the quotient `R ⧸ I` has characteristic `p`.

## Main results

- `split_equalCharZero_mixedCharZero` : Split a statement into equal/mixed characteristic zero.

This main theorem has the following three corollaries which include the positive
characteristic case for convenience:

- `split_by_characteristic` : Generally consider positive char `p ≠ 0`.
- `split_by_characteristic_domain` : In a domain we can assume that `p` is prime.
- `split_by_characteristic_localRing` : In a local ring we can assume that `p` is a prime power.

## Implementation Notes

We use the terms `EqualCharZero` and `AlgebraRat` despite not being such definitions in mathlib.
The former refers to the statement `∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)`, the latter
refers to the existence of an instance `[Algebra ℚ R]`. The two are shown to be
equivalent conditions.

## TODO

- Relate mixed characteristic in a local ring to p-adic numbers [NumberTheory.PAdics].
-/

variable (R : Type*) [CommRing R]

/-!
### Mixed characteristic
-/

/--
A ring of characteristic zero is of "mixed characteristic `(0, p)`" if there exists an ideal
such that the quotient `R ⧸ I` has characteristic `p`.

**Remark:** For `p = 0`, `MixedChar R 0` is a meaningless definition (i.e. satisfied by any ring)
as `R ⧸ ⊥ ≅ R` has by definition always characteristic zero.
One could require `(I ≠ ⊥)` in the definition, but then `MixedChar R 0` would mean something
like `ℤ`-algebra of extension degree `≥ 1` and would be completely independent from
whether something is a `ℚ`-algebra or not (e.g. `ℚ[X]` would satisfy it but `ℚ` wouldn't).
-/
class MixedCharZero (p : ℕ) : Prop where
  [toCharZero : CharZero R]
  charP_quotient : ∃ I : Ideal R, I ≠ ⊤ ∧ CharP (R ⧸ I) p
#align mixed_char_zero MixedCharZero

namespace MixedCharZero

/--
Reduction to `p` prime: When proving any statement `P` about mixed characteristic rings we
can always assume that `p` is prime.
-/
theorem reduce_to_p_prime {P : Prop} :
    (∀ p > 0, MixedCharZero R p → P) ↔ ∀ p : ℕ, p.Prime → MixedCharZero R p → P := by
  constructor
  -- ⊢ (∀ (p : ℕ), p > 0 → MixedCharZero R p → P) → ∀ (p : ℕ), Nat.Prime p → MixedC …
  · intro h q q_prime q_mixedChar
    -- ⊢ P
    exact h q (Nat.Prime.pos q_prime) q_mixedChar
    -- 🎉 no goals
  · intro h q q_pos q_mixedChar
    -- ⊢ P
    rcases q_mixedChar.charP_quotient with ⟨I, hI_ne_top, _⟩
    -- ⊢ P
    -- Krull's Thm: There exists a prime ideal `P` such that `I ≤ P`
    rcases Ideal.exists_le_maximal I hI_ne_top with ⟨M, hM_max, h_IM⟩
    -- ⊢ P
    let r := ringChar (R ⧸ M)
    -- ⊢ P
    have r_pos : r ≠ 0
    -- ⊢ r ≠ 0
    · have q_zero :=
        congr_arg (Ideal.Quotient.factor I M h_IM) (CharP.cast_eq_zero (R ⧸ I) q)
      simp only [map_natCast, map_zero] at q_zero
      -- ⊢ r ≠ 0
      apply ne_zero_of_dvd_ne_zero (ne_of_gt q_pos)
      -- ⊢ r ∣ q
      exact (CharP.cast_eq_zero_iff (R ⧸ M) r q).mp q_zero
      -- 🎉 no goals
    have r_prime : Nat.Prime r :=
      or_iff_not_imp_right.1 (CharP.char_is_prime_or_zero (R ⧸ M) r) r_pos
    apply h r r_prime
    -- ⊢ MixedCharZero R r
    have : CharZero R := q_mixedChar.toCharZero
    -- ⊢ MixedCharZero R r
    exact ⟨⟨M, hM_max.ne_top, ringChar.of_eq rfl⟩⟩
    -- 🎉 no goals
#align mixed_char_zero.reduce_to_p_prime MixedCharZero.reduce_to_p_prime

/--
Reduction to `I` prime ideal: When proving statements about mixed characteristic rings,
after we reduced to `p` prime, we can assume that the ideal `I` in the definition is maximal.
-/
theorem reduce_to_maximal_ideal {p : ℕ} (hp : Nat.Prime p) :
    (∃ I : Ideal R, I ≠ ⊤ ∧ CharP (R ⧸ I) p) ↔ ∃ I : Ideal R, I.IsMaximal ∧ CharP (R ⧸ I) p := by
  constructor
  -- ⊢ (∃ I, I ≠ ⊤ ∧ CharP (R ⧸ I) p) → ∃ I, Ideal.IsMaximal I ∧ CharP (R ⧸ I) p
  · intro g
    -- ⊢ ∃ I, Ideal.IsMaximal I ∧ CharP (R ⧸ I) p
    rcases g with ⟨I, ⟨hI_not_top, _⟩⟩
    -- ⊢ ∃ I, Ideal.IsMaximal I ∧ CharP (R ⧸ I) p
    -- Krull's Thm: There exists a prime ideal `M` such that `I ≤ M`.
    rcases Ideal.exists_le_maximal I hI_not_top with ⟨M, ⟨hM_max, hM_ge⟩⟩
    -- ⊢ ∃ I, Ideal.IsMaximal I ∧ CharP (R ⧸ I) p
    use M
    -- ⊢ Ideal.IsMaximal M ∧ CharP (R ⧸ M) p
    constructor
    -- ⊢ Ideal.IsMaximal M
    · exact hM_max
      -- 🎉 no goals
    · cases CharP.exists (R ⧸ M) with
      | intro r hr =>
        -- Porting note: This is odd. Added `have hr := hr`.
        -- Without this it seems that lean does not find `hr` as an instance.
        have hr := hr
        convert hr
        have r_dvd_p : r ∣ p
        · rw [← CharP.cast_eq_zero_iff (R ⧸ M) r p]
          convert congr_arg (Ideal.Quotient.factor I M hM_ge) (CharP.cast_eq_zero (R ⧸ I) p)
        symm
        apply (Nat.Prime.eq_one_or_self_of_dvd hp r r_dvd_p).resolve_left
        exact CharP.char_ne_one (R ⧸ M) r
  · intro ⟨I, hI_max, h_charP⟩
    -- ⊢ ∃ I, I ≠ ⊤ ∧ CharP (R ⧸ I) p
    use I
    -- ⊢ I ≠ ⊤ ∧ CharP (R ⧸ I) p
    exact ⟨Ideal.IsMaximal.ne_top hI_max, h_charP⟩
    -- 🎉 no goals
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
an explicit algebra map `ℚ →+* R` (given by `x ↦ (x.num : R) /ₚ ↑x.pnatDen`)
for the direction `(1) ← (2)`.

Note: Property `(2)` is denoted as `EqualCharZero` in the statement names below.
-/

namespace EqualCharZero

/-- `ℚ`-algebra implies equal characteristic. -/
theorem of_algebraRat [Algebra ℚ R] : ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
  intro I hI
  -- ⊢ CharZero (R ⧸ I)
  constructor
  -- ⊢ Function.Injective Nat.cast
  intro a b h_ab
  -- ⊢ a = b
  contrapose! hI
  -- ⊢ I = ⊤
  -- `↑a - ↑b` is a unit contained in `I`, which contradicts `I ≠ ⊤`.
  refine' I.eq_top_of_isUnit_mem _ (IsUnit.map (algebraMap ℚ R) (IsUnit.mk0 (a - b : ℚ) _))
  -- ⊢ ↑(algebraMap ℚ R) (↑a - ↑b) ∈ I
  · simpa only [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_natCast]
    -- 🎉 no goals
  simpa only [Ne.def, sub_eq_zero] using (@Nat.cast_injective ℚ _ _).ne hI
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Q_algebra_to_equal_char_zero EqualCharZero.of_algebraRat

section ConstructionAlgebraRat

variable {R}

/-- Internal: Not intended to be used outside this local construction. -/
theorem PNat.isUnit_natCast [h : Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))]
    (n : ℕ+) : IsUnit (n : R) := by
  -- `n : R` is a unit iff `(n)` is not a proper ideal in `R`.
  rw [← Ideal.span_singleton_eq_top]
  -- ⊢ Ideal.span {↑↑n} = ⊤
  -- So by contrapositive, we should show the quotient does not have characteristic zero.
  apply not_imp_comm.mp (h.elim (Ideal.span {↑n}))
  -- ⊢ ¬CharZero (R ⧸ Ideal.span {↑↑n})
  intro h_char_zero
  -- ⊢ False
  -- In particular, the image of `n` in the quotient should be nonzero.
  apply h_char_zero.cast_injective.ne n.ne_zero
  -- ⊢ ↑↑n = ↑0
  -- But `n` generates the ideal, so its image is clearly zero.
  rw [← map_natCast (Ideal.Quotient.mk _), Nat.cast_zero, Ideal.Quotient.eq_zero_iff_mem]
  -- ⊢ ↑↑n ∈ Ideal.span {↑↑n}
  exact Ideal.subset_span (Set.mem_singleton _)
  -- 🎉 no goals
#align equal_char_zero.pnat_coe_is_unit EqualCharZero.PNat.isUnit_natCast

@[coe]
noncomputable def pnatCast [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] : ℕ+ → Rˣ :=
  fun n => (PNat.isUnit_natCast n).unit

/-- Internal: Not intended to be used outside this local construction. -/
noncomputable instance coePNatUnits
    [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] : Coe ℕ+ Rˣ :=
  ⟨EqualCharZero.pnatCast⟩
#align equal_char_zero.pnat_has_coe_units EqualCharZero.coePNatUnits

/-- Internal: Not intended to be used outside this local construction. -/
@[simp]
theorem pnatCast_one [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] : ((1 : ℕ+) : Rˣ) = 1 := by
  apply Units.ext
  -- ⊢ ↑↑1 = ↑1
  rw [Units.val_one]
  -- ⊢ ↑↑1 = 1
  change ((PNat.isUnit_natCast (R := R) 1).unit : R) = 1
  -- ⊢ ↑(IsUnit.unit (_ : IsUnit ↑↑1)) = 1
  rw [IsUnit.unit_spec (PNat.isUnit_natCast 1)]
  -- ⊢ ↑↑1 = 1
  rw [PNat.one_coe, Nat.cast_one]
  -- 🎉 no goals
#align equal_char_zero.pnat_coe_units_eq_one EqualCharZero.pnatCast_one

/-- Internal: Not intended to be used outside this local construction. -/
@[simp]
theorem pnatCast_eq_natCast [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] (n : ℕ+) :
    ((n : Rˣ) : R) = ↑n := by
  change ((PNat.isUnit_natCast (R := R) n).unit : R) = ↑n
  -- ⊢ ↑(IsUnit.unit (_ : IsUnit ↑↑n)) = ↑↑n
  simp only [IsUnit.unit_spec]
  -- 🎉 no goals
#align equal_char_zero.pnat_coe_units_coe_eq_coe EqualCharZero.pnatCast_eq_natCast

/-- Equal characteristic implies `ℚ`-algebra. -/
noncomputable def algebraRat (h : ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) :
    Algebra ℚ R :=
  haveI : Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) := ⟨h⟩
  RingHom.toAlgebra
  { toFun := fun x => x.num /ₚ ↑x.pnatDen
    map_zero' := by simp [divp]
                    -- 🎉 no goals
                   -- 🎉 no goals
    map_one' := by simp
    map_mul' := by
      -- ⊢ OneHom.toFun { toFun := fun x => ↑x.num /ₚ ↑(Rat.pnatDen x), map_one' := (_  …
      intro a b
      -- ⊢ ↑(a * b).num * (↑b.den * ↑a.den) = ↑a.num * ↑b.num * ↑(a * b).den
      field_simp
      -- ⊢ ↑(a * b).num * (↑b.den * ↑a.den) = ↑((a * b).num * ↑a.den * ↑b.den)
      trans (↑((a * b).num * a.den * b.den) : R)
        -- ⊢ ↑(a * b).num * (↑b.den * ↑a.den) = ↑(a * b).num * ↑a.den * ↑b.den
      · simp_rw [Int.cast_mul, Int.cast_ofNat]
        -- 🎉 no goals
        ring
      -- ⊢ ↑(a.num * b.num * ↑(a * b).den) = ↑a.num * ↑b.num * ↑(a * b).den
      rw [Rat.mul_num_den' a b]
      -- 🎉 no goals
      simp
    map_add' := by
      intro a b
      -- ⊢ OneHom.toFun (↑{ toOneHom := { toFun := fun x => ↑x.num /ₚ ↑(Rat.pnatDen x), …
      field_simp
      -- ⊢ ↑(a + b).num * (↑b.den * ↑a.den) = (↑a.num * ↑b.den + ↑b.num * ↑a.den) * ↑(a …
      trans (↑((a + b).num * a.den * b.den) : R)
      -- ⊢ ↑(a + b).num * (↑b.den * ↑a.den) = ↑((a + b).num * ↑a.den * ↑b.den)
      · simp_rw [Int.cast_mul, Int.cast_ofNat]
        -- ⊢ ↑(a + b).num * (↑b.den * ↑a.den) = ↑(a + b).num * ↑a.den * ↑b.den
        ring
        -- 🎉 no goals
      rw [Rat.add_num_den' a b]
      -- ⊢ ↑((a.num * ↑b.den + b.num * ↑a.den) * ↑(a + b).den) = (↑a.num * ↑b.den + ↑b. …
      simp }
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align equal_char_zero_to_Q_algebra EqualCharZero.algebraRat

end ConstructionAlgebraRat

/-- Not mixed characteristic implies equal characteristic. -/
theorem of_not_mixedCharZero [CharZero R] (h : ∀ p > 0, ¬MixedCharZero R p) :
    ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
  intro I hI_ne_top
  -- ⊢ CharZero (R ⧸ I)
  suffices h_charP : CharP (R ⧸ I) 0
  -- ⊢ CharZero (R ⧸ I)
  · apply CharP.charP_to_charZero
    -- 🎉 no goals
  cases CharP.exists (R ⧸ I) with
  | intro p hp =>
    cases p with
    | zero => exact hp
    | succ p =>
      have h_mixed : MixedCharZero R p.succ := ⟨⟨I, ⟨hI_ne_top, hp⟩⟩⟩
      exact absurd h_mixed (h p.succ p.succ_pos)
#align not_mixed_char_to_equal_char_zero EqualCharZero.of_not_mixedCharZero

/-- Equal characteristic implies not mixed characteristic. -/
theorem to_not_mixedCharZero (h : ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) :
    ∀ p > 0, ¬MixedCharZero R p := by
  intro p p_pos
  -- ⊢ ¬MixedCharZero R p
  by_contra hp_mixedChar
  -- ⊢ False
  rcases hp_mixedChar.charP_quotient with ⟨I, hI_ne_top, hI_p⟩
  -- ⊢ False
  replace hI_zero : CharP (R ⧸ I) 0 := @CharP.ofCharZero _ _ (h I hI_ne_top)
  -- ⊢ False
  exact absurd (CharP.eq (R ⧸ I) hI_p hI_zero) (ne_of_gt p_pos)
  -- 🎉 no goals
#align equal_char_zero_to_not_mixed_char EqualCharZero.to_not_mixedCharZero

/--
A ring of characteristic zero has equal characteristic iff it does not
have mixed characteristic for any `p`.
-/
theorem iff_not_mixedCharZero [CharZero R] :
    (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) ↔ ∀ p > 0, ¬MixedCharZero R p :=
  ⟨to_not_mixedCharZero R, of_not_mixedCharZero R⟩
#align equal_char_zero_iff_not_mixed_char EqualCharZero.iff_not_mixedCharZero

/-- A ring is a `ℚ`-algebra iff it has equal characteristic zero. -/
theorem nonempty_algebraRat_iff :
    Nonempty (Algebra ℚ R) ↔ ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
  constructor
  -- ⊢ Nonempty (Algebra ℚ R) → ∀ (I : Ideal R), I ≠ ⊤ → CharZero (R ⧸ I)
  · intro h_alg
    -- ⊢ ∀ (I : Ideal R), I ≠ ⊤ → CharZero (R ⧸ I)
    haveI h_alg' : Algebra ℚ R := h_alg.some
    -- ⊢ ∀ (I : Ideal R), I ≠ ⊤ → CharZero (R ⧸ I)
    apply of_algebraRat
    -- 🎉 no goals
  · intro h
    -- ⊢ Nonempty (Algebra ℚ R)
    apply Nonempty.intro
    -- ⊢ Algebra ℚ R
    exact algebraRat h
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Q_algebra_iff_equal_char_zero EqualCharZero.nonempty_algebraRat_iff

end EqualCharZero

/--
A ring of characteristic zero is not a `ℚ`-algebra iff it has mixed characteristic for some `p`.
-/
theorem isEmpty_algebraRat_iff_mixedCharZero [CharZero R] :
    IsEmpty (Algebra ℚ R) ↔ ∃ p > 0, MixedCharZero R p := by
  rw [← not_iff_not]
  -- ⊢ ¬IsEmpty (Algebra ℚ R) ↔ ¬∃ p, p > 0 ∧ MixedCharZero R p
  push_neg
  -- ⊢ ¬IsEmpty (Algebra ℚ R) ↔ ∀ (p : ℕ), p > 0 → ¬MixedCharZero R p
  rw [not_isEmpty_iff, ← EqualCharZero.iff_not_mixedCharZero]
  -- ⊢ Nonempty (Algebra ℚ R) ↔ ∀ (I : Ideal R), I ≠ ⊤ → CharZero (R ⧸ I)
  apply EqualCharZero.nonempty_algebraRat_iff
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align not_Q_algebra_iff_not_equal_char_zero isEmpty_algebraRat_iff_mixedCharZero

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

/-- Split a `Prop` in characteristic zero into equal and mixed characteristic. -/
theorem split_equalCharZero_mixedCharZero [CharZero R] (h_equal : Algebra ℚ R → P)
    (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  by_cases h : ∃ p > 0, MixedCharZero R p
  -- ⊢ P
  · rcases h with ⟨p, ⟨H, hp⟩⟩
    -- ⊢ P
    rw [← MixedCharZero.reduce_to_p_prime] at h_mixed
    -- ⊢ P
    exact h_mixed p H hp
    -- 🎉 no goals
  · apply h_equal
    -- ⊢ Algebra ℚ R
    rw [← isEmpty_algebraRat_iff_mixedCharZero, not_isEmpty_iff] at h
    -- ⊢ Algebra ℚ R
    exact h.some
    -- 🎉 no goals
#align split_equal_mixed_char split_equalCharZero_mixedCharZero

example (n : ℕ) (h : n ≠ 0) : 0 < n :=
  zero_lt_iff.mpr h

/--
Split any `Prop` over `R` into the three cases:
- positive characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
theorem split_by_characteristic (h_pos : ∀ p : ℕ, p ≠ 0 → CharP R p → P) (h_equal : Algebra ℚ R → P)
    (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  cases CharP.exists R with
  | intro p p_charP =>
    by_cases p = 0
    · rw [h] at p_charP
      haveI h0 : CharZero R := CharP.charP_to_charZero R
      exact split_equalCharZero_mixedCharZero R h_equal h_mixed
    · exact h_pos p h p_charP
#align split_by_characteristic split_by_characteristic

/--
In an `IsDomain R`, split any `Prop` over `R` into the three cases:
- *prime* characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
theorem split_by_characteristic_domain [IsDomain R] (h_pos : ∀ p : ℕ, Nat.Prime p → CharP R p → P)
    (h_equal : Algebra ℚ R → P) (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  refine split_by_characteristic R ?_ h_equal h_mixed
  -- ⊢ ∀ (p : ℕ), p ≠ 0 → CharP R p → P
  intro p p_pos p_char
  -- ⊢ P
  have p_prime : Nat.Prime p := or_iff_not_imp_right.mp (CharP.char_is_prime_or_zero R p) p_pos
  -- ⊢ P
  exact h_pos p p_prime p_char
  -- 🎉 no goals
#align split_by_characteristic_domain split_by_characteristic_domain

 /--
In a `LocalRing R`, split any `Prop` over `R` into the three cases:
- *prime power* characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
theorem split_by_characteristic_localRing [LocalRing R]
    (h_pos : ∀ p : ℕ, IsPrimePow p → CharP R p → P) (h_equal : Algebra ℚ R → P)
    (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  refine' split_by_characteristic R _ h_equal h_mixed
  -- ⊢ ∀ (p : ℕ), p ≠ 0 → CharP R p → P
  intro p p_pos p_char
  -- ⊢ P
  have p_ppow : IsPrimePow (p : ℕ) := or_iff_not_imp_left.mp (charP_zero_or_prime_power R p) p_pos
  -- ⊢ P
  exact h_pos p p_ppow p_char
  -- 🎉 no goals
#align split_by_characteristic_local_ring split_by_characteristic_localRing

end MainStatements
