/-
Copyright (c) 2025 Michal Staromiejski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Staromiejski
-/
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!

# The exponent of purely inseparable extensions

This file defines the exponent of a purely inseparable extension (if one exists) and
some related results.

Most results are stated using `ringExpChar K` rather than using `[ExpChar K p]` parameter because
it gives cleaner API. To use the results in a context with `[ExpChar K p]`, consider using
`ringExpChar.eq K p` for substitution.

## Main definitions

- `IsPurelyInseparable.HasExponent`: typeclass to assert a purely inseparable field extension
  `L / K` has an exponent, that is a smallest natural number `e` such that
  `a ^ ringExpChar K ^ e ∈ K` for all `a ∈ L`.
- `IsPurelyInseparable.exponent`: the exponent of a purely inseparable field extension.
- `IsPurelyInseparable.elemExponent`: the exponent of an element of a purely inseparable
  field extension, that is the smallest natural number `e` such that `a ^ ringExpChar K ^ e ∈ K`.
- `IsPurelyInseparable.iterateFrobenius`: the iterated Frobenius map (ring homomorphism) `L →+* K`
  for purely inseparable field extension `L / K` with exponent; for `n ≥ exponent K L`, it acts like
  `x ↦ x ^ p ^ n` but the codomain is the base field `K`.
- `IsPurelyInseparable.iterateFrobeniusₛₗ`: version of `iterateFrobenius` as a semilinear map over
  a subfield `F` of `K`, w.r.t. the iterated Frobenius homomorphism on `F`.

## Tags

purely inseparable

-/

namespace IsPurelyInseparable

variable (F K L : Type*)

section Ring

variable [CommRing K] [Ring L] [Algebra K L]

/-- A predicate class on a ring extension saying that there is a natural number `e`
such that `a ^ ringExpChar K ^ e ∈ K` for all `a ∈ L`. -/
@[mk_iff]
class HasExponent : Prop where
  has_exponent : ∃ e, ∀ a, a ^ ringExpChar K ^ e ∈ (algebraMap K L).range

/-- Version of `hasExponent_iff` using `ExpChar`. -/
theorem hasExponent_iff' (p : ℕ) [ExpChar K p] :
    HasExponent K L ↔ ∃ e, ∀ (a : L), a ^ p ^ e ∈ (algebraMap K L).range :=
  ringExpChar.eq K p ▸ hasExponent_iff K L

open scoped Classical in
/-- The *exponent* of a purely inseparable extension is the smallest
natural number `e` such that `a ^ ringExpChar K ^ e ∈ K` for all `a ∈ L`. -/
noncomputable def exponent [HasExponent K L] : ℕ :=
  Nat.find ‹HasExponent K L›.has_exponent

variable {L}

open Classical in
theorem exponent_def [HasExponent K L] (a : L) :
    a ^ ringExpChar K ^ exponent K L ∈ (algebraMap K L).range :=
  Nat.find_spec ‹HasExponent K L›.has_exponent a

/-- Version of `exponent_def` using `ExpChar`. -/
theorem exponent_def' [HasExponent K L] (p : ℕ) [ExpChar K p] (a : L) :
    a ^ p ^ exponent K L ∈ (algebraMap K L).range :=
  ringExpChar.eq K p ▸ exponent_def K a

variable {K}

open Classical in
theorem exponent_min [HasExponent K L] {e : ℕ} (h : e < exponent K L) :
    ∃ a, a ^ ringExpChar K ^ e ∉ (algebraMap K L).range :=
  not_forall.mp <| Nat.find_min ‹HasExponent K L›.has_exponent h

/-- Version of `exponent_min` using `ExpChar`. -/
theorem exponent_min' [HasExponent K L] (p : ℕ) [ExpChar K p] {e : ℕ} (h : e < exponent K L) :
    ∃ a, a ^ p ^ e ∉ (algebraMap K L).range :=
  ringExpChar.eq K p ▸ exponent_min h

end Ring

section IsDomain

variable [Field K] [Ring L] [IsDomain L] [Algebra K L]

instance [HasExponent K L] : IsPurelyInseparable K L :=
  let ⟨n, h⟩ := ‹HasExponent K L›.has_exponent
  (isPurelyInseparable_iff_pow_mem K (ringExpChar K)).mpr fun x ↦ ⟨n, h x⟩

end IsDomain

section Field

open Polynomial

variable [Field K] [Field L] [Algebra K L] [IsPurelyInseparable K L]
variable {L}

open Classical in
/-- The exponent of an element `a ∈ L` of a purely inseparable field extension `L / K`
is the smallest natural number `e` such that `a ^ ringExpChar K ^ e ∈ K`. -/
noncomputable def elemExponent (a : L) : ℕ :=
  Nat.find <| minpoly_eq_X_pow_sub_C K (ringExpChar K) a

open Classical in
variable {K} in
theorem elemExponent_eq_zero_of_mem_range {a : L} (h : a ∈ (algebraMap K L).range) :
    elemExponent K a = 0 := by
  apply (Nat.find_eq_zero _).mpr
  rw [pow_zero, pow_one]
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy ▸ minpoly.eq_X_sub_C L y⟩

theorem elemExponent_eq_zero_of_charZero (a : L) [CharZero K] :
    elemExponent K a = 0 :=
  elemExponent_eq_zero_of_mem_range <| surjective_algebraMap_of_isSeparable K L a

open Classical in
/-- The element `y` of the base field `K` such that
`a ^ ringExpChar K ^ elemExponent K a = algebraMap K L y`.
See `IsPurelyInseparable.algebraMap_elemReduct_eq`. -/
noncomputable def elemReduct (a : L) : K :=
  Classical.choose <| Nat.find_spec <| minpoly_eq_X_pow_sub_C K (ringExpChar K) a

open Classical in
theorem minpoly_eq (a : L) :
    minpoly K a = X ^ ringExpChar K ^ elemExponent K a - C (elemReduct K a) :=
  Classical.choose_spec <| Nat.find_spec <| minpoly_eq_X_pow_sub_C K (ringExpChar K) a

open Classical in
/-- Version of `minpoly_eq` using `ExpChar`. -/
theorem minpoly_eq' (p : ℕ) [ExpChar K p] (a : L) :
    minpoly K a = X ^ p ^ elemExponent K a - C (elemReduct K a) :=
  ringExpChar.eq K p ▸ minpoly_eq K a

/-- The degree of the minimal polynomial of an element `a ∈ L` equals
`ringExpChar K ^ elemExponent K a`. -/
theorem minpoly_natDegree_eq (a : L) :
    (minpoly K a).natDegree = ringExpChar K ^ elemExponent K a := by
  rw [minpoly_eq K a, natDegree_sub_C, natDegree_pow, natDegree_X, mul_one]

/-- Version of `minpoly_natDegree_eq` using `ExpChar`. -/
theorem minpoly_natDegree_eq' (p : ℕ) [ExpChar K p] (a : L) :
    (minpoly K a).natDegree = p ^ elemExponent K a :=
  ringExpChar.eq K p ▸ minpoly_natDegree_eq K a

theorem algebraMap_elemReduct_eq (a : L) :
    algebraMap K L (elemReduct K a) = a ^ ringExpChar K ^ elemExponent K a := by
  have := minpoly_eq K a ▸ minpoly.aeval K a
  rwa [map_sub, aeval_C, map_pow, aeval_X, sub_eq_zero, eq_comm] at this

/-- Version of `algebraMap_elemReduct_eq` using `ExpChar`. -/
theorem algebraMap_elemReduct_eq' (p : ℕ) [ExpChar K p] (a : L) :
    algebraMap K L (elemReduct K a) = a ^ p ^ elemExponent K a :=
  ringExpChar.eq K p ▸ algebraMap_elemReduct_eq K a

theorem elemExponent_def (a : L) :
    a ^ ringExpChar K ^ elemExponent K a ∈ (algebraMap K L).range :=
  RingHom.mem_range.mpr <| ⟨_, algebraMap_elemReduct_eq K a⟩

/-- Version of `elemExponent_def` using `ExpChar`. -/
theorem elemExponent_def' (p : ℕ) [ExpChar K p] (a : L) :
    a ^ p ^ elemExponent K a ∈ (algebraMap K L).range :=
  ringExpChar.eq K p ▸ elemExponent_def K a

variable {K} in
theorem elemExponent_le_of_pow_mem {a : L} {n : ℕ}
    (h : a ^ ringExpChar K ^ n ∈ (algebraMap K L).range) : elemExponent K a ≤ n := by
  let ⟨p, _⟩ := ExpChar.exists K
  rcases ‹ExpChar K p› with _ | ⟨hp⟩
  · exact elemExponent_eq_zero_of_charZero K a ▸ Nat.zero_le _
  · obtain ⟨y, hy⟩ := RingHom.mem_range.mp <| h
    let f := X ^ ringExpChar K ^ n - C y
    have hf₁ : f.aeval a = 0 := by rwa [map_sub, aeval_C, aeval_X_pow, sub_eq_zero, eq_comm]
    have hf₂ : f.Monic := monic_X_pow_sub_C y <| Nat.pos_iff_ne_zero.mp <| expChar_pow_pos K _ _
    have hf₃ : f.natDegree = ringExpChar K ^ n := by
      rw [natDegree_sub_C, natDegree_pow, natDegree_X, mul_one]
    exact (Nat.pow_le_pow_iff_right <| Nat.Prime.one_lt hp).mp <|
      ringExpChar.eq K p ▸ hf₃ ▸ minpoly_natDegree_eq K a ▸
      natDegree_le_natDegree (minpoly.min K a hf₂ hf₁)

variable {K} in
/-- Version of `elemExponent_le_of_pow_mem` using `ExpChar`. -/
theorem elemExponent_le_of_pow_mem' (p : ℕ) [ExpChar K p] {a : L} {n : ℕ}
    (h : a ^ p ^ n ∈ (algebraMap K L).range) : elemExponent K a ≤ n :=
  elemExponent_le_of_pow_mem (ringExpChar.eq K p ▸ h)

variable {K} in
theorem elemExponent_min {a : L} {n : ℕ} (h : n < elemExponent K a) :
    a ^ ringExpChar K ^ n ∉ (algebraMap K L).range :=
  fun hn ↦ (Nat.not_lt_of_ge <| elemExponent_le_of_pow_mem hn) h

/-- Version of `elemExponent_min` using `ExpChar`. -/
theorem elemExponent_min' (p : ℕ) [ExpChar K p] {a : L} {n : ℕ} (h : n < elemExponent K a) :
    a ^ p ^ n ∉ (algebraMap K L).range :=
  ringExpChar.eq K p ▸ elemExponent_min h

/-- An exponent of an element is less or equal than exponent of the extension. -/
theorem elemExponent_le_exponent [HasExponent K L] (a : L) :
    elemExponent K a ≤ exponent K L :=
  elemExponent_le_of_pow_mem <| exponent_def K a

variable {K} in
instance hasExponent_of_finiteDimensional [IsPurelyInseparable K L] [FiniteDimensional K L] :
    HasExponent K L := by
  let ⟨p, _⟩ := ExpChar.exists K
  rcases ‹ExpChar K p› with _ | ⟨hp⟩
  · exact ⟨0, fun a ↦ surjective_algebraMap_of_isSeparable K L _⟩
  · let e := Nat.log (ringExpChar K) (Module.finrank K L)
    refine ⟨e, fun a ↦ ⟨elemReduct K a ^ ringExpChar K ^ (e - elemExponent K a), ?_⟩⟩
    have h_elemexp_bound (a : L) : elemExponent K a ≤ e :=
      Nat.le_log_of_pow_le (Nat.Prime.one_lt <| ringExpChar.eq K p ▸ hp)
        (minpoly_natDegree_eq K a ▸ minpoly.natDegree_le a)
    rw [RingHom.map_pow, algebraMap_elemReduct_eq, ← pow_mul, ← pow_add,
      Nat.add_sub_cancel' (h_elemexp_bound a)]

end Field

section Frobenius

/-
This section defines the iterated Frobenius map `x ↦ x ^ p ^ n` for a purely inseparable
field extension `L / K` with exponent, with the base field `K` as a codomain, when
`n ≥ exponent K L`.
We define it both as a ring homomorphism and a semilinear map over a subfield `F` of `K`.

Implementation note: the API exposes arguments `{n : ℕ} (hn : exponent K L ≤ n)` to define the
action `x ↦ x ^ p ^ n` instead of just `(n : ℕ)` with action `x ↦ x ^ p ^ (exponent K L + n)`
to avoid problems with definitional equality when using the semilinear map version.
-/

variable [Field K] [Field L] [Algebra K L] [HasExponent K L]
variable (p : ℕ) [ExpChar K p]

private noncomputable def iterateFrobeniusAux (n : ℕ) : L → K :=
  fun a ↦ elemReduct K a ^ p ^ (n - elemExponent K a)

variable {L} in
/-- Action of `iterateFrobeniusAux` on the top field. -/
private theorem algebraMap_iterateFrobeniusAux {n : ℕ} (hn : exponent K L ≤ n) (a : L) :
    algebraMap K L (iterateFrobeniusAux K L p n a) = a ^ p ^ n := by
  rw [iterateFrobeniusAux, RingHom.map_pow, algebraMap_elemReduct_eq' K p, ← pow_mul, ← pow_add,
    Nat.add_sub_cancel' <| (elemExponent_le_exponent K a).trans hn]

section RingHom

/-- Iterated Frobenius map (ring homomorphism) for purely inseparable field extension with exponent.
If `n ≥ exponent K L`, it acts like `x ↦ x ^ p ^ n` but the codomain is the base field `K`. -/
noncomputable def iterateFrobenius {n : ℕ} (hn : exponent K L ≤ n) : L →+* K where
  toFun := iterateFrobeniusAux K L p n
  map_zero' := by
    apply (algebraMap K L).injective
    rw [(algebraMap K L).map_zero,
      algebraMap_iterateFrobeniusAux K p hn 0,
      zero_pow]
    exact Nat.pos_iff_ne_zero.mp <| expChar_pow_pos K p n
  map_add' a b := by
    have inj := (algebraMap K L).injective
    have : ExpChar L p := expChar_of_injective_ringHom inj p
    apply inj
    rw [(algebraMap K L).map_add,
      algebraMap_iterateFrobeniusAux K p hn a,
      algebraMap_iterateFrobeniusAux K p hn b,
      algebraMap_iterateFrobeniusAux K p hn (a + b),
      add_pow_expChar_pow a b]
  map_one' := by
    apply (algebraMap K L).injective
    rw [(algebraMap K L).map_one,
      algebraMap_iterateFrobeniusAux K p hn 1,
      one_pow]
  map_mul' a b := by
    apply (algebraMap K L).injective
    rw [(algebraMap K L).map_mul,
      algebraMap_iterateFrobeniusAux K p hn a,
      algebraMap_iterateFrobeniusAux K p hn b,
      algebraMap_iterateFrobeniusAux K p hn (a * b),
      mul_pow]

variable {L} in
/-- Action of `iterateFrobenius` on the top field. -/
theorem algebraMap_iterateFrobenius {n : ℕ} (hn : exponent K L ≤ n) (a : L) :
    algebraMap K L (iterateFrobenius K L p hn a) = a ^ p ^ n :=
  algebraMap_iterateFrobeniusAux K p hn a

variable {K} in
/-- Action of `iterateFrobenius` on the bottom field. -/
theorem iterateFrobenius_algebraMap {n : ℕ} (hn : exponent K L ≤ n) (a : K) :
    iterateFrobenius K L p hn (algebraMap K L a) = a ^ p ^ n := by
  apply (algebraMap K L).injective
  rw [map_pow, algebraMap_iterateFrobenius K p hn]

end RingHom

section Semilinear

variable [Field F] [Algebra F K] [Algebra F L] [IsScalarTower F K L]
variable [ExpChar F p]

/-- Version of `iterateFrobenius` as a semilinear map over a subfield `F` of `K`, w.r.t. the
iterated Frobenius homomorphism on `F`. -/
noncomputable def iterateFrobeniusₛₗ {n : ℕ} (hn : exponent K L ≤ n) :
    L →ₛₗ[_root_.iterateFrobenius F p n] K where
  __ := iterateFrobenius K L p hn
  map_smul' r a := by
    dsimp [iterateFrobenius]
    rw [Algebra.smul_def _ (iterateFrobeniusAux K L p n a)]
    apply (algebraMap K L).injective
    rw [(algebraMap K L).map_mul,
      ← IsScalarTower.algebraMap_apply,
      algebraMap_iterateFrobeniusAux K p hn a,
      algebraMap_iterateFrobeniusAux K p hn (r • a),
      iterateFrobenius_def,
      map_pow,
      Algebra.smul_def,
      mul_pow]

/-- Action of `iterateFrobeniusₛₗ` on the top field. -/
theorem algebraMap_iterateFrobeniusₛₗ {n : ℕ} (hn : exponent K L ≤ n) (a : L) :
    algebraMap K L (iterateFrobeniusₛₗ F K L p hn a) = a ^ p ^ n :=
  algebraMap_iterateFrobenius K p hn a

/-- Action of `iterateFrobeniusₛₗ` on the bottom field. -/
theorem iterateFrobeniusₛₗ_algebraMap {n : ℕ} (hn : exponent K L ≤ n) (a : K) :
    iterateFrobeniusₛₗ F K L p hn (algebraMap K L a) = a ^ p ^ n :=
  iterateFrobenius_algebraMap L p hn a

/-- Action of `iterateFrobeniusₛₗ` on the base field. -/
theorem iterateFrobeniusₛₗ_algebraMap_base {n : ℕ} (hn : exponent K L ≤ n) (a : F) :
    iterateFrobeniusₛₗ F K L p hn (algebraMap F L a) = (algebraMap F K a) ^ p ^ n := by
  apply (algebraMap K L).injective
  rw [← map_pow, ← IsScalarTower.algebraMap_apply, map_pow,
    algebraMap_iterateFrobeniusₛₗ F K L p hn]

end Semilinear

end Frobenius

end IsPurelyInseparable
