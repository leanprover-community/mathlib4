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

## Main definitions

- `IsPurelyInseparable.HasExponent`: typeclass to assert a purely inseparable field extension
  `L / K` has an exponent, that is a smallest natural number `e` such that
  `a ^ ringExpChar K ^ e ∈ K`
  for all `a ∈ L`.
- `IsPurelyInseparable.exponent`: the exponent of a purely inseparable field extension.
- `IsPurelyInseparable.elemExponent`: the exponent of an element of a purely inseparable
  field extension, that is the smallest natural number `e` such that `a ^ ringExpChar K ^ e ∈ K`.
  Note: the result is currently meaningful only when `ringExpChar ≠ 1`.

## Tags

purely inseparable

-/

namespace IsPurelyInseparable

variable (K L : Type*)

section Ring

variable [CommRing K] [Ring L] [Algebra K L]

/-- A predicate class on a ring extension saying that there is a natural number `e`
such that `a ^ ringExpChar K ^ e ∈ K` for all `a ∈ L`. -/
class HasExponent : Prop where
  has_exponent' : ∃ e, ∀ a, a ^ ringExpChar K ^ e ∈ (algebraMap K L).range

theorem HasExponent.hasExponent (p : ℕ) [ExpChar K p] [HasExponent K L] :
    ∃ e, ∀ a, a ^ p ^ e ∈ (algebraMap K L).range :=
  ringExpChar.eq K p ▸ has_exponent'

open scoped Classical in
/-- The *exponent* of a purely inseparable extension is the smallest
natural number `e` such that `a ^ ringExpChar K ^ e ∈ K` for all `a ∈ L`. -/
noncomputable def exponent [HasExponent K L] : ℕ :=
  Nat.find ‹HasExponent K L›.has_exponent'

variable {L}

open Classical in
theorem exponent_def [HasExponent K L] (a : L) :
    a ^ ringExpChar K ^ exponent K L ∈ (algebraMap K L).range :=
  Nat.find_spec ‹HasExponent K L›.has_exponent' a

end Ring

section IsDomain

variable [Field K] [Ring L] [IsDomain L] [Algebra K L]

instance [HasExponent K L] : IsPurelyInseparable K L :=
  let ⟨n, h⟩ := ‹HasExponent K L›.has_exponent'
  (isPurelyInseparable_iff_pow_mem K (ringExpChar K)).mpr fun x ↦ ⟨n, h x⟩

end IsDomain

section Field

open Polynomial

variable [Field K] [Field L] [Algebra K L] [IsPurelyInseparable K L]
variable {L}

/-- 'Encoding' of an element `a : L` as the pair `⟨n, y⟩ : ℕ × K` with
`minpoly K a = X ^ ringExpChar K ^ n - y`. -/
noncomputable def elemEncode (a : L) : ℕ × K :=
  let p := ringExpChar K
  haveI : ExpChar K p := inferInstance
  Classical.choose <| Prod.exists'.mpr (minpoly_eq_X_pow_sub_C K p a)

/-- The exponent of an element `a ∈ L` of a purely inseparable field extension `L / K`
is the smallest natural number `e` such that `a ^ ringExpChar K ^ e ∈ K`.
The result is currently meaningful only when `ringExpChar ≠ 1`.
TODO: extend the definition for `ringExpChar = 1`, when the exponent is `0`. -/
noncomputable def elemExponent (a : L) : ℕ := (elemEncode K a).1

/-- The element `y` of the base field `K` such that
`a ^ ringExpChar K ^ elemExponent K a = algebraMap K L y`.
See `IsPurelyInseparable.algebraMap_elemReduct_eq`. -/
noncomputable def elemReduct (a : L) : K := (elemEncode K a).2

theorem minpoly_eq (a : L) :
    minpoly K a = X ^ ringExpChar K ^ elemExponent K a - C (elemReduct K a) :=
  let p := ringExpChar K
  haveI : ExpChar K p := inferInstance
  Classical.choose_spec <| Prod.exists'.mpr (minpoly_eq_X_pow_sub_C K p a)

/-- The degree of the minimal polynomial of an element `a ∈ L` equals
`ringExpChar K ^ elemExponent K a`. -/
theorem minpoly_natDegree_eq (a : L) :
    (minpoly K a).natDegree = ringExpChar K ^ elemExponent K a := by
  rw [minpoly_eq K a, natDegree_sub_C, natDegree_pow, natDegree_X, mul_one]

theorem algebraMap_elemReduct_eq (a : L) :
    algebraMap K L (elemReduct K a) = a ^ ringExpChar K ^ elemExponent K a := by
  have := minpoly_eq K a ▸ minpoly.aeval K a
  rw [map_sub, aeval_C, map_pow, aeval_X, sub_eq_zero] at this
  exact this.symm

variable {K} in
instance exponent_exists_of_finiteDimensional [IsPurelyInseparable K L] [FiniteDimensional K L] :
    HasExponent K L := by
  let ⟨p, _⟩ := ExpChar.exists K
  rcases ‹ExpChar K p› with _ | ⟨hp⟩
  · exact ⟨0, fun a ↦ surjective_algebraMap_of_isSeparable K L _⟩
  · let e := Nat.log (ringExpChar K) (Module.finrank K L)
    refine ⟨e, fun a ↦ ⟨elemReduct K a ^ ringExpChar K ^ (e - elemExponent K a), ?_⟩⟩
    have h_elemexp_bound (a : L) : elemExponent K a ≤ e :=
      Nat.le_log_of_pow_le (Nat.Prime.one_lt <| ringExpChar.eq K p ▸ hp)
        (minpoly_natDegree_eq K a ▸ minpoly.natDegree_le a)
    rw [RingHom.map_pow,
      algebraMap_elemReduct_eq,
      ← pow_mul, ← pow_add,
      Nat.add_sub_cancel' (h_elemexp_bound a)]

/-- An exponent of an element is less or equal than exponent of the extension
in non-zero characteristic.
The assumption that `ringExpChar K` is prime is necessary here as currently it cannot
be proven that element exponent is `0` when `ringExpChar K` is 1. -/
lemma elemExponent_le_exponent' [HasExponent K L] (hp : (ringExpChar K).Prime) (a : L) :
    elemExponent K a ≤ exponent K L := by
  obtain ⟨y, hy⟩ := RingHom.mem_range.mp <| exponent_def K a
  let f := X ^ ringExpChar K ^ exponent K L - C y
  have hf₁ : aeval a f = 0 := by rwa [map_sub, aeval_C, aeval_X_pow, sub_eq_zero, eq_comm]
  have hf₂ : f.Monic := monic_X_pow_sub_C y <| Nat.pos_iff_ne_zero.mp <| expChar_pow_pos K _ _
  have hf₃ : f.natDegree = ringExpChar K ^ exponent K L := by
    rw [natDegree_sub_C, natDegree_pow, natDegree_X, mul_one]
  exact (Nat.pow_le_pow_iff_right <| Nat.Prime.one_lt hp).mp <|
    hf₃ ▸ minpoly_natDegree_eq K a ▸ natDegree_le_natDegree (minpoly.min K a hf₂ hf₁)

end Field

end IsPurelyInseparable
