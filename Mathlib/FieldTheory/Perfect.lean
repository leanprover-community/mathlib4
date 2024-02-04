/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.Algebra.CharP.Reduced

/-!

# Perfect fields and rings

In this file we define perfect fields, together with a generalisation to (commutative) rings in
prime characteristic.

## Main definitions / statements:
 * `PerfectRing`: a ring of characteristic `p` (prime) is said to be perfect in the sense of Serre,
   if its absolute Frobenius map `x ↦ xᵖ` is bijective.
 * `PerfectField`: a field `K` is said to be perfect if every irreducible polynomial over `K` is
   separable.
 * `PerfectRing.toPerfectField`: a field that is perfect in the sense of Serre is a perfect field.
 * `PerfectField.toPerfectRing`: a perfect field of characteristic `p` (prime) is perfect in the
   sense of Serre.
 * `PerfectField.ofCharZero`: all fields of characteristic zero are perfect.
 * `PerfectField.ofFinite`: all finite fields are perfect.
 * `PerfectField.separable_iff_squarefree`: a polynomial over a perfect field is separable iff
   it is square-free.
 * `Algebra.IsAlgebraic.isSeparable_of_perfectField`, `Algebra.IsAlgebraic.perfectField`:
   if `L / K` is an algebraic extension, `K` is a perfect field, then `L / K` is separable,
   and `L` is also a perfect field.

-/

open Function Polynomial

/-- A perfect ring of characteristic `p` (prime) in the sense of Serre.

NB: This is not related to the concept with the same name introduced by Bass (related to projective
covers of modules). -/
class PerfectRing (R : Type*) (p : ℕ) [CommSemiring R] [ExpChar R p] : Prop where
  /-- A ring is perfect if the Frobenius map is bijective. -/
  bijective_frobenius : Bijective <| frobenius R p

section PerfectRing

variable (R : Type*) (p n : ℕ) [CommSemiring R] [ExpChar R p]

/-- For a reduced ring, surjectivity of the Frobenius map is a sufficient condition for perfection.
-/
lemma PerfectRing.ofSurjective (R : Type*) (p : ℕ) [CommRing R] [ExpChar R p]
    [IsReduced R] (h : Surjective <| frobenius R p) : PerfectRing R p :=
  ⟨frobenius_inj R p, h⟩
#align perfect_ring.of_surjective PerfectRing.ofSurjective

instance PerfectRing.ofFiniteOfIsReduced (R : Type*) [CommRing R] [ExpChar R p]
    [Finite R] [IsReduced R] : PerfectRing R p :=
  ofSurjective _ _ <| Finite.surjective_of_injective (frobenius_inj R p)

variable [PerfectRing R p]

@[simp]
theorem bijective_frobenius : Bijective (frobenius R p) := PerfectRing.bijective_frobenius

theorem bijective_iterateFrobenius : Bijective (iterateFrobenius R p n) :=
  coe_iterateFrobenius R p n ▸ (bijective_frobenius R p).iterate n

@[simp]
theorem injective_frobenius : Injective (frobenius R p) := (bijective_frobenius R p).1

@[simp]
theorem surjective_frobenius : Surjective (frobenius R p) := (bijective_frobenius R p).2

/-- The Frobenius automorphism for a perfect ring. -/
@[simps! apply]
noncomputable def frobeniusEquiv : R ≃+* R :=
  RingEquiv.ofBijective (frobenius R p) PerfectRing.bijective_frobenius
#align frobenius_equiv frobeniusEquiv

@[simp]
theorem coe_frobeniusEquiv : ⇑(frobeniusEquiv R p) = frobenius R p := rfl
#align coe_frobenius_equiv coe_frobeniusEquiv

/-- The iterated Frobenius automorphism for a perfect ring. -/
@[simps! apply]
noncomputable def iterateFrobeniusEquiv : R ≃+* R :=
  RingEquiv.ofBijective (iterateFrobenius R p n) (bijective_iterateFrobenius R p n)

@[simp]
theorem coe_iterateFrobeniusEquiv : ⇑(iterateFrobeniusEquiv R p n) = iterateFrobenius R p n := rfl

@[simp]
theorem frobeniusEquiv_symm_apply_frobenius (x : R) :
    (frobeniusEquiv R p).symm (frobenius R p x) = x :=
  leftInverse_surjInv PerfectRing.bijective_frobenius x

@[simp]
theorem frobenius_apply_frobeniusEquiv_symm (x : R) :
    frobenius R p ((frobeniusEquiv R p).symm x) = x :=
  surjInv_eq _ _

@[simp]
theorem frobenius_comp_frobeniusEquiv_symm :
    (frobenius R p).comp (frobeniusEquiv R p).symm = RingHom.id R := by
  ext; simp

@[simp]
theorem frobeniusEquiv_symm_comp_frobenius :
    ((frobeniusEquiv R p).symm : R →+* R).comp (frobenius R p) = RingHom.id R := by
  ext; simp

@[simp]
theorem frobeniusEquiv_symm_pow_p (x : R) : ((frobeniusEquiv R p).symm x) ^ p = x :=
  frobenius_apply_frobeniusEquiv_symm R p x

theorem injective_pow_p {x y : R} (h : x ^ p = y ^ p) : x = y := (frobeniusEquiv R p).injective h
#align injective_pow_p injective_pow_p

lemma polynomial_expand_eq (f : R[X]) :
    expand R p f = (f.map (frobeniusEquiv R p).symm) ^ p := by
  rw [← (f.map (S := R) (frobeniusEquiv R p).symm).expand_char p, map_expand, map_map,
    frobenius_comp_frobeniusEquiv_symm, map_id]

@[simp]
theorem not_irreducible_expand (R p) [CommSemiring R] [Fact p.Prime] [CharP R p] [PerfectRing R p]
    (f : R[X]) : ¬ Irreducible (expand R p f) := by
  rw [polynomial_expand_eq]
  exact not_irreducible_pow (Fact.out : p.Prime).ne_one

instance instPerfectRingProd (S : Type*) [CommSemiring S] [ExpChar S p] [PerfectRing S p] :
    PerfectRing (R × S) p where
  bijective_frobenius := (bijective_frobenius R p).Prod_map (bijective_frobenius S p)

namespace Polynomial

open scoped Classical

variable {R : Type*} [CommRing R] [IsDomain R] (p : ℕ) [ExpChar R p] [PerfectRing R p] (f : R[X])

/-- If `f` is a polynomial over a perfect integral domain `R` of characteristic `p`, then there is
a bijection from the set of roots of `Polynomial.expand R p f` to the set of roots of `f`.
It's given by `x ↦ x ^ p`, see `rootsExpandEquivRoots_apply`. -/
noncomputable def rootsExpandEquivRoots : (expand R p f).roots.toFinset ≃ f.roots.toFinset :=
  ((frobeniusEquiv R p).image _).trans <| Equiv.Set.ofEq <| show _ '' (setOf _) = setOf _ by
    ext r; obtain ⟨r, rfl⟩ := surjective_frobenius R p r
    simp [expand_eq_zero (expChar_pos R p), (frobenius_inj R p).eq_iff, ← frobenius_def]

@[simp]
theorem rootsExpandEquivRoots_apply (x) : (rootsExpandEquivRoots p f x : R) = x ^ p := rfl

/-- If `f` is a polynomial over a perfect integral domain `R` of characteristic `p`, then there is
a bijection from the set of roots of `Polynomial.expand R (p ^ n) f` to the set of roots of `f`.
It's given by `x ↦ x ^ (p ^ n)`, see `rootsExpandPowEquivRoots_apply`. -/
noncomputable def rootsExpandPowEquivRoots :
    (n : ℕ) → (expand R (p ^ n) f).roots.toFinset ≃ f.roots.toFinset
  | 0 => Equiv.Set.ofEq <| by rw [pow_zero, expand_one]
  | n + 1 => (Equiv.Set.ofEq <| by rw [pow_succ, ← expand_expand]).trans
    (rootsExpandEquivRoots p (expand R (p ^ n) f)) |>.trans (rootsExpandPowEquivRoots n)

@[simp]
theorem rootsExpandPowEquivRoots_apply (n : ℕ) (x) :
    (rootsExpandPowEquivRoots p f n x : R) = x ^ p ^ n := by
  induction' n with n ih
  · simp only [pow_zero, pow_one]
    rfl
  simp_rw [rootsExpandPowEquivRoots, Equiv.trans_apply, ih, pow_succ, pow_mul]
  rfl

end Polynomial

end PerfectRing

/-- A perfect field.

See also `PerfectRing` for a generalisation in positive characteristic. -/
class PerfectField (K : Type*) [Field K] : Prop where
  /-- A field is perfect if every irreducible polynomial is separable. -/
  separable_of_irreducible : ∀ {f : K[X]}, Irreducible f → f.Separable

lemma PerfectRing.toPerfectField (K : Type*) (p : ℕ)
    [Field K] [ExpChar K p] [PerfectRing K p] : PerfectField K := by
  obtain hp | ⟨hp⟩ := ‹ExpChar K p›
  · exact ⟨Irreducible.separable⟩
  refine PerfectField.mk fun hf ↦ ?_
  rcases separable_or p hf with h | ⟨-, g, -, rfl⟩
  · assumption
  · exfalso; revert hf; haveI := Fact.mk hp; simp

namespace PerfectField

variable {K : Type*} [Field K]

instance ofCharZero [CharZero K] : PerfectField K := ⟨Irreducible.separable⟩

instance ofFinite [Finite K] : PerfectField K := by
  obtain ⟨p, _instP⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  exact PerfectRing.toPerfectField K p

variable [PerfectField K]

/-- A perfect field of characteristic `p` (prime) is a perfect ring. -/
instance toPerfectRing (p : ℕ) [ExpChar K p] : PerfectRing K p := by
  refine' PerfectRing.ofSurjective _ _ fun y ↦ _
  let f : K[X] := X ^ p - C y
  let L := f.SplittingField
  let ι := algebraMap K L
  have hf_deg : f.degree ≠ 0 := by
    rw [degree_X_pow_sub_C (expChar_pos K p) y, p.cast_ne_zero]; exact (expChar_pos K p).ne'
  let a : L := f.rootOfSplits ι (SplittingField.splits f) hf_deg
  have hfa : aeval a f = 0 := by rw [aeval_def, map_rootOfSplits _ (SplittingField.splits f) hf_deg]
  have ha_pow : a ^ p = ι y := by rwa [AlgHom.map_sub, aeval_X_pow, aeval_C, sub_eq_zero] at hfa
  let g : K[X] := minpoly K a
  suffices : (g.map ι).natDegree = 1
  · rw [g.natDegree_map, ← degree_eq_iff_natDegree_eq_of_pos Nat.one_pos] at this
    obtain ⟨a' : K, ha' : ι a' = a⟩ := minpoly.mem_range_of_degree_eq_one K a this
    refine' ⟨a', NoZeroSMulDivisors.algebraMap_injective K L _⟩
    rw [RingHom.map_frobenius, ha', frobenius_def, ha_pow]
  have hg_dvd : g.map ι ∣ (X - C a) ^ p := by
    convert Polynomial.map_dvd ι (minpoly.dvd K a hfa)
    rw [sub_pow_expChar, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, ← ha_pow, map_pow]
  have ha : IsIntegral K a := .of_finite K a
  have hg_pow : g.map ι = (X - C a) ^ (g.map ι).natDegree := by
    obtain ⟨q, -, hq⟩ := (dvd_prime_pow (prime_X_sub_C a) p).mp hg_dvd
    rw [eq_of_monic_of_associated ((minpoly.monic ha).map ι) ((monic_X_sub_C a).pow q) hq,
      natDegree_pow, natDegree_X_sub_C, mul_one]
  have hg_sep : (g.map ι).Separable := (separable_of_irreducible <| minpoly.irreducible ha).map
  rw [hg_pow] at hg_sep
  refine' (Separable.of_pow (not_isUnit_X_sub_C a) _ hg_sep).2
  rw [g.natDegree_map ι, ← Nat.pos_iff_ne_zero, natDegree_pos_iff_degree_pos]
  exact minpoly.degree_pos ha

theorem separable_iff_squarefree {g : K[X]} : g.Separable ↔ Squarefree g := by
  refine ⟨Separable.squarefree,
    fun sqf ↦ isCoprime_of_irreducible_dvd (not_and_of_not_left _ sqf.ne_zero) ?_⟩
  rintro p (h : Irreducible p) ⟨q, rfl⟩ (dvd : p ∣ derivative (p * q))
  replace dvd : p ∣ q := by
    rw [derivative_mul, dvd_add_left (dvd_mul_right p _)] at dvd
    exact (separable_of_irreducible h).dvd_of_dvd_mul_left dvd
  exact (h.1 : ¬ IsUnit p) (sqf _ <| mul_dvd_mul_left _ dvd)

end PerfectField

/-- If `L / K` is an algebraic extension, `K` is a perfect field, then `L / K` is separable. -/
theorem Algebra.IsAlgebraic.isSeparable_of_perfectField {K L : Type*} [Field K] [Field L]
    [Algebra K L] [PerfectField K] (halg : Algebra.IsAlgebraic K L) : IsSeparable K L :=
  ⟨fun x ↦ PerfectField.separable_of_irreducible <| minpoly.irreducible (halg x).isIntegral⟩

/-- If `L / K` is an algebraic extension, `K` is a perfect field, then so is `L`. -/
theorem Algebra.IsAlgebraic.perfectField {K L : Type*} [Field K] [Field L] [Algebra K L]
    [PerfectField K] (halg : Algebra.IsAlgebraic K L) : PerfectField L := ⟨fun {f} hf ↦ by
  obtain ⟨_, _, hi, h⟩ := hf.exists_dvd_monic_irreducible_of_isIntegral halg.isIntegral
  exact (PerfectField.separable_of_irreducible hi).map |>.of_dvd h⟩
