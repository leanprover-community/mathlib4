/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SplittingField.Construction

/-!

# Perfect fields and rings

In this file we define perfect fields, together with a generalisation to (commutative) rings in
prime characteristic.

## Main definitions / statements:
 * `PerfectRing`: a ring of characteristic `p` (prime) is said to be perfect in the sense of Serre,
   if its Frobenius map is bijective.
 * `PerfectField`: a field `K` is said to be perfect if every irreducible polynomial over `K` is
   separable.
 * `PerfectRing.toPerfectField`: a field that is perfect in the sense of Serre is a perfect field.
 * `PerfectField.toPerfectRing`: a perfect field of characteristic `p` (prime) is perfect in the
   sense of Serre.
 * `PerfectField.ofCharZero`: all fields of characteristic zero are perfect.
 * `PerfectField.ofFinite`: all finite fields are perfect.

-/

open Function Polynomial

/-- A perfect ring of characteristic `p` (prime) in the sense of Serre.

NB: This is not related to the concept with the same name introduced by Bass (related to projective
covers of modules). -/
class PerfectRing (R : Type _) (p : ℕ) [CommRing R] [Fact p.Prime] [CharP R p] : Prop where
  /-- A ring is perfect if the Frobenius map is bijective. -/
  bijective_frobenius : Bijective $ frobenius R p

section PerfectRing

variable (R : Type _) (p : ℕ) [CommRing R] [Fact p.Prime] [CharP R p]

/-- For a reduced ring, surjectivity of the Frobenius map is a sufficient condition for perfection.
-/
lemma PerfectRing.mkOfReduced [IsReduced R] (h : Surjective $ frobenius R p) : PerfectRing R p :=
  ⟨frobenius_inj R p, h⟩

instance PerfectRing.ofFiniteOfIsReduced [Finite R] [IsReduced R] : PerfectRing R p :=
  mkOfReduced _ _ $ Finite.surjective_of_injective (frobenius_inj R p)

variable [PerfectRing R p]

/-- The Frobenius automorphism for a perfect ring. -/
@[simps!]
noncomputable def frobeniusEquiv : R ≃+* R :=
  RingEquiv.ofBijective (frobenius R p) PerfectRing.bijective_frobenius
#align frobenius_equiv frobeniusEquiv

@[simp]
theorem coe_frobeniusEquiv : ⇑(frobeniusEquiv R p) = frobenius R p := rfl
#align coe_frobenius_equiv coe_frobeniusEquiv

@[simp]
theorem frobenius_comp_frobeniusEquiv_symm :
    (frobenius R p).comp (frobeniusEquiv R p).symm = RingHom.id R := by
  ext; simp [surjInv_eq]

lemma polynomial_expand_eq (f : R[X]) :
    expand R p f = (f.map (frobeniusEquiv R p).symm) ^ p := by
  rw [← (f.map (S := R) (frobeniusEquiv R p).symm).expand_char p, map_expand, map_map,
    frobenius_comp_frobeniusEquiv_symm, map_id]

@[simp]
theorem not_irreducible_expand (f : R[X]) : ¬ Irreducible (expand R p f) := by
  have hp : Fact p.Prime := inferInstance
  rw [polynomial_expand_eq]
  exact fun hf ↦ hf.not_unit $ (of_irreducible_pow hp.out.ne_one hf).pow p

end PerfectRing

/-- A perfect field.

See also `PerfectRing` for a generalisation in positive characteristic. -/
class PerfectField (K : Type _) [Field K] : Prop where
  /-- A field is perfect if every irreducible polynomial is separable. -/
  separable_of_irreducible : ∀ {f : K[X]}, Irreducible f → f.Separable

lemma PerfectRing.toPerfectField (K : Type _) (p : ℕ)
    [Field K] [hp : Fact p.Prime] [CharP K p] [PerfectRing K p] : PerfectField K := by
  refine' PerfectField.mk $ fun hf ↦ _
  rcases separable_or p hf with h | ⟨-, g, -, rfl⟩
  · assumption
  · exfalso; revert hf; simp

namespace PerfectField

variable (K : Type _) [Field K]

instance ofCharZero [CharZero K] : PerfectField K := ⟨Irreducible.separable⟩

instance ofFinite [Finite K] : PerfectField K := by
  obtain ⟨p, _instP⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  exact PerfectRing.toPerfectField K p

variable [PerfectField K]

instance toPerfectRing (p : ℕ) [hp : Fact p.Prime] [CharP K p] : PerfectRing K p := by
  refine' PerfectRing.mkOfReduced _ _ $ fun y ↦ _
  let f : K[X] := X ^ p - C y
  let L := f.SplittingField
  let ι := algebraMap K L
  have hf_deg : f.degree ≠ 0 := by
    rw [degree_X_pow_sub_C hp.out.pos y, p.cast_ne_zero]; exact hp.out.ne_zero
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
    rw [sub_pow_char, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, ← ha_pow, map_pow]
  have ha : IsIntegral K a := isIntegral_of_finite K a
  have hg_pow : g.map ι = (X - C a) ^ (g.map ι).natDegree := by
    obtain ⟨q, -, hq⟩ := (dvd_prime_pow (prime_X_sub_C a) p).mp hg_dvd
    rw [eq_of_monic_of_associated ((minpoly.monic ha).map ι) ((monic_X_sub_C a).pow q) hq,
      natDegree_pow, natDegree_X_sub_C, mul_one]
  have hg_sep : (g.map ι).Separable := (separable_of_irreducible $ minpoly.irreducible ha).map
  rw [hg_pow] at hg_sep
  refine' (Separable.of_pow (not_isUnit_X_sub_C a) _ hg_sep).2
  rw [g.natDegree_map ι, ← Nat.pos_iff_ne_zero, natDegree_pos_iff_degree_pos]
  exact minpoly.degree_pos ha

end PerfectField
