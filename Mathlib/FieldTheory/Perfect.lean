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

-/

open Function

/-- A perfect ring of characteristic `p` (prime) in the sense of Serre.

NB: This is not related to the concept with the same name introduced by Bass (related to projective
covers of modules). -/
class PerfectRing (R : Type _) (p : ℕ) [CommRing R] [Fact p.Prime] [CharP R p] : Prop where
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

lemma polynomial_expand_eq (f : Polynomial R) :
    Polynomial.expand R p f = (f.map (frobeniusEquiv R p).symm) ^ p := by
  rw [← (f.map (S := R) (frobeniusEquiv R p).symm).expand_char p, Polynomial.map_expand,
    Polynomial.map_map, frobenius_comp_frobeniusEquiv_symm, Polynomial.map_id]

@[simp]
theorem not_irreducible_expand (f : Polynomial R) : ¬ Irreducible (Polynomial.expand R p f) := by
  have hp : Fact p.Prime := inferInstance
  rw [polynomial_expand_eq]
  exact fun hf ↦ hf.not_unit $ (of_irreducible_pow hp.out.ne_one hf).pow p

end PerfectRing

/-- A perfect field.

See also `PerfectRing` for a generalisation in positive characteristic. -/
class PerfectField (K : Type _) [Field K] : Prop where
  separable_of_irreducible : ∀ {f : Polynomial K}, Irreducible f → f.Separable

lemma PerfectRing.toPerfectField (K : Type _) (p : ℕ)
    [Field K] [hp : Fact p.Prime] [CharP K p] [PerfectRing K p] : PerfectField K := by
  refine' PerfectField.mk $ fun hf ↦ _
  rcases Polynomial.separable_or p hf with h | ⟨-, g, -, rfl⟩
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

instance PerfectField.toPerfectRing (p : ℕ) [hp : Fact p.Prime] [CharP K p] : PerfectRing K p := by
  refine' PerfectRing.mkOfReduced _ _ $ fun y ↦ _
  let f : Polynomial K := Polynomial.X ^ p - Polynomial.C y
  let L := f.SplittingField
  let ι := algebraMap K L
  have : CharP L p := -- TODO Make this a global `instance`
    charP_of_injective_algebraMap (NoZeroSMulDivisors.algebraMap_injective K L) p
  have hf : f.degree ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C hp.out.pos y, p.cast_ne_zero]; exact hp.out.ne_zero
  let a : L := f.rootOfSplits ι (Polynomial.SplittingField.splits f) hf
  have hfa : Polynomial.aeval a f = 0 := by
    rw [Polynomial.aeval_def, Polynomial.map_rootOfSplits _ (Polynomial.SplittingField.splits f) hf]
  have hfa' : a^p = ι y := by
    rwa [AlgHom.map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, sub_eq_zero] at hfa
  let g : Polynomial K := minpoly K a
  have hgd : 0 < g.degree := minpoly.degree_pos (isIntegral_of_finite K a)
  suffices : g.degree = 1
  · obtain ⟨a' : K, ha' : ι a' = a⟩ := minpoly.mem_range_of_degree_eq_one K a this
    refine' ⟨a', NoZeroSMulDivisors.algebraMap_injective K L _⟩
    rw [RingHom.map_frobenius, ha', frobenius_def, hfa']
  have hg : g.Separable := separable_of_irreducible $ minpoly.irreducible $ isIntegral_of_finite K a
  have hgf : g ∣ f := minpoly.dvd K a hfa
  have hgf' := Polynomial.map_dvd ι hgf
  have hg' : (g.map ι).Separable := hg.map
  have hf' : f.map ι = (Polynomial.X - Polynomial.C a)^p := by
    rw [sub_pow_char, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      ← hfa', map_pow]
  rw [hf'] at hgf'
  have hgg : g.map ι = (Polynomial.X - Polynomial.C a)^(g.map ι).natDegree := by
    have hgm : (g.map ι).Monic := (minpoly.monic $ isIntegral_of_finite K a).map ι
    obtain ⟨q, -, hq⟩ := (dvd_prime_pow (Polynomial.prime_X_sub_C a) p).mp hgf'
    rw [Polynomial.eq_of_monic_of_associated hgm ((Polynomial.monic_X_sub_C a).pow q) hq,
      Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  suffices : (g.map ι).natDegree = 1
  · rwa [g.natDegree_map, ← Polynomial.degree_eq_iff_natDegree_eq_of_pos Nat.one_pos] at this
  rw [hgg] at hg'
  refine' (Polynomial.Separable.of_pow (Polynomial.not_isUnit_X_sub_C a) _ hg').2
  rwa [g.natDegree_map ι, ← Nat.pos_iff_ne_zero, Polynomial.natDegree_pos_iff_degree_pos]

end PerfectField
