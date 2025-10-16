/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Jacobson.Polynomial
import Mathlib.RingTheory.Artinian.Module

/-!
# Jacobson Rings
The following conditions are equivalent for a ring `R`:
1. Every radical ideal `I` is equal to its Jacobson radical
2. Every radical ideal `I` can be written as an intersection of maximal ideals
3. Every prime ideal `I` is equal to its Jacobson radical
Any ring satisfying any of these equivalent conditions is said to be Jacobson.
Some particular examples of Jacobson rings are also proven.
`isJacobsonRing_quotient` says that the quotient of a Jacobson ring is Jacobson.
`isJacobsonRing_localization` says the localization of a Jacobson ring
  to a single element is Jacobson.
`isJacobsonRing_polynomial_iff_isJacobsonRing` says polynomials over a Jacobson ring
  form a Jacobson ring.
## Main definitions
Let `R` be a commutative ring. Jacobson rings are defined using the first of the above conditions
* `IsJacobsonRing R` is the proposition that `R` is a Jacobson ring. It is a class,
  implemented as the predicate that for any ideal, `I.isRadical` implies `I.jacobson = I`.

## Main statements
* `isJacobsonRing_iff_prime_eq` is the equivalence between conditions 1 and 3 above.
* `isJacobsonRing_iff_sInf_maximal` is the equivalence between conditions 1 and 2 above.
* `isJacobsonRing_of_surjective` says that if `R` is a Jacobson ring and
  `f : R →+* S` is surjective, then `S` is also a Jacobson ring
* `MvPolynomial.isJacobsonRing` says that multi-variate polynomials
  over a Jacobson ring are Jacobson.
## Tags
Jacobson, Jacobson Ring
-/

universe u

open Polynomial
open Ideal

section IsJacobsonRing

variable {R S : Type*} [CommRing R] [CommRing S] {I : Ideal R}

/-- A ring is a Jacobson ring if for every radical ideal `I`,
the Jacobson radical of `I` is equal to `I`.
See `isJacobsonRing_iff_prime_eq` and `isJacobsonRing_iff_sInf_maximal`
for equivalent definitions. -/
class IsJacobsonRing (R : Type*) [CommRing R] : Prop where
  out' : ∀ I : Ideal R, I.IsRadical → I.jacobson = I

theorem isJacobsonRing_iff {R} [CommRing R] :
    IsJacobsonRing R ↔ ∀ I : Ideal R, I.IsRadical → I.jacobson = I :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem IsJacobsonRing.out {R} [CommRing R] :
    IsJacobsonRing R → ∀ {I : Ideal R}, I.IsRadical → I.jacobson = I :=
  isJacobsonRing_iff.1

/-- A ring is a Jacobson ring if and only if for all prime ideals `P`,
the Jacobson radical of `P` is equal to `P`. -/
theorem isJacobsonRing_iff_prime_eq :
    IsJacobsonRing R ↔ ∀ P : Ideal R, IsPrime P → P.jacobson = P := by
  refine isJacobsonRing_iff.trans ⟨fun h I hI => h I hI.isRadical, ?_⟩
  refine fun h I hI ↦ le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ mem_sInf.mpr fun _ hJ ↦ hJ.left hx)
  rw [← hI.radical, radical_eq_sInf I, mem_sInf]
  intro P hP
  rw [Set.mem_setOf_eq] at hP
  rw [jacobson, mem_sInf] at hx
  rw [← h P hP.right, jacobson, mem_sInf]
  exact fun J hJ => hx ⟨le_trans hP.left hJ.left, hJ.right⟩

/-- A ring `R` is Jacobson if and only if for every prime ideal `I`,
`I` can be written as the infimum of some collection of maximal ideals.
Allowing ⊤ in the set `M` of maximal ideals is equivalent, but makes some proofs cleaner. -/
theorem isJacobsonRing_iff_sInf_maximal : IsJacobsonRing R ↔ ∀ {I : Ideal R}, I.IsPrime →
    ∃ M : Set (Ideal R), (∀ J ∈ M, IsMaximal J ∨ J = ⊤) ∧ I = sInf M :=
  ⟨fun H _I h => eq_jacobson_iff_sInf_maximal.1 (H.out h.isRadical), fun H =>
    isJacobsonRing_iff_prime_eq.2 fun _P hP => eq_jacobson_iff_sInf_maximal.2 (H hP)⟩

/-- A variant of `isJacobsonRing_iff_sInf_maximal` with a different spelling of "maximal or `⊤`". -/
theorem isJacobsonRing_iff_sInf_maximal' : IsJacobsonRing R ↔ ∀ {I : Ideal R}, I.IsPrime →
    ∃ M : Set (Ideal R), (∀ J ∈ M, ∀ (K : Ideal R), J < K → K = ⊤) ∧ I = sInf M :=
  ⟨fun H _I h => eq_jacobson_iff_sInf_maximal'.1 (H.out h.isRadical), fun H =>
    isJacobsonRing_iff_prime_eq.2 fun _P hP => eq_jacobson_iff_sInf_maximal'.2 (H hP)⟩

theorem Ideal.radical_eq_jacobson [H : IsJacobsonRing R] (I : Ideal R) : I.radical = I.jacobson :=
  le_antisymm (le_sInf fun _J ⟨hJ, hJ_max⟩ => (IsPrime.radical_le_iff hJ_max.isPrime).mpr hJ)
    (H.out (radical_isRadical I) ▸ jacobson_mono le_radical)

instance (priority := 100) [IsArtinianRing R] : IsJacobsonRing R :=
  isJacobsonRing_iff_prime_eq.mpr fun _ _ ↦ jacobson_eq_self_of_isMaximal

theorem isJacobsonRing_of_surjective [H : IsJacobsonRing R] :
    (∃ f : R →+* S, Function.Surjective ↑f) → IsJacobsonRing S := by
  rintro ⟨f, hf⟩
  rw [isJacobsonRing_iff_sInf_maximal]
  intro p hp
  use map f '' { J : Ideal R | comap f p ≤ J ∧ J.IsMaximal }
  use fun j ⟨J, hJ, hmap⟩ => hmap ▸ (map_eq_top_or_isMaximal_of_surjective f hf hJ.right).symm
  have : p = map f (comap f p).jacobson :=
    (IsJacobsonRing.out' _ <| hp.isRadical.comap f).symm ▸ (map_comap_of_surjective f hf p).symm
  exact this.trans (map_sInf hf fun J ⟨hJ, _⟩ => le_trans (Ideal.ker_le_comap f) hJ)

instance (priority := 100) isJacobsonRing_quotient [IsJacobsonRing R] : IsJacobsonRing (R ⧸ I) :=
  isJacobsonRing_of_surjective ⟨Ideal.Quotient.mk I, by
    rintro ⟨x⟩
    use x
    rfl⟩

theorem isJacobsonRing_iso (e : R ≃+* S) : IsJacobsonRing R ↔ IsJacobsonRing S where
  mp _ := isJacobsonRing_of_surjective ⟨(e : R →+* S), e.surjective⟩
  mpr _ := isJacobsonRing_of_surjective ⟨(e.symm : S →+* R), e.symm.surjective⟩

theorem isJacobsonRing_of_isIntegral [Algebra R S] [Algebra.IsIntegral R S] [IsJacobsonRing R] :
    IsJacobsonRing S := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hP_top : comap (algebraMap R S) P = ⊤
  · simp [comap_eq_top_iff.1 hP_top]
  · have : Nontrivial (R ⧸ comap (algebraMap R S) P) := Quotient.nontrivial hP_top
    rw [jacobson_eq_iff_jacobson_quotient_eq_bot]
    refine eq_bot_of_comap_eq_bot (R := R ⧸ comap (algebraMap R S) P) ?_
    rw [eq_bot_iff, ← jacobson_eq_iff_jacobson_quotient_eq_bot.1
      ((isJacobsonRing_iff_prime_eq.1 ‹_›) (comap (algebraMap R S) P) (comap_isPrime _ _)),
      comap_jacobson]
    refine sInf_le_sInf fun J hJ => ?_
    simp only [true_and, Set.mem_image, bot_le, Set.mem_setOf_eq]
    have : J.IsMaximal := by simpa using hJ
    exact exists_ideal_over_maximal_of_isIntegral J
      (comap_bot_le_of_injective _ algebraMap_quotient_injective)

/-- A variant of `isJacobsonRing_of_isIntegral` that takes `RingHom.IsIntegral` instead. -/
theorem isJacobsonRing_of_isIntegral' (f : R →+* S) (hf : f.IsIntegral) [IsJacobsonRing R] :
    IsJacobsonRing S :=
  let _ : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  isJacobsonRing_of_isIntegral (R := R)

end IsJacobsonRing

section Localization

open IsLocalization Submonoid

variable {R S : Type*} [CommRing R] [CommRing S]
variable (y : R) [Algebra R S] [IsLocalization.Away y S]

variable (S) in
/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its comap.
See `le_relIso_of_maximal` for the more general relation isomorphism -/
theorem IsLocalization.isMaximal_iff_isMaximal_disjoint [H : IsJacobsonRing R] (J : Ideal S) :
    J.IsMaximal ↔ (comap (algebraMap R S) J).IsMaximal ∧ y ∉ Ideal.comap (algebraMap R S) J := by
  constructor
  · refine fun h => ⟨?_, fun hy =>
      h.ne_top (Ideal.eq_top_of_isUnit_mem _ hy (map_units _ ⟨y, Submonoid.mem_powers _⟩))⟩
    have hJ : J.IsPrime := IsMaximal.isPrime h
    rw [isPrime_iff_isPrime_disjoint (Submonoid.powers y)] at hJ
    have : y ∉ (comap (algebraMap R S) J).1 := Set.disjoint_left.1 hJ.right (Submonoid.mem_powers _)
    rw [← H.out hJ.left.isRadical, jacobson, Submodule.mem_toAddSubmonoid, Ideal.mem_sInf] at this
    push_neg at this
    rcases this with ⟨I, hI, hI'⟩
    convert hI.right
    by_cases hJ : J = I.map (algebraMap R S)
    · rw [hJ, comap_map_of_isPrime_disjoint (powers y) S I (IsMaximal.isPrime hI.right)]
      rwa [disjoint_powers_iff_notMem y hI.right.isPrime.isRadical]
    · have hI_p : (I.map (algebraMap R S)).IsPrime := by
        refine isPrime_of_isPrime_disjoint (powers y) _ I hI.right.isPrime ?_
        rwa [disjoint_powers_iff_notMem y hI.right.isPrime.isRadical]
      have : J ≤ I.map (algebraMap R S) := map_comap (Submonoid.powers y) S J ▸ map_mono hI.left
      exact absurd (h.1.2 _ (lt_of_le_of_ne this hJ)) hI_p.1
  · refine fun h => ⟨⟨fun hJ => h.1.ne_top (eq_top_iff.2 ?_), fun I hI => ?_⟩⟩
    · rwa [eq_top_iff, ← (IsLocalization.orderEmbedding (powers y) S).le_iff_le] at hJ
    · have := congr_arg (Ideal.map (algebraMap R S)) (h.1.1.2 _ ⟨comap_mono (le_of_lt hI), ?_⟩)
      · rwa [map_comap (powers y) S I, Ideal.map_top] at this
      refine fun hI' => hI.right ?_
      rw [← map_comap (powers y) S I, ← map_comap (powers y) S J]
      exact map_mono hI'

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its map.
See `le_relIso_of_maximal` for the more general statement, and the reverse of this implication -/
theorem IsLocalization.isMaximal_of_isMaximal_disjoint
    [IsJacobsonRing R] (I : Ideal R) (hI : I.IsMaximal)
    (hy : y ∉ I) : (I.map (algebraMap R S)).IsMaximal := by
  rw [isMaximal_iff_isMaximal_disjoint S y,
    comap_map_of_isPrime_disjoint (powers y) S I (IsMaximal.isPrime hI)
      ((disjoint_powers_iff_notMem y hI.isPrime.isRadical).2 hy)]
  exact ⟨hI, hy⟩

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y` -/
def IsLocalization.orderIsoOfMaximal [IsJacobsonRing R] :
    { p : Ideal S // p.IsMaximal } ≃o { p : Ideal R // p.IsMaximal ∧ y ∉ p } where
  toFun p := ⟨Ideal.comap (algebraMap R S) p.1, (isMaximal_iff_isMaximal_disjoint S y p.1).1 p.2⟩
  invFun p := ⟨Ideal.map (algebraMap R S) p.1, isMaximal_of_isMaximal_disjoint y p.1 p.2.1 p.2.2⟩
  left_inv J := Subtype.eq (map_comap (powers y) S J)
  right_inv I := Subtype.eq (comap_map_of_isPrime_disjoint _ _ I.1 (IsMaximal.isPrime I.2.1)
    ((disjoint_powers_iff_notMem y I.2.1.isPrime.isRadical).2 I.2.2))
  map_rel_iff' {I I'} := ⟨fun h => show I.val ≤ I'.val from
    map_comap (powers y) S I.val ▸ map_comap (powers y) S I'.val ▸ Ideal.map_mono h,
    fun h _ hx => h hx⟩

include y in
/-- If `S` is the localization of the Jacobson ring `R` at the submonoid generated by `y : R`, then
`S` is Jacobson. -/
theorem isJacobsonRing_localization [H : IsJacobsonRing R] : IsJacobsonRing S := by
  rw [isJacobsonRing_iff_prime_eq]
  refine fun P' hP' => le_antisymm ?_ le_jacobson
  obtain ⟨hP', hPM⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint (powers y) S P').mp hP'
  have hP := H.out hP'.isRadical
  refine (IsLocalization.map_comap (powers y) S P'.jacobson).ge.trans
    ((map_mono ?_).trans (IsLocalization.map_comap (powers y) S P').le)
  have : sInf { I : Ideal R | comap (algebraMap R S) P' ≤ I ∧ I.IsMaximal ∧ y ∉ I } ≤
      comap (algebraMap R S) P' := by
    intro x hx
    have hxy : x * y ∈ (comap (algebraMap R S) P').jacobson := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      intro J hJ
      by_cases h : y ∈ J
      · exact J.mul_mem_left x h
      · exact J.mul_mem_right y ((mem_sInf.1 hx) ⟨hJ.left, ⟨hJ.right, h⟩⟩)
    rw [hP] at hxy
    rcases hP'.mem_or_mem hxy with hxy | hxy
    · exact hxy
    · exact (hPM.le_bot ⟨Submonoid.mem_powers _, hxy⟩).elim
  refine le_trans ?_ this
  rw [Ideal.jacobson, comap_sInf', sInf_eq_iInf]
  refine iInf_le_iInf_of_subset fun I hI => ⟨map (algebraMap R S) I, ⟨?_, ?_⟩⟩
  · exact ⟨le_trans (le_of_eq (IsLocalization.map_comap (powers y) S P').symm) (map_mono hI.1),
      isMaximal_of_isMaximal_disjoint y _ hI.2.1 hI.2.2⟩
  · exact IsLocalization.comap_map_of_isPrime_disjoint _ S I (IsMaximal.isPrime hI.2.1)
      ((disjoint_powers_iff_notMem y hI.2.1.isPrime.isRadical).2 hI.2.2)

end Localization

namespace Polynomial

section CommRing

-- Porting note: move to better place
lemma mem_closure_X_union_C {R : Type*} [Ring R] (p : R[X]) :
    p ∈ Subring.closure (insert X {f | f.degree ≤ 0} : Set R[X]) := by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro r
    apply Subring.subset_closure
    apply Set.mem_insert_of_mem
    exact degree_C_le
  · intro p1 p2 h1 h2
    exact Subring.add_mem _ h1 h2
  · intro n r hr
    rw [pow_succ, ← mul_assoc]
    apply Subring.mul_mem _ hr
    apply Subring.subset_closure
    apply Set.mem_insert

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
variable {Rₘ Sₘ : Type*} [CommRing Rₘ] [CommRing Sₘ]

/-- If `I` is a prime ideal of `R[X]` and `pX ∈ I` is a non-constant polynomial,
  then the map `R →+* R[x]/I` descends to an integral map when localizing at `pX.leadingCoeff`.
  In particular `X` is integral because it satisfies `pX`, and constants are trivially integral,
  so integrality of the entire extension follows by closure under addition and multiplication. -/
theorem isIntegral_isLocalization_polynomial_quotient
    (P : Ideal R[X]) (pX : R[X]) (hpX : pX ∈ P) [Algebra (R ⧸ P.comap (C : R →+* R[X])) Rₘ]
    [IsLocalization.Away (pX.map (Ideal.Quotient.mk (P.comap (C : R →+* R[X])))).leadingCoeff Rₘ]
    [Algebra (R[X] ⧸ P) Sₘ] [IsLocalization ((Submonoid.powers (pX.map (Ideal.Quotient.mk (P.comap
      (C : R →+* R[X])))).leadingCoeff).map (quotientMap P C le_rfl) : Submonoid (R[X] ⧸ P)) Sₘ] :
    (IsLocalization.map Sₘ (quotientMap P C le_rfl) (Submonoid.powers (pX.map (Ideal.Quotient.mk
      (P.comap (C : R →+* R[X])))).leadingCoeff).le_comap_map : Rₘ →+* Sₘ).IsIntegral := by
  let P' : Ideal R := P.comap C
  let M : Submonoid (R ⧸ P') :=
    Submonoid.powers (pX.map (Ideal.Quotient.mk (P.comap (C : R →+* R[X])))).leadingCoeff
  let M' : Submonoid (R[X] ⧸ P) :=
    (Submonoid.powers (pX.map (Ideal.Quotient.mk (P.comap (C : R →+* R[X])))).leadingCoeff).map
      (quotientMap P C le_rfl)
  let φ : R ⧸ P' →+* R[X] ⧸ P := quotientMap P C le_rfl
  let φ' : Rₘ →+* Sₘ := IsLocalization.map Sₘ φ M.le_comap_map
  have hφ' : φ.comp (Ideal.Quotient.mk P') = (Ideal.Quotient.mk P).comp C := rfl
  intro p
  obtain ⟨⟨p', ⟨q, hq⟩⟩, hp⟩ := IsLocalization.surj M' p
  suffices φ'.IsIntegralElem (algebraMap (R[X] ⧸ P) Sₘ p') by
    obtain ⟨q', hq', rfl⟩ := hq
    obtain ⟨q'', hq''⟩ := isUnit_iff_exists_inv'.1 (IsLocalization.map_units Rₘ (⟨q', hq'⟩ : M))
    refine (hp.symm ▸ this).of_mul_unit φ' p (algebraMap (R[X] ⧸ P) Sₘ (φ q')) q'' ?_
    rw [← φ'.map_one, ← congr_arg φ' hq'', φ'.map_mul, ← φ'.comp_apply]
    simp only [φ', IsLocalization.map_comp _, RingHom.comp_apply]
  dsimp at hp
  refine @IsIntegral.of_mem_closure'' Rₘ _ Sₘ _ φ'
    ((algebraMap (R[X] ⧸ P) Sₘ).comp (Ideal.Quotient.mk P) '' insert X { p | p.degree ≤ 0 }) ?_
    ((algebraMap (R[X] ⧸ P) Sₘ) p') ?_
  · rintro x ⟨p, hp, rfl⟩
    simp only [Set.mem_insert_iff] at hp
    rcases hp with hy | hy
    · rw [hy]
      refine φ.isIntegralElem_localization_at_leadingCoeff ((Ideal.Quotient.mk P) X)
        (pX.map (Ideal.Quotient.mk P')) ?_ M ?_
      · rwa [eval₂_map, hφ', ← hom_eval₂, Quotient.eq_zero_iff_mem, eval₂_C_X]
      · use 1
        simp only [P', pow_one]
    · rw [Set.mem_setOf_eq, degree_le_zero_iff] at hy
      rw [hy]
      refine ⟨X - C (algebraMap _ _ ((Ideal.Quotient.mk P') (p.coeff 0))), monic_X_sub_C _, ?_⟩
      simp only [eval₂_sub, eval₂_X, eval₂_C]
      rw [sub_eq_zero, ← φ'.comp_apply]
      simp [φ', IsLocalization.map_comp _, P', φ]
  · obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p'
    rw [← RingHom.comp_apply]
    apply Subring.mem_closure_image_of
    apply Polynomial.mem_closure_X_union_C

/-- If `f : R → S` descends to an integral map in the localization at `x`,
  and `R` is a Jacobson ring, then the intersection of all maximal ideals in `S` is trivial -/
theorem jacobson_bot_of_integral_localization
    {R : Type*} [CommRing R] [IsDomain R] [IsJacobsonRing R]
    (Rₘ Sₘ : Type*) [CommRing Rₘ] [CommRing Sₘ] (φ : R →+* S) (hφ : Function.Injective ↑φ) (x : R)
    (hx : x ≠ 0) [Algebra R Rₘ] [IsLocalization.Away x Rₘ] [Algebra S Sₘ]
    [IsLocalization ((Submonoid.powers x).map φ : Submonoid S) Sₘ]
    (hφ' :
      RingHom.IsIntegral (IsLocalization.map Sₘ φ (Submonoid.powers x).le_comap_map : Rₘ →+* Sₘ)) :
    (⊥ : Ideal S).jacobson = (⊥ : Ideal S) := by
  have hM : ((Submonoid.powers x).map φ : Submonoid S) ≤ nonZeroDivisors S :=
    map_le_nonZeroDivisors_of_injective φ hφ (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
  letI : IsDomain Sₘ := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  let φ' : Rₘ →+* Sₘ := IsLocalization.map _ φ (Submonoid.powers x).le_comap_map
  suffices ∀ I : Ideal Sₘ, I.IsMaximal → (I.comap (algebraMap S Sₘ)).IsMaximal by
    have hϕ' : comap (algebraMap S Sₘ) (⊥ : Ideal Sₘ) = (⊥ : Ideal S) := by
      rw [← RingHom.ker_eq_comap_bot, ← RingHom.injective_iff_ker_eq_bot]
      exact IsLocalization.injective Sₘ hM
    have hRₘ : IsJacobsonRing Rₘ := isJacobsonRing_localization x
    have hSₘ : IsJacobsonRing Sₘ := isJacobsonRing_of_isIntegral' φ' hφ'
    refine eq_bot_iff.mpr (le_trans ?_ (le_of_eq hϕ'))
    rw [← hSₘ.out isRadical_bot_of_noZeroDivisors, comap_jacobson]
    exact sInf_le_sInf fun j hj => ⟨bot_le,
      let ⟨J, hJ⟩ := hj
      hJ.2 ▸ this J hJ.1.2⟩
  intro I hI
  -- Remainder of the proof is pulling and pushing ideals around the square and the quotient square
  have : (I.comap (algebraMap S Sₘ)).IsPrime := comap_isPrime _ I
  have : (I.comap φ').IsPrime := comap_isPrime φ' I
  have : (⊥ : Ideal (S ⧸ I.comap (algebraMap S Sₘ))).IsPrime := bot_prime
  have hcomm : φ'.comp (algebraMap R Rₘ) = (algebraMap S Sₘ).comp φ := IsLocalization.map_comp _
  let f := quotientMap (I.comap (algebraMap S Sₘ)) φ le_rfl
  let g := quotientMap I (algebraMap S Sₘ) le_rfl
  have := isMaximal_comap_of_isIntegral_of_isMaximal' φ' hφ' I
  have := ((IsLocalization.isMaximal_iff_isMaximal_disjoint Rₘ x _).1 this).left
  have : ((I.comap (algebraMap S Sₘ)).comap φ).IsMaximal := by
    rwa [comap_comap, hcomm, ← comap_comap] at this
  rw [← bot_quotient_isMaximal_iff] at this ⊢
  refine isMaximal_of_isIntegral_of_isMaximal_comap' f ?_ ⊥
    ((eq_bot_iff.2 (comap_bot_le_of_injective f quotientMap_injective)).symm ▸ this)
  exact RingHom.IsIntegral.tower_bot f g quotientMap_injective
    ((comp_quotientMap_eq_of_comp_eq hcomm I).symm ▸
      (RingHom.isIntegral_of_surjective _
        (IsLocalization.surjective_quotientMap_of_maximal_of_localization (Submonoid.powers x) Rₘ
          (by rwa [comap_comap, hcomm, ← bot_quotient_isMaximal_iff]))).trans _ _ (hφ'.quotient _))

/-- Used to bootstrap the proof of `isJacobsonRing_polynomial_iff_isJacobsonRing`.
  That theorem is more general and should be used instead of this one. -/
private theorem isJacobsonRing_polynomial_of_domain (R : Type*) [CommRing R] [IsDomain R]
    [hR : IsJacobsonRing R] (P : Ideal R[X]) [IsPrime P] (hP : ∀ x : R, C x ∈ P → x = 0) :
    P.jacobson = P := by
  by_cases Pb : P = ⊥
  · exact Pb.symm ▸
      jacobson_bot_polynomial_of_jacobson_bot (hR.out isRadical_bot_of_noZeroDivisors)
  · rw [jacobson_eq_iff_jacobson_quotient_eq_bot]
    let P' := P.comap (C : R →+* R[X])
    have : P'.IsPrime := comap_isPrime C P
    have hR' : IsJacobsonRing (R ⧸ P') := by infer_instance
    obtain ⟨p, pP, p0⟩ := exists_nonzero_mem_of_ne_bot Pb hP
    let x := (Polynomial.map (Ideal.Quotient.mk P') p).leadingCoeff
    have hx : x ≠ 0 := by rwa [Ne, leadingCoeff_eq_zero]
    let φ : R ⧸ P' →+* R[X] ⧸ P := Ideal.quotientMap P (C : R →+* R[X]) le_rfl
    let hφ : Function.Injective ↑φ := quotientMap_injective
    let Rₘ := Localization.Away x
    let Sₘ := (Localization ((Submonoid.powers x).map φ : Submonoid (R[X] ⧸ P)))
    refine jacobson_bot_of_integral_localization (S := R[X] ⧸ P) (R := R ⧸ P') Rₘ Sₘ _ hφ _ hx ?_
    exact isIntegral_isLocalization_polynomial_quotient P p pP

theorem isJacobsonRing_polynomial_of_isJacobsonRing (hR : IsJacobsonRing R) :
    IsJacobsonRing R[X] := by
  rw [isJacobsonRing_iff_prime_eq]
  intro I hI
  let R' : Subring (R[X] ⧸ I) := ((Ideal.Quotient.mk I).comp C).range
  let i : R →+* R' := ((Ideal.Quotient.mk I).comp C).rangeRestrict
  have hi : Function.Surjective ↑i := ((Ideal.Quotient.mk I).comp C).rangeRestrict_surjective
  have hi' : RingHom.ker (mapRingHom i) ≤ I := by
    intro f hf
    apply polynomial_mem_ideal_of_coeff_mem_ideal I f
    intro n
    replace hf := congrArg (fun g : Polynomial ((Ideal.Quotient.mk I).comp C).range => g.coeff n) hf
    change (Polynomial.map ((Ideal.Quotient.mk I).comp C).rangeRestrict f).coeff n = 0 at hf
    rw [coeff_map, Subtype.ext_iff] at hf
    rwa [mem_comap, ← Quotient.eq_zero_iff_mem, ← RingHom.comp_apply]
  have R'_jacob : IsJacobsonRing R' := isJacobsonRing_of_surjective ⟨i, hi⟩
  let J := I.map (mapRingHom i)
  have h_surj : Function.Surjective (mapRingHom i) := Polynomial.map_surjective i hi
  have : IsPrime J := map_isPrime_of_surjective h_surj hi'
  suffices h : J.jacobson = J by
    replace h := congrArg (comap (Polynomial.mapRingHom i)) h
    rw [← map_jacobson_of_surjective h_surj hi', comap_map_of_surjective _ h_surj,
      comap_map_of_surjective _ h_surj] at h
    refine le_antisymm ?_ le_jacobson
    exact le_trans (le_sup_of_le_left le_rfl) (le_trans (le_of_eq h) (sup_le le_rfl hi'))
  apply isJacobsonRing_polynomial_of_domain R' J
  exact eq_zero_of_polynomial_mem_map_range I

theorem isJacobsonRing_polynomial_iff_isJacobsonRing : IsJacobsonRing R[X] ↔ IsJacobsonRing R := by
  refine ⟨?_, isJacobsonRing_polynomial_of_isJacobsonRing⟩
  intro H
  exact isJacobsonRing_of_surjective ⟨eval₂RingHom (RingHom.id _) 1, fun x =>
    ⟨C x, by simp only [coe_eval₂RingHom, RingHom.id_apply, eval₂_C]⟩⟩

instance [IsJacobsonRing R] : IsJacobsonRing R[X] :=
  isJacobsonRing_polynomial_iff_isJacobsonRing.mpr ‹IsJacobsonRing R›

end CommRing

section

variable {R : Type*} [CommRing R]
variable (P : Ideal R[X]) [hP : P.IsMaximal]

theorem isMaximal_comap_C_of_isMaximal [IsJacobsonRing R] [Nontrivial R]
    (hP' : ∀ x : R, C x ∈ P → x = 0) :
    IsMaximal (comap (C : R →+* R[X]) P : Ideal R) := by
  let P' := comap (C : R →+* R[X]) P
  have hP'_prime : P'.IsPrime := comap_isPrime C P
  obtain ⟨⟨m, hmem_P⟩, hm⟩ :=
    Submodule.nonzero_mem_of_bot_lt (bot_lt_of_maximal P polynomial_not_isField)
  have hm' : m ≠ 0 := by
    simpa [Submodule.coe_eq_zero] using hm
  let φ : R ⧸ P' →+* R[X] ⧸ P := quotientMap P (C : R →+* R[X]) le_rfl
  let a : R ⧸ P' := (m.map (Ideal.Quotient.mk P')).leadingCoeff
  let M : Submonoid (R ⧸ P') := Submonoid.powers a
  rw [← bot_quotient_isMaximal_iff]
  have hp0 : a ≠ 0 := fun hp0' =>
    hm' <| map_injective (Ideal.Quotient.mk (P.comap (C : R →+* R[X]) : Ideal R))
      ((injective_iff_map_eq_zero (Ideal.Quotient.mk (P.comap (C : R →+* R[X]) : Ideal R))).2
        fun x hx => by
          rwa [Quotient.eq_zero_iff_mem, (by rwa [eq_bot_iff] : (P.comap C : Ideal R) = ⊥)] at hx)
        (by simpa only [a, leadingCoeff_eq_zero, Polynomial.map_zero] using hp0')
  have hM : (0 : R ⧸ P') ∉ M := fun ⟨n, hn⟩ => hp0 (eq_zero_of_pow_eq_zero hn)
  suffices (⊥ : Ideal (Localization M)).IsMaximal by
    rw [← IsLocalization.comap_map_of_isPrime_disjoint M (Localization M) ⊥ bot_prime
      (disjoint_iff_inf_le.mpr fun x hx => hM (hx.2 ▸ hx.1))]
    exact ((IsLocalization.isMaximal_iff_isMaximal_disjoint (Localization M) a _).mp
      (by rwa [Ideal.map_bot])).1
  let M' : Submonoid (R[X] ⧸ P) := M.map φ
  have hM' : (0 : R[X] ⧸ P) ∉ M' := fun ⟨z, hz⟩ =>
    hM (quotientMap_injective (_root_.trans hz.2 φ.map_zero.symm) ▸ hz.1)
  suffices (⊥ : Ideal (Localization M')).IsMaximal by
    rw [le_antisymm bot_le (comap_bot_le_of_injective _
      (IsLocalization.map_injective_of_injective M (Localization M) (Localization M')
        quotientMap_injective))]
    refine isMaximal_comap_of_isIntegral_of_isMaximal' _ ?_ ⊥
    have isloc : IsLocalization (Submonoid.map φ M) (Localization M') := by infer_instance
    exact @isIntegral_isLocalization_polynomial_quotient R _
      (Localization M) (Localization M') _ _ P m hmem_P _ _ _ isloc
  rw [(map_bot.symm :
    (⊥ : Ideal (Localization M')) = Ideal.map (algebraMap (R[X] ⧸ P) (Localization M')) ⊥)]
  let bot_maximal := (bot_quotient_isMaximal_iff _).mpr hP
  refine bot_maximal.map_bijective (algebraMap (R[X] ⧸ P) (Localization M')) ?_
  apply IsField.localization_map_bijective hM'
  rwa [← Quotient.maximal_ideal_iff_isField_quotient, ← bot_quotient_isMaximal_iff]

/-- Used to bootstrap the more general `quotient_mk_comp_C_isIntegral_of_jacobson` -/
private theorem quotient_mk_comp_C_isIntegral_of_jacobson' [Nontrivial R] (hR : IsJacobsonRing R)
    (hP' : ∀ x : R, C x ∈ P → x = 0) :
    ((Ideal.Quotient.mk P).comp C : R →+* R[X] ⧸ P).IsIntegral := by
  refine (isIntegral_quotientMap_iff _).mp ?_
  let P' : Ideal R := P.comap C
  obtain ⟨pX, hpX, hp0⟩ :=
    exists_nonzero_mem_of_ne_bot (ne_of_lt (bot_lt_of_maximal P polynomial_not_isField)).symm hP'
  let a : R ⧸ P' := (pX.map (Ideal.Quotient.mk P')).leadingCoeff
  let M : Submonoid (R ⧸ P') := Submonoid.powers a
  let φ : R ⧸ P' →+* R[X] ⧸ P := quotientMap P C le_rfl
  have hP'_prime : P'.IsPrime := comap_isPrime C P
  have hM : (0 : R ⧸ P') ∉ M := fun ⟨n, hn⟩ =>
    hp0 <| leadingCoeff_eq_zero.mp (eq_zero_of_pow_eq_zero hn)
  let M' : Submonoid (R[X] ⧸ P) := M.map φ
  refine RingHom.IsIntegral.tower_bot φ (algebraMap _ (Localization M')) ?_ ?_
  · refine IsLocalization.injective (Localization M')
      (show M' ≤ _ from le_nonZeroDivisors_of_noZeroDivisors fun hM' => hM ?_)
    exact
      let ⟨z, zM, z0⟩ := hM'
      quotientMap_injective (_root_.trans z0 φ.map_zero.symm) ▸ zM
  · suffices RingHom.comp (algebraMap (R[X] ⧸ P) (Localization M')) φ =
      (IsLocalization.map (Localization M') φ M.le_comap_map).comp
        (algebraMap (R ⧸ P') (Localization M)) by
      rw [this]
      refine RingHom.IsIntegral.trans (algebraMap (R ⧸ P') (Localization M))
        (IsLocalization.map (Localization M') φ M.le_comap_map) ?_ ?_
      · exact (algebraMap (R ⧸ P') (Localization M)).isIntegral_of_surjective
          (IsField.localization_map_bijective hM ((Quotient.maximal_ideal_iff_isField_quotient _).mp
            (isMaximal_comap_C_of_isMaximal P hP'))).2
      · -- `convert` here is faster than `exact`, and this proof is near the time limit.
        -- convert isIntegral_isLocalization_polynomial_quotient P pX hpX
        have isloc : IsLocalization M' (Localization M') := by infer_instance
        exact @isIntegral_isLocalization_polynomial_quotient R _
          (Localization M) (Localization M') _ _ P pX hpX _ _ _ isloc
    rw [IsLocalization.map_comp M.le_comap_map]

variable [IsJacobsonRing R]

/-- If `R` is a Jacobson ring, and `P` is a maximal ideal of `R[X]`,
  then `R → R[X]/P` is an integral map. -/
theorem quotient_mk_comp_C_isIntegral_of_isJacobsonRing :
    ((Ideal.Quotient.mk P).comp C : R →+* R[X] ⧸ P).IsIntegral := by
  let P' : Ideal R := P.comap C
  have : P'.IsPrime := comap_isPrime C P
  let f : R[X] →+* Polynomial (R ⧸ P') := Polynomial.mapRingHom (Ideal.Quotient.mk P')
  have hf : Function.Surjective ↑f := map_surjective (Ideal.Quotient.mk P') Quotient.mk_surjective
  have hPJ : P = (P.map f).comap f := by
    rw [comap_map_of_surjective _ hf]
    refine le_antisymm (le_sup_of_le_left le_rfl) (sup_le le_rfl ?_)
    refine fun p hp =>
      polynomial_mem_ideal_of_coeff_mem_ideal P p fun n => Quotient.eq_zero_iff_mem.mp ?_
    simpa only [f, coeff_map, coe_mapRingHom] using (Polynomial.ext_iff.mp hp) n
  refine RingHom.IsIntegral.tower_bot
    (T := (R ⧸ comap C P)[X] ⧸ _) _ _ (injective_quotient_le_comap_map P) ?_
  rw [← quotient_mk_maps_eq]
  refine ((Ideal.Quotient.mk P').isIntegral_of_surjective Quotient.mk_surjective).trans _ _ ?_
  have : IsMaximal (Ideal.map (mapRingHom (Ideal.Quotient.mk (comap C P))) P) :=
    Or.recOn (map_eq_top_or_isMaximal_of_surjective f hf hP)
      (fun h => absurd (_root_.trans (h ▸ hPJ : P = comap f ⊤) comap_top : P = ⊤) hP.ne_top) id
  apply quotient_mk_comp_C_isIntegral_of_jacobson' _ ?_ (fun x hx => ?_)
  any_goals exact isJacobsonRing_quotient
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rwa [Quotient.eq_zero_iff_mem, mem_comap, hPJ, mem_comap, coe_mapRingHom, map_C]

theorem isMaximal_comap_C_of_isJacobsonRing : (P.comap (C : R →+* R[X])).IsMaximal := by
  rw [← @mk_ker _ _ P, RingHom.ker_eq_comap_bot, comap_comap]
  have := (bot_quotient_isMaximal_iff _).mpr hP
  exact isMaximal_comap_of_isIntegral_of_isMaximal' _
    (quotient_mk_comp_C_isIntegral_of_isJacobsonRing P) ⊥

theorem comp_C_integral_of_surjective_of_isJacobsonRing {S : Type*} [Field S] (f : R[X] →+* S)
    (hf : Function.Surjective ↑f) : (f.comp C).IsIntegral := by
  have : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hf
  let g : R[X] ⧸ (RingHom.ker f) →+* S := Ideal.Quotient.lift (RingHom.ker f) f fun _ h => h
  have hfg : g.comp (Ideal.Quotient.mk (RingHom.ker f)) = f := ringHom_ext' rfl rfl
  rw [← hfg, RingHom.comp_assoc]
  refine (quotient_mk_comp_C_isIntegral_of_isJacobsonRing (RingHom.ker f)).trans _ g
    (g.isIntegral_of_surjective ?_)
  rw [← hfg] at hf
  norm_num at hf
  exact Function.Surjective.of_comp hf

end

end Polynomial

open MvPolynomial RingHom

namespace MvPolynomial

theorem isJacobsonRing_MvPolynomial_fin {R : Type u} [CommRing R] [H : IsJacobsonRing R] :
    ∀ n : ℕ, IsJacobsonRing (MvPolynomial (Fin n) R)
  | 0 => (isJacobsonRing_iso ((renameEquiv R (Equiv.equivPEmpty (Fin 0))).toRingEquiv.trans
    (isEmptyRingEquiv R PEmpty.{u+1}))).mpr H
  | n + 1 => (isJacobsonRing_iso (finSuccEquiv R n).toRingEquiv).2
    (Polynomial.isJacobsonRing_polynomial_iff_isJacobsonRing.2 (isJacobsonRing_MvPolynomial_fin n))

/-- General form of the Nullstellensatz for Jacobson rings, since in a Jacobson ring we have
  `Inf {P maximal | P ≥ I} = Inf {P prime | P ≥ I} = I.radical`. Fields are always Jacobson,
  and in that special case this is (most of) the classical Nullstellensatz,
  since `I(V(I))` is the intersection of maximal ideals containing `I`, which is then `I.radical` -/
instance isJacobsonRing {R : Type*} [CommRing R] {ι : Type*} [Finite ι] [IsJacobsonRing R] :
    IsJacobsonRing (MvPolynomial ι R) := by
  cases nonempty_fintype ι
  let e := Fintype.equivFin ι
  rw [isJacobsonRing_iso (renameEquiv R e).toRingEquiv]
  exact isJacobsonRing_MvPolynomial_fin _

variable {n : ℕ}

universe v w

/-- The constant coefficient as an R-linear morphism -/
private noncomputable def Cₐ (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] : S →ₐ[R] S[X] :=
  { Polynomial.C with commutes' := fun r => by rfl }

private lemma aux_IH {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] [IsJacobsonRing S] [Algebra R S] [Algebra R T]
    (IH : ∀ (Q : Ideal S), (IsMaximal Q) → RingHom.IsIntegral (algebraMap R (S ⧸ Q)))
    (v : S[X] ≃ₐ[R] T) (P : Ideal T) (hP : P.IsMaximal) :
    RingHom.IsIntegral (algebraMap R (T ⧸ P)) := by
  let Q := P.comap v.toAlgHom.toRingHom
  have hw : Ideal.map v Q = P := map_comap_of_surjective v v.surjective P
  have hQ : IsMaximal Q := comap_isMaximal_of_surjective _ v.surjective
  let w : (S[X] ⧸ Q) ≃ₐ[R] (T ⧸ P) := Ideal.quotientEquivAlg Q P v hw.symm
  let Q' := Q.comap (Polynomial.C)
  let w' : (S ⧸ Q') →ₐ[R] (S[X] ⧸ Q) := Ideal.quotientMapₐ Q (Cₐ R S) le_rfl
  have h_eq : algebraMap R (T ⧸ P) =
    w.toRingEquiv.toRingHom.comp (w'.toRingHom.comp (algebraMap R (S ⧸ Q'))) := by
    ext r
    simp only [AlgHom.toRingHom_eq_coe, AlgEquiv.toRingEquiv_eq_coe,
      RingEquiv.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower, coe_comp, coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes]
  rw [h_eq]
  apply RingHom.IsIntegral.trans
  · apply RingHom.IsIntegral.trans
    · apply IH
      apply Polynomial.isMaximal_comap_C_of_isJacobsonRing
    · suffices w'.toRingHom = Ideal.quotientMap Q (Polynomial.C) le_rfl by
        rw [this]
        rw [isIntegral_quotientMap_iff _]
        apply Polynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing
      rfl
  · apply RingHom.isIntegral_of_surjective
    exact w.surjective

private theorem quotient_mk_comp_C_isIntegral_of_isJacobsonRing'
    {R : Type*} [CommRing R] [IsJacobsonRing R]
    (P : Ideal (MvPolynomial (Fin n) R)) (hP : P.IsMaximal) :
    RingHom.IsIntegral (algebraMap R (MvPolynomial (Fin n) R ⧸ P)) := by
  induction n with
  | zero =>
    apply RingHom.isIntegral_of_surjective
    apply Function.Surjective.comp Quotient.mk_surjective
    exact C_surjective (Fin 0)
  | succ n IH => apply aux_IH IH (finSuccEquiv R n).symm P hP

theorem quotient_mk_comp_C_isIntegral_of_isJacobsonRing {R : Type*} [CommRing R] [IsJacobsonRing R]
    (P : Ideal (MvPolynomial (Fin n) R)) [hP : P.IsMaximal] :
    RingHom.IsIntegral (RingHom.comp (Ideal.Quotient.mk P) (MvPolynomial.C)) := by
  change RingHom.IsIntegral (algebraMap R (MvPolynomial (Fin n) R ⧸ P))
  apply quotient_mk_comp_C_isIntegral_of_isJacobsonRing'
  infer_instance

theorem comp_C_integral_of_surjective_of_isJacobsonRing {R : Type*} [CommRing R] [IsJacobsonRing R]
    {σ : Type*} [Finite σ] {S : Type*} [Field S] (f : MvPolynomial σ R →+* S)
    (hf : Function.Surjective ↑f) : (f.comp C).IsIntegral := by
  cases nonempty_fintype σ
  have e := (Fintype.equivFin σ).symm
  let f' : MvPolynomial (Fin _) R →+* S := f.comp (renameEquiv R e).toRingEquiv.toRingHom
  have hf' := Function.Surjective.comp hf (renameEquiv R e).surjective
  change Function.Surjective ↑f' at hf'
  have : (f'.comp C).IsIntegral := by
    have : (RingHom.ker f').IsMaximal := ker_isMaximal_of_surjective f' hf'
    let g : MvPolynomial _ R ⧸ (RingHom.ker f') →+* S :=
      Ideal.Quotient.lift (RingHom.ker f') f' fun _ h => h
    have hfg : g.comp (Ideal.Quotient.mk (RingHom.ker f')) = f' :=
      ringHom_ext (fun r => rfl) fun i => rfl
    rw [← hfg, RingHom.comp_assoc]
    refine (quotient_mk_comp_C_isIntegral_of_isJacobsonRing (RingHom.ker f')).trans _ g
      (g.isIntegral_of_surjective ?_)
    rw [← hfg] at hf'
    norm_num at hf'
    exact Function.Surjective.of_comp hf'
  rw [RingHom.comp_assoc] at this
  convert this
  refine RingHom.ext fun x => ?_
  exact ((renameEquiv R e).commutes' x).symm

end MvPolynomial

lemma isJacobsonRing_of_finiteType {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsJacobsonRing A] [Algebra.FiniteType A B] : IsJacobsonRing B := by
  obtain ⟨ι, hι, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp ‹_›
  exact isJacobsonRing_of_surjective ⟨f.toRingHom, hf⟩

lemma RingHom.FiniteType.isJacobsonRing {A B : Type*} [CommRing A] [CommRing B]
    {f : A →+* B} [IsJacobsonRing A] (H : f.FiniteType) : IsJacobsonRing B :=
  @isJacobsonRing_of_finiteType A B _ _ f.toAlgebra _ H

@[stacks 0CY7 "See also https://en.wikipedia.org/wiki/Zariski%27s_lemma."]
lemma finite_of_finite_type_of_isJacobsonRing (R S : Type*) [CommRing R] [Field S]
    [Algebra R S] [IsJacobsonRing R] [Algebra.FiniteType R S] :
    Module.Finite R S := by
  obtain ⟨ι, hι, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp ‹_›
  have : (algebraMap R S).IsIntegral := by
    rw [← f.comp_algebraMap]
    -- We need to write `f.toRingHom` instead of just `f`, to avoid unification issues.
    exact MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing f.toRingHom hf
  have : Algebra.IsIntegral R S := Algebra.isIntegral_def.mpr this
  exact Algebra.IsIntegral.finite

/--
If `f : R →+* S` is a ring homomorphism from a Jacobson ring to a field,
then it is finite if and only if it is finite type.
-/
lemma RingHom.finite_iff_finiteType_of_isJacobsonRing
    {R S : Type*} [CommRing R] [IsJacobsonRing R] [Field S]
    {f : R →+* S} : f.Finite ↔ f.FiniteType :=
  ⟨RingHom.FiniteType.of_finite,
    by intro; algebraize [f]; exact finite_of_finite_type_of_isJacobsonRing R S⟩

/-- If `K` is a Jacobson Noetherian ring, `A` a nontrivial `K`-algebra of finite type,
then any `K`-subfield of `A` is finite over `K`. -/
theorem finite_of_algHom_finiteType_of_isJacobsonRing
    {K L A : Type*} [CommRing K] [DivisionRing L] [CommRing A]
    [IsJacobsonRing K] [IsNoetherianRing K] [Nontrivial A]
    [Algebra K L] [Algebra K A]
    [Algebra.FiniteType K A] (f : L →ₐ[K] A) :
    Module.Finite K L := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI := Ideal.Quotient.field m
  have := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  exact Module.Finite.of_injective ((Ideal.Quotient.mkₐ K m).comp f).toLinearMap
    (RingHom.injective _)

/-- If `K` is a Jacobson Noetherian ring, `A` a nontrivial `K`-algebra of finite type,
then any `K`-subfield of `A` is finite over `K`. -/
nonrec theorem RingHom.finite_of_algHom_finiteType_of_isJacobsonRing
    {K L A : Type*} [CommRing K] [Field L] [CommRing A]
    [IsJacobsonRing K] [IsNoetherianRing K] [Nontrivial A]
    (f : K →+* L) (g : L →+* A) (hfg : (g.comp f).FiniteType) :
    f.Finite := by
  algebraize [f, (g.comp f)]
  exact finite_of_algHom_finiteType_of_isJacobsonRing ⟨g, fun _ ↦ rfl⟩
