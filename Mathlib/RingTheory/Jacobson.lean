/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.JacobsonIdeal

#align_import ring_theory.jacobson from "leanprover-community/mathlib"@"a7c017d750512a352b623b1824d75da5998457d0"

/-!
# Jacobson Rings
The following conditions are equivalent for a ring `R`:
1. Every radical ideal `I` is equal to its Jacobson radical
2. Every radical ideal `I` can be written as an intersection of maximal ideals
3. Every prime ideal `I` is equal to its Jacobson radical
Any ring satisfying any of these equivalent conditions is said to be Jacobson.
Some particular examples of Jacobson rings are also proven.
`isJacobson_quotient` says that the quotient of a Jacobson ring is Jacobson.
`isJacobson_localization` says the localization of a Jacobson ring to a single element is Jacobson.
`isJacobson_polynomial_iff_isJacobson` says polynomials over a Jacobson ring form a Jacobson ring.
## Main definitions
Let `R` be a commutative ring. Jacobson rings are defined using the first of the above conditions
* `IsJacobson R` is the proposition that `R` is a Jacobson ring. It is a class,
  implemented as the predicate that for any ideal, `I.isRadical` implies `I.jacobson = I`.

## Main statements
* `isJacobson_iff_prime_eq` is the equivalence between conditions 1 and 3 above.
* `isJacobson_iff_sInf_maximal` is the equivalence between conditions 1 and 2 above.
* `isJacobson_of_surjective` says that if `R` is a Jacobson ring and `f : R →+* S` is surjective,
  then `S` is also a Jacobson ring
* `MvPolynomial.isJacobson` says that multi-variate polynomials over a Jacobson ring are Jacobson.
## Tags
Jacobson, Jacobson Ring
-/

set_option autoImplicit true

universe u
namespace Ideal

open Polynomial

open Polynomial

section IsJacobson

variable {R S : Type*} [CommRing R] [CommRing S] {I : Ideal R}

/-- A ring is a Jacobson ring if for every radical ideal `I`,
 the Jacobson radical of `I` is equal to `I`.
 See `isJacobson_iff_prime_eq` and `isJacobson_iff_sInf_maximal` for equivalent definitions. -/
class IsJacobson (R : Type*) [CommRing R] : Prop where
  out' : ∀ I : Ideal R, I.IsRadical → I.jacobson = I
#align ideal.is_jacobson Ideal.IsJacobson

theorem isJacobson_iff {R} [CommRing R] :
    IsJacobson R ↔ ∀ I : Ideal R, I.IsRadical → I.jacobson = I :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align ideal.is_jacobson_iff Ideal.isJacobson_iff

theorem IsJacobson.out {R} [CommRing R] :
    IsJacobson R → ∀ {I : Ideal R}, I.IsRadical → I.jacobson = I :=
  isJacobson_iff.1
#align ideal.is_jacobson.out Ideal.IsJacobson.out

/-- A ring is a Jacobson ring if and only if for all prime ideals `P`,
 the Jacobson radical of `P` is equal to `P`. -/
theorem isJacobson_iff_prime_eq : IsJacobson R ↔ ∀ P : Ideal R, IsPrime P → P.jacobson = P := by
  refine' isJacobson_iff.trans ⟨fun h I hI => h I hI.isRadical, _⟩
  -- ⊢ (∀ (P : Ideal R), IsPrime P → jacobson P = P) → ∀ (I : Ideal R), IsRadical I …
  refine fun h I hI ↦ le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ mem_sInf.mpr fun _ hJ ↦ hJ.left hx)
  -- ⊢ x ∈ I
  rw [← hI.radical, radical_eq_sInf I, mem_sInf]
  -- ⊢ ∀ ⦃I_1 : Ideal R⦄, I_1 ∈ {J | I ≤ J ∧ IsPrime J} → x ∈ I_1
  intro P hP
  -- ⊢ x ∈ P
  rw [Set.mem_setOf_eq] at hP
  -- ⊢ x ∈ P
  erw [mem_sInf] at hx
  -- ⊢ x ∈ P
  erw [← h P hP.right, mem_sInf]
  -- ⊢ ∀ ⦃I : Ideal R⦄, I ∈ {J | P ≤ J ∧ IsMaximal J} → x ∈ I
  exact fun J hJ => hx ⟨le_trans hP.left hJ.left, hJ.right⟩
  -- 🎉 no goals
#align ideal.is_jacobson_iff_prime_eq Ideal.isJacobson_iff_prime_eq

/-- A ring `R` is Jacobson if and only if for every prime ideal `I`,
 `I` can be written as the infimum of some collection of maximal ideals.
 Allowing ⊤ in the set `M` of maximal ideals is equivalent, but makes some proofs cleaner. -/
theorem isJacobson_iff_sInf_maximal : IsJacobson R ↔ ∀ {I : Ideal R}, I.IsPrime →
    ∃ M : Set (Ideal R), (∀ J ∈ M, IsMaximal J ∨ J = ⊤) ∧ I = sInf M :=
  ⟨fun H _I h => eq_jacobson_iff_sInf_maximal.1 (H.out h.isRadical), fun H =>
    isJacobson_iff_prime_eq.2 fun _P hP => eq_jacobson_iff_sInf_maximal.2 (H hP)⟩
#align ideal.is_jacobson_iff_Inf_maximal Ideal.isJacobson_iff_sInf_maximal

theorem isJacobson_iff_sInf_maximal' : IsJacobson R ↔ ∀ {I : Ideal R}, I.IsPrime →
    ∃ M : Set (Ideal R), (∀ J ∈ M, ∀ (K : Ideal R), J < K → K = ⊤) ∧ I = sInf M :=
  ⟨fun H _I h => eq_jacobson_iff_sInf_maximal'.1 (H.out h.isRadical), fun H =>
    isJacobson_iff_prime_eq.2 fun _P hP => eq_jacobson_iff_sInf_maximal'.2 (H hP)⟩
#align ideal.is_jacobson_iff_Inf_maximal' Ideal.isJacobson_iff_sInf_maximal'

theorem radical_eq_jacobson [H : IsJacobson R] (I : Ideal R) : I.radical = I.jacobson :=
  le_antisymm (le_sInf fun _J ⟨hJ, hJ_max⟩ => (IsPrime.radical_le_iff hJ_max.isPrime).mpr hJ)
    (H.out (radical_isRadical I) ▸ jacobson_mono le_radical)
#align ideal.radical_eq_jacobson Ideal.radical_eq_jacobson

/-- Fields have only two ideals, and the condition holds for both of them. -/
instance (priority := 100) isJacobson_field {K : Type*} [Field K] : IsJacobson K :=
  ⟨fun I _ => Or.recOn (eq_bot_or_top I)
    (fun h => le_antisymm (sInf_le ⟨le_rfl, h.symm ▸ bot_isMaximal⟩) (h.symm ▸ bot_le)) fun h =>
      by rw [h, jacobson_eq_top_iff]⟩
         -- 🎉 no goals
#align ideal.is_jacobson_field Ideal.isJacobson_field

theorem isJacobson_of_surjective [H : IsJacobson R] :
    (∃ f : R →+* S, Function.Surjective ↑f) → IsJacobson S := by
  rintro ⟨f, hf⟩
  -- ⊢ IsJacobson S
  rw [isJacobson_iff_sInf_maximal]
  -- ⊢ ∀ {I : Ideal S}, IsPrime I → ∃ M, (∀ (J : Ideal S), J ∈ M → IsMaximal J ∨ J  …
  intro p hp
  -- ⊢ ∃ M, (∀ (J : Ideal S), J ∈ M → IsMaximal J ∨ J = ⊤) ∧ p = sInf M
  use map f '' { J : Ideal R | comap f p ≤ J ∧ J.IsMaximal }
  -- ⊢ (∀ (J : Ideal S), J ∈ map f '' {J | comap f p ≤ J ∧ IsMaximal J} → IsMaximal …
  use fun j ⟨J, hJ, hmap⟩ => hmap ▸ (map_eq_top_or_isMaximal_of_surjective f hf hJ.right).symm
  -- ⊢ p = sInf (map f '' {J | comap f p ≤ J ∧ IsMaximal J})
  have : p = map f (comap f p).jacobson :=
    (IsJacobson.out' _ <| hp.isRadical.comap f).symm ▸ (map_comap_of_surjective f hf p).symm
  exact this.trans (map_sInf hf fun J ⟨hJ, _⟩ => le_trans (Ideal.ker_le_comap f) hJ)
  -- 🎉 no goals
#align ideal.is_jacobson_of_surjective Ideal.isJacobson_of_surjective

instance (priority := 100) isJacobson_quotient [IsJacobson R] : IsJacobson (R ⧸ I) :=
  isJacobson_of_surjective ⟨Quotient.mk I, by
    rintro ⟨x⟩
    -- ⊢ ∃ a, ↑(Quotient.mk I) a = Quot.mk Setoid.r x
    use x
    -- ⊢ ↑(Quotient.mk I) x = Quot.mk Setoid.r x
    rfl⟩
    -- 🎉 no goals
#align ideal.is_jacobson_quotient Ideal.isJacobson_quotient

theorem isJacobson_iso (e : R ≃+* S) : IsJacobson R ↔ IsJacobson S :=
  ⟨fun h => @isJacobson_of_surjective _ _ _ _ h ⟨(e : R →+* S), e.surjective⟩, fun h =>
    @isJacobson_of_surjective _ _ _ _ h ⟨(e.symm : S →+* R), e.symm.surjective⟩⟩
#align ideal.is_jacobson_iso Ideal.isJacobson_iso

theorem isJacobson_of_isIntegral [Algebra R S] (hRS : Algebra.IsIntegral R S) (hR : IsJacobson R) :
    IsJacobson S := by
  rw [isJacobson_iff_prime_eq]
  -- ⊢ ∀ (P : Ideal S), IsPrime P → jacobson P = P
  intro P hP
  -- ⊢ jacobson P = P
  by_cases hP_top : comap (algebraMap R S) P = ⊤
  -- ⊢ jacobson P = P
  · simp [comap_eq_top_iff.1 hP_top]
    -- 🎉 no goals
  · haveI : Nontrivial (R ⧸ comap (algebraMap R S) P) := Quotient.nontrivial hP_top
    -- ⊢ jacobson P = P
    rw [jacobson_eq_iff_jacobson_quotient_eq_bot]
    -- ⊢ jacobson ⊥ = ⊥
    refine' eq_bot_of_comap_eq_bot (isIntegral_quotient_of_isIntegral hRS) _
    -- ⊢ comap (algebraMap (R ⧸ comap (algebraMap R S) P) (S ⧸ P)) (jacobson ⊥) = ⊥
    rw [eq_bot_iff, ← jacobson_eq_iff_jacobson_quotient_eq_bot.1
      ((isJacobson_iff_prime_eq.1 hR) (comap (algebraMap R S) P) (comap_isPrime _ _)),
      comap_jacobson]
    refine' sInf_le_sInf fun J hJ => _
    -- ⊢ J ∈ comap (algebraMap (R ⧸ comap (algebraMap R S) P) (S ⧸ P)) '' {J | ⊥ ≤ J  …
    simp only [true_and_iff, Set.mem_image, bot_le, Set.mem_setOf_eq]
    -- ⊢ ∃ x, IsMaximal x ∧ comap (algebraMap (R ⧸ comap (algebraMap R S) P) (S ⧸ P)) …
    have : J.IsMaximal := by simpa using hJ
    -- ⊢ ∃ x, IsMaximal x ∧ comap (algebraMap (R ⧸ comap (algebraMap R S) P) (S ⧸ P)) …
    exact exists_ideal_over_maximal_of_isIntegral (isIntegral_quotient_of_isIntegral hRS) J
      (comap_bot_le_of_injective _ algebraMap_quotient_injective)
#align ideal.is_jacobson_of_is_integral Ideal.isJacobson_of_isIntegral

theorem isJacobson_of_isIntegral' (f : R →+* S) (hf : f.IsIntegral) (hR : IsJacobson R) :
    IsJacobson S := @isJacobson_of_isIntegral _ _ _ _ f.toAlgebra hf hR
#align ideal.is_jacobson_of_is_integral' Ideal.isJacobson_of_isIntegral'

end IsJacobson

section Localization

open IsLocalization Submonoid

variable {R S : Type*} [CommRing R] [CommRing S] {I : Ideal R}

variable (y : R) [Algebra R S] [IsLocalization.Away y S]

theorem disjoint_powers_iff_not_mem (hI : I.IsRadical) :
    Disjoint (Submonoid.powers y : Set R) ↑I ↔ y ∉ I.1 := by
  refine'
    ⟨fun h => Set.disjoint_left.1 h (mem_powers _), fun h => disjoint_iff.mpr (eq_bot_iff.mpr _)⟩
  rintro x ⟨⟨n, rfl⟩, hx'⟩
  -- ⊢ (fun x x_1 => x ^ x_1) y n ∈ ⊥
  exact h (hI <| mem_radical_of_pow_mem <| le_radical hx')
  -- 🎉 no goals
#align ideal.disjoint_powers_iff_not_mem Ideal.disjoint_powers_iff_not_mem

variable (S)

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its comap.
See `le_relIso_of_maximal` for the more general relation isomorphism -/
theorem isMaximal_iff_isMaximal_disjoint [H : IsJacobson R] (J : Ideal S) :
    J.IsMaximal ↔ (comap (algebraMap R S) J).IsMaximal ∧ y ∉ Ideal.comap (algebraMap R S) J := by
  constructor
  -- ⊢ IsMaximal J → IsMaximal (comap (algebraMap R S) J) ∧ ¬y ∈ comap (algebraMap  …
  · refine' fun h => ⟨_, fun hy =>
      h.ne_top (Ideal.eq_top_of_isUnit_mem _ hy (map_units _ ⟨y, Submonoid.mem_powers _⟩))⟩
    have hJ : J.IsPrime := IsMaximal.isPrime h
    -- ⊢ IsMaximal (comap (algebraMap R S) J)
    rw [isPrime_iff_isPrime_disjoint (Submonoid.powers y)] at hJ
    -- ⊢ IsMaximal (comap (algebraMap R S) J)
    have : y ∉ (comap (algebraMap R S) J).1 := Set.disjoint_left.1 hJ.right (Submonoid.mem_powers _)
    -- ⊢ IsMaximal (comap (algebraMap R S) J)
    erw [← H.out hJ.left.isRadical, mem_sInf] at this
    -- ⊢ IsMaximal (comap (algebraMap R S) J)
    push_neg at this
    -- ⊢ IsMaximal (comap (algebraMap R S) J)
    rcases this with ⟨I, hI, hI'⟩
    -- ⊢ IsMaximal (comap (algebraMap R S) J)
    convert hI.right
    -- ⊢ comap (algebraMap R S) J = I
    by_cases hJ : J = map (algebraMap R S) I
    -- ⊢ comap (algebraMap R S) J = I
    · rw [hJ, comap_map_of_isPrime_disjoint (powers y) S I (IsMaximal.isPrime hI.right)]
      -- ⊢ Disjoint ↑(powers y) ↑I
      rwa [disjoint_powers_iff_not_mem y hI.right.isPrime.isRadical]
      -- 🎉 no goals
    · have hI_p : (map (algebraMap R S) I).IsPrime := by
        refine' isPrime_of_isPrime_disjoint (powers y) _ I hI.right.isPrime _
        rwa [disjoint_powers_iff_not_mem y hI.right.isPrime.isRadical]
      have : J ≤ map (algebraMap R S) I := map_comap (Submonoid.powers y) S J ▸ map_mono hI.left
      -- ⊢ comap (algebraMap R S) J = I
      exact absurd (h.1.2 _ (lt_of_le_of_ne this hJ)) hI_p.1
      -- 🎉 no goals
  · refine' fun h => ⟨⟨fun hJ => h.1.ne_top (eq_top_iff.2 _), fun I hI => _⟩⟩
    -- ⊢ ⊤ ≤ comap (algebraMap R S) J
    · rwa [eq_top_iff, ← (IsLocalization.orderEmbedding (powers y) S).le_iff_le] at hJ
      -- 🎉 no goals
    · have := congr_arg (map (algebraMap R S)) (h.1.1.2 _ ⟨comap_mono (le_of_lt hI), ?_⟩)
      -- ⊢ I = ⊤
      rwa [map_comap (powers y) S I, map_top] at this
      -- ⊢ ¬↑(comap (algebraMap R S) I) ⊆ ↑(comap (algebraMap R S) J)
      refine' fun hI' => hI.right _
      -- ⊢ ↑I ⊆ ↑J
      rw [← map_comap (powers y) S I, ← map_comap (powers y) S J]
      -- ⊢ ↑(map (algebraMap R S) (comap (algebraMap R S) I)) ⊆ ↑(map (algebraMap R S)  …
      exact map_mono hI'
      -- 🎉 no goals
#align ideal.is_maximal_iff_is_maximal_disjoint Ideal.isMaximal_iff_isMaximal_disjoint

variable {S}

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its map.
See `le_relIso_of_maximal` for the more general statement, and the reverse of this implication -/
theorem isMaximal_of_isMaximal_disjoint [IsJacobson R] (I : Ideal R) (hI : I.IsMaximal)
    (hy : y ∉ I) : (map (algebraMap R S) I).IsMaximal := by
  rw [isMaximal_iff_isMaximal_disjoint S y,
    comap_map_of_isPrime_disjoint (powers y) S I (IsMaximal.isPrime hI)
      ((disjoint_powers_iff_not_mem y hI.isPrime.isRadical).2 hy)]
  exact ⟨hI, hy⟩
  -- 🎉 no goals
#align ideal.is_maximal_of_is_maximal_disjoint Ideal.isMaximal_of_isMaximal_disjoint

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y` -/
def orderIsoOfMaximal [IsJacobson R] :
    { p : Ideal S // p.IsMaximal } ≃o { p : Ideal R // p.IsMaximal ∧ y ∉ p } where
  toFun p := ⟨Ideal.comap (algebraMap R S) p.1, (isMaximal_iff_isMaximal_disjoint S y p.1).1 p.2⟩
  invFun p := ⟨Ideal.map (algebraMap R S) p.1, isMaximal_of_isMaximal_disjoint y p.1 p.2.1 p.2.2⟩
  left_inv J := Subtype.eq (map_comap (powers y) S J)
  right_inv I := Subtype.eq (comap_map_of_isPrime_disjoint _ _ I.1 (IsMaximal.isPrime I.2.1)
    ((disjoint_powers_iff_not_mem y I.2.1.isPrime.isRadical).2 I.2.2))
  map_rel_iff' {I I'} := ⟨fun h => show I.val ≤ I'.val from
    map_comap (powers y) S I.val ▸ map_comap (powers y) S I'.val ▸ Ideal.map_mono h,
    fun h _ hx => h hx⟩
#align ideal.order_iso_of_maximal Ideal.orderIsoOfMaximal

/-- If `S` is the localization of the Jacobson ring `R` at the submonoid generated by `y : R`, then
`S` is Jacobson. -/
theorem isJacobson_localization [H : IsJacobson R] : IsJacobson S := by
  rw [isJacobson_iff_prime_eq]
  -- ⊢ ∀ (P : Ideal S), IsPrime P → jacobson P = P
  refine' fun P' hP' => le_antisymm _ le_jacobson
  -- ⊢ jacobson P' ≤ P'
  obtain ⟨hP', hPM⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint (powers y) S P').mp hP'
  -- ⊢ jacobson P' ≤ P'
  have hP := H.out hP'.isRadical
  -- ⊢ jacobson P' ≤ P'
  refine' (IsLocalization.map_comap (powers y) S P'.jacobson).ge.trans
    ((map_mono _).trans (IsLocalization.map_comap (powers y) S P').le)
  have : sInf { I : Ideal R | comap (algebraMap R S) P' ≤ I ∧ I.IsMaximal ∧ y ∉ I } ≤
      comap (algebraMap R S) P' := by
    intro x hx
    have hxy : x * y ∈ (comap (algebraMap R S) P').jacobson := by
      rw [Ideal.jacobson, mem_sInf]
      intro J hJ
      by_cases y ∈ J
      · exact J.mul_mem_left x h
      · exact J.mul_mem_right y ((mem_sInf.1 hx) ⟨hJ.left, ⟨hJ.right, h⟩⟩)
    rw [hP] at hxy
    cases' hP'.mem_or_mem hxy with hxy hxy
    · exact hxy
    · exact (hPM.le_bot ⟨Submonoid.mem_powers _, hxy⟩).elim
  refine' le_trans _ this
  -- ⊢ comap (algebraMap R S) (jacobson P') ≤ sInf {I | comap (algebraMap R S) P' ≤ …
  rw [Ideal.jacobson, comap_sInf', sInf_eq_iInf]
  -- ⊢ ⨅ (I : Ideal R) (_ : I ∈ comap (algebraMap R S) '' {J | P' ≤ J ∧ IsMaximal J …
  refine' iInf_le_iInf_of_subset fun I hI => ⟨map (algebraMap R S) I, ⟨_, _⟩⟩
  -- ⊢ map (algebraMap R S) I ∈ {J | P' ≤ J ∧ IsMaximal J}
  · exact ⟨le_trans (le_of_eq (IsLocalization.map_comap (powers y) S P').symm) (map_mono hI.1),
      isMaximal_of_isMaximal_disjoint y _ hI.2.1 hI.2.2⟩
  · exact IsLocalization.comap_map_of_isPrime_disjoint _ S I (IsMaximal.isPrime hI.2.1)
      ((disjoint_powers_iff_not_mem y hI.2.1.isPrime.isRadical).2 hI.2.2)
#align ideal.is_jacobson_localization Ideal.isJacobson_localization

end Localization

namespace Polynomial

open Polynomial

section CommRing

-- Porting note: move to better place
-- Porting note: make `S` and `T` universe polymorphic
lemma Subring.mem_closure_image_of {S T : Type*} [CommRing S] [CommRing T] (g : S →+* T)
    (u : Set S) (x : S) (hx : x ∈ Subring.closure u) : g x ∈ Subring.closure (g '' u) := by
  rw [Subring.mem_closure] at hx ⊢
  -- ⊢ ∀ (S_1 : Subring ((fun x => T) x)), ↑g '' u ⊆ ↑S_1 → ↑g x ∈ S_1
  intro T₁ h₁
  -- ⊢ ↑g x ∈ T₁
  rw [← Subring.mem_comap]
  -- ⊢ x ∈ Subring.comap g T₁
  apply hx
  -- ⊢ u ⊆ ↑(Subring.comap g T₁)
  simp only [Subring.coe_comap, ← Set.image_subset_iff, SetLike.mem_coe]
  -- ⊢ ↑g '' u ⊆ ↑T₁
  exact h₁
  -- 🎉 no goals

-- Porting note: move to better place
lemma mem_closure_X_union_C {R : Type*} [Ring R] (p : R[X]) :
    p ∈ Subring.closure (insert X {f | f.degree ≤ 0} : Set R[X]) := by
  refine' Polynomial.induction_on p _ _ _
  · intro r
    -- ⊢ ↑C r ∈ Subring.closure (insert X {f | degree f ≤ 0})
    apply Subring.subset_closure
    -- ⊢ ↑C r ∈ insert X {f | degree f ≤ 0}
    apply Set.mem_insert_of_mem
    -- ⊢ ↑C r ∈ {f | degree f ≤ 0}
    exact degree_C_le
    -- 🎉 no goals
  · intros p1 p2 h1 h2
    -- ⊢ p1 + p2 ∈ Subring.closure (insert X {f | degree f ≤ 0})
    exact Subring.add_mem _ h1 h2
    -- 🎉 no goals
  · intros n r hr
    -- ⊢ ↑C r * X ^ (n + 1) ∈ Subring.closure (insert X {f | degree f ≤ 0})
    rw [pow_succ', ← mul_assoc]
    -- ⊢ ↑C r * X ^ n * X ∈ Subring.closure (insert X {f | degree f ≤ 0})
    apply Subring.mul_mem _ hr
    -- ⊢ X ∈ Subring.closure (insert X {f | degree f ≤ 0})
    apply Subring.subset_closure
    -- ⊢ X ∈ insert X {f | degree f ≤ 0}
    apply Set.mem_insert
    -- 🎉 no goals

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]

variable {Rₘ Sₘ : Type*} [CommRing Rₘ] [CommRing Sₘ]

set_option maxHeartbeats 300000 in
/-- If `I` is a prime ideal of `R[X]` and `pX ∈ I` is a non-constant polynomial,
  then the map `R →+* R[x]/I` descends to an integral map when localizing at `pX.leadingCoeff`.
  In particular `X` is integral because it satisfies `pX`, and constants are trivially integral,
  so integrality of the entire extension follows by closure under addition and multiplication. -/
theorem isIntegral_isLocalization_polynomial_quotient
    (P : Ideal R[X]) (pX : R[X]) (hpX : pX ∈ P) [Algebra (R ⧸ P.comap (C : R →+* R[X])) Rₘ]
    [IsLocalization.Away (pX.map (Quotient.mk (P.comap (C : R →+* R[X])))).leadingCoeff Rₘ]
    [Algebra (R[X] ⧸ P) Sₘ] [IsLocalization ((Submonoid.powers (pX.map (Quotient.mk (P.comap
      (C : R →+* R[X])))).leadingCoeff).map (quotientMap P C le_rfl) : Submonoid (R[X] ⧸ P)) Sₘ] :
    (IsLocalization.map Sₘ (quotientMap P C le_rfl) (Submonoid.powers (pX.map (Quotient.mk (P.comap
      (C : R →+* R[X])))).leadingCoeff).le_comap_map : Rₘ →+* Sₘ).IsIntegral := by
  let P' : Ideal R := P.comap C
  -- ⊢ RingHom.IsIntegral (IsLocalization.map Sₘ (quotientMap P C (_ : comap C P ≤  …
  let M : Submonoid (R ⧸ P') :=
    Submonoid.powers (pX.map (Quotient.mk (P.comap (C : R →+* R[X])))).leadingCoeff
  let M' : Submonoid (R[X] ⧸ P) :=
    (Submonoid.powers (pX.map (Quotient.mk (P.comap (C : R →+* R[X])))).leadingCoeff).map
      (quotientMap P C le_rfl)
  let φ : R ⧸ P' →+* R[X] ⧸ P := quotientMap P C le_rfl
  -- ⊢ RingHom.IsIntegral (IsLocalization.map Sₘ (quotientMap P C (_ : comap C P ≤  …
  let φ' : Rₘ →+* Sₘ := IsLocalization.map Sₘ φ M.le_comap_map
  -- ⊢ RingHom.IsIntegral (IsLocalization.map Sₘ (quotientMap P C (_ : comap C P ≤  …
  have hφ' : φ.comp (Quotient.mk P') = (Quotient.mk P).comp C := rfl
  -- ⊢ RingHom.IsIntegral (IsLocalization.map Sₘ (quotientMap P C (_ : comap C P ≤  …
  intro p
  -- ⊢ RingHom.IsIntegralElem (IsLocalization.map Sₘ (quotientMap P C (_ : comap C  …
  obtain ⟨⟨p', ⟨q, hq⟩⟩, hp⟩ := IsLocalization.surj M' p
  -- ⊢ RingHom.IsIntegralElem (IsLocalization.map Sₘ (quotientMap P C (_ : comap C  …
  suffices φ'.IsIntegralElem (algebraMap (R[X] ⧸ P) Sₘ p') by
    obtain ⟨q', hq', rfl⟩ := hq
    obtain ⟨q'', hq''⟩ := isUnit_iff_exists_inv'.1 (IsLocalization.map_units Rₘ (⟨q', hq'⟩ : M))
    refine' φ'.isIntegral_of_isIntegral_mul_unit p (algebraMap (R[X] ⧸ P) Sₘ (φ q'))
      q'' _ (hp.symm ▸ this)
    rw [← φ'.map_one, ← congr_arg φ' hq'', φ'.map_mul, ← φ'.comp_apply]
    simp only [IsLocalization.map_comp _]
    rw [RingHom.comp_apply]
  dsimp at hp
  -- ⊢ RingHom.IsIntegralElem φ' (↑(algebraMap (R[X] ⧸ P) Sₘ) p')
  refine' @isIntegral_of_mem_closure'' Rₘ _ Sₘ _ φ'
    ((algebraMap (R[X] ⧸ P) Sₘ).comp (Quotient.mk P) '' insert X { p | p.degree ≤ 0 }) _
    ((algebraMap (R[X] ⧸ P) Sₘ) p') _
  · rintro x ⟨p, hp, rfl⟩
    -- ⊢ RingHom.IsIntegralElem φ' (↑(RingHom.comp (algebraMap (R[X] ⧸ P) Sₘ) (Quotie …
    simp only [Set.mem_insert_iff] at hp
    -- ⊢ RingHom.IsIntegralElem φ' (↑(RingHom.comp (algebraMap (R[X] ⧸ P) Sₘ) (Quotie …
    cases' hp with hy hy
    -- ⊢ RingHom.IsIntegralElem φ' (↑(RingHom.comp (algebraMap (R[X] ⧸ P) Sₘ) (Quotie …
    · rw [hy]
      -- ⊢ RingHom.IsIntegralElem φ' (↑(RingHom.comp (algebraMap (R[X] ⧸ P) Sₘ) (Quotie …
      refine' φ.isIntegralElem_localization_at_leadingCoeff ((Quotient.mk P) X)
        (pX.map (Quotient.mk P')) _ M _
      · rwa [eval₂_map, hφ', ← hom_eval₂, Quotient.eq_zero_iff_mem, eval₂_C_X]
        -- 🎉 no goals
      · use 1
        -- ⊢ (fun x x_1 => x ^ x_1) (Polynomial.leadingCoeff (Polynomial.map (Quotient.mk …
        simp only [pow_one]
        -- 🎉 no goals
    · rw [Set.mem_setOf_eq, degree_le_zero_iff] at hy
      -- ⊢ RingHom.IsIntegralElem φ' (↑(RingHom.comp (algebraMap (R[X] ⧸ P) Sₘ) (Quotie …
      -- Porting note: was `refine' hy.symm ▸`
      -- `⟨X - C (algebraMap _ _ ((Quotient.mk P') (p.coeff 0))), monic_X_sub_C _, _⟩`
      rw [hy]
      -- ⊢ RingHom.IsIntegralElem φ' (↑(RingHom.comp (algebraMap (R[X] ⧸ P) Sₘ) (Quotie …
      use X - C (algebraMap (R ⧸ P') Rₘ ((Quotient.mk P') (p.coeff 0)))
      -- ⊢ Monic (X - ↑C (↑(algebraMap (R ⧸ P') Rₘ) (↑(Quotient.mk P') (coeff p 0)))) ∧ …
      constructor
      -- ⊢ Monic (X - ↑C (↑(algebraMap (R ⧸ P') Rₘ) (↑(Quotient.mk P') (coeff p 0))))
      · apply monic_X_sub_C
        -- 🎉 no goals
      · simp only [eval₂_sub, eval₂_X, eval₂_C]
        -- ⊢ ↑(RingHom.comp (algebraMap (R[X] ⧸ P) Sₘ) (Quotient.mk P)) (↑C (coeff p 0))  …
        rw [sub_eq_zero, ← φ'.comp_apply]
        -- ⊢ ↑(RingHom.comp (algebraMap (R[X] ⧸ P) Sₘ) (Quotient.mk P)) (↑C (coeff p 0))  …
        simp only [IsLocalization.map_comp _]
        -- ⊢ ↑(RingHom.comp (algebraMap (R[X] ⧸ P) Sₘ) (Quotient.mk P)) (↑C (coeff p 0))  …
        rfl
        -- 🎉 no goals
  · obtain ⟨p, rfl⟩ := Quotient.mk_surjective p'
    -- ⊢ ↑(algebraMap (R[X] ⧸ P) Sₘ) (↑(Quotient.mk P) p) ∈ Subring.closure (↑(RingHo …
    rw [← RingHom.comp_apply]
    -- ⊢ ↑(RingHom.comp (algebraMap (R[X] ⧸ P) Sₘ) (Quotient.mk P)) p ∈ Subring.closu …
    apply Subring.mem_closure_image_of
    -- ⊢ p ∈ Subring.closure (insert X {p | degree p ≤ 0})
    apply Polynomial.mem_closure_X_union_C
    -- 🎉 no goals
#align ideal.polynomial.is_integral_is_localization_polynomial_quotient Ideal.Polynomial.isIntegral_isLocalization_polynomial_quotient

/-- If `f : R → S` descends to an integral map in the localization at `x`,
  and `R` is a Jacobson ring, then the intersection of all maximal ideals in `S` is trivial -/
theorem jacobson_bot_of_integral_localization {R : Type*} [CommRing R] [IsDomain R] [IsJacobson R]
    (Rₘ Sₘ : Type*) [CommRing Rₘ] [CommRing Sₘ] (φ : R →+* S) (hφ : Function.Injective ↑φ) (x : R)
    (hx : x ≠ 0) [Algebra R Rₘ] [IsLocalization.Away x Rₘ] [Algebra S Sₘ]
    [IsLocalization ((Submonoid.powers x).map φ : Submonoid S) Sₘ]
    (hφ' :
      RingHom.IsIntegral (IsLocalization.map Sₘ φ (Submonoid.powers x).le_comap_map : Rₘ →+* Sₘ)) :
    (⊥ : Ideal S).jacobson = (⊥ : Ideal S) := by
  have hM : ((Submonoid.powers x).map φ : Submonoid S) ≤ nonZeroDivisors S :=
    map_le_nonZeroDivisors_of_injective φ hφ (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
  letI : IsDomain Sₘ := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  -- ⊢ jacobson ⊥ = ⊥
  let φ' : Rₘ →+* Sₘ := IsLocalization.map _ φ (Submonoid.powers x).le_comap_map
  -- ⊢ jacobson ⊥ = ⊥
  suffices ∀ I : Ideal Sₘ, I.IsMaximal → (I.comap (algebraMap S Sₘ)).IsMaximal by
    have hϕ' : comap (algebraMap S Sₘ) (⊥ : Ideal Sₘ) = (⊥ : Ideal S) := by
      rw [← RingHom.ker_eq_comap_bot, ← RingHom.injective_iff_ker_eq_bot]
      exact IsLocalization.injective Sₘ hM
    have hSₘ : IsJacobson Sₘ := isJacobson_of_isIntegral' φ' hφ' (isJacobson_localization x)
    refine' eq_bot_iff.mpr (le_trans _ (le_of_eq hϕ'))
    rw [← hSₘ.out isRadical_bot_of_noZeroDivisors, comap_jacobson]
    exact sInf_le_sInf fun j hj => ⟨bot_le,
      let ⟨J, hJ⟩ := hj
      hJ.2 ▸ this J hJ.1.2⟩
  intro I hI
  -- ⊢ IsMaximal (comap (algebraMap S Sₘ) I)
  -- Remainder of the proof is pulling and pushing ideals around the square and the quotient square
  haveI : (I.comap (algebraMap S Sₘ)).IsPrime := comap_isPrime _ I
  -- ⊢ IsMaximal (comap (algebraMap S Sₘ) I)
  haveI : (I.comap φ').IsPrime := comap_isPrime φ' I
  -- ⊢ IsMaximal (comap (algebraMap S Sₘ) I)
  haveI : (⊥ : Ideal (S ⧸ I.comap (algebraMap S Sₘ))).IsPrime := bot_prime
  -- ⊢ IsMaximal (comap (algebraMap S Sₘ) I)
  have hcomm : φ'.comp (algebraMap R Rₘ) = (algebraMap S Sₘ).comp φ := IsLocalization.map_comp _
  -- ⊢ IsMaximal (comap (algebraMap S Sₘ) I)
  let f := quotientMap (I.comap (algebraMap S Sₘ)) φ le_rfl
  -- ⊢ IsMaximal (comap (algebraMap S Sₘ) I)
  let g := quotientMap I (algebraMap S Sₘ) le_rfl
  -- ⊢ IsMaximal (comap (algebraMap S Sₘ) I)
  have := isMaximal_comap_of_isIntegral_of_isMaximal' φ' hφ' I hI
  -- ⊢ IsMaximal (comap (algebraMap S Sₘ) I)
  have := ((isMaximal_iff_isMaximal_disjoint Rₘ x _).1 this).left
  -- ⊢ IsMaximal (comap (algebraMap S Sₘ) I)
  have : ((I.comap (algebraMap S Sₘ)).comap φ).IsMaximal := by
    rwa [comap_comap, hcomm, ← comap_comap] at this
  rw [← bot_quotient_isMaximal_iff] at this⊢
  -- ⊢ IsMaximal ⊥
  refine' isMaximal_of_isIntegral_of_isMaximal_comap' f _ ⊥
    ((eq_bot_iff.2 (comap_bot_le_of_injective f quotientMap_injective)).symm ▸ this)
  exact f.isIntegral_tower_bot_of_isIntegral g quotientMap_injective
    ((comp_quotientMap_eq_of_comp_eq hcomm I).symm ▸
      RingHom.isIntegral_trans _ _ (RingHom.isIntegral_of_surjective _
        (IsLocalization.surjective_quotientMap_of_maximal_of_localization (Submonoid.powers x) Rₘ
          (by rwa [comap_comap, hcomm, ← bot_quotient_isMaximal_iff])))
      (RingHom.isIntegral_quotient_of_isIntegral _ hφ'))
#align ideal.polynomial.jacobson_bot_of_integral_localization Ideal.Polynomial.jacobson_bot_of_integral_localization

/-- Used to bootstrap the proof of `isJacobson_polynomial_iff_isJacobson`.
  That theorem is more general and should be used instead of this one. -/
private theorem isJacobson_polynomial_of_domain (R : Type*) [CommRing R] [IsDomain R]
    [hR : IsJacobson R] (P : Ideal R[X]) [IsPrime P] (hP : ∀ x : R, C x ∈ P → x = 0) :
    P.jacobson = P := by
  by_cases Pb : P = ⊥
  -- ⊢ jacobson P = P
  · exact Pb.symm ▸
      jacobson_bot_polynomial_of_jacobson_bot (hR.out isRadical_bot_of_noZeroDivisors)
  · rw [jacobson_eq_iff_jacobson_quotient_eq_bot]
    -- ⊢ jacobson ⊥ = ⊥
    let P' := P.comap (C : R →+* R[X])
    -- ⊢ jacobson ⊥ = ⊥
    haveI : P'.IsPrime := comap_isPrime C P
    -- ⊢ jacobson ⊥ = ⊥
    haveI hR' : IsJacobson (R ⧸ P') := by infer_instance
    -- ⊢ jacobson ⊥ = ⊥
    obtain ⟨p, pP, p0⟩ := exists_nonzero_mem_of_ne_bot Pb hP
    -- ⊢ jacobson ⊥ = ⊥
    let x := (Polynomial.map (Quotient.mk P') p).leadingCoeff
    -- ⊢ jacobson ⊥ = ⊥
    have hx : x ≠ 0 := by rwa [Ne.def, leadingCoeff_eq_zero]
    -- ⊢ jacobson ⊥ = ⊥
    let φ : R ⧸ P' →+* R[X] ⧸ P := Ideal.quotientMap P (C : R →+* R[X]) le_rfl
    -- ⊢ jacobson ⊥ = ⊥
    let hφ : Function.Injective ↑φ := quotientMap_injective
    -- ⊢ jacobson ⊥ = ⊥
    let Rₘ := Localization.Away x
    -- ⊢ jacobson ⊥ = ⊥
    let Sₘ := (Localization ((Submonoid.powers x).map φ : Submonoid (R[X] ⧸ P)))
    -- ⊢ jacobson ⊥ = ⊥
    refine' jacobson_bot_of_integral_localization (S := R[X] ⧸ P) (R := R ⧸ P') Rₘ Sₘ _ hφ _ hx _
    -- ⊢ RingHom.IsIntegral (IsLocalization.map Sₘ φ (_ : Submonoid.powers x ≤ Submon …
    haveI islocSₘ : IsLocalization (Submonoid.map φ (Submonoid.powers x)) Sₘ := by infer_instance
    -- ⊢ RingHom.IsIntegral (IsLocalization.map Sₘ φ (_ : Submonoid.powers x ≤ Submon …
    exact @isIntegral_isLocalization_polynomial_quotient R _ Rₘ Sₘ _ _ P p pP _ _ _ islocSₘ
    -- 🎉 no goals

set_option maxHeartbeats 300000 in
theorem isJacobson_polynomial_of_isJacobson (hR : IsJacobson R) : IsJacobson R[X] := by
  rw [isJacobson_iff_prime_eq]
  -- ⊢ ∀ (P : Ideal R[X]), IsPrime P → jacobson P = P
  intro I hI
  -- ⊢ jacobson I = I
  let R' : Subring (R[X] ⧸ I) := ((Quotient.mk I).comp C).range
  -- ⊢ jacobson I = I
  let i : R →+* R' := ((Quotient.mk I).comp C).rangeRestrict
  -- ⊢ jacobson I = I
  have hi : Function.Surjective ↑i := ((Quotient.mk I).comp C).rangeRestrict_surjective
  -- ⊢ jacobson I = I
  have hi' : RingHom.ker (mapRingHom i) ≤ I
  -- ⊢ RingHom.ker (mapRingHom i) ≤ I
  · intro f hf
    -- ⊢ f ∈ I
    apply polynomial_mem_ideal_of_coeff_mem_ideal I f
    -- ⊢ ∀ (n : ℕ), coeff f n ∈ comap C I
    intro n
    -- ⊢ coeff f n ∈ comap C I
    replace hf := congrArg (fun g : Polynomial ((Quotient.mk I).comp C).range => g.coeff n) hf
    -- ⊢ coeff f n ∈ comap C I
    change (Polynomial.map ((Quotient.mk I).comp C).rangeRestrict f).coeff n = 0 at hf
    -- ⊢ coeff f n ∈ comap C I
    rw [coeff_map, Subtype.ext_iff] at hf
    -- ⊢ coeff f n ∈ comap C I
    rwa [mem_comap, ← Quotient.eq_zero_iff_mem, ← RingHom.comp_apply]
    -- 🎉 no goals
  have R'_jacob : IsJacobson R' := isJacobson_of_surjective ⟨i, hi⟩
  -- ⊢ jacobson I = I
  let J := map (mapRingHom i) I
  -- ⊢ jacobson I = I
  -- Porting note: moved ↓ this up a few lines, so that it can be used in the `have`
  have h_surj : Function.Surjective (mapRingHom i) := Polynomial.map_surjective i hi
  -- ⊢ jacobson I = I
  have : IsPrime J := map_isPrime_of_surjective h_surj hi'
  -- ⊢ jacobson I = I
  suffices h : J.jacobson = J
  -- ⊢ jacobson I = I
  · replace h := congrArg (comap (Polynomial.mapRingHom i)) h
    -- ⊢ jacobson I = I
    rw [← map_jacobson_of_surjective h_surj hi', comap_map_of_surjective _ h_surj,
      comap_map_of_surjective _ h_surj] at h
    refine le_antisymm ?_ le_jacobson
    -- ⊢ jacobson I ≤ I
    exact le_trans (le_sup_of_le_left le_rfl) (le_trans (le_of_eq h) (sup_le le_rfl hi'))
    -- 🎉 no goals
  apply isJacobson_polynomial_of_domain R' J
  -- ⊢ ∀ (x : { x // x ∈ R' }), ↑C x ∈ J → x = 0
  exact (eq_zero_of_polynomial_mem_map_range I)
  -- 🎉 no goals
#align ideal.polynomial.is_jacobson_polynomial_of_is_jacobson Ideal.Polynomial.isJacobson_polynomial_of_isJacobson

theorem isJacobson_polynomial_iff_isJacobson : IsJacobson R[X] ↔ IsJacobson R := by
  refine' ⟨_, isJacobson_polynomial_of_isJacobson⟩
  -- ⊢ IsJacobson R[X] → IsJacobson R
  intro H
  -- ⊢ IsJacobson R
  exact isJacobson_of_surjective ⟨eval₂RingHom (RingHom.id _) 1, fun x =>
    ⟨C x, by simp only [coe_eval₂RingHom, RingHom.id_apply, eval₂_C]⟩⟩
#align ideal.polynomial.is_jacobson_polynomial_iff_is_jacobson Ideal.Polynomial.isJacobson_polynomial_iff_isJacobson

instance [IsJacobson R] : IsJacobson R[X] :=
  isJacobson_polynomial_iff_isJacobson.mpr ‹IsJacobson R›

end CommRing

section

variable {R : Type*} [CommRing R] [IsJacobson R]

variable (P : Ideal R[X]) [hP : P.IsMaximal]

theorem isMaximal_comap_C_of_isMaximal [Nontrivial R] (hP' : ∀ x : R, C x ∈ P → x = 0) :
    IsMaximal (comap (C : R →+* R[X]) P : Ideal R) := by
  let P' := comap (C : R →+* R[X]) P
  -- ⊢ IsMaximal (comap C P)
  haveI hP'_prime : P'.IsPrime := comap_isPrime C P
  -- ⊢ IsMaximal (comap C P)
  obtain ⟨⟨m, hmem_P⟩, hm⟩ :=
    Submodule.nonzero_mem_of_bot_lt (bot_lt_of_maximal P polynomial_not_isField)
  have hm' : m ≠ 0 := by
    simpa [Submodule.coe_eq_zero] using hm
  let φ : R ⧸ P' →+* R[X] ⧸ P := quotientMap P (C : R →+* R[X]) le_rfl
  -- ⊢ IsMaximal (comap C P)
  let a : R ⧸ P' := (m.map (Quotient.mk P')).leadingCoeff
  -- ⊢ IsMaximal (comap C P)
  let M : Submonoid (R ⧸ P') := Submonoid.powers a
  -- ⊢ IsMaximal (comap C P)
  rw [← bot_quotient_isMaximal_iff]
  -- ⊢ IsMaximal ⊥
  have hp0 : a ≠ 0 := fun hp0' =>
    hm' <| map_injective (Quotient.mk (P.comap (C : R →+* R[X]) : Ideal R))
      ((injective_iff_map_eq_zero (Quotient.mk (P.comap (C : R →+* R[X]) : Ideal R))).2
        fun x hx => by
          rwa [Quotient.eq_zero_iff_mem, (by rwa [eq_bot_iff] : (P.comap C : Ideal R) = ⊥)] at hx)
        (by simpa only [leadingCoeff_eq_zero, Polynomial.map_zero] using hp0')
  have hM : (0 : R ⧸ P') ∉ M := fun ⟨n, hn⟩ => hp0 (pow_eq_zero hn)
  -- ⊢ IsMaximal ⊥
  suffices (⊥ : Ideal (Localization M)).IsMaximal by
    rw [← IsLocalization.comap_map_of_isPrime_disjoint M (Localization M) ⊥ bot_prime
      (disjoint_iff_inf_le.mpr fun x hx => hM (hx.2 ▸ hx.1))]
    refine' ((isMaximal_iff_isMaximal_disjoint (Localization M) _ _).mp (by rwa [map_bot])).1
  let M' : Submonoid (R[X] ⧸ P) := M.map φ
  -- ⊢ IsMaximal ⊥
  have hM' : (0 : R[X] ⧸ P) ∉ M' := fun ⟨z, hz⟩ =>
    hM (quotientMap_injective (_root_.trans hz.2 φ.map_zero.symm) ▸ hz.1)
  haveI : IsDomain (Localization M') :=
    IsLocalization.isDomain_localization (le_nonZeroDivisors_of_noZeroDivisors hM')
  suffices (⊥ : Ideal (Localization M')).IsMaximal by
    rw [le_antisymm bot_le (comap_bot_le_of_injective _
      (IsLocalization.map_injective_of_injective M (Localization M) (Localization M')
        quotientMap_injective))]
    refine' isMaximal_comap_of_isIntegral_of_isMaximal' _ _ ⊥ this
    have isloc : IsLocalization (Submonoid.map φ M) (Localization M') := by infer_instance
    exact @isIntegral_isLocalization_polynomial_quotient R _
      (Localization M) (Localization M') _ _ P m hmem_P _ _ _ isloc
  rw [(map_bot.symm :
    (⊥ : Ideal (Localization M')) = map (algebraMap (R[X] ⧸ P) (Localization M')) ⊥)]
  let bot_maximal := (bot_quotient_isMaximal_iff _).mpr hP
  -- ⊢ IsMaximal (map (algebraMap (R[X] ⧸ P) (Localization M')) ⊥)
  refine' map.isMaximal (algebraMap (R[X] ⧸ P) (Localization M')) _ bot_maximal
  -- ⊢ Function.Bijective ↑(algebraMap (R[X] ⧸ P) (Localization M'))
  apply IsField.localization_map_bijective hM'
  -- ⊢ IsField (R[X] ⧸ P)
  rwa [← Quotient.maximal_ideal_iff_isField_quotient, ← bot_quotient_isMaximal_iff]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align ideal.polynomial.is_maximal_comap_C_of_is_maximal Ideal.Polynomial.isMaximal_comap_C_of_isMaximal

/-- Used to bootstrap the more general `quotient_mk_comp_C_isIntegral_of_jacobson` -/
private theorem quotient_mk_comp_C_isIntegral_of_jacobson' [Nontrivial R] (hR : IsJacobson R)
    (hP' : ∀ x : R, C x ∈ P → x = 0) : ((Quotient.mk P).comp C : R →+* R[X] ⧸ P).IsIntegral := by
  refine' (isIntegral_quotientMap_iff _).mp _
  -- ⊢ RingHom.IsIntegral (quotientMap P C (_ : comap C P ≤ comap C P))
  let P' : Ideal R := P.comap C
  -- ⊢ RingHom.IsIntegral (quotientMap P C (_ : comap C P ≤ comap C P))
  obtain ⟨pX, hpX, hp0⟩ :=
    exists_nonzero_mem_of_ne_bot (ne_of_lt (bot_lt_of_maximal P polynomial_not_isField)).symm hP'
  let a : R ⧸ P' := (pX.map (Quotient.mk P')).leadingCoeff
  -- ⊢ RingHom.IsIntegral (quotientMap P C (_ : comap C P ≤ comap C P))
  let M : Submonoid (R ⧸ P') := Submonoid.powers a
  -- ⊢ RingHom.IsIntegral (quotientMap P C (_ : comap C P ≤ comap C P))
  let φ : R ⧸ P' →+* R[X] ⧸ P := quotientMap P C le_rfl
  -- ⊢ RingHom.IsIntegral (quotientMap P C (_ : comap C P ≤ comap C P))
  haveI hP'_prime : P'.IsPrime := comap_isPrime C P
  -- ⊢ RingHom.IsIntegral (quotientMap P C (_ : comap C P ≤ comap C P))
  have hM : (0 : R ⧸ P') ∉ M := fun ⟨n, hn⟩ => hp0 <| leadingCoeff_eq_zero.mp (pow_eq_zero hn)
  -- ⊢ RingHom.IsIntegral (quotientMap P C (_ : comap C P ≤ comap C P))
  let M' : Submonoid (R[X] ⧸ P) := M.map φ
  -- ⊢ RingHom.IsIntegral (quotientMap P C (_ : comap C P ≤ comap C P))
  refine' φ.isIntegral_tower_bot_of_isIntegral (algebraMap _ (Localization M')) _ _
  -- ⊢ Function.Injective ↑(algebraMap (R[X] ⧸ P) (Localization M'))
  · refine' IsLocalization.injective (Localization M')
      (show M' ≤ _ from le_nonZeroDivisors_of_noZeroDivisors fun hM' => hM _)
    exact
      let ⟨z, zM, z0⟩ := hM'
      quotientMap_injective (_root_.trans z0 φ.map_zero.symm) ▸ zM
  · suffices : RingHom.comp (algebraMap (R[X] ⧸ P) (Localization M')) φ =
      (IsLocalization.map (Localization M') φ M.le_comap_map).comp
        (algebraMap (R ⧸ P') (Localization M))
    rw [this]
    -- ⊢ RingHom.IsIntegral (RingHom.comp (IsLocalization.map (Localization M') φ (_  …
    refine' RingHom.isIntegral_trans (algebraMap (R ⧸ P') (Localization M))
      (IsLocalization.map (Localization M') φ M.le_comap_map) _ _
    · exact (algebraMap (R ⧸ P') (Localization M)).isIntegral_of_surjective
        (IsField.localization_map_bijective hM ((Quotient.maximal_ideal_iff_isField_quotient _).mp
          (isMaximal_comap_C_of_isMaximal P hP'))).2
    · -- `convert` here is faster than `exact`, and this proof is near the time limit.
      -- convert isIntegral_isLocalization_polynomial_quotient P pX hpX
      have isloc : IsLocalization M' (Localization M') := by infer_instance
      -- ⊢ RingHom.IsIntegral (IsLocalization.map (Localization M') φ (_ : M ≤ Submonoi …
      exact @isIntegral_isLocalization_polynomial_quotient R _
        (Localization M) (Localization M') _ _ P pX hpX _ _ _ isloc
    rw [IsLocalization.map_comp M.le_comap_map]
    -- 🎉 no goals

/-- If `R` is a Jacobson ring, and `P` is a maximal ideal of `R[X]`,
  then `R → R[X]/P` is an integral map. -/
theorem quotient_mk_comp_C_isIntegral_of_jacobson :
    ((Quotient.mk P).comp C : R →+* R[X] ⧸ P).IsIntegral := by
  let P' : Ideal R := P.comap C
  -- ⊢ RingHom.IsIntegral (RingHom.comp (Quotient.mk P) C)
  haveI : P'.IsPrime := comap_isPrime C P
  -- ⊢ RingHom.IsIntegral (RingHom.comp (Quotient.mk P) C)
  let f : R[X] →+* Polynomial (R ⧸ P') := Polynomial.mapRingHom (Quotient.mk P')
  -- ⊢ RingHom.IsIntegral (RingHom.comp (Quotient.mk P) C)
  have hf : Function.Surjective ↑f := map_surjective (Quotient.mk P') Quotient.mk_surjective
  -- ⊢ RingHom.IsIntegral (RingHom.comp (Quotient.mk P) C)
  have hPJ : P = (P.map f).comap f := by
    rw [comap_map_of_surjective _ hf]
    refine' le_antisymm (le_sup_of_le_left le_rfl) (sup_le le_rfl _)
    refine' fun p hp =>
      polynomial_mem_ideal_of_coeff_mem_ideal P p fun n => Quotient.eq_zero_iff_mem.mp _
    simpa only [coeff_map, coe_mapRingHom] using (Polynomial.ext_iff.mp hp) n
  refine' RingHom.isIntegral_tower_bot_of_isIntegral _ _ (injective_quotient_le_comap_map P) _
  -- ⊢ RingHom.IsIntegral (RingHom.comp (quotientMap (map (mapRingHom (Quotient.mk  …
  rw [← quotient_mk_maps_eq]
  -- ⊢ RingHom.IsIntegral (RingHom.comp (RingHom.comp (Quotient.mk (map (mapRingHom …
  refine RingHom.isIntegral_trans _ _
    ((Quotient.mk P').isIntegral_of_surjective Quotient.mk_surjective) ?_
  have : IsMaximal (map (mapRingHom (Quotient.mk (comap C P))) P)
  -- ⊢ IsMaximal (map (mapRingHom (Quotient.mk (comap C P))) P)
  · exact Or.recOn (map_eq_top_or_isMaximal_of_surjective f hf hP)
      (fun h => absurd (_root_.trans (h ▸ hPJ : P = comap f ⊤) comap_top : P = ⊤) hP.ne_top) id
  apply quotient_mk_comp_C_isIntegral_of_jacobson' _ ?_ (fun x hx => ?_)
  -- ⊢ IsJacobson (R ⧸ comap C P)
  any_goals exact Ideal.isJacobson_quotient
  -- ⊢ x = 0
  · obtain ⟨z, rfl⟩ := Quotient.mk_surjective x
    -- ⊢ ↑(Quotient.mk (comap C P)) z = 0
    rwa [Quotient.eq_zero_iff_mem, mem_comap, hPJ, mem_comap, coe_mapRingHom, map_C]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align ideal.polynomial.quotient_mk_comp_C_is_integral_of_jacobson Ideal.Polynomial.quotient_mk_comp_C_isIntegral_of_jacobson

theorem isMaximal_comap_C_of_isJacobson : (P.comap (C : R →+* R[X])).IsMaximal := by
  rw [← @mk_ker _ _ P, RingHom.ker_eq_comap_bot, comap_comap]
  -- ⊢ IsMaximal (comap (RingHom.comp (Quotient.mk P) C) ⊥)
  exact isMaximal_comap_of_isIntegral_of_isMaximal' _ (quotient_mk_comp_C_isIntegral_of_jacobson P)
    ⊥ ((bot_quotient_isMaximal_iff _).mpr hP)
set_option linter.uppercaseLean3 false in
#align ideal.polynomial.is_maximal_comap_C_of_is_jacobson Ideal.Polynomial.isMaximal_comap_C_of_isJacobson

lemma isMaximal_comap_C_of_isJacobson' {P : Ideal R[X]} (hP : IsMaximal P) :
  (P.comap (C : R →+* R[X])).IsMaximal := by
  haveI := hP
  -- ⊢ IsMaximal (comap C P)
  exact isMaximal_comap_C_of_isJacobson P
  -- 🎉 no goals

theorem comp_C_integral_of_surjective_of_jacobson {S : Type*} [Field S] (f : R[X] →+* S)
    (hf : Function.Surjective ↑f) : (f.comp C).IsIntegral := by
  haveI : f.ker.IsMaximal := RingHom.ker_isMaximal_of_surjective f hf
  -- ⊢ RingHom.IsIntegral (RingHom.comp f C)
  let g : R[X] ⧸ (RingHom.ker f) →+* S := Ideal.Quotient.lift (RingHom.ker f) f fun _ h => h
  -- ⊢ RingHom.IsIntegral (RingHom.comp f C)
  have hfg : g.comp (Quotient.mk (RingHom.ker f)) = f := ringHom_ext' rfl rfl
  -- ⊢ RingHom.IsIntegral (RingHom.comp f C)
  rw [← hfg, RingHom.comp_assoc]
  -- ⊢ RingHom.IsIntegral (RingHom.comp g (RingHom.comp (Quotient.mk (RingHom.ker f …
  refine RingHom.isIntegral_trans _ g (quotient_mk_comp_C_isIntegral_of_jacobson (RingHom.ker f))
    (g.isIntegral_of_surjective ?_)
  rw [← hfg] at hf
  -- ⊢ Function.Surjective ↑g
  norm_num at hf
  -- ⊢ Function.Surjective ↑g
  exact Function.Surjective.of_comp hf
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align ideal.polynomial.comp_C_integral_of_surjective_of_jacobson Ideal.Polynomial.comp_C_integral_of_surjective_of_jacobson

end

end Polynomial

open MvPolynomial RingHom

namespace MvPolynomial

theorem isJacobson_MvPolynomial_fin {R : Type u} [CommRing R] [H : IsJacobson R] :
    ∀ n : ℕ, IsJacobson (MvPolynomial (Fin n) R)
  | 0 => (isJacobson_iso ((renameEquiv R (Equiv.equivPEmpty (Fin 0))).toRingEquiv.trans
    (isEmptyRingEquiv R PEmpty.{u+1}))).mpr H
  | n + 1 => (isJacobson_iso (finSuccEquiv R n).toRingEquiv).2
    (Polynomial.isJacobson_polynomial_iff_isJacobson.2 (isJacobson_MvPolynomial_fin n))
#align ideal.mv_polynomial.is_jacobson_mv_polynomial_fin Ideal.MvPolynomial.isJacobson_MvPolynomial_fin

/-- General form of the Nullstellensatz for Jacobson rings, since in a Jacobson ring we have
  `Inf {P maximal | P ≥ I} = Inf {P prime | P ≥ I} = I.radical`. Fields are always Jacobson,
  and in that special case this is (most of) the classical Nullstellensatz,
  since `I(V(I))` is the intersection of maximal ideals containing `I`, which is then `I.radical` -/
instance isJacobson {R : Type*} [CommRing R] {ι : Type*} [Finite ι] [IsJacobson R] :
    IsJacobson (MvPolynomial ι R) := by
  cases nonempty_fintype ι
  -- ⊢ IsJacobson (MvPolynomial ι R)
  haveI := Classical.decEq ι
  -- ⊢ IsJacobson (MvPolynomial ι R)
  let e := Fintype.equivFin ι
  -- ⊢ IsJacobson (MvPolynomial ι R)
  rw [isJacobson_iso (renameEquiv R e).toRingEquiv]
  -- ⊢ IsJacobson (MvPolynomial (Fin (Fintype.card ι)) R)
  exact isJacobson_MvPolynomial_fin _
  -- 🎉 no goals
#align ideal.mv_polynomial.is_jacobson Ideal.MvPolynomial.isJacobson

variable {n : ℕ}

-- Porting note: split out `aux_IH` and `quotient_mk_comp_C_isIntegral_of_jacobson'`
-- from the long proof of `Ideal.MvPolynomial.quotient_mk_comp_C_isIntegral_of_jacobson`

/-- The constant coefficient as an R-linear morphism -/
private noncomputable def Cₐ (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] : S →ₐ[R] S[X] :=
  { Polynomial.C with commutes' := fun r => by rfl }
                                               -- 🎉 no goals

private lemma aux_IH {R : Type u} {S : Type v} {T : Type w}
  [CommRing R] [CommRing S] [CommRing T] [IsJacobson S] [Algebra R S] [Algebra R T]
  (IH : ∀ (Q : Ideal S), (IsMaximal Q) → RingHom.IsIntegral (algebraMap R (S ⧸ Q)))
  (v : S[X] ≃ₐ[R] T) (P : Ideal T) (hP : P.IsMaximal) :
  RingHom.IsIntegral (algebraMap R (T ⧸ P)) := by
  let Q := P.comap v.toAlgHom.toRingHom
  -- ⊢ RingHom.IsIntegral (algebraMap R (T ⧸ P))
  have hw : Ideal.map v Q = P := map_comap_of_surjective v v.surjective P
  -- ⊢ RingHom.IsIntegral (algebraMap R (T ⧸ P))
  haveI hQ : IsMaximal Q := comap_isMaximal_of_surjective _ v.surjective
  -- ⊢ RingHom.IsIntegral (algebraMap R (T ⧸ P))
  let w : (S[X] ⧸ Q) ≃ₐ[R] (T ⧸ P) := Ideal.quotientEquivAlg Q P v hw.symm
  -- ⊢ RingHom.IsIntegral (algebraMap R (T ⧸ P))
  let Q' := Q.comap (Polynomial.C)
  -- ⊢ RingHom.IsIntegral (algebraMap R (T ⧸ P))
  let w' : (S ⧸ Q') →ₐ[R] (S[X] ⧸ Q) := Ideal.quotientMapₐ Q (Cₐ R S) le_rfl
  -- ⊢ RingHom.IsIntegral (algebraMap R (T ⧸ P))
  have h_eq : algebraMap R (T ⧸ P) =
    w.toRingEquiv.toRingHom.comp (w'.toRingHom.comp (algebraMap R (S ⧸ Q'))) := by
    ext r
    simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe, AlgEquiv.toRingEquiv_eq_coe,
      RingEquiv.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower, coe_comp, coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes]
  rw [h_eq]
  -- ⊢ RingHom.IsIntegral (RingHom.comp (RingEquiv.toRingHom (AlgEquiv.toRingEquiv  …
  apply RingHom.isIntegral_trans
  -- ⊢ RingHom.IsIntegral (RingHom.comp (↑w') (algebraMap R (S ⧸ Q')))
  apply RingHom.isIntegral_trans
  · apply IH
    -- ⊢ IsMaximal Q'
    apply Polynomial.isMaximal_comap_C_of_isJacobson'
    -- ⊢ IsMaximal Q
    exact hQ
    -- 🎉 no goals
  · suffices : w'.toRingHom = Ideal.quotientMap Q (Polynomial.C) le_rfl
    -- ⊢ RingHom.IsIntegral ↑w'
    · rw [this]
      -- ⊢ RingHom.IsIntegral (quotientMap Q Polynomial.C (_ : comap Polynomial.C Q ≤ c …
      rw [isIntegral_quotientMap_iff _]
      -- ⊢ RingHom.IsIntegral (RingHom.comp (Quotient.mk Q) Polynomial.C)
      apply Polynomial.quotient_mk_comp_C_isIntegral_of_jacobson
      -- 🎉 no goals
    · rfl
      -- 🎉 no goals
  · apply RingHom.isIntegral_of_surjective
    -- ⊢ Function.Surjective ↑(RingEquiv.toRingHom (AlgEquiv.toRingEquiv w))
    exact w.surjective
    -- 🎉 no goals

private theorem quotient_mk_comp_C_isIntegral_of_jacobson' {R : Type*} [CommRing R] [IsJacobson R]
    (P : Ideal (MvPolynomial (Fin n) R)) (hP : P.IsMaximal) :
    RingHom.IsIntegral (algebraMap R (MvPolynomial (Fin n) R ⧸ P)) := by
  induction' n with n IH
  -- ⊢ RingHom.IsIntegral (algebraMap R (MvPolynomial (Fin Nat.zero) R ⧸ P))
  · apply RingHom.isIntegral_of_surjective
    -- ⊢ Function.Surjective ↑(algebraMap R (MvPolynomial (Fin Nat.zero) R ⧸ P))
    apply Function.Surjective.comp Quotient.mk_surjective
    -- ⊢ Function.Surjective fun x => ↑(algebraMap R (MvPolynomial (Fin Nat.zero) R)) x
    exact C_surjective (Fin 0)
    -- 🎉 no goals
  · apply aux_IH IH (finSuccEquiv R n).symm P hP
    -- 🎉 no goals

theorem quotient_mk_comp_C_isIntegral_of_jacobson {R : Type*} [CommRing R] [IsJacobson R]
    (P : Ideal (MvPolynomial (Fin n) R)) [hP : P.IsMaximal] :
    RingHom.IsIntegral (RingHom.comp (Quotient.mk P) (MvPolynomial.C)) := by
  change RingHom.IsIntegral (algebraMap R (MvPolynomial (Fin n) R ⧸ P))
  -- ⊢ RingHom.IsIntegral (algebraMap R (MvPolynomial (Fin n) R ⧸ P))
  apply quotient_mk_comp_C_isIntegral_of_jacobson'
  -- ⊢ IsMaximal P
  infer_instance
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align ideal.mv_polynomial.quotient_mk_comp_C_isIntegral_of_jacobson Ideal.MvPolynomial.quotient_mk_comp_C_isIntegral_of_jacobson

theorem comp_C_integral_of_surjective_of_jacobson {R : Type*} [CommRing R] [IsJacobson R]
    {σ : Type*} [Finite σ] {S : Type*} [Field S] (f : MvPolynomial σ R →+* S)
    (hf : Function.Surjective ↑f) : (f.comp C).IsIntegral := by
  cases nonempty_fintype σ
  -- ⊢ RingHom.IsIntegral (RingHom.comp f MvPolynomial.C)
  have e := (Fintype.equivFin σ).symm
  -- ⊢ RingHom.IsIntegral (RingHom.comp f MvPolynomial.C)
  let f' : MvPolynomial (Fin _) R →+* S := f.comp (renameEquiv R e).toRingEquiv.toRingHom
  -- ⊢ RingHom.IsIntegral (RingHom.comp f MvPolynomial.C)
  have hf' := Function.Surjective.comp hf (renameEquiv R e).surjective
  -- ⊢ RingHom.IsIntegral (RingHom.comp f MvPolynomial.C)
  change Function.Surjective ↑f' at hf'
  -- ⊢ RingHom.IsIntegral (RingHom.comp f MvPolynomial.C)
  have : (f'.comp C).IsIntegral := by
    haveI : f'.ker.IsMaximal := ker_isMaximal_of_surjective f' hf'
    let g : MvPolynomial _ R ⧸ (RingHom.ker f') →+* S :=
      Ideal.Quotient.lift (RingHom.ker f') f' fun _ h => h
    have hfg : g.comp (Quotient.mk (RingHom.ker f')) = f' := ringHom_ext (fun r => rfl) fun i => rfl
    rw [← hfg, RingHom.comp_assoc]
    refine' RingHom.isIntegral_trans _ g (quotient_mk_comp_C_isIntegral_of_jacobson
      (RingHom.ker f')) (g.isIntegral_of_surjective _)
    rw [← hfg] at hf'
    norm_num at hf'
    exact Function.Surjective.of_comp hf'
  rw [RingHom.comp_assoc] at this
  -- ⊢ RingHom.IsIntegral (RingHom.comp f MvPolynomial.C)
  convert this
  -- ⊢ MvPolynomial.C = RingHom.comp (RingEquiv.toRingHom (AlgEquiv.toRingEquiv (re …
  refine' RingHom.ext fun x => _
  -- ⊢ ↑MvPolynomial.C x = ↑(RingHom.comp (RingEquiv.toRingHom (AlgEquiv.toRingEqui …
  exact ((renameEquiv R e).commutes' x).symm
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align ideal.mv_polynomial.comp_C_integral_of_surjective_of_jacobson Ideal.MvPolynomial.comp_C_integral_of_surjective_of_jacobson

end MvPolynomial

end Ideal
