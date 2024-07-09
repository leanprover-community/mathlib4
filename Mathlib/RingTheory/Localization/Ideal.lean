/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.RingTheory.Localization.Basic

#align_import ring_theory.localization.ideal from "leanprover-community/mathlib"@"e7f0ddbf65bd7181a85edb74b64bdc35ba4bdc74"

/-!
# Ideals in localizations of commutative rings
## Implementation notes
See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.
## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


namespace IsLocalization

section CommSemiring

variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S]
variable [Algebra R S] [IsLocalization M S]

/-- Explicit characterization of the ideal given by `Ideal.map (algebraMap R S) I`.
In practice, this ideal differs only in that the carrier set is defined explicitly.
This definition is only meant to be used in proving `mem_map_algebraMap_iff`,
and any proof that needs to refer to the explicit carrier set should use that theorem. -/
private def map_ideal (I : Ideal R) : Ideal S where
  carrier := { z : S | ∃ x : I × M, z * algebraMap R S x.2 = algebraMap R S x.1 }
  zero_mem' := ⟨⟨0, 1⟩, by simp⟩
  add_mem' := by
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩
    let Z : { x // x ∈ I } := ⟨(a'.2 : R) * (b'.1 : R) + (b'.2 : R) * (a'.1 : R),
      I.add_mem (I.mul_mem_left _ b'.1.2) (I.mul_mem_left _ a'.1.2)⟩
    use ⟨Z, a'.2 * b'.2⟩
    simp only [RingHom.map_add, Submodule.coe_mk, Submonoid.coe_mul, RingHom.map_mul]
    rw [add_mul, ← mul_assoc a, ha, mul_comm (algebraMap R S a'.2) (algebraMap R S b'.2), ←
      mul_assoc b, hb]
    ring
  smul_mem' := by
    rintro c x ⟨x', hx⟩
    obtain ⟨c', hc⟩ := IsLocalization.surj M c
    let Z : { x // x ∈ I } := ⟨c'.1 * x'.1, I.mul_mem_left c'.1 x'.1.2⟩
    use ⟨Z, c'.2 * x'.2⟩
    simp only [← hx, ← hc, smul_eq_mul, Submodule.coe_mk, Submonoid.coe_mul, RingHom.map_mul]
    ring
-- Porting note: removed #align declaration since it is a private def

theorem mem_map_algebraMap_iff {I : Ideal R} {z} : z ∈ Ideal.map (algebraMap R S) I ↔
    ∃ x : I × M, z * algebraMap R S x.2 = algebraMap R S x.1 := by
  constructor
  · change _ → z ∈ map_ideal M S I
    refine fun h => Ideal.mem_sInf.1 h fun z hz => ?_
    obtain ⟨y, hy⟩ := hz
    let Z : { x // x ∈ I } := ⟨y, hy.left⟩
    use ⟨Z, 1⟩
    simp [hy.right]
  · rintro ⟨⟨a, s⟩, h⟩
    rw [← Ideal.unit_mul_mem_iff_mem _ (map_units S s), mul_comm]
    exact h.symm ▸ Ideal.mem_map_of_mem _ a.2
#align is_localization.mem_map_algebra_map_iff IsLocalization.mem_map_algebraMap_iff

theorem map_comap (J : Ideal S) : Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) J) = J :=
  le_antisymm (Ideal.map_le_iff_le_comap.2 le_rfl) fun x hJ => by
    obtain ⟨r, s, hx⟩ := mk'_surjective M x
    rw [← hx] at hJ ⊢
    exact
      Ideal.mul_mem_right _ _
        (Ideal.mem_map_of_mem _
          (show (algebraMap R S) r ∈ J from
            mk'_spec S r s ▸ J.mul_mem_right ((algebraMap R S) s) hJ))
#align is_localization.map_comap IsLocalization.map_comap

theorem comap_map_of_isPrime_disjoint (I : Ideal R) (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) :
    Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) I) = I := by
  refine le_antisymm ?_ Ideal.le_comap_map
  refine (fun a ha => ?_)
  obtain ⟨⟨b, s⟩, h⟩ := (mem_map_algebraMap_iff M S).1 (Ideal.mem_comap.1 ha)
  replace h : algebraMap R S (s * a) = algebraMap R S b := by
    simpa only [← map_mul, mul_comm] using h
  obtain ⟨c, hc⟩ := (eq_iff_exists M S).1 h
  have : ↑c * ↑s * a ∈ I := by
    rw [mul_assoc, hc]
    exact I.mul_mem_left c b.2
  exact (hI.mem_or_mem this).resolve_left fun hsc => hM.le_bot ⟨(c * s).2, hsc⟩
#align is_localization.comap_map_of_is_prime_disjoint IsLocalization.comap_map_of_isPrime_disjoint

/-- If `S` is the localization of `R` at a submonoid, the ordering of ideals of `S` is
embedded in the ordering of ideals of `R`. -/
def orderEmbedding : Ideal S ↪o Ideal R where
  toFun J := Ideal.comap (algebraMap R S) J
  inj' := Function.LeftInverse.injective (map_comap M S)
  map_rel_iff' := by
    rintro J₁ J₂
    constructor
    · exact fun hJ => (map_comap M S) J₁ ▸ (map_comap M S) J₂ ▸ Ideal.map_mono hJ
    · exact fun hJ => Ideal.comap_mono hJ
#align is_localization.order_embedding IsLocalization.orderEmbedding

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its comap,
see `le_rel_iso_of_prime` for the more general relation isomorphism -/
theorem isPrime_iff_isPrime_disjoint (J : Ideal S) :
    J.IsPrime ↔
      (Ideal.comap (algebraMap R S) J).IsPrime ∧
        Disjoint (M : Set R) ↑(Ideal.comap (algebraMap R S) J) := by
  constructor
  · refine fun h =>
      ⟨⟨?_, ?_⟩,
        Set.disjoint_left.mpr fun m hm1 hm2 =>
          h.ne_top (Ideal.eq_top_of_isUnit_mem _ hm2 (map_units S ⟨m, hm1⟩))⟩
    · refine fun hJ => h.ne_top ?_
      rw [eq_top_iff, ← (orderEmbedding M S).le_iff_le]
      exact le_of_eq hJ.symm
    · intro x y hxy
      rw [Ideal.mem_comap, RingHom.map_mul] at hxy
      exact h.mem_or_mem hxy
  · refine fun h => ⟨fun hJ => h.left.ne_top (eq_top_iff.2 ?_), ?_⟩
    · rwa [eq_top_iff, ← (orderEmbedding M S).le_iff_le] at hJ
    · intro x y hxy
      obtain ⟨a, s, ha⟩ := mk'_surjective M x
      obtain ⟨b, t, hb⟩ := mk'_surjective M y
      have : mk' S (a * b) (s * t) ∈ J := by rwa [mk'_mul, ha, hb]
      rw [mk'_mem_iff, ← Ideal.mem_comap] at this
      have this₂ := (h.1).mul_mem_iff_mem_or_mem.1 this
      rw [Ideal.mem_comap, Ideal.mem_comap] at this₂
      rwa [← ha, ← hb, mk'_mem_iff, mk'_mem_iff]
#align is_localization.is_prime_iff_is_prime_disjoint IsLocalization.isPrime_iff_isPrime_disjoint

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its map,
see `le_rel_iso_of_prime` for the more general relation isomorphism, and the reverse implication -/
theorem isPrime_of_isPrime_disjoint (I : Ideal R) (hp : I.IsPrime) (hd : Disjoint (M : Set R) ↑I) :
    (Ideal.map (algebraMap R S) I).IsPrime := by
  rw [isPrime_iff_isPrime_disjoint M S, comap_map_of_isPrime_disjoint M S I hp hd]
  exact ⟨hp, hd⟩
#align is_localization.is_prime_of_is_prime_disjoint IsLocalization.isPrime_of_isPrime_disjoint

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M` -/
def orderIsoOfPrime :
    { p : Ideal S // p.IsPrime } ≃o { p : Ideal R // p.IsPrime ∧ Disjoint (M : Set R) ↑p } where
  toFun p := ⟨Ideal.comap (algebraMap R S) p.1, (isPrime_iff_isPrime_disjoint M S p.1).1 p.2⟩
  invFun p := ⟨Ideal.map (algebraMap R S) p.1, isPrime_of_isPrime_disjoint M S p.1 p.2.1 p.2.2⟩
  left_inv J := Subtype.eq (map_comap M S J)
  right_inv I := Subtype.eq (comap_map_of_isPrime_disjoint M S I.1 I.2.1 I.2.2)
  map_rel_iff' := by
    rintro I I'
    constructor
    · exact (fun h => show I.val ≤ I'.val from map_comap M S I.val ▸
        map_comap M S I'.val ▸ Ideal.map_mono h)
    exact fun h x hx => h hx
#align is_localization.order_iso_of_prime IsLocalization.orderIsoOfPrime

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] (M : Submonoid R) (S : Type*) [CommRing S]
variable [Algebra R S] [IsLocalization M S]

/-- `quotientMap` applied to maximal ideals of a localization is `surjective`.
  The quotient by a maximal ideal is a field, so inverses to elements already exist,
  and the localization necessarily maps the equivalence class of the inverse in the localization -/
theorem surjective_quotientMap_of_maximal_of_localization {I : Ideal S} [I.IsPrime] {J : Ideal R}
    {H : J ≤ I.comap (algebraMap R S)} (hI : (I.comap (algebraMap R S)).IsMaximal) :
    Function.Surjective (Ideal.quotientMap I (algebraMap R S) H) := by
  intro s
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := mk'_surjective M s
  by_cases hM : (Ideal.Quotient.mk (I.comap (algebraMap R S))) m = 0
  · have : I = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap] at hM
      convert I.mul_mem_right (mk' S (1 : R) ⟨m, hm⟩) hM
      rw [← mk'_eq_mul_mk'_one, mk'_self]
    exact ⟨0, eq_comm.1 (by simp [Ideal.Quotient.eq_zero_iff_mem, this])⟩
  · rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient] at hI
    obtain ⟨n, hn⟩ := hI.3 hM
    obtain ⟨rn, rfl⟩ := Ideal.Quotient.mk_surjective n
    refine ⟨(Ideal.Quotient.mk J) (r * rn), ?_⟩
    -- The rest of the proof is essentially just algebraic manipulations to prove the equality
    replace hn := congr_arg (Ideal.quotientMap I (algebraMap R S) le_rfl) hn
    rw [RingHom.map_one, RingHom.map_mul] at hn
    rw [Ideal.quotientMap_mk, ← sub_eq_zero, ← RingHom.map_sub, Ideal.Quotient.eq_zero_iff_mem, ←
      Ideal.Quotient.eq_zero_iff_mem, RingHom.map_sub, sub_eq_zero, mk'_eq_mul_mk'_one]
    simp only [mul_eq_mul_left_iff, RingHom.map_mul]
    refine
      Or.inl
        (mul_left_cancel₀ (M₀ := S ⧸ I)
          (fun hn =>
            hM
              (Ideal.Quotient.eq_zero_iff_mem.2
                (Ideal.mem_comap.2 (Ideal.Quotient.eq_zero_iff_mem.1 hn))))
          (_root_.trans hn ?_))
    -- Porting note (#10691): was `rw`, but this took extremely long.
    refine Eq.trans ?_ (RingHom.map_mul (Ideal.Quotient.mk I) (algebraMap R S m) (mk' S 1 ⟨m, hm⟩))
    rw [← mk'_eq_mul_mk'_one, mk'_self, RingHom.map_one]
#align is_localization.surjective_quotient_map_of_maximal_of_localization IsLocalization.surjective_quotientMap_of_maximal_of_localization

open nonZeroDivisors

theorem bot_lt_comap_prime [IsDomain R] (hM : M ≤ R⁰) (p : Ideal S) [hpp : p.IsPrime]
    (hp0 : p ≠ ⊥) : ⊥ < Ideal.comap (algebraMap R S) p := by
  haveI : IsDomain S := isDomain_of_le_nonZeroDivisors _ hM
  rw [← Ideal.comap_bot_of_injective (algebraMap R S) (IsLocalization.injective _ hM)]
  convert (orderIsoOfPrime M S).lt_iff_lt.mpr (show (⟨⊥, Ideal.bot_prime⟩ :
    { p : Ideal S // p.IsPrime }) < ⟨p, hpp⟩ from hp0.bot_lt)
#align is_localization.bot_lt_comap_prime IsLocalization.bot_lt_comap_prime

end CommRing

end IsLocalization
