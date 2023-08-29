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
                           -- 🎉 no goals
  add_mem' := by
    -- ⊢ a + b ∈ {z | ∃ x, z * ↑(algebraMap R S) ↑x.snd = ↑(algebraMap R S) ↑x.fst}
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩
    let Z : { x // x ∈ I } := ⟨(a'.2 : R) * (b'.1 : R) + (b'.2 : R) * (a'.1 : R),
      I.add_mem (I.mul_mem_left _ b'.1.2) (I.mul_mem_left _ a'.1.2)⟩
    -- ⊢ (a + b) * ↑(algebraMap R S) ↑(Z, a'.snd * b'.snd).snd = ↑(algebraMap R S) ↑( …
    use ⟨Z, a'.2 * b'.2⟩
    -- ⊢ (a + b) * (↑(algebraMap R S) ↑a'.snd * ↑(algebraMap R S) ↑b'.snd) = ↑(algebr …
    simp only [RingHom.map_add, Submodule.coe_mk, Submonoid.coe_mul, RingHom.map_mul]
    rw [add_mul, ← mul_assoc a, ha, mul_comm (algebraMap R S a'.2) (algebraMap R S b'.2), ←
      mul_assoc b, hb]
    -- 🎉 no goals
    ring
  smul_mem' := by
    rintro c x ⟨x', hx⟩
    -- ⊢ c • x ∈ { toAddSubsemigroup := { carrier := {z | ∃ x, z * ↑(algebraMap R S)  …
    obtain ⟨c', hc⟩ := IsLocalization.surj M c
    -- ⊢ c • x ∈ { toAddSubsemigroup := { carrier := {z | ∃ x, z * ↑(algebraMap R S)  …
    let Z : { x // x ∈ I } := ⟨c'.1 * x'.1, I.mul_mem_left c'.1 x'.1.2⟩
    -- ⊢ c • x ∈ { toAddSubsemigroup := { carrier := {z | ∃ x, z * ↑(algebraMap R S)  …
    use ⟨Z, c'.2 * x'.2⟩
    -- ⊢ c • x * ↑(algebraMap R S) ↑(Z, c'.snd * x'.snd).snd = ↑(algebraMap R S) ↑(Z, …
    simp only [← hx, ← hc, smul_eq_mul, Submodule.coe_mk, Submonoid.coe_mul, RingHom.map_mul]
    -- ⊢ c * x * (↑(algebraMap R S) ↑c'.snd * ↑(algebraMap R S) ↑x'.snd) = c * ↑(alge …
    ring
    -- 🎉 no goals
-- Porting note: removed #align declaration since it is a private def

theorem mem_map_algebraMap_iff {I : Ideal R} {z} : z ∈ Ideal.map (algebraMap R S) I ↔
    ∃ x : I × M, z * algebraMap R S x.2 = algebraMap R S x.1 := by
  constructor
  -- ⊢ z ∈ Ideal.map (algebraMap R S) I → ∃ x, z * ↑(algebraMap R S) ↑x.snd = ↑(alg …
  · change _ → z ∈ map_ideal M S I
    -- ⊢ z ∈ Ideal.map (algebraMap R S) I → z ∈ IsLocalization.map_ideal M S I
    refine' fun h => Ideal.mem_sInf.1 h fun z hz => _
    -- ⊢ z ∈ ↑(IsLocalization.map_ideal M S I)
    obtain ⟨y, hy⟩ := hz
    -- ⊢ z ∈ ↑(IsLocalization.map_ideal M S I)
    let Z : { x // x ∈ I } := ⟨y, hy.left⟩
    -- ⊢ z ∈ ↑(IsLocalization.map_ideal M S I)
    use ⟨Z, 1⟩
    -- ⊢ z * ↑(algebraMap R S) ↑(Z, 1).snd = ↑(algebraMap R S) ↑(Z, 1).fst
    simp [hy.right]
    -- 🎉 no goals
  · rintro ⟨⟨a, s⟩, h⟩
    -- ⊢ z ∈ Ideal.map (algebraMap R S) I
    rw [← Ideal.unit_mul_mem_iff_mem _ (map_units S s), mul_comm]
    -- ⊢ z * ↑(algebraMap R S) ↑s ∈ Ideal.map (algebraMap R S) I
    exact h.symm ▸ Ideal.mem_map_of_mem _ a.2
    -- 🎉 no goals
#align is_localization.mem_map_algebra_map_iff IsLocalization.mem_map_algebraMap_iff

theorem map_comap (J : Ideal S) : Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) J) = J :=
  le_antisymm (Ideal.map_le_iff_le_comap.2 le_rfl) fun x hJ => by
    obtain ⟨r, s, hx⟩ := mk'_surjective M x
    -- ⊢ x ∈ Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) J)
    rw [← hx] at hJ ⊢
    -- ⊢ mk' S r s ∈ Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) J)
    exact
      Ideal.mul_mem_right _ _
        (Ideal.mem_map_of_mem _
          (show (algebraMap R S) r ∈ J from
            mk'_spec S r s ▸ J.mul_mem_right ((algebraMap R S) s) hJ))
#align is_localization.map_comap IsLocalization.map_comap

theorem comap_map_of_isPrime_disjoint (I : Ideal R) (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) :
    Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) I) = I := by
  refine' le_antisymm _ Ideal.le_comap_map
  -- ⊢ Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) I) ≤ I
  refine' (fun a ha => _)
  -- ⊢ a ∈ I
  obtain ⟨⟨b, s⟩, h⟩ := (mem_map_algebraMap_iff M S).1 (Ideal.mem_comap.1 ha)
  -- ⊢ a ∈ I
  replace h : algebraMap R S (s * a) = algebraMap R S b := by
    simpa only [← map_mul, mul_comm] using h
  obtain ⟨c, hc⟩ := (eq_iff_exists M S).1 h
  -- ⊢ a ∈ I
  have : ↑c * ↑s * a ∈ I := by
    rw [mul_assoc, hc]
    exact I.mul_mem_left c b.2
  exact (hI.mem_or_mem this).resolve_left fun hsc => hM.le_bot ⟨(c * s).2, hsc⟩
  -- 🎉 no goals
#align is_localization.comap_map_of_is_prime_disjoint IsLocalization.comap_map_of_isPrime_disjoint

/-- If `S` is the localization of `R` at a submonoid, the ordering of ideals of `S` is
embedded in the ordering of ideals of `R`. -/
def orderEmbedding : Ideal S ↪o Ideal R where
  toFun J := Ideal.comap (algebraMap R S) J
  inj' := Function.LeftInverse.injective (map_comap M S)
  map_rel_iff' := by
    rintro J₁ J₂
    -- ⊢ ↑{ toFun := fun J => Ideal.comap (algebraMap R S) J, inj' := (_ : Function.I …
    constructor
    -- ⊢ ↑{ toFun := fun J => Ideal.comap (algebraMap R S) J, inj' := (_ : Function.I …
    exact (fun hJ => (map_comap M S) J₁ ▸ (map_comap M S) J₂ ▸ Ideal.map_mono hJ)
    -- ⊢ J₁ ≤ J₂ → ↑{ toFun := fun J => Ideal.comap (algebraMap R S) J, inj' := (_ :  …
    exact (fun hJ => Ideal.comap_mono hJ)
    -- 🎉 no goals
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
  -- ⊢ Ideal.IsPrime J → Ideal.IsPrime (Ideal.comap (algebraMap R S) J) ∧ Disjoint  …
  · refine' fun h =>
      ⟨⟨_, _⟩,
        Set.disjoint_left.mpr fun m hm1 hm2 =>
          h.ne_top (Ideal.eq_top_of_isUnit_mem _ hm2 (map_units S ⟨m, hm1⟩))⟩
    · refine' fun hJ => h.ne_top _
      -- ⊢ J = ⊤
      rw [eq_top_iff, ← (orderEmbedding M S).le_iff_le]
      -- ⊢ ↑(orderEmbedding M S) ⊤ ≤ ↑(orderEmbedding M S) J
      exact le_of_eq hJ.symm
      -- 🎉 no goals
    · intro x y hxy
      -- ⊢ x ∈ Ideal.comap (algebraMap R S) J ∨ y ∈ Ideal.comap (algebraMap R S) J
      rw [Ideal.mem_comap, RingHom.map_mul] at hxy
      -- ⊢ x ∈ Ideal.comap (algebraMap R S) J ∨ y ∈ Ideal.comap (algebraMap R S) J
      exact h.mem_or_mem hxy
      -- 🎉 no goals
  · refine' fun h => ⟨fun hJ => h.left.ne_top (eq_top_iff.2 _), _⟩
    -- ⊢ ⊤ ≤ Ideal.comap (algebraMap R S) J
    · rwa [eq_top_iff, ← (orderEmbedding M S).le_iff_le] at hJ
      -- 🎉 no goals
    · intro x y hxy
      -- ⊢ x ∈ J ∨ y ∈ J
      obtain ⟨a, s, ha⟩ := mk'_surjective M x
      -- ⊢ x ∈ J ∨ y ∈ J
      obtain ⟨b, t, hb⟩ := mk'_surjective M y
      -- ⊢ x ∈ J ∨ y ∈ J
      have : mk' S (a * b) (s * t) ∈ J := by rwa [mk'_mul, ha, hb]
      -- ⊢ x ∈ J ∨ y ∈ J
      rw [mk'_mem_iff, ← Ideal.mem_comap] at this
      -- ⊢ x ∈ J ∨ y ∈ J
      have this₂ := (h.1).mul_mem_iff_mem_or_mem.1 this
      -- ⊢ x ∈ J ∨ y ∈ J
      rw [Ideal.mem_comap, Ideal.mem_comap] at this₂
      -- ⊢ x ∈ J ∨ y ∈ J
      rwa [← ha, ← hb, mk'_mem_iff, mk'_mem_iff]
      -- 🎉 no goals
#align is_localization.is_prime_iff_is_prime_disjoint IsLocalization.isPrime_iff_isPrime_disjoint

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its map,
see `le_rel_iso_of_prime` for the more general relation isomorphism, and the reverse implication -/
theorem isPrime_of_isPrime_disjoint (I : Ideal R) (hp : I.IsPrime) (hd : Disjoint (M : Set R) ↑I) :
    (Ideal.map (algebraMap R S) I).IsPrime := by
  rw [isPrime_iff_isPrime_disjoint M S, comap_map_of_isPrime_disjoint M S I hp hd]
  -- ⊢ Ideal.IsPrime I ∧ Disjoint ↑M ↑I
  exact ⟨hp, hd⟩
  -- 🎉 no goals
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
    -- ⊢ ↑{ toFun := fun p => { val := Ideal.comap (algebraMap R S) ↑p, property := ( …
    constructor
    -- ⊢ ↑{ toFun := fun p => { val := Ideal.comap (algebraMap R S) ↑p, property := ( …
    exact (fun h => show I.val ≤ I'.val from map_comap M S I.val ▸
      map_comap M S I'.val ▸ Ideal.map_mono h)
    exact (fun h x hx => h hx)
    -- 🎉 no goals
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
  -- ⊢ ∃ a, ↑(Ideal.quotientMap I (algebraMap R S) H) a = s
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  -- ⊢ ∃ a, ↑(Ideal.quotientMap I (algebraMap R S) H) a = ↑(Ideal.Quotient.mk I) s
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := mk'_surjective M s
  -- ⊢ ∃ a, ↑(Ideal.quotientMap I (algebraMap R S) H) a = ↑(Ideal.Quotient.mk I) (m …
  by_cases hM : (Ideal.Quotient.mk (I.comap (algebraMap R S))) m = 0
  -- ⊢ ∃ a, ↑(Ideal.quotientMap I (algebraMap R S) H) a = ↑(Ideal.Quotient.mk I) (m …
  · have : I = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap] at hM
      convert I.mul_mem_right (mk' S (1 : R) ⟨m, hm⟩) hM
      rw [← mk'_eq_mul_mk'_one, mk'_self]
    exact ⟨0, eq_comm.1 (by simp [Ideal.Quotient.eq_zero_iff_mem, this])⟩
    -- 🎉 no goals
  · rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient] at hI
    -- ⊢ ∃ a, ↑(Ideal.quotientMap I (algebraMap R S) H) a = ↑(Ideal.Quotient.mk I) (m …
    obtain ⟨n, hn⟩ := hI.3 hM
    -- ⊢ ∃ a, ↑(Ideal.quotientMap I (algebraMap R S) H) a = ↑(Ideal.Quotient.mk I) (m …
    obtain ⟨rn, rfl⟩ := Ideal.Quotient.mk_surjective n
    -- ⊢ ∃ a, ↑(Ideal.quotientMap I (algebraMap R S) H) a = ↑(Ideal.Quotient.mk I) (m …
    refine' ⟨(Ideal.Quotient.mk J) (r * rn), _⟩
    -- ⊢ ↑(Ideal.quotientMap I (algebraMap R S) H) (↑(Ideal.Quotient.mk J) (r * rn))  …
    -- The rest of the proof is essentially just algebraic manipulations to prove the equality
    replace hn := congr_arg (Ideal.quotientMap I (algebraMap R S) le_rfl) hn
    -- ⊢ ↑(Ideal.quotientMap I (algebraMap R S) H) (↑(Ideal.Quotient.mk J) (r * rn))  …
    rw [RingHom.map_one, RingHom.map_mul] at hn
    -- ⊢ ↑(Ideal.quotientMap I (algebraMap R S) H) (↑(Ideal.Quotient.mk J) (r * rn))  …
    rw [Ideal.quotientMap_mk, ← sub_eq_zero, ← RingHom.map_sub, Ideal.Quotient.eq_zero_iff_mem, ←
      Ideal.Quotient.eq_zero_iff_mem, RingHom.map_sub, sub_eq_zero, mk'_eq_mul_mk'_one]
    simp only [mul_eq_mul_left_iff, RingHom.map_mul]
    -- ⊢ ↑(Ideal.Quotient.mk I) (↑(algebraMap R S) rn) = ↑(Ideal.Quotient.mk I) (mk'  …
    refine
      Or.inl
        (mul_left_cancel₀ (M₀ := S ⧸ I)
          (fun hn =>
            hM
              (Ideal.Quotient.eq_zero_iff_mem.2
                (Ideal.mem_comap.2 (Ideal.Quotient.eq_zero_iff_mem.1 hn))))
          (_root_.trans hn ?_))
    -- Porting note: was `rw`, but this took extremely long.
    refine Eq.trans ?_ (RingHom.map_mul (Ideal.Quotient.mk I) (algebraMap R S m) (mk' S 1 ⟨m, hm⟩))
    -- ⊢ 1 = ↑(Ideal.Quotient.mk I) (↑(algebraMap R S) m * mk' S 1 { val := m, proper …
    rw [← mk'_eq_mul_mk'_one, mk'_self, RingHom.map_one]
    -- 🎉 no goals
#align is_localization.surjective_quotient_map_of_maximal_of_localization IsLocalization.surjective_quotientMap_of_maximal_of_localization

open nonZeroDivisors

theorem bot_lt_comap_prime [IsDomain R] (hM : M ≤ R⁰) (p : Ideal S) [hpp : p.IsPrime]
    (hp0 : p ≠ ⊥) : ⊥ < Ideal.comap (algebraMap R S) p := by
  haveI : IsDomain S := isDomain_of_le_nonZeroDivisors _ hM
  -- ⊢ ⊥ < Ideal.comap (algebraMap R S) p
  rw [← Ideal.comap_bot_of_injective (algebraMap R S) (IsLocalization.injective _ hM)]
  -- ⊢ Ideal.comap (algebraMap R S) ⊥ < Ideal.comap (algebraMap R S) p
  convert (orderIsoOfPrime M S).lt_iff_lt.mpr (show (⟨⊥, Ideal.bot_prime⟩ :
    { p : Ideal S // p.IsPrime }) < ⟨p, hpp⟩ from hp0.bot_lt)
#align is_localization.bot_lt_comap_prime IsLocalization.bot_lt_comap_prime

end CommRing

end IsLocalization
