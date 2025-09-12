/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.RingTheory.Ideal.Maps

/-!
# Ideals in product rings

For commutative rings `R` and `S` and ideals `I ≤ R`, `J ≤ S`, we define `Ideal.prod I J` as the
product `I × J`, viewed as an ideal of `R × S`. In `ideal_prod_eq` we show that every ideal of
`R × S` is of this form.  Furthermore, we show that every prime ideal of `R × S` is of the form
`p × S` or `R × p`, where `p` is a prime ideal.
-/


universe u v

variable {R : Type u} {S : Type v} [Semiring R] [Semiring S] (I : Ideal R) (J : Ideal S)

namespace Ideal

/-- `I × J` as an ideal of `R × S`. -/
def prod : Ideal (R × S) := I.comap (RingHom.fst R S) ⊓ J.comap (RingHom.snd R S)

@[simp]
theorem coe_prod (I : Ideal R) (J : Ideal S) : ↑(prod I J) = (I ×ˢ J : Set (R × S)) :=
  rfl

@[simp]
theorem mem_prod {x : R × S} : x ∈ prod I J ↔ x.1 ∈ I ∧ x.2 ∈ J :=
  Iff.rfl

@[simp]
theorem prod_top_top : prod (⊤ : Ideal R) (⊤ : Ideal S) = ⊤ :=
  Ideal.ext <| by simp

@[simp]
theorem prod_bot_bot : prod (⊥ : Ideal R) (⊥ : Ideal S) = ⊥ :=
  SetLike.coe_injective <| Set.singleton_prod_singleton

@[gcongr]
theorem prod_mono {I₁ I₂ : Ideal R} {J₁ J₂ : Ideal S} (hI : I₁ ≤ I₂) (hJ : J₁ ≤ J₂) :
    prod I₁ J₁ ≤ prod I₂ J₂ :=
  Set.prod_mono hI hJ

theorem prod_mono_left {I₁ I₂ : Ideal R} {J : Ideal S} (hI : I₁ ≤ I₂) : prod I₁ J ≤ prod I₂ J :=
  Set.prod_mono_left hI

theorem prod_mono_right {I : Ideal R} {J₁ J₂ : Ideal S} (hJ : J₁ ≤ J₂) : prod I J₁ ≤ prod I J₂ :=
  Set.prod_mono_right hJ

/-- Every ideal of the product ring is of the form `I × J`, where `I` and `J` can be explicitly
    given as the image under the projection maps. -/
theorem ideal_prod_eq (I : Ideal (R × S)) :
    I = Ideal.prod (map (RingHom.fst R S) I : Ideal R) (map (RingHom.snd R S) I) := by
  apply Ideal.ext
  rintro ⟨r, s⟩
  rw [mem_prod, mem_map_iff_of_surjective (RingHom.fst R S) Prod.fst_surjective,
    mem_map_iff_of_surjective (RingHom.snd R S) Prod.snd_surjective]
  refine ⟨fun h => ⟨⟨_, ⟨h, rfl⟩⟩, ⟨_, ⟨h, rfl⟩⟩⟩, ?_⟩
  rintro ⟨⟨⟨r, s'⟩, ⟨h₁, rfl⟩⟩, ⟨⟨r', s⟩, ⟨h₂, rfl⟩⟩⟩
  simpa using I.add_mem (I.mul_mem_left (1, 0) h₁) (I.mul_mem_left (0, 1) h₂)

@[simp]
theorem map_fst_prod (I : Ideal R) (J : Ideal S) : map (RingHom.fst R S) (prod I J) = I := by
  ext x
  rw [mem_map_iff_of_surjective (RingHom.fst R S) Prod.fst_surjective]
  exact
    ⟨by
      rintro ⟨x, ⟨h, rfl⟩⟩
      exact h.1, fun h => ⟨⟨x, 0⟩, ⟨⟨h, Ideal.zero_mem _⟩, rfl⟩⟩⟩

@[simp]
theorem map_snd_prod (I : Ideal R) (J : Ideal S) : map (RingHom.snd R S) (prod I J) = J := by
  ext x
  rw [mem_map_iff_of_surjective (RingHom.snd R S) Prod.snd_surjective]
  exact
    ⟨by
      rintro ⟨x, ⟨h, rfl⟩⟩
      exact h.2, fun h => ⟨⟨0, x⟩, ⟨⟨Ideal.zero_mem _, h⟩, rfl⟩⟩⟩

@[simp]
theorem map_prodComm_prod :
    map ((RingEquiv.prodComm : R × S ≃+* S × R) : R × S →+* S × R) (prod I J) = prod J I := by
  refine Trans.trans (ideal_prod_eq _) ?_
  simp [map_map]

/-- Ideals of `R × S` are in one-to-one correspondence with pairs of ideals of `R` and ideals of
`S`. -/
def idealProdEquiv : Ideal (R × S) ≃o Ideal R × Ideal S where
  toFun I := ⟨map (RingHom.fst R S) I, map (RingHom.snd R S) I⟩
  invFun I := prod I.1 I.2
  left_inv I := (ideal_prod_eq I).symm
  right_inv := fun ⟨I, J⟩ => by simp
  map_rel_iff' {I J} := by
    simp only [Equiv.coe_fn_mk, ge_iff_le, Prod.mk_le_mk]
    refine ⟨fun h ↦ ?_, fun h ↦ ⟨map_mono h, map_mono h⟩⟩
    rw [ideal_prod_eq I, ideal_prod_eq J]
    exact inf_le_inf (comap_mono h.1) (comap_mono h.2)

@[simp]
theorem idealProdEquiv_symm_apply (I : Ideal R) (J : Ideal S) :
    idealProdEquiv.symm ⟨I, J⟩ = prod I J :=
  rfl

theorem span_prod_le {s : Set R} {t : Set S} :
    span (s ×ˢ t) ≤ prod (span s) (span t) := by
  rw [ideal_prod_eq (span (s ×ˢ t)), map_span, map_span]
  gcongr
  · exact Set.fst_image_prod_subset _ _
  · exact Set.snd_image_prod_subset _ _

theorem span_prod {s : Set R} {t : Set S} (hst : s.Nonempty ↔ t.Nonempty) :
    span (s ×ˢ t) = prod (span s) (span t) := by
  simp_rw [iff_iff_and_or_not_and_not, Set.not_nonempty_iff_eq_empty] at hst
  obtain ⟨hs, ht⟩ | ⟨rfl, rfl⟩ := hst
  · conv_lhs => rw [Ideal.ideal_prod_eq (Ideal.span (s ×ˢ t))]
    congr 1
    · rw [Ideal.map_span]
      simp [Set.fst_image_prod _ ht]
    · rw [Ideal.map_span]
      simp [Set.snd_image_prod hs]
  · simp

@[simp]
theorem prod_inj {I I' : Ideal R} {J J' : Ideal S} :
    prod I J = prod I' J' ↔ I = I' ∧ J = J' := by
  simp only [← idealProdEquiv_symm_apply, idealProdEquiv.symm.injective.eq_iff, Prod.mk_inj]

@[deprecated (since := "2025-05-22")] alias prod.ext_iff := prod_inj

@[simp]
theorem prod_eq_bot_iff {I : Ideal R} {J : Ideal S} :
    prod I J = ⊥ ↔ I = ⊥ ∧ J = ⊥ := by
  rw [← prod_inj, prod_bot_bot]

@[simp]
theorem prod_eq_top_iff {I : Ideal R} {J : Ideal S} :
    prod I J = ⊤ ↔ I = ⊤ ∧ J = ⊤ := by
  rw [← prod_inj, prod_top_top]

theorem isPrime_of_isPrime_prod_top {I : Ideal R} (h : (Ideal.prod I (⊤ : Ideal S)).IsPrime) :
    I.IsPrime := by
  constructor
  · contrapose! h
    rw [h, prod_top_top, isPrime_iff]
    simp
  · intro x y hxy
    have : (⟨x, 1⟩ : R × S) * ⟨y, 1⟩ ∈ prod I ⊤ := by
      rw [Prod.mk_mul_mk, mul_one, mem_prod]
      exact ⟨hxy, trivial⟩
    simpa using h.mem_or_mem this

theorem isPrime_of_isPrime_prod_top' {I : Ideal S} (h : (Ideal.prod (⊤ : Ideal R) I).IsPrime) :
    I.IsPrime := by
  apply isPrime_of_isPrime_prod_top (S := R)
  rw [← map_prodComm_prod]
  -- Note: couldn't synthesize the right instances without the `R` and `S` hints
  exact map_isPrime_of_equiv (RingEquiv.prodComm (R := R) (S := S))

theorem isPrime_ideal_prod_top {I : Ideal R} [h : I.IsPrime] : (prod I (⊤ : Ideal S)).IsPrime where
  ne_top' := by simpa using h.ne_top
  mem_or_mem' {x y} := by simpa using h.mem_or_mem

theorem isPrime_ideal_prod_top' {I : Ideal S} [h : I.IsPrime] : (prod (⊤ : Ideal R) I).IsPrime := by
  letI : IsPrime (prod I (⊤ : Ideal R)) := isPrime_ideal_prod_top
  rw [← map_prodComm_prod]
  -- Note: couldn't synthesize the right instances without the `R` and `S` hints
  exact map_isPrime_of_equiv (RingEquiv.prodComm (R := S) (S := R))

theorem ideal_prod_prime_aux {I : Ideal R} {J : Ideal S} :
    (Ideal.prod I J).IsPrime → I = ⊤ ∨ J = ⊤ := by
  contrapose!
  simp only [ne_top_iff_one, isPrime_iff, not_and, not_forall, not_or]
  exact fun ⟨hI, hJ⟩ _ => ⟨⟨0, 1⟩, ⟨1, 0⟩, by simp, by simp [hJ], by simp [hI]⟩

/-- Classification of prime ideals in product rings: the prime ideals of `R × S` are precisely the
    ideals of the form `p × S` or `R × p`, where `p` is a prime ideal of `R` or `S`. -/
theorem ideal_prod_prime (I : Ideal (R × S)) :
    I.IsPrime ↔
      (∃ p : Ideal R, p.IsPrime ∧ I = Ideal.prod p ⊤) ∨
        ∃ p : Ideal S, p.IsPrime ∧ I = Ideal.prod ⊤ p := by
  constructor
  · rw [ideal_prod_eq I]
    intro hI
    rcases ideal_prod_prime_aux hI with (h | h)
    · right
      rw [h] at hI ⊢
      exact ⟨_, ⟨isPrime_of_isPrime_prod_top' hI, rfl⟩⟩
    · left
      rw [h] at hI ⊢
      exact ⟨_, ⟨isPrime_of_isPrime_prod_top hI, rfl⟩⟩
  · rintro (⟨p, ⟨h, rfl⟩⟩ | ⟨p, ⟨h, rfl⟩⟩)
    · exact isPrime_ideal_prod_top
    · exact isPrime_ideal_prod_top'

end Ideal

open Submodule.IsPrincipal in
instance [IsPrincipalIdealRing R] [IsPrincipalIdealRing S] : IsPrincipalIdealRing (R × S) where
  principal I := by
    rw [I.ideal_prod_eq, ← span_singleton_generator (I.map _),
      ← span_singleton_generator (I.map (RingHom.snd R S)), ← Ideal.span, ← Ideal.span,
      ← Ideal.span_prod (iff_of_true (by simp) (by simp)), Set.singleton_prod_singleton]
    exact ⟨_, rfl⟩
