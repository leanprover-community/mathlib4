/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Devon Tuma
-/
import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Polynomial.Quotient

#align_import ring_theory.jacobson_ideal from "leanprover-community/mathlib"@"da420a8c6dd5bdfb85c4ced85c34388f633bc6ff"

/-!
# Jacobson radical

The Jacobson radical of a ring `R` is defined to be the intersection of all maximal ideals of `R`.
This is similar to how the nilradical is equal to the intersection of all prime ideals of `R`.

We can extend the idea of the nilradical to ideals of `R`,
by letting the radical of an ideal `I` be the intersection of prime ideals containing `I`.
Under this extension, the original nilradical is the radical of the zero ideal `⊥`.
Here we define the Jacobson radical of an ideal `I` in a similar way,
as the intersection of maximal ideals containing `I`.

## Main definitions

Let `R` be a commutative ring, and `I` be an ideal of `R`

* `Ideal.jacobson I` is the jacobson radical, i.e. the infimum of all maximal ideals containing I.

* `Ideal.IsLocal I` is the proposition that the jacobson radical of `I` is itself a maximal ideal

## Main statements

* `mem_jacobson_iff` gives a characterization of members of the jacobson of I

* `Ideal.isLocal_of_isMaximal_radical`: if the radical of I is maximal then so is the jacobson
  radical

## Tags

Jacobson, Jacobson radical, Local Ideal

-/


universe u v

namespace Ideal

variable {R : Type u} {S : Type v}

open Polynomial

section Jacobson

section Ring

variable [Ring R] [Ring S] {I : Ideal R}

/-- The Jacobson radical of `I` is the infimum of all maximal (left) ideals containing `I`. -/
def jacobson (I : Ideal R) : Ideal R :=
  sInf { J : Ideal R | I ≤ J ∧ IsMaximal J }
#align ideal.jacobson Ideal.jacobson

theorem le_jacobson : I ≤ jacobson I := fun _ hx => mem_sInf.mpr fun _ hJ => hJ.left hx
#align ideal.le_jacobson Ideal.le_jacobson

@[simp]
theorem jacobson_idem : jacobson (jacobson I) = jacobson I :=
  le_antisymm (sInf_le_sInf fun _ hJ => ⟨sInf_le hJ, hJ.2⟩) le_jacobson
#align ideal.jacobson_idem Ideal.jacobson_idem

@[simp]
theorem jacobson_top : jacobson (⊤ : Ideal R) = ⊤ :=
  eq_top_iff.2 le_jacobson
#align ideal.jacobson_top Ideal.jacobson_top

@[simp]
theorem jacobson_eq_top_iff : jacobson I = ⊤ ↔ I = ⊤ :=
  ⟨fun H =>
    by_contradiction fun hi => let ⟨M, hm, him⟩ := exists_le_maximal I hi
      lt_top_iff_ne_top.1
        (lt_of_le_of_lt (show jacobson I ≤ M from sInf_le ⟨him, hm⟩) <|
          lt_top_iff_ne_top.2 hm.ne_top) H,
    fun H => eq_top_iff.2 <| le_sInf fun _ ⟨hij, _⟩ => H ▸ hij⟩
#align ideal.jacobson_eq_top_iff Ideal.jacobson_eq_top_iff

theorem jacobson_eq_bot : jacobson I = ⊥ → I = ⊥ := fun h => eq_bot_iff.mpr (h ▸ le_jacobson)
#align ideal.jacobson_eq_bot Ideal.jacobson_eq_bot

theorem jacobson_eq_self_of_isMaximal [H : IsMaximal I] : I.jacobson = I :=
  le_antisymm (sInf_le ⟨le_of_eq rfl, H⟩) le_jacobson
#align ideal.jacobson_eq_self_of_is_maximal Ideal.jacobson_eq_self_of_isMaximal

instance (priority := 100) jacobson.isMaximal [H : IsMaximal I] : IsMaximal (jacobson I) :=
  ⟨⟨fun htop => H.1.1 (jacobson_eq_top_iff.1 htop), fun _ hJ =>
    H.1.2 _ (lt_of_le_of_lt le_jacobson hJ)⟩⟩
#align ideal.jacobson.is_maximal Ideal.jacobson.isMaximal

theorem mem_jacobson_iff {x : R} : x ∈ jacobson I ↔ ∀ y, ∃ z, z * y * x + z - 1 ∈ I :=
  ⟨fun hx y =>
    by_cases
      (fun hxy : I ⊔ span {y * x + 1} = ⊤ =>
        let ⟨p, hpi, q, hq, hpq⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 hxy)
        let ⟨r, hr⟩ := mem_span_singleton'.1 hq
        ⟨r, by
          -- Porting note: supply `mul_add_one` with explicit variables
          rw [mul_assoc, ← mul_add_one r (y * x), hr, ← hpq, ← neg_sub, add_sub_cancel_right]
          exact I.neg_mem hpi⟩)
      fun hxy : I ⊔ span {y * x + 1} ≠ ⊤ => let ⟨M, hm1, hm2⟩ := exists_le_maximal _ hxy
      suffices x ∉ M from (this <| mem_sInf.1 hx ⟨le_trans le_sup_left hm2, hm1⟩).elim
      fun hxm => hm1.1.1 <| (eq_top_iff_one _).2 <| add_sub_cancel_left (y * x) 1 ▸
        M.sub_mem (le_sup_right.trans hm2 <| subset_span rfl) (M.mul_mem_left _ hxm),
    fun hx => mem_sInf.2 fun M ⟨him, hm⟩ => by_contradiction fun hxm =>
      let ⟨y, i, hi, df⟩ := hm.exists_inv hxm
      let ⟨z, hz⟩ := hx (-y)
      hm.1.1 <| (eq_top_iff_one _).2 <| sub_sub_cancel (z * -y * x + z) 1 ▸
        M.sub_mem (by
          -- Porting note: supply `mul_add_one` with explicit variables
          rw [mul_assoc, ← mul_add_one z, neg_mul, ← sub_eq_iff_eq_add.mpr df.symm, neg_sub,
            sub_add_cancel]
          exact M.mul_mem_left _ hi) <| him hz⟩
#align ideal.mem_jacobson_iff Ideal.mem_jacobson_iff

theorem exists_mul_sub_mem_of_sub_one_mem_jacobson {I : Ideal R} (r : R) (h : r - 1 ∈ jacobson I) :
    ∃ s, s * r - 1 ∈ I := by
  cases' mem_jacobson_iff.1 h 1 with s hs
  use s
  simpa [mul_sub] using hs
#align ideal.exists_mul_sub_mem_of_sub_one_mem_jacobson Ideal.exists_mul_sub_mem_of_sub_one_mem_jacobson

/-- An ideal equals its Jacobson radical iff it is the intersection of a set of maximal ideals.
Allowing the set to include ⊤ is equivalent, and is included only to simplify some proofs. -/
theorem eq_jacobson_iff_sInf_maximal :
    I.jacobson = I ↔ ∃ M : Set (Ideal R), (∀ J ∈ M, IsMaximal J ∨ J = ⊤) ∧ I = sInf M := by
  use fun hI => ⟨{ J : Ideal R | I ≤ J ∧ J.IsMaximal }, ⟨fun _ hJ => Or.inl hJ.right, hI.symm⟩⟩
  rintro ⟨M, hM, hInf⟩
  refine le_antisymm (fun x hx => ?_) le_jacobson
  rw [hInf, mem_sInf]
  intro I hI
  cases' hM I hI with is_max is_top
  · exact (mem_sInf.1 hx) ⟨le_sInf_iff.1 (le_of_eq hInf) I hI, is_max⟩
  · exact is_top.symm ▸ Submodule.mem_top
#align ideal.eq_jacobson_iff_Inf_maximal Ideal.eq_jacobson_iff_sInf_maximal

theorem eq_jacobson_iff_sInf_maximal' :
    I.jacobson = I ↔ ∃ M : Set (Ideal R), (∀ J ∈ M, ∀ (K : Ideal R), J < K → K = ⊤) ∧ I = sInf M :=
  eq_jacobson_iff_sInf_maximal.trans
    ⟨fun h =>
      let ⟨M, hM⟩ := h
      ⟨M,
        ⟨fun J hJ K hK =>
          Or.recOn (hM.1 J hJ) (fun h => h.1.2 K hK) fun h => eq_top_iff.2 (le_of_lt (h ▸ hK)),
          hM.2⟩⟩,
      fun h =>
      let ⟨M, hM⟩ := h
      ⟨M,
        ⟨fun J hJ =>
          Or.recOn (Classical.em (J = ⊤)) (fun h => Or.inr h) fun h => Or.inl ⟨⟨h, hM.1 J hJ⟩⟩,
          hM.2⟩⟩⟩
#align ideal.eq_jacobson_iff_Inf_maximal' Ideal.eq_jacobson_iff_sInf_maximal'

/-- An ideal `I` equals its Jacobson radical if and only if every element outside `I`
also lies outside of a maximal ideal containing `I`. -/
theorem eq_jacobson_iff_not_mem :
    I.jacobson = I ↔ ∀ (x) (_ : x ∉ I), ∃ M : Ideal R, (I ≤ M ∧ M.IsMaximal) ∧ x ∉ M := by
  constructor
  · intro h x hx
    erw [← h, mem_sInf] at hx
    push_neg at hx
    exact hx
  · refine fun h => le_antisymm (fun x hx => ?_) le_jacobson
    contrapose hx
    erw [mem_sInf]
    push_neg
    exact h x hx
#align ideal.eq_jacobson_iff_not_mem Ideal.eq_jacobson_iff_not_mem

theorem map_jacobson_of_surjective {f : R →+* S} (hf : Function.Surjective f) :
    RingHom.ker f ≤ I → map f I.jacobson = (map f I).jacobson := by
  intro h
  unfold Ideal.jacobson
  -- Porting note: dot notation for `RingHom.ker` does not work
  have : ∀ J ∈ { J : Ideal R | I ≤ J ∧ J.IsMaximal }, RingHom.ker f ≤ J :=
    fun J hJ => le_trans h hJ.left
  refine Trans.trans (map_sInf hf this) (le_antisymm ?_ ?_)
  · refine
      sInf_le_sInf fun J hJ =>
        ⟨comap f J, ⟨⟨le_comap_of_map_le hJ.1, ?_⟩, map_comap_of_surjective f hf J⟩⟩
    haveI : J.IsMaximal := hJ.right
    exact comap_isMaximal_of_surjective f hf
  · refine sInf_le_sInf_of_subset_insert_top fun j hj => hj.recOn fun J hJ => ?_
    rw [← hJ.2]
    cases' map_eq_top_or_isMaximal_of_surjective f hf hJ.left.right with htop hmax
    · exact htop.symm ▸ Set.mem_insert ⊤ _
    · exact Set.mem_insert_of_mem ⊤ ⟨map_mono hJ.1.1, hmax⟩
#align ideal.map_jacobson_of_surjective Ideal.map_jacobson_of_surjective

theorem map_jacobson_of_bijective {f : R →+* S} (hf : Function.Bijective f) :
    map f I.jacobson = (map f I).jacobson :=
  map_jacobson_of_surjective hf.right
    (le_trans (le_of_eq (f.injective_iff_ker_eq_bot.1 hf.left)) bot_le)
#align ideal.map_jacobson_of_bijective Ideal.map_jacobson_of_bijective

theorem comap_jacobson {f : R →+* S} {K : Ideal S} :
    comap f K.jacobson = sInf (comap f '' { J : Ideal S | K ≤ J ∧ J.IsMaximal }) :=
  Trans.trans (comap_sInf' f _) sInf_eq_iInf.symm
#align ideal.comap_jacobson Ideal.comap_jacobson

theorem comap_jacobson_of_surjective {f : R →+* S} (hf : Function.Surjective f) {K : Ideal S} :
    comap f K.jacobson = (comap f K).jacobson := by
  unfold Ideal.jacobson
  refine le_antisymm ?_ ?_
  · rw [← top_inf_eq (sInf _), ← sInf_insert, comap_sInf', sInf_eq_iInf]
    refine iInf_le_iInf_of_subset fun J hJ => ?_
    have : comap f (map f J) = J :=
      Trans.trans (comap_map_of_surjective f hf J)
        (le_antisymm (sup_le_iff.2 ⟨le_of_eq rfl, le_trans (comap_mono bot_le) hJ.left⟩)
          le_sup_left)
    cases' map_eq_top_or_isMaximal_of_surjective _ hf hJ.right with htop hmax
    · exact ⟨⊤, Set.mem_insert ⊤ _, htop ▸ this⟩
    · exact ⟨map f J, Set.mem_insert_of_mem _ ⟨le_map_of_comap_le_of_surjective f hf hJ.1, hmax⟩,
        this⟩
  · simp_rw [comap_sInf, le_iInf_iff]
    intros J hJ
    haveI : J.IsMaximal := hJ.right
    exact sInf_le ⟨comap_mono hJ.left, comap_isMaximal_of_surjective _ hf⟩
#align ideal.comap_jacobson_of_surjective Ideal.comap_jacobson_of_surjective

@[mono]
theorem jacobson_mono {I J : Ideal R} : I ≤ J → I.jacobson ≤ J.jacobson := by
  intro h x hx
  erw [mem_sInf] at hx ⊢
  exact fun K ⟨hK, hK_max⟩ => hx ⟨Trans.trans h hK, hK_max⟩
#align ideal.jacobson_mono Ideal.jacobson_mono

end Ring

section CommRing

variable [CommRing R] [CommRing S] {I : Ideal R}

theorem radical_le_jacobson : radical I ≤ jacobson I :=
  le_sInf fun _ hJ => (radical_eq_sInf I).symm ▸ sInf_le ⟨hJ.left, IsMaximal.isPrime hJ.right⟩
#align ideal.radical_le_jacobson Ideal.radical_le_jacobson

theorem isRadical_of_eq_jacobson (h : jacobson I = I) : I.IsRadical :=
  radical_le_jacobson.trans h.le
#align ideal.is_radical_of_eq_jacobson Ideal.isRadical_of_eq_jacobson

theorem isUnit_of_sub_one_mem_jacobson_bot (r : R) (h : r - 1 ∈ jacobson (⊥ : Ideal R)) :
    IsUnit r := by
  cases' exists_mul_sub_mem_of_sub_one_mem_jacobson r h with s hs
  rw [mem_bot, sub_eq_zero, mul_comm] at hs
  exact isUnit_of_mul_eq_one _ _ hs
#align ideal.is_unit_of_sub_one_mem_jacobson_bot Ideal.isUnit_of_sub_one_mem_jacobson_bot

theorem mem_jacobson_bot {x : R} : x ∈ jacobson (⊥ : Ideal R) ↔ ∀ y, IsUnit (x * y + 1) :=
  ⟨fun hx y =>
    let ⟨z, hz⟩ := (mem_jacobson_iff.1 hx) y
    isUnit_iff_exists_inv.2
      ⟨z, by rwa [add_mul, one_mul, ← sub_eq_zero, mul_right_comm, mul_comm _ z, mul_right_comm]⟩,
    fun h =>
    mem_jacobson_iff.mpr fun y =>
      let ⟨b, hb⟩ := isUnit_iff_exists_inv.1 (h y)
      ⟨b, (Submodule.mem_bot R).2 (hb ▸ by ring)⟩⟩
#align ideal.mem_jacobson_bot Ideal.mem_jacobson_bot

/-- An ideal `I` of `R` is equal to its Jacobson radical if and only if
the Jacobson radical of the quotient ring `R/I` is the zero ideal -/
-- Porting note: changed `Quotient.mk'` to ``
theorem jacobson_eq_iff_jacobson_quotient_eq_bot :
    I.jacobson = I ↔ jacobson (⊥ : Ideal (R ⧸ I)) = ⊥ := by
  have hf : Function.Surjective (Ideal.Quotient.mk I) := Submodule.Quotient.mk_surjective I
  constructor
  · intro h
    replace h := congr_arg (Ideal.map (Ideal.Quotient.mk I)) h
    rw [map_jacobson_of_surjective hf (le_of_eq mk_ker)] at h
    simpa using h
  · intro h
    replace h := congr_arg (comap (Ideal.Quotient.mk I)) h
    rw [comap_jacobson_of_surjective hf, ← RingHom.ker_eq_comap_bot (Ideal.Quotient.mk I)] at h
    simpa using h
#align ideal.jacobson_eq_iff_jacobson_quotient_eq_bot Ideal.jacobson_eq_iff_jacobson_quotient_eq_bot

/-- The standard radical and Jacobson radical of an ideal `I` of `R` are equal if and only if
the nilradical and Jacobson radical of the quotient ring `R/I` coincide -/
-- Porting note: changed `Quotient.mk'` to ``
theorem radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot :
    I.radical = I.jacobson ↔ radical (⊥ : Ideal (R ⧸ I)) = jacobson ⊥ := by
  have hf : Function.Surjective (Ideal.Quotient.mk I) := Submodule.Quotient.mk_surjective I
  constructor
  · intro h
    have := congr_arg (map (Ideal.Quotient.mk I)) h
    rw [map_radical_of_surjective hf (le_of_eq mk_ker),
      map_jacobson_of_surjective hf (le_of_eq mk_ker)] at this
    simpa using this
  · intro h
    have := congr_arg (comap (Ideal.Quotient.mk I)) h
    rw [comap_radical, comap_jacobson_of_surjective hf,
      ← RingHom.ker_eq_comap_bot (Ideal.Quotient.mk I)] at this
    simpa using this
#align ideal.radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot Ideal.radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot

theorem jacobson_radical_eq_jacobson : I.radical.jacobson = I.jacobson :=
  le_antisymm
    (le_trans (le_of_eq (congr_arg jacobson (radical_eq_sInf I)))
      (sInf_le_sInf fun _ hJ => ⟨sInf_le ⟨hJ.1, hJ.2.isPrime⟩, hJ.2⟩))
    (jacobson_mono le_radical)
#align ideal.jacobson_radical_eq_jacobson Ideal.jacobson_radical_eq_jacobson

end CommRing

end Jacobson

section Polynomial

open Polynomial

variable [CommRing R]

theorem jacobson_bot_polynomial_le_sInf_map_maximal :
    jacobson (⊥ : Ideal R[X]) ≤ sInf (map (C : R →+* R[X]) '' { J : Ideal R | J.IsMaximal }) := by
  refine le_sInf fun J => exists_imp.2 fun j hj => ?_
  haveI : j.IsMaximal := hj.1
  refine Trans.trans (jacobson_mono bot_le) (le_of_eq ?_ : J.jacobson ≤ J)
  suffices t : (⊥ : Ideal (Polynomial (R ⧸ j))).jacobson = ⊥ by
    rw [← hj.2, jacobson_eq_iff_jacobson_quotient_eq_bot]
    replace t := congr_arg (map (polynomialQuotientEquivQuotientPolynomial j).toRingHom) t
    rwa [map_jacobson_of_bijective _, map_bot] at t
    exact RingEquiv.bijective (polynomialQuotientEquivQuotientPolynomial j)
  refine eq_bot_iff.2 fun f hf => ?_
  have r1 : (X : (R ⧸ j)[X]) ≠ 0 := fun hX => by
    replace hX := congr_arg (fun f => coeff f 1) hX
    simp only [coeff_X_one, coeff_zero] at hX
    exact zero_ne_one hX.symm
  have r2 := eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit ((mem_jacobson_bot.1 hf) X))
  simp only [coeff_add, mul_coeff_zero, coeff_X_zero, mul_zero, coeff_one_zero, zero_add] at r2
  erw [add_left_eq_self] at r2
  simpa using (mul_eq_zero.mp r2).resolve_right r1
  -- Porting note: this is golfed to much
  -- simpa [(fun hX => by simpa using congr_arg (fun f => coeff f 1) hX : (X : (R ⧸ j)[X]) ≠ 0)]
  --   using eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit ((mem_jacobson_bot.1 hf) X))
#align ideal.jacobson_bot_polynomial_le_Inf_map_maximal Ideal.jacobson_bot_polynomial_le_sInf_map_maximal

theorem jacobson_bot_polynomial_of_jacobson_bot (h : jacobson (⊥ : Ideal R) = ⊥) :
    jacobson (⊥ : Ideal R[X]) = ⊥ := by
  refine eq_bot_iff.2 (le_trans jacobson_bot_polynomial_le_sInf_map_maximal ?_)
  refine fun f hf => (Submodule.mem_bot R[X]).2 <| Polynomial.ext fun n =>
    Trans.trans (?_ : coeff f n = 0) (coeff_zero n).symm
  suffices f.coeff n ∈ Ideal.jacobson ⊥ by rwa [h, Submodule.mem_bot] at this
  exact mem_sInf.2 fun j hj => (mem_map_C_iff.1 ((mem_sInf.1 hf) ⟨j, ⟨hj.2, rfl⟩⟩)) n
#align ideal.jacobson_bot_polynomial_of_jacobson_bot Ideal.jacobson_bot_polynomial_of_jacobson_bot

end Polynomial

section IsLocal

variable [CommRing R]

/-- An ideal `I` is local iff its Jacobson radical is maximal. -/
class IsLocal (I : Ideal R) : Prop where
  /-- A ring `R` is local if and only if its jacobson radical is maximal -/
  out : IsMaximal (jacobson I)
#align ideal.is_local Ideal.IsLocal

theorem isLocal_iff {I : Ideal R} : IsLocal I ↔ IsMaximal (jacobson I) :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align ideal.is_local_iff Ideal.isLocal_iff

theorem isLocal_of_isMaximal_radical {I : Ideal R} (hi : IsMaximal (radical I)) : IsLocal I :=
  ⟨have : radical I = jacobson I :=
      le_antisymm (le_sInf fun _ ⟨him, hm⟩ => hm.isPrime.radical_le_iff.2 him)
        (sInf_le ⟨le_radical, hi⟩)
    show IsMaximal (jacobson I) from this ▸ hi⟩
#align ideal.is_local_of_is_maximal_radical Ideal.isLocal_of_isMaximal_radical

theorem IsLocal.le_jacobson {I J : Ideal R} (hi : IsLocal I) (hij : I ≤ J) (hj : J ≠ ⊤) :
    J ≤ jacobson I :=
  let ⟨_, hm, hjm⟩ := exists_le_maximal J hj
  le_trans hjm <| le_of_eq <| Eq.symm <| hi.1.eq_of_le hm.1.1 <| sInf_le ⟨le_trans hij hjm, hm⟩
#align ideal.is_local.le_jacobson Ideal.IsLocal.le_jacobson

theorem IsLocal.mem_jacobson_or_exists_inv {I : Ideal R} (hi : IsLocal I) (x : R) :
    x ∈ jacobson I ∨ ∃ y, y * x - 1 ∈ I :=
  by_cases
    (fun h : I ⊔ span {x} = ⊤ =>
      let ⟨p, hpi, q, hq, hpq⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 h)
      let ⟨r, hr⟩ := mem_span_singleton.1 hq
      Or.inr ⟨r, by
        rw [← hpq, mul_comm, ← hr, ← neg_sub, add_sub_cancel_right]; exact I.neg_mem hpi⟩)
    fun h : I ⊔ span {x} ≠ ⊤ =>
    Or.inl <|
      le_trans le_sup_right (hi.le_jacobson le_sup_left h) <| mem_span_singleton.2 <| dvd_refl x
#align ideal.is_local.mem_jacobson_or_exists_inv Ideal.IsLocal.mem_jacobson_or_exists_inv

end IsLocal

theorem isPrimary_of_isMaximal_radical [CommRing R] {I : Ideal R} (hi : IsMaximal (radical I)) :
    IsPrimary I :=
  have : radical I = jacobson I :=
    le_antisymm (le_sInf fun M ⟨him, hm⟩ => hm.isPrime.radical_le_iff.2 him)
      (sInf_le ⟨le_radical, hi⟩)
  ⟨ne_top_of_lt <| lt_of_le_of_lt le_radical (lt_top_iff_ne_top.2 hi.1.1), fun {x y} hxy =>
    ((isLocal_of_isMaximal_radical hi).mem_jacobson_or_exists_inv y).symm.imp
      (fun ⟨z, hz⟩ => by
        rw [← mul_one x, ← sub_sub_cancel (z * y) 1, mul_sub, mul_left_comm]
        exact I.sub_mem (I.mul_mem_left _ hxy) (I.mul_mem_left _ hz))
      (this ▸ id)⟩
#align ideal.is_primary_of_is_maximal_radical Ideal.isPrimary_of_isMaximal_radical

end Ideal
