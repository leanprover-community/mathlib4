/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Eric Wieser
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Characteristic of quotient rings
-/

@[expose] public section

theorem CharP.ker_intAlgebraMap_eq_span
    {R : Type*} [Ring R] (p : ℕ) [CharP R p] :
    RingHom.ker (algebraMap ℤ R) = Ideal.span {(p : ℤ)} := by
  ext a
  simp [CharP.intCast_eq_zero_iff R p, Ideal.mem_span_singleton]

variable {R : Type*} [CommRing R]

namespace CharP

variable (R) in
theorem quotient (p : ℕ) [hp1 : Fact p.Prime] (hp2 : ↑p ∈ nonunits R) :
    CharP (R ⧸ (Ideal.span ({(p : R)} : Set R) : Ideal R)) p :=
  have hp0 : (p : R ⧸ (Ideal.span {(p : R)} : Ideal R)) = 0 :=
    map_natCast (Ideal.Quotient.mk (Ideal.span {(p : R)} : Ideal R)) p ▸
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span <| Set.mem_singleton _)
  ringChar.of_eq <|
    Or.resolve_left ((Nat.dvd_prime hp1.1).1 <| ringChar.dvd hp0) fun h1 =>
      hp2 <|
        isUnit_iff_dvd_one.2 <|
          Ideal.mem_span_singleton.1 <|
            Ideal.Quotient.eq_zero_iff_mem.1 <|
              @Subsingleton.elim _ (@CharOne.subsingleton _ _ (ringChar.of_eq h1)) _ _

/-- If an ideal does not contain any coercions of natural numbers other than zero, then its quotient
inherits the characteristic of the underlying ring. -/
theorem quotient' (p : ℕ) [CharP R p] (I : Ideal R) (h : ∀ x : ℕ, (x : R) ∈ I → (x : R) = 0) :
    CharP (R ⧸ I) p where
  cast_eq_zero_iff x := by
    rw [← cast_eq_zero_iff R p x, ← map_natCast (Ideal.Quotient.mk I)]
    refine Ideal.Quotient.eq.trans (?_ : ↑x - 0 ∈ I ↔ _)
    rw [sub_zero]
    exact ⟨h x, fun h' => h'.symm ▸ I.zero_mem⟩

/-- `CharP.quotient'` as an `Iff`. -/
theorem quotient_iff (n : ℕ) [CharP R n] (I : Ideal R) :
    CharP (R ⧸ I) n ↔ ∀ x : ℕ, ↑x ∈ I → (x : R) = 0 := by
  refine ⟨fun _ x hx => ?_, CharP.quotient' n I⟩
  rw [CharP.cast_eq_zero_iff R n, ← CharP.cast_eq_zero_iff (R ⧸ I) n _]
  exact (Submodule.Quotient.mk_eq_zero I).mpr hx

/-- `CharP.quotient_iff`, but stated in terms of inclusions of ideals. -/
theorem quotient_iff_le_ker_natCast (n : ℕ) [CharP R n] (I : Ideal R) :
    CharP (R ⧸ I) n ↔ I.comap (Nat.castRingHom R) ≤ RingHom.ker (Nat.castRingHom R) := by
  rw [CharP.quotient_iff, RingHom.ker_eq_comap_bot]; rfl

end CharP

lemma Ideal.natCast_mem_of_charP_quotient (p : ℕ) (I : Ideal R) [CharP (R ⧸ I) p] :
    (p : R) ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem.mp <| by simp

theorem Ideal.Quotient.index_eq_zero (I : Ideal R) : (↑I.toAddSubgroup.index : R ⧸ I) = 0 := by
  rw [AddSubgroup.index, Nat.card_eq]
  split_ifs with hq; swap
  · simp
  letI : Fintype (R ⧸ I) := @Fintype.ofFinite _ hq
  exact Nat.cast_card_eq_zero (R ⧸ I)
