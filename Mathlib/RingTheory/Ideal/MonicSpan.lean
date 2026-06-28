/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Basic

/-!

# Lemmas for ideal in polynomial span by monic polynomial

-/

@[expose] public section

variable (R : Type*) [CommRing R]

open Polynomial Ideal

lemma Polynomial.exists_monic_span {k : Type*} [Field k] (I : Ideal k[X]) (ne : I ≠ ⊥) :
    ∃ f, f.Monic ∧ I = Ideal.span {f} := by
  classical
  obtain ⟨x, rfl⟩ := IsPrincipalIdealRing.principal I
  have xne : x ≠ 0 := by
    by_contra eq0
    simp [eq0] at ne
  exact ⟨normalize x, monic_normalize xne,
    Ideal.span_singleton_eq_span_singleton.mpr (normalize_associated x).symm⟩

lemma Polynomial.exists_monic_span_sup_map_eq (p : Ideal R[X]) [p.IsPrime]
    (ism : (p.comap C).IsMaximal) (ne : p ≠ (p.comap C).map C) :
    ∃ f : R[X], f.Monic ∧ p = (p.comap C).map C ⊔ Ideal.span {f} := by
  let q := p.comap C
  let : Field (R ⧸ q) := Ideal.Quotient.field q
  have ne' : Ideal.map (mapRingHom (Ideal.Quotient.mk q)) p ≠ ⊥ := by
    simp only [ne_eq, map_eq_bot_iff_le_ker, Polynomial.ker_mapRingHom, q, mk_ker]
    exact not_le_of_gt (lt_of_le_of_ne Ideal.map_comap_le ne.symm)
  rcases Polynomial.exists_monic_span _ ne' with ⟨y, mony, hy⟩
  have : y ∈ lifts (Ideal.Quotient.mk q) := map_surjective _ Ideal.Quotient.mk_surjective _
  rcases Polynomial.lifts_and_natDegree_eq_and_monic this mony with ⟨f, hf, deg, monf⟩
  use f, monf
  trans comap (mapRingHom (Ideal.Quotient.mk q)) ((span {f}).map (mapRingHom (Ideal.Quotient.mk q)))
  · rw [Ideal.map_span, coe_mapRingHom, Set.image_singleton, hf, ← hy,
      Ideal.comap_map_of_surjective' _ (map_surjective _ Ideal.Quotient.mk_surjective)]
    simpa [Polynomial.ker_mapRingHom, q] using Ideal.map_comap_le
  · rw [Ideal.comap_map_of_surjective' _ (map_surjective _ Ideal.Quotient.mk_surjective),
      sup_comm, Polynomial.ker_mapRingHom, mk_ker]
