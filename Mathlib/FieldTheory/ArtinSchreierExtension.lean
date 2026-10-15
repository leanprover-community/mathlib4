/-
Copyright (c) 2026 Kiran S. Kedlaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kiran S. Kedlaya
-/
module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.IsAdjoinRoot
public import Mathlib.RingTheory.Trace.Basic

/-!
# Artin-Schreier Extensions

Let `K` be a field of prime characteristic `p`. Artin-Schreier theory classifies finite extensions
of `K` whose Galois group is cyclic of order `p`: they are obtained by adjoining a single root of a
polynomial of the form `X ^ p - X - C a` for some `a` in `K`.

## Naming convention

* `artinSchreierPoly` refers to a term of the form `X ^ p - X - C a`.

TODO: extend to finite extensions whose Galois group is cyclic of order `p^n` (Artin-Schreier-Witt
theory).
-/

public section
universe u

variable {F : Type u} [CommRing F]

open IntermediateField Polynomial

/--
The Artin-Schreier polynomial defined by an element `a` of a ring `F` of exponential characteristic
`p` is `X ^ p - X - C a`.
-/
noncomputable def artinSchreierPoly (a : F) : Polynomial F := X ^ ringExpChar F -  X - C a

lemma artinSchreierPoly_def (p : ℕ) [ExpChar F p] (a : F) :
    artinSchreierPoly a = X ^ p - X - C a := by simp [artinSchreierPoly, ringExpChar.eq F p]

lemma artinSchreierPoly_taylor (p : ℕ) [ExpChar F p] (a c : F) :
    (artinSchreierPoly a).taylor c = artinSchreierPoly (-(artinSchreierPoly a).eval c) := by
  simp_rw [artinSchreierPoly_def p]
  rcases expChar_is_prime_or_one F p with hp | rfl
  · simp [add_pow_expChar]; ring
  · simp

lemma artinSchreierPoly_map (p : ℕ) [ExpChar F p] (a : F) {K : Type u}
    [CommRing K] [ExpChar K p] (f : F →+* K) :
    (artinSchreierPoly a).map f = artinSchreierPoly (f a) := by
  simp [artinSchreierPoly_def p]

@[simp]
lemma artinSchreierPoly_isMonicOfDegree (p : ℕ) [ExpChar F p] [hp : Fact p.Prime]
    (a : F) : (artinSchreierPoly a).IsMonicOfDegree p := by
  have : CharP F p := (expChar_prime_iff F hp.elim).mp ‹ExpChar F p›
  have : Nontrivial F := CharP.nontrivial_of_char_ne_one hp.elim.ne_one
  rw [artinSchreierPoly_def p]
  constructor
  · compute_degree <;> grind [one_ne_zero, hp.elim.one_lt]
  · monicity <;> grind [hp.elim.one_lt]

variable {F : Type u} (p : ℕ) [Field F] [ExpChar F p]

open AdjoinRoot Multiset

lemma artinSchreierPoly_splits {a c : F} (hr : (artinSchreierPoly a).IsRoot c) :
    Splits (artinSchreierPoly a) := by
  let p := ringExpChar F
  have : ExpChar F p := ringExpChar.expChar F
  rcases expChar_is_prime_or_one F p with hp | hp1
  · rw [IsRoot.def] at hr
    rw [← Splits.taylor_iff c, artinSchreierPoly_taylor p, hr, artinSchreierPoly_def p]
    have : CharP F p := (expChar_prime_iff F hp).mp ‹ExpChar F p›
    have := Fact.mk hp
    simpa using splits_X_pow_char_sub_X F p
  · simp [artinSchreierPoly_def p, hp1]

lemma artinSchreierPoly_irreducible [hp : Fact p.Prime]
    {a : F} (hr : (artinSchreierPoly a).roots = 0) : Irreducible (artinSchreierPoly a) := by
  have hmon := artinSchreierPoly_isMonicOfDegree p a
  have h0 := hmon.ne_zero
  have ⟨b, hb2, hb3⟩ := exists_irreducible_of_natDegree_pos (hp.elim.pos.trans_eq hmon.1.symm)
  have h1 : b.natDegree ≠ 1 := by
    contrapose hr
    rw [eq_zero_iff_forall_notMem, not_forall_not]
    have ⟨x, hx⟩ := exists_root_of_natDegree_eq_one hr
    exact ⟨x, (mem_roots h0).mpr (hx.dvd hb3)⟩
  have h2 : b.natDegree ∣ (artinSchreierPoly a).natDegree := by
    refine dvd_natDegree_of_monic_of_irreducible _ fun c hc0 hc hc1 ↦ ?_
    have := Fact.mk hc
    have : ExpChar (AdjoinRoot c) p := (RingHom.expChar_iff (algebraMap F _)
      (FaithfulSMul.algebraMap_injective F _) p).mp ‹ExpChar F p›
    rw [← (AdjoinRoot.isAdjoinRootMonic _ hc0).finrank]
    have hm0 : (artinSchreierPoly a).map (of c) ≠ 0 := map_ne_zero h0
    have hdiv : b.map (of c) ∣ (artinSchreierPoly a).map (of c) := map_dvd _ hb3
    have hc := IsRoot.dvd (isRoot_root c) (map_dvd (of c) hc1)
    have h : (artinSchreierPoly a).map (of c) = artinSchreierPoly (of c a) := by
      simp [artinSchreierPoly_def p]
    rw [h] at hm0 hdiv hc
    exact hb2.natDegree_dvd_finrank ((artinSchreierPoly_splits hc).of_dvd hm0 hdiv)
  have h3 := (((Nat.dvd_prime hp.elim).mp (h2.trans hmon.1.dvd)).resolve_left h1).symm
  exact (associated_of_dvd_of_natDegree_le hb3 h0 (hmon.1.trans h3).le).irreducible hb2

lemma artinSchreierPoly_irreducible_or_splits (a : F) :
    Irreducible (artinSchreierPoly a) ∨ Splits (artinSchreierPoly a) := by
  let p := ringExpChar F
  have : ExpChar F p := ringExpChar.expChar F
  rcases expChar_is_prime_or_one F p with hp | hp1
  · have := Fact.mk hp
    by_cases hr : (artinSchreierPoly a).roots = 0
    · left; exact artinSchreierPoly_irreducible p hr
    · right
      have ⟨_, hc⟩ := exists_mem_of_ne_zero hr
      simp only [mem_roots', ne_eq] at hc
      exact artinSchreierPoly_splits hc.2
  · right
    simp [artinSchreierPoly_def p, hp1]
