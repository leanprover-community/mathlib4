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

* `Polynomial.artinSchreier` refers to a term of the form `X ^ p - X - C a`.

TODO: extend to finite extensions whose Galois group is cyclic of order `p^n` (Artin-Schreier-Witt
theory).
-/

public section

namespace Polynomial

section CommRing

variable {F : Type*} [CommRing F]

open IntermediateField

/--
The Artin-Schreier polynomial defined by an element `a` of a ring `F` of exponential characteristic
`p` is `X ^ p - X - C a`.
-/
noncomputable def artinSchreier (a : F) : Polynomial F := X ^ ringExpChar F - X - C a

lemma artinSchreier_def (p : ℕ) [ExpChar F p] (a : F) :
    artinSchreier a = X ^ p - X - C a := by simp [artinSchreier, ringExpChar.eq F p]

lemma artinSchreier_taylor (p : ℕ) [ExpChar F p] (a c : F) :
    (artinSchreier a).taylor c = artinSchreier (-(artinSchreier a).eval c) := by
  simp_rw [artinSchreier_def p]
  rcases expChar_is_prime_or_one F p with hp | rfl
  · simp [add_pow_expChar]; ring
  · simp

lemma artinSchreier_map (p : ℕ) [ExpChar F p] (a : F) {K : Type*}
    [CommRing K] [ExpChar K p] (f : F →+* K) :
    (artinSchreier a).map f = artinSchreier (f a) := by
  simp [artinSchreier_def p]

@[simp]
lemma artinSchreier_isMonicOfDegree (p : ℕ) [ExpChar F p] [hp : Fact p.Prime]
    (a : F) : (artinSchreier a).IsMonicOfDegree p := by
  have : Nontrivial F := ExpChar.nontrivial F p
  rw [artinSchreier_def p]
  constructor
  · compute_degree <;> grind [one_ne_zero, hp.elim.one_lt]
  · monicity <;> grind [hp.elim.one_lt]

end CommRing

section Field

variable {F : Type*} [Field F]

open AdjoinRoot Multiset IntermediateField Polynomial

lemma artinSchreier_splits {a c : F} (hr : (artinSchreier a).IsRoot c) :
    Splits (artinSchreier a) := by
  let p := ringExpChar F
  have : ExpChar F p := ringExpChar.expChar F
  rcases expChar_is_prime_or_one F p with hp | hp1
  · rw [IsRoot.def] at hr
    rw [← splits_taylor_iff c, artinSchreier_taylor p, hr, artinSchreier_def p]
    have : CharP F p := (expChar_prime_iff F hp).mp ‹ExpChar F p›
    have := Fact.mk hp
    simpa using splits_X_pow_char_sub_X F p
  · simp [artinSchreier_def p, hp1]

variable (p : ℕ) [ExpChar F p]

lemma artinSchreier_irreducible [hp : Fact p.Prime]
    {a : F} (hr : (artinSchreier a).roots = 0) : Irreducible (artinSchreier a) := by
  have hmon := artinSchreier_isMonicOfDegree p a
  have h0 := hmon.ne_zero
  have ⟨b, hb2, hb3⟩ := exists_irreducible_of_natDegree_pos (hp.elim.pos.trans_eq hmon.1.symm)
  have h1 : b.natDegree ≠ 1 := by
    contrapose hr
    rw [eq_zero_iff_forall_notMem, not_forall_not]
    have ⟨x, hx⟩ := exists_root_of_natDegree_eq_one hr
    exact ⟨x, (mem_roots h0).mpr (hx.dvd hb3)⟩
  have h2 : b.natDegree ∣ (artinSchreier a).natDegree := by
    refine dvd_natDegree_of_monic_of_irreducible _ _ fun c hc0 hc hc1 ↦ ?_
    have := Fact.mk hc
    have : ExpChar (AdjoinRoot c) p := (RingHom.expChar_iff (algebraMap F _)
      (FaithfulSMul.algebraMap_injective F _) p).mp ‹ExpChar F p›
    rw [← (AdjoinRoot.isAdjoinRootMonic _ hc0).finrank]
    have hm0 : (artinSchreier a).map (of c) ≠ 0 := map_ne_zero h0
    have hdiv : b.map (of c) ∣ (artinSchreier a).map (of c) := map_dvd _ hb3
    have hc := IsRoot.dvd (isRoot_root c) (map_dvd (of c) hc1)
    have h : (artinSchreier a).map (of c) = artinSchreier (of c a) := by
      simp [artinSchreier_def p]
    rw [h] at hm0 hdiv hc
    exact hb2.natDegree_dvd_finrank ((artinSchreier_splits hc).of_dvd hm0 hdiv)
  have h3 := (((Nat.dvd_prime hp.elim).mp (h2.trans hmon.1.dvd)).resolve_left h1).symm
  exact (associated_of_dvd_of_natDegree_le hb3 h0 (hmon.1.trans h3).le).irreducible hb2

lemma artinSchreier_irreducible_or_splits (a : F) :
    Irreducible (artinSchreier a) ∨ Splits (artinSchreier a) := by
  let p := ringExpChar F
  have : ExpChar F p := ringExpChar.expChar F
  rcases expChar_is_prime_or_one F p with hp | hp1
  · have := Fact.mk hp
    by_cases hr : (artinSchreier a).roots = 0
    · left; exact artinSchreier_irreducible p hr
    · right
      have ⟨_, hc⟩ := exists_mem_of_ne_zero hr
      simp only [mem_roots', ne_eq] at hc
      exact artinSchreier_splits hc.2
  · right
    simp [artinSchreier_def p, hp1]

end Field

end Polynomial
