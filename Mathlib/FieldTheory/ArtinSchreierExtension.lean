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

TODO:
* Extend to finite extensions whose Galois group is cyclic of order `p^n` (Artin-Schreier-Witt
theory).
* Rewrite in terms of "Additive Hilbert 90" once this has been implemented.

-/

public section
universe u

section ArtinScheierPolynomial

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
    rw [← splits_taylor_iff c, artinSchreierPoly_taylor p, hr, artinSchreierPoly_def p]
    have : CharP F p := (expChar_prime_iff F hp).mp ‹ExpChar F p›
    have := Fact.mk hp
    simp [splits_X_pow_char_sub_X F p]
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

end ArtinScheierPolynomial

section Lemmas

variable {F : Type u} {K : Type u} {p : ℕ} [Field F] [CharP F p] [Field K] [Algebra F K]
  [FiniteDimensional F K] [IsGalois F K] [hp : Fact p.Prime] (hrank : Module.finrank F K = p)
include hrank

open Finset

private
lemma generator_of_charP (g : Gal(K/F)) (h_gen : Subgroup.zpowers g = ⊤) :
    ∃ z : K, g z = z - 1 := by
  have := (Algebra.charP_iff F K p).mp ‹CharP F p›
  have h_ord := (IsGalois.card_aut_eq_finrank F K).trans hrank
  obtain ⟨y, hy⟩ := Algebra.trace_surjective F K 1
  let rp := Finset.range p
  use ∑ i : rp, (g ^ (i : ℕ)) y * i
  have hz1 : ∑ i : rp, (g ^ (i + 1 : ℕ)) y * (i + 1) = ∑ i : rp, (g ^ (i : ℕ)) y * i := by
    let f := fun (i : ℕ) ↦ (g ^ i) y * i
    have hp1 : p - 1 + 1 = p := Nat.succ_pred_prime hp.elim
    calc
    _ = ∑ i : rp, f (i + 1) := by simp [f]
    _ = ∑ i ∈ rp, f (i + 1) := (sum_subtype rp (fun _ ↦ Iff.of_eq rfl) fun i ↦ f (i + 1)).symm
    _ = ∑ i ∈ rp, f i := by subst rp f; rw [← hp1, sum_range_succ, sum_range_succ']; simp [hp1]
    _ = _ := sum_subtype rp (fun _ ↦ Iff.of_eq rfl) f
  have hz2 : ∑ i : rp, (g ^ (i + 1 : ℕ)) y = ∑ σ : Gal(K/F), σ y := by
    let f := fun (i : rp) ↦ g ^ (i + 1 : ℕ)
    refine sum_bijective f ?_ (by simp) fun _ _ ↦ rfl
    refine (Nat.bijective_iff_injective_and_card f).mpr
      ⟨fun a b h ↦ ?_, by rw [h_ord, Nat.card_eq_finsetCard rp, Finset.card_range p]⟩
    rw [pow_eq_pow_iff_modEq, Nat.ModEq.add_iff_right rfl, ← pow_eq_pow_iff_modEq, pow_inj_mod,
      orderOf_eq_card_of_zpowers_eq_top h_gen, h_ord, Nat.mod_eq_of_lt (by grind),
      Nat.mod_eq_of_lt (by grind), SetCoe.ext_iff] at h
    exact h
  calc
  _ = ∑ i : rp, g ((g ^ (i : ℕ)) y * i) := map_finsetSum ..
  _ = ∑ i : rp, (g ^ (i + 1 : ℕ)) y * i := by simp [pow_succ' g]
  _ = ∑ i : rp, ((g ^ (i + 1 : ℕ)) y * (i + 1) - (g ^ (i + 1 : ℕ)) y) := by grind only
  _ = _ := by rw [sum_sub_distrib, hz1, hz2, ← trace_eq_sum_automorphisms, hy, map_one]

end Lemmas

open Field IntermediateField minpoly Polynomial

variable {F : Type u} {K : Type u} {p : ℕ} [Field F] [ExpChar F p] [Field K] [Algebra F K]
  [hp : Fact p.Prime]

theorem isCyclic_charP_tfae (hrank : Module.finrank F K = p) :
    [IsGalois F K,
    ∃ a : F, Irreducible (artinSchreierPoly a) ∧ IsSplittingField F K (artinSchreierPoly a),
    ∃ α : K, α ^ p - α ∈ Set.range ⇑(algebraMap F K) ∧ F⟮α⟯ = ⊤,
    ∃ a : F, ∃ α : K, minpoly F α = artinSchreierPoly a,
    ∃ a : F, Nonempty (IsAdjoinRootMonic K (artinSchreierPoly a))].TFAE := by
  let := FiniteDimensional.of_finrank_pos (hp.elim.pos.trans_eq hrank.symm)
  have : CharP F p := (expChar_prime_iff F hp.elim).mp ‹ExpChar F p›
  have := (Algebra.charP_iff F K p).mp ‹CharP F p›
  have ha := fun (a : F) ↦ artinSchreierPoly_isMonicOfDegree p a
  have h_int := fun (z : K) ↦ Algebra.IsIntegral.isIntegral z (R := F)
  have hprim := fun (z : K) ↦ primitive_element_iff_minpoly_natDegree_eq F z
  tfae_have 1 → 3 := by
    intro hgal
    have h_ord := (hgal.card_aut_eq_finrank F K).trans hrank
    obtain ⟨g, h_gen⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (isCyclic_of_prime_card h_ord)
    obtain ⟨z, hgz⟩ := generator_of_charP hrank g h_gen
    refine ⟨z, ⟨(hgal.mem_range_algebraMap_iff_fixed _).mpr fun γ ↦ ?_, (hprim z).mpr (Eq.symm ?_)⟩⟩
    · obtain ⟨n, rfl⟩ : ∃ n, g ^ n = γ := Subgroup.mem_zpowers_iff.mp (by simp [h_gen])
      rw [← AlgEquiv.smul_def, ← MulAction.mem_fixedBy]
      exact MulAction.mem_fixedBy_zpow (by simp [hgz, sub_pow_char]) n
    · have hz := (hgal.mem_range_algebraMap_iff_fixed z).mp.mt (by grind)
      rw [hrank, ← hp.elim.dvd_iff_eq (natDegree_eq_one_iff.mp.mt hz)]
      simpa [hrank] using degree_dvd (h_int z)
  tfae_have 3 → 4 := by
    refine fun ⟨z, ⟨a, _⟩, htop⟩ ↦ ⟨a, z, ?_⟩
    refine (eq_of_monic_of_dvd_of_natDegree_le (monic (h_int z)) (ha a).2 (dvd _ _ ?_) ?_).symm
    · rw [artinSchreierPoly_def p]; aesop
    · simp [(ha a).1, (hprim z).mp htop, hrank]
  tfae_have 4 → 2 := by
    refine fun ⟨a, z, h⟩ ↦ ⟨a, ⟨by simpa [← h] using irreducible (h_int z), ?_⟩⟩
    set f := artinSchreierPoly a with hf
    have h_root : (f.map (algebraMap F K)).IsRoot z := by simpa [h, hf] using minpoly.aeval F z
    refine isSplittingField_iff_intermediateField.mpr ⟨?_, ?_⟩
    · rw [artinSchreierPoly_map p a] at h_root ⊢
      exact artinSchreierPoly_splits h_root
    · rw [eq_top_iff, ← (hprim z).mpr (by rw [h, (ha a).1, hrank]), adjoin_simple_le_iff]
      exact mem_adjoin_of_mem F ((ha a).2.mem_rootSet.mpr (by simp_all))
  tfae_have 2 → 1 :=
    fun ⟨a, h1, _⟩ ↦ IsGalois.of_separable_splitting_field ((separable_iff_derivative_ne_zero
      h1).mpr (by simp [artinSchreierPoly_def p, derivative_pow]))
  tfae_have 4 → 5 := by
    refine fun ⟨a, z, h⟩ ↦ ⟨a, Nonempty.intro ?_⟩
    rw [← h]
    refine IsAdjoinRootMonic.mkOfPrimitiveElement (h_int z) ((hprim z).mpr ?_)
    rw [h, (ha a).1, hrank]
  tfae_have 5 → 4 := by
    refine fun ⟨a, ⟨h, h1⟩⟩ ↦ ⟨a, ?_⟩
    let z := h.root
    refine ⟨z, (eq_of_monic_of_dvd_of_natDegree_le (monic (h_int z)) h1 (dvd_iff.mpr ?_) ?_).symm⟩
    · rw [h.aeval_root_eq_map, h.map_self]
    · simp [(ha a).1, (hprim z).mp (adjoin_eq_top_iff.mpr h.adjoin_root_eq_top), hrank]
  tfae_finish

/- This is the first step towards the Artin-Schreier-Witt construction.
-/
lemma irreducible_artinSchreierPoly_tower {a : F} {x : K} (hx : minpoly F x = artinSchreierPoly a)
    : Irreducible (artinSchreierPoly (algebraMap F F⟮x⟯ a *
      ⟨x, mem_adjoin_simple_self F x⟩ ^ (p - 1))) := by
  have hp := hp.elim
  have : ExpChar F⟮x⟯ p :=
    have : CharP F p := (expChar_prime_iff F hp).mp ‹ExpChar F p›
    have := (Algebra.charP_iff F F⟮x⟯ p).mp ‹CharP F p›
    expChar_prime F⟮x⟯ p
  by_contra h
  have splits := (artinSchreierPoly_irreducible_or_splits _).resolve_left h
  have h_a := artinSchreierPoly_isMonicOfDegree p a
  have hs :=
    have h_a1 := artinSchreierPoly_isMonicOfDegree p (algebraMap F F⟮x⟯ a *
      ⟨x, mem_adjoin_simple_self F x⟩ ^ (p - 1))
    (degree_eq_iff_natDegree_eq h_a1.ne_zero).mp.mt (h_a1.1.trans_ne hp.ne_zero)
  set y := rootOfSplits splits hs with hy
  have hp1 : 1 < (minpoly F x).natDegree := by simpa [h_a.1, hx] using hp.one_lt
  have h_int : IsIntegral F x := ne_zero_iff.mp (ne_zero_of_natDegree_gt hp1)
  obtain ⟨f, h_pb, hf⟩ := (adjoin.powerBasis h_int).exists_eq_aeval y
  absurd (irreducible h_int).not_isRoot_of_natDegree_ne_one hp1.ne' (x := f.coeff (p - 1))
  simp only [adjoin.powerBasis_dim, hx, h_a.1] at h_pb
  rw [artinSchreierPoly_def p] at hx
  let m := f.map (frobenius F p)
  have hd : m.natDegree = f.natDegree := natDegree_map _
  have h : m.taylor a = f + monomial (p - 1) a := by
    refine sub_eq_zero.mp (eq_zero_of_dvd_of_natDegree_lt (dvd _ x ?_) ?_)
    · have he : x ^ p = x + algebraMap F K a := by
        simpa [hx, sub_sub, sub_eq_zero] using minpoly.aeval F x
      rw [taylor_apply, aeval_sub, aeval_comp, _root_.map_add, _root_.map_add, aeval_X, aeval_C,
          aeval_monomial, ← he, ← expand_aeval, ← map_expand, map_frobenius_expand]
      have h := congr(algebraMap F⟮x⟯ K $(eval_rootOfSplits splits hs))
      rw [← hy] at h
      simpa [hf, artinSchreierPoly_def p, ← sub_add_eq_sub_sub] using h
    · compute_degree!
      simp [hx, hd, FiniteField.X_pow_card_sub_X_natDegree_eq F hp.one_lt, hp.pos, h_pb]
  have h1 : (m.taylor a).coeff (p - 1) = f.coeff (p - 1) ^ p := by
    by_cases h0 : f.natDegree = p - 1
    · rw [← h0, ← hd, coeff_taylor_natDegree, leadingCoeff_map, hd]; rfl
    · repeat rw [coeff_eq_zero_of_natDegree_lt]
      repeat grind only [zero_pow, (natDegree_taylor m a).trans hd]
  simp [hx, ← h1, h, coeff_add, coeff_monomial_same]
