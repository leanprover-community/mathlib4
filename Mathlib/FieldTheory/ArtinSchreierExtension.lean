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
of `K` whose Galois group is cyclic of order `p`.

TODO: extend to finite extensions whose Galois group is cyclic of order `p^n` (Artin-Schreier-Witt
theory).

-/

@[expose] public section
universe u

open IntermediateField Polynomial

@[simp]
lemma artinSchreierPoly_isMonicOfDegree {F : Type u} [CommRing F] [Nontrivial F] (a : F)
    {p : ℕ} (hp : 1 < p) : (X ^ p - X - C a).IsMonicOfDegree p := by
  rw [←sub_add_eq_sub_sub]
  exact (isMonicOfDegree_X_pow F p).sub ((natDegree_X_add_C a).trans_lt hp)

@[simp]
lemma artinSchreierPoly_taylor {F : Type u} [CommRing F] (a c : F) {p : ℕ}
    [CharP F p] (hp : p.Prime) :
    (X ^ p - X - C a).taylor c = X^p - X + C (c^p - c - a) := by
  have := fact_iff.mpr hp
  simp only [map_sub, taylor_pow, taylor_X, add_pow_char, taylor_C, map_pow]
  ring

variable {F : Type u} {K : Type u} {p : ℕ} [Field F] [Field K] [Algebra F K] [CharP F p]

lemma artinSchreierPoly_splits (a : F) (hr : (X ^ p - X - C a).roots ≠ 0) :
    Splits (X ^ p - X - C a) := by
  rcases CharP.char_is_prime_or_zero F p with hp | rfl
  · have := fact_iff.mpr hp
    have ⟨c, _⟩ := Multiset.exists_mem_of_ne_zero hr
    have := (Subfield.splits_bot F p).map (algebraMap _ F)
    have h : ((X ^ p - X - C a).taylor c).Splits := by simp_all
    exact (splits_iff_comp_splits_of_natDegree_eq_one (natDegree_X_add_C c)).mpr h
  · apply Splits.of_natDegree_le_one
    compute_degree

lemma artinSchreierPoly_irreducible (a : F) (hr : (X ^ p - X - C a).roots = 0) :
    Irreducible (X ^ p - X - C a) := by
  open AdjoinRoot Multiset in
  rcases CharP.char_is_prime_or_zero F p with hp | rfl
  · have hmon := artinSchreierPoly_isMonicOfDegree a hp.one_lt
    have h0 := IsMonicOfDegree.ne_zero hmon
    have ⟨b, hb2, hb3⟩ := exists_irreducible_of_natDegree_pos (hp.pos.trans_eq hmon.1.symm)
    have h1 : b.natDegree ≠ 1 := by
      contrapose hr
      have ⟨x, hx⟩ := exists_root_of_natDegree_eq_one hr
      apply eq_zero_iff_forall_notMem.mp.mt
      push Not
      exact ⟨x, (mem_roots h0).mpr (hx.dvd hb3)⟩
    have h2 : b.natDegree ∣ (X ^ p - X - C a).natDegree := by
      refine dvd_natDegree_of_monic_of_irreducible _ fun c hc0 hc hc1 ↦ ?_
      have := fact_iff.mpr hc
      let i := algebraMap F (AdjoinRoot c)
      have hmap : (X ^ p - X - C a).map i = X^p - X - C (i a) := by aesop
      have hm0 := map_ne_zero (f := i) h0
      have hdiv := map_dvd i hb3
      have := (isRoot_root _).dvd (map_dvd i (y := X ^ p - X - C a) (by aesop))
      have h : ((X ^ p - X - C a).map i).roots ≠ 0 := eq_zero_iff_forall_notMem.mp.mt (by aesop)
      rw [hmap] at hm0 hdiv h
      have := (Algebra.charP_iff F (AdjoinRoot c) p).mp ‹CharP F p›
      rw [←(AdjoinRoot.isAdjoinRootMonic _ hc0).finrank]
      exact hb2.natDegree_dvd_finrank ((artinSchreierPoly_splits _ h).of_dvd hm0 hdiv)
    have h3 := (((Nat.dvd_prime hp).mp (h2.trans hmon.1.dvd)).resolve_left h1).symm
    exact (associated_of_dvd_of_natDegree_le hb3 h0 (hmon.1.trans h3).le).irreducible hb2
  · apply irreducible_of_natDegree_eq_one
    compute_degree!

lemma artinSchreierPoly_irreducible_or_splits (a : F) :
    Irreducible (X ^ p - X - C a) ∨ Splits (X ^ p - X - C a) := by
  by_cases hr : (X ^ p - X - C a).roots = 0
  · left; exact artinSchreierPoly_irreducible a hr
  · right; exact artinSchreierPoly_splits a hr

section Lemmas

private
lemma cyclic_charP_as_param [IsGalois F K] (hp : p.Prime) (hrank : Module.finrank F K = p) :
    ∃ a : F, ∃ z : K, minpoly F z = X ^ p - X - C a := by
  open Algebra FiniteDimensional Finset IsGalois MulAction Subgroup Nat minpoly in
  have := of_finrank_pos (hrank.trans_gt hp.pos)
  have h_ord := (card_aut_eq_finrank F K).trans hrank
  have := fact_iff.mpr hp
  have ⟨g, h_gen⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (isCyclic_of_prime_card h_ord)
  have h_ordg := (orderOf_eq_card_of_zpowers_eq_top h_gen).trans h_ord
  let rp := range p
  have ⟨y, hy⟩ := trace_surjective F K 1
  let z := ∑ i : rp, (g^(i:ℕ)) y * i
  have := (Algebra.charP_iff F K p).mp ‹CharP F p›
  have hz1 : ∑ i : rp, (g^(i+1:ℕ)) y * (i+1) = z :=
    let f := fun (i : ℕ) ↦ (g^i) y * i
    have hp1 : p-1+1 = p := succ_pred_prime hp
    calc
    _ = ∑ i : rp, f (i+1) := by simp [f]
    _ = ∑ i ∈ rp, f (i+1) := (sum_subtype rp (fun _ ↦ Iff.of_eq rfl) (fun i ↦ f (i+1))).symm
    _ = ∑ i ∈ rp, f i := by subst rp f; rw [←hp1, sum_range_succ, sum_range_succ']; simp [hp1]
    _ = _ := sum_subtype rp (fun _ ↦ Iff.of_eq rfl) f
  have hz2 : ∑ i : rp, (g^(i+1:ℕ)) y = ∑ σ : Gal(K/F), σ y := by
    let f := fun (i : rp) ↦ g ^ (i+1:ℕ)
    refine sum_bijective f ?_ (by simp) (fun _ _ ↦ rfl)
    refine (Nat.bijective_iff_surjective_and_card f).mpr ⟨?_, ?_⟩
    · intro b
      have h := mem_top (g ^ (-1:ℤ) * b)
      rw [←h_gen] at h
      have := Classical.typeDecidableEq Gal(K/F)
      have h := (isOfFinOrder_of_finite g).mem_zpowers_iff_mem_range_orderOf.mp h
      rw [h_ordg, mem_image] at h
      have ⟨i, h1, h2⟩ := h
      exact ⟨⟨i, h1⟩, (by simp [f, pow_succ' g, h2])⟩
    · rw [h_ord, card_eq_finsetCard rp, card_range p]
  have hgz : g z = z - 1 := calc
    _ = ∑ i : rp, g ((g^(i:ℕ)) y * i) := map_finsetSum _ _
    _ = ∑ i : rp, (g^(i+1:ℕ)) y * i := by simp [pow_succ' g]
    _ = ∑ i : rp, ((g^(i+1:ℕ)) y * (i+1) - (g^(i+1:ℕ)) y) := by grind only
    _ = _ := by rw [sum_sub_distrib, hz1, hz2, ←trace_eq_sum_automorphisms, hy, map_one]
  have h_int := IsIntegral.isIntegral z (R := F)
  have ⟨a, _⟩ : z^p - z ∈ (⊥ : IntermediateField F K) := by
    apply (mem_bot_iff_fixed (z^p - z)).mpr
    intro γ
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ((Subgroup.ext_iff.mp h_gen.symm γ).mp (mem_top _))
    rw [←AlgEquiv.smul_def, ←mem_stabilizerSubmonoid_iff]
    apply fixedBy_subset_fixedBy_zpow
    simp [hgz, sub_pow_char]
  have hd := artinSchreierPoly_isMonicOfDegree a hp.one_lt
  have hz3 := (mem_range_algebraMap_iff_fixed z (F := F)).mp.mt (by grind only)
  have h := (degree_dvd h_int).trans hrank.dvd
  have h := hd.1.trans ((hp.dvd_iff_eq (natDegree_eq_one_iff.mp.mt hz3)).mp h)
  refine ⟨a, z, (eq_of_monic_of_dvd_of_natDegree_le (monic h_int) hd.2 ?_ h.le).symm⟩
  exact (dvd _ _ (by aesop))

lemma cyclic_charP_splitting (hp : p.Prime) (hrank : Module.finrank F K = p)
    (h : ∃ α : K, α ^ p - α ∈ Set.range ⇑(algebraMap F K) ∧ F⟮α⟯ = ⊤) :
    ∃ a : F, Irreducible (X ^ p - X - C a) ∧ IsSplittingField F K (X ^ p - X - C a) := by
  open Field FiniteDimensional Function minpoly in
  obtain ⟨z, ⟨a, h1⟩, h2⟩ := h
  have := of_finrank_pos (hp.pos.trans_eq hrank.symm)
  have hd := artinSchreierPoly_isMonicOfDegree a hp.one_lt
  have h_eval : (X ^ p - X - C a).aeval z = 0 := by aesop
  have h_div : minpoly F z ∣ X ^ p - X - C a := dvd_iff.mpr h_eval
  have h := ((primitive_element_iff_minpoly_natDegree_eq F z).mp h2).trans hrank
  have h_int := Algebra.IsIntegral.isIntegral z (R := F)
  have hpol := eq_of_monic_of_dvd_of_natDegree_le (monic h_int) hd.2 h_div (by simp [hd.1, h])
  refine ⟨a, ⟨(by rw [hpol]; exact irreducible h_int), ?_⟩⟩
  have adjoin : adjoin F ((X ^ p - X - C a).rootSet K) = ⊤ := by
    have := adjoin_simple_le_iff.mpr (mem_adjoin_of_mem F (hd.2.mem_rootSet.mpr h_eval))
    rw [h2] at this
    simp_all
  let pol' := (X ^ p - X - C a).map (algebraMap F K)
  have splits : pol'.Splits := by
    have hi : pol' = X ^ p - X - C ((algebraMap F K) a) := by aesop
    have h : pol' ≠ 0 := map_monic_ne_zero hd.2
    have hr := (roots_eq_zero_iff_isRoot_eq_bot h).mp.mt (ne_iff.mpr ⟨z, (by aesop)⟩)
    rw [hi] at hr ⊢
    have := (Algebra.charP_iff F K p).mp inferInstance
    exact artinSchreierPoly_splits _ hr
  exact isSplittingField_iff_intermediateField.mpr ⟨splits, adjoin⟩

end Lemmas

theorem isCyclic_charP_tfae (hp : p.Prime) (hrank : Module.finrank F K = p) :
    [IsGalois F K,
    IsGalois F K ∧ IsCyclic Gal(K/F),
    ∃ a : F, Irreducible (X ^ p - X - C a) ∧ IsSplittingField F K (X ^ p - X - C a),
    ∃ α : K, α ^ p - α ∈ Set.range ⇑(algebraMap F K) ∧ F⟮α⟯ = ⊤,
    ∃ a : F, ∃ α : K, minpoly F α = X ^ p - X - C a].TFAE := by
  open Field FiniteDimensional FiniteField IsGalois minpoly in
  have := fact_iff.mpr hp
  have := of_finrank_pos (hp.pos.trans_eq hrank.symm)
  tfae_have 2 → 5 := fun ⟨_, _⟩ ↦ cyclic_charP_as_param hp hrank
  tfae_have 5 → 4 := by
    refine fun ⟨a, z, hz⟩ ↦ ⟨z, ⟨a, (sub_eq_zero.mp ?_).symm⟩, ?_⟩
    · have := aeval F z
      simp_all only [aeval_sub, map_pow, aeval_X, aeval_C]
    · apply (primitive_element_iff_minpoly_natDegree_eq F z).mpr
      rw [hz, hrank]
      exact (artinSchreierPoly_isMonicOfDegree a hp.one_lt).1
  tfae_have 4 → 3 := fun h ↦ cyclic_charP_splitting hp hrank h
  tfae_have 3 → 1 := fun ⟨a, h1, _⟩ ↦ of_separable_splitting_field
    ((separable_iff_derivative_ne_zero h1).mpr (by simp [@derivative_X_pow]))
  tfae_have 1 → 2 := fun h ↦ ⟨h, isCyclic_of_card_dvd_prime
    ((card_aut_eq_finrank F K).trans hrank).dvd⟩
  tfae_finish

lemma irreducible_artinSchreierPoly_tower (hp : p.Prime) (hrank : Module.finrank F K = p)
    (a : F) (x : K) (hx : minpoly F x = X ^ p - X - C a) :
    Irreducible (X^p - X - C ((algebraMap F K) a * x ^ (p-1))) := by
  open Field FiniteDimensional minpoly in
  by_contra h
  have hp1 := hp.one_lt
  have := (Algebra.charP_iff F K p).mp ‹CharP F p›
  have h := (artinSchreierPoly_irreducible_or_splits _).resolve_left h
  have h_a {E} [Field E] (x : E) := artinSchreierPoly_isMonicOfDegree x hp1
  have h_a1 := h_a ((algebraMap F K) a * x ^ (p-1))
  have hs := (degree_eq_iff_natDegree_eq h_a1.ne_zero).mp.mt (h_a1.1.trans_ne hp.ne_zero)
  have hy := eval_rootOfSplits h hs
  simp only [eval_sub, eval_pow, eval_X, eval_C] at hy
  have h_d := (h_a a).1
  rw [←h_d, ←hx] at hp1
  have := of_finrank_pos (hp.pos.trans_eq hrank.symm)
  have ht := (primitive_element_iff_minpoly_natDegree_eq F x).mpr (by rw [hx, hrank]; exact h_d)
  obtain ⟨y, _⟩ : ∃ y : F⟮x⟯, y = rootOfSplits h hs := CanLift.prf _ (by rw [ht]; exact mem_top)
  have h_int := ne_zero_iff.mp (ne_zero_of_natDegree_gt hp1)
  obtain ⟨f, h_pb, rfl⟩ := (adjoin.powerBasis h_int).exists_eq_aeval y
  simp only [adjoin.powerBasis_gen, AdjoinSimple.coe_aeval_gen_apply] at *
  have : (f.coeff (p-1)) ^ p = f.coeff (p-1) + a := by
    have := fact_iff.mpr hp
    let m := f.map (frobenius F p)
    have hd : m.natDegree = f.natDegree := natDegree_map (frobenius F p)
    have h : m.taylor a - (f + monomial (p-1) a) = 0 := by
      refine eq_zero_of_dvd_of_natDegree_lt (dvd _ x ?_) ?_
      · have he : x ^ p = x + (algebraMap F K) a := by
          have := aeval F x
          simp_all only [map_pow, aeval_sub, aeval_X, aeval_C]
          grind
        simp only [taylor_apply, aeval_sub, aeval_comp, map_add, aeval_X, aeval_C, aeval_monomial]
        rw [←he, ←expand_aeval, ←map_expand, map_frobenius_expand, map_pow]
        grind
      · compute_degree!
        simp_all [hp.pos]
    have h1 : (m.taylor a).coeff (p-1) = (f.coeff (p-1)) ^ p := by
      have h2 := (natDegree_taylor m a).trans hd
      by_cases h0 : f.natDegree = p-1
      · rw [←h0, ←leadingCoeff, ←h2, ←leadingCoeff, leadingCoeff_taylor, leadingCoeff_map]
        rfl
      · simp only [adjoin.powerBasis_dim, hx, h_d] at h_pb
        repeat rw [coeff_eq_zero_of_natDegree_lt]
        repeat grind only [zero_pow]
    rw [←h1, sub_eq_zero.mp h, coeff_add, coeff_monomial_same]
  absurd (irreducible h_int).not_isRoot_of_natDegree_ne_one hp1.ne' (x := f.coeff (p-1))
  simp_all
