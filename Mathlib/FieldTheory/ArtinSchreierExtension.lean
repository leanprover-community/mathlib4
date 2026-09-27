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

@[expose] public section
universe u

open IntermediateField Polynomial

@[simp]
lemma artinSchreierPoly_isMonicOfDegree {F : Type u} [CommRing F] [Nontrivial F] (a : F)
    {p : ℕ} (hp : 1 < p) : (X ^ p - X - C a).IsMonicOfDegree p where
  natDegree_eq := by compute_degree <;> grind [one_ne_zero]
  monic := by monicity <;> grind

@[simp]
lemma artinSchreierPoly_taylor {F : Type u} [CommRing F] (a c : F) {p : ℕ}
    [CharP F p] [hp : Fact p.Prime] :
    (X ^ p - X - C a).taylor c = X ^ p - X + C (c ^ p - c - a) := by
  simp [add_pow_char]
  ring

variable {F : Type u} {K : Type u} {p : ℕ} [Field F] [Field K] [Algebra F K] [CharP F p]

open AdjoinRoot Multiset

lemma splits_artinSchreierPoly {a : F} {c : F} (hr : c ^ p - c - a = 0) :
    Splits (X ^ p - X - C a) := by
  rcases CharP.char_is_prime_or_zero F p with hp | rfl
  · have := Fact.mk hp
    have := Polynomial.splits_X_pow_char_sub_X F p
    have h : ((X ^ p - X - C a).taylor c).Splits := by simp_all
    exact (splits_iff_comp_splits_of_natDegree_eq_one (natDegree_X_add_C c)).mpr h
  · apply Splits.of_natDegree_le_one
    compute_degree

lemma irreducible_artinSchreierPoly {a : F} (hr : (X ^ p - X - C a).roots = 0) :
    Irreducible (X ^ p - X - C a) := by
  rcases CharP.char_is_prime_or_zero F p with hp | rfl
  · set f := X ^ p - X - C a with hf
    have hmon : f.IsMonicOfDegree p := artinSchreierPoly_isMonicOfDegree a hp.one_lt
    have h0 : f ≠ 0 := IsMonicOfDegree.ne_zero hmon
    have ⟨b, hb2, hb3⟩ := exists_irreducible_of_natDegree_pos (hp.pos.trans_eq hmon.1.symm)
    have h1 : b.natDegree ≠ 1 := by
      contrapose hr
      have ⟨x, hx⟩ := exists_root_of_natDegree_eq_one hr
      rw [eq_zero_iff_forall_notMem]
      push Not
      exact ⟨x, (mem_roots h0).mpr (hx.dvd hb3)⟩
    have h2 : b.natDegree ∣ f.natDegree := by
      refine dvd_natDegree_of_monic_of_irreducible _ fun c hc0 hc hc1 ↦ ?_
      have := Fact.mk hc
      let i := algebraMap F (AdjoinRoot c)
      have hm0 : f.map i ≠ 0 := map_ne_zero h0
      have hdiv : b.map i ∣ f.map i := map_dvd i hb3
      have hc : (f.map i).IsRoot (root c) := (isRoot_root _).dvd (map_dvd i (by aesop))
      rw [show f.map i = X ^ p - X - C (i a) by simp [hf]] at hm0 hdiv hc
      simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C] at hc
      have := (Algebra.charP_iff F (AdjoinRoot c) p).mp ‹CharP F p›
      rw [← (AdjoinRoot.isAdjoinRootMonic _ hc0).finrank]
      exact hb2.natDegree_dvd_finrank ((splits_artinSchreierPoly hc).of_dvd hm0 hdiv)
    have h3 := (((Nat.dvd_prime hp).mp (h2.trans hmon.1.dvd)).resolve_left h1).symm
    exact (associated_of_dvd_of_natDegree_le hb3 h0 (hmon.1.trans h3).le).irreducible hb2
  · apply irreducible_of_natDegree_eq_one
    compute_degree!

lemma artinSchreierPoly_irreducible_or_splits (a : F) :
    Irreducible (X ^ p - X - C a) ∨ Splits (X ^ p - X - C a) := by
  by_cases hr : (X ^ p - X - C a).roots = 0
  · left; exact irreducible_artinSchreierPoly hr
  · right
    have ⟨c, hc⟩ := exists_mem_of_ne_zero hr
    simp only [mem_roots', ne_eq, IsRoot.def, eval_sub, eval_pow, eval_X, eval_C] at hc
    exact splits_artinSchreierPoly hc.2

section Lemmas

private
lemma cyclic_charP_as_param [IsGalois F K] [hp : Fact p.Prime] (hrank : Module.finrank F K = p) :
    ∃ a : F, ∃ z : K, minpoly F z = X ^ p - X - C a := by
  open Finset IsGalois MulAction Subgroup Nat minpoly in
  have := FiniteDimensional.of_finrank_pos (hrank.trans_gt hp.elim.pos)
  have := (Algebra.charP_iff F K p).mp ‹CharP F p›
  have h_ord := (card_aut_eq_finrank F K).trans hrank
  have ⟨g, h_gen⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (isCyclic_of_prime_card h_ord)
  let rp := Finset.range p
  have ⟨y, hy⟩ := Algebra.trace_surjective F K 1
  let z := ∑ i : rp, (g^(i:ℕ)) y * i
  have hz1 : ∑ i : rp, (g^(i+1:ℕ)) y * (i+1) = z :=
    let f := fun (i : ℕ) ↦ (g^i) y * i
    have hp1 : p-1+1 = p := succ_pred_prime hp.elim
    calc
    _ = ∑ i : rp, f (i+1) := by simp [f]
    _ = ∑ i ∈ rp, f (i+1) := (sum_subtype rp (fun _ ↦ Iff.of_eq rfl) (fun i ↦ f (i+1))).symm
    _ = ∑ i ∈ rp, f i := by subst rp f; rw [← hp1, sum_range_succ, sum_range_succ']; simp [hp1]
    _ = _ := sum_subtype rp (fun _ ↦ Iff.of_eq rfl) f
  have hz2 : ∑ i : rp, (g^(i+1:ℕ)) y = ∑ σ : Gal(K/F), σ y := by
    let f := fun (i : rp) ↦ g ^ (i+1:ℕ)
    refine sum_bijective f ?_ (by simp) (fun _ _ ↦ rfl)
    refine (Nat.bijective_iff_surjective_and_card f).mpr ⟨?_, ?_⟩
    · classical
      intro b
      have h := mem_top (g ^ (-1:ℤ) * b)
      rw [← h_gen] at h
      have h := (isOfFinOrder_of_finite g).mem_zpowers_iff_mem_range_orderOf.mp h
      rw [(orderOf_eq_card_of_zpowers_eq_top h_gen).trans h_ord, mem_image] at h
      obtain ⟨i, h1, h2⟩ := h
      exact ⟨⟨i, h1⟩, (by simp [f, pow_succ' g, h2])⟩
    · rw [h_ord, card_eq_finsetCard rp, Finset.card_range p]
  have hgz : g z = z - 1 := calc
    _ = ∑ i : rp, g ((g^(i:ℕ)) y * i) := map_finsetSum _ _
    _ = ∑ i : rp, (g^(i+1:ℕ)) y * i := by simp [pow_succ' g]
    _ = ∑ i : rp, ((g^(i+1:ℕ)) y * (i+1) - (g^(i+1:ℕ)) y) := by grind only
    _ = _ := by rw [sum_sub_distrib, hz1, hz2, ← trace_eq_sum_automorphisms, hy, map_one]
  have h_int : IsIntegral F z := Algebra.IsIntegral.isIntegral z
  have ⟨a, _⟩ : z ^ p - z ∈ (⊥ : IntermediateField F K) := by
    apply (mem_bot_iff_fixed (z ^ p - z)).mpr
    intro γ
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ((Subgroup.ext_iff.mp h_gen.symm γ).mp (mem_top _))
    rw [← AlgEquiv.smul_def, ← mem_stabilizerSubmonoid_iff]
    apply fixedBy_subset_fixedBy_zpow
    simp [hgz, sub_pow_char]
  have hd := artinSchreierPoly_isMonicOfDegree a hp.elim.one_lt
  have hz3 := (mem_range_algebraMap_iff_fixed z (F := F)).mp.mt (by grind only)
  have h := (degree_dvd h_int).trans hrank.dvd
  have h := hd.1.trans ((hp.elim.dvd_iff_eq (natDegree_eq_one_iff.mp.mt hz3)).mp h)
  refine ⟨a, z, (eq_of_monic_of_dvd_of_natDegree_le (monic h_int) hd.2 ?_ h.le).symm⟩
  exact (dvd _ _ (by aesop))

end Lemmas

open Field minpoly

theorem isCyclic_charP_tfae [hp : Fact p.Prime] (hrank : Module.finrank F K = p) :
    [IsGalois F K,
    ∃ a : F, Irreducible (X ^ p - X - C a) ∧ IsSplittingField F K (X ^ p - X - C a),
    ∃ α : K, α ^ p - α ∈ Set.range ⇑(algebraMap F K) ∧ F⟮α⟯ = ⊤,
    ∃ a : F, ∃ α : K, minpoly F α = X ^ p - X - C a,
    ∃ a : F, Nonempty (IsAdjoinRootMonic K (X ^ p - X - C a))].TFAE := by
  open IntermediateField IsGalois in
  let := FiniteDimensional.of_finrank_pos (hp.elim.pos.trans_eq hrank.symm)
  have := (Algebra.charP_iff F K p).mp ‹CharP F p›
  let ha := fun (a : F) ↦ artinSchreierPoly_isMonicOfDegree a hp.elim.one_lt
  have h_int : ∀ z : K, IsIntegral F z := Algebra.IsIntegral.isIntegral
  tfae_have 2 → 1 := fun ⟨a, h1, _⟩ ↦ of_separable_splitting_field
    ((separable_iff_derivative_ne_zero h1).mpr (by simp [@derivative_X_pow]))
  tfae_have 1 → 4 := fun _ ↦ cyclic_charP_as_param hrank
  tfae_have 4 → 3 := by
    refine fun ⟨a, z, hz⟩ ↦ ⟨z, ⟨a, (sub_eq_zero.mp ?_).symm⟩, ?_⟩
    · have := aeval F z
      simp_all only [aeval_sub, map_pow, aeval_X, aeval_C]
    · apply (primitive_element_iff_minpoly_natDegree_eq F z).mpr
      rw [hz, hrank, (ha a).1]
  tfae_have 3 → 5 := by
    refine fun ⟨z, ⟨⟨a, h1⟩, h2⟩⟩ ↦ ⟨a, Nonempty.intro ?_⟩
    have h_eval : (aeval z) (X ^ p - X - C a) = 0 := by simp_all
    have hmin : X ^ p - X - C a = minpoly F z := by
      refine unique_of_degree_le_degree_minpoly F z (ha a).2 h_eval ?_
      rw [(primitive_element_iff_minpoly_degree_eq F z).mp h2, hrank,
          degree_eq_natDegree (ha a).2.ne_zero, (ha a).1]
    rw [hmin]
    exact IsAdjoinRootMonic.mkOfPrimitiveElement (h_int z) h2
  tfae_have 5 → 2 := by
    refine fun ⟨a, ⟨h, hmon⟩⟩ ↦ ⟨a, ?_⟩
    set f := X ^ p - X - C a with hf
    let z := h.map X
    have h_eval : f.aeval z = 0 := by aesop
    have h2 : F⟮z⟯ = ⊤ := adjoin_eq_top_iff.mpr (IsAdjoinRoot.adjoin_root_eq_top h)
    have hpol : f = minpoly F z := by
      have h_div : minpoly F z ∣ f := dvd_iff.mpr h_eval
      have h := ((primitive_element_iff_minpoly_natDegree_eq F z).mp h2).trans hrank
      refine eq_of_monic_of_dvd_of_natDegree_le (monic (h_int z)) (ha a).2 h_div ?_
      simp [hf, (ha a).1, h]
    let pol' := f.map (algebraMap F K)
    have splits : pol'.Splits := by
      rw [show pol' = X ^ p - X - C (algebraMap F K a) by simp [pol', hf]]
      simp only [hf, aeval_sub, map_pow, aeval_X, aeval_C] at h_eval
      exact splits_artinSchreierPoly h_eval
    have adjoin : adjoin F (f.rootSet K) = ⊤ := by
      have := adjoin_simple_le_iff.mpr (mem_adjoin_of_mem F ((ha a).2.mem_rootSet.mpr h_eval))
      rw [h2] at this
      aesop
    refine ⟨(by rw [hpol]; exact irreducible (h_int z)), ?_⟩
    exact isSplittingField_iff_intermediateField.mpr ⟨splits, adjoin⟩
  tfae_finish

/- This is the first step towards the Artin-Schreier-Witt construction.
-/

lemma irreducible_artinSchreierPoly_tower [hp : Fact p.Prime] (hrank : Module.finrank F K = p)
    {a : F} {x : K} (hx : minpoly F x = X ^ p - X - C a) :
    Irreducible (X ^ p - X - C ((algebraMap F K) a * x ^ (p-1))) := by
  have hp1 := hp.elim.one_lt
  let := (Algebra.charP_iff F K p).mp ‹CharP F p›
  by_contra h
  have h := (artinSchreierPoly_irreducible_or_splits _).resolve_left h
  have h_a {E} [Field E] (x : E) := artinSchreierPoly_isMonicOfDegree x hp1
  set f1 := X ^ p - X - C ((algebraMap F K) a * x ^ (p-1)) with hf1
  have h_a1 : f1.IsMonicOfDegree p := h_a (algebraMap F K a * x ^ (p-1))
  have hs := (degree_eq_iff_natDegree_eq h_a1.ne_zero).mp.mt (h_a1.1.trans_ne hp.elim.ne_zero)
  have h_d := (h_a a).1
  rw [← h_d, ← hx] at hp1
  have := FiniteDimensional.of_finrank_pos (hp.elim.pos.trans_eq hrank.symm)
  have ht := (primitive_element_iff_minpoly_natDegree_eq F x).mpr (by rw [hx, hrank]; exact h_d)
  obtain ⟨y, hy⟩ : ∃ y : F⟮x⟯, y = rootOfSplits h hs := CanLift.prf _ (by rw [ht]; exact mem_top)
  have h_int : IsIntegral F x := ne_zero_iff.mp (ne_zero_of_natDegree_gt hp1)
  obtain ⟨f, h_pb, rfl⟩ := (adjoin.powerBasis h_int).exists_eq_aeval y
  simp only [adjoin.powerBasis_gen, AdjoinSimple.coe_aeval_gen_apply] at hy
  have : (f.coeff (p-1)) ^ p = f.coeff (p-1) + a := by
    let m := f.map (frobenius F p)
    have hd : m.natDegree = f.natDegree := natDegree_map (frobenius F p)
    have h : m.taylor a - (f + monomial (p-1) a) = 0 := by
      refine eq_zero_of_dvd_of_natDegree_lt (dvd _ x ?_) ?_
      · have he : x ^ p = x + algebraMap F K a := by grind [aeval F x, aeval_sub, aeval_X, aeval_C]
        rw [taylor_apply, aeval_sub, aeval_comp, _root_.map_add, _root_.map_add, aeval_X, aeval_C,
            aeval_monomial, ← he, ← expand_aeval, ← map_expand, map_frobenius_expand, map_pow]
        have hy := eval_rootOfSplits h hs
        simp only [hf1, eval_sub, eval_pow, eval_X, eval_C] at hy
        grind
      · compute_degree!
        simp_all [hp.elim.pos]
    have h1 : (m.taylor a).coeff (p-1) = (f.coeff (p-1)) ^ p := by
      have h2 := (natDegree_taylor m a).trans hd
      by_cases h0 : f.natDegree = p-1
      · rw [← h0, ← leadingCoeff, ← h2, ← leadingCoeff, leadingCoeff_taylor, leadingCoeff_map]
        rfl
      · simp only [adjoin.powerBasis_dim, hx, h_d] at h_pb
        repeat rw [coeff_eq_zero_of_natDegree_lt]
        repeat grind only [zero_pow]
    rw [← h1, sub_eq_zero.mp h, coeff_add, coeff_monomial_same]
  absurd (irreducible h_int).not_isRoot_of_natDegree_ne_one hp1.ne' (x := f.coeff (p-1))
  simp_all
