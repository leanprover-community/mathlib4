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

variable {F : Type u} [CommRing F]

open IntermediateField Polynomial

noncomputable def artinSchreierPoly (a : F) : Polynomial F := X ^ ringExpChar F -  X - C a

lemma artinSchreierPoly.def (p : ℕ) [ExpChar F p] (a : F) :
    artinSchreierPoly a = X ^ p - X - C a := by simp [artinSchreierPoly, ringExpChar.eq F p]

@[simp]
lemma artinSchreierPoly.taylor (p : ℕ) [ExpChar F p] (a c : F) :
    (artinSchreierPoly a).taylor c = artinSchreierPoly (c - c ^ p + a) := by
  repeat rw [artinSchreierPoly.def p]
  rcases expChar_is_prime_or_one F p with hp | rfl
  · have := (expChar_prime_iff F hp).mp ‹ExpChar F p›
    simp [add_pow_expChar]; ring
  · simp

@[simp]
lemma artinSchreierPoly.isMonicOfDegree [Nontrivial F] {p} [ExpChar F p] (hp : 1 < p)
    (a : F) : (artinSchreierPoly a).IsMonicOfDegree p := by
  rw [artinSchreierPoly.def p]
  exact { natDegree_eq := by compute_degree <;> grind [one_ne_zero], monic := by monicity <;> grind}

variable {F : Type u} (p : ℕ) [Field F] [ExpChar F p]

open AdjoinRoot Multiset

lemma artinSchreierPoly.splits {a c : F} (hr : (artinSchreierPoly a).IsRoot c) :
    Splits (artinSchreierPoly a) := by
  let p := ringExpChar F
  have : ExpChar F p := ringExpChar.expChar F
  rcases expChar_is_prime_or_one F p with hp | hp1
  · simp only [artinSchreierPoly.def p, IsRoot.def, eval_sub, eval_pow, eval_X, eval_C] at hr
    ring_nf at hr
    rw [← Splits.taylor_iff c, artinSchreierPoly.taylor p,
      show c - c ^ p + a = 0 by grind, artinSchreierPoly.def p]
    have : CharP F p := (expChar_prime_iff F hp).mp ‹ExpChar F p›
    have := Fact.mk hp
    simpa [hr] using splits_X_pow_char_sub_X F p
  · simp [artinSchreierPoly.def p, hp1]

lemma artinSchreierPoly.irreducible [hp : Fact p.Prime]
    {a : F} (hr : (artinSchreierPoly a).roots = 0) :
    Irreducible (artinSchreierPoly a) := by
  have hmon := artinSchreierPoly.isMonicOfDegree hp.elim.one_lt a
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
      simp [artinSchreierPoly.def p]
    rw [h] at hm0 hdiv hc
    exact hb2.natDegree_dvd_finrank ((artinSchreierPoly.splits hc).of_dvd hm0 hdiv)
  have h3 := (((Nat.dvd_prime hp.elim).mp (h2.trans hmon.1.dvd)).resolve_left h1).symm
  exact (associated_of_dvd_of_natDegree_le hb3 h0 (hmon.1.trans h3).le).irreducible hb2

lemma artinSchreierPoly.irreducible_or_splits (a : F) :
    Irreducible (artinSchreierPoly a) ∨ Splits (artinSchreierPoly a) := by
  let p := ringExpChar F
  have : ExpChar F p := ringExpChar.expChar F
  rcases expChar_is_prime_or_one F p with hp | hp1
  · have := Fact.mk hp
    by_cases hr : (artinSchreierPoly a).roots = 0
    · left; exact artinSchreierPoly.irreducible p hr
    · right
      have ⟨_, hc⟩ := exists_mem_of_ne_zero hr
      simp only [mem_roots', ne_eq] at hc
      exact artinSchreierPoly.splits hc.2
  · right
    simp [artinSchreierPoly.def p, hp1]

variable {F : Type u} {K : Type u} {p : ℕ} [Field F] [ExpChar F p] [Field K] [Algebra F K]
  [hp : Fact p.Prime] (hrank : Module.finrank F K = p)

section Lemmas

include hrank in
open Finset IsGalois MulAction Subgroup Nat minpoly in
private
lemma isGalois_generator_of_charP [IsGalois F K] :
     ∃ a : F, ∃ z : K, minpoly F z = artinSchreierPoly a := by
  have := FiniteDimensional.of_finrank_pos (hrank.trans_gt hp.elim.pos)
  have : CharP F p := (expChar_prime_iff F hp.elim).mp ‹ExpChar F p›
  have := (Algebra.charP_iff F K p).mp ‹CharP F p›
  have h_ord := (card_aut_eq_finrank F K).trans hrank
  have ⟨g, h_gen⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (isCyclic_of_prime_card h_ord)
  let rp := Finset.range p
  obtain ⟨y, hy⟩ := Algebra.trace_surjective F K 1
  let z := ∑ i : rp, (g ^ (i : ℕ)) y * i
  have hz1 : ∑ i : rp, (g ^ (i + 1 : ℕ)) y * (i + 1) = z := by
    let f := fun (i : ℕ) ↦ (g ^ i) y * i
    have hp1 : p - 1 + 1 = p := succ_pred_prime hp.elim
    calc
    _ = ∑ i : rp, f (i + 1) := by simp [f]
    _ = ∑ i ∈ rp, f (i + 1) := (sum_subtype rp (fun _ ↦ Iff.of_eq rfl) fun i ↦ f (i + 1)).symm
    _ = ∑ i ∈ rp, f i := by subst rp f; rw [← hp1, sum_range_succ, sum_range_succ']; simp [hp1]
    _ = _ := sum_subtype rp (fun _ ↦ Iff.of_eq rfl) f
  have hz2 : ∑ i : rp, (g^(i + 1 : ℕ)) y = ∑ σ : Gal(K/F), σ y := by
    let f := fun (i : rp) ↦ g ^ (i + 1 : ℕ)
    refine sum_bijective f ?_ (by simp) fun _ _ ↦ rfl
    refine (Nat.bijective_iff_surjective_and_card f).mpr ⟨?_, ?_⟩
    · classical
      intro b
      have h := mem_top (g ^ (-1 : ℤ) * b)
      rw [← h_gen] at h
      have h0 := (isOfFinOrder_of_finite g).mem_zpowers_iff_mem_range_orderOf.mp h
      rw [(orderOf_eq_card_of_zpowers_eq_top h_gen).trans h_ord, mem_image] at h0
      obtain ⟨i, h1, h2⟩ := h0
      exact ⟨⟨i, h1⟩, (by simp [f, pow_succ' g, h2])⟩
    · rw [h_ord, card_eq_finsetCard rp, Finset.card_range p]
  have hgz : g z = z - 1 := calc
    _ = ∑ i : rp, g ((g ^ (i : ℕ)) y * i) := map_finsetSum _ _
    _ = ∑ i : rp, (g ^ (i + 1 : ℕ)) y * i := by simp [pow_succ' g]
    _ = ∑ i : rp, ((g ^ (i + 1 : ℕ)) y * (i + 1) - (g^(i + 1 : ℕ)) y) := by grind only
    _ = _ := by rw [sum_sub_distrib, hz1, hz2, ← trace_eq_sum_automorphisms, hy, map_one]
  have hz3 : z ∉ Set.range ⇑(algebraMap F K) := (mem_range_algebraMap_iff_fixed z).mp.mt (by grind)
  have h_int : IsIntegral F z := Algebra.IsIntegral.isIntegral z
  have ⟨a, _⟩ : z ^ p - z ∈ (⊥ : IntermediateField F K) := by
    refine (mem_bot_iff_fixed (z ^ p - z)).mpr fun γ ↦ ?_
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ((Subgroup.ext_iff.mp h_gen.symm γ).mp (mem_top _))
    rw [← AlgEquiv.smul_def, ← mem_fixedBy]
    apply mem_fixedBy_zpow (by simp [hgz, sub_pow_char])
  have hd := artinSchreierPoly.isMonicOfDegree hp.elim.one_lt a
  have h : (minpoly F z).natDegree ∣ p := (degree_dvd h_int).trans hrank.dvd
  have h := hd.1.trans ((hp.elim.dvd_iff_eq (natDegree_eq_one_iff.mp.mt hz3)).mp h)
  refine ⟨a, z, (eq_of_monic_of_dvd_of_natDegree_le (monic h_int) hd.2 (dvd _ _ ?_) h.le).symm⟩
  rw [artinSchreierPoly.def p]; aesop

end Lemmas

open Field minpoly

include hrank in
theorem isCyclic_charP_tfae :
    [IsGalois F K,
    ∃ a : F, Irreducible (artinSchreierPoly a) ∧ IsSplittingField F K (artinSchreierPoly a),
    ∃ α : K, α ^ p - α ∈ Set.range ⇑(algebraMap F K) ∧ F⟮α⟯ = ⊤,
    ∃ a : F, ∃ α : K, minpoly F α = artinSchreierPoly a,
    ∃ a : F, Nonempty (IsAdjoinRootMonic K (artinSchreierPoly a))].TFAE := by
  let := FiniteDimensional.of_finrank_pos (hp.elim.pos.trans_eq hrank.symm)
  have : CharP F p := (expChar_prime_iff F hp.elim).mp ‹ExpChar F p›
  have := (Algebra.charP_iff F K p).mp ‹CharP F p›
  have ha := fun (a : F) ↦ artinSchreierPoly.isMonicOfDegree hp.elim.one_lt a
  have h_int := fun (z : K) ↦ Algebra.IsIntegral.isIntegral z (R := F)
  have hprim := fun (z : K) ↦ primitive_element_iff_minpoly_natDegree_eq F z
  tfae_have 2 → 1 := by
    refine fun ⟨a, h1, _⟩ ↦ IsGalois.of_separable_splitting_field
      ((separable_iff_derivative_ne_zero h1).mpr ?_)
    simp [artinSchreierPoly.def p, derivative_pow]
  tfae_have 1 → 4 := fun _ ↦ isGalois_generator_of_charP hrank
  tfae_have 4 → 3 := by
    refine fun ⟨a, z, hz⟩ ↦ ⟨z, ⟨a, (sub_eq_zero.mp ?_).symm⟩, ?_⟩
    · have := aeval F z
      rw [hz, artinSchreierPoly.def p] at this
      simp_all only [aeval_sub, map_pow, aeval_X, aeval_C]
    · rw [hprim z, hz, hrank, (ha a).1]
  tfae_have 3 → 5 := by
    refine fun ⟨z, ⟨⟨a, h1⟩, htop⟩⟩ ↦ ⟨a, Nonempty.intro ?_⟩
    have h_eval : (aeval z) (artinSchreierPoly a) = 0 := by
      simp_all [artinSchreierPoly.def p]
    have hmin : artinSchreierPoly a = minpoly F z := by
      refine unique_of_degree_le_degree_minpoly F z (ha a).2 h_eval ?_
      rw [degree_eq_natDegree (ha a).ne_zero, (ha a).1,
        degree_eq_natDegree (ne_zero_iff.mpr (h_int z)), (hprim z).mp htop, hrank]
    rw [hmin]
    exact IsAdjoinRootMonic.mkOfPrimitiveElement (h_int z) htop
  tfae_have 5 → 2 := by
    refine fun ⟨a, ⟨h, hmon⟩⟩ ↦ ⟨a, ?_⟩
    set f := artinSchreierPoly a with hf
    let z := h.root
    have h_eval : (aeval z) f = 0 := by rw [h.aeval_root_eq_map, h.map_self]
    have htop : F⟮z⟯ = ⊤ := adjoin_eq_top_iff.mpr h.adjoin_root_eq_top
    have hpol : f = minpoly F z := by
      refine eq_of_monic_of_dvd_of_natDegree_le (monic (h_int z)) hmon (dvd_iff.mpr h_eval) ?_
      simp [hf, (ha a).1, ((hprim z).mp htop).trans hrank]
    let pol' := f.map (algebraMap F K)
    have splits : pol'.Splits := by
      rw [hf, artinSchreierPoly.def p] at h_eval
      simp only [← eval_map_algebraMap, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C,
        eval_sub, eval_pow, eval_X, eval_C] at h_eval
      subst pol'
      simp only [hf, artinSchreierPoly.def p, Polynomial.map_sub, Polynomial.map_pow, map_X,
        map_C]
      rw [← artinSchreierPoly.def]
      apply artinSchreierPoly.splits (c := z)
      simp [artinSchreierPoly.def p, h_eval]
    have adjoin : adjoin F (f.rootSet K) = ⊤ := by
      rw [eq_top_iff, ← htop, adjoin_simple_le_iff]
      exact mem_adjoin_of_mem F (hmon.mem_rootSet.mpr h_eval)
    refine ⟨(by rw [hpol]; exact irreducible (h_int z)), ?_⟩
    exact isSplittingField_iff_intermediateField.mpr ⟨splits, adjoin⟩
  tfae_finish

/- This is the first step towards the Artin-Schreier-Witt construction.
-/

include hrank in
lemma irreducible_artinSchreierPoly_tower {a : F} {x : K} (hx : minpoly F x = artinSchreierPoly a) :
    Irreducible (artinSchreierPoly ((algebraMap F K) a * x ^ (p-1))) := by
  have hp1 := hp.elim.one_lt
  have : CharP F p := (expChar_prime_iff F hp.elim).mp ‹ExpChar F p›
  let := (Algebra.charP_iff F K p).mp ‹CharP F p›
  have : ExpChar K p := expChar_prime K p
  by_contra h
  have h := (artinSchreierPoly.irreducible_or_splits _).resolve_left h
  have h_a := artinSchreierPoly.isMonicOfDegree hp1 a
  set f1 := artinSchreierPoly ((algebraMap F K) a * x ^ (p - 1)) with hf1
  have h_a1 : f1.IsMonicOfDegree p := artinSchreierPoly.isMonicOfDegree hp1 _
  have hs := (degree_eq_iff_natDegree_eq h_a1.ne_zero).mp.mt (h_a1.1.trans_ne hp.elim.ne_zero)
  rw [← h_a.1, ← hx] at hp1
  have := FiniteDimensional.of_finrank_pos (hp.elim.pos.trans_eq hrank.symm)
  have ht : F⟮x⟯ = ⊤ := by rw [primitive_element_iff_minpoly_natDegree_eq F x, hx, h_a.1, hrank]
  obtain ⟨y, hy⟩ : ∃ y : F⟮x⟯, y = rootOfSplits h hs := CanLift.prf _ (by rw [ht]; exact mem_top)
  have h_int : IsIntegral F x := ne_zero_iff.mp (ne_zero_of_natDegree_gt hp1)
  obtain ⟨f, h_pb, rfl⟩ := (adjoin.powerBasis h_int).exists_eq_aeval y
  simp only [adjoin.powerBasis_gen, AdjoinSimple.coe_aeval_gen_apply] at hy
  have : (f.coeff (p - 1)) ^ p = f.coeff (p - 1) + a := by
    let m := f.map (frobenius F p)
    have hd : m.natDegree = f.natDegree := natDegree_map (frobenius F p)
    have h : m.taylor a - (f + monomial (p - 1) a) = 0 := by
      refine eq_zero_of_dvd_of_natDegree_lt (dvd _ x ?_) ?_
      · have hy1 := eval_rootOfSplits h hs
        nth_rw 2 [hf1] at hy1
        simp only [artinSchreierPoly.def p, map_mul, map_pow, eval_sub, eval_pow, eval_X,
          eval_mul, eval_C] at hy1
        have he : x ^ p = x + algebraMap F K a := by
          rw [artinSchreierPoly.def p] at hx
          have : (aeval x) (minpoly F x) = 0 := minpoly.aeval F x
          simp_all only [natDegree_sub_C, adjoin_eq_top_iff, adjoin.powerBasis_dim, aeval_sub,
            map_pow, aeval_X, aeval_C]
          rw [sub_sub (x ^ p) x ((algebraMap F K) a)] at this
          rw [sub_eq_zero] at this
          exact this
        rw [taylor_apply, aeval_sub, aeval_comp, _root_.map_add, _root_.map_add, aeval_X, aeval_C,
            aeval_monomial, ← he, ← expand_aeval, ← map_expand, map_frobenius_expand, map_pow]
        grind
      · compute_degree!
        simp_all only [artinSchreierPoly.def p, natDegree_sub_C, map_mul, map_pow,
          adjoin_eq_top_iff, adjoin.powerBasis_dim, true_and]
        rw [FiniteField.X_pow_card_sub_X_natDegree_eq F hp.elim.one_lt]
        simp [hp.elim.pos]
    have h1 : (m.taylor a).coeff (p - 1) = (f.coeff (p - 1)) ^ p := by
      have h2 : ((taylor a) m).natDegree = f.natDegree := (natDegree_taylor m a).trans hd
      by_cases h0 : f.natDegree = p - 1
      · rw [← h0, ← leadingCoeff, ← h2, ← leadingCoeff, leadingCoeff_taylor, leadingCoeff_map]
        rfl
      · simp only [adjoin.powerBasis_dim, hx, h_a.1] at h_pb
        repeat rw [coeff_eq_zero_of_natDegree_lt]
        repeat grind only [zero_pow]
    rw [← h1, sub_eq_zero.mp h, coeff_add, coeff_monomial_same]
  absurd (irreducible h_int).not_isRoot_of_natDegree_ne_one hp1.ne' (x := f.coeff (p - 1))
  simp_all [artinSchreierPoly.def p]
