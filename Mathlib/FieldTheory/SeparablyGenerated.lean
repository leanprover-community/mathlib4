/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Order.Ring.Finset
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!

# Separably generated extensions

We aim to formalize the following result:

Let `K/k` be a finitely generated field extension with characteristic `p > 0`, then TFAE
1. `K/k` is separably generated
2. If `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
  `{ sᵢᵖ } ⊆ K` is also `k`-linearly independent
3. `K ⊗ₖ k^{1/p}` is reduced
4. `K` is geometrically reduced over `k`.
5. `k ⊗_{kᵖ} Kᵖ` is linearly disjoint in `K`.

## Main result
- `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow`: (2) => (1)

-/

noncomputable section

section

attribute [local instance 2000] Polynomial.isScalarTower Algebra.toSMul IsScalarTower.right

open MvPolynomial
open scoped IntermediateField

variable {k K ι : Type*} [Field k] [Field K] [Algebra k K] (p : ℕ) [ExpChar k p] (hp : p.Prime)
variable (a : ι → K) (n : ι) (ha : IntermediateField.adjoin k (Set.range a) = ⊤)
variable (ha' : IsTranscendenceBasis k fun i : {i // i ≠ n} ↦ a i)
variable (H : ∀ s : Finset K,
  LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (· ^ p) (s : Set K))

section

variable (F : MvPolynomial ι k) (hF0 : F ≠ 0) (hFa : F.aeval a = 0)
variable (HF : ∀ (F' : MvPolynomial ι k), F' ≠ 0 → F'.aeval a = 0 → F.totalDegree ≤ F'.totalDegree)

include hF0 hFa HF in
theorem irreducible_of_forall_aeval_eq_zero_totalDegree_le :
    Irreducible F := by
  refine ⟨fun h' ↦ (h'.map (aeval a)).ne_zero hFa, fun q₁ q₂ e ↦ ?_⟩
  by_contra! hq₁q₂
  wlog hq₁ : aeval a q₁ = 0 generalizing q₁ q₂
  · refine this q₂ q₁ (e.trans (mul_comm _ _)) hq₁q₂.symm ?_
    simpa only [map_mul, @eq_comm K 0, hFa, mul_eq_zero, or_iff_right hq₁] using congr(aeval a $e)
  subst e
  simp only [ne_eq, mul_eq_zero, not_or] at hF0
  have := HF q₁ hF0.1 hq₁
  rw [MvPolynomial.totalDegree_mul_of_isDomain hF0.1 hF0.2,
    add_le_iff_nonpos_right, nonpos_iff_eq_zero] at this
  apply hF0.2
  rw [totalDegree_eq_zero_iff_eq_C.mp this]
  convert C.map_zero
  simpa [this] using isUnit_iff_totalDegree_of_isReduced.not.mp hq₁q₂.2

include HF in
theorem coeff_eval_ite_ne_zero_of_forall_aeval_eq_zero_totalDegree_le [DecidableEq ι] (i : ι)
    (n : ℕ) (hn0 : n ≠ 0) (hn : ∃ σ ∈ F.support, σ i = n) :
    (F.aeval fun j ↦ if j = i then Polynomial.X else .C (a j)).coeff n ≠ 0 := by
  intro H
  let Fi := optionEquivLeft k _ (renameEquiv k (Equiv.optionSubtypeNe i).symm F)
  obtain ⟨σ, hσ, hσi⟩ := hn
  have H := HF (rename (↑) (Fi.coeff n)) ?_ ?_
  · have : (Fi.coeff _).totalDegree + n ≤ _ :=
      totalDegree_coeff_optionEquivLeft_add_le _ _ (renameEquiv k _ F) n (by
        rw [totalDegree_renameEquiv, ← hσi]
        exact le_trans (Finset.single_le_sum (by simp) (by simpa [hσi])) (le_totalDegree hσ))
    rw [totalDegree_renameEquiv] at this
    simpa [hn0] using (this.trans H).trans (totalDegree_rename_le _ _)
  · refine (map_eq_zero_iff _ (rename_injective _ Subtype.val_injective)).not.mpr fun H ↦ ?_
    have : coeff _ (Fi.coeff _) = _ :=
      optionEquivLeft_coeff_coeff _ _ (σ.equivMapDomain (Equiv.optionSubtypeNe i).symm)
        (renameEquiv k (Equiv.optionSubtypeNe i).symm F)
    rw [renameEquiv_apply, Finsupp.equivMapDomain_eq_mapDomain,
      coeff_rename_mapDomain _ (Equiv.optionSubtypeNe i).symm.injective,
      Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Equiv.optionSubtypeNe_none, hσi,
      H, coeff_zero, eq_comm, ← notMem_support_iff] at this
    exact this hσ
  · refine .trans ?_ H
    trans (Polynomial.mapAlgHom (MvPolynomial.aeval (a ·.1)) Fi).coeff n
    · simp [aeval_rename, Function.comp_def]
    · congr 1
      show ((Polynomial.mapAlgHom _).comp ((optionEquivLeft k _).toAlgHom.comp (rename _))) F = _
      congr 1
      ext : 1
      aesop (add simp optionEquivLeft_X_some) (add simp optionEquivLeft_X_none)

end

include hp ha' H in
omit [ExpChar k p] in
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin_eq_top_aux :
    ∃ (i : ι) (F : Polynomial (MvPolynomial { j // j ≠ i } k)),
      letI F' := F.mapAlgHom (B := K) (aeval fun j ↦ a j.1)
      Irreducible F ∧ F.natDegree ≠ 0 ∧ F'.aeval (a i) = 0 ∧ ∃ d, ¬p ∣ d ∧ F'.coeff d ≠ 0 := by
  classical
  have : ¬ AlgebraicIndependent k a := fun h ↦
    ((AlgebraicIndependent.iff_transcendental_adjoin_image n).mp h).2
      (Set.image_eq_range .. ▸ ha'.isAlgebraic.isAlgebraic _)
  have HF : ∃ F : MvPolynomial ι k, F ≠ 0 ∧ MvPolynomial.aeval a F = 0 := by
    simpa [algebraicIndependent_iff, and_comm] using this
  replace HF : ∃ m, ∃ F : MvPolynomial ι k, F.totalDegree = m ∧ F ≠ 0 ∧ F.aeval a = 0 :=
    have ⟨F, hF, h⟩ := HF; ⟨F.totalDegree, F, rfl, hF, h⟩
  -- We choose the one with the least total degree `m`.
  let m := Nat.find HF
  obtain ⟨F, hm : _ = m, hF, h⟩ := Nat.find_spec HF
  replace H (ι : Type u_3) (_ : Fintype ι) (v : ι → K) (hv : LinearIndependent k v) :
      LinearIndependent k (v · ^ p) := by
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ, linearIndepOn_range_iff
      hv.injective] using H (Finset.univ.image v) (by simpa using hv.linearIndepOn_id)
  -- By the minimality of total degree, `F` is irreducible.
  have hFirr : Irreducible F := irreducible_of_forall_aeval_eq_zero_totalDegree_le a F hF h
    fun F' h₁ h₂ ↦ hm.trans_le (Nat.find_min' HF ⟨F', rfl, h₁, h₂⟩)
  -- By the minimality of total degree and the linearly independent condition,
  -- there exists some `Xᵢᵈ` with `p ∤ d` appearing in `F`.
  obtain ⟨i, hi⟩ : ∃ i, ∃ σ ∈ F.support, ¬ p ∣ σ i := by
    by_contra!
    have (σ) (hσ : σ ∈ F.support) : ∃ σ', σ = p • σ' := by
      choose σ' hσ' using (this · σ hσ)
      exact ⟨⟨σ.support, σ', by simp [hσ', hp.ne_zero]⟩, Finsupp.ext hσ'⟩
    choose! σ' hσ' using this
    have hσ'' (σ : F.support) : σ.1 = p • σ' σ := hσ' σ.1 σ.2
    have := mt (H F.support inferInstance (fun s ↦ aeval a (monomial (σ' s) (1 : k)))) (by
      simp_rw [← map_pow, monomial_pow, ← hσ'', one_pow, not_linearIndependent_iff]
      refine ⟨.univ, (F.coeff ·), ?_, by simpa [MvPolynomial.eq_zero_iff] using hF⟩
      simp only [← map_smul, ← map_sum, Finset.univ_eq_attach, smul_eq_mul, mul_one]
      rw [F.support.sum_attach (fun i ↦ monomial i (F.coeff i)), support_sum_monomial_coeff, h])
    simp only [LinearIndependent, injective_iff_map_eq_zero, not_forall] at this
    obtain ⟨F', hF', hF'0⟩ := this
    let F'' : MvPolynomial ι k := F'.mapDomain fun s ↦ σ' s.1
    have hF''0 : F'' ≠ 0 := ne_of_ne_of_eq ((Finsupp.mapDomain_injective fun s t h ↦ Subtype.ext
      (Finsupp.ext fun i ↦ by rw [hσ' _ s.2, hσ' _ t.2, h])).ne_iff.mpr hF'0) (by simp)
    have hF'' : aeval a F'' = 0 := by
      have : (aeval a).toLinearMap ∘ₗ (Finsupp.lmapDomain k k fun s : F.support ↦ σ' ↑s) =
          (Finsupp.linearCombination k fun s : F.support ↦ aeval a (monomial (σ' ↑s) (1 : k))) := by
        ext v; simp [MvPolynomial, AddMonoidAlgebra, monomial]
      simp only [← hF', F'', ← this]; rfl
    have : m ≤ _ := Nat.find_min' HF ⟨F'', rfl, hF''0, hF''⟩
    suffices hpm : p * F''.totalDegree ≤ m by
      have hF''0' : F''.totalDegree ≠ 0 := by
        contrapose! hF''0
        rw [totalDegree_eq_zero_iff_eq_C.mp hF''0, aeval_C, map_eq_zero] at hF''
        rw [totalDegree_eq_zero_iff_eq_C.mp hF''0, hF'', map_zero]
      replace this := hpm.trans (this.trans_eq (one_mul _).symm)
      exact hp.one_lt.not_ge ((mul_le_mul_iff_of_pos_right hF''0'.bot_lt).mp this)
    rw [totalDegree, Finset.mul_sup₀, Finset.sup_le_iff, ← hm]
    intro σ hσ
    obtain ⟨σ, hσ₂, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hσ)
    refine le_trans ?_ (Finset.le_sup σ.2)
    conv_rhs => rw [hσ' _ σ.2, Finsupp.sum_smul_index (fun _ ↦ rfl), ← Finsupp.mul_sum]
  -- Now we view `F` as a polynomial in one variable `Xᵢ`.
  let Fi := optionEquivLeft k _ (renameEquiv k (Equiv.optionSubtypeNe i).symm F)
  let F' := Fi.mapAlgHom (B := K) (aeval fun j ↦ a j.1)
  have hF' : Polynomial.aeval (a i) F' = 0 := by
    simp only [← h, F', ← AlgEquiv.coe_algHom, ← AlgHom.comp_apply, Fi,
      ← AlgHom.restrictScalars_apply k (Polynomial.aeval _)]
    congr 1
    ext j
    obtain ⟨_ | j, rfl⟩ := (Equiv.optionSubtypeNe i).surjective j
    · simp [optionEquivLeft_X_none]
    · simp [Subalgebra.algebraMap_eq, j.2, optionEquivLeft_X_some]
  -- We show that the `Xᵢᵈ` with `p ∤ d` is still present in `F` after mapping into `K`,
  -- or else there is a non-trivial algebraic relation, contradicting the minimality of `F`.
  have hF'' : ∃ d, ¬ p ∣ d ∧ F'.coeff d ≠ 0 := by
    obtain ⟨σ, hσ, hi⟩ := hi
    refine ⟨σ i, hi, fun hF'i ↦ ?_⟩
    refine coeff_eval_ite_ne_zero_of_forall_aeval_eq_zero_totalDegree_le a F
      (fun F' h₁ h₂ ↦ hm.trans_le (Nat.find_min' HF ⟨F', rfl, h₁, h₂⟩)) i (σ i)
      (fun H ↦ hi (H ▸ dvd_zero p)) ⟨σ, hσ, rfl⟩ (.trans ?_ hF'i)
    show _ = (((Polynomial.mapAlgHom _).comp
      ((optionEquivLeft k _).toAlgHom.comp (rename _))) _).coeff (σ i)
    congr 2
    ext : 1
    aesop (add simp optionEquivLeft_X_some) (add simp optionEquivLeft_X_none)
  have hFi : Fi.natDegree ≠ 0 := by
    intro e
    obtain ⟨d, hpd, hF'd⟩ := hF''
    obtain rfl : d = 0 := by
      rw [← le_zero_iff, ← e]
      exact (Polynomial.le_natDegree_of_ne_zero hF'd).trans Polynomial.natDegree_map_le
    exact hpd (dvd_zero _)
  exact ⟨i, Fi, (hFirr.map (renameEquiv k _)).map (optionEquivLeft k _), hFi, hF', hF''⟩

include hp ha ha' H in
/--
Suppose `k` has chararcteristic `p` and `K/k` is generated by `a₁,...,aₙ₊₁`,
where `a₁,...aₙ` forms a transcendental basis.
Suppose furthermore that if `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
`{ sᵢᵖ } ⊆ K` is also `k`-linearly independent (which is true when `K ⊗ₖ k^{1/p}` is reduced).

Then some subset of `a₁,...,aₙ₊₁` forms a separable transcedental basis.
-/
@[stacks 0H71]
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin_eq_top :
    ∃ i : ι, IsTranscendenceBasis k (fun j : {j // j ≠ i} ↦ a j) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (a '' {i}ᶜ)) K := by
  classical
  -- By the previous lemma, we can find an irreducible polynomial `F(x₁,...,xₙ₊₁)` such that
  -- `F(a₁,...,aₙ₊₁) = 0`, and some `Xᵢᵈ` appears in `F` with `¬ p ∣ d`.
  obtain ⟨i, F, hFIrr, hF0, haF, H⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin_eq_top_aux
      p hp a n ha' H
  let F' : Polynomial (Algebra.adjoin k (a '' {i}ᶜ)) := Polynomial.mapAlgHom
    (aeval fun j ↦ ⟨a (Equiv.optionSubtypeNe i j), Algebra.subset_adjoin ⟨j, j.2, rfl⟩⟩) F
  have hF' : Polynomial.aeval (a i) F' = 0 := by
    simp only [← haF, F',  ← AlgEquiv.coe_algHom, ← AlgHom.comp_apply,
      ← AlgHom.restrictScalars_apply k (Polynomial.aeval _)]
    congr 1
    ext j <;> simp [Subalgebra.algebraMap_eq]
  replace H : ∃ d, ¬p ∣ d ∧ F'.coeff d ≠ 0 :=
    have ⟨d, hpd, H⟩ := H; ⟨d, hpd, fun e ↦ H (.trans (by
      simp [F', ← aeval_algebraMap_apply, -map_aeval]; rfl) congr(algebraMap _ _ ($e)))⟩
  have Hi := IsTranscendenceBasis.ne_of_isTranscendenceBasis_ne n i a ha'
    ⟨F', fun e ↦ by simp [e] at H, hF'⟩
  refine ⟨i, Hi, ?_⟩
  have hai : a '' {i}ᶜ = Set.range (a ∘ (Subtype.val : { b | b ≠ i } → ι)) := by ext; aesop
  rw [hai]
  set k' := IntermediateField.adjoin k (Set.range (a ∘ (Subtype.val : { b | b ≠ i } → ι)))
  have hk' : k'⟮a i⟯ = ⊤ := by
    apply IntermediateField.restrictScalars_injective k
    rw [IntermediateField.adjoin_adjoin_left, IntermediateField.restrictScalars_top, ← ha,
      ← Set.image_singleton, ← hai, ← Set.image_union, ← Set.image_univ, Set.compl_union_self]
  rw [← AlgEquiv.Algebra.isSeparable_iff IntermediateField.topEquiv, ← hk',
    IntermediateField.isSeparable_adjoin_simple_iff_isSeparable]
  have hk'' : Algebra.adjoin k (a '' {i}ᶜ) ≤ k'.toSubalgebra :=
    hai ▸ IntermediateField.algebra_adjoin_le_adjoin _ _
  let F'' : Polynomial k' := F'.mapAlgHom (B := k') (Subalgebra.inclusion hk'')
  -- By gauss' lemma, `F` is still irrreducible over `k(x₁,...,xᵢ₋₁, xᵢ₊₁,...,xₙ₊₁)`.
  have hF''irr : Irreducible F'' := by
    have inst : NormalizedGCDMonoid (MvPolynomial { b // b ≠ i } k) := Nonempty.some inferInstance
    have : Irreducible (F.mapAlgHom (IsScalarTower.toAlgHom k _ _)) :=
      (hFIrr.isPrimitive hF0).irreducible_iff_irreducible_map_fraction_map
        (K := FractionRing (MvPolynomial { b // b ≠ i } k)).mp hFIrr
    convert this.map (Polynomial.mapAlgEquiv Hi.1.aevalEquivField) using 1
    simp only [F', Polynomial.mapAlgHom_comp, ← AlgEquiv.coe_algHom, AlgEquiv.toAlgHom_eq_coe,
      ← AlgHom.comp_apply, Polynomial.mapAlgEquiv_toAlgHom, F'']
    congr
    ext j
    simp only [ne_eq, Equiv.optionSubtypeNe_apply, Option.casesOn'_some, AlgHom.coe_comp,
      Function.comp_apply, aeval_X]
    show a _ = Hi.1.aevalEquivField (algebraMap _ _ _)
    rw [Hi.1.aevalEquivField_algebraMap_apply_coe, aeval_X]
  have hF''ai : Polynomial.aeval (a i) F'' = 0 := by
    simpa only [Polynomial.coe_mapAlgHom, Polynomial.aeval_def, Polynomial.eval₂_map, F''] using hF'
  have hF''0 : F'' ≠ 0 := (map_ne_zero_iff _ (Polynomial.map_injective _
    (Subalgebra.inclusion_injective hk''))).mpr fun e ↦ by simp [e] at H
  -- And by the existence of `Xᵢᵈ` with `p ∤ d`, it is separable.
  by_contra Hsep
  have instExpChar : ExpChar k' p := expChar_of_injective_algebraMap (algebraMap k k').injective _
  have : CharP k' p := by
    cases instExpChar
    · cases hp.ne_one rfl
    · assumption
  obtain ⟨g, hg, e⟩ := (((minpoly k' (a i)).separable_or p (minpoly.irreducible
    (isAlgebraic_iff_isIntegral.mp ⟨F'', hF''0, hF''ai⟩))).resolve_left Hsep).2
  obtain ⟨d, hpd, hF'd⟩ := H
  replace e := congr(Polynomial.coeff $e d)
  rw [← minpoly.eq_of_irreducible hF''irr hF''ai, Polynomial.coeff_mul_C,
    Polynomial.coeff_expand hp.pos, if_neg hpd, eq_mul_inv_iff_mul_eq₀ (by simpa using hF''0),
    zero_mul, eq_comm] at e
  exact (Subalgebra.inclusion_injective hk'').ne_iff.mpr hF'd (by simpa [F''] using e)

open IntermediateField

include hp H in
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_aux
    (t : Set K) (x : K) (ht : IsTranscendenceBasis k ((↑) : t → K)) (hxt : x ∉ t) :
    ∃ (i : ↑(insert x t)), (IsTranscendenceBasis k fun (j : {j // j ≠ i}) ↦ j.1.1) ∧
      IntermediateField.adjoin k (insert x ↑t : Set K) ≤ (separableClosure
        (IntermediateField.adjoin k (Subtype.val '' {i}ᶜ)) K).restrictScalars _ := by
  classical
  have inst : ExpChar K p := expChar_of_injective_ringHom (algebraMap k K).injective p
  letI K' := IntermediateField.adjoin k (insert x ↑t : Set K)
  have : Algebra.IsAlgebraic K' K := by
    have := ht.isAlgebraic_field
    rw [IntermediateField.isAlgebraic_adjoin_iff_top,
      ← AlgebraicIndependent.matroid_spanning_iff] at this ⊢
    exact .superset this (by simp)
  letI tx : (insert x ↑t : Set K) → K' := fun a ↦ ⟨a.1, IntermediateField.subset_adjoin _ _ a.2⟩
  have htx : K'.val '' Set.range tx = insert x ↑t := by
    rw [← Set.range_comp]
    exact Subtype.range_val
  have ⟨i, hi, H⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin_eq_top
    (k := k) (K := K') p hp tx ⟨x, by simp⟩ ?_ ?_ ?_
  · let K₁ := IntermediateField.adjoin k (tx '' {i}ᶜ)
    let K₂ := IntermediateField.adjoin k (Subtype.val '' {i}ᶜ)
    letI e : K₁ ≃ₐ[k] K₂ := (equivMap K₁ K'.val).trans (equivOfEq (by
      simp only [adjoin_map, coe_val, K₁, K₂, ← Set.image_comp]; rfl))
    letI := e.toRingHom.toAlgebra
    have : IsScalarTower K₁ K₂ K := .of_algebraMap_eq' rfl
    refine ⟨i, hi.algebraMap_comp, ?_⟩
    intro x hx
    have := (Algebra.IsSeparable.isSeparable (IntermediateField.adjoin k (tx '' {i}ᶜ)) (K := K')
      ⟨x, hx⟩).map (L := K) ⟨K'.val.toRingHom, fun _ ↦ by rfl⟩ Subtype.val_injective
    rw [mem_restrictScalars, mem_separableClosure_iff]
    exact this.tower_top (IntermediateField.adjoin k (Subtype.val '' {i}ᶜ))
  · apply IntermediateField.map_injective (IntermediateField.val _)
    rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map, fieldRange_val, htx]
  · apply IsTranscendenceBasis.of_comp (IntermediateField.val _) Subtype.val_injective
    convert ht.comp_equiv ?_ using 1; swap
    · exact ⟨fun x ↦ ⟨x.1, by aesop⟩, fun x ↦ ⟨⟨x.1, by aesop⟩, by aesop⟩,
        fun x ↦ by aesop, fun x ↦ by aesop⟩
    ext
    simp [K', tx]
  · intro s
    have := H (s.image (IntermediateField.val _))
    simp only [coe_val, Finset.coe_image] at this
    rw [← linearIndepOn_iff_image Subtype.val_injective.injOn] at this
    rw [linearIndepOn_iff_image (f := (· ^ p)) (frobenius_inj K p).injOn,
      ← Set.image_comp, ← linearIndepOn_iff_image (f := (· ^ p) ∘ Subtype.val)
        ((frobenius_inj K p).comp Subtype.val_injective).injOn] at this
    rw [← LinearMap.linearIndepOn_iff_of_injOn K'.val.toLinearMap Subtype.val_injective.injOn,
      ← LinearMap.linearIndepOn_iff_of_injOn K'.val.toLinearMap Subtype.val_injective.injOn]
    exact this

/-- In a finitely generated field extension, there exists a maximal
separably generated field extension. -/
lemma exists_isTranscendenceBasis_forall_separableClosure_not_lt
    (Hfg : IntermediateField.FG (F := k) (E := K) ⊤) :
    ∃ t : Finset K, IsTranscendenceBasis k ((↑) : t → K) ∧
      ∀ t' : Set K, IsTranscendenceBasis k ((↑) : t' → K) →
      ¬ (separableClosure (IntermediateField.adjoin k (t : Set K)) K).restrictScalars k <
        (separableClosure (IntermediateField.adjoin k t') K).restrictScalars k := by
  classical
  have Hexists : ∃ n : ℕ, ∃ t : Finset K, IsTranscendenceBasis k ((↑) : t → K) ∧
      Field.finInsepDegree (IntermediateField.adjoin k (t : Set K)) K = n := by
    obtain ⟨s, hs⟩ := Hfg
    have : Algebra.IsAlgebraic (Algebra.adjoin k (s : Set K)) K := by
      rw [← isAlgebraic_adjoin_iff_top, hs, Algebra.isAlgebraic_iff_isIntegral]
      refine Algebra.isIntegral_of_surjective topEquiv.surjective
    obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := k) (s : Set K)
    have ht' : t.Finite := s.finite_toSet.subset hts
    refine ⟨_, ht'.toFinset, (by convert ht <;> ext <;> simp), rfl⟩
  let N := Nat.find Hexists
  obtain ⟨t, ht, htN : _ = N⟩ := Nat.find_spec Hexists
  refine ⟨t, ht, fun t' ht' H ↦ ?_⟩
  have : t'.Finite := by
    rw [Set.Finite, ← Cardinal.mk_lt_aleph0_iff, ← ht.cardinalMk_eq ht']
    simp [Cardinal.nat_lt_aleph0]
  lift t' to Finset K using this
  have := htN.trans_le (Nat.find_min' Hexists ⟨t', ht', rfl⟩)
  dsimp [Field.finInsepDegree] at this
  have inst : Module.Finite (IntermediateField.adjoin k (t : Set K)) K := by
    apply (config := { allowSynthFailures := true })
      IntermediateField.finite_of_fg_of_isAlgebraic
    · exact .of_restrictScalars (K := k) (by rwa [restrictScalars_top])
    · convert IsTranscendenceBasis.isAlgebraic_field ht <;> simp
  have inst : Module.Finite
      ((separableClosure (↥(IntermediateField.adjoin k (t : Set K))) K).restrictScalars k) K := by
    show Module.Finite (separableClosure (↥(IntermediateField.adjoin k (t : Set K))) K) K
    infer_instance
  exact (IntermediateField.finrank_lt_of_lt H).not_ge this

include hp H in
/--
Suppose `k` has chararcteristic `p` and `K/k` is finitely generated.
Suppose furthermore that if `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
`{ sᵢᵖ } ⊆ K` is also `k`-linearly independent (which is true when `K ⊗ₖ k^{1/p}` is reduced).

Then `K/k` is finite separably generated.

TODO: show that this is an if and only if.
-/
@[stacks 030W "(2) => (1) finitely genenerated case"]
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow
    (Hfg : IntermediateField.FG (F := k) (E := K) ⊤) :
    ∃ s : Finset K, IsTranscendenceBasis k ((↑) : s → K) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K := by
  classical
  obtain ⟨t, ht, Ht⟩ := exists_isTranscendenceBasis_forall_separableClosure_not_lt Hfg
  refine ⟨t, ht, ?_⟩
  rw [Algebra.isSeparable_def]
  by_contra!
  obtain ⟨x, hx⟩ := this
  have hxt : x ∉ t := by
    contrapose! hx
    exact isSeparable_algebraMap (F := IntermediateField.adjoin k (t : Set K))
      ⟨x, IntermediateField.subset_adjoin _ _ hx⟩
  obtain ⟨i, hi₁, hi₂⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_aux p hp H t x ht hxt
  apply Ht (Set.range (Subtype.val ∘ Subtype.val)) hi₁.to_subtype_range
  refine lt_of_lt_of_eq (b := restrictScalars k
    (separableClosure (↥(IntermediateField.adjoin k (Subtype.val '' {i}ᶜ))) K)) ?_ ?_
  · rw [SetLike.lt_iff_le_and_exists]
    constructor
    · rw [separableClosure_le_separableClosure_iff]
      exact .trans (IntermediateField.gi.gc.monotone_l (Set.subset_insert _ _)) hi₂
    · exact ⟨x, hi₂ (IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)), hx⟩
  · rw [Set.range_comp]
    congr! <;> simp <;> rfl

end
