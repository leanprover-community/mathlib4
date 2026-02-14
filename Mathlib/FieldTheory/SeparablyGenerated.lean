/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Christian Merten, Junyan Xu
-/
module

public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.Order.Ring.Finset
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!

# Separably generated extensions

We aim to formalize the following result:

Let `K/k` be a finitely generated field extension with characteristic `p > 0`, then TFAE
1. `K/k` is separably generated
2. If `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
  `{ sᵢᵖ } ⊆ K` is also `k`-linearly independent
3. `K ⊗ₖ k^{1/p}` is reduced
4. `K` is geometrically reduced over `k`.
5. `k` and `Kᵖ` are linearly disjoint over `kᵖ` in `K`.

## Main result
- `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow`: (2) ⇒ (1)

-/

@[expose] public noncomputable section

section

attribute [local instance 2000] Polynomial.isScalarTower Algebra.toSMul IsScalarTower.right

open MvPolynomial
open scoped IntermediateField

variable {k K ι : Type*} [Field k] [Field K] [Algebra k K] (p : ℕ) (hp : p.Prime)
variable (H : ∀ s : Finset K,
  LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (· ^ p) (s : Set K))
variable {a : ι → K} (n : ι)

namespace MvPolynomial

/-- View a multivariate polynomial `F(x₁,...,xₙ)` as a polynomial in `xᵢ` with coefficients
in `F(x₁,...,xᵢ₋₁,xᵢ₊₁,...,xₙ)`. -/
def toPolynomialAdjoinImageCompl (F : MvPolynomial ι k) (a : ι → K) (i : ι) :
    Polynomial (Algebra.adjoin k (a '' {i}ᶜ)) :=
  letI := Classical.typeDecidableEq ι
  (optionEquivLeft k _ (renameEquiv k (Equiv.optionSubtypeNe i).symm F)).mapAlgHom
    (aeval fun j : {j // j ≠ i} ↦
      (⟨a j, Algebra.subset_adjoin ⟨j, j.2, rfl⟩⟩ : Algebra.adjoin k (a '' {i}ᶜ)))

theorem aeval_toPolynomialAdjoinImageCompl_eq_zero
    {a : ι → K} {F : MvPolynomial ι k} (hFa : F.aeval a = 0) (i : ι) :
    (toPolynomialAdjoinImageCompl F a i).aeval (a i) = 0 := by
  rw [← hFa, ← AlgHom.restrictScalars_apply k]
  simp_rw [toPolynomialAdjoinImageCompl, ← AlgEquiv.coe_algHom, ← AlgHom.comp_apply]
  congr; ext; aesop (add simp optionEquivLeft_X_some) (add simp optionEquivLeft_X_none)

theorem irreducible_toPolynomialAdjoinImageCompl {F : MvPolynomial ι k} (hF : Irreducible F) (i : ι)
    (H : AlgebraicIndependent k fun x : {j | j ≠ i} ↦ a x) :
    Irreducible (toPolynomialAdjoinImageCompl F a i) := by
  have : a '' {i}ᶜ = Set.range (fun x : {j | j ≠ i} ↦ a x) := by ext; simp
  delta toPolynomialAdjoinImageCompl
  convert hF.map (renameEquiv k (Equiv.optionSubtypeNe i).symm) |>.map (optionEquivLeft k _) |>.map
    (Polynomial.mapAlgEquiv (H.aevalEquiv.trans
      (Subalgebra.equivOfEq _ _ congr(Algebra.adjoin k $this.symm))))
  rw [← AlgEquiv.coe_algHom]
  congr
  aesop

-- Suppose `F` has minimal total degree among the relations of `a`.
variable {F : MvPolynomial ι k}
variable (HF : ∀ F' : MvPolynomial ι k, F' ≠ 0 → F'.aeval a = 0 → F.totalDegree ≤ F'.totalDegree)

include HF

/-- If `F` has minimal total degree among the relations of `a`, then `F` is irreducible. -/
lemma irreducible_of_forall_totalDegree_le (hF0 : F ≠ 0) (hFa : F.aeval a = 0) : Irreducible F := by
  refine ⟨fun h' ↦ (h'.map (aeval a)).ne_zero hFa, fun q₁ q₂ e ↦ ?_⟩
  wlog h₁ : aeval a q₁ = 0 generalizing q₁ q₂
  · exact .symm (this q₂ q₁ (e.trans (mul_comm ..)) <| by simpa [h₁, hFa] using congr(aeval a $e))
  have ne := mul_ne_zero_iff.mp (e ▸ hF0)
  have := HF q₁ ne.1 h₁
  rw [e, totalDegree_mul_of_isDomain ne.1 ne.2, add_le_iff_nonpos_right, nonpos_iff_eq_zero] at this
  refine .inr (isUnit_iff_totalDegree_of_isReduced.mpr ⟨?_, this⟩)
  rw [totalDegree_eq_zero_iff_eq_C.mp this] at ne
  simpa using ne.2

theorem coeff_toPolynomialAdjoinImageCompl_ne_zero
    (σ : ι →₀ ℕ) (hσ : σ ∈ F.support) (i : ι) (hσi : σ i ≠ 0) :
    (toPolynomialAdjoinImageCompl F a i).coeff (σ i) ≠ 0 := by
  classical
  intro H
  let F₀ := optionEquivLeft k _ (renameEquiv k (Equiv.optionSubtypeNe i).symm F)
  have H := HF (rename (↑) (F₀.coeff (σ i))) ?_ ?_
  · have : (F₀.coeff (σ i)).totalDegree + σ i ≤ _ :=
      totalDegree_coeff_optionEquivLeft_add_le _ _ _ (σ i) <| by
        rw [totalDegree_renameEquiv]
        exact (Finsupp.le_degree ..).trans (le_totalDegree hσ)
    rw [totalDegree_renameEquiv] at this
    simpa [hσi] using (this.trans H).trans (totalDegree_rename_le _ _)
  · refine (map_eq_zero_iff _ (rename_injective _ Subtype.val_injective)).not.mpr fun H ↦ ?_
    let e := (Equiv.optionSubtypeNe i).symm
    have : coeff _ (F₀.coeff _) = _ :=
      optionEquivLeft_coeff_some_coeff_none _ _ (σ.equivMapDomain e) (renameEquiv k e F)
    dsimp only [F₀] at this
    rw [renameEquiv_apply, Finsupp.equivMapDomain_eq_mapDomain, coeff_rename_mapDomain _
      e.injective, Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Equiv.optionSubtypeNe_none,
      ← renameEquiv_apply, H, coeff_zero, eq_comm, ← notMem_support_iff] at this
    exact this hσ
  · apply_fun Subalgebra.val _ at H
    simp_rw [toPolynomialAdjoinImageCompl, Polynomial.coe_mapAlgHom, Polynomial.coeff_map,
      AlgHom.coe_toRingHom, map_zero] at H
    simp_rw [← H, ← AlgHom.comp_apply]
    congr; ext; simp

theorem isAlgebraic_of_mem_vars_of_forall_totalDegree_le (hFa : F.aeval a = 0) (i : ι)
    (hi : i ∈ F.vars) : IsAlgebraic (Algebra.adjoin k (a '' {i}ᶜ)) (a i) := by
  classical
  have ⟨σ, hσ, hσi⟩ := (mem_vars i).mp hi
  refine ⟨toPolynomialAdjoinImageCompl F a i,
    fun h ↦ coeff_toPolynomialAdjoinImageCompl_ne_zero HF σ hσ i
      (Finsupp.mem_support_iff.mp hσi) ?_, aeval_toPolynomialAdjoinImageCompl_eq_zero hFa ..⟩
  rw [h, Polynomial.coeff_zero]

include hp H in
theorem exists_mem_support_not_dvd_of_forall_totalDegree_le (hF0 : F ≠ 0) (hFa : F.aeval a = 0) :
    ∃ i, ∃ σ ∈ F.support, ¬ p ∣ σ i := by
  by_contra!
  have (σ) (hσ : σ ∈ F.support) : ∃ σ', σ = p • σ' := by
    choose σ' hσ' using (this · σ hσ)
    exact ⟨⟨σ.support, σ', by simp [hσ', hp.ne_zero]⟩, Finsupp.ext hσ'⟩
  choose! σ' hσ' using this
  have hσ'' (σ : F.support) : σ.1 = p • σ' σ := hσ' σ.1 σ.2
  classical
  replace H (ι : Type u_3) (_ : Fintype ι) (v : ι → K) (hv : LinearIndependent k v) :
      LinearIndependent k (v · ^ p) := by
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ, linearIndepOn_range_iff
      hv.injective] using H (Finset.univ.image v) (by simpa using hv.linearIndepOn_id)
  have := mt (H F.support inferInstance (fun s ↦ aeval a (monomial (σ' s) (1 : k)))) (by
    simp_rw [← map_pow, monomial_pow, ← hσ'', one_pow, not_linearIndependent_iff]
    refine ⟨.univ, (F.coeff ·), ?_, by simpa [MvPolynomial.eq_zero_iff] using hF0⟩
    simp only [← map_smul, ← map_sum, Finset.univ_eq_attach, smul_eq_mul, mul_one]
    rw [F.support.sum_attach (fun i ↦ monomial i (F.coeff i)), support_sum_monomial_coeff, hFa])
  simp only [LinearIndependent, injective_iff_map_eq_zero, not_forall] at this
  obtain ⟨F', hF', hF'0⟩ := this
  let F'' : MvPolynomial ι k := F'.mapDomain fun s ↦ σ' s.1
  have hF''0 : F'' ≠ 0 := ne_of_ne_of_eq ((Finsupp.mapDomain_injective fun s t h ↦ Subtype.ext
    (Finsupp.ext fun i ↦ by rw [hσ' _ s.2, hσ' _ t.2, h])).ne_iff.mpr hF'0) (by simp)
  have hF'' : aeval a F'' = 0 := by
    have : (aeval a).toLinearMap ∘ₗ (Finsupp.lmapDomain k k fun s : F.support ↦ σ' s) =
        (Finsupp.linearCombination k fun s : F.support ↦ aeval a (monomial (σ' s) (1 : k))) := by
      ext v; simp [MvPolynomial, AddMonoidAlgebra, monomial]
    simp only [← hF', F'', ← this]; rfl
  suffices hpm : p * F''.totalDegree ≤ F.totalDegree by
    have hF''0' : F''.totalDegree ≠ 0 := by
      contrapose! hF''0
      rw [totalDegree_eq_zero_iff_eq_C.mp hF''0, aeval_C, map_eq_zero] at hF''
      rw [totalDegree_eq_zero_iff_eq_C.mp hF''0, hF'', map_zero]
    replace this := hpm.trans ((HF F'' hF''0 hF'').trans_eq (one_mul _).symm)
    exact hp.one_lt.not_ge ((mul_le_mul_iff_of_pos_right hF''0'.bot_lt).mp this)
  rw [totalDegree, Finset.mul_sup₀, Finset.sup_le_iff]
  intro σ hσ
  obtain ⟨σ, hσ₂, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hσ)
  refine le_trans ?_ (Finset.le_sup σ.2)
  conv_rhs => rw [hσ' _ σ.2, Finsupp.sum_smul_index (fun _ ↦ rfl), ← Finsupp.mul_sum]

end MvPolynomial

open IntermediateField

section

variable [ExpChar k p]

include hp H

/--
Suppose `k` has chararcteristic `p` and `a₁,...,aₙ` is a transcendental basis of `K/k`.
Suppose furthermore that if `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
`{ sᵢᵖ } ⊆ K` is also `k`-linearly independent (which is true when `K ⊗ₖ k^{1/p}` is reduced).

Then some subset of `a₁,...,aₙ₊₁` forms a transcedental basis that `a₁,...,aₙ₊₁` are separable over.
-/
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow
    (ha' : IsTranscendenceBasis k fun i : {i // i ≠ n} ↦ a i) :
    ∃ i : ι, IsTranscendenceBasis k (fun j : {j // j ≠ i} ↦ a j) ∧
      IsSeparable (adjoin k (a '' {i}ᶜ)) (a i) := by
  have : a '' {n}ᶜ = Set.range (ι := { i // i ≠ n }) (a ·) := by aesop
  have ha'' : ¬ AlgebraicIndependent k a := fun h ↦
    ((AlgebraicIndepOn.insert_iff (show n ∉ {n}ᶜ by simp)).mp
      (by simpa [Set.insert_def, eq_or_ne])).2 (by convert ha'.isAlgebraic.isAlgebraic _)
  have HF : {F : MvPolynomial ι k | F ≠ 0 ∧ F.aeval a = 0}.Nonempty := by
    simpa [algebraicIndependent_iff, and_comm] using ha''
  let F := totalDegree.argminOn _ HF
  obtain ⟨hF0, hFa⟩ := totalDegree.argminOn_mem _ HF
  replace HF f h₁ h₂ := totalDegree.argminOn_le _ (a := f) (.intro h₁ h₂) HF
  have hFirr : Irreducible F := irreducible_of_forall_totalDegree_le HF hF0 hFa
  obtain ⟨i, σ, hσ, hi⟩ := exists_mem_support_not_dvd_of_forall_totalDegree_le p hp H HF hF0 hFa
  have hσi : σ i ≠ 0 := by aesop
  have alg := isAlgebraic_of_mem_vars_of_forall_totalDegree_le HF hFa i <|
    (mem_vars i).mpr ⟨σ, hσ, by simpa⟩
  have Hi := ha'.of_isAlgebraic_adjoin_image_compl _ i _ alg
  refine ⟨i, Hi, ?_⟩
  let k' := adjoin k (a '' {i}ᶜ)
  have hF₁irr := irreducible_toPolynomialAdjoinImageCompl hFirr i Hi.1
  have := (AlgebraicIndepOn.aevalEquiv (s := {i}ᶜ) Hi.1).uniqueFactorizationMonoid inferInstance
  have coeff_ne := coeff_toPolynomialAdjoinImageCompl_ne_zero HF σ hσ i hσi
  open scoped algebraAdjoinAdjoin in
  have hF₂irr := (hF₁irr.isPrimitive fun h ↦ coeff_ne <| Polynomial.coeff_eq_zero_of_natDegree_lt <|
    h.trans_lt <| Nat.pos_iff_ne_zero.2 hσi).irreducible_iff_irreducible_map_fraction_map
    (K := k').1 hF₁irr
  contrapose! coeff_ne with Hsep
  have : CharP k' p := (expChar_of_injective_algebraMap (algebraMap k k').injective p).casesOn
    (fun e ↦ (e rfl).elim) (fun _ _ _ ↦ ‹_›) hp.ne_one
  obtain ⟨g, hg, eq⟩ := (((minpoly k' (a i)).separable_or p (minpoly.irreducible
    (isAlgebraic_iff_isIntegral.mp <| isAlgebraic_adjoin_iff.mpr alg))).resolve_left Hsep).2
  replace eq := congr(Polynomial.coeff $eq (σ i))
  rwa [← minpoly.eq_of_irreducible hF₂irr ((Polynomial.aeval_map_algebraMap ..).trans
    (aeval_toPolynomialAdjoinImageCompl_eq_zero hFa i)), Polynomial.coeff_mul_C,
    Polynomial.coeff_expand hp.pos, if_neg hi, eq_mul_inv_iff_mul_eq₀
    (by simpa using hF₂irr.ne_zero), zero_mul, eq_comm,
    Polynomial.coeff_map, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ..)] at eq

lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow'
    (s : Set ι) (n : ι) (ha : IsTranscendenceBasis k fun i : s ↦ a i) (hn : n ∉ s) :
    ∃ i : ι, IsTranscendenceBasis k (fun j : ↥(insert n s \ {i}) ↦ a j) ∧
      IsSeparable (adjoin k (a '' (insert n s \ {i}))) (a i) := by
  let e₁ : {j : ↥(insert n s) // j ≠ ⟨n, by simp⟩} ≃ ↑s :=
    ⟨fun x ↦ ⟨x, by aesop⟩, fun x ↦ ⟨⟨x, by aesop⟩, by aesop⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  obtain ⟨i, hi, hi'⟩ := exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow p hp H
    (a := fun i : ↥(insert n s) ↦ a i) ⟨n, by simp⟩ (ha.comp_equiv e₁)
  let e₂ : {j // j ≠ i} ≃ ↥(insert n s \ {i.1}) := ⟨fun x ↦ ⟨x, x.1.2, fun h ↦ x.2 (Subtype.ext h)⟩,
    fun x ↦ ⟨⟨x, x.2.1⟩, fun h ↦ x.2.2 congr($h.1)⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  have : a '' (insert n s \ {i.1}) = (a ·.1) '' {i}ᶜ := by ext; aesop
  refine ⟨i, hi.comp_equiv e₂.symm, by convert hi'⟩

/--
Suppose `k` has chararcteristic `p` and `K/k` is generated by `a₁,...,aₙ₊₁`,
where `a₁,...aₙ` forms a transcendental basis.
Suppose furthermore that if `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
`{ sᵢᵖ } ⊆ K` is also `k`-linearly independent (which is true when `K ⊗ₖ k^{1/p}` is reduced).

Then some subset of `a₁,...,aₙ₊₁` forms a separable transcedental basis.
-/
@[stacks 0H71]
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin_eq_top
    (ha : IntermediateField.adjoin k (Set.range a) = ⊤)
    (ha' : IsTranscendenceBasis k fun i : {i // i ≠ n} ↦ a i) :
    ∃ i : ι, IsTranscendenceBasis k (fun j : {j // j ≠ i} ↦ a j) ∧
      Algebra.IsSeparable (adjoin k (a '' {i}ᶜ)) K := by
  have ⟨i, hi⟩ := exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow p hp H n ha'
  refine ⟨i, hi.1, ?_⟩
  rw [← separableClosure.eq_top_iff, ← (restrictScalars_injective k).eq_iff,
    restrictScalars_top, eq_top_iff, ← ha, adjoin_le_iff]
  rintro _ ⟨x, rfl⟩
  obtain rfl | ne := eq_or_ne x i
  · exact hi.2
  · exact isSeparable_algebraMap (F := adjoin k (a '' {i}ᶜ)) ⟨_, subset_adjoin _ _ ⟨x, ne, rfl⟩⟩

/--
Suppose `k` has chararcteristic `p` and `K/k` is finitely generated.
Suppose furthermore that if `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
`{ sᵢᵖ } ⊆ K` is also `k`-linearly independent (which is true when `K ⊗ₖ k^{1/p}` is reduced).

Then `K/k` is finite separably generated.

TODO: show that this is an if and only if.
-/
@[stacks 030W "(2) ⇒ (1) finitely genenerated case"]
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
    [Algebra.EssFiniteType k K] :
    ∃ s : Finset K, IsTranscendenceBasis k ((↑) : s → K) ∧
      Algebra.IsSeparable (adjoin k (s : Set K)) K := by
  have ⟨s, hs, Hs⟩ := exists_finset_maximalFor_isTranscendenceBasis_separableClosure k K
  refine ⟨s, hs, ⟨fun n ↦ of_not_not fun hn ↦ ?_⟩⟩
  have hns : n ∉ s := fun h ↦ hn (le_restrictScalars_separableClosure _ (subset_adjoin _ _ h))
  have ⟨i, hi₁, hi₂⟩ := exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow'
    p hp (a := id) H s n hs hns
  rw [Set.image_id] at hi₂
  refine not_lt_iff_le_imp_ge.mpr (Hs hi₁) (SetLike.lt_iff_le_and_exists.mpr ⟨?_, n, ?_, hn⟩)
  · rw [separableClosure_le_separableClosure_iff, adjoin_le_iff]
    intro x hx
    obtain rfl | ne := eq_or_ne x i
    exacts [hi₂, le_restrictScalars_separableClosure _ (subset_adjoin _ _ ⟨.inr hx, ne⟩)]
  · obtain rfl | ne := eq_or_ne n i
    exacts [hi₂, le_restrictScalars_separableClosure _ (subset_adjoin _ _ ⟨.inl rfl, ne⟩)]

end

variable (k K) in
/-- Any finitely generated extension over perfect fields are separably generated. -/
lemma exists_isTranscendenceBasis_and_isSeparable_of_perfectField
    [PerfectField k] [Algebra.EssFiniteType k K] :
    ∃ s : Finset K, IsTranscendenceBasis k ((↑) : s → K) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K := by
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · obtain ⟨s, hs⟩ := IntermediateField.fg_top k K
    have : Algebra.IsAlgebraic (Algebra.adjoin k (s : Set K)) K := by
      rw [← isAlgebraic_adjoin_iff_top, hs, Algebra.isAlgebraic_iff_isIntegral]
      exact Algebra.isIntegral_of_surjective topEquiv.surjective
    obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := k) (s : Set K)
    lift t to Finset K using s.finite_toSet.subset hts
    have : Algebra.IsAlgebraic (IntermediateField.adjoin k (t : Set K)) K := by
      convert ht.isAlgebraic_field <;> simp
    exact ⟨t, ht, inferInstance⟩
  have : ExpChar k p := .prime hp.out
  have : CharP K p := .of_ringHom_of_ne_zero (algebraMap k K) p hp.out.ne_zero
  refine exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
    p hp.out fun s hs ↦ ?_
  apply hs.map_of_injective_injective (frobeniusEquiv k p).symm (frobenius K p).toAddMonoidHom <;>
    simp [frobenius, Algebra.smul_def, mul_pow, ← map_pow, frobeniusEquiv_symm_pow]

end
