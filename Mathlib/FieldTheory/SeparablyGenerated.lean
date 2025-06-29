/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Order.Ring.Finset
import Mathlib.Data.Set.Subset
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
5. `k` and `Kᵖ` are linearly disjoint over `kᵖ` in `K`.

## Main result
- `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow`: (2) ⇒ (1)

-/

noncomputable section

section

attribute [local instance 2000] Polynomial.isScalarTower Algebra.toSMul IsScalarTower.right

open MvPolynomial
open scoped IntermediateField

variable {k K ι : Type*} [Field k] [Field K] [Algebra k K] (p : ℕ) (hp : p.Prime)
variable (a : ι → K) (n : ι) (ha : IntermediateField.adjoin k (Set.range a) = ⊤)
variable (ha' : IsTranscendenceBasis k fun i : {i // i ≠ n} ↦ a i)
variable (H : ∀ s : Finset K,
  LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (· ^ p) (s : Set K))

set_option quotPrecheck false
local notation "aevalAdjoin" a:arg i:arg => aeval fun j : {j // j ≠ i} ↦
  (⟨a j, Algebra.subset_adjoin ⟨j, j.2, rfl⟩⟩ : Algebra.adjoin k (a '' {i}ᶜ))

namespace MvPolynomial

variable (F : MvPolynomial ι k) (hF0 : F ≠ 0) (hFa : F.aeval a = 0)
variable (HF : ∀ (F' : MvPolynomial ι k), F' ≠ 0 → F'.aeval a = 0 → F.totalDegree ≤ F'.totalDegree)

include hF0 hFa HF in
theorem irreducible_of_forall_aeval_eq_zero_totalDegree_le : Irreducible F := by
  refine ⟨fun h' ↦ (h'.map (aeval a)).ne_zero hFa, fun q₁ q₂ e ↦ ?_⟩
  wlog h₁ : aeval a q₁ = 0 generalizing q₁ q₂
  · exact .symm (this q₂ q₁ (e.trans (mul_comm ..)) <| by simpa [h₁, hFa] using congr(aeval a $e))
  have ne := mul_ne_zero_iff.mp (e ▸ hF0)
  have := HF q₁ ne.1 h₁
  rw [e, totalDegree_mul_of_isDomain ne.1 ne.2, add_le_iff_nonpos_right, nonpos_iff_eq_zero] at this
  refine .inr (isUnit_iff_totalDegree_of_isReduced.mpr ⟨?_, this⟩)
  rw [totalDegree_eq_zero_iff_eq_C.mp this] at ne
  simpa using ne.2

set_option quotPrecheck false
local notation "e" i => (Equiv.optionSubtypeNe i).symm
local notation "F₀" i => optionEquivLeft k _ (renameEquiv k (e i) F)
local notation "F₁" i => (F₀ i).mapAlgHom (aevalAdjoin a i)

include hFa in
theorem aeval_ite_aeval_eq_zero [DecidableEq ι] (i : ι) : (F₁ i).aeval (a i) = 0 := by
  rw [← hFa, ← AlgHom.restrictScalars_apply k]
  simp_rw [← AlgEquiv.coe_algHom, ← AlgHom.comp_apply]
  congr; ext; aesop (add simp optionEquivLeft_X_some) (add simp optionEquivLeft_X_none)

include HF in
theorem coeff_aeval_ite_ne_zero_of_forall_aeval_eq_zero_totalDegree_le [DecidableEq ι]
    (σ : ι →₀ ℕ) (hσ : σ ∈ F.support) (i : ι) (hσi : σ i ≠ 0) :
    (F₁ i).coeff (σ i) ≠ 0 := by
  intro H
  have H := HF (rename (↑) ((F₀ i).coeff (σ i))) ?_ ?_
  · have : ((F₀ i).coeff (σ i)).totalDegree + σ i ≤ _ :=
      totalDegree_coeff_optionEquivLeft_add_le _ _ _ (σ i) <| by
        rw [totalDegree_renameEquiv]
        exact (Finsupp.le_degree ..).trans (le_totalDegree hσ)
    rw [totalDegree_renameEquiv] at this
    simpa [hσi] using (this.trans H).trans (totalDegree_rename_le _ _)
  · refine (map_eq_zero_iff _ (rename_injective _ Subtype.val_injective)).not.mpr fun H ↦ ?_
    have : coeff _ ((F₀ i).coeff _) = _ :=
      optionEquivLeft_coeff_coeff _ _ (σ.equivMapDomain (e i)) (renameEquiv k (e i) F)
    rw [renameEquiv_apply, Finsupp.equivMapDomain_eq_mapDomain, coeff_rename_mapDomain _
      (e i).injective, Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Equiv.optionSubtypeNe_none,
      ← renameEquiv_apply, H, coeff_zero, eq_comm, ← notMem_support_iff] at this
    exact this hσ
  · apply_fun Subalgebra.val _ at H
    simp_rw [Polynomial.coe_mapAlgHom, Polynomial.coeff_map, AlgHom.coe_toRingHom, map_zero] at H
    simp_rw [← H, ← AlgHom.comp_apply]
    congr; ext; simp

include hFa HF in
theorem isAlgebraic_of_mem_vars_of_forall_aeval_eq_zero_totalDegree_le (i : ι)
    (hi : i ∈ F.vars) : IsAlgebraic (Algebra.adjoin k (a '' {i}ᶜ)) (a i) := by
  have ⟨σ, hσ, hσi⟩ := (mem_vars i).mp hi
  classical refine ⟨F₁ i, fun h ↦ coeff_aeval_ite_ne_zero_of_forall_aeval_eq_zero_totalDegree_le
    _ _ HF σ hσ i (Finsupp.mem_support_iff.mp hσi) ?_, aeval_ite_aeval_eq_zero _ _ hFa ..⟩
  rw [h, Polynomial.coeff_zero]

include hF0 hFa HF hp H in
theorem exists_mem_support_not_dvd_of_forall_aeval_eq_zero_totalDegree_le :
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

variable [ExpChar k p]

include hp H in
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow
    (s : Set ι) (n : ι) (ha : IsTranscendenceBasis k fun i : s ↦ a i) (hn : n ∉ s) :
    ∃ i : ι, IsTranscendenceBasis k (fun j : ↥(insert n s \ {i}) ↦ a j) ∧
      IsSeparable (adjoin k (a '' (insert n s \ {i}))) (a i) := by
  have ha' : ¬ AlgebraicIndepOn k a (insert n s) := fun h ↦ by
    rw [AlgebraicIndepOn.insert_iff hn, Set.image_eq_range] at h
    exact h.2 (ha.isAlgebraic.isAlgebraic _)
  have HF : {F : MvPolynomial ↥(insert n s) k | F ≠ 0 ∧ MvPolynomial.aeval (a ·.1) F = 0}.Nonempty
    := by simpa [algebraicIndependent_iff, and_comm] using ha'
  let F := totalDegree.argminOn _ HF
  obtain ⟨hF0, hFa⟩ : F ∈ _ := totalDegree.argminOn_mem _ HF
  replace HF f h₁ h₂ := totalDegree.argminOn_le _ (a := f) (.intro h₁ h₂) HF
  -- By the minimality of total degree, `F` is irreducible.
  have hFirr : Irreducible F := irreducible_of_forall_aeval_eq_zero_totalDegree_le _ F hF0 hFa HF
  -- By the minimality of total degree and the linearly independent condition,
  -- there exists some `Xᵢᵈ` with `p ∤ d` appearing in `F`.
  have ⟨i, σ, hσ, hi⟩ := exists_mem_support_not_dvd_of_forall_aeval_eq_zero_totalDegree_le
    p hp _ H F hF0 hFa HF
  have hσi : σ i ≠ 0 := (by simp [·] at hi)
  have alg := isAlgebraic_of_mem_vars_of_forall_aeval_eq_zero_totalDegree_le _ F hFa HF i <|
    (mem_vars i).mpr ⟨σ, hσ, Finsupp.mem_support_iff.mpr hσi⟩
  have eq : (a ·.1) '' {i}ᶜ = a '' (insert n s \ {i.1}) := by
    rw [← Function.comp_def (f := a), Set.image_comp, Set.image_val_compl, Set.image_singleton]
  have Hi := ha.of_isAlgebraic_adjoin_insert_diff s n i a i.2 (eq ▸ alg)
  refine ⟨i, Hi, ?_⟩
  let e' : {j // j ≠ i} ≃ ↥(insert n s \ {i.1}) := ⟨fun x ↦ ⟨x, x.1.2, fun h ↦ x.2 (Subtype.ext h)⟩,
    fun x ↦ ⟨⟨x, x.2.1⟩, fun h ↦ x.2.2 congr($h.1)⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  let e := (Hi.comp_equiv e').1.aevalEquiv.trans <| Subalgebra.equivOfEq _ _ <| congr_arg
    (Algebra.adjoin k) <| (EquivLike.range_comp ..).trans <| (eq.trans (Set.image_eq_range ..)).symm
  classical
  have hF₁irr := hFirr.map (renameEquiv k (Equiv.optionSubtypeNe i).symm)
    |>.map (optionEquivLeft k _) |>.map (Polynomial.mapAlgEquiv e)
  rw [← AlgEquiv.coe_algHom, AlgEquiv.toAlgHom_eq_coe, Polynomial.mapAlgEquiv_toAlgHom e,
    ← AlgEquiv.toAlgHom_eq_coe, show e.toAlgHom = aevalAdjoin (a ·.1) i by ext; simp [e, e']]
    at hF₁irr
  have coeff_ne := coeff_aeval_ite_ne_zero_of_forall_aeval_eq_zero_totalDegree_le _ F HF σ hσ i hσi
  -- By Gauss's lemma, `F` is still irrreducible over `k(x₁,...,xᵢ₋₁, xᵢ₊₁,...,xₙ₊₁)`.
  have := e.uniqueFactorizationMonoid inferInstance
  let k' := adjoin k ((a ·.1) '' {i}ᶜ)
  open scoped algebraAdjoinAdjoin in
  have hF₂irr := (hF₁irr.isPrimitive fun h ↦ coeff_ne <| Polynomial.coeff_eq_zero_of_natDegree_lt <|
    h.trans_lt <| Nat.pos_iff_ne_zero.2 hσi).irreducible_iff_irreducible_map_fraction_map
    (K := k').1 hF₁irr
  -- And by the existence of `Xᵢᵈ` with `p ∤ d`, it is separable.
  contrapose! coeff_ne with Hsep
  rw [← eq] at Hsep
  have instExpChar : ExpChar k' p := expChar_of_injective_algebraMap (algebraMap k k').injective _
  have : CharP k' p := by
    cases instExpChar
    · cases hp.ne_one rfl
    · assumption
  obtain ⟨g, hg, eq⟩ := (((minpoly k' (a i)).separable_or p (minpoly.irreducible
    (isAlgebraic_iff_isIntegral.mp <| isAlgebraic_adjoin_iff.mpr alg))).resolve_left Hsep).2
  replace eq := congr(Polynomial.coeff $eq (σ i))
  rwa [← minpoly.eq_of_irreducible hF₂irr ((Polynomial.aeval_map_algebraMap ..).trans
    (aeval_ite_aeval_eq_zero _ F hFa i)), Polynomial.coeff_mul_C, Polynomial.coeff_expand hp.pos,
    if_neg hi, eq_mul_inv_iff_mul_eq₀ (by simpa using hF₂irr.ne_zero), zero_mul, eq_comm,
    Polynomial.coeff_map, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ..)] at eq

include hp ha ha' H in
open Set in
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
  have ⟨i, hi⟩ := exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow
    p hp a H {n}ᶜ n ha' (· rfl)
  rw [compl_eq_univ_diff, insert_diff_self_of_mem (mem_univ _), ← compl_eq_univ_diff] at hi
  refine ⟨i, hi.1, ?_⟩
  rw [← separableClosure.eq_top_iff, ← (restrictScalars_injective k).eq_iff,
    restrictScalars_top, eq_top_iff, ← ha, adjoin_le_iff]
  rintro _ ⟨x, rfl⟩
  obtain rfl | ne := eq_or_ne x i
  · exact hi.2
  · exact isSeparable_algebraMap (F := adjoin k (a '' {i}ᶜ)) ⟨_, subset_adjoin _ _ ⟨x, ne, rfl⟩⟩

include hp H in
/--
Suppose `k` has chararcteristic `p` and `K/k` is finitely generated.
Suppose furthermore that if `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
`{ sᵢᵖ } ⊆ K` is also `k`-linearly independent (which is true when `K ⊗ₖ k^{1/p}` is reduced).

Then `K/k` is finite separably generated.

TODO: show that this is an if and only if.
-/
@[stacks 030W "(2) ⇒ (1) finitely genenerated case"]
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_fg
    (Hfg : FG (F := k) (E := K) ⊤) :
    ∃ s : Finset K, IsTranscendenceBasis k ((↑) : s → K) ∧
      Algebra.IsSeparable (adjoin k (s : Set K)) K := by
  have ⟨t, ht⟩ := Hfg
  let sc (t : Set K) := (separableClosure (adjoin k t) K).restrictScalars k
  have incl (t : Set K) : t ⊆ sc t := fun x hx ↦
    isSeparable_algebraMap (F := adjoin k t) ⟨x, subset_adjoin _ _ hx⟩
  have : Algebra.IsAlgebraic (Algebra.adjoin k t.toSet) K := by
    rw [← isAlgebraic_adjoin_iff_top, ht, Algebra.isAlgebraic_iff_isIntegral]
    exact Algebra.isIntegral_of_surjective fun x ↦ ⟨⟨x, ⟨⟩⟩, rfl⟩
  classical
  have h := (t.finite_toSet.powerset.inter_of_left {s | IsTranscendenceBasis k ((↑) : s → K)}
      |>.image sc).wellFoundedOn (r := (· > ·)).has_min Set.univ <|
    have ⟨s, hs⟩ := exists_isTranscendenceBasis_subset (R := k) (s := t.toSet)
    ⟨⟨_, (t.finite_toSet.subset hs.1).toFinset, by simp [hs], rfl⟩, ⟨⟩⟩
  obtain ⟨⟨_, s, ⟨hst, hs⟩, rfl⟩, -, Hs⟩ := h
  have fin := t.finite_toSet.subset hst
  refine ⟨fin.toFinset, by rwa [← fin.coe_toFinset] at hs, ?_⟩
  rw [fin.coe_toFinset, ← separableClosure.eq_top_iff,
    ← (restrictScalars_injective k).eq_iff, restrictScalars_top, eq_top_iff, ← ht, adjoin_le_iff]
  by_contra!
  obtain ⟨n, hnt, hn⟩ := Set.not_subset.mp this
  have hns : n ∉ s := (hn <| incl s ·)
  have ⟨i, hi₁, hi₂⟩ := exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow
    p hp id H s n hs hns
  refine Hs ⟨_, _, ⟨?_, hi₁.to_subtype_range⟩, rfl⟩ ⟨⟩ ?_
  · rintro _ ⟨x, rfl⟩; exact Set.insert_subset hnt hst x.2.1
  rw [Set.image_id] at hi₂
  simp_rw [id_eq, Subrel, Order.Preimage, Subtype.range_val]
  rw [GT.gt, SetLike.lt_iff_le_and_exists]
  refine ⟨?_, n, incl _ ⟨.inl rfl, ?_⟩, hn⟩
  · rw [separableClosure_le_separableClosure_iff, adjoin_le_iff]
    intro x hx
    obtain rfl | ne := eq_or_ne x i
    · exact hi₂
    · refine incl _ ⟨.inr hx, ne⟩
  · rintro rfl; exact hn (by rwa [Set.insert_diff_self_of_notMem hns] at hi₂)

end
