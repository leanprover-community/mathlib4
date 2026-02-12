/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Group.Irreducible.Indecomposable
public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-!
# Existence of bases for crystallographic root systems

## Main results:
 * `RootPairing.Base.mk'`: an alternate constructor for `RootPairing.Base` which demands the axioms
   for roots but not for coroots.
 * `RootPairing.nonempty_base`: base existence proof for reduced crystallographic root systems.

## Implementation details

The proof needs a set of ordered coefficients, even though the ultimate existence statement does
not. There are at least two ways to deal with this:
 (a) Using the fact that a crystallographic root system induces a `ℚ`-structure, pass to the root
     system over `ℚ` defined by `RootPairing.restrictScalarsRat`, and develop a theory of base
     change for root system bases.
 (b) Introduce a second set of ordered coefficients (ultimately taken to be `ℚ`) and develop a
     theory with two sets of coefficients simultaneously in play.

It is not really clear which is the better approach but here we opt for approach (b) as it seems
to yield slightly more general results.

-/

@[expose] public section

open Function IsAddIndecomposable Module Set Submodule

namespace RootPairing

variable {ι R M N : Type*} [Finite ι] [AddCommGroup M] [AddCommGroup N]

section CommRing

variable [CommRing R] [Module R M] [Module R N] (P : RootPairing ι R M N)
  {S : Type*} [LinearOrder S] [AddCommGroup S] [IsOrderedAddMonoid S] (f : M →+ S)

/-- This is [serre1965](Ch. V, §9, Lemma 3). -/
lemma baseOf_pairwise_pairing_le_zero [CharZero R] [IsDomain R] [P.IsCrystallographic]
    (hf : ∀ i, f (P.root i) ≠ 0) :
    (baseOf P.root f).Pairwise fun i j ↦ P.pairingIn ℤ i j ≤ 0 := by
  letI _i := P.indexNeg
  intro i hi j hj hne
  have := IsAddIndecomposable.pairwise_baseOf_sub_notMem P.root (by simp) f hf hi hj hne
  contrapose! this
  exact P.root_sub_root_mem_of_pairingIn_pos this hne

/-- This lemma is usually established for root systems with coefficients `R` equal to `ℚ` or `ℝ`, in
which case one may take `S = R`. However our statement allows for more general coefficients such as
`R = ℂ` and `S = ℚ`.

This lemma is mostly a stepping stone en route to `RootPairing.linearIndepOn_root_baseOf` (where
linear independence is established over `R` rather than just `S`) except that this version does not
make the field assumption and so covers the case `S = R = ℤ` which the latter does not. -/
lemma linearIndepOn_root_baseOf' [IsDomain R] {S : Type*}
    [LinearOrder S] [CommRing S] [IsStrictOrderedRing S] [Algebra S R] [FaithfulSMul S R]
    [Module S M] [IsScalarTower S R M] [Module S N] [IsScalarTower S R N]
    [P.IsValuedIn S] [P.IsCrystallographic]
    (f : Dual S M) (hf : ∀ i, f (P.root i) ≠ 0) :
    LinearIndepOn S P.root (baseOf P.root (f : M →+ S)) := by
  have : CharZero R := Algebra.charZero_of_charZero S R
  have : Fintype ι := Fintype.ofFinite ι
  let M₀ := span S (range P.root)
  let v (i : baseOf P.root (f : M →+ S)) : M₀ := P.rootSpanMem S i
  change LinearIndependent S (M₀.subtype ∘ v)
  suffices LinearIndependent S v by
    rwa [LinearMap.linearIndependent_iff_of_disjoint M₀.subtype (by simp)]
  let f' : Dual S M₀ := f ∘ₗ M₀.subtype
  obtain ⟨B, hB⟩ : ∃ B : P.RootPositiveForm S, B.posForm.toQuadraticMap.PosDef :=
    ⟨P.posRootForm S, by simpa using P.posRootForm_rootFormIn_posDef S⟩
  have hp (i : baseOf P.root (f : M →+ S)) : 0 < f' (v i) := by obtain ⟨i, -, hi⟩ := i; simpa
  have hn : Pairwise fun (i j : baseOf P.root (f : M →+ S)) ↦ B.posForm (v i) (v j) ≤ 0 := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
    rw [B.posForm_apply_root_root_le_zero_iff, ← P.algebraMap_pairingIn' S ℤ]
    simpa using P.baseOf_pairwise_pairing_le_zero _ hf (by simpa) (by simpa) (by aesop : i ≠ j)
  exact LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero B.posForm hB f' v hp hn

lemma ncard_eq_finrank_of_linearIndepOn_of [P.IsRootSystem] [Nontrivial R]
    {s : Set ι}
    (hli : LinearIndepOn R P.root s)
    (hsp : ∀ i, P.root i ∈ AddSubmonoid.closure (P.root '' s) ∨
               -P.root i ∈ AddSubmonoid.closure (P.root '' s)) :
    s.ncard = finrank R M := by
  let b : Basis s R M := Basis.mk hli <| by
    rw [← IsRootSystem.span_root_eq_top (P := P), span_le, ← span_span_of_tower (R := ℤ)]
    rintro - ⟨i, rfl⟩
    apply subset_span
    rcases hsp i with hi | hi <;>
      simpa [SetLike.mem_coe, ← Submodule.mem_toAddSubgroup, span_int_eq_addSubgroupClosure,
        ← image_eq_range] using AddSubgroup.le_closure_toAddSubmonoid (P.root '' s) hi
  have _i : Fintype s := Fintype.ofFinite s
  rw [ncard_eq_toFinset_card]
  simpa using (finrank_eq_card_basis b).symm

end CommRing

section Field

variable [Field R] [CharZero R] [Module R M] [Module R N] (P : RootPairing ι R M N)
  [P.IsRootSystem] [P.IsCrystallographic]

lemma linearIndepOn_root_baseOf (f : M →+ ℚ) (hf : ∀ i, f (P.root i) ≠ 0) :
    LinearIndepOn R P.root (baseOf P.root f) := by
  let _i : Module ℚ M := Module.compHom M (algebraMap ℚ R)
  let _i : Module ℚ N := Module.compHom N (algebraMap ℚ R)
  letI := P.indexNeg
  have : Fintype (baseOf P.root f) := Fintype.ofFinite _
  let v (i : baseOf P.root f) : P.rootSpan ℚ := P.rootSpanMem ℚ i
  change LinearIndependent R ((P.rootSpan ℚ).subtype ∘ v)
  have h_span : span ℚ (range v) = ⊤ := by
    suffices span ℚ (range v) = span ℚ (range (P.rootSpanMem ℚ)) by
      rw [this, eq_top_iff, ← (P.rootSpan ℚ).subtype.map_le_map_iff' (by simp), map_span,
        ← image_univ, ← image_comp]
      simp
    apply le_antisymm (span_mono fun x i ↦ by aesop) (span_le.mpr ?_)
    rintro - ⟨i, rfl⟩
    suffices (P.rootSpanMem ℚ i : M) ∈ span ℚ (P.root '' baseOf P.root f) by
      rw [← (injective_subtype (P.rootSpan ℚ)).mem_set_image, ← map_coe, SetLike.mem_coe, map_span,
        ← image_univ, ← image_comp]
      convert this
      aesop
    rw [← span_span_of_tower ℤ, ← Submodule.coe_toAddSubgroup, span_int_eq_addSubgroupClosure,
      AddSubgroup.closure_image_isAddIndecomposable_baseOf P.root (by simp) f (by simpa)]
    exact subset_span <| AddSubgroup.subset_closure <| by simp
  have h_card : Nat.card (baseOf P.root f) = finrank R M := by
    let b : Basis (baseOf P.root f) ℚ (P.rootSpan ℚ) := by
      replace this : LinearIndependent ℚ v :=
        .of_comp (P.rootSpan ℚ).subtype <| P.linearIndepOn_root_baseOf' f.toRatLinearMap hf
      exact Basis.mk this (by rw [h_span])
    rw [← RootPairing.finrank_rootSpanIn ℚ P, finrank_eq_nat_card_basis b]
  replace h_span : span R (range <| (P.rootSpan ℚ).subtype ∘ v) = ⊤ := by
    rw [range_comp, ← span_span_of_tower ℚ, span_image, h_span]
    simp
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, h_span, finrank_top, ← h_card,
    Fintype.card_eq_nat_card]

lemma eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure
    (s : Set ι)
    (hli : LinearIndepOn R P.root s)
    (hsp : ∀ i, P.root i ∈ AddSubmonoid.closure (P.root '' s) ∨
               -P.root i ∈ AddSubmonoid.closure (P.root '' s))
    (f : M →+ ℚ) (hf : ∀ i ∈ s, f (P.root i) = 1) :
    s = baseOf P.root f := by
  letI _i := P.indexNeg
  have h_card : (baseOf P.root f).ncard = s.ncard := by
    have hf' (i : ι) : f (P.root i) ≠ 0 := AddSubmonoid.apply_ne_zero_of_mem_or_neg_mem_closure
      P.root f s (by aesop) i (P.ne_zero i) (by simp) (hsp i)
    have aux (i : ι) := mem_or_neg_mem_closure_baseOf P.root f i (hf' i) (by simp)
    rw [P.ncard_eq_finrank_of_linearIndepOn_of hli hsp, P.ncard_eq_finrank_of_linearIndepOn_of
      (P.linearIndepOn_root_baseOf f hf') aux]
  suffices s ⊆ baseOf P.root f from eq_of_subset_of_ncard_le this (by rw [h_card])
  replace hsp (i : ι) : ∃ z : ℤ, f (P.root i) = z := by
    rcases hsp i with hi | hi
    · exact AddSubmonoid.closure_induction (fun x ⟨j, hj, hx⟩ ↦ ⟨1, by simp [hf _ hj, ← hx]⟩)
        ⟨0, by simp⟩ (fun x y hx hy ⟨n, hn⟩ ⟨m, hm⟩ ↦ ⟨n + m, by simp [hn, hm]⟩) hi
    · suffices ∃ z : ℤ, f (P.root (-i)) = z by obtain ⟨z, hz⟩ := this; exact ⟨-z, by simp [← hz]⟩
      replace hi : P.root (-i) ∈ AddSubmonoid.closure (P.root '' s) := by simpa
      exact AddSubmonoid.closure_induction (fun x ⟨j, hj, hx⟩ ↦ ⟨1, by simp [hf _ hj, ← hx]⟩)
        ⟨0, by simp⟩ (fun x y hx hy ⟨n, hn⟩ ⟨m, hm⟩ ↦ ⟨n + m, by simp [hn, hm]⟩) hi
  refine fun i hi ↦ ⟨by aesop, fun j hj k hk contra ↦ ?_⟩
  obtain ⟨n, hn⟩ := hsp j
  obtain ⟨m, hm⟩ := hsp k
  replace hj : 0 < n := by simpa [hn] using hj
  replace hk : 0 < m := by simpa [hm] using hk
  replace contra : 1 = n + m := by
    replace contra := congr(f $contra)
    rwa [hf i hi, map_add, hn, hm, ← Int.cast_add, ← Int.cast_one, Int.cast_inj] at contra
  lia

lemma eq_baseOf_iff (s : Set ι) (f : M →+ ℚ)
    (hf : ∀ i ∈ s, f (P.root i) = 1) (hf' : ∀ i, f (P.root i) ≠ 0) :
    s = baseOf P.root f ↔
      LinearIndepOn R P.root s ∧
        ∀ i, P.root i ∈ AddSubmonoid.closure (P.root '' s) ∨
            -P.root i ∈ AddSubmonoid.closure (P.root '' s) := by
  letI := P.indexNeg
  refine ⟨?_, fun ⟨hli, sp⟩ ↦ P.eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure s hli sp f hf⟩
  rintro rfl
  exact ⟨P.linearIndepOn_root_baseOf f hf', fun i ↦
    mem_or_neg_mem_closure_baseOf P.root f i (by aesop) (by simp)⟩

variable [P.IsReduced]

private lemma baseOf_root_eq_baseOf_coroot_aux
    (f : M →+ ℚ) (g : N →+ ℚ) (hf : ∀ i, f (P.root i) ≠ 0)
    (hfg : ∀ i, 0 < f (P.root i) ↔ 0 < g (P.coroot i)) :
    baseOf P.root f ⊆ baseOf P.coroot (g : N →+ ℚ) := by
  classical
  have _i : Fintype ι := Fintype.ofFinite _
  let _i : Module ℚ M := Module.compHom M (algebraMap ℚ R)
  let s := baseOf P.root f
  refine fun i hi ↦ ⟨by obtain ⟨hi, -⟩ := hi; aesop, fun j hj k hk contra ↦ ?_⟩
  suffices i = j by grind
  obtain ⟨u, hu, v, hv, huv⟩ : ∃ᵉ (u > (0 : ℚ)) (v > (0 : ℚ)),
      P.root i = u • P.root j + v • P.root k := by
    let l (i : ι) := P.RootFormIn ℚ (P.rootSpanMem ℚ i) (P.rootSpanMem ℚ i)
    have hl (i : ι) : 0 < l i := by
      simpa only [l, ← posRootForm_eq] using RootPositiveForm.zero_lt_posForm_apply_root _ _
    refine ⟨l i / l j, by simp [hl], l i / l k, by simp [hl], ?_⟩
    simp only [P.coroot_eq_polarizationEquiv_apply_root, ← map_smul, ← map_add,
      P.PolarizationEquiv.injective.eq_iff] at contra
    let l' (i : ι) := P.RootForm (P.root i) (P.root i)
    have hll' (i : ι) : l i = l' i := P.algebraMap_rootFormIn ℚ _ _
    change (2 / l' i) • P.root i = (2 / l' j) • P.root j + (2 / l' k) • P.root k at contra
    replace contra := congr_arg ((2 / l' i)⁻¹ • ·) contra
    have aux₁ : 2 / l' i ≠ 0 := by simpa using IsAnisotropic.rootForm_root_ne_zero i
    have aux₂ (j : ι) : (2 / l' i)⁻¹ * (2 / l' j) = l i / l j := by ring_nf; simp [hll']
    simp only [smul_add, smul_smul, inv_mul_cancel₀ aux₁, aux₂, one_smul] at contra
    rw [contra]
    module
  have hjk {l : ι} (hl : 0 < g (P.coroot l)) :
      ∃ c : P.root '' s → ℕ, ∑ x, c x • (x : M) = P.root l := by
    rwa [← Submodule.mem_span_iff_of_fintype, ← mem_toAddSubmonoid, span_nat_eq_addSubmonoidClosure,
      AddSubmonoid.closure_image_isAddIndecomposable_baseOf,
      AddSubmonoid.mem_closure_image_pos_iff P.root f _ (P.ne_zero _), hfg]
  obtain ⟨a, ha⟩ : ∃ c : P.root '' s → ℕ, ∑ x, c x • (x : M) = P.root j := hjk hj
  obtain ⟨b, hb⟩ : ∃ d : P.root '' s → ℕ, ∑ x, d x • (x : M) = P.root k := hjk hk
  let ri : P.root '' s := ⟨P.root i, mem_image_of_mem _ hi⟩
  replace huv : u • (Nat.cast ∘ a) + v • (Nat.cast (R := ℚ) ∘ b) = Pi.single ri 1 := by
    simp_rw [← ha, ← hb, Finset.smul_sum, ← Finset.sum_add_distrib, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul, ← add_smul] at huv
    have aux : P.root i = ∑ x, Pi.single (M := fun x : P.root '' s ↦ ℚ) ri 1 x • (x : M) := by
      simp [ri]
    rw [eq_comm, aux] at huv
    have hli : LinearIndepOn ℚ id (P.root '' s) := by
      rw [← linearIndepOn_iff_image P.root.injective.injOn]
      exact (linearIndepOn_root_baseOf P f hf).restrict_scalars' ℚ
    rw [← linearIndependent_subtype_iff] at hli
    exact linearIndependent_iff_injective_fintypeLinearCombination.mp hli huv
  obtain ⟨q, hq, hq'⟩ : ∃ q > (0 : ℚ), P.root j = q • P.root i := by
    suffices P.root j = (a ri : ℚ) • P.root i by
      refine ⟨a ri, ?_, this⟩
      by_contra contra
      replace contra : a ri = 0 := by simpa using contra
      simp [contra, P.ne_zero j] at this
    have (x : P.root '' s) (hx : x ≠ ri) : a x = 0 := by
      replace huv : u * ↑(a x) + v * ↑(b x) = 0 := by simpa [hx] using congr($huv x)
      suffices u * (a x) = 0 by simpa [hu.ne'] using this
      have : 0 ≤ u * (a x) := by positivity
      have : 0 ≤ v * (b x) := by positivity
      grind
    replace this (x : P.root '' s) (hx : a x • (x : M) ≠ 0) :  x ∈ ({ri} : Finset _) := by
      rw [Finset.mem_singleton]
      by_contra! contra
      simp [this x contra] at hx
    simp [← ha, ← Fintype.sum_subset this, ri, Nat.cast_smul_eq_nsmul]
  have hij : ¬ LinearIndependent R ![P.root i, P.root j] := by
    simp_rw [LinearIndependent.pair_iff, not_forall]
    exact ⟨q, -1, by simp [Rat.cast_smul_eq_qsmul, hq'], by simp⟩
  rcases IsReduced.eq_or_eq_neg i j hij with hij | hij
  · simpa using hij
  · obtain ⟨rfl⟩ : q = -1 := smul_left_injective ℚ (P.ne_zero j) <| by
      simp_rw [neg_smul, ← neg_eq_iff_eq_neg, ← smul_neg, ← hij, one_smul, hq']
    lia

lemma baseOf_root_eq_baseOf_coroot
    (f : M →+ ℚ) (hf : ∀ i, f (P.root i) ≠ 0)
    (g : N →+ ℚ) (hg : ∀ i, g (P.coroot i) ≠ 0)
    (hfg : ∀ i, 0 < f (P.root i) ↔ 0 < g (P.coroot i)) :
    baseOf P.root f = baseOf P.coroot (g : N →+ ℚ) :=
  subset_antisymm (P.baseOf_root_eq_baseOf_coroot_aux f g hf hfg)
    (P.flip.baseOf_root_eq_baseOf_coroot_aux g f hg (by aesop))

/-- This is really just an auxiliary result en route to `RootPairing.Base.mk'`. -/
lemma coroot_mem_or_neg_mem_closure_of_root (s : Set ι)
    (hli : LinearIndepOn R P.root s)
    (hsp : ∀ i, P.root i ∈ AddSubmonoid.closure (P.root '' s) ∨
               -P.root i ∈ AddSubmonoid.closure (P.root '' s))
    (i : ι) :
     P.coroot i ∈ AddSubmonoid.closure (P.coroot '' s) ∨
    -P.coroot i ∈ AddSubmonoid.closure (P.coroot '' s) := by
  letI _i := P.indexNeg
  letI _i : Fintype ι := Fintype.ofFinite ι
  let _i : Module ℚ M := Module.compHom M (algebraMap ℚ R)
  let _i : Module ℚ N := Module.compHom N (algebraMap ℚ R)
  obtain ⟨f, hf'⟩ := exists_dual_forall_apply_eq_one (hli.restrict_scalars' ℚ)
  have hf := P.eq_baseOf_of_linearIndepOn_of_mem_or_neg_mem_closure s hli hsp f hf'
  have hf₀ (i : ι) : f (P.root i) ≠ 0 :=
    AddSubmonoid.apply_ne_zero_of_mem_or_neg_mem_closure P.root (f : M →+ ℚ) s (by aesop) i
      (P.ne_zero i) (by simp) (hsp i)
  have aux (i : ι) : ∃ q : ℚ, 0 < q ∧ q = 2 / P.RootForm (P.root i) (P.root i) := by
    refine ⟨2 / P.RootFormIn ℚ (P.rootSpanMem ℚ i) (P.rootSpanMem ℚ i), ?_, ?_⟩
    · simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, ← posRootForm_eq]
      exact (P.posRootForm ℚ).zero_lt_posForm_apply_root i (P.rootSpanMem ℚ i).property
    · simp [← P.algebraMap_rootFormIn ℚ (P.rootSpanMem ℚ i) (P.rootSpanMem ℚ i)]
  let g : Dual ℚ N := f ∘ₗ (P.PolarizationEquiv.symm.restrictScalars ℚ).toLinearMap
  have hg₀ (i : ι) : g (P.coroot i) ≠ 0 := by
    obtain ⟨q, hq₀, hq⟩ := aux i
    simp [g, coroot_eq_polarizationEquiv_apply_root, ← hq, Rat.cast_smul_eq_qsmul, hq₀.ne', hf₀ i]
  have hg (i : ι) : 0 < g (P.coroot i) ↔ 0 < f (P.root i) := by
    obtain ⟨q, hq₀, hq⟩ := aux i
    simp [g, coroot_eq_polarizationEquiv_apply_root, ← hq, Rat.cast_smul_eq_qsmul, hq₀]
  rw [hf, P.baseOf_root_eq_baseOf_coroot f hf₀ g hg₀ (fun i ↦ (hg i).symm)]
  exact mem_or_neg_mem_closure_baseOf P.coroot (g : N →+ ℚ) i (hg₀ i) (by simp)

/-- An alternate constructor for `RootPairing.Base` which demands the axioms for roots but not for
coroots. -/
noncomputable def Base.mk' (s : Set ι)
    (hli : LinearIndepOn R P.root s)
    (hsp : ∀ i, P.root i ∈ AddSubmonoid.closure (P.root '' s) ∨
               -P.root i ∈ AddSubmonoid.closure (P.root '' s)) :
    P.Base where
  support := (toFinite s).toFinset
  linearIndepOn_root := by simpa
  linearIndepOn_coroot := by have : Fintype ι := Fintype.ofFinite ι; simpa
  root_mem_or_neg_mem i := by simpa using hsp i
  coroot_mem_or_neg_mem i := by simpa using coroot_mem_or_neg_mem_closure_of_root P s hli hsp i

lemma nonempty_base : Nonempty P.Base := by
  let _i : Module ℚ M := Module.compHom M (algebraMap ℚ R)
  let _i : Module ℚ N := Module.compHom N (algebraMap ℚ R)
  obtain ⟨f, hf⟩ : ∃ f : Dual ℚ M, ∀ i, f (P.root i) ≠ 0 :=
    exists_dual_forall_apply_ne_zero P.root <| by simp [P.ne_zero]
  letI := P.indexNeg
  exact ⟨Base.mk' P (baseOf P.root (f : M →+ ℚ)) (P.linearIndepOn_root_baseOf f hf)
    (fun i ↦ mem_or_neg_mem_closure_baseOf P.root (f : M →+ ℚ) i (hf i) (by simp))⟩

end Field

end RootPairing
