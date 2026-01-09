/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Group.Irreducible.Indecomposable
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-!
# Existence of bases for crystallographic root systems

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

## TODO

1. Prove that for crystallographic reduced root systems, the axiom `coroot_mem_or_neg_mem` appearing
   in `RootPairing.Base` follows from the others, and combine this with
   `RootPairing.linearIndepOn_coroot_iff` to thus provide an alternate constructor for
   `RootPairing.Base` which demands only the hypotheses on the roots.
2. [Easy given 1 above] Prove that every reduced crystallographic root system has a base by
   combining the constructor in 1 above with `RootPairing.linearIndepOn_root_baseOf`,
   `IsAddIndecomposable.mem_or_neg_mem_closure_baseOf`, `Module.exists_dual_forall_apply_ne_zero`.

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

end CommRing

section Field

variable [Field R] [CharZero R] [Module R M] [Module R N] (P : RootPairing ι R M N)
  [P.IsRootSystem] [P.IsCrystallographic]

lemma linearIndepOn_root_baseOf [Module ℚ M] [Module ℚ N]
    (f : Dual ℚ M) (hf : ∀ i, f (P.root i) ≠ 0) :
    LinearIndepOn R P.root (baseOf P.root (f : M →+ ℚ)) := by
  letI := P.indexNeg
  have : Fintype (baseOf P.root (f : M →+ ℚ)) := Fintype.ofFinite _
  let v (i : baseOf P.root (f : M →+ ℚ)) : P.rootSpan ℚ := P.rootSpanMem ℚ i
  change LinearIndependent R ((P.rootSpan ℚ).subtype ∘ v)
  have h_span : span ℚ (range v) = ⊤ := by
    suffices span ℚ (range v) = span ℚ (range (P.rootSpanMem ℚ)) by
      rw [this, eq_top_iff, ← LinearMap.map_le_map_iff' (f := (P.rootSpan ℚ).subtype) (by simp),
        map_span, ← image_univ, ← image_comp]
      simp
    apply le_antisymm (span_mono fun x i ↦ by aesop) (span_le.mpr ?_)
    rintro - ⟨i, rfl⟩
    suffices (P.rootSpanMem ℚ i : M) ∈ span ℚ (P.root '' baseOf P.root (f : M →+ ℚ)) by
      rw [← (injective_subtype (P.rootSpan ℚ)).mem_set_image, ← map_coe, SetLike.mem_coe, map_span,
        ← image_univ, ← image_comp]
      convert this
      aesop
    rw [← span_span_of_tower ℤ, ← Submodule.coe_toAddSubgroup, span_int_eq_addSubgroupClosure,
      AddSubgroup.closure_image_isAddIndecomposable_baseOf P.root (by simp) (f : M →+ ℚ) (by simpa)]
    exact subset_span <| AddSubgroup.subset_closure <| by simp
  have h_card : Nat.card (baseOf P.root (f : M →+ ℚ)) = finrank R M := by
    let b : Basis (baseOf P.root (f : M →+ ℚ)) ℚ (P.rootSpan ℚ) := by
      replace this : LinearIndependent ℚ v :=
        .of_comp (P.rootSpan ℚ).subtype <| P.linearIndepOn_root_baseOf' f hf
      exact Basis.mk this (by rw [h_span])
    rw [← RootPairing.finrank_rootSpanIn ℚ P, finrank_eq_nat_card_basis b]
  have hv : span R (range <| (P.rootSpan ℚ).subtype ∘ v) = ⊤ := by
    rw [range_comp, ← span_span_of_tower ℚ, span_image, h_span]
    simp
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hv, finrank_top, ← h_card,
    Fintype.card_eq_nat_card]

/-- A set of linearly independent roots whose cone span over `ℕ` contains all the roots is a basis
for the ambient space. -/
noncomputable def basisOfBase
    (s : Set ι)
    (hli : LinearIndepOn R P.root s)
    (hsp : ∀ i, P.root i ∈ AddSubmonoid.closure (P.root '' s) ∨
               -P.root i ∈ AddSubmonoid.closure (P.root '' s)) :
    Basis s R M := Basis.mk hli <| by
      rw [← IsRootSystem.span_root_eq_top (P := P), span_le, ← span_span_of_tower (R := ℤ)]
      rintro - ⟨i, rfl⟩
      apply subset_span
      rcases hsp i with hi | hi <;>
        simpa [SetLike.mem_coe, ← Submodule.mem_toAddSubgroup, span_int_eq_addSubgroupClosure,
          ← image_eq_range] using AddSubgroup.le_closure_toAddSubmonoid (P.root '' s) hi

lemma exists_dual_baseOf_eq [Module ℚ M] [Module ℚ N]
    (s : Set ι)
    (hli : LinearIndepOn R P.root s)
    (hsp : ∀ i, P.root i ∈ AddSubmonoid.closure (P.root '' s) ∨
               -P.root i ∈ AddSubmonoid.closure (P.root '' s)) :
    ∃ f : Dual ℚ M, baseOf P.root (f : M →+ ℚ) = s ∧ ∀ i ∈ s, f (P.root i) = 1 := by
  classical
  have _i : Fintype ι := Fintype.ofFinite _
  letI _i := P.indexNeg
  obtain ⟨f, hf⟩ : ∃ f : Dual ℚ M, ∀ i ∈ s, f (P.root i) = 1 := by
    replace hli : LinearIndepOn ℚ id (P.root '' s) :=
      LinearIndepOn.id_image (hli.restrict_scalars' ℚ)
    let b : Basis _ ℚ M := .mk (hli.linearIndepOn_extend (subset_univ _)) <| by
      simpa using hli.span_extend_eq_span <| subset_univ _
    refine ⟨b.constr ℚ 1, fun i hi ↦ ?_⟩
    replace hi : P.root i ∈ hli.extend (subset_univ _) :=
      hli.subset_extend _ <| mem_image_of_mem P.root hi
    let ri : hli.extend (subset_univ _) := ⟨P.root i, hi⟩
    have : b ri = P.root i := by simp [b, ri]
    simp [← this]
  refine ⟨f, ?_, hf⟩
  have h_card : (baseOf P.root (f : M →+ ℚ)).ncard = s.ncard := by
    have hf' (i : ι) : f (P.root i) ≠ 0 := AddSubmonoid.apply_ne_zero_of_mem_or_neg_mem_closure
      P.root (fun i ↦ P.ne_zero i) (by simp) (f : M →+ ℚ) s hsp (by aesop) i
    set b₁ := P.basisOfBase s hli hsp
    set b₂ := P.basisOfBase (baseOf P.root (f : M →+ ℚ)) (P.linearIndepOn_root_baseOf f hf')
      (mem_or_neg_mem_closure_baseOf P.root (by simp) (f : M →+ ℚ) hf')
    rw [ncard_eq_toFinset_card, ncard_eq_toFinset_card]
    simpa [Module.finrank_eq_card_basis b₂] using Module.finrank_eq_card_basis b₁
  suffices s ⊆ baseOf P.root (f : M →+ ℚ) from (eq_of_subset_of_ncard_le this (by rw [h_card])).symm
  replace hsp (i : ι) : ∃ z : ℤ, f (P.root i) = z := by
    rcases hsp i with hi | hi
    · exact AddSubmonoid.closure_induction (fun x ⟨j, hj, hx⟩ ↦ ⟨1, by simp [hf _ hj, ← hx]⟩)
        ⟨0, by simp⟩ (fun x y hx hy ⟨n, hn⟩ ⟨m, hm⟩ ↦ ⟨n + m, by simp [hn, hm]⟩) hi
    · suffices ∃ z : ℤ, f (P.root (-i)) = z by obtain ⟨z, hz⟩ := this; exact ⟨-z, by simp [← hz]⟩
      replace hi : P.root (-i) ∈ AddSubmonoid.closure (P.root '' s) := by simpa
      exact AddSubmonoid.closure_induction (fun x ⟨j, hj, hx⟩ ↦ ⟨1, by simp [hf _ hj, ← hx]⟩)
        ⟨0, by simp⟩ (fun x y hx hy ⟨n, hn⟩ ⟨m, hm⟩ ↦ ⟨n + m, by simp [hn, hm]⟩) hi
  intro i hi
  refine ⟨by aesop, fun j hj k hk contra ↦ ?_⟩
  obtain ⟨n, hn⟩ := hsp j
  obtain ⟨m, hm⟩ := hsp k
  replace hj : 0 < n := by simpa [hn] using hj
  replace hk : 0 < m := by simpa [hm] using hk
  replace contra : 1 = n + m := by
    replace contra := congr(f $contra)
    rwa [hf i hi, map_add, hn, hm, ← Int.cast_add, ← Int.cast_one, Int.cast_inj] at contra
  lia

end Field

end RootPairing
