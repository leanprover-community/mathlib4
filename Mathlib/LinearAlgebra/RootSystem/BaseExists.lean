/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Group.Irreducible.Indecomposable
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import Mathlib.LinearAlgebra.RootSystem.Base

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

end Field

end RootPairing
