/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.split_simplicial_object
! leanprover-community/mathlib commit 31019c2504b17f85af7e0577585fad996935a317
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.SplitSimplicialObject
import Mathbin.AlgebraicTopology.DoldKan.Degeneracies
import Mathbin.AlgebraicTopology.DoldKan.FunctorN

/-!

# Split simplicial objects in preadditive categories

In this file we define a functor `nondeg_complex : simplicial_object.split C ⥤ chain_complex C ℕ`
when `C` is a preadditive category with finite coproducts, and get an isomorphism
`to_karoubi_nondeg_complex_iso_N₁ : nondeg_complex ⋙ to_karoubi _ ≅ forget C ⋙ dold_kan.N₁`.
-/


noncomputable section

open
  CategoryTheory CategoryTheory.Limits CategoryTheory.Category CategoryTheory.Preadditive CategoryTheory.Idempotents Opposite AlgebraicTopology AlgebraicTopology.DoldKan

open BigOperators Simplicial DoldKan

namespace SimplicialObject

namespace Splitting

variable {C : Type _} [Category C] [HasFiniteCoproducts C] {X : SimplicialObject C}
  (s : Splitting X)

/-- The projection on a summand of the coproduct decomposition given
by a splitting of a simplicial object. -/
def πSummand [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    X.obj Δ ⟶ s.n A.1.unop.len :=
  by
  refine' (s.iso Δ).inv ≫ sigma.desc fun B => _
  by_cases B = A
  ·
    exact
      eq_to_hom
        (by
          subst h
          rfl)
  · exact 0
#align simplicial_object.splitting.π_summand SimplicialObject.Splitting.πSummand

@[simp, reassoc.1]
theorem ι_πSummand_eq_id [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    s.ιSummand A ≫ s.πSummand A = 𝟙 _ :=
  by
  dsimp [ι_summand, π_summand]
  simp only [summand, assoc, is_iso.hom_inv_id_assoc]
  erw [colimit.ι_desc, cofan.mk_ι_app]
  dsimp
  simp only [eq_self_iff_true, if_true]
#align simplicial_object.splitting.ι_π_summand_eq_id SimplicialObject.Splitting.ι_πSummand_eq_id

@[simp, reassoc.1]
theorem ι_πSummand_eq_zero [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A B : IndexSet Δ)
    (h : B ≠ A) : s.ιSummand A ≫ s.πSummand B = 0 :=
  by
  dsimp [ι_summand, π_summand]
  simp only [summand, assoc, is_iso.hom_inv_id_assoc]
  erw [colimit.ι_desc, cofan.mk_ι_app]
  apply dif_neg
  exact h.symm
#align simplicial_object.splitting.ι_π_summand_eq_zero SimplicialObject.Splitting.ι_πSummand_eq_zero

variable [Preadditive C]

theorem decomposition_id (Δ : SimplexCategoryᵒᵖ) :
    𝟙 (X.obj Δ) = ∑ A : IndexSet Δ, s.πSummand A ≫ s.ιSummand A :=
  by
  apply s.hom_ext'
  intro A
  rw [comp_id, comp_sum, Finset.sum_eq_single A, ι_π_summand_eq_id_assoc]
  · intro B h₁ h₂
    rw [s.ι_π_summand_eq_zero_assoc _ _ h₂, zero_comp]
  · simp only [Finset.mem_univ, not_true, IsEmpty.forall_iff]
#align simplicial_object.splitting.decomposition_id SimplicialObject.Splitting.decomposition_id

@[simp, reassoc.1]
theorem σ_comp_πSummand_id_eq_zero {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ s.πSummand (IndexSet.id (op [n + 1])) = 0 :=
  by
  apply s.hom_ext'
  intro A
  dsimp only [simplicial_object.σ]
  rw [comp_zero, s.ι_summand_epi_naturality_assoc A (SimplexCategory.σ i).op, ι_π_summand_eq_zero]
  symm
  change ¬(A.epi_comp (SimplexCategory.σ i).op).EqId
  rw [index_set.eq_id_iff_len_eq]
  have h := SimplexCategory.len_le_of_epi (inferInstance : epi A.e)
  dsimp at h⊢
  linarith
#align simplicial_object.splitting.σ_comp_π_summand_id_eq_zero SimplicialObject.Splitting.σ_comp_πSummand_id_eq_zero

/-- If a simplicial object `X` in an additive category is split,
then `P_infty` vanishes on all the summands of `X _[n]` which do
not correspond to the identity of `[n]`. -/
theorem ιSummand_comp_pInfty_eq_zero {X : SimplicialObject C} (s : SimplicialObject.Splitting X)
    {n : ℕ} (A : SimplicialObject.Splitting.IndexSet (op [n])) (hA : ¬A.EqId) :
    s.ιSummand A ≫ PInfty.f n = 0 :=
  by
  rw [SimplicialObject.Splitting.IndexSet.eqId_iff_mono] at hA
  rw [SimplicialObject.Splitting.ιSummand_eq, assoc, degeneracy_comp_P_infty X n A.e hA, comp_zero]
#align simplicial_object.splitting.ι_summand_comp_P_infty_eq_zero SimplicialObject.Splitting.ιSummand_comp_pInfty_eq_zero

theorem comp_pInfty_eq_zero_iff {Z : C} {n : ℕ} (f : Z ⟶ X _[n]) :
    f ≫ PInfty.f n = 0 ↔ f ≫ s.πSummand (IndexSet.id (op [n])) = 0 :=
  by
  constructor
  · intro h
    cases n
    · dsimp at h
      rw [comp_id] at h
      rw [h, zero_comp]
    · have h' := f ≫= P_infty_f_add_Q_infty_f (n + 1)
      dsimp at h'
      rw [comp_id, comp_add, h, zero_add] at h'
      rw [← h', assoc, Q_infty_f, decomposition_Q, preadditive.sum_comp, preadditive.comp_sum,
        Finset.sum_eq_zero]
      intro i hi
      simp only [assoc, σ_comp_π_summand_id_eq_zero, comp_zero]
  · intro h
    rw [← comp_id f, assoc, s.decomposition_id, preadditive.sum_comp, preadditive.comp_sum,
      Fintype.sum_eq_zero]
    intro A
    by_cases hA : A.eq_id
    · dsimp at hA
      subst hA
      rw [assoc, reassoc_of h, zero_comp]
    · simp only [assoc, s.ι_summand_comp_P_infty_eq_zero A hA, comp_zero]
#align simplicial_object.splitting.comp_P_infty_eq_zero_iff SimplicialObject.Splitting.comp_pInfty_eq_zero_iff

@[simp, reassoc.1]
theorem pInfty_comp_πSummand_id (n : ℕ) :
    PInfty.f n ≫ s.πSummand (IndexSet.id (op [n])) = s.πSummand (IndexSet.id (op [n])) :=
  by
  conv_rhs => rw [← id_comp (s.π_summand _)]
  symm
  rw [← sub_eq_zero, ← sub_comp, ← comp_P_infty_eq_zero_iff, sub_comp, id_comp, P_infty_f_idem,
    sub_self]
#align simplicial_object.splitting.P_infty_comp_π_summand_id SimplicialObject.Splitting.pInfty_comp_πSummand_id

@[simp, reassoc.1]
theorem πSummand_comp_ιSummand_comp_pInfty_eq_pInfty (n : ℕ) :
    s.πSummand (IndexSet.id (op [n])) ≫ s.ιSummand (IndexSet.id (op [n])) ≫ PInfty.f n =
      PInfty.f n :=
  by
  conv_rhs => rw [← id_comp (P_infty.f n)]
  erw [s.decomposition_id, preadditive.sum_comp]
  rw [Fintype.sum_eq_single (index_set.id (op [n])), assoc]
  rintro A (hA : ¬A.eq_id)
  rw [assoc, s.ι_summand_comp_P_infty_eq_zero A hA, comp_zero]
#align simplicial_object.splitting.π_summand_comp_ι_summand_comp_P_infty_eq_P_infty SimplicialObject.Splitting.πSummand_comp_ιSummand_comp_pInfty_eq_pInfty

/-- The differentials `s.d i j : s.N i ⟶ s.N j` on nondegenerate simplices of a split
simplicial object are induced by the differentials on the alternating face map complex. -/
@[simp]
def d (i j : ℕ) : s.n i ⟶ s.n j :=
  s.ιSummand (IndexSet.id (op [i])) ≫ K[X].d i j ≫ s.πSummand (IndexSet.id (op [j]))
#align simplicial_object.splitting.d SimplicialObject.Splitting.d

theorem ιSummand_comp_d_comp_πSummand_eq_zero (j k : ℕ) (A : IndexSet (op [j])) (hA : ¬A.EqId) :
    s.ιSummand A ≫ K[X].d j k ≫ s.πSummand (IndexSet.id (op [k])) = 0 :=
  by
  rw [A.eq_id_iff_mono] at hA
  rw [← assoc, ← s.comp_P_infty_eq_zero_iff, assoc, ← P_infty.comm j k, s.ι_summand_eq, assoc,
    degeneracy_comp_P_infty_assoc X j A.e hA, zero_comp, comp_zero]
#align simplicial_object.splitting.ι_summand_comp_d_comp_π_summand_eq_zero SimplicialObject.Splitting.ιSummand_comp_d_comp_πSummand_eq_zero

/-- If `s` is a splitting of a simplicial object `X` in a preadditive category,
`s.nondeg_complex` is a chain complex which is given in degree `n` by
the nondegenerate `n`-simplices of `X`. -/
@[simps]
def nondegComplex : ChainComplex C ℕ where
  pt := s.n
  d := s.d
  shape' i j hij := by simp only [d, K[X].shape i j hij, zero_comp, comp_zero]
  d_comp_d' i j k hij hjk := by
    simp only [d, assoc]
    have eq :
      K[X].d i j ≫ 𝟙 (X.obj (op [j])) ≫ K[X].d j k ≫ s.π_summand (index_set.id (op [k])) = 0 := by
      erw [id_comp, HomologicalComplex.d_comp_d_assoc, zero_comp]
    rw [s.decomposition_id] at eq
    classical
      rw [Fintype.sum_eq_add_sum_compl (index_set.id (op [j])), add_comp, comp_add, assoc,
        preadditive.sum_comp, preadditive.comp_sum, Finset.sum_eq_zero, add_zero] at eq
      swap
      · intro A hA
        simp only [Finset.mem_compl, Finset.mem_singleton] at hA
        simp only [assoc, ι_summand_comp_d_comp_π_summand_eq_zero _ _ _ _ hA, comp_zero]
      rw [Eq, comp_zero]
#align simplicial_object.splitting.nondeg_complex SimplicialObject.Splitting.nondegComplex

/-- The chain complex `s.nondeg_complex` attached to a splitting of a simplicial object `X`
becomes isomorphic to the normalized Moore complex `N₁.obj X` defined as a formal direct
factor in the category `karoubi (chain_complex C ℕ)`. -/
@[simps]
def toKaroubiNondegComplexIsoN₁ : (toKaroubi _).obj s.nondegComplex ≅ N₁.obj X
    where
  Hom :=
    { f :=
        { f := fun n => s.ιSummand (IndexSet.id (op [n])) ≫ PInfty.f n
          comm' := fun i j hij => by
            dsimp
            rw [assoc, assoc, assoc, π_summand_comp_ι_summand_comp_P_infty_eq_P_infty,
              HomologicalComplex.Hom.comm] }
      comm := by
        ext n
        dsimp
        rw [id_comp, assoc, P_infty_f_idem] }
  inv :=
    { f :=
        { f := fun n => s.πSummand (IndexSet.id (op [n]))
          comm' := fun i j hij => by
            dsimp
            slice_rhs 1 1 => rw [← id_comp (K[X].d i j)]
            erw [s.decomposition_id]
            rw [sum_comp, sum_comp, Finset.sum_eq_single (index_set.id (op [i])), assoc, assoc]
            · intro A h hA
              simp only [assoc, s.ι_summand_comp_d_comp_π_summand_eq_zero _ _ _ hA, comp_zero]
            · simp only [Finset.mem_univ, not_true, IsEmpty.forall_iff] }
      comm := by
        ext n
        dsimp
        simp only [comp_id, P_infty_comp_π_summand_id] }
  hom_inv_id' := by
    ext n
    simpa only [assoc, P_infty_comp_π_summand_id, karoubi.comp_f, HomologicalComplex.comp_f,
      ι_π_summand_eq_id]
  inv_hom_id' := by
    ext n
    simp only [π_summand_comp_ι_summand_comp_P_infty_eq_P_infty, karoubi.comp_f,
      HomologicalComplex.comp_f, N₁_obj_p, karoubi.id_eq]
#align simplicial_object.splitting.to_karoubi_nondeg_complex_iso_N₁ SimplicialObject.Splitting.toKaroubiNondegComplexIsoN₁

end Splitting

namespace Split

variable {C : Type _} [Category C] [Preadditive C] [HasFiniteCoproducts C]

/-- The functor which sends a split simplicial object in a preadditive category to
the chain complex which consists of nondegenerate simplices. -/
@[simps]
def nondegComplexFunctor : Split C ⥤ ChainComplex C ℕ
    where
  obj S := S.s.nondegComplex
  map S₁ S₂ Φ :=
    { f := Φ.f
      comm' := fun i j hij => by
        dsimp
        erw [← ι_summand_naturality_symm_assoc Φ (splitting.index_set.id (op [i])),
          ((alternating_face_map_complex C).map Φ.F).comm_assoc i j]
        simp only [assoc]
        congr 2
        apply S₁.s.hom_ext'
        intro A
        dsimp [alternating_face_map_complex]
        erw [ι_summand_naturality_symm_assoc Φ A]
        by_cases A.eq_id
        · dsimp at h
          subst h
          simpa only [splitting.ι_π_summand_eq_id, comp_id, splitting.ι_π_summand_eq_id_assoc]
        · have h' : splitting.index_set.id (op [j]) ≠ A :=
            by
            symm
            exact h
          rw [S₁.s.ι_π_summand_eq_zero_assoc _ _ h', S₂.s.ι_π_summand_eq_zero _ _ h', zero_comp,
            comp_zero] }
#align simplicial_object.split.nondeg_complex_functor SimplicialObject.Split.nondegComplexFunctor

/-- The natural isomorphism (in `karoubi (chain_complex C ℕ)`) between the chain complex
of nondegenerate simplices of a split simplicial object and the normalized Moore complex
defined as a formal direct factor of the alternating face map complex. -/
@[simps]
def toKaroubiNondegComplexFunctorIsoN₁ :
    nondegComplexFunctor ⋙ toKaroubi (ChainComplex C ℕ) ≅ forget C ⋙ DoldKan.N₁ :=
  NatIso.ofComponents (fun S => S.s.toKaroubiNondegComplexIsoN₁) fun S₁ S₂ Φ =>
    by
    ext n
    dsimp
    simp only [karoubi.comp_f, to_karoubi_map_f, HomologicalComplex.comp_f,
      nondeg_complex_functor_map_f, splitting.to_karoubi_nondeg_complex_iso_N₁_hom_f_f, N₁_map_f,
      alternating_face_map_complex.map_f, assoc, P_infty_f_idem_assoc]
    erw [← split.ι_summand_naturality_symm_assoc Φ (splitting.index_set.id (op [n]))]
    rw [P_infty_f_naturality]
#align simplicial_object.split.to_karoubi_nondeg_complex_functor_iso_N₁ SimplicialObject.Split.toKaroubiNondegComplexFunctorIsoN₁

end Split

end SimplicialObject

