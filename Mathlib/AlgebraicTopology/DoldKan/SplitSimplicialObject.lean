/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SplitSimplicialObject
import Mathlib.AlgebraicTopology.DoldKan.Degeneracies
import Mathlib.AlgebraicTopology.DoldKan.FunctorN

#align_import algebraic_topology.dold_kan.split_simplicial_object from "leanprover-community/mathlib"@"32a7e535287f9c73f2e4d2aef306a39190f0b504"

/-!

# Split simplicial objects in preadditive categories

In this file we define a functor `nondegComplex : SimplicialObject.Split C ⥤ ChainComplex C ℕ`
when `C` is a preadditive category with finite coproducts, and get an isomorphism
`toKaroubiNondegComplexFunctorIsoN₁ : nondegComplex ⋙ toKaroubi _ ≅ forget C ⋙ DoldKan.N₁`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/


open CategoryTheory CategoryTheory.Limits CategoryTheory.Category CategoryTheory.Preadditive
  CategoryTheory.Idempotents Opposite AlgebraicTopology AlgebraicTopology.DoldKan
  BigOperators Simplicial DoldKan

namespace SimplicialObject

namespace Splitting

variable {C : Type*} [Category C] [HasFiniteCoproducts C] {X : SimplicialObject C}
  (s : Splitting X)

/-- The projection on a summand of the coproduct decomposition given
by a splitting of a simplicial object. -/
noncomputable def πSummand [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    X.obj Δ ⟶ s.N A.1.unop.len := by
  refine' (s.iso Δ).inv ≫ Sigma.desc fun B => _
  -- ⊢ summand s.N Δ B ⟶ N s (SimplexCategory.len A.fst.unop)
  by_cases B = A
  -- ⊢ summand s.N Δ B ⟶ N s (SimplexCategory.len A.fst.unop)
  -- ⊢ summand s.N Δ B ⟶ N s (SimplexCategory.len A.fst.unop)
  · exact eqToHom (by subst h; rfl)
    -- 🎉 no goals
  · exact 0
    -- 🎉 no goals
#align simplicial_object.splitting.π_summand SimplicialObject.Splitting.πSummand

@[reassoc (attr := simp)]
theorem ι_πSummand_eq_id [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    s.ιSummand A ≫ s.πSummand A = 𝟙 _ := by
  dsimp only [ιSummand, iso_hom, πSummand, iso_inv, summand]
  -- ⊢ ((ιCoprod s.N A ≫ map X s.ι Δ) ≫ inv (map X s.ι Δ) ≫ Sigma.desc fun B => if  …
  simp only [summand, assoc, IsIso.hom_inv_id_assoc]
  -- ⊢ (ιCoprod s.N A ≫ Sigma.desc fun B => if h : B = A then eqToHom (_ : summand  …
  erw [colimit.ι_desc, Cofan.mk_ι_app]
  -- ⊢ (if h : { as := A }.as = A then eqToHom (_ : summand s.N Δ { as := A }.as =  …
  dsimp
  -- ⊢ (if h : A = A then 𝟙 (N s (SimplexCategory.len A.fst.unop)) else 0) = 𝟙 (N s …
  simp only [dite_eq_ite, ite_true]
  -- 🎉 no goals
#align simplicial_object.splitting.ι_π_summand_eq_id SimplicialObject.Splitting.ι_πSummand_eq_id

@[reassoc (attr := simp)]
theorem ι_πSummand_eq_zero [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A B : IndexSet Δ)
    (h : B ≠ A) : s.ιSummand A ≫ s.πSummand B = 0 := by
  dsimp only [ιSummand, iso_hom, πSummand, iso_inv, summand]
  -- ⊢ ((ιCoprod s.N A ≫ map X s.ι Δ) ≫ inv (map X s.ι Δ) ≫ Sigma.desc fun B_1 => i …
  simp only [summand, assoc, IsIso.hom_inv_id_assoc]
  -- ⊢ (ιCoprod s.N A ≫ Sigma.desc fun B_1 => if h : B_1 = B then eqToHom (_ : summ …
  erw [colimit.ι_desc, Cofan.mk_ι_app]
  -- ⊢ (if h : { as := A }.as = B then eqToHom (_ : summand s.N Δ { as := A }.as =  …
  exact dif_neg h.symm
  -- 🎉 no goals
#align simplicial_object.splitting.ι_π_summand_eq_zero SimplicialObject.Splitting.ι_πSummand_eq_zero

variable [Preadditive C]

theorem decomposition_id (Δ : SimplexCategoryᵒᵖ) :
    𝟙 (X.obj Δ) = ∑ A : IndexSet Δ, s.πSummand A ≫ s.ιSummand A := by
  apply s.hom_ext'
  -- ⊢ ∀ (A : IndexSet Δ), ιSummand s A ≫ 𝟙 (X.obj Δ) = ιSummand s A ≫ ∑ A : IndexS …
  intro A
  -- ⊢ ιSummand s A ≫ 𝟙 (X.obj Δ) = ιSummand s A ≫ ∑ A : IndexSet Δ, πSummand s A ≫ …
  rw [comp_id, comp_sum, Finset.sum_eq_single A, ι_πSummand_eq_id_assoc]
  -- ⊢ ∀ (b : IndexSet Δ), b ∈ Finset.univ → b ≠ A → ιSummand s A ≫ πSummand s b ≫  …
  · intro B _ h₂
    -- ⊢ ιSummand s A ≫ πSummand s B ≫ ιSummand s B = 0
    rw [s.ι_πSummand_eq_zero_assoc _ _ h₂, zero_comp]
    -- 🎉 no goals
  · simp only [Finset.mem_univ, not_true, IsEmpty.forall_iff]
    -- 🎉 no goals
#align simplicial_object.splitting.decomposition_id SimplicialObject.Splitting.decomposition_id

@[reassoc (attr := simp)]
theorem σ_comp_πSummand_id_eq_zero {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ s.πSummand (IndexSet.id (op [n + 1])) = 0 := by
  apply s.hom_ext'
  -- ⊢ ∀ (A : IndexSet (op [n])), ιSummand s A ≫ SimplicialObject.σ X i ≫ πSummand  …
  intro A
  -- ⊢ ιSummand s A ≫ SimplicialObject.σ X i ≫ πSummand s (IndexSet.id (op [n + 1]) …
  dsimp only [SimplicialObject.σ]
  -- ⊢ ιSummand s A ≫ X.map (SimplexCategory.σ i).op ≫ πSummand s (IndexSet.id (op  …
  rw [comp_zero, s.ιSummand_epi_naturality_assoc A (SimplexCategory.σ i).op, ι_πSummand_eq_zero]
  -- ⊢ IndexSet.id (op [n + 1]) ≠ IndexSet.epiComp A (SimplexCategory.σ i).op
  rw [ne_comm]
  -- ⊢ IndexSet.epiComp A (SimplexCategory.σ i).op ≠ IndexSet.id (op [n + 1])
  change ¬(A.epiComp (SimplexCategory.σ i).op).EqId
  -- ⊢ ¬IndexSet.EqId (IndexSet.epiComp A (SimplexCategory.σ i).op)
  rw [IndexSet.eqId_iff_len_eq]
  -- ⊢ ¬SimplexCategory.len (IndexSet.epiComp A (SimplexCategory.σ i).op).fst.unop  …
  have h := SimplexCategory.len_le_of_epi (inferInstance : Epi A.e)
  -- ⊢ ¬SimplexCategory.len (IndexSet.epiComp A (SimplexCategory.σ i).op).fst.unop  …
  dsimp at h ⊢
  -- ⊢ ¬SimplexCategory.len A.fst.unop = n + 1
  linarith
  -- 🎉 no goals
#align simplicial_object.splitting.σ_comp_π_summand_id_eq_zero SimplicialObject.Splitting.σ_comp_πSummand_id_eq_zero

/-- If a simplicial object `X` in an additive category is split,
then `PInfty` vanishes on all the summands of `X _[n]` which do
not correspond to the identity of `[n]`. -/
theorem ιSummand_comp_PInfty_eq_zero {X : SimplicialObject C} (s : SimplicialObject.Splitting X)
    {n : ℕ} (A : SimplicialObject.Splitting.IndexSet (op [n])) (hA : ¬A.EqId) :
    s.ιSummand A ≫ PInfty.f n = 0 := by
  rw [SimplicialObject.Splitting.IndexSet.eqId_iff_mono] at hA
  -- ⊢ ιSummand s A ≫ HomologicalComplex.Hom.f PInfty n = 0
  rw [SimplicialObject.Splitting.ιSummand_eq, assoc, degeneracy_comp_PInfty X n A.e hA, comp_zero]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align simplicial_object.splitting.ι_summand_comp_P_infty_eq_zero SimplicialObject.Splitting.ιSummand_comp_PInfty_eq_zero

theorem comp_PInfty_eq_zero_iff {Z : C} {n : ℕ} (f : Z ⟶ X _[n]) :
    f ≫ PInfty.f n = 0 ↔ f ≫ s.πSummand (IndexSet.id (op [n])) = 0 := by
  constructor
  -- ⊢ f ≫ HomologicalComplex.Hom.f PInfty n = 0 → f ≫ πSummand s (IndexSet.id (op  …
  · intro h
    -- ⊢ f ≫ πSummand s (IndexSet.id (op [n])) = 0
    rcases n with _|n
    -- ⊢ f ≫ πSummand s (IndexSet.id (op [Nat.zero])) = 0
    · dsimp at h
      -- ⊢ f ≫ πSummand s (IndexSet.id (op [Nat.zero])) = 0
      rw [comp_id] at h
      -- ⊢ f ≫ πSummand s (IndexSet.id (op [Nat.zero])) = 0
      rw [h, zero_comp]
      -- 🎉 no goals
    · have h' := f ≫= PInfty_f_add_QInfty_f (n + 1)
      -- ⊢ f ≫ πSummand s (IndexSet.id (op [Nat.succ n])) = 0
      dsimp at h'
      -- ⊢ f ≫ πSummand s (IndexSet.id (op [Nat.succ n])) = 0
      rw [comp_id, comp_add, h, zero_add] at h'
      -- ⊢ f ≫ πSummand s (IndexSet.id (op [Nat.succ n])) = 0
      rw [← h', assoc, QInfty_f, decomposition_Q, Preadditive.sum_comp, Preadditive.comp_sum,
        Finset.sum_eq_zero]
      intro i _
      -- ⊢ f ≫ (HomologicalComplex.Hom.f (P ↑i) (n + 1) ≫ SimplicialObject.δ X (Fin.suc …
      simp only [assoc, σ_comp_πSummand_id_eq_zero, comp_zero]
      -- 🎉 no goals
  · intro h
    -- ⊢ f ≫ HomologicalComplex.Hom.f PInfty n = 0
    rw [← comp_id f, assoc, s.decomposition_id, Preadditive.sum_comp, Preadditive.comp_sum,
      Fintype.sum_eq_zero]
    intro A
    -- ⊢ f ≫ (πSummand s A ≫ ιSummand s A) ≫ HomologicalComplex.Hom.f PInfty n = 0
    by_cases hA : A.EqId
    -- ⊢ f ≫ (πSummand s A ≫ ιSummand s A) ≫ HomologicalComplex.Hom.f PInfty n = 0
    · dsimp at hA
      -- ⊢ f ≫ (πSummand s A ≫ ιSummand s A) ≫ HomologicalComplex.Hom.f PInfty n = 0
      subst hA
      -- ⊢ f ≫ (πSummand s (IndexSet.id (op [n])) ≫ ιSummand s (IndexSet.id (op [n])))  …
      rw [assoc, reassoc_of% h, zero_comp]
      -- 🎉 no goals
    · simp only [assoc, s.ιSummand_comp_PInfty_eq_zero A hA, comp_zero]
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align simplicial_object.splitting.comp_P_infty_eq_zero_iff SimplicialObject.Splitting.comp_PInfty_eq_zero_iff

@[reassoc (attr := simp)]
theorem PInfty_comp_πSummand_id (n : ℕ) :
    PInfty.f n ≫ s.πSummand (IndexSet.id (op [n])) = s.πSummand (IndexSet.id (op [n])) := by
  conv_rhs => rw [← id_comp (s.πSummand _)]
  -- ⊢ HomologicalComplex.Hom.f PInfty n ≫ πSummand s (IndexSet.id (op [n])) = 𝟙 (X …
  symm
  -- ⊢ 𝟙 (X.obj (op [n])) ≫ πSummand s (IndexSet.id (op [n])) = HomologicalComplex. …
  rw [← sub_eq_zero, ← sub_comp, ← comp_PInfty_eq_zero_iff, sub_comp, id_comp, PInfty_f_idem,
    sub_self]
set_option linter.uppercaseLean3 false in
#align simplicial_object.splitting.P_infty_comp_π_summand_id SimplicialObject.Splitting.PInfty_comp_πSummand_id

@[reassoc (attr := simp)]
theorem πSummand_comp_ιSummand_comp_PInfty_eq_PInfty (n : ℕ) :
    s.πSummand (IndexSet.id (op [n])) ≫ s.ιSummand (IndexSet.id (op [n])) ≫ PInfty.f n =
      PInfty.f n := by
  conv_rhs => rw [← id_comp (PInfty.f n)]
  -- ⊢ πSummand s (IndexSet.id (op [n])) ≫ ιSummand s (IndexSet.id (op [n])) ≫ Homo …
  erw [s.decomposition_id, Preadditive.sum_comp]
  -- ⊢ πSummand s (IndexSet.id (op [n])) ≫ ιSummand s (IndexSet.id (op [n])) ≫ Homo …
  rw [Fintype.sum_eq_single (IndexSet.id (op [n])), assoc]
  -- ⊢ ∀ (x : IndexSet (op [n])), x ≠ IndexSet.id (op [n]) → (πSummand s x ≫ ιSumma …
  rintro A (hA : ¬A.EqId)
  -- ⊢ (πSummand s A ≫ ιSummand s A) ≫ HomologicalComplex.Hom.f PInfty n = 0
  rw [assoc, s.ιSummand_comp_PInfty_eq_zero A hA, comp_zero]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align simplicial_object.splitting.π_summand_comp_ι_summand_comp_P_infty_eq_P_infty SimplicialObject.Splitting.πSummand_comp_ιSummand_comp_PInfty_eq_PInfty

/-- The differentials `s.d i j : s.N i ⟶ s.N j` on nondegenerate simplices of a split
simplicial object are induced by the differentials on the alternating face map complex. -/
@[simp]
noncomputable def d (i j : ℕ) : s.N i ⟶ s.N j :=
  s.ιSummand (IndexSet.id (op [i])) ≫ K[X].d i j ≫ s.πSummand (IndexSet.id (op [j]))
#align simplicial_object.splitting.d SimplicialObject.Splitting.d

theorem ιSummand_comp_d_comp_πSummand_eq_zero (j k : ℕ) (A : IndexSet (op [j])) (hA : ¬A.EqId) :
    s.ιSummand A ≫ K[X].d j k ≫ s.πSummand (IndexSet.id (op [k])) = 0 := by
  rw [A.eqId_iff_mono] at hA
  -- ⊢ ιSummand s A ≫ HomologicalComplex.d K[X] j k ≫ πSummand s (IndexSet.id (op [ …
  rw [← assoc, ← s.comp_PInfty_eq_zero_iff, assoc, ← PInfty.comm j k, s.ιSummand_eq, assoc,
    degeneracy_comp_PInfty_assoc X j A.e hA, zero_comp, comp_zero]
#align simplicial_object.splitting.ι_summand_comp_d_comp_π_summand_eq_zero SimplicialObject.Splitting.ιSummand_comp_d_comp_πSummand_eq_zero

/-- If `s` is a splitting of a simplicial object `X` in a preadditive category,
`s.nondeg_complex` is a chain complex which is given in degree `n` by
the nondegenerate `n`-simplices of `X`. -/
@[simps]
noncomputable def nondegComplex : ChainComplex C ℕ where
  X := s.N
  d := s.d
  shape i j hij := by simp only [d, K[X].shape i j hij, zero_comp, comp_zero]
                      -- 🎉 no goals
  d_comp_d' i j k _ _ := by
    simp only [d, assoc]
    -- ⊢ ιSummand s (IndexSet.id (op [i])) ≫ HomologicalComplex.d K[X] i j ≫ πSummand …
    have eq : K[X].d i j ≫ 𝟙 (X.obj (op [j])) ≫ K[X].d j k ≫
        s.πSummand (IndexSet.id (op [k])) = 0 := by
      erw [id_comp, HomologicalComplex.d_comp_d_assoc, zero_comp]
    rw [s.decomposition_id] at eq
    -- ⊢ ιSummand s (IndexSet.id (op [i])) ≫ HomologicalComplex.d K[X] i j ≫ πSummand …
    classical
    rw [Fintype.sum_eq_add_sum_compl (IndexSet.id (op [j])), add_comp, comp_add, assoc,
      Preadditive.sum_comp, Preadditive.comp_sum, Finset.sum_eq_zero, add_zero] at eq
    swap
    · intro A hA
      simp only [Finset.mem_compl, Finset.mem_singleton] at hA
      simp only [assoc, ιSummand_comp_d_comp_πSummand_eq_zero _ _ _ _ hA, comp_zero]
    rw [eq, comp_zero]
#align simplicial_object.splitting.nondeg_complex SimplicialObject.Splitting.nondegComplex

/-- The chain complex `s.nondegComplex` attached to a splitting of a simplicial object `X`
becomes isomorphic to the normalized Moore complex `N₁.obj X` defined as a formal direct
factor in the category `Karoubi (ChainComplex C ℕ)`. -/
@[simps]
noncomputable def toKaroubiNondegComplexIsoN₁ :
    (toKaroubi _).obj s.nondegComplex ≅ N₁.obj X where
  hom :=
    { f :=
        { f := fun n => s.ιSummand (IndexSet.id (op [n])) ≫ PInfty.f n
          comm' := fun i j _ => by
            dsimp
            -- ⊢ (ιSummand s (IndexSet.id (op [i])) ≫ HomologicalComplex.Hom.f PInfty i) ≫ Ho …
            rw [assoc, assoc, assoc, πSummand_comp_ιSummand_comp_PInfty_eq_PInfty,
              HomologicalComplex.Hom.comm] }
      comm := by
        ext n
        -- ⊢ HomologicalComplex.Hom.f (HomologicalComplex.Hom.mk fun n => ιSummand s (Ind …
        dsimp
        -- ⊢ ιSummand s (IndexSet.id (op [n])) ≫ HomologicalComplex.Hom.f PInfty n = 𝟙 (N …
        rw [id_comp, assoc, PInfty_f_idem] }
        -- 🎉 no goals
  inv :=
    { f :=
        { f := fun n => s.πSummand (IndexSet.id (op [n]))
          comm' := fun i j _ => by
            dsimp
            -- ⊢ πSummand s (IndexSet.id (op [i])) ≫ ιSummand s (IndexSet.id (op [i])) ≫ Homo …
            slice_rhs 1 1 => rw [← id_comp (K[X].d i j)]
            -- ⊢ πSummand s (IndexSet.id (op [i])) ≫ ιSummand s (IndexSet.id (op [i])) ≫ Homo …
            erw [s.decomposition_id]
            -- ⊢ πSummand s (IndexSet.id (op [i])) ≫ ιSummand s (IndexSet.id (op [i])) ≫ Homo …
            rw [sum_comp, sum_comp, Finset.sum_eq_single (IndexSet.id (op [i])), assoc, assoc]
            -- ⊢ ∀ (b : IndexSet (op [i])), b ∈ Finset.univ → b ≠ IndexSet.id (op [i]) → ((πS …
            · intro A _ hA
              -- ⊢ ((πSummand s A ≫ ιSummand s A) ≫ HomologicalComplex.d K[X] i j) ≫ πSummand s …
              simp only [assoc, s.ιSummand_comp_d_comp_πSummand_eq_zero _ _ _ hA, comp_zero]
              -- 🎉 no goals
            · simp only [Finset.mem_univ, not_true, IsEmpty.forall_iff] }
              -- 🎉 no goals
      comm := by
        ext n
        -- ⊢ HomologicalComplex.Hom.f (HomologicalComplex.Hom.mk fun n => πSummand s (Ind …
        dsimp
        -- ⊢ πSummand s (IndexSet.id (op [n])) = HomologicalComplex.Hom.f PInfty n ≫ πSum …
        simp only [comp_id, PInfty_comp_πSummand_id] }
        -- 🎉 no goals
  hom_inv_id := by
    ext n
    -- ⊢ HomologicalComplex.Hom.f (Karoubi.Hom.mk (HomologicalComplex.Hom.mk fun n => …
    simp only [assoc, PInfty_comp_πSummand_id, Karoubi.comp_f, HomologicalComplex.comp_f,
      ι_πSummand_eq_id]
    rfl
    -- 🎉 no goals
  inv_hom_id := by
    ext n
    -- ⊢ HomologicalComplex.Hom.f (Karoubi.Hom.mk (HomologicalComplex.Hom.mk fun n => …
    simp only [πSummand_comp_ιSummand_comp_PInfty_eq_PInfty, Karoubi.comp_f,
      HomologicalComplex.comp_f, N₁_obj_p, Karoubi.id_eq]
set_option linter.uppercaseLean3 false in
#align simplicial_object.splitting.to_karoubi_nondeg_complex_iso_N₁ SimplicialObject.Splitting.toKaroubiNondegComplexIsoN₁

end Splitting

namespace Split

variable {C : Type*} [Category C] [Preadditive C] [HasFiniteCoproducts C]

/-- The functor which sends a split simplicial object in a preadditive category to
the chain complex which consists of nondegenerate simplices. -/
@[simps]
noncomputable def nondegComplexFunctor : Split C ⥤ ChainComplex C ℕ where
  obj S := S.s.nondegComplex
  map {S₁ S₂} Φ :=
    { f := Φ.f
      comm' := fun i j _ => by
        dsimp
        -- ⊢ Hom.f Φ i ≫ Splitting.ιSummand S₂.s (Splitting.IndexSet.id (op [i])) ≫ Homol …
        erw [← ιSummand_naturality_symm_assoc Φ (Splitting.IndexSet.id (op [i])),
          ((alternatingFaceMapComplex C).map Φ.F).comm_assoc i j]
        simp only [assoc]
        -- ⊢ Splitting.ιSummand S₁.s (Splitting.IndexSet.id (op [i])) ≫ HomologicalComple …
        congr 2
        -- ⊢ HomologicalComplex.Hom.f ((alternatingFaceMapComplex C).map Φ.F) j ≫ Splitti …
        apply S₁.s.hom_ext'
        -- ⊢ ∀ (A : Splitting.IndexSet (op [j])), Splitting.ιSummand S₁.s A ≫ Homological …
        intro A
        -- ⊢ Splitting.ιSummand S₁.s A ≫ HomologicalComplex.Hom.f ((alternatingFaceMapCom …
        dsimp [alternatingFaceMapComplex]
        -- ⊢ Splitting.ιSummand S₁.s A ≫ NatTrans.app Φ.F (op [j]) ≫ Splitting.πSummand S …
        erw [ιSummand_naturality_symm_assoc Φ A]
        -- ⊢ Hom.f Φ (SimplexCategory.len A.fst.unop) ≫ Splitting.ιSummand S₂.s A ≫ Split …
        by_cases A.EqId
        -- ⊢ Hom.f Φ (SimplexCategory.len A.fst.unop) ≫ Splitting.ιSummand S₂.s A ≫ Split …
        -- ⊢ Hom.f Φ (SimplexCategory.len A.fst.unop) ≫ Splitting.ιSummand S₂.s A ≫ Split …
        · dsimp at h
          -- ⊢ Hom.f Φ (SimplexCategory.len A.fst.unop) ≫ Splitting.ιSummand S₂.s A ≫ Split …
          subst h
          -- ⊢ Hom.f Φ (SimplexCategory.len (Splitting.IndexSet.id (op [j])).fst.unop) ≫ Sp …
          simp only [Splitting.ι_πSummand_eq_id, comp_id, Splitting.ι_πSummand_eq_id_assoc]
          -- ⊢ Hom.f Φ (SimplexCategory.len (Splitting.IndexSet.id (op [j])).fst.unop) = Ho …
          rfl
          -- 🎉 no goals
        · have h' : Splitting.IndexSet.id (op [j]) ≠ A := by
            rw [ne_comm]
            exact h
          rw [S₁.s.ι_πSummand_eq_zero_assoc _ _ h', S₂.s.ι_πSummand_eq_zero _ _ h', zero_comp,
            comp_zero] }
#align simplicial_object.split.nondeg_complex_functor SimplicialObject.Split.nondegComplexFunctor

/-- The natural isomorphism (in `Karoubi (ChainComplex C ℕ)`) between the chain complex
of nondegenerate simplices of a split simplicial object and the normalized Moore complex
defined as a formal direct factor of the alternating face map complex. -/
@[simps!]
noncomputable def toKaroubiNondegComplexFunctorIsoN₁ :
    nondegComplexFunctor ⋙ toKaroubi (ChainComplex C ℕ) ≅ forget C ⋙ DoldKan.N₁ :=
  NatIso.ofComponents (fun S => S.s.toKaroubiNondegComplexIsoN₁) fun Φ => by
    ext n
    -- ⊢ HomologicalComplex.Hom.f ((nondegComplexFunctor ⋙ toKaroubi (ChainComplex C  …
    dsimp
    -- ⊢ Hom.f Φ n ≫ Splitting.ιSummand Y✝.s (Splitting.IndexSet.id (op [n])) ≫ Homol …
    simp only [Karoubi.comp_f, toKaroubi_map_f, HomologicalComplex.comp_f,
      nondegComplexFunctor_map_f, Splitting.toKaroubiNondegComplexIsoN₁_hom_f_f, N₁_map_f,
      AlternatingFaceMapComplex.map_f, assoc, PInfty_f_idem_assoc]
    erw [← Split.ιSummand_naturality_symm_assoc Φ (Splitting.IndexSet.id (op [n]))]
    -- ⊢ Splitting.ιSummand X✝.s (Splitting.IndexSet.id (op [n])) ≫ NatTrans.app Φ.F  …
    rw [PInfty_f_naturality]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align simplicial_object.split.to_karoubi_nondeg_complex_functor_iso_N₁ SimplicialObject.Split.toKaroubiNondegComplexFunctorIsoN₁

end Split

end SimplicialObject
