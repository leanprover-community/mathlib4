/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Adam Topaz, Johan Commelin
-/
import Mathlib.Algebra.Homology.Additive
import Mathlib.AlgebraicTopology.MooreComplex
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Idempotents.FunctorCategories

#align_import algebraic_topology.alternating_face_map_complex from "leanprover-community/mathlib"@"88bca0ce5d22ebfd9e73e682e51d60ea13b48347"

/-!

# The alternating face map complex of a simplicial object in a preadditive category

We construct the alternating face map complex, as a
functor `alternatingFaceMapComplex : SimplicialObject C ⥤ ChainComplex C ℕ`
for any preadditive category `C`. For any simplicial object `X` in `C`,
this is the homological complex `... → X_2 → X_1 → X_0`
where the differentials are alternating sums of faces.

The dual version `alternatingCofaceMapComplex : CosimplicialObject C ⥤ CochainComplex C ℕ`
is also constructed.

We also construct the natural transformation
`inclusionOfMooreComplex : normalizedMooreComplex A ⟶ alternatingFaceMapComplex A`
when `A` is an abelian category.

## References
* https://stacks.math.columbia.edu/tag/0194
* https://ncatlab.org/nlab/show/Moore+complex

-/


open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject

open CategoryTheory.Preadditive CategoryTheory.Category CategoryTheory.Idempotents

open Opposite

open Simplicial

noncomputable section

namespace AlgebraicTopology

namespace AlternatingFaceMapComplex

/-!
## Construction of the alternating face map complex
-/


variable {C : Type*} [Category C] [Preadditive C]
variable (X : SimplicialObject C)
variable (Y : SimplicialObject C)

/-- The differential on the alternating face map complex is the alternate
sum of the face maps -/
@[simp]
def objD (n : ℕ) : X _[n + 1] ⟶ X _[n] :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i
#align algebraic_topology.alternating_face_map_complex.obj_d AlgebraicTopology.AlternatingFaceMapComplex.objD

/-- ## The chain complex relation `d ≫ d`
-/
theorem d_squared (n : ℕ) : objD X (n + 1) ≫ objD X n = 0 := by
  -- we start by expanding d ≫ d as a double sum
  dsimp
  simp only [comp_sum, sum_comp, ← Finset.sum_product']
  -- then, we decompose the index set P into a subset S and its complement Sᶜ
  let P := Fin (n + 2) × Fin (n + 3)
  let S := Finset.univ.filter fun ij : P => (ij.2 : ℕ) ≤ (ij.1 : ℕ)
  erw [← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  /- we are reduced to showing that two sums are equal, and this is obtained
    by constructing a bijection φ : S -> Sᶜ, which maps (i,j) to (j,i+1),
    and by comparing the terms -/
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.1)), ij.1.succ)
  apply Finset.sum_bij φ
  · -- φ(S) is contained in Sᶜ
    intro ij hij
    simp only [S, Finset.mem_univ, Finset.compl_filter, Finset.mem_filter, true_and_iff,
      Fin.val_succ, Fin.coe_castLT] at hij ⊢
    linarith
  · -- φ : S → Sᶜ is injective
    rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk.inj_iff]
    exact ⟨by simpa using congr_arg Prod.snd h,
      by simpa [Fin.castSucc_castLT] using congr_arg Fin.castSucc (congr_arg Prod.fst h)⟩
  · -- φ : S → Sᶜ is surjective
    rintro ⟨i', j'⟩ hij'
    simp only [S, Finset.mem_univ, forall_true_left, Prod.forall, ge_iff_le, Finset.compl_filter,
      not_le, Finset.mem_filter, true_and] at hij'
    refine ⟨(j'.pred <| ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero'] at hij'
    · simpa only [S, Finset.mem_univ, forall_true_left, Prod.forall, ge_iff_le, Finset.mem_filter,
        Fin.coe_castSucc, Fin.coe_pred, true_and] using Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · -- identification of corresponding terms in both sums
    rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [Fin.val_succ, pow_add, pow_one, mul_neg, neg_neg, mul_one]
      apply mul_comm
    · rw [CategoryTheory.SimplicialObject.δ_comp_δ'']
      simpa [S] using hij
#align algebraic_topology.alternating_face_map_complex.d_squared AlgebraicTopology.AlternatingFaceMapComplex.d_squared

/-!
## Construction of the alternating face map complex functor
-/


/-- The alternating face map complex, on objects -/
def obj : ChainComplex C ℕ :=
  ChainComplex.of (fun n => X _[n]) (objD X) (d_squared X)
#align algebraic_topology.alternating_face_map_complex.obj AlgebraicTopology.AlternatingFaceMapComplex.obj

@[simp]
theorem obj_X (X : SimplicialObject C) (n : ℕ) : (AlternatingFaceMapComplex.obj X).X n = X _[n] :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_topology.alternating_face_map_complex.obj_X AlgebraicTopology.AlternatingFaceMapComplex.obj_X

@[simp]
theorem obj_d_eq (X : SimplicialObject C) (n : ℕ) :
    (AlternatingFaceMapComplex.obj X).d (n + 1) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i :=
  by apply ChainComplex.of_d
#align algebraic_topology.alternating_face_map_complex.obj_d_eq AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq

variable {X} {Y}

/-- The alternating face map complex, on morphisms -/
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ChainComplex.ofHom _ _ _ _ _ _ (fun n => f.app (op [n])) fun n => by
    dsimp
    rw [comp_sum, sum_comp]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [comp_zsmul, zsmul_comp]
    congr 1
    symm
    apply f.naturality
#align algebraic_topology.alternating_face_map_complex.map AlgebraicTopology.AlternatingFaceMapComplex.map

@[simp]
theorem map_f (f : X ⟶ Y) (n : ℕ) : (map f).f n = f.app (op [n]) :=
  rfl
#align algebraic_topology.alternating_face_map_complex.map_f AlgebraicTopology.AlternatingFaceMapComplex.map_f

end AlternatingFaceMapComplex

variable (C : Type*) [Category C] [Preadditive C]

/-- The alternating face map complex, as a functor -/
def alternatingFaceMapComplex : SimplicialObject C ⥤ ChainComplex C ℕ where
  obj := AlternatingFaceMapComplex.obj
  map f := AlternatingFaceMapComplex.map f
#align algebraic_topology.alternating_face_map_complex AlgebraicTopology.alternatingFaceMapComplex

variable {C}

@[simp]
theorem alternatingFaceMapComplex_obj_X (X : SimplicialObject C) (n : ℕ) :
    ((alternatingFaceMapComplex C).obj X).X n = X _[n] :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_topology.alternating_face_map_complex_obj_X AlgebraicTopology.alternatingFaceMapComplex_obj_X

@[simp]
theorem alternatingFaceMapComplex_obj_d (X : SimplicialObject C) (n : ℕ) :
    ((alternatingFaceMapComplex C).obj X).d (n + 1) n = AlternatingFaceMapComplex.objD X n := by
 dsimp only [alternatingFaceMapComplex, AlternatingFaceMapComplex.obj]
 apply ChainComplex.of_d
#align algebraic_topology.alternating_face_map_complex_obj_d AlgebraicTopology.alternatingFaceMapComplex_obj_d

@[simp]
theorem alternatingFaceMapComplex_map_f {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    ((alternatingFaceMapComplex C).map f).f n = f.app (op [n]) :=
  rfl
#align algebraic_topology.alternating_face_map_complex_map_f AlgebraicTopology.alternatingFaceMapComplex_map_f

theorem map_alternatingFaceMapComplex {D : Type*} [Category D] [Preadditive D] (F : C ⥤ D)
    [F.Additive] :
    alternatingFaceMapComplex C ⋙ F.mapHomologicalComplex _ =
      (SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D := by
  apply CategoryTheory.Functor.ext
  · intro X Y f
    ext n
    simp only [Functor.comp_map, HomologicalComplex.comp_f, alternatingFaceMapComplex_map_f,
      Functor.mapHomologicalComplex_map_f, HomologicalComplex.eqToHom_f, eqToHom_refl, comp_id,
      id_comp, SimplicialObject.whiskering_obj_map_app]
  · intro X
    apply HomologicalComplex.ext
    · rintro i j (rfl : j + 1 = i)
      dsimp only [Functor.comp_obj]
      simp only [Functor.mapHomologicalComplex_obj_d, alternatingFaceMapComplex_obj_d,
        eqToHom_refl, id_comp, comp_id, AlternatingFaceMapComplex.objD, Functor.map_sum,
        Functor.map_zsmul]
      rfl
    · ext n
      rfl
#align algebraic_topology.map_alternating_face_map_complex AlgebraicTopology.map_alternatingFaceMapComplex

theorem karoubi_alternatingFaceMapComplex_d (P : Karoubi (SimplicialObject C)) (n : ℕ) :
    ((AlternatingFaceMapComplex.obj (KaroubiFunctorCategoryEmbedding.obj P)).d (n + 1) n).f =
      P.p.app (op [n + 1]) ≫ (AlternatingFaceMapComplex.obj P.X).d (n + 1) n := by
  dsimp
  simp only [AlternatingFaceMapComplex.obj_d_eq, Karoubi.sum_hom, Preadditive.comp_sum,
    Karoubi.zsmul_hom, Preadditive.comp_zsmul]
  rfl
#align algebraic_topology.karoubi_alternating_face_map_complex_d AlgebraicTopology.karoubi_alternatingFaceMapComplex_d

namespace AlternatingFaceMapComplex

/-- The natural transformation which gives the augmentation of the alternating face map
complex attached to an augmented simplicial object. -/
def ε [Limits.HasZeroObject C] :
    SimplicialObject.Augmented.drop ⋙ AlgebraicTopology.alternatingFaceMapComplex C ⟶
      SimplicialObject.Augmented.point ⋙ ChainComplex.single₀ C where
  app X := by
    refine (ChainComplex.toSingle₀Equiv _ _).symm ?_
    refine ⟨X.hom.app (op [0]), ?_⟩
    dsimp
    rw [alternatingFaceMapComplex_obj_d, objD, Fin.sum_univ_two, Fin.val_zero,
      pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, one_smul, add_comp,
      neg_comp, SimplicialObject.δ_naturality, SimplicialObject.δ_naturality]
    apply add_right_neg
  naturality X Y f := by
    apply HomologicalComplex.to_single_hom_ext
    dsimp
    erw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero,
      ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
    simp only [ChainComplex.single₀_map_f_zero]
    exact congr_app f.w _
#align algebraic_topology.alternating_face_map_complex.ε AlgebraicTopology.AlternatingFaceMapComplex.ε

@[simp]
lemma ε_app_f_zero [Limits.HasZeroObject C] (X : SimplicialObject.Augmented C) :
    (ε.app X).f 0 = X.hom.app (op [0]) :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

@[simp]
lemma ε_app_f_succ [Limits.HasZeroObject C] (X : SimplicialObject.Augmented C) (n : ℕ) :
    (ε.app X).f (n + 1) = 0 := rfl

end AlternatingFaceMapComplex

/-!
## Construction of the natural inclusion of the normalized Moore complex
-/

variable {A : Type*} [Category A] [Abelian A]

/-- The inclusion map of the Moore complex in the alternating face map complex -/
def inclusionOfMooreComplexMap (X : SimplicialObject A) :
    (normalizedMooreComplex A).obj X ⟶ (alternatingFaceMapComplex A).obj X := by
  dsimp only [normalizedMooreComplex, NormalizedMooreComplex.obj,
    alternatingFaceMapComplex, AlternatingFaceMapComplex.obj]
  apply ChainComplex.ofHom _ _ _ _ _ _ (fun n => (NormalizedMooreComplex.objX X n).arrow)
  /- we have to show the compatibility of the differentials on the alternating
           face map complex with those defined on the normalized Moore complex:
           we first get rid of the terms of the alternating sum that are obviously
           zero on the normalized_Moore_complex -/
  intro i
  simp only [AlternatingFaceMapComplex.objD, comp_sum]
  rw [Fin.sum_univ_succ, Fintype.sum_eq_zero]
  swap
  · intro j
    rw [NormalizedMooreComplex.objX, comp_zsmul,
      ← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ _ (Finset.mem_univ j)),
      Category.assoc, kernelSubobject_arrow_comp, comp_zero, smul_zero]
  -- finally, we study the remaining term which is induced by X.δ 0
  rw [add_zero, Fin.val_zero, pow_zero, one_zsmul]
  dsimp [NormalizedMooreComplex.objD, NormalizedMooreComplex.objX]
  cases i <;> simp
set_option linter.uppercaseLean3 false in
#align algebraic_topology.inclusion_of_Moore_complex_map AlgebraicTopology.inclusionOfMooreComplexMap

@[simp]
theorem inclusionOfMooreComplexMap_f (X : SimplicialObject A) (n : ℕ) :
    (inclusionOfMooreComplexMap X).f n = (NormalizedMooreComplex.objX X n).arrow := by
  dsimp only [inclusionOfMooreComplexMap]
  exact ChainComplex.ofHom_f _ _ _ _ _ _ _ _ n
set_option linter.uppercaseLean3 false in
#align algebraic_topology.inclusion_of_Moore_complex_map_f AlgebraicTopology.inclusionOfMooreComplexMap_f

variable (A)

/-- The inclusion map of the Moore complex in the alternating face map complex,
as a natural transformation -/
@[simps]
def inclusionOfMooreComplex : normalizedMooreComplex A ⟶ alternatingFaceMapComplex A where
  app := inclusionOfMooreComplexMap
set_option linter.uppercaseLean3 false in
#align algebraic_topology.inclusion_of_Moore_complex AlgebraicTopology.inclusionOfMooreComplex

namespace AlternatingCofaceMapComplex

variable (X Y : CosimplicialObject C)

/-- The differential on the alternating coface map complex is the alternate
sum of the coface maps -/
@[simp]
def objD (n : ℕ) : X.obj [n] ⟶ X.obj [n + 1] :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i
#align algebraic_topology.alternating_coface_map_complex.obj_d AlgebraicTopology.AlternatingCofaceMapComplex.objD

theorem d_eq_unop_d (n : ℕ) :
    objD X n =
      (AlternatingFaceMapComplex.objD ((cosimplicialSimplicialEquiv C).functor.obj (op X))
          n).unop := by
  simp only [objD, AlternatingFaceMapComplex.objD, unop_sum, unop_zsmul]
  rfl
#align algebraic_topology.alternating_coface_map_complex.d_eq_unop_d AlgebraicTopology.AlternatingCofaceMapComplex.d_eq_unop_d

theorem d_squared (n : ℕ) : objD X n ≫ objD X (n + 1) = 0 := by
  simp only [d_eq_unop_d, ← unop_comp, AlternatingFaceMapComplex.d_squared, unop_zero]
#align algebraic_topology.alternating_coface_map_complex.d_squared AlgebraicTopology.AlternatingCofaceMapComplex.d_squared

/-- The alternating coface map complex, on objects -/
def obj : CochainComplex C ℕ :=
  CochainComplex.of (fun n => X.obj [n]) (objD X) (d_squared X)
#align algebraic_topology.alternating_coface_map_complex.obj AlgebraicTopology.AlternatingCofaceMapComplex.obj

variable {X} {Y}

/-- The alternating face map complex, on morphisms -/
@[simp]
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  CochainComplex.ofHom _ _ _ _ _ _ (fun n => f.app [n]) fun n => by
    dsimp
    rw [comp_sum, sum_comp]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [comp_zsmul, zsmul_comp]
    congr 1
    symm
    apply f.naturality
#align algebraic_topology.alternating_coface_map_complex.map AlgebraicTopology.AlternatingCofaceMapComplex.map

end AlternatingCofaceMapComplex

variable (C)

/-- The alternating coface map complex, as a functor -/
@[simps]
def alternatingCofaceMapComplex : CosimplicialObject C ⥤ CochainComplex C ℕ where
  obj := AlternatingCofaceMapComplex.obj
  map f := AlternatingCofaceMapComplex.map f
#align algebraic_topology.alternating_coface_map_complex AlgebraicTopology.alternatingCofaceMapComplex

end AlgebraicTopology
