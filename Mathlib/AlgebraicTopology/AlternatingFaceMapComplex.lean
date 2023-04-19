/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Adam Topaz, Johan Commelin

! This file was ported from Lean 3 source module algebraic_topology.alternating_face_map_complex
! leanprover-community/mathlib commit 88bca0ce5d22ebfd9e73e682e51d60ea13b48347
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.Additive
import Mathbin.AlgebraicTopology.MooreComplex
import Mathbin.Algebra.BigOperators.Fin
import Mathbin.CategoryTheory.Preadditive.Opposite
import Mathbin.CategoryTheory.Idempotents.FunctorCategories
import Mathbin.Tactic.EquivRw

/-!

# The alternating face map complex of a simplicial object in a preadditive category

We construct the alternating face map complex, as a
functor `alternating_face_map_complex : simplicial_object C ⥤ chain_complex C ℕ`
for any preadditive category `C`. For any simplicial object `X` in `C`,
this is the homological complex `... → X_2 → X_1 → X_0`
where the differentials are alternating sums of faces.

The dual version `alternating_coface_map_complex : cosimplicial_object C ⥤ cochain_complex C ℕ`
is also constructed.

We also construct the natural transformation
`inclusion_of_Moore_complex : normalized_Moore_complex A ⟶ alternating_face_map_complex A`
when `A` is an abelian category.

## References
* https://stacks.math.columbia.edu/tag/0194
* https://ncatlab.org/nlab/show/Moore+complex

-/


open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject

open CategoryTheory.Preadditive CategoryTheory.Category CategoryTheory.Idempotents

open Opposite

open BigOperators

open Simplicial

noncomputable section

namespace AlgebraicTopology

namespace AlternatingFaceMapComplex

/-!
## Construction of the alternating face map complex
-/


variable {C : Type _} [Category C] [Preadditive C]

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
theorem d_squared (n : ℕ) : objD X (n + 1) ≫ objD X n = 0 :=
  by
  -- we start by expanding d ≫ d as a double sum
  dsimp
  rw [comp_sum]
  let d_l := fun j : Fin (n + 3) => (-1 : ℤ) ^ (j : ℕ) • X.δ j
  let d_r := fun i : Fin (n + 2) => (-1 : ℤ) ^ (i : ℕ) • X.δ i
  rw [show (fun i => (∑ j : Fin (n + 3), d_l j) ≫ d_r i) = fun i => ∑ j : Fin (n + 3), d_l j ≫ d_r i
      by
      ext i
      rw [sum_comp]]
  rw [← Finset.sum_product']
  -- then, we decompose the index set P into a subet S and its complement Sᶜ
  let P := Fin (n + 2) × Fin (n + 3)
  let S := finset.univ.filter fun ij : P => (ij.2 : ℕ) ≤ (ij.1 : ℕ)
  let term := fun ij : P => d_l ij.2 ≫ d_r ij.1
  erw [show (∑ ij : P, term ij) = (∑ ij in S, term ij) + ∑ ij in Sᶜ, term ij by
      rw [Finset.sum_add_sum_compl]]
  rw [← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  /- we are reduced to showing that two sums are equal, and this is obtained
    by constructing a bijection φ : S -> Sᶜ, which maps (i,j) to (j,i+1),
    and by comparing the terms -/
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (finset.mem_filter.mp hij).right (Fin.is_lt ij.1)), ij.1.succ)
  apply Finset.sum_bij φ
  · -- φ(S) is contained in Sᶜ
    intro ij hij
    simp only [Finset.mem_univ, Finset.compl_filter, Finset.mem_filter, true_and_iff, Fin.val_succ,
      Fin.coe_castLT] at hij⊢
    linarith
  · -- identification of corresponding terms in both sums
    rintro ⟨i, j⟩ hij
    simp only [term, d_l, d_r, φ, comp_zsmul, zsmul_comp, ← neg_smul, ← mul_smul, pow_add, neg_mul,
      mul_one, Fin.coe_castLT, Fin.val_succ, pow_one, mul_neg, neg_neg]
    let jj : Fin (n + 2) := (φ (i, j) hij).1
    have ineq : jj ≤ i := by
      rw [← Fin.val_fin_le]
      simpa using hij
    rw [CategoryTheory.SimplicialObject.δ_comp_δ X ineq, Fin.castSucc_castLT, mul_comm]
  · -- φ : S → Sᶜ is injective
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij hij' h
    rw [Prod.mk.inj_iff]
    refine' ⟨by simpa using congr_arg Prod.snd h, _⟩
    have h1 := congr_arg Fin.castSucc (congr_arg Prod.fst h)
    simpa [Fin.castSucc_castLT] using h1
  · -- φ : S → Sᶜ is surjective
    rintro ⟨i', j'⟩ hij'
    simp only [true_and_iff, Finset.mem_univ, Finset.compl_filter, not_le, Finset.mem_filter] at
      hij'
    refine' ⟨(j'.pred _, Fin.castSucc i'), _, _⟩
    · intro H
      simpa only [H, Nat.not_lt_zero, Fin.val_zero] using hij'
    ·
      simpa only [true_and_iff, Finset.mem_univ, Fin.coe_castSucc, Fin.coe_pred,
        Finset.mem_filter] using Nat.le_pred_of_lt hij'
    · simp only [Prod.mk.inj_iff, Fin.succ_pred, Fin.castLT_castSucc]
      constructor <;> rfl
#align algebraic_topology.alternating_face_map_complex.d_squared AlgebraicTopology.AlternatingFaceMapComplex.d_squared

/-!
## Construction of the alternating face map complex functor
-/


/-- The alternating face map complex, on objects -/
def obj : ChainComplex C ℕ :=
  ChainComplex.of (fun n => X _[n]) (objD X) (d_squared X)
#align algebraic_topology.alternating_face_map_complex.obj AlgebraicTopology.AlternatingFaceMapComplex.obj

@[simp]
theorem obj_x (X : SimplicialObject C) (n : ℕ) : (AlternatingFaceMapComplex.obj X).pt n = X _[n] :=
  rfl
#align algebraic_topology.alternating_face_map_complex.obj_X AlgebraicTopology.AlternatingFaceMapComplex.obj_x

@[simp]
theorem obj_d_eq (X : SimplicialObject C) (n : ℕ) :
    (AlternatingFaceMapComplex.obj X).d (n + 1) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i :=
  by apply ChainComplex.of_d
#align algebraic_topology.alternating_face_map_complex.obj_d_eq AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq

variable {X} {Y}

/-- The alternating face map complex, on morphisms -/
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ChainComplex.ofHom _ _ _ _ _ _ (fun n => f.app (op [n])) fun n =>
    by
    dsimp
    rw [comp_sum, sum_comp]
    apply Finset.sum_congr rfl fun x h => _
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

variable (C : Type _) [Category C] [Preadditive C]

/-- The alternating face map complex, as a functor -/
def alternatingFaceMapComplex : SimplicialObject C ⥤ ChainComplex C ℕ
    where
  obj := AlternatingFaceMapComplex.obj
  map X Y f := AlternatingFaceMapComplex.map f
#align algebraic_topology.alternating_face_map_complex AlgebraicTopology.alternatingFaceMapComplex

variable {C}

@[simp]
theorem alternatingFaceMapComplex_obj_x (X : SimplicialObject C) (n : ℕ) :
    ((alternatingFaceMapComplex C).obj X).pt n = X _[n] :=
  rfl
#align algebraic_topology.alternating_face_map_complex_obj_X AlgebraicTopology.alternatingFaceMapComplex_obj_x

@[simp]
theorem alternatingFaceMapComplex_objD (X : SimplicialObject C) (n : ℕ) :
    ((alternatingFaceMapComplex C).obj X).d (n + 1) n = AlternatingFaceMapComplex.objD X n := by
  apply ChainComplex.of_d
#align algebraic_topology.alternating_face_map_complex_obj_d AlgebraicTopology.alternatingFaceMapComplex_objD

@[simp]
theorem alternatingFaceMapComplex_map_f {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    ((alternatingFaceMapComplex C).map f).f n = f.app (op [n]) :=
  rfl
#align algebraic_topology.alternating_face_map_complex_map_f AlgebraicTopology.alternatingFaceMapComplex_map_f

theorem map_alternatingFaceMapComplex {D : Type _} [Category D] [Preadditive D] (F : C ⥤ D)
    [F.Additive] :
    alternatingFaceMapComplex C ⋙ F.mapHomologicalComplex _ =
      (SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D :=
  by
  apply CategoryTheory.Functor.ext
  · intro X Y f
    ext n
    simp only [functor.comp_map, HomologicalComplex.comp_f, alternating_face_map_complex_map_f,
      functor.map_homological_complex_map_f, HomologicalComplex.eqToHom_f, eq_to_hom_refl, comp_id,
      id_comp, simplicial_object.whiskering_obj_map_app]
  · intro X
    apply HomologicalComplex.ext
    · rintro i j (rfl : j + 1 = i)
      dsimp only [functor.comp_obj]
      simpa only [functor.map_homological_complex_obj_d, alternating_face_map_complex_obj_d,
        eq_to_hom_refl, id_comp, comp_id, alternating_face_map_complex.obj_d, functor.map_sum,
        functor.map_zsmul]
    · ext n
      rfl
#align algebraic_topology.map_alternating_face_map_complex AlgebraicTopology.map_alternatingFaceMapComplex

theorem karoubi_alternating_face_map_complex_d (P : Karoubi (SimplicialObject C)) (n : ℕ) :
    ((AlternatingFaceMapComplex.obj (KaroubiFunctorCategoryEmbedding.obj P)).d (n + 1) n).f =
      P.p.app (op [n + 1]) ≫ (AlternatingFaceMapComplex.obj P.pt).d (n + 1) n :=
  by
  dsimp
  simpa only [alternating_face_map_complex.obj_d_eq, karoubi.sum_hom, preadditive.comp_sum,
    karoubi.zsmul_hom, preadditive.comp_zsmul]
#align algebraic_topology.karoubi_alternating_face_map_complex_d AlgebraicTopology.karoubi_alternating_face_map_complex_d

namespace AlternatingFaceMapComplex

/-- The natural transformation which gives the augmentation of the alternating face map
complex attached to an augmented simplicial object. -/
@[simps]
def ε [Limits.HasZeroObject C] :
    SimplicialObject.Augmented.drop ⋙ AlgebraicTopology.alternatingFaceMapComplex C ⟶
      SimplicialObject.Augmented.point ⋙ ChainComplex.single₀ C
    where
  app X := by
    equiv_rw ChainComplex.toSingle₀Equiv _ _
    refine' ⟨X.hom.app (op [0]), _⟩
    dsimp
    simp only [alternating_face_map_complex_obj_d, obj_d, Fin.sum_univ_two, Fin.val_zero, pow_zero,
      one_zsmul, Fin.val_one, pow_one, neg_smul, add_comp, simplicial_object.δ_naturality, neg_comp]
    apply add_right_neg
  naturality' X Y f := by
    ext
    exact congr_app f.w _
#align algebraic_topology.alternating_face_map_complex.ε AlgebraicTopology.alternatingFaceMapComplex.ε

end AlternatingFaceMapComplex

/-!
## Construction of the natural inclusion of the normalized Moore complex
-/


variable {A : Type _} [Category A] [Abelian A]

/-- The inclusion map of the Moore complex in the alternating face map complex -/
def inclusionOfMooreComplexMap (X : SimplicialObject A) :
    (normalizedMooreComplex A).obj X ⟶ (alternatingFaceMapComplex A).obj X :=
  ChainComplex.ofHom _ _ _ _ _ _ (fun n => (NormalizedMooreComplex.objX X n).arrow) fun n =>
    by
    /- we have to show the compatibility of the differentials on the alternating
             face map complex with those defined on the normalized Moore complex:
             we first get rid of the terms of the alternating sum that are obviously
             zero on the normalized_Moore_complex -/
    simp only [alternating_face_map_complex.obj_d]
    rw [comp_sum]
    let t := fun j : Fin (n + 2) =>
      (normalized_Moore_complex.obj_X X (n + 1)).arrow ≫ ((-1 : ℤ) ^ (j : ℕ) • X.δ j)
    have def_t :
      ∀ j : Fin (n + 2),
        t j = (normalized_Moore_complex.obj_X X (n + 1)).arrow ≫ ((-1 : ℤ) ^ (j : ℕ) • X.δ j) :=
      by
      intro j
      rfl
    rw [Fin.sum_univ_succ t]
    have null : ∀ j : Fin (n + 1), t j.succ = 0 :=
      by
      intro j
      rw [def_t, comp_zsmul, ← zsmul_zero ((-1 : ℤ) ^ (j.succ : ℕ))]
      apply congr_arg
      rw [normalized_Moore_complex.obj_X]
      rw [←
        factor_thru_arrow _ _
          (finset_inf_arrow_factors Finset.univ _ j (by simp only [Finset.mem_univ]))]
      slice_lhs 2 3 => rw [kernel_subobject_arrow_comp (X.δ j.succ)]
      simp only [comp_zero]
    rw [Fintype.sum_eq_zero _ null]
    simp only [add_zero]
    -- finally, we study the remaining term which is induced by X.δ 0
    let eq := def_t 0
    rw [show (-1 : ℤ) ^ ((0 : Fin (n + 2)) : ℕ) = 1 by ring] at eq
    rw [one_smul] at eq
    rw [Eq]
    cases n <;> dsimp <;> simp
#align algebraic_topology.inclusion_of_Moore_complex_map AlgebraicTopology.inclusionOfMooreComplexMap

@[simp]
theorem inclusionOfMooreComplexMap_f (X : SimplicialObject A) (n : ℕ) :
    (inclusionOfMooreComplexMap X).f n = (NormalizedMooreComplex.objX X n).arrow :=
  ChainComplex.ofHom_f _ _ _ _ _ _ _ _ n
#align algebraic_topology.inclusion_of_Moore_complex_map_f AlgebraicTopology.inclusionOfMooreComplexMap_f

variable (A)

/-- The inclusion map of the Moore complex in the alternating face map complex,
as a natural transformation -/
@[simps]
def inclusionOfMooreComplex : normalizedMooreComplex A ⟶ alternatingFaceMapComplex A
    where app := inclusionOfMooreComplexMap
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
      (AlternatingFaceMapComplex.objD ((cosimplicialSimplicialEquiv C).Functor.obj (op X))
          n).unop :=
  by simpa only [obj_d, alternating_face_map_complex.obj_d, unop_sum, unop_zsmul]
#align algebraic_topology.alternating_coface_map_complex.d_eq_unop_d AlgebraicTopology.AlternatingCofaceMapComplex.d_eq_unop_d

theorem d_squared (n : ℕ) : objD X n ≫ objD X (n + 1) = 0 := by
  simp only [d_eq_unop_d, ← unop_comp, alternating_face_map_complex.d_squared, unop_zero]
#align algebraic_topology.alternating_coface_map_complex.d_squared AlgebraicTopology.AlternatingCofaceMapComplex.d_squared

/-- The alternating coface map complex, on objects -/
def obj : CochainComplex C ℕ :=
  CochainComplex.of (fun n => X.obj [n]) (objD X) (d_squared X)
#align algebraic_topology.alternating_coface_map_complex.obj AlgebraicTopology.AlternatingCofaceMapComplex.obj

variable {X} {Y}

/-- The alternating face map complex, on morphisms -/
@[simp]
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  CochainComplex.ofHom _ _ _ _ _ _ (fun n => f.app [n]) fun n =>
    by
    dsimp
    rw [comp_sum, sum_comp]
    apply Finset.sum_congr rfl fun x h => _
    rw [comp_zsmul, zsmul_comp]
    congr 1
    symm
    apply f.naturality
#align algebraic_topology.alternating_coface_map_complex.map AlgebraicTopology.AlternatingCofaceMapComplex.map

end AlternatingCofaceMapComplex

variable (C)

/-- The alternating coface map complex, as a functor -/
@[simps]
def alternatingCofaceMapComplex : CosimplicialObject C ⥤ CochainComplex C ℕ
    where
  obj := AlternatingCofaceMapComplex.obj
  map X Y f := AlternatingCofaceMapComplex.map f
#align algebraic_topology.alternating_coface_map_complex AlgebraicTopology.alternatingCofaceMapComplex

end AlgebraicTopology

