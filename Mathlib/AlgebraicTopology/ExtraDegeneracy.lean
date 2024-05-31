/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Tactic.FinCases

#align_import algebraic_topology.extra_degeneracy from "leanprover-community/mathlib"@"324a7502510e835cdbd3de1519b6c66b51fb2467"

/-!

# Augmented simplicial objects with an extra degeneracy

In simplicial homotopy theory, in order to prove that the connected components
of a simplicial set `X` are contractible, it suffices to construct an extra
degeneracy as it is defined in *Simplicial Homotopy Theory* by Goerss-Jardine p. 190.
It consists of a series of maps `π₀ X → X _[0]` and `X _[n] → X _[n+1]` which
behave formally like an extra degeneracy `σ (-1)`. It can be thought as a datum
associated to the augmented simplicial set `X → π₀ X`.

In this file, we adapt this definition to the case of augmented
simplicial objects in any category.

## Main definitions

- the structure `ExtraDegeneracy X` for any `X : SimplicialObject.Augmented C`
- `ExtraDegeneracy.map`: extra degeneracies are preserved by the application of any
functor `C ⥤ D`
- `SSet.Augmented.StandardSimplex.extraDegeneracy`: the standard `n`-simplex has
an extra degeneracy
- `Arrow.AugmentedCechNerve.extraDegeneracy`: the Čech nerve of a split
epimorphism has an extra degeneracy
- `ExtraDegeneracy.homotopyEquiv`: in the case the category `C` is preadditive,
if we have an extra degeneracy on `X : SimplicialObject.Augmented C`, then
the augmentation on the alternating face map complex of `X` is a homotopy
equivalence.

## References
* [Paul G. Goerss, John F. Jardine, *Simplicial Homotopy Theory*][goerss-jardine-2009]

-/


open CategoryTheory Category SimplicialObject.Augmented Opposite Simplicial

namespace SimplicialObject

namespace Augmented

variable {C : Type*} [Category C]

-- Porting note: in the formulation of the axioms `s_comp_δ₀`, etc, `drop.obj X` has been
-- replaced by `X.left` in order to have lemmas with LHS/RHS in normal form
/-- The datum of an extra degeneracy is a technical condition on
augmented simplicial objects. The morphisms `s'` and `s n` of the
structure formally behave like extra degeneracies `σ (-1)`. -/
@[ext]
structure ExtraDegeneracy (X : SimplicialObject.Augmented C) where
  s' : point.obj X ⟶ drop.obj X _[0]
  s : ∀ n : ℕ, drop.obj X _[n] ⟶ drop.obj X _[n + 1]
  s'_comp_ε : s' ≫ X.hom.app (op [0]) = 𝟙 _
  s₀_comp_δ₁ : s 0 ≫ X.left.δ 1 = X.hom.app (op [0]) ≫ s'
  s_comp_δ₀ : ∀ n : ℕ, s n ≫ X.left.δ 0 = 𝟙 _
  s_comp_δ :
    ∀ (n : ℕ) (i : Fin (n + 2)), s (n + 1) ≫ X.left.δ i.succ = X.left.δ i ≫ s n
  s_comp_σ :
    ∀ (n : ℕ) (i : Fin (n + 1)), s n ≫ X.left.σ i.succ = X.left.σ i ≫ s (n + 1)
#align simplicial_object.augmented.extra_degeneracy SimplicialObject.Augmented.ExtraDegeneracy

namespace ExtraDegeneracy

attribute [reassoc] s₀_comp_δ₁ s_comp_δ s_comp_σ
attribute [reassoc (attr := simp)] s'_comp_ε s_comp_δ₀

/-- If `ed` is an extra degeneracy for `X : SimplicialObject.Augmented C` and
`F : C ⥤ D` is a functor, then `ed.map F` is an extra degeneracy for the
augmented simplicial object in `D` obtained by applying `F` to `X`. -/
def map {D : Type*} [Category D] {X : SimplicialObject.Augmented C} (ed : ExtraDegeneracy X)
    (F : C ⥤ D) : ExtraDegeneracy (((whiskering _ _).obj F).obj X) where
  s' := F.map ed.s'
  s n := F.map (ed.s n)
  s'_comp_ε := by
    dsimp
    erw [comp_id, ← F.map_comp, ed.s'_comp_ε, F.map_id]
  s₀_comp_δ₁ := by
    dsimp
    erw [comp_id, ← F.map_comp, ← F.map_comp, ed.s₀_comp_δ₁]
  s_comp_δ₀ n := by
    dsimp
    erw [← F.map_comp, ed.s_comp_δ₀, F.map_id]
  s_comp_δ n i := by
    dsimp
    erw [← F.map_comp, ← F.map_comp, ed.s_comp_δ]
    rfl
  s_comp_σ n i := by
    dsimp
    erw [← F.map_comp, ← F.map_comp, ed.s_comp_σ]
    rfl
#align simplicial_object.augmented.extra_degeneracy.map SimplicialObject.Augmented.ExtraDegeneracy.map

/-- If `X` and `Y` are isomorphic augmented simplicial objects, then an extra
degeneracy for `X` gives also an extra degeneracy for `Y` -/
def ofIso {X Y : SimplicialObject.Augmented C} (e : X ≅ Y) (ed : ExtraDegeneracy X) :
    ExtraDegeneracy Y where
  s' := (point.mapIso e).inv ≫ ed.s' ≫ (drop.mapIso e).hom.app (op [0])
  s n := (drop.mapIso e).inv.app (op [n]) ≫ ed.s n ≫ (drop.mapIso e).hom.app (op [n + 1])
  s'_comp_ε := by
    simpa only [Functor.mapIso, assoc, w₀, ed.s'_comp_ε_assoc] using (point.mapIso e).inv_hom_id
  s₀_comp_δ₁ := by
    have h := w₀ e.inv
    dsimp at h ⊢
    simp only [assoc, ← SimplicialObject.δ_naturality, ed.s₀_comp_δ₁_assoc, reassoc_of% h]
  s_comp_δ₀ n := by
    have h := ed.s_comp_δ₀
    dsimp at h ⊢
    simpa only [assoc, ← SimplicialObject.δ_naturality, reassoc_of% h] using
      congr_app (drop.mapIso e).inv_hom_id (op [n])
  s_comp_δ n i := by
    have h := ed.s_comp_δ n i
    dsimp at h ⊢
    simp only [assoc, ← SimplicialObject.δ_naturality, reassoc_of% h,
      ← SimplicialObject.δ_naturality_assoc]
  s_comp_σ n i := by
    have h := ed.s_comp_σ n i
    dsimp at h ⊢
    simp only [assoc, ← SimplicialObject.σ_naturality, reassoc_of% h,
      ← SimplicialObject.σ_naturality_assoc]
#align simplicial_object.augmented.extra_degeneracy.of_iso SimplicialObject.Augmented.ExtraDegeneracy.ofIso

end ExtraDegeneracy

end Augmented

end SimplicialObject

namespace SSet

namespace Augmented

namespace StandardSimplex

/-- When `[HasZero X]`, the shift of a map `f : Fin n → X`
is a map `Fin (n+1) → X` which sends `0` to `0` and `i.succ` to `f i`. -/
def shiftFun {n : ℕ} {X : Type*} [Zero X] (f : Fin n → X) (i : Fin (n + 1)) : X :=
  dite (i = 0) (fun _ => 0) fun h => f (i.pred h)
set_option linter.uppercaseLean3 false in
#align sSet.augmented.standard_simplex.shift_fun SSet.Augmented.StandardSimplex.shiftFun

@[simp]
theorem shiftFun_0 {n : ℕ} {X : Type*} [Zero X] (f : Fin n → X) : shiftFun f 0 = 0 :=
  rfl
set_option linter.uppercaseLean3 false in
#align sSet.augmented.standard_simplex.shift_fun_0 SSet.Augmented.StandardSimplex.shiftFun_0

@[simp]
theorem shiftFun_succ {n : ℕ} {X : Type*} [Zero X] (f : Fin n → X) (i : Fin n) :
    shiftFun f i.succ = f i := by
  dsimp [shiftFun]
  split_ifs with h
  · exfalso
    simp only [Fin.ext_iff, Fin.val_succ, Fin.val_zero, add_eq_zero, and_false] at h
  · simp only [Fin.pred_succ]
set_option linter.uppercaseLean3 false in
#align sSet.augmented.standard_simplex.shift_fun_succ SSet.Augmented.StandardSimplex.shiftFun_succ

/-- The shift of a morphism `f : [n] → Δ` in `SimplexCategory` corresponds to
the monotone map which sends `0` to `0` and `i.succ` to `f.toOrderHom i`. -/
@[simp]
def shift {n : ℕ} {Δ : SimplexCategory}
    (f : ([n] : SimplexCategory) ⟶ Δ) : ([n + 1] : SimplexCategory) ⟶ Δ :=
  SimplexCategory.Hom.mk
    { toFun := shiftFun f.toOrderHom
      monotone' := fun i₁ i₂ hi => by
        by_cases h₁ : i₁ = 0
        · subst h₁
          simp only [shiftFun_0, Fin.zero_le]
        · have h₂ : i₂ ≠ 0 := by
            intro h₂
            subst h₂
            exact h₁ (le_antisymm hi (Fin.zero_le _))
          cases' Fin.eq_succ_of_ne_zero h₁ with j₁ hj₁
          cases' Fin.eq_succ_of_ne_zero h₂ with j₂ hj₂
          substs hj₁ hj₂
          simpa only [shiftFun_succ] using f.toOrderHom.monotone (Fin.succ_le_succ_iff.mp hi) }
set_option linter.uppercaseLean3 false in
#align sSet.augmented.standard_simplex.shift SSet.Augmented.StandardSimplex.shift

open SSet.standardSimplex in
/-- The obvious extra degeneracy on the standard simplex. -/
protected noncomputable def extraDegeneracy (Δ : SimplexCategory) :
    SimplicialObject.Augmented.ExtraDegeneracy (standardSimplex.obj Δ) where
  s' _ := objMk (OrderHom.const _ 0)
  s  n f := (objEquiv _ _).symm
    (shift (objEquiv _ _ f))
  s'_comp_ε := by
    dsimp
    apply Subsingleton.elim
  s₀_comp_δ₁ := by
    dsimp
    ext1 x
    apply (objEquiv _ _).injective
    ext j
    fin_cases j
    rfl
  s_comp_δ₀ n := by
    ext1 φ
    apply (objEquiv _ _).injective
    apply SimplexCategory.Hom.ext
    ext i : 2
    dsimp [SimplicialObject.δ, SimplexCategory.δ, SSet.standardSimplex,
      objEquiv, Equiv.ulift, uliftFunctor]
    simp only [shiftFun_succ]
  s_comp_δ n i := by
    ext1 φ
    apply (objEquiv _ _).injective
    apply SimplexCategory.Hom.ext
    ext j : 2
    dsimp [SimplicialObject.δ, SimplexCategory.δ, SSet.standardSimplex,
      objEquiv, Equiv.ulift, uliftFunctor]
    by_cases h : j = 0
    · subst h
      simp only [Fin.succ_succAbove_zero, shiftFun_0]
    · obtain ⟨_, rfl⟩ := Fin.eq_succ_of_ne_zero <| h
      simp only [Fin.succ_succAbove_succ, shiftFun_succ, Function.comp_apply,
        Fin.succAboveOrderEmb_apply]
  s_comp_σ n i := by
    ext1 φ
    apply (objEquiv _ _).injective
    apply SimplexCategory.Hom.ext
    ext j : 2
    dsimp [SimplicialObject.σ, SimplexCategory.σ, SSet.standardSimplex,
      objEquiv, Equiv.ulift, uliftFunctor]
    by_cases h : j = 0
    · subst h
      rfl
    · obtain ⟨_, rfl⟩ := Fin.eq_succ_of_ne_zero h
      simp only [Fin.succ_predAbove_succ, shiftFun_succ, Function.comp_apply]
set_option linter.uppercaseLean3 false in
#align sSet.augmented.standard_simplex.extra_degeneracy SSet.Augmented.StandardSimplex.extraDegeneracy

instance nonempty_extraDegeneracy_standardSimplex (Δ : SimplexCategory) :
    Nonempty (SimplicialObject.Augmented.ExtraDegeneracy (standardSimplex.obj Δ)) :=
  ⟨StandardSimplex.extraDegeneracy Δ⟩
set_option linter.uppercaseLean3 false in
#align sSet.augmented.standard_simplex.nonempty_extra_degeneracy_standard_simplex SSet.Augmented.StandardSimplex.nonempty_extraDegeneracy_standardSimplex

end StandardSimplex

end Augmented

end SSet

namespace CategoryTheory

open Limits

namespace Arrow

namespace AugmentedCechNerve

variable {C : Type*} [Category C] (f : Arrow C)
  [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]
  (S : SplitEpi f.hom)

/-- The extra degeneracy map on the Čech nerve of a split epi. It is
given on the `0`-projection by the given section of the split epi,
and by shifting the indices on the other projections. -/
noncomputable def ExtraDegeneracy.s (n : ℕ) :
    f.cechNerve.obj (op [n]) ⟶ f.cechNerve.obj (op [n + 1]) :=
  WidePullback.lift (WidePullback.base _)
    (fun i =>
      dite (i = 0)
        (fun _ => WidePullback.base _ ≫ S.section_)
        (fun h => WidePullback.π _ (i.pred h)))
    fun i => by
      dsimp
      split_ifs with h
      · subst h
        simp only [assoc, SplitEpi.id, comp_id]
      · simp only [WidePullback.π_arrow]
#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s

-- Porting note (#11119): @[simp] removed as the linter complains the LHS is not in normal form
theorem ExtraDegeneracy.s_comp_π_0 (n : ℕ) :
    ExtraDegeneracy.s f S n ≫ WidePullback.π _ 0 =
      @WidePullback.base _ _ _ f.right (fun _ : Fin (n + 1) => f.left) (fun _ => f.hom) _ ≫
        S.section_ := by
  dsimp [ExtraDegeneracy.s]
  simp only [WidePullback.lift_π]
  rfl

-- Porting note (#11119): @[simp] removed as the linter complains the LHS is not in normal form
theorem ExtraDegeneracy.s_comp_π_succ (n : ℕ) (i : Fin (n + 1)) :
    ExtraDegeneracy.s f S n ≫ WidePullback.π _ i.succ =
      @WidePullback.π _ _ _ f.right (fun _ : Fin (n + 1) => f.left) (fun _ => f.hom) _ i := by
  dsimp [ExtraDegeneracy.s]
  simp only [WidePullback.lift_π]
  split_ifs with h
  · simp only [Fin.ext_iff, Fin.val_succ, Fin.val_zero, add_eq_zero, and_false] at h
  · simp only [Fin.pred_succ]
#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s_comp_π_succ CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s_comp_π_succ

-- Porting note (#11119): @[simp] removed as the linter complains the LHS is not in normal form
theorem ExtraDegeneracy.s_comp_base (n : ℕ) :
    ExtraDegeneracy.s f S n ≫ WidePullback.base _ = WidePullback.base _ := by
  apply WidePullback.lift_base
#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s_comp_base CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s_comp_base

/-- The augmented Čech nerve associated to a split epimorphism has an extra degeneracy. -/
noncomputable def extraDegeneracy :
    SimplicialObject.Augmented.ExtraDegeneracy f.augmentedCechNerve where
  s' := S.section_ ≫ WidePullback.lift f.hom (fun _ => 𝟙 _) fun i => by rw [id_comp]
  s n := ExtraDegeneracy.s f S n
  s'_comp_ε := by
    dsimp
    simp only [augmentedCechNerve_hom_app, assoc, WidePullback.lift_base, SplitEpi.id]
  s₀_comp_δ₁ := by
    dsimp [cechNerve, SimplicialObject.δ, SimplexCategory.δ]
    ext j
    · fin_cases j
      simpa only [assoc, WidePullback.lift_π, comp_id] using ExtraDegeneracy.s_comp_π_0 f S 0
    · simpa only [assoc, WidePullback.lift_base, SplitEpi.id, comp_id] using
        ExtraDegeneracy.s_comp_base f S 0
  s_comp_δ₀ n := by
    dsimp [cechNerve, SimplicialObject.δ, SimplexCategory.δ]
    ext j
    · simpa only [assoc, WidePullback.lift_π, id_comp] using ExtraDegeneracy.s_comp_π_succ f S n j
    · simpa only [assoc, WidePullback.lift_base, id_comp] using ExtraDegeneracy.s_comp_base f S n
  s_comp_δ n i := by
    dsimp [cechNerve, SimplicialObject.δ, SimplexCategory.δ]
    ext j
    · simp only [assoc, WidePullback.lift_π]
      by_cases h : j = 0
      · subst h
        erw [Fin.succ_succAbove_zero, ExtraDegeneracy.s_comp_π_0, ExtraDegeneracy.s_comp_π_0]
        dsimp
        simp only [WidePullback.lift_base_assoc]
      · cases' Fin.eq_succ_of_ne_zero h with k hk
        subst hk
        erw [Fin.succ_succAbove_succ, ExtraDegeneracy.s_comp_π_succ,
          ExtraDegeneracy.s_comp_π_succ]
        simp only [WidePullback.lift_π]
    · simp only [assoc, WidePullback.lift_base]
      erw [ExtraDegeneracy.s_comp_base, ExtraDegeneracy.s_comp_base]
      dsimp
      simp only [WidePullback.lift_base]
  s_comp_σ n i := by
    dsimp [cechNerve, SimplicialObject.σ, SimplexCategory.σ]
    ext j
    · simp only [assoc, WidePullback.lift_π]
      by_cases h : j = 0
      · subst h
        erw [ExtraDegeneracy.s_comp_π_0, ExtraDegeneracy.s_comp_π_0]
        dsimp
        simp only [WidePullback.lift_base_assoc]
      · cases' Fin.eq_succ_of_ne_zero h with k hk
        subst hk
        erw [Fin.succ_predAbove_succ, ExtraDegeneracy.s_comp_π_succ,
          ExtraDegeneracy.s_comp_π_succ]
        simp only [WidePullback.lift_π]
    · simp only [assoc, WidePullback.lift_base]
      erw [ExtraDegeneracy.s_comp_base, ExtraDegeneracy.s_comp_base]
      dsimp
      simp only [WidePullback.lift_base]
#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy CategoryTheory.Arrow.AugmentedCechNerve.extraDegeneracy

end AugmentedCechNerve

end Arrow

end CategoryTheory

namespace SimplicialObject

namespace Augmented

namespace ExtraDegeneracy

open AlgebraicTopology CategoryTheory Limits

/-- If `C` is a preadditive category and `X` is an augmented simplicial object
in `C` that has an extra degeneracy, then the augmentation on the alternating
face map complex of `X` is a homotopy equivalence. -/
noncomputable def homotopyEquiv {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    {X : SimplicialObject.Augmented C} (ed : ExtraDegeneracy X) :
    HomotopyEquiv (AlgebraicTopology.AlternatingFaceMapComplex.obj (drop.obj X))
      ((ChainComplex.single₀ C).obj (point.obj X)) where
  hom := AlternatingFaceMapComplex.ε.app X
  inv := (ChainComplex.fromSingle₀Equiv _ _).symm (by exact ed.s')
  homotopyInvHomId := Homotopy.ofEq (by
    ext
    dsimp
    erw [AlternatingFaceMapComplex.ε_app_f_zero,
      ChainComplex.fromSingle₀Equiv_symm_apply_f_zero, s'_comp_ε]
    rfl)
  homotopyHomInvId :=
    { hom := fun i j => by
        by_cases i + 1 = j
        · exact (-ed.s i) ≫ eqToHom (by congr)
        · exact 0
      zero := fun i j hij => by
        dsimp
        split_ifs with h
        · exfalso
          exact hij h
        · simp only [eq_self_iff_true]
      comm := fun i => by
        rcases i with _|i
        · rw [Homotopy.prevD_chainComplex, Homotopy.dNext_zero_chainComplex, zero_add]
          dsimp
          erw [ChainComplex.fromSingle₀Equiv_symm_apply_f_zero]
          simp only [comp_id, ite_true, zero_add, ComplexShape.down_Rel, not_true,
            AlternatingFaceMapComplex.obj_d_eq, Preadditive.neg_comp]
          rw [Fin.sum_univ_two]
          simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
            Preadditive.comp_add, s_comp_δ₀, drop_obj, Preadditive.comp_neg, neg_add_rev,
            neg_neg, neg_add_cancel_right, s₀_comp_δ₁,
            AlternatingFaceMapComplex.ε_app_f_zero]
        · rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex]
          dsimp
          simp only [Preadditive.neg_comp,
            AlternatingFaceMapComplex.obj_d_eq, comp_id, ite_true, Preadditive.comp_neg,
            @Fin.sum_univ_succ _ _ (i + 2), Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
            Preadditive.comp_add, drop_obj, s_comp_δ₀, Preadditive.sum_comp,
            Preadditive.zsmul_comp, Preadditive.comp_sum, Preadditive.comp_zsmul,
            zsmul_neg, s_comp_δ, pow_add, pow_one, mul_neg, mul_one, neg_zsmul, neg_neg,
            neg_add_cancel_comm_assoc, add_left_neg, zero_comp] }
#align simplicial_object.augmented.extra_degeneracy.homotopy_equiv SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv

end ExtraDegeneracy

end Augmented

end SimplicialObject
