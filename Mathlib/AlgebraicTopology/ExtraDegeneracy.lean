/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.extra_degeneracy
! leanprover-community/mathlib commit 324a7502510e835cdbd3de1519b6c66b51fb2467
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.AlternatingFaceMapComplex
import Mathbin.AlgebraicTopology.SimplicialSet
import Mathbin.AlgebraicTopology.CechNerve
import Mathbin.Algebra.Homology.Homotopy
import Mathbin.Tactic.FinCases

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

- the structure `extra_degeneracy X` for any `X : simplicial_object.augmented C`
- `extra_degeneracy.map`: extra degeneracies are preserved by the application of any
functor `C ⥤ D`
- `sSet.augmented.standard_simplex.extra_degeneracy`: the standard `n`-simplex has
an extra degeneracy
- `arrow.augmented_cech_nerve.extra_degeneracy`: the Čech nerve of a split
epimorphism has an extra degeneracy
- `extra_degeneracy.homotopy_equiv`: in the case the category `C` is preadditive,
if we have an extra degeneracy on `X : simplicial_object.augmented C`, then
the augmentation on the alternating face map complex of `X` is a homotopy
equivalence.

## References
* [Paul G. Goerss, John F. Jardine, *Simplical Homotopy Theory*][goerss-jardine-2009]

-/


open CategoryTheory CategoryTheory.Category

open CategoryTheory.SimplicialObject.Augmented

open Opposite

open Simplicial

namespace SimplicialObject

namespace Augmented

variable {C : Type _} [Category C]

/-- The datum of an extra degeneracy is a technical condition on
augmented simplicial objects. The morphisms `s'` and `s n` of the
structure formally behave like extra degeneracies `σ (-1)`. -/
@[ext]
structure ExtraDegeneracy (X : SimplicialObject.Augmented C) where
  s' : point.obj X ⟶ drop.obj X _[0]
  s : ∀ n : ℕ, drop.obj X _[n] ⟶ drop.obj X _[n + 1]
  s'_comp_ε' : s' ≫ X.Hom.app (op [0]) = 𝟙 _
  s₀_comp_δ₁' : s 0 ≫ (drop.obj X).δ 1 = X.Hom.app (op [0]) ≫ s'
  s_comp_δ₀' : ∀ n : ℕ, s n ≫ (drop.obj X).δ 0 = 𝟙 _
  s_comp_δ' :
    ∀ (n : ℕ) (i : Fin (n + 2)), s (n + 1) ≫ (drop.obj X).δ i.succ = (drop.obj X).δ i ≫ s n
  s_comp_σ' :
    ∀ (n : ℕ) (i : Fin (n + 1)), s n ≫ (drop.obj X).σ i.succ = (drop.obj X).σ i ≫ s (n + 1)
#align simplicial_object.augmented.extra_degeneracy SimplicialObject.Augmented.ExtraDegeneracy

namespace ExtraDegeneracy

restate_axiom s'_comp_ε'

restate_axiom s₀_comp_δ₁'

restate_axiom s_comp_δ₀'

restate_axiom s_comp_δ'

restate_axiom s_comp_σ'

attribute [reassoc.1] s'_comp_ε s₀_comp_δ₁ s_comp_δ₀ s_comp_δ s_comp_σ

attribute [simp] s'_comp_ε s_comp_δ₀

/-- If `ed` is an extra degeneracy for `X : simplicial_object.augmented C` and
`F : C ⥤ D` is a functor, then `ed.map F` is an extra degeneracy for the
augmented simplical object in `D` obtained by applying `F` to `X`. -/
def map {D : Type _} [Category D] {X : SimplicialObject.Augmented C} (ed : ExtraDegeneracy X)
    (F : C ⥤ D) : ExtraDegeneracy (((whiskering _ _).obj F).obj X)
    where
  s' := F.map ed.s'
  s n := F.map (ed.s n)
  s'_comp_ε' := by
    dsimp
    erw [comp_id, ← F.map_comp, ed.s'_comp_ε, F.map_id]
  s₀_comp_δ₁' := by
    dsimp
    erw [comp_id, ← F.map_comp, ← F.map_comp, ed.s₀_comp_δ₁]
  s_comp_δ₀' n := by
    dsimp
    erw [← F.map_comp, ed.s_comp_δ₀, F.map_id]
  s_comp_δ' n i := by
    dsimp
    erw [← F.map_comp, ← F.map_comp, ed.s_comp_δ]
    rfl
  s_comp_σ' n i := by
    dsimp
    erw [← F.map_comp, ← F.map_comp, ed.s_comp_σ]
    rfl
#align simplicial_object.augmented.extra_degeneracy.map SimplicialObject.Augmented.ExtraDegeneracy.map

/-- If `X` and `Y` are isomorphic augmented simplicial objects, then an extra
degeneracy for `X` gives also an extra degeneracy for `Y` -/
def ofIso {X Y : SimplicialObject.Augmented C} (e : X ≅ Y) (ed : ExtraDegeneracy X) :
    ExtraDegeneracy Y
    where
  s' := (point.mapIso e).inv ≫ ed.s' ≫ (drop.mapIso e).Hom.app (op [0])
  s n := (drop.mapIso e).inv.app (op [n]) ≫ ed.s n ≫ (drop.mapIso e).Hom.app (op [n + 1])
  s'_comp_ε' := by
    simpa only [functor.map_iso, assoc, w₀, ed.s'_comp_ε_assoc] using (point.map_iso e).inv_hom_id
  s₀_comp_δ₁' := by
    have h := w₀ e.inv
    dsimp at h⊢
    simp only [assoc, ← simplicial_object.δ_naturality, ed.s₀_comp_δ₁_assoc, reassoc_of h]
  s_comp_δ₀' n := by
    have h := ed.s_comp_δ₀'
    dsimp at h⊢
    simpa only [assoc, ← simplicial_object.δ_naturality, reassoc_of h] using
      congr_app (drop.map_iso e).inv_hom_id (op [n])
  s_comp_δ' n i := by
    have h := ed.s_comp_δ' n i
    dsimp at h⊢
    simp only [assoc, ← simplicial_object.δ_naturality, reassoc_of h, ←
      simplicial_object.δ_naturality_assoc]
  s_comp_σ' n i := by
    have h := ed.s_comp_σ' n i
    dsimp at h⊢
    simp only [assoc, ← simplicial_object.σ_naturality, reassoc_of h, ←
      simplicial_object.σ_naturality_assoc]
#align simplicial_object.augmented.extra_degeneracy.of_iso SimplicialObject.Augmented.ExtraDegeneracy.ofIso

end ExtraDegeneracy

end Augmented

end SimplicialObject

namespace SSet

namespace Augmented

namespace StandardSimplex

/-- When `[has_zero X]`, the shift of a map `f : fin n → X`
is a map `fin (n+1) → X` which sends `0` to `0` and `i.succ` to `f i`. -/
def shiftFun {n : ℕ} {X : Type _} [Zero X] (f : Fin n → X) (i : Fin (n + 1)) : X :=
  dite (i = 0) (fun h => 0) fun h => f (i.pred h)
#align sSet.augmented.standard_simplex.shift_fun SSet.Augmented.standardSimplex.shiftFun

@[simp]
theorem shiftFun_0 {n : ℕ} {X : Type _} [Zero X] (f : Fin n → X) : shiftFun f 0 = 0 :=
  rfl
#align sSet.augmented.standard_simplex.shift_fun_0 SSet.Augmented.standardSimplex.shiftFun_0

@[simp]
theorem shiftFun_succ {n : ℕ} {X : Type _} [Zero X] (f : Fin n → X) (i : Fin n) :
    shiftFun f i.succ = f i := by
  dsimp [shift_fun]
  split_ifs
  · exfalso
    simpa only [Fin.ext_iff, Fin.val_succ] using h
  · simp only [Fin.pred_succ]
#align sSet.augmented.standard_simplex.shift_fun_succ SSet.Augmented.standardSimplex.shiftFun_succ

/-- The shift of a morphism `f : [n] → Δ` in `simplex_category` corresponds to
the monotone map which sends `0` to `0` and `i.succ` to `f.to_order_hom i`. -/
@[simp]
def shift {n : ℕ} {Δ : SimplexCategory} (f : [n] ⟶ Δ) : [n + 1] ⟶ Δ :=
  SimplexCategory.Hom.mk
    { toFun := shiftFun f.toOrderHom
      monotone' := fun i₁ i₂ hi => by
        by_cases h₁ : i₁ = 0
        · subst h₁
          simp only [shift_fun_0, Fin.zero_le]
        · have h₂ : i₂ ≠ 0 := by
            intro h₂
            subst h₂
            exact h₁ (le_antisymm hi (Fin.zero_le _))
          cases' Fin.eq_succ_of_ne_zero h₁ with j₁ hj₁
          cases' Fin.eq_succ_of_ne_zero h₂ with j₂ hj₂
          substs hj₁ hj₂
          simpa only [shift_fun_succ] using f.to_order_hom.monotone (fin.succ_le_succ_iff.mp hi) }
#align sSet.augmented.standard_simplex.shift SSet.Augmented.standardSimplex.shift

/-- The obvious extra degeneracy on the standard simplex. -/
@[protected]
def extraDegeneracy (Δ : SimplexCategory) :
    SimplicialObject.Augmented.ExtraDegeneracy (standardSimplex.obj Δ)
    where
  s' x := SimplexCategory.Hom.mk (OrderHom.const _ 0)
  s n f := shift f
  s'_comp_ε' := by
    ext1 j
    fin_cases j
  s₀_comp_δ₁' := by
    ext (x j)
    fin_cases j
    rfl
  s_comp_δ₀' n := by
    ext (φ i) : 4
    dsimp [simplicial_object.δ, SimplexCategory.δ, SSet.standardSimplex]
    simp only [shift_fun_succ]
  s_comp_δ' n i := by
    ext (φ j) : 4
    dsimp [simplicial_object.δ, SimplexCategory.δ, SSet.standardSimplex]
    by_cases j = 0
    · subst h
      simp only [Fin.succ_succAbove_zero, shift_fun_0]
    · cases' Fin.eq_succ_of_ne_zero h with k hk
      subst hk
      simp only [Fin.succ_succAbove_succ, shift_fun_succ]
  s_comp_σ' n i := by
    ext (φ j) : 4
    dsimp [simplicial_object.σ, SimplexCategory.σ, SSet.standardSimplex]
    by_cases j = 0
    · subst h
      simpa only [shift_fun_0] using shift_fun_0 φ.to_order_hom
    · cases' Fin.eq_succ_of_ne_zero h with k hk
      subst hk
      simp only [Fin.succ_predAbove_succ, shift_fun_succ]
#align sSet.augmented.standard_simplex.extra_degeneracy SSet.Augmented.standardSimplex.extraDegeneracy

instance nonempty_extraDegeneracy_standardSimplex (Δ : SimplexCategory) :
    Nonempty (SimplicialObject.Augmented.ExtraDegeneracy (standardSimplex.obj Δ)) :=
  ⟨standardSimplex.extraDegeneracy Δ⟩
#align sSet.augmented.standard_simplex.nonempty_extra_degeneracy_standard_simplex SSet.Augmented.standardSimplex.nonempty_extraDegeneracy_standardSimplex

end StandardSimplex

end Augmented

end SSet

namespace CategoryTheory

open Limits

namespace Arrow

namespace AugmentedCechNerve

variable {C : Type _} [Category C] (f : Arrow C)
  [∀ n : ℕ, HasWidePullback f.right (fun i : Fin (n + 1) => f.left) fun i => f.Hom]
  (S : SplitEpi f.Hom)

include S

/-- The extra degeneracy map on the Čech nerve of a split epi. It is
given on the `0`-projection by the given section of the split epi,
and by shifting the indices on the other projections. -/
noncomputable def ExtraDegeneracy.s (n : ℕ) :
    f.cechNerve.obj (op [n]) ⟶ f.cechNerve.obj (op [n + 1]) :=
  WidePullback.lift (WidePullback.base _)
    (fun i =>
      dite (i = 0) (fun h => WidePullback.base _ ≫ S.section_) fun h => WidePullback.π _ (i.pred h))
    fun i => by
    split_ifs
    · subst h
      simp only [assoc, split_epi.id, comp_id]
    · simp only [wide_pullback.π_arrow]
#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s CategoryTheory.Arrow.augmentedCechNerve.ExtraDegeneracy.s

@[simp]
theorem ExtraDegeneracy.s_comp_π_0 (n : ℕ) :
    ExtraDegeneracy.s f S n ≫ WidePullback.π _ 0 = WidePullback.base _ ≫ S.section_ :=
  by
  dsimp [extra_degeneracy.s]
  simpa only [wide_pullback.lift_π]
#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s_comp_π_0 CategoryTheory.Arrow.augmentedCechNerve.ExtraDegeneracy.s_comp_π_0

@[simp]
theorem ExtraDegeneracy.s_comp_π_succ (n : ℕ) (i : Fin (n + 1)) :
    ExtraDegeneracy.s f S n ≫ WidePullback.π _ i.succ = WidePullback.π _ i :=
  by
  dsimp [extra_degeneracy.s]
  simp only [wide_pullback.lift_π]
  split_ifs
  · exfalso
    simpa only [Fin.ext_iff, Fin.val_succ, Fin.val_zero, Nat.succ_ne_zero] using h
  · congr
    apply Fin.pred_succ
#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s_comp_π_succ CategoryTheory.Arrow.augmentedCechNerve.ExtraDegeneracy.s_comp_π_succ

@[simp]
theorem ExtraDegeneracy.s_comp_base (n : ℕ) :
    ExtraDegeneracy.s f S n ≫ WidePullback.base _ = WidePullback.base _ := by
  apply wide_pullback.lift_base
#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s_comp_base CategoryTheory.Arrow.augmentedCechNerve.ExtraDegeneracy.s_comp_base

/-- The augmented Čech nerve associated to a split epimorphism has an extra degeneracy. -/
noncomputable def extraDegeneracy : SimplicialObject.Augmented.ExtraDegeneracy f.augmentedCechNerve
    where
  s' := S.section_ ≫ WidePullback.lift f.Hom (fun i => 𝟙 _) fun i => by rw [id_comp]
  s n := ExtraDegeneracy.s f S n
  s'_comp_ε' := by
    simp only [augmented_cech_nerve_hom_app, assoc, wide_pullback.lift_base, split_epi.id]
  s₀_comp_δ₁' := by
    dsimp [cech_nerve, simplicial_object.δ, SimplexCategory.δ]
    ext j
    · fin_cases j
      simpa only [assoc, wide_pullback.lift_π, comp_id] using extra_degeneracy.s_comp_π_0 f S 0
    ·
      simpa only [assoc, wide_pullback.lift_base, split_epi.id, comp_id] using
        extra_degeneracy.s_comp_base f S 0
  s_comp_δ₀' n := by
    dsimp [cech_nerve, simplicial_object.δ, SimplexCategory.δ]
    ext j
    · simpa only [assoc, wide_pullback.lift_π, id_comp] using extra_degeneracy.s_comp_π_succ f S n j
    · simpa only [assoc, wide_pullback.lift_base, id_comp] using extra_degeneracy.s_comp_base f S n
  s_comp_δ' n i := by
    dsimp [cech_nerve, simplicial_object.δ, SimplexCategory.δ]
    ext j
    · simp only [assoc, wide_pullback.lift_π]
      by_cases j = 0
      · subst h
        erw [Fin.succ_succAbove_zero, extra_degeneracy.s_comp_π_0, extra_degeneracy.s_comp_π_0]
        dsimp
        simp only [wide_pullback.lift_base_assoc]
      · cases' Fin.eq_succ_of_ne_zero h with k hk
        subst hk
        erw [Fin.succ_succAbove_succ, extra_degeneracy.s_comp_π_succ,
          extra_degeneracy.s_comp_π_succ]
        dsimp
        simp only [wide_pullback.lift_π]
    · simp only [assoc, wide_pullback.lift_base]
      erw [extra_degeneracy.s_comp_base, extra_degeneracy.s_comp_base]
      dsimp
      simp only [wide_pullback.lift_base]
  s_comp_σ' n i := by
    dsimp [cech_nerve, simplicial_object.σ, SimplexCategory.σ]
    ext j
    · simp only [assoc, wide_pullback.lift_π]
      by_cases j = 0
      · subst h
        erw [extra_degeneracy.s_comp_π_0, extra_degeneracy.s_comp_π_0]
        dsimp
        simp only [wide_pullback.lift_base_assoc]
      · cases' Fin.eq_succ_of_ne_zero h with k hk
        subst hk
        erw [Fin.succ_predAbove_succ, extra_degeneracy.s_comp_π_succ,
          extra_degeneracy.s_comp_π_succ]
        dsimp
        simp only [wide_pullback.lift_π]
    · simp only [assoc, wide_pullback.lift_base]
      erw [extra_degeneracy.s_comp_base, extra_degeneracy.s_comp_base]
      dsimp
      simp only [wide_pullback.lift_base]
#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy CategoryTheory.Arrow.augmentedCechNerve.extraDegeneracy

end AugmentedCechNerve

end Arrow

end CategoryTheory

namespace SimplicialObject

namespace Augmented

namespace ExtraDegeneracy

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

/-- If `C` is a preadditive category and `X` is an augmented simplicial object
in `C` that has an extra degeneracy, then the augmentation on the alternating
face map complex of `X` is an homotopy equivalence. -/
noncomputable def homotopyEquiv {C : Type _} [Category C] [Preadditive C] [HasZeroObject C]
    {X : SimplicialObject.Augmented C} (ed : ExtraDegeneracy X) :
    HomotopyEquiv (AlgebraicTopology.AlternatingFaceMapComplex.obj (drop.obj X))
      ((ChainComplex.single₀ C).obj (point.obj X))
    where
  Hom := AlternatingFaceMapComplex.ε.app X
  inv := (ChainComplex.fromSingle₀Equiv _ _).invFun ed.s'
  homotopyInvHomId :=
    Homotopy.ofEq
      (by
        ext
        exact ed.s'_comp_ε)
  homotopyHomInvId :=
    { Hom := fun i j => by
        by_cases i + 1 = j
        · exact (-ed.s i) ≫ eq_to_hom (by congr )
        · exact 0
      zero' := fun i j hij => by
        split_ifs
        · exfalso
          exact hij h
        · simp only [eq_self_iff_true]
      comm := fun i => by
        cases i
        · rw [Homotopy.prevD_chainComplex, Homotopy.dNext_zero_chainComplex, zero_add]
          dsimp [ChainComplex.fromSingle₀Equiv, ChainComplex.toSingle₀Equiv]
          simp only [zero_add, eq_self_iff_true, preadditive.neg_comp, comp_id, if_true,
            alternating_face_map_complex.obj_d_eq, Fin.sum_univ_two, Fin.val_zero, pow_zero,
            one_zsmul, Fin.val_one, pow_one, neg_smul, preadditive.comp_add, ← s₀_comp_δ₁,
            s_comp_δ₀, preadditive.comp_neg, neg_add_rev, neg_neg, neg_add_cancel_right,
            neg_add_cancel_comm]
        · rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex]
          dsimp [ChainComplex.toSingle₀Equiv, ChainComplex.fromSingle₀Equiv]
          simp only [zero_comp, alternating_face_map_complex.obj_d_eq, eq_self_iff_true,
            preadditive.neg_comp, comp_id, if_true, preadditive.comp_neg,
            @Fin.sum_univ_succ _ _ (i + 2), preadditive.comp_add, Fin.val_zero, pow_zero, one_zsmul,
            s_comp_δ₀, Fin.val_succ, pow_add, pow_one, mul_neg, neg_zsmul, preadditive.comp_sum,
            preadditive.sum_comp, neg_neg, mul_one, preadditive.comp_zsmul, preadditive.zsmul_comp,
            s_comp_δ, zsmul_neg]
          rw [add_comm (-𝟙 _), add_assoc, add_assoc, add_left_neg, add_zero, Finset.sum_neg_distrib,
            add_left_neg] }
#align simplicial_object.augmented.extra_degeneracy.homotopy_equiv SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv

end ExtraDegeneracy

end Augmented

end SimplicialObject

