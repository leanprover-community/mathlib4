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
* [Paul G. Goerss, John F. Jardine, *Simplical Homotopy Theory*][goerss-jardine-2009]

-/


open CategoryTheory Category SimplicialObject.Augmented Opposite Simplicial

namespace SimplicialObject

namespace Augmented

variable {C : Type*} [Category C]

-- porting note: in the formulation of the axioms `s_comp_δ₀`, etc, `drop.obj X` has been
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
augmented simplical object in `D` obtained by applying `F` to `X`. -/
def map {D : Type*} [Category D] {X : SimplicialObject.Augmented C} (ed : ExtraDegeneracy X)
    (F : C ⥤ D) : ExtraDegeneracy (((whiskering _ _).obj F).obj X) where
  s' := F.map ed.s'
  s n := F.map (ed.s n)
  s'_comp_ε := by
    dsimp
    -- ⊢ F.map ed.s' ≫ F.map (NatTrans.app X.hom (op [0])) ≫ 𝟙 (F.obj X.right) = 𝟙 (F …
    erw [comp_id, ← F.map_comp, ed.s'_comp_ε, F.map_id]
    -- 🎉 no goals
  s₀_comp_δ₁ := by
    dsimp
    -- ⊢ F.map (s ed 0) ≫ SimplicialObject.δ (((SimplicialObject.whiskering C D).obj  …
    erw [comp_id, ← F.map_comp, ← F.map_comp, ed.s₀_comp_δ₁]
    -- 🎉 no goals
  s_comp_δ₀ n := by
    dsimp
    -- ⊢ F.map (s ed n) ≫ SimplicialObject.δ (((SimplicialObject.whiskering C D).obj  …
    erw [← F.map_comp, ed.s_comp_δ₀, F.map_id]
    -- 🎉 no goals
  s_comp_δ n i := by
    dsimp
    -- ⊢ F.map (s ed (n + 1)) ≫ SimplicialObject.δ (((SimplicialObject.whiskering C D …
    erw [← F.map_comp, ← F.map_comp, ed.s_comp_δ]
    -- ⊢ F.map (SimplicialObject.δ X.left i ≫ s ed n) = F.map (X.left.map (SimplexCat …
    rfl
    -- 🎉 no goals
  s_comp_σ n i := by
    dsimp
    -- ⊢ F.map (s ed n) ≫ SimplicialObject.σ (((SimplicialObject.whiskering C D).obj  …
    erw [← F.map_comp, ← F.map_comp, ed.s_comp_σ]
    -- ⊢ F.map (SimplicialObject.σ X.left i ≫ s ed (n + 1)) = F.map (X.left.map (Simp …
    rfl
    -- 🎉 no goals
#align simplicial_object.augmented.extra_degeneracy.map SimplicialObject.Augmented.ExtraDegeneracy.map

/-- If `X` and `Y` are isomorphic augmented simplicial objects, then an extra
degeneracy for `X` gives also an extra degeneracy for `Y` -/
def ofIso {X Y : SimplicialObject.Augmented C} (e : X ≅ Y) (ed : ExtraDegeneracy X) :
    ExtraDegeneracy Y where
  s' := (point.mapIso e).inv ≫ ed.s' ≫ (drop.mapIso e).hom.app (op [0])
  s n := (drop.mapIso e).inv.app (op [n]) ≫ ed.s n ≫ (drop.mapIso e).hom.app (op [n + 1])
  s'_comp_ε := by
    simpa only [Functor.mapIso, assoc, w₀, ed.s'_comp_ε_assoc] using (point.mapIso e).inv_hom_id
    -- 🎉 no goals
  s₀_comp_δ₁ := by
    have h := w₀ e.inv
    -- ⊢ (fun n => NatTrans.app (drop.mapIso e).inv (op [n]) ≫ s ed n ≫ NatTrans.app  …
    dsimp at h ⊢
    -- ⊢ (NatTrans.app e.inv.left (op [0]) ≫ s ed 0 ≫ NatTrans.app e.hom.left (op [0  …
    simp only [assoc, ← SimplicialObject.δ_naturality, ed.s₀_comp_δ₁_assoc, reassoc_of% h]
    -- 🎉 no goals
  s_comp_δ₀ n := by
    have h := ed.s_comp_δ₀
    -- ⊢ (fun n => NatTrans.app (drop.mapIso e).inv (op [n]) ≫ s ed n ≫ NatTrans.app  …
    dsimp at h ⊢
    -- ⊢ (NatTrans.app e.inv.left (op [n]) ≫ s ed n ≫ NatTrans.app e.hom.left (op [n  …
    simpa only [assoc, ← SimplicialObject.δ_naturality, reassoc_of% h] using
      congr_app (drop.mapIso e).inv_hom_id (op [n])
  s_comp_δ n i := by
    have h := ed.s_comp_δ n i
    -- ⊢ (fun n => NatTrans.app (drop.mapIso e).inv (op [n]) ≫ s ed n ≫ NatTrans.app  …
    dsimp at h ⊢
    -- ⊢ (NatTrans.app e.inv.left (op [n + 1]) ≫ s ed (n + 1) ≫ NatTrans.app e.hom.le …
    simp only [assoc, ← SimplicialObject.δ_naturality, reassoc_of% h,
      ← SimplicialObject.δ_naturality_assoc]
  s_comp_σ n i := by
    have h := ed.s_comp_σ n i
    -- ⊢ (fun n => NatTrans.app (drop.mapIso e).inv (op [n]) ≫ s ed n ≫ NatTrans.app  …
    dsimp at h ⊢
    -- ⊢ (NatTrans.app e.inv.left (op [n]) ≫ s ed n ≫ NatTrans.app e.hom.left (op [n  …
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
  -- ⊢ (if x : Fin.succ i = 0 then 0 else f (Fin.pred (Fin.succ i) x)) = f i
  split_ifs with h
  -- ⊢ 0 = f i
  · exfalso
    -- ⊢ False
    simp only [Fin.ext_iff, Fin.val_succ, Fin.val_zero, add_eq_zero, and_false] at h
    -- 🎉 no goals
  · simp only [Fin.pred_succ]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align sSet.augmented.standard_simplex.shift_fun_succ SSet.Augmented.StandardSimplex.shiftFun_succ

/-- The shift of a morphism `f : [n] → Δ` in `SimplexCategory` corresponds to
the monotone map which sends `0` to `0` and `i.succ` to `f.to_order_hom i`. -/
@[simp]
def shift {n : ℕ} {Δ : SimplexCategory}
    (f : ([n] : SimplexCategory) ⟶ Δ) : ([n + 1] : SimplexCategory) ⟶ Δ :=
  SimplexCategory.Hom.mk
    { toFun := shiftFun f.toOrderHom
      monotone' := fun i₁ i₂ hi => by
        by_cases h₁ : i₁ = 0
        -- ⊢ shiftFun (↑(SimplexCategory.Hom.toOrderHom f)) i₁ ≤ shiftFun (↑(SimplexCateg …
        · subst h₁
          -- ⊢ shiftFun (↑(SimplexCategory.Hom.toOrderHom f)) 0 ≤ shiftFun (↑(SimplexCatego …
          simp only [shiftFun_0, Fin.zero_le]
          -- 🎉 no goals
        · have h₂ : i₂ ≠ 0 := by
            intro h₂
            subst h₂
            exact h₁ (le_antisymm hi (Fin.zero_le _))
          cases' Fin.eq_succ_of_ne_zero h₁ with j₁ hj₁
          -- ⊢ shiftFun (↑(SimplexCategory.Hom.toOrderHom f)) i₁ ≤ shiftFun (↑(SimplexCateg …
          cases' Fin.eq_succ_of_ne_zero h₂ with j₂ hj₂
          -- ⊢ shiftFun (↑(SimplexCategory.Hom.toOrderHom f)) i₁ ≤ shiftFun (↑(SimplexCateg …
          substs hj₁ hj₂
          -- ⊢ shiftFun (↑(SimplexCategory.Hom.toOrderHom f)) (Fin.succ j₁) ≤ shiftFun (↑(S …
          simpa only [shiftFun_succ] using f.toOrderHom.monotone (Fin.succ_le_succ_iff.mp hi) }
          -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align sSet.augmented.standard_simplex.shift SSet.Augmented.StandardSimplex.shift

/-- The obvious extra degeneracy on the standard simplex. -/
protected noncomputable def extraDegeneracy (Δ : SimplexCategory) :
    SimplicialObject.Augmented.ExtraDegeneracy (standardSimplex.obj Δ) where
  s' _ := SimplexCategory.Hom.mk (OrderHom.const _ 0)
  s n f := shift f
  s'_comp_ε := by
    dsimp
    -- ⊢ (fun x => SimplexCategory.Hom.mk (↑(OrderHom.const (Fin (0 + 1))) 0)) ≫ NatT …
    apply Subsingleton.elim
    -- 🎉 no goals
  s₀_comp_δ₁ := by
    ext1 x
    -- ⊢ ((fun n f => shift f) 0 ≫ SimplicialObject.δ (standardSimplex.obj Δ).left 1) …
    apply SimplexCategory.Hom.ext
    -- ⊢ SimplexCategory.Hom.toOrderHom (((fun n f => shift f) 0 ≫ SimplicialObject.δ …
    ext j
    -- ⊢ ↑(↑(SimplexCategory.Hom.toOrderHom (((fun n f => shift f) 0 ≫ SimplicialObje …
    fin_cases j
    -- ⊢ ↑(↑(SimplexCategory.Hom.toOrderHom (((fun n f => shift f) 0 ≫ SimplicialObje …
    rfl
    -- 🎉 no goals
  s_comp_δ₀ n := by
    ext1 φ
    -- ⊢ ((fun n f => shift f) n ≫ SimplicialObject.δ (standardSimplex.obj Δ).left 0) …
    apply SimplexCategory.Hom.ext
    -- ⊢ SimplexCategory.Hom.toOrderHom (((fun n f => shift f) n ≫ SimplicialObject.δ …
    ext i : 2
    -- ⊢ ↑(SimplexCategory.Hom.toOrderHom (((fun n f => shift f) n ≫ SimplicialObject …
    dsimp [SimplicialObject.δ, SimplexCategory.δ, SSet.standardSimplex]
    -- ⊢ shiftFun (↑(SimplexCategory.Hom.toOrderHom φ)) (Fin.succ i) = ↑(SimplexCateg …
    simp only [shiftFun_succ]
    -- 🎉 no goals
  s_comp_δ n i := by
    ext1 φ
    -- ⊢ ((fun n f => shift f) (n + 1) ≫ SimplicialObject.δ (standardSimplex.obj Δ).l …
    apply SimplexCategory.Hom.ext
    -- ⊢ SimplexCategory.Hom.toOrderHom (((fun n f => shift f) (n + 1) ≫ SimplicialOb …
    ext j : 2
    -- ⊢ ↑(SimplexCategory.Hom.toOrderHom (((fun n f => shift f) (n + 1) ≫ Simplicial …
    dsimp [SimplicialObject.δ, SimplexCategory.δ, SSet.standardSimplex]
    -- ⊢ shiftFun (↑(SimplexCategory.Hom.toOrderHom φ)) (Fin.succAbove (Fin.succ i) j …
    by_cases j = 0
    -- ⊢ shiftFun (↑(SimplexCategory.Hom.toOrderHom φ)) (Fin.succAbove (Fin.succ i) j …
    -- ⊢ shiftFun (↑(SimplexCategory.Hom.toOrderHom φ)) (Fin.succAbove (Fin.succ i) j …
    · subst h
      -- ⊢ shiftFun (↑(SimplexCategory.Hom.toOrderHom φ)) (Fin.succAbove (Fin.succ i) 0 …
      simp only [Fin.succ_succAbove_zero, shiftFun_0]
      -- 🎉 no goals
    · obtain ⟨_, rfl⟩ := Fin.eq_succ_of_ne_zero <| h
      -- ⊢ shiftFun (↑(SimplexCategory.Hom.toOrderHom φ)) (Fin.succAbove (Fin.succ i) ( …
      simp only [Fin.succ_succAbove_succ, shiftFun_succ, Function.comp_apply,
        Fin.succAboveEmb_apply]
  s_comp_σ n i := by
    ext1 φ
    -- ⊢ ((fun n f => shift f) n ≫ SimplicialObject.σ (standardSimplex.obj Δ).left (F …
    apply SimplexCategory.Hom.ext
    -- ⊢ SimplexCategory.Hom.toOrderHom (((fun n f => shift f) n ≫ SimplicialObject.σ …
    ext j : 2
    -- ⊢ ↑(SimplexCategory.Hom.toOrderHom (((fun n f => shift f) n ≫ SimplicialObject …
    dsimp [SimplicialObject.σ, SimplexCategory.σ, SSet.standardSimplex]
    -- ⊢ shiftFun (↑(SimplexCategory.Hom.toOrderHom φ)) (Fin.predAbove (Fin.succ i) j …
    by_cases j = 0
    -- ⊢ shiftFun (↑(SimplexCategory.Hom.toOrderHom φ)) (Fin.predAbove (Fin.succ i) j …
    -- ⊢ shiftFun (↑(SimplexCategory.Hom.toOrderHom φ)) (Fin.predAbove (Fin.succ i) j …
    · subst h
      -- ⊢ shiftFun (↑(SimplexCategory.Hom.toOrderHom φ)) (Fin.predAbove (Fin.succ i) 0 …
      simp only [shiftFun_0]
      -- ⊢ shiftFun (↑(SimplexCategory.Hom.toOrderHom φ)) (Fin.predAbove (Fin.succ i) 0 …
      exact shiftFun_0 φ.toOrderHom
      -- 🎉 no goals
    · obtain ⟨_, rfl⟩ := Fin.eq_succ_of_ne_zero h
      -- ⊢ shiftFun (↑(SimplexCategory.Hom.toOrderHom φ)) (Fin.predAbove (Fin.succ i) ( …
      simp only [Fin.succ_predAbove_succ, shiftFun_succ, Function.comp_apply]
      -- 🎉 no goals
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
      -- ⊢ (if x : i = 0 then (WidePullback.base fun x => f.hom) ≫ S.section_ else Wide …
      split_ifs with h
      -- ⊢ ((WidePullback.base fun x => f.hom) ≫ S.section_) ≫ f.hom = WidePullback.bas …
      · subst h
        -- ⊢ ((WidePullback.base fun x => f.hom) ≫ S.section_) ≫ f.hom = WidePullback.bas …
        simp only [assoc, SplitEpi.id, comp_id]
        -- 🎉 no goals
      · simp only [WidePullback.π_arrow]
        -- 🎉 no goals
#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s

-- porting note: @[simp] removed as the linter complains the LHS is not in normal form
theorem ExtraDegeneracy.s_comp_π_0 (n : ℕ) :
    ExtraDegeneracy.s f S n ≫ WidePullback.π _ 0 =
      @WidePullback.base _ _ _ f.right (fun _ : Fin (n + 1) => f.left) (fun _ => f.hom) _ ≫
        S.section_ := by
  dsimp [ExtraDegeneracy.s]
  -- ⊢ WidePullback.lift (WidePullback.base fun x => f.hom) (fun i => if x : i = 0  …
  simp only [WidePullback.lift_π]
  -- ⊢ (if h : True then (WidePullback.base fun x => f.hom) ≫ S.section_ else WideP …
  rfl
  -- 🎉 no goals

-- porting note: @[simp] removed as the linter complains the LHS is not in normal form
theorem ExtraDegeneracy.s_comp_π_succ (n : ℕ) (i : Fin (n + 1)) :
    ExtraDegeneracy.s f S n ≫ WidePullback.π _ i.succ =
      @WidePullback.π _ _ _ f.right (fun _ : Fin (n + 1) => f.left) (fun _ => f.hom) _ i := by
  dsimp [ExtraDegeneracy.s]
  -- ⊢ WidePullback.lift (WidePullback.base fun x => f.hom) (fun i => if x : i = 0  …
  simp only [WidePullback.lift_π]
  -- ⊢ (if x : Fin.succ i = 0 then (WidePullback.base fun x => f.hom) ≫ S.section_  …
  split_ifs with h
  -- ⊢ (WidePullback.base fun x => f.hom) ≫ S.section_ = WidePullback.π (fun x => f …
  · simp only [Fin.ext_iff, Fin.val_succ, Fin.val_zero, add_eq_zero, and_false] at h
    -- 🎉 no goals
  · simp only [Fin.pred_succ]
    -- 🎉 no goals
#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s_comp_π_succ CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s_comp_π_succ

-- porting note: @[simp] removed as the linter complains the LHS is not in normal form
theorem ExtraDegeneracy.s_comp_base (n : ℕ) :
    ExtraDegeneracy.s f S n ≫ WidePullback.base _ = WidePullback.base _ := by
  apply WidePullback.lift_base
  -- 🎉 no goals
#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s_comp_base CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s_comp_base

/-- The augmented Čech nerve associated to a split epimorphism has an extra degeneracy. -/
noncomputable def extraDegeneracy : SimplicialObject.Augmented.ExtraDegeneracy f.augmentedCechNerve
    where
  s' := S.section_ ≫ WidePullback.lift f.hom (fun _ => 𝟙 _) fun i => by rw [id_comp]
                                                                        -- 🎉 no goals
  s n := ExtraDegeneracy.s f S n
  s'_comp_ε := by
    dsimp
    -- ⊢ ((S.section_ ≫ WidePullback.lift f.hom (fun x => 𝟙 f.left) (_ : Fin (0 + 1)  …
    simp only [augmentedCechNerve_hom_app, assoc, WidePullback.lift_base, SplitEpi.id]
    -- 🎉 no goals
  s₀_comp_δ₁ := by
    dsimp [cechNerve, SimplicialObject.δ, SimplexCategory.δ]
    -- ⊢ ExtraDegeneracy.s f S 0 ≫ WidePullback.lift (WidePullback.base fun x => f.ho …
    ext j
    -- ⊢ (ExtraDegeneracy.s f S 0 ≫ WidePullback.lift (WidePullback.base fun x => f.h …
    · fin_cases j
      -- ⊢ (ExtraDegeneracy.s f S 0 ≫ WidePullback.lift (WidePullback.base fun x => f.h …
      simpa only [assoc, WidePullback.lift_π, comp_id] using ExtraDegeneracy.s_comp_π_0 f S 0
      -- 🎉 no goals
    · simpa only [assoc, WidePullback.lift_base, SplitEpi.id, comp_id] using
        ExtraDegeneracy.s_comp_base f S 0
  s_comp_δ₀ n := by
    dsimp [cechNerve, SimplicialObject.δ, SimplexCategory.δ]
    -- ⊢ ExtraDegeneracy.s f S n ≫ WidePullback.lift (WidePullback.base fun x => f.ho …
    ext j
    -- ⊢ (ExtraDegeneracy.s f S n ≫ WidePullback.lift (WidePullback.base fun x => f.h …
    · simpa only [assoc, WidePullback.lift_π, id_comp] using ExtraDegeneracy.s_comp_π_succ f S n j
      -- 🎉 no goals
    · simpa only [assoc, WidePullback.lift_base, id_comp] using ExtraDegeneracy.s_comp_base f S n
      -- 🎉 no goals
  s_comp_δ n i := by
    dsimp [cechNerve, SimplicialObject.δ, SimplexCategory.δ]
    -- ⊢ ExtraDegeneracy.s f S (n + 1) ≫ WidePullback.lift (WidePullback.base fun x = …
    ext j
    -- ⊢ (ExtraDegeneracy.s f S (n + 1) ≫ WidePullback.lift (WidePullback.base fun x  …
    · simp only [assoc, WidePullback.lift_π]
      -- ⊢ ExtraDegeneracy.s f S (n + 1) ≫ WidePullback.π (fun x => f.hom) (Fin.succAbo …
      by_cases j = 0
      -- ⊢ ExtraDegeneracy.s f S (n + 1) ≫ WidePullback.π (fun x => f.hom) (Fin.succAbo …
      -- ⊢ ExtraDegeneracy.s f S (n + 1) ≫ WidePullback.π (fun x => f.hom) (Fin.succAbo …
      · subst h
        -- ⊢ ExtraDegeneracy.s f S (n + 1) ≫ WidePullback.π (fun x => f.hom) (Fin.succAbo …
        erw [Fin.succ_succAbove_zero, ExtraDegeneracy.s_comp_π_0, ExtraDegeneracy.s_comp_π_0]
        -- ⊢ (WidePullback.base fun x => f.hom) ≫ S.section_ = WidePullback.lift (WidePul …
        dsimp
        -- ⊢ (WidePullback.base fun x => f.hom) ≫ S.section_ = WidePullback.lift (WidePul …
        simp only [WidePullback.lift_base_assoc]
        -- 🎉 no goals
      · cases' Fin.eq_succ_of_ne_zero h with k hk
        -- ⊢ ExtraDegeneracy.s f S (n + 1) ≫ WidePullback.π (fun x => f.hom) (Fin.succAbo …
        subst hk
        -- ⊢ ExtraDegeneracy.s f S (n + 1) ≫ WidePullback.π (fun x => f.hom) (Fin.succAbo …
        erw [Fin.succ_succAbove_succ, ExtraDegeneracy.s_comp_π_succ,
          ExtraDegeneracy.s_comp_π_succ]
        simp only [WidePullback.lift_π]
        -- 🎉 no goals
    · simp only [assoc, WidePullback.lift_base]
      -- ⊢ (ExtraDegeneracy.s f S (n + 1) ≫ WidePullback.base fun x => f.hom) = WidePul …
      erw [ExtraDegeneracy.s_comp_base, ExtraDegeneracy.s_comp_base]
      -- ⊢ (WidePullback.base fun x => f.hom) = WidePullback.lift (WidePullback.base fu …
      dsimp
      -- ⊢ (WidePullback.base fun x => f.hom) = WidePullback.lift (WidePullback.base fu …
      simp only [WidePullback.lift_base]
      -- 🎉 no goals
  s_comp_σ n i := by
    dsimp [cechNerve, SimplicialObject.σ, SimplexCategory.σ]
    -- ⊢ ExtraDegeneracy.s f S n ≫ WidePullback.lift (WidePullback.base fun x => f.ho …
    ext j
    -- ⊢ (ExtraDegeneracy.s f S n ≫ WidePullback.lift (WidePullback.base fun x => f.h …
    · simp only [assoc, WidePullback.lift_π]
      -- ⊢ ExtraDegeneracy.s f S n ≫ WidePullback.π (fun x => f.hom) (Fin.predAbove (Fi …
      by_cases j = 0
      -- ⊢ ExtraDegeneracy.s f S n ≫ WidePullback.π (fun x => f.hom) (Fin.predAbove (Fi …
      -- ⊢ ExtraDegeneracy.s f S n ≫ WidePullback.π (fun x => f.hom) (Fin.predAbove (Fi …
      · subst h
        -- ⊢ ExtraDegeneracy.s f S n ≫ WidePullback.π (fun x => f.hom) (Fin.predAbove (Fi …
        erw [ExtraDegeneracy.s_comp_π_0, ExtraDegeneracy.s_comp_π_0]
        -- ⊢ (WidePullback.base fun x => f.hom) ≫ S.section_ = WidePullback.lift (WidePul …
        dsimp
        -- ⊢ (WidePullback.base fun x => f.hom) ≫ S.section_ = WidePullback.lift (WidePul …
        simp only [WidePullback.lift_base_assoc]
        -- 🎉 no goals
      · cases' Fin.eq_succ_of_ne_zero h with k hk
        -- ⊢ ExtraDegeneracy.s f S n ≫ WidePullback.π (fun x => f.hom) (Fin.predAbove (Fi …
        subst hk
        -- ⊢ ExtraDegeneracy.s f S n ≫ WidePullback.π (fun x => f.hom) (Fin.predAbove (Fi …
        erw [Fin.succ_predAbove_succ, ExtraDegeneracy.s_comp_π_succ,
          ExtraDegeneracy.s_comp_π_succ]
        simp only [WidePullback.lift_π]
        -- 🎉 no goals
    · simp only [assoc, WidePullback.lift_base]
      -- ⊢ (ExtraDegeneracy.s f S n ≫ WidePullback.base fun x => f.hom) = WidePullback. …
      erw [ExtraDegeneracy.s_comp_base, ExtraDegeneracy.s_comp_base]
      -- ⊢ (WidePullback.base fun x => f.hom) = WidePullback.lift (WidePullback.base fu …
      dsimp
      -- ⊢ (WidePullback.base fun x => f.hom) = WidePullback.lift (WidePullback.base fu …
      simp only [WidePullback.lift_base]
      -- 🎉 no goals
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
  inv := (ChainComplex.fromSingle₀Equiv _ _).invFun ed.s'
  homotopyInvHomId := Homotopy.ofEq (ChainComplex.to_single₀_ext _ _ (ed.s'_comp_ε))
  homotopyHomInvId :=
    { hom := fun i j => by
        by_cases i + 1 = j
        -- ⊢ HomologicalComplex.X (AlternatingFaceMapComplex.obj (drop.obj X)) i ⟶ Homolo …
        -- ⊢ HomologicalComplex.X (AlternatingFaceMapComplex.obj (drop.obj X)) i ⟶ Homolo …
        · exact (-ed.s i) ≫ eqToHom (by congr)
          -- 🎉 no goals
        · exact 0
          -- 🎉 no goals
      zero := fun i j hij => by
        dsimp
        -- ⊢ (if h : i + 1 = j then (-s ed i) ≫ eqToHom (_ : X.left.obj (op [i + 1]) = X. …
        split_ifs with h
        -- ⊢ (-s ed i) ≫ eqToHom (_ : X.left.obj (op [i + 1]) = X.left.obj (op [j])) = 0
        · exfalso
          -- ⊢ False
          exact hij h
          -- 🎉 no goals
        · simp only [eq_self_iff_true]
          -- 🎉 no goals
      comm := fun i => by
        rcases i with _|i
        -- ⊢ HomologicalComplex.Hom.f (NatTrans.app AlternatingFaceMapComplex.ε X ≫ Equiv …
        · rw [Homotopy.prevD_chainComplex, Homotopy.dNext_zero_chainComplex, zero_add]
          -- ⊢ HomologicalComplex.Hom.f (NatTrans.app AlternatingFaceMapComplex.ε X ≫ Equiv …
          dsimp [ChainComplex.fromSingle₀Equiv, ChainComplex.toSingle₀Equiv]
          -- ⊢ HomologicalComplex.Hom.f (NatTrans.app AlternatingFaceMapComplex.ε X) 0 ≫ ed …
          simp only [comp_id, ite_true, zero_add, ComplexShape.down_Rel, not_true,
            AlternatingFaceMapComplex.obj_d_eq, Preadditive.neg_comp]
          erw [Fin.sum_univ_two]
          -- ⊢ HomologicalComplex.Hom.f (NatTrans.app AlternatingFaceMapComplex.ε X) 0 ≫ ed …
          simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
            Preadditive.comp_add, s_comp_δ₀, drop_obj, Preadditive.comp_neg, neg_add_rev,
            neg_neg, neg_add_cancel_right, s₀_comp_δ₁]
          rfl
          -- 🎉 no goals
        · rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex]
          -- ⊢ HomologicalComplex.Hom.f (NatTrans.app AlternatingFaceMapComplex.ε X ≫ Equiv …
          dsimp [ChainComplex.toSingle₀Equiv, ChainComplex.fromSingle₀Equiv]
          -- ⊢ HomologicalComplex.Hom.f (NatTrans.app AlternatingFaceMapComplex.ε X) (Nat.s …
          simp only [comp_zero, ComplexShape.down_Rel, not_true, Preadditive.neg_comp,
            AlternatingFaceMapComplex.obj_d_eq, comp_id, ite_true, Preadditive.comp_neg,
            @Fin.sum_univ_succ _ _ (i + 2), Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
            Preadditive.comp_add, drop_obj, s_comp_δ₀, Preadditive.sum_comp,
            Preadditive.zsmul_comp, Preadditive.comp_sum, Preadditive.comp_zsmul,
            zsmul_neg, ed.s_comp_δ, pow_add, pow_one, mul_neg, mul_one, neg_zsmul, neg_neg,
            neg_add_cancel_comm_assoc, add_left_neg] }
#align simplicial_object.augmented.extra_degeneracy.homotopy_equiv SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv

end ExtraDegeneracy

end Augmented

end SimplicialObject
