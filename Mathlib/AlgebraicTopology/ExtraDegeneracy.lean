/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Tactic.FinCases

/-!

# Augmented simplicial objects with an extra degeneracy

In simplicial homotopy theory, in order to prove that the connected components
of a simplicial set `X` are contractible, it suffices to construct an extra
degeneracy as it is defined in *Simplicial Homotopy Theory* by Goerss-Jardine p. 190.
It consists of a series of maps `π₀ X → X _⦋0⦌` and `X _⦋n⦌ → X _⦋n+1⦌` which
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

@[expose] public section


open CategoryTheory Category SimplicialObject.Augmented Opposite Simplicial

namespace CategoryTheory

namespace SimplicialObject

namespace Augmented

variable {C : Type*} [Category* C]

/-- The datum of an extra degeneracy is a technical condition on
augmented simplicial objects. The morphisms `s'` and `s n` of the
structure formally behave like extra degeneracies `σ (-1)`. -/
@[ext]
structure ExtraDegeneracy (X : SimplicialObject.Augmented C) where
  /-- a section of the augmentation in dimension `0` -/
  s' : point.obj X ⟶ drop.obj X _⦋0⦌
  /-- the extra degeneracy -/
  s : ∀ n : ℕ, drop.obj X _⦋n⦌ ⟶ drop.obj X _⦋n + 1⦌
  s'_comp_ε : s' ≫ X.hom.app (op ⦋0⦌) = 𝟙 _ := by cat_disch
  s₀_comp_δ₁ : s 0 ≫ X.left.δ 1 = X.hom.app (op ⦋0⦌) ≫ s' := by cat_disch
  s_comp_δ₀ : ∀ n : ℕ, s n ≫ X.left.δ 0 = 𝟙 _ := by cat_disch
  s_comp_δ :
    ∀ (n : ℕ) (i : Fin (n + 2)), s (n + 1) ≫ X.left.δ i.succ = X.left.δ i ≫ s n := by cat_disch
  s_comp_σ :
    ∀ (n : ℕ) (i : Fin (n + 1)), s n ≫ X.left.σ i.succ = X.left.σ i ≫ s (n + 1) := by cat_disch

namespace ExtraDegeneracy

attribute [reassoc] s₀_comp_δ₁ s_comp_δ s_comp_σ
set_option backward.isDefEq.respectTransparency false in -- This is needed below.
attribute [reassoc (attr := simp)] s'_comp_ε s_comp_δ₀

set_option backward.isDefEq.respectTransparency false in
/-- If `ed` is an extra degeneracy for `X : SimplicialObject.Augmented C` and
`F : C ⥤ D` is a functor, then `ed.map F` is an extra degeneracy for the
augmented simplicial object in `D` obtained by applying `F` to `X`. -/
def map {D : Type*} [Category* D] {X : SimplicialObject.Augmented C} (ed : ExtraDegeneracy X)
    (F : C ⥤ D) : ExtraDegeneracy (((whiskering _ _).obj F).obj X) where
  s' := F.map ed.s'
  s n := F.map (ed.s n)
  s'_comp_ε := by
    dsimp
    rw [comp_id, ← F.map_comp, ed.s'_comp_ε]
    dsimp only [point_obj]
    rw [F.map_id]
  s₀_comp_δ₁ := by
    dsimp
    rw [comp_id, ← F.map_comp]
    dsimp [SimplicialObject.whiskering, SimplicialObject.δ]
    rw [← F.map_comp]
    erw [ed.s₀_comp_δ₁]
  s_comp_δ₀ n := by
    dsimp [SimplicialObject.δ]
    rw [← F.map_comp]
    erw [ed.s_comp_δ₀]
    dsimp
    rw [F.map_id]
  s_comp_δ n i := by
    dsimp [SimplicialObject.δ]
    rw [← F.map_comp, ← F.map_comp]
    erw [ed.s_comp_δ]
    rfl
  s_comp_σ n i := by
    dsimp [SimplicialObject.whiskering, SimplicialObject.σ]
    rw [← F.map_comp, ← F.map_comp]
    erw [ed.s_comp_σ]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- If `X` and `Y` are isomorphic augmented simplicial objects, then an extra
degeneracy for `X` gives also an extra degeneracy for `Y` -/
def ofIso {X Y : SimplicialObject.Augmented C} (e : X ≅ Y) (ed : ExtraDegeneracy X) :
    ExtraDegeneracy Y where
  s' := (point.mapIso e).inv ≫ ed.s' ≫ (drop.mapIso e).hom.app (op ⦋0⦌)
  s n := (drop.mapIso e).inv.app (op ⦋n⦌) ≫ ed.s n ≫ (drop.mapIso e).hom.app (op ⦋n + 1⦌)
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
      congr_app (drop.mapIso e).inv_hom_id (op ⦋n⦌)
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

end ExtraDegeneracy

end Augmented

end SimplicialObject

end CategoryTheory

namespace SSet

namespace Augmented

namespace StandardSimplex

/-- When `[Zero X]`, the shift of a map `f : Fin n → X`
is a map `Fin (n + 1) → X` which sends `0` to `0` and `i.succ` to `f i`. -/
def shiftFun {n : ℕ} {X : Type*} [Zero X] (f : Fin n → X) (i : Fin (n + 1)) : X :=
  Matrix.vecCons 0 f i

@[simp]
theorem shiftFun_zero {n : ℕ} {X : Type*} [Zero X] (f : Fin n → X) : shiftFun f 0 = 0 :=
  rfl

@[simp]
theorem shiftFun_succ {n : ℕ} {X : Type*} [Zero X] (f : Fin n → X) (i : Fin n) :
    shiftFun f i.succ = f i :=
  rfl

/-- The shift of a morphism `f : ⦋n⦌ → Δ` in `SimplexCategory` corresponds to
the monotone map which sends `0` to `0` and `i.succ` to `f.toOrderHom i`. -/
@[simp]
def shift {n : ℕ} {Δ : SimplexCategory} (f : ⦋n⦌ ⟶ Δ) : ⦋n + 1⦌ ⟶ Δ :=
  SimplexCategory.Hom.mk
    { toFun := shiftFun f.toOrderHom
      monotone' := fun i₁ i₂ hi => by
        by_cases h₁ : i₁ = 0
        · subst h₁
          simp only [shiftFun_zero, Fin.zero_le]
        · have h₂ : i₂ ≠ 0 := by
            intro h₂
            subst h₂
            exact h₁ (le_antisymm hi (Fin.zero_le _))
          obtain ⟨j₁, hj₁⟩ := Fin.eq_succ_of_ne_zero h₁
          obtain ⟨j₂, hj₂⟩ := Fin.eq_succ_of_ne_zero h₂
          substs hj₁ hj₂
          simpa only [shiftFun_succ] using f.toOrderHom.monotone (Fin.succ_le_succ_iff.mp hi) }

set_option backward.isDefEq.respectTransparency false in
open SSet.stdSimplex in
/-- The obvious extra degeneracy on the standard simplex. -/
protected noncomputable def extraDegeneracy (Δ : SimplexCategory) :
    SimplicialObject.Augmented.ExtraDegeneracy (stdSimplex.obj Δ) where
  s' := TypeCat.ofHom ⟨fun _ ↦ objMk (OrderHom.const _ 0)⟩
  s _ := TypeCat.ofHom ⟨fun f ↦ objEquiv.symm (shift (objEquiv f))⟩
  s'_comp_ε := by
    dsimp
    subsingleton
  s₀_comp_δ₁ := by
    dsimp
    ext x
    apply objEquiv.injective
    ext j
    fin_cases j
    rfl
  s_comp_δ₀ n := by
    ext φ
    apply objEquiv.injective
    apply SimplexCategory.Hom.ext
    ext i : 2
    dsimp [SimplicialObject.δ, SimplexCategory.δ, SSet.stdSimplex,
      objEquiv, Equiv.ulift, uliftFunctor]
    rfl
  s_comp_δ n i := by
    ext φ
    apply objEquiv.injective
    apply SimplexCategory.Hom.ext
    ext j : 2
    dsimp [SimplicialObject.δ, SimplexCategory.δ, SSet.stdSimplex,
      objEquiv, Equiv.ulift, uliftFunctor]
    cases j using Fin.cases <;> simp
  s_comp_σ n i := by
    ext φ
    apply objEquiv.injective
    apply SimplexCategory.Hom.ext
    ext j : 2
    dsimp [SimplicialObject.σ, SimplexCategory.σ, SSet.stdSimplex, objEquiv, Equiv.ulift,
      uliftFunctor, Function.comp_def]
    cases j using Fin.cases <;> simp

instance nonempty_extraDegeneracy_stdSimplex (Δ : SimplexCategory) :
    Nonempty (SimplicialObject.Augmented.ExtraDegeneracy (stdSimplex.obj Δ)) :=
  ⟨StandardSimplex.extraDegeneracy Δ⟩

end StandardSimplex

end Augmented

end SSet

namespace CategoryTheory

open Limits

namespace Arrow

namespace AugmentedCechNerve

variable {C : Type*} [Category* C] (f : Arrow C)
  [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]
  (S : SplitEpi f.hom)

set_option backward.isDefEq.respectTransparency false in
/-- The extra degeneracy map on the Čech nerve of a split epi. It is
given on the `0`-projection by the given section of the split epi,
and by shifting the indices on the other projections. -/
noncomputable def ExtraDegeneracy.s (n : ℕ) :
    f.cechNerve.obj (op ⦋n⦌) ⟶ f.cechNerve.obj (op ⦋n + 1⦌) :=
  WidePullback.lift (WidePullback.base _)
    (Fin.cases (WidePullback.base _ ≫ S.section_) (WidePullback.π _))
    fun i => by
      cases i using Fin.cases <;> simp

set_option backward.isDefEq.respectTransparency false in
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11119): @[simp] removed as the linter complains the LHS is not in normal form
-- The problem is that the type of `ExtraDegeneracy.s` is not in normal form, this causes the `erw`
-- in the proofs below.
theorem ExtraDegeneracy.s_comp_π_0 (n : ℕ) :
    ExtraDegeneracy.s f S n ≫ WidePullback.π _ 0 =
      @WidePullback.base _ _ _ f.right (fun _ : Fin (n + 1) => f.left) (fun _ => f.hom) _ ≫
        S.section_ := by
  dsimp [ExtraDegeneracy.s]
  simp

set_option backward.isDefEq.respectTransparency false in
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11119): @[simp] removed as the linter complains the LHS is not in normal form
theorem ExtraDegeneracy.s_comp_π_succ (n : ℕ) (i : Fin (n + 1)) :
    ExtraDegeneracy.s f S n ≫ WidePullback.π _ i.succ =
      @WidePullback.π _ _ _ f.right (fun _ : Fin (n + 1) => f.left) (fun _ => f.hom) _ i := by
  simp [ExtraDegeneracy.s]

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11119): @[simp] removed as the linter complains the LHS is not in normal form
theorem ExtraDegeneracy.s_comp_base (n : ℕ) :
    ExtraDegeneracy.s f S n ≫ WidePullback.base _ = WidePullback.base _ := by
  apply WidePullback.lift_base

set_option backward.isDefEq.respectTransparency false in
/-- The augmented Čech nerve associated to a split epimorphism has an extra degeneracy. -/
noncomputable def extraDegeneracy :
    SimplicialObject.Augmented.ExtraDegeneracy f.augmentedCechNerve where
  s' := S.section_ ≫ WidePullback.lift f.hom (fun _ => 𝟙 _) fun i => by rw [id_comp]
  s n := ExtraDegeneracy.s f S n
  s'_comp_ε := by
    dsimp
    simp only [assoc, WidePullback.lift_base, SplitEpi.id]
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
    dsimp [SimplicialObject.δ, SimplexCategory.δ]
    ext j
    · simp only [assoc, WidePullback.lift_π]
      cases j using Fin.cases with
      | zero =>
        rw [Fin.succ_succAbove_zero]
        erw [ExtraDegeneracy.s_comp_π_0, ExtraDegeneracy.s_comp_π_0]
        dsimp
        simp only [WidePullback.lift_base_assoc]
      | succ k =>
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
      cases j using Fin.cases with
      | zero =>
        erw [ExtraDegeneracy.s_comp_π_0, ExtraDegeneracy.s_comp_π_0]
        dsimp
        simp only [WidePullback.lift_base_assoc]
      | succ k =>
        erw [Fin.succ_predAbove_succ, ExtraDegeneracy.s_comp_π_succ,
          ExtraDegeneracy.s_comp_π_succ]
        simp only [WidePullback.lift_π]
    · simp only [assoc, WidePullback.lift_base]
      erw [ExtraDegeneracy.s_comp_base, ExtraDegeneracy.s_comp_base]
      dsimp
      simp only [WidePullback.lift_base]

end AugmentedCechNerve

end Arrow

namespace SimplicialObject

namespace Augmented

namespace ExtraDegeneracy

open AlgebraicTopology CategoryTheory Limits
variable {C : Type*} [Category* C]

/-- The constant augmented simplicial object has an extra degeneracy. -/
@[simps]
def const (X : C) : ExtraDegeneracy (Augmented.const.obj X) where
  s' := 𝟙 _
  s _ := 𝟙 _

set_option backward.isDefEq.respectTransparency false in
/-- If `C` is a preadditive category and `X` is an augmented simplicial object
in `C` that has an extra degeneracy, then the augmentation on the alternating
face map complex of `X` is a homotopy equivalence. -/
noncomputable def homotopyEquiv [Preadditive C] [HasZeroObject C]
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
    { hom i := Pi.single (i + 1) (-ed.s i)
      zero i j hij := Pi.single_eq_of_ne (Ne.symm hij) _
      comm i := by
        cases i with
        | zero =>
          rw [Homotopy.prevD_chainComplex, Homotopy.dNext_zero_chainComplex, zero_add]
          dsimp
          erw [ChainComplex.fromSingle₀Equiv_symm_apply_f_zero]
          simp only [AlternatingFaceMapComplex.obj_d_eq]
          rw [Fin.sum_univ_two]
          simp [s_comp_δ₀, s₀_comp_δ₁]
        | succ i =>
          rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex]
          simp [Fin.sum_univ_succ (n := i + 2), s_comp_δ₀, Preadditive.sum_comp,
            Preadditive.comp_sum,
            s_comp_δ, pow_succ] }

end ExtraDegeneracy

end Augmented

end SimplicialObject

end CategoryTheory
