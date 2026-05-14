/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.SimplicialObject.DeltaZeroIter
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

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
- `ExtraDegeneracy.homotopy`: if we have an extra degeneracy `ed` on
  `X : SimplicialObject.Augmented C` (for any category `C`), then
  the morphism `X.hom ≫ ed.section_` is homotopic to `𝟙 X.left`.

## References
* [Paul G. Goerss, John F. Jardine, *Simplicial Homotopy Theory*][goerss-jardine-2009]
* [M. Barr, J. Kennison, J. and R. Robert,
  *Contractible simplicial objects*][barr-kennison-robert-2019]

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
  s' : X.right ⟶ X.left _⦋0⦌
  /-- the extra degeneracy -/
  s : ∀ n : ℕ, X.left _⦋n⦌ ⟶ X.left _⦋n + 1⦌
  s'_comp_ε : dsimp% s' ≫ X.hom.app (op ⦋0⦌) = 𝟙 X.right := by cat_disch
  s₀_comp_δ₁ : dsimp% s 0 ≫ X.left.δ 1 = X.hom.app (op ⦋0⦌) ≫ s' := by cat_disch
  s_comp_δ₀ : ∀ n : ℕ, s n ≫ X.left.δ 0 = 𝟙 _ := by cat_disch
  s_comp_δ :
    ∀ (n : ℕ) (i : Fin (n + 2)), s (n + 1) ≫ X.left.δ i.succ = X.left.δ i ≫ s n := by cat_disch
  s_comp_σ :
    ∀ (n : ℕ) (i : Fin (n + 1)), s n ≫ X.left.σ i.succ = X.left.σ i ≫ s (n + 1) := by cat_disch

namespace ExtraDegeneracy

attribute [reassoc] s₀_comp_δ₁ s_comp_δ s_comp_σ
attribute [reassoc (attr := simp)] s'_comp_ε s_comp_δ₀

attribute [local simp←] Functor.map_comp in
attribute [local simp] s₀_comp_δ₁ s_comp_δ s_comp_σ in
/-- If `ed` is an extra degeneracy for `X : SimplicialObject.Augmented C` and
`F : C ⥤ D` is a functor, then `ed.map F` is an extra degeneracy for the
augmented simplicial object in `D` obtained by applying `F` to `X`. -/
def map {D : Type*} [Category* D] {X : SimplicialObject.Augmented C} (ed : ExtraDegeneracy X)
    (F : C ⥤ D) : ExtraDegeneracy (((whiskering _ _).obj F).obj X) where
  s' := F.map ed.s'
  s n := F.map (ed.s n)

/-- If `X` and `Y` are isomorphic augmented simplicial objects, then an extra
degeneracy for `X` gives also an extra degeneracy for `Y` -/
def ofIso {X Y : SimplicialObject.Augmented C} (e : X ≅ Y) (ed : ExtraDegeneracy X) :
    ExtraDegeneracy Y where
  s' := (point.mapIso e).inv ≫ ed.s' ≫ (drop.mapIso e).hom.app (op ⦋0⦌)
  s n := (drop.mapIso e).inv.app (op ⦋n⦌) ≫ ed.s n ≫ (drop.mapIso e).hom.app (op ⦋n + 1⦌)
  s'_comp_ε := by
    simpa [w₀, ed.s'_comp_ε_assoc] using (point.mapIso e).inv_hom_id
  s₀_comp_δ₁ := by
    simp [← SimplicialObject.δ_naturality, s₀_comp_δ₁_assoc, w₀_assoc]
  s_comp_δ₀ n := by
    simpa [← SimplicialObject.δ_naturality] using
      congr_app (drop.mapIso e).inv_hom_id (op ⦋n⦌)
  s_comp_δ n i := by
    simp [← SimplicialObject.δ_naturality, s_comp_δ_assoc,
      ← SimplicialObject.δ_naturality_assoc]
  s_comp_σ n i := by
    simp [← SimplicialObject.σ_naturality, s_comp_σ_assoc,
      ← SimplicialObject.σ_naturality_assoc]

variable {X : SimplicialObject.Augmented C} (ed : ExtraDegeneracy X)

attribute [local simp←] Functor.map_comp in
/-- The section of the augmentation that is induced by the extradegeneracy. -/
def section_ : (SimplicialObject.const C).obj X.right ⟶ X.left where
  app n := ed.s' ≫ X.left.map (SimplexCategory.isTerminalZero.from _).op

@[simp]
lemma section_app_op_mk_zero :
    ed.section_.app (op ⦋0⦌) = ed.s' := by
  simp [section_]

@[reassoc (attr := simp)]
lemma section_app_comp_hom_app (n : SimplexCategoryᵒᵖ) :
    dsimp% ed.section_.app n ≫ X.hom.app n = 𝟙 _ := by
  dsimp [section_]
  rw [assoc, dsimp% X.hom.naturality, comp_id]
  exact ed.s'_comp_ε

@[simp]
lemma section_comp_hom : ed.section_ ≫ X.hom = 𝟙 _ := by cat_disch

/-- If an augmented simplicial object has an extradegeneracy, then
then augmentation is a split epimorphism. -/
def splitEpi : SplitEpi X.hom where
  section_ := ed.section_

@[reassoc (attr := simp)]
lemma s'_σ₀Iter (n : ℕ) :
    ed.s' ≫ X.left.σ₀Iter n = ed.section_.app (op ⦋n⦌) := by
  dsimp [section_, SimplicialObject.σ₀Iter]
  congr 3
  subsingleton

namespace homotopy

/-- Auxiliary definition for `ExtraDegeneracy.homotopy`. -/
def h {n : ℕ} (i : Fin (n + 1)) : X.left _⦋n⦌ ⟶ X.left _⦋n + 1⦌ :=
  X.left.δ₀Iter i.val (by grind) ≫ ed.s i.rev.val ≫ X.left.σ₀Iter i.val (by grind)

@[reassoc]
lemma h_eq {n : ℕ} (i : Fin (n + 1)) (j : ℕ) (hj : j = i.rev.val := by grind) :
    h ed i = X.left.δ₀Iter i.val (by grind) ≫ ed.s j ≫ X.left.σ₀Iter i.val (by grind) := by
  subst hj
  rfl

end homotopy

open homotopy in
/-- If `ed` is an extradegeneracy for an augmented simplicial object `X`, then this
is a homotopy from `X.hom ≫ ed.section_` to `𝟙 X.left`. -/
@[simps]
def homotopy : SimplicialObject.Homotopy (X.hom ≫ ed.section_) (𝟙 X.left) where
  h := h ed
  h_zero_comp_δ_zero n := by simp [h_eq_assoc ed (0 : Fin (n + 1)) n (by simp)]
  h_last_comp_δ_last n := by
    dsimp
    rw [h_eq_assoc _ _ 0, X.left.σ₀Iter_δ' _ _ 1 (by grind),
      ed.s₀_comp_δ₁_assoc, X.δ₀Iter_hom_app_assoc _ (by grind)]
    simp
  h_succ_comp_δ_castSucc_of_lt {n} i j hij := by
    generalize hk : j.succ.rev = k
    dsimp
    rw [h_eq_assoc _ _ k, h_eq _ _ k]
    dsimp
    rw [X.left.σ₀Iter_δ _ _ (by grind), X.left.δ_δ₀Iter_assoc _ _ (by grind)]
  h_castSucc_comp_δ_succ_of_lt {n} i j hij := by
    generalize hk : j.rev = k
    obtain ⟨l, hl⟩ : ∃ l, i.val = j + 1 + l := by
      rw [Fin.castSucc_lt_iff_succ_le, Fin.le_def] at hij
      obtain ⟨l, hl⟩ := Nat.le.dest hij
      exact ⟨l, by grind⟩
    have := ed.s_comp_δ k ⟨l + 1, by grind⟩
    dsimp at this ⊢
    rw [h_eq_assoc _ _ (k + 1), h_eq _ _ k,
      X.left.σ₀Iter_δ' _ _ ⟨l + 2, by grind⟩ (by grind),
      reassoc_of% this, ← X.left.δ_δ₀Iter'_assoc _ _ i (by grind)]
    dsimp
  h_succ_comp_δ_castSucc_succ {n} i := by
    generalize hk : i.succ.rev = k
    dsimp
    rw [h_eq_assoc _ _ k, h_eq_assoc _ _ (k + 1)]
    dsimp
    rw [X.left.δ₀Iter_succ'_assoc _ (by grind),
      X.left.σ₀Iter_δ' i.castSucc.succ i.val (m := k.val + 1)
        (i' := 1) (by grind) (by grind) (by simp; grind),
      dsimp% ed.s_comp_δ_assoc k.val 0, X.left.σ₀Iter_δ _ _ (by grind)]
  h_comp_σ_castSucc_of_le {n} i j hij := by
    generalize hk : j.rev = k
    dsimp
    rw [h_eq_assoc _ _ k, h_eq _ _ k]
    dsimp
    rw [X.left.σ_δ₀Iter_assoc _ _ (by grind), X.left.σ₀Iter_σ _ _ (by grind)]
  h_comp_σ_succ_of_lt {n} i j hij := by
    generalize hk : j.rev = k
    obtain ⟨l, hl⟩ := Nat.le.dest (Fin.le_def.1 hij)
    dsimp
    rw [h_eq_assoc _ _ k, h_eq _ _ (k + 1),
      X.left.σ_δ₀Iter'_assoc _ _ ⟨l, by grind⟩
        (by grind),
      ← ed.s_comp_σ_assoc,
      X.left.σ₀Iter_σ' j i.succ ⟨l + 1, by grind⟩ (by grind)]
    dsimp

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
            rintro rfl
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
  s' := ↾fun _ ↦ objMk (OrderHom.const _ 0)
  s _ := ↾fun f ↦ objEquiv.symm (shift (objEquiv f))
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
@[reassoc (attr := simp)]
theorem ExtraDegeneracy.s_comp_π_0 (n : ℕ) :
    dsimp% ExtraDegeneracy.s f S n ≫ WidePullback.π _ 0 =
      WidePullback.base (B := f.right) (objs := fun _ ↦ f.left)
        (arrows := fun _ ↦ f.hom) ≫ S.section_ := by
  simp [ExtraDegeneracy.s]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ExtraDegeneracy.s_comp_π_succ (n : ℕ) (i : Fin (n + 1)) :
    dsimp% ExtraDegeneracy.s f S n ≫ WidePullback.π _ i.succ =
      WidePullback.π (B := f.right) (objs := fun _ ↦ f.left)
        (arrows := fun _ ↦ f.hom) i := by
  simp [ExtraDegeneracy.s]

@[reassoc (attr := simp)]
theorem ExtraDegeneracy.s_comp_base (n : ℕ) :
    dsimp% ExtraDegeneracy.s f S n ≫ WidePullback.base _ = WidePullback.base _ :=
  WidePullback.lift_base ..

set_option backward.isDefEq.respectTransparency false in
/-- The augmented Čech nerve associated to a split epimorphism has an extra degeneracy. -/
noncomputable def extraDegeneracy :
    SimplicialObject.Augmented.ExtraDegeneracy f.augmentedCechNerve where
  s' := S.section_ ≫ WidePullback.lift f.hom (fun _ ↦ 𝟙 _) (by simp)
  s n := ExtraDegeneracy.s f S n
  s₀_comp_δ₁ := by
    dsimp [SimplicialObject.δ, SimplexCategory.δ]
    ext j
    · fin_cases j
      simp
    · simp
  s_comp_δ₀ n := by
    dsimp [SimplicialObject.δ, SimplexCategory.δ]
    cat_disch
  s_comp_δ n i := by
    dsimp [SimplicialObject.δ, SimplexCategory.δ]
    ext j
    · induction j using Fin.cases <;> simp
    · simp
  s_comp_σ n i := by
    dsimp [SimplicialObject.σ, SimplexCategory.σ]
    ext j
    · induction j using Fin.cases <;> simp
    · simp

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
    simp [dsimp% ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
      (C := AlternatingFaceMapComplex.obj X.left)])
  homotopyHomInvId :=
    { hom i := Pi.single (i + 1) (-ed.s i)
      zero i j hij := Pi.single_eq_of_ne (Ne.symm hij) _
      comm i := by
        cases i with
        | zero =>
          rw [Homotopy.prevD_chainComplex, Homotopy.dNext_zero_chainComplex]
          simp [dsimp% ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
            (C := AlternatingFaceMapComplex.obj X.left), s_comp_δ₀, s₀_comp_δ₁]
        | succ i =>
          rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex]
          simp [Fin.sum_univ_succ (n := i + 2), s_comp_δ₀, Preadditive.sum_comp,
            Preadditive.comp_sum,
            s_comp_δ, pow_succ] }

end ExtraDegeneracy

end Augmented

end SimplicialObject

end CategoryTheory
