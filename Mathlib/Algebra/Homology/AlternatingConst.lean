/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.CategoryTheory.Elementwise
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
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
# The alternating constant complex

Given an object `X : C` and endomorphisms `φ, ψ : X ⟶ X` such that `φ ∘ ψ = ψ ∘ φ = 0`, this file
defines the periodic chain and cochain complexes
`... ⟶ X --φ--> X --ψ--> X --φ--> X --ψ--> 0` and `0 ⟶ X --ψ--> X --φ--> X --ψ--> X --φ--> ...`
(or more generally for any complex shape `c` on `ℕ` where `c.Rel i j` implies `i` and `j` have
different parity). We calculate the homology of these periodic complexes.

In particular, we show `... ⟶ X --𝟙--> X --0--> X --𝟙--> X --0--> X ⟶ 0` is homotopy equivalent
to the single complex where `X` is in degree `0`.

-/

@[expose] public section
universe v u

open CategoryTheory Limits

namespace ComplexShape

lemma up_nat_odd_add {i j : ℕ} (h : (ComplexShape.up ℕ).Rel i j) : Odd (i + j) := by
  subst h
  norm_num

lemma down_nat_odd_add {i j : ℕ} (h : (ComplexShape.down ℕ).Rel i j) : Odd (i + j) := by
  subst h
  norm_num

end ComplexShape

namespace HomologicalComplex

open ShortComplex

variable {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
  (A : C) {φ : A ⟶ A} {ψ : A ⟶ A} (hOdd : φ ≫ ψ = 0) (hEven : ψ ≫ φ = 0)

/-- Let `c : ComplexShape ℕ` be such that `i j : ℕ` have opposite parity if they are related by
`c`. Let `φ, ψ : A ⟶ A` be such that `φ ∘ ψ = ψ ∘ φ = 0`. This is a complex of shape `c` whose
objects are all `A`. For all `i, j` related by `c`, `dᵢⱼ = φ` when `i` is even, and `dᵢⱼ = ψ` when
`i` is odd. -/
@[simps!]
noncomputable def alternatingConst {c : ComplexShape ℕ} [DecidableRel c.Rel]
    (hc : ∀ i j, c.Rel i j → Odd (i + j)) :
    HomologicalComplex C c where
  X n := A
  d i j :=
    if hij : c.Rel i j then
      if hi : Even i then φ
      else ψ
    else 0
  shape i j := by aesop
  d_comp_d' i j k hij hjk := by
    have := hc i j hij
    split_ifs with hi hj hj
    · exact False.elim <| Nat.not_odd_iff_even.2 hi <| by simp_all [Nat.odd_add]
    · assumption
    · assumption
    · exact False.elim <| hj <| by simp_all [Nat.odd_add]

variable {c : ComplexShape ℕ} [DecidableRel c.Rel] (hc : ∀ i j, c.Rel i j → Odd (i + j))

open HomologicalComplex hiding mk

set_option backward.isDefEq.respectTransparency false in
/-- The `i, j, k`th short complex associated to the alternating constant complex on `φ, ψ : A ⟶ A`
is `A --ψ--> A --φ--> A` when `i ~ j, j ~ k` and `j` is even. -/
noncomputable def alternatingConstScIsoEven
    {i j k : ℕ} (hij : c.Rel i j) (hjk : c.Rel j k) (h : Even j) :
    (alternatingConst A hOdd hEven hc).sc' i j k ≅ ShortComplex.mk ψ φ hEven :=
  isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp_all only [alternatingConst, dite_eq_ite, Iso.refl_hom, Category.id_comp,
        shortComplexFunctor'_obj_f, ↓reduceIte, Category.comp_id, right_eq_ite_iff]
      intro hi
      have := hc i j hij
      exact False.elim <| Nat.not_odd_iff_even.2 hi <| by simp_all [Nat.odd_add])
    (by simp_all [alternatingConst])

set_option backward.isDefEq.respectTransparency false in
/-- The `i, j, k`th short complex associated to the alternating constant complex on `φ, ψ : A ⟶ A`
is `A --φ--> A --ψ--> A` when `i ~ j, j ~ k` and `j` is even. -/
noncomputable def alternatingConstScIsoOdd
    {i j k : ℕ} (hij : c.Rel i j) (hjk : c.Rel j k) (h : Odd j) :
    (alternatingConst A hOdd hEven hc).sc' i j k ≅ ShortComplex.mk φ ψ hOdd :=
  isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp_all only [alternatingConst, dite_eq_ite, Iso.refl_hom, Category.id_comp,
        shortComplexFunctor'_obj_f, ↓reduceIte, Category.comp_id, left_eq_ite_iff]
      intro hi
      have := hc i j hij
      exact False.elim <| Nat.not_even_iff_odd.2 h <| by simp_all [Nat.odd_add])
    (by simp_all [alternatingConst])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma alternatingConst_iCycles_even_comp [CategoryWithHomology C]
    {j : ℕ} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Even j) :
    (alternatingConst A hOdd hEven hc).iCycles j ≫ φ = 0 := by
  rw [← cancel_epi (ShortComplex.cyclesMapIso
    (alternatingConstScIsoEven A hOdd hEven hc hpj hnj h)).inv]
  simpa [HomologicalComplex.iCycles, -Preadditive.IsIso.comp_left_eq_zero, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor, alternatingConstScIsoEven,
    Category.id_comp (X := (alternatingConst A hOdd hEven hc).X _)]
    using (ShortComplex.mk ψ φ hEven).iCycles_g

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma alternatingConst_iCycles_odd_comp [CategoryWithHomology C]
    {j : ℕ} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Odd j) :
    (alternatingConst A hOdd hEven hc).iCycles j ≫ ψ = 0 := by
  rw [← cancel_epi (ShortComplex.cyclesMapIso
    (alternatingConstScIsoOdd A hOdd hEven hc hpj hnj h)).inv]
  simpa [HomologicalComplex.iCycles, -Preadditive.IsIso.comp_left_eq_zero, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor, alternatingConstScIsoOdd,
    Category.id_comp (X := (alternatingConst A hOdd hEven hc).X _)]
    using (ShortComplex.mk φ ψ hOdd).iCycles_g

/-- The `j`th homology of the alternating constant complex on `φ, ψ : A ⟶ A` is the homology of
`A --ψ--> A --φ--> A` when `prev(j) ~ j, j ~ next(j)` and `j` is even. -/
noncomputable def alternatingConstHomologyIsoEven [CategoryWithHomology C]
    {j : ℕ} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Even j) :
    (alternatingConst A hOdd hEven hc).homology j ≅ (ShortComplex.mk ψ φ hEven).homology :=
  ShortComplex.homologyMapIso (alternatingConstScIsoEven A hOdd hEven hc hpj hnj h)

/-- The `j`th homology of the alternating constant complex on `φ, ψ : A ⟶ A` is the homology of
`A --φ--> A --ψ--> A` when `prev(j) ~ j, j ~ next(j)` and `j` is odd. -/
noncomputable def alternatingConstHomologyIsoOdd [CategoryWithHomology C]
    {j : ℕ} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Odd j) :
    (alternatingConst A hOdd hEven hc).homology j ≅ (ShortComplex.mk φ ψ hOdd).homology :=
  ShortComplex.homologyMapIso (alternatingConstScIsoOdd A hOdd hEven hc hpj hnj h)

end HomologicalComplex

open CategoryTheory Limits AlgebraicTopology

variable {C : Type*} [Category* C]

namespace ChainComplex

/-- The chain complex `X ←0- X ←𝟙- X ←0- X ←𝟙- X ⋯`.
It is exact away from `0` and has homology `X` at `0`. -/
@[simps]
noncomputable def alternatingConst [HasZeroMorphisms C] : C ⥤ ChainComplex C ℕ where
  obj X := HomologicalComplex.alternatingConst X (Category.id_comp 0) (Category.comp_id 0)
    (fun _ _ => ComplexShape.down_nat_odd_add)
  map {X Y} f := {
    f _ := f
    comm' i j hij := by by_cases Even i <;> simp_all [-Nat.not_even_iff_odd] }

variable [HasZeroMorphisms C] [HasZeroObject C]

open ZeroObject

set_option backward.isDefEq.respectTransparency false in
/-- The `n`-th homology of the alternating constant complex is zero for non-zero even `n`. -/
noncomputable
def alternatingConstHomologyDataEvenNEZero (X : C) (n : ℕ) (hn : Even n) (h₀ : n ≠ 0) :
    ((alternatingConst.obj X).sc n).HomologyData :=
  .ofIsLimitKernelFork _ (by simp [Nat.even_add_one, hn]) _
    (Limits.zeroKernelOfCancelZero _ (by cases n <;> simp_all))

set_option backward.isDefEq.respectTransparency false in
/-- The `n`-th homology of the alternating constant complex is zero for odd `n`. -/
noncomputable
def alternatingConstHomologyDataOdd (X : C) (n : ℕ) (hn : Odd n) :
    ((alternatingConst.obj X).sc n).HomologyData :=
  .ofIsColimitCokernelCofork _ (by simp [hn]) _ (Limits.zeroCokernelOfZeroCancel _ (by simp [hn]))

set_option backward.isDefEq.respectTransparency false in
/-- The `n`-th homology of the alternating constant complex is `X` for `n = 0`. -/
noncomputable
def alternatingConstHomologyDataZero (X : C) (n : ℕ) (hn : n = 0) :
    ((alternatingConst.obj X).sc n).HomologyData :=
  .ofZeros _ (by simp [hn]) (by simp [hn])

instance (X : C) (n : ℕ) : (alternatingConst.obj X).HasHomology n := by
  rcases n.even_or_odd with h | h
  · rcases n with - | n
    · exact ⟨⟨alternatingConstHomologyDataZero X _ rfl⟩⟩
    · exact ⟨⟨alternatingConstHomologyDataEvenNEZero X _ h (by simp)⟩⟩
  · exact ⟨⟨alternatingConstHomologyDataOdd X _ h⟩⟩

/-- The `n`-th homology of the alternating constant complex is `X` for `n ≠ 0`. -/
lemma alternatingConst_exactAt (X : C) (n : ℕ) (hn : n ≠ 0) :
    (alternatingConst.obj X).ExactAt n := by
  rcases n.even_or_odd with h | h
  · exact ⟨(alternatingConstHomologyDataEvenNEZero X _ h hn), isZero_zero C⟩
  · exact ⟨(alternatingConstHomologyDataOdd X _ h), isZero_zero C⟩

/-- The `n`-th homology of the alternating constant complex is `X` for `n = 0`. -/
noncomputable
def alternatingConstHomologyZero (X : C) : (alternatingConst.obj X).homology 0 ≅ X :=
  (alternatingConstHomologyDataZero X _ rfl).left.homologyIso

end ChainComplex

variable [Preadditive C] [HasZeroObject C]

set_option backward.isDefEq.respectTransparency false in
/-- The alternating face complex of the constant complex is the alternating constant complex. -/
noncomputable def AlgebraicTopology.alternatingFaceMapComplexConst :
    Functor.const _ ⋙ alternatingFaceMapComplex C ≅ ChainComplex.alternatingConst :=
  NatIso.ofComponents (fun X ↦ HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) <| by
    rintro _ i rfl
    simp [SimplicialObject.δ, ← Finset.sum_smul, Fin.sum_neg_one_pow, Nat.even_add_one,
      -Nat.not_even_iff_odd]) (by intros; ext; simp)

namespace ChainComplex

/-- `alternatingConst.obj X` is homotopy equivalent to the chain
complex `(single₀ C).obj X`. -/
noncomputable def alternatingConstHomotopyEquiv (X : C) :
    HomotopyEquiv (alternatingConst.obj X) ((single₀ C).obj X) :=
  (HomotopyEquiv.ofIso (alternatingFaceMapComplexConst.app X).symm).trans
    ((SimplicialObject.Augmented.ExtraDegeneracy.const X).homotopyEquiv)

end ChainComplex
