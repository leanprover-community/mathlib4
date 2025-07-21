/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Amelia Livingston
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Module.BigOperators
import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# hm

-/

universe v u

open CategoryTheory Limits

@[simp]
lemma ComplexShape.up_nat_odd_add {i j : ℕ} (h : (ComplexShape.up ℕ).Rel i j) : Odd (i + j) := by
  subst h
  norm_num

@[simp]
lemma ComplexShape.down_nat_odd_add {i j : ℕ} (h : (ComplexShape.down ℕ).Rel i j) :
    Odd (i + j) := by
  subst h
  norm_num

namespace HomologicalComplex

open ShortComplex

variable {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
  (A : C) {φ : A ⟶ A} {ψ : A ⟶ A} (hOdd : φ ≫ ψ = 0) (hEven : ψ ≫ φ = 0)

/-- Given `c : ComplexShape ℕ` such that `i j : ℕ` have opposite parity if they are related by
`c`.vfdsfd -/
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

noncomputable def alternatingConstScEvenIso
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

noncomputable def alternatingConstScOddIso
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

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma alternatingConst_iCycles_even_comp [CategoryWithHomology C]
    {j : ℕ} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Even j) :
    (alternatingConst A hOdd hEven hc).iCycles j ≫ φ = 0 := by
  rw [← cancel_epi (ShortComplex.cyclesMapIso
    (alternatingConstScEvenIso A hOdd hEven hc hpj hnj  h)).inv]
  simpa [HomologicalComplex.iCycles, -Preadditive.IsIso.comp_left_eq_zero, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor, alternatingConstScEvenIso,
    Category.id_comp (X := (alternatingConst A hOdd hEven hc).X _)]
    using (ShortComplex.mk ψ φ hEven).iCycles_g

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma alternatingConst_iCycles_odd_comp [CategoryWithHomology C]
    {j : ℕ} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Odd j) :
    (alternatingConst A hOdd hEven hc).iCycles j ≫ ψ = 0 := by
  rw [← cancel_epi (ShortComplex.cyclesMapIso
    (alternatingConstScOddIso A hOdd hEven hc hpj hnj h)).inv]
  simpa [HomologicalComplex.iCycles, -Preadditive.IsIso.comp_left_eq_zero, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor, alternatingConstScOddIso,
    Category.id_comp (X := (alternatingConst A hOdd hEven hc).X _)]
    using (ShortComplex.mk φ ψ hOdd).iCycles_g

noncomputable def alternatingConstHomologyEvenIso [CategoryWithHomology C]
    {j : ℕ} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Even j) :
    (alternatingConst A hOdd hEven hc).homology j ≅ (ShortComplex.mk ψ φ hEven).homology :=
  ShortComplex.homologyMapIso (alternatingConstScEvenIso A hOdd hEven hc hpj hnj h)

noncomputable def alternatingConstHomologyOddIso [CategoryWithHomology C]
    {j : ℕ} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Odd j) :
    (alternatingConst A hOdd hEven hc).homology j ≅ (ShortComplex.mk φ ψ hOdd).homology :=
  ShortComplex.homologyMapIso (alternatingConstScOddIso A hOdd hEven hc hpj hnj h)

end HomologicalComplex

open CategoryTheory Limits AlgebraicTopology

variable {C : Type*} [Category C]

namespace ChainComplex

/-- The chain complex `X ←0- X ←𝟙- X ←0- X ←𝟙- X ⋯`.
It is exact away from `0` and has homology `X` at `0`. -/
@[simps]
noncomputable def alternatingConstFunctor [HasZeroMorphisms C] : C ⥤ ChainComplex C ℕ where
  obj X := HomologicalComplex.alternatingConst X (Category.id_comp 0) (Category.comp_id 0)
    (fun _ _ => ComplexShape.down_nat_odd_add)
  map {X Y} f := {
    f _ := f
    comm' i j hij := by by_cases Even i <;> simp_all [-Nat.not_even_iff_odd] }

variable [HasZeroMorphisms C] [HasZeroObject C]

open ZeroObject

/-- The `n`-th homology of the alternating constant complex is zero for non-zero even `n`. -/
noncomputable
def alternatingConstFunctorHomologyDataEvenNEZero (X : C) (n : ℕ) (hn : Even n) (h₀ : n ≠ 0) :
    ((alternatingConstFunctor.obj X).sc n).HomologyData :=
  .ofIsLimitKernelFork _ (by simp [Nat.even_add_one, hn]) _
    (Limits.zeroKernelOfCancelZero _ (by cases n <;> simp_all))

/-- The `n`-th homology of the alternating constant complex is zero for odd `n`. -/
noncomputable
def alternatingConstFunctorHomologyDataOdd (X : C) (n : ℕ) (hn : Odd n) :
    ((alternatingConstFunctor.obj X).sc n).HomologyData :=
  .ofIsColimitCokernelCofork _ (by simp [hn]) _ (Limits.zeroCokernelOfZeroCancel _ (by simp [hn]))

/-- The `n`-th homology of the alternating constant complex is `X` for `n = 0`. -/
noncomputable
def alternatingConstFunctorHomologyDataZero (X : C) (n : ℕ) (hn : n = 0) :
    ((alternatingConstFunctor.obj X).sc n).HomologyData :=
  .ofZeros _ (by simp [hn]) (by simp [hn])

instance (X : C) (n : ℕ) : (alternatingConstFunctor.obj X).HasHomology n := by
  rcases n.even_or_odd with h | h
  · rcases n with - | n
    · exact ⟨⟨alternatingConstFunctorHomologyDataZero X _ rfl⟩⟩
    · exact ⟨⟨alternatingConstFunctorHomologyDataEvenNEZero X _ h (by simp)⟩⟩
  · exact ⟨⟨alternatingConstFunctorHomologyDataOdd X _ h⟩⟩

/-- The `n`-th homology of the alternating constant complex is `X` for `n ≠ 0`. -/
lemma alternatingConstFunctor_exactAt (X : C) (n : ℕ) (hn : n ≠ 0) :
    (alternatingConstFunctor.obj X).ExactAt n := by
  rcases n.even_or_odd with h | h
  · exact ⟨(alternatingConstFunctorHomologyDataEvenNEZero X _ h hn), isZero_zero C⟩
  · exact ⟨(alternatingConstFunctorHomologyDataOdd X _ h), isZero_zero C⟩

/-- The `n`-th homology of the alternating constant complex is `X` for `n = 0`. -/
noncomputable
def alternatingConstFunctorHomologyZero (X : C) : (alternatingConstFunctor.obj X).homology 0 ≅ X :=
  (alternatingConstFunctorHomologyDataZero X _ rfl).left.homologyIso

end ChainComplex

variable [Preadditive C] [HasZeroObject C]

/-- The alternating face complex of the constant complex is the alternating constant complex. -/
noncomputable def AlgebraicTopology.alternatingFaceMapComplexConstFunctor :
    Functor.const _ ⋙ alternatingFaceMapComplex C ≅ ChainComplex.alternatingConstFunctor :=
  NatIso.ofComponents (fun X ↦ HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) <| by
    rintro _ i rfl
    simp [SimplicialObject.δ, ← Finset.sum_smul, Fin.sum_neg_one_pow, Nat.even_add_one,
      -Nat.not_even_iff_odd]) (by intros; ext; simp)

namespace ChainComplex

/-- `alternatingConst.obj X` is homotopy equivalent to the chain
complex `(single₀ C).obj X`. -/
noncomputable def alternatingConstFunctorHomotopyEquiv (X : C) :
    HomotopyEquiv (alternatingConstFunctor.obj X) ((single₀ C).obj X) :=
  (HomotopyEquiv.ofIso (alternatingFaceMapComplexConstFunctor.app X).symm).trans
    ((SimplicialObject.Augmented.ExtraDegeneracy.const X).homotopyEquiv)

end ChainComplex
