/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Cochains from or to single complexes

We introduce constructors `Cochain.fromSingleMk` and `Cocycle.fromSingleMk`
for cochains and cocycles from a single complex. We also introduce similar
definitions for cochains and cocyles to a single complex.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

namespace CochainComplex

namespace HomComplex

variable {X : C} {K : CochainComplex C ℤ}

namespace Cochain

/-- Constructor for cochains from a single complex. -/
@[nolint unusedArguments]
noncomputable def fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (_ : p + n = q) :
    Cochain ((singleFunctor C p).obj X) K n :=
  Cochain.single ((HomologicalComplex.singleObjXSelf (.up ℤ) p X).hom ≫ f) n

variable (X K) in
@[simp]
lemma fromSingleMk_zero (p q n : ℤ) (h : p + n = q) :
    fromSingleMk (X := X) (K := K) 0 h = 0 := by
  simp [fromSingleMk]

@[simp]
lemma fromSingleMk_v {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    (fromSingleMk f h).v p q h =
      (HomologicalComplex.singleObjXSelf (.up ℤ) p X).hom ≫ f := by
  simp [fromSingleMk]

lemma fromSingleMk_v_eq_zero {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (p' q' : ℤ) (hpq' : p' + n = q') (hp' : p' ≠ p) :
    (fromSingleMk f h).v p' q' hpq' = 0 :=
  single_v_eq_zero _ _ _ _ _ hp'

lemma δ_fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (n' q' : ℤ) (h' : p + n' = q') :
    δ n n' (fromSingleMk f h) = fromSingleMk (f ≫ K.d q q') h' := by
  by_cases hq : q + 1 = q'
  · dsimp only [fromSingleMk]
    rw [δ_single _ n n' (by lia) (p - 1) q' (by lia) hq]
    simp
  · simp [δ_shape n n' (by lia), HomologicalComplex.shape K q q' (by simp; lia),
      fromSingleMk]

/-- Constructor for cochains to a single complex. -/
@[nolint unusedArguments]
noncomputable def toSingleMk {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (_ : p + n = q) :
    Cochain K ((singleFunctor C q).obj X) n :=
  Cochain.single (f ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) q X).inv) n

variable (X K) in
@[simp]
lemma toSingleMk_zero (p q n : ℤ) (h : p + n = q) :
    toSingleMk (X := X) (K := K) 0 h = 0 := by
  simp [toSingleMk]

@[simp]
lemma toSingleMk_v {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    (toSingleMk f h).v p q h =
      f ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) q X).inv := by
  simp [toSingleMk]

lemma toSingleMk_v_eq_zero {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' q' : ℤ) (hpq' : p' + n = q') (hp' : p' ≠ p) :
    (toSingleMk f h).v p' q' hpq' = 0 :=
  single_v_eq_zero _ _ _ _ _ hp'

lemma δ_toSingleMk {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (n' p' : ℤ) (h' : p' + n' = q) :
    δ n n' (toSingleMk f h) = n'.negOnePow • toSingleMk (K.d p' p ≫ f) h' := by
  by_cases hp : p' + 1 = p
  · dsimp only [toSingleMk]
    rw [δ_single _ n n' (by lia) p' (q + 1) (by lia) rfl]
    simp
  · simp [δ_shape n n' (by lia), HomologicalComplex.shape K p' p (by simp; lia)]

end Cochain

namespace Cocycle

/-- Constructor for cocycles from a single complex. -/
@[simps!]
noncomputable def fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    Cocycle ((singleFunctor C p).obj X) K n :=
  Cocycle.mk (Cochain.fromSingleMk f h) _ rfl (by
    rw [Cochain.δ_fromSingleMk _ _ _ q' (by lia), hf]
    simp)

/-- Constructor for cocycles to a single complex. -/
@[simps!]
noncomputable def toSingleMk {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) :
    Cocycle K ((singleFunctor C q).obj X) n :=
  Cocycle.mk (Cochain.toSingleMk f h) _ rfl (by
    rw [Cochain.δ_toSingleMk _ _ _ p' (by lia), hf]
    simp)

end Cocycle

end HomComplex

end CochainComplex
