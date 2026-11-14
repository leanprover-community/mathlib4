/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-! # Conditions under which the complex of morphisms is bounded below

If `K` and `L` are cochain complexes indexed by `ℤ` in a `R`-linear category,
we show that the cochain complex `linearHomComplex R K L` of morphisms
from `K` to `L` is `≥ n` if `K ≤ p`, `L ≥ q`, and `p + n ≤ q`.
In particular, if `K ≤ 0` and `L ≥ 0`, then `linearHomComplex R K L` if `≥ 0`.

-/

@[expose] public section

open CategoryTheory Category Limits Preadditive

variable {C : Type*} [Category* C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

namespace CochainComplex.HomComplex

variable (K L : CochainComplex C ℤ)

lemma subsingleton_cochain
    (n p q : ℤ) [K.IsStrictlyLE p] [L.IsStrictlyGE q] (h : p + n < q) :
    Subsingleton (Cochain K L n) where
  allEq α β := by
    ext i j hij
    by_cases! hi : i ≤ p
    · by_cases! hj : q ≤ j
      · lia
      · exact (L.isZero_of_isStrictlyGE q j hj).eq_of_tgt ..
    · exact (K.isZero_of_isStrictlyLE p i hi).eq_of_src ..

lemma isStrictlyGE_linearHomComplex (n p q : ℤ) [K.IsStrictlyLE p] [L.IsStrictlyGE q]
    (h : p + n ≤ q := by lia) :
    (linearHomComplex R K L).IsStrictlyGE n := by
  rw [isStrictlyGE_iff]
  intro a ha
  rw [ModuleCat.isZero_of_iff_subsingleton]
  exact subsingleton_cochain K L a p q (by lia)

instance [K.IsStrictlyLE 0] [L.IsStrictlyGE 0] :
    (linearHomComplex R K L).IsStrictlyGE 0 :=
  isStrictlyGE_linearHomComplex K L 0 0 0

end CochainComplex.HomComplex
