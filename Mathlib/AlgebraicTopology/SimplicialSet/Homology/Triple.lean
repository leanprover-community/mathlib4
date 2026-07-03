/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative

/-!
# The long exact sequence of a triple of simplicial sets


-/

@[expose] public section

universe w

open Simplicial CategoryTheory Limits

namespace SSetPair

variable {C : Type*} [Category* C] [Abelian C] [HasCoproducts.{w} C]
  {X Y Z : SSet.{w}} (i : X ⟶ Y) (j : Y ⟶ Z) (ij : X ⟶ Z)
  [Mono i] [Mono j] [Mono ij] (fac : i ≫ j = ij) (R : C)

abbrev tripleMap₁₂ : SSetPair.of i ⟶ SSetPair.of ij := homMk (𝟙 X) j

abbrev tripleMap₂₃ : SSetPair.of ij ⟶ SSetPair.of j := homMk i (𝟙 Z)

abbrev tripleMap₁₃ : SSetPair.of i ⟶ SSetPair.of j := homMk i j

@[reassoc (attr := simp)]
lemma tripleMap₁₂_comp_tripleMap₂₃ :
    tripleMap₁₂ i j ij fac ≫ tripleMap₂₃ i j ij fac = tripleMap₁₃ i j := by
  cat_disch

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma chainComplexMap_tripleMap₁₃ :
    chainComplexMap (tripleMap₁₃ i j ) R = 0 := by
  ext n
  rw [← cancel_epi (((SSetPair.of i).chainComplexπ R).f n)]
  cat_disch

@[reassoc (attr := simp)]
lemma chainComplexMap_tripleMap₁₂_chainComplexMap_tripleMap₂₃ :
    chainComplexMap (tripleMap₁₂ i j ij fac) R ≫
      chainComplexMap (tripleMap₂₃ i j ij fac) R = 0 := by
  rw [← chainComplexMap_comp, tripleMap₁₂_comp_tripleMap₂₃,
    chainComplexMap_tripleMap₁₃]

noncomputable abbrev tripleShortComplex : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk _ _ (chainComplexMap_tripleMap₁₂_chainComplexMap_tripleMap₂₃ i j ij fac R)

lemma shortExact_tripleShortComplex_eval (n : ℕ) :
    ((tripleShortComplex i j ij fac R).map (HomologicalComplex.eval _ _ n)).ShortExact := by
  sorry

instance (n : ℕ) : Mono ((tripleShortComplex i j ij fac R).f.f n) :=
  (shortExact_tripleShortComplex_eval i j ij fac R n).mono_f

instance (n : ℕ) : Epi ((tripleShortComplex i j ij fac R).g.f n) :=
  (shortExact_tripleShortComplex_eval i j ij fac R n).epi_g

instance : Mono (tripleShortComplex i j ij fac R).f :=
  HomologicalComplex.mono_of_mono_f _ inferInstance

instance : Epi (tripleShortComplex i j ij fac R).g :=
  HomologicalComplex.epi_of_epi_f _ inferInstance

lemma shortExact_tripleShortComplex :
    (tripleShortComplex i j ij fac R).ShortExact where
  exact := by
    rw [HomologicalComplex.exact_iff_degreewise_exact]
    intro n
    exact (shortExact_tripleShortComplex_eval i j ij fac R n).exact

end SSetPair
