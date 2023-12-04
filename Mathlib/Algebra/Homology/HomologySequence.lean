/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# The homology sequence

If `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is a short exact sequence in a category of complexes
`HomologicalComplex C c` in an abelian category (i.e. `S` is a short complex in
that category and satisfies `hS : S.ShortExact`), then whenever `i` and `j` are degrees
such that `hij : c.Rel i j`, then there is a long exact sequence :
`... ⟶ S.X₁.homology i ⟶ S.X₂.homology i ⟶ S.X₃.homology i ⟶ S.X₁.homology j ⟶ ...` (TODO).

The proof is based on the snake lemma, similarly as it was originally done in
the Liquid Tensor Experiment.

## References

* https://stacks.math.columbia.edu/tag/0111

-/

open CategoryTheory Category Limits

namespace HomologicalComplex

section HasZeroMorphisms

variable {C ι : Type*} [Category C] [HasZeroMorphisms C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) (φ : K ⟶ L) (i j : ι)
  [K.HasHomology i] [K.HasHomology j] [L.HasHomology i] [L.HasHomology j]

/-- The morphism `K.opcycles i ⟶ K.cycles j` that is induced by `K.d i j`. -/
noncomputable def opcyclesToCycles [K.HasHomology i] [K.HasHomology j] :
    K.opcycles i ⟶ K.cycles j :=
  K.liftCycles (K.fromOpcycles i j) _ rfl (by simp)

@[reassoc (attr := simp)]
lemma opcyclesToCycles_iCycles : K.opcyclesToCycles i j ≫ K.iCycles j = K.fromOpcycles i j := by
  dsimp only [opcyclesToCycles]
  simp

@[reassoc]
lemma pOpcycles_opcyclesToCycles_iCycles :
    K.pOpcycles i ≫ K.opcyclesToCycles i j ≫ K.iCycles j = K.d i j := by
  simp [opcyclesToCycles]

@[reassoc (attr := simp)]
lemma pOpcycles_opcyclesToCycles :
    K.pOpcycles i ≫ K.opcyclesToCycles i j = K.toCycles i j := by
  simp only [← cancel_mono (K.iCycles j), assoc, opcyclesToCycles_iCycles,
    p_fromOpcycles, toCycles_i]

@[reassoc (attr := simp)]
lemma homologyι_opcyclesToCycles :
    K.homologyι i ≫ K.opcyclesToCycles i j = 0 := by
  simp only [← cancel_mono (K.iCycles j), assoc, opcyclesToCycles_iCycles,
    homologyι_comp_fromOpcycles, zero_comp]

@[reassoc (attr := simp)]
lemma opcyclesToCycles_homologyπ :
    K.opcyclesToCycles i j ≫ K.homologyπ j = 0 := by
  simp only [← cancel_epi (K.pOpcycles i),
    pOpcycles_opcyclesToCycles_assoc, toCycles_comp_homologyπ, comp_zero]

variable {K L}

@[reassoc (attr := simp)]
lemma opcyclesToCycles_naturality :
    opcyclesMap φ i ≫ opcyclesToCycles L i j = opcyclesToCycles K i j ≫ cyclesMap φ j := by
  simp only [← cancel_mono (L.iCycles j), ← cancel_epi (K.pOpcycles i),
    assoc, p_opcyclesMap_assoc, pOpcycles_opcyclesToCycles_iCycles, Hom.comm, cyclesMap_i,
    pOpcycles_opcyclesToCycles_iCycles_assoc]

variable (C c)

/-- The natural transformation `K.opcyclesToCycles i j : K.opcycles i ⟶ K.cycles j` for all
`K : HomologicalComplex C c`. -/
@[simps]
noncomputable def natTransOpCyclesToCycles [CategoryWithHomology C] :
    opcyclesFunctor C c i ⟶ cyclesFunctor C c j where
  app K := K.opcyclesToCycles i j

end HasZeroMorphisms

section Preadditive

variable {C ι : Type*} [Category C] [Preadditive C] {c : ComplexShape ι}
  (K : HomologicalComplex C c) (i j : ι) (hij : c.Rel i j)

namespace HomologySequence

/-- The diagram `K.homology i ⟶ K.opcycles i ⟶ K.cycles j ⟶ K.homology j`. -/
@[simp]
noncomputable def composableArrows₃ [K.HasHomology i] [K.HasHomology j] :
    ComposableArrows C 3 :=
  ComposableArrows.mk₃ (K.homologyι i) (K.opcyclesToCycles i j) (K.homologyπ j)

instance [K.HasHomology i] [K.HasHomology j] :
    Mono ((composableArrows₃ K i j).map' 0 1) := by
  dsimp
  infer_instance

instance [K.HasHomology i] [K.HasHomology j] :
    Epi ((composableArrows₃ K i j).map' 2 3) := by
  dsimp
  infer_instance

/-- The diagram `K.homology i ⟶ K.opcycles i ⟶ K.cycles j ⟶ K.homology j` is exact
when `c.Rel i j`. -/
lemma composableArrows₃_exact [CategoryWithHomology C] :
    (composableArrows₃ K i j).Exact := by
  let S := ShortComplex.mk (K.homologyι i) (K.opcyclesToCycles i j) (by simp)
  let S' := ShortComplex.mk (K.homologyι i) (K.fromOpcycles i j) (by simp)
  let ι : S ⟶ S' :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := K.iCycles j }
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono ι]
    exact S'.exact_of_f_is_kernel (K.homologyIsKernel i j (c.next_eq' hij))
  let T := ShortComplex.mk (K.opcyclesToCycles i j) (K.homologyπ j) (by simp)
  let T' := ShortComplex.mk (K.toCycles i j) (K.homologyπ j) (by simp)
  let π : T' ⟶ T :=
    { τ₁ := K.pOpcycles i
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  have hT : T.Exact := by
    rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono π]
    exact T'.exact_of_g_is_cokernel (K.homologyIsCokernel i j (c.prev_eq' hij))
  apply ComposableArrows.exact_of_δ₀
  · exact hS.exact_toComposableArrows
  · exact hT.exact_toComposableArrows

variable (C)

attribute [local simp] homologyMap_comp cyclesMap_comp opcyclesMap_comp

/-- The functor `HomologicalComplex C c ⥤ ComposableArrows C 3` that maps `K` to the
diagram `K.homology i ⟶ K.opcycles i ⟶ K.cycles j ⟶ K.homology j`. -/
@[simps]
noncomputable def composableArrows₃Functor [CategoryWithHomology C] :
    HomologicalComplex C c ⥤ ComposableArrows C 3 where
  obj K := composableArrows₃ K i j
  map {K L} φ := ComposableArrows.homMk₃ (homologyMap φ i) (opcyclesMap φ i) (cyclesMap φ j)
    (homologyMap φ j) (by aesop_cat) (by aesop_cat) (by aesop_cat)

end HomologySequence

end Preadditive

end HomologicalComplex
