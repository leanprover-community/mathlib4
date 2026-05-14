/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.CategoryTheory.MarkovCategory.Positive
public import Mathlib.CategoryTheory.CopyDiscardCategory.Widesubcategory
public import Mathlib.Probability.Kernel.Category.SFinKer
public import Mathlib.Probability.Kernel.Deterministic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Stoch

The category of measurable spaces with Markov kernels is a positive Markov category.

## Main definition

`Stoch` is defined as the wide subcategory `WideSubcategory StochHom` of `SFinKer`, where
`StochHom` selects Markov kernels, and this construction provides in particular the instance
`PositiveCategory Stoch`.

### Implementation notes

Among categories of measurable spaces and probability kernels, `Stoch` stands out as the unique
positive Markov category. In contrast, `SFinKer` and the category of finite kernels (not
implemented) do not satisfy positivity. To see why, consider the counterexample with
$X = Y = \{\varnothing\}$, kernels $\kappa(\cdot | \varnothing) = 2\delta_{\varnothing}$ and
$\eta(\cdot | \varnothing) = (1/2)\delta_{\varnothing}$: although their composition is
deterministic, the positivity equation fails.

## References

* [A synthetic approach to
  Markov kernels, conditional independence and theorems on sufficient statistics][fritz2020]
-/

public section

open CategoryTheory ProbabilityTheory Kernel

open scoped MonoidalCategory SFinKer ComonObj

universe u

/-- Morphism property selecting Markov kernels in `SFinKer`. -/
abbrev StochHom : MorphismProperty SFinKer := fun _ _ κ => IsMarkovKernel κ.1

instance : StochHom.IsStableUnderBraiding where
  id_mem X := by dsimp [StochHom]; infer_instance
  comp_mem κ η hκ hη := by dsimp [StochHom]; infer_instance
  whiskerLeft X Y Z κ hκ := by dsimp [StochHom]; infer_instance
  whiskerRight κ hκ Y := by dsimp [StochHom]; infer_instance
  associator_hom_mem X Y Z := isMarkovKernel_deterministic <| MeasurableEquiv.measurable _
  associator_inv_mem X Y Z := isMarkovKernel_deterministic <| MeasurableEquiv.measurable _
  leftUnitor_hom_mem X := IsMarkovKernel.map Kernel.id (by fun_prop)
  leftUnitor_inv_mem X := IsMarkovKernel.map Kernel.id (by fun_prop)
  rightUnitor_hom_mem X := IsMarkovKernel.map Kernel.id (by fun_prop)
  rightUnitor_inv_mem X := IsMarkovKernel.map Kernel.id (by fun_prop)
  braiding_hom_mem X Y := instIsMarkovKernelProdSwap
  braiding_inv_mem X Y := instIsMarkovKernelProdSwap

instance {X} : StochHom.IsStableUnderComonoid X where
  counit_mem := by dsimp [StochHom]; infer_instance
  comul_mem := by dsimp [StochHom]; infer_instance

/-- `Stoch` is the wide subcategory of `SFinKer` with Markov-kernel morphisms. -/
abbrev Stoch := WideSubcategory StochHom

variable {X Y : Stoch} (κ : X ⟶ Y)

instance [Deterministic κ.hom] : Deterministic κ where

instance : Deterministic (Δ[X]) where

instance : Deterministic (ε[X]) where
  hom_comul := by
    ext : 1
    simp only [WideSubcategory.comp_def, MorphismProperty.counit_hom]
    cat_disch

instance (X Y : Stoch) (κ : Kernel X.obj Y.obj) [IsDeterministic κ] [IsMarkovKernel κ] :
    Deterministic (X := X) (Y := Y) (⟨⟨κ, inferInstance⟩, inferInstance⟩ : X ⟶ Y) where
  hom_comul := by
    ext : 1; dsimp
    exact Deterministic.copy_natural _

section PositiveCategory

instance : IsMarkovKernel κ.hom.hom := κ.2

instance [Deterministic κ] : Deterministic κ.hom where
  hom_comul := WideSubcategory.hom_ext_iff.mp <| Deterministic.copy_natural κ

instance [Deterministic κ] : IsDeterministic κ.hom.hom where
  parallelComp_self_comp_copy' := by
    have := Deterministic.copy_natural κ.hom
    rw [SFinKer.Hom.ext_iff] at this
    dsimp at this
    rw [id_parallelComp_comp_parallelComp_id] at this
    exact this.symm

noncomputable instance : PositiveCategory Stoch.{u} where
  discard_natural κ := by ext : 2; simp
  copy_comp_natural κ η _ := by
    ext : 2
    dsimp
    simp only [id_parallelComp_id, id_comp, id_parallelComp_comp_parallelComp_id]
    have : IsDeterministic (κ ≫ η).hom.hom := inferInstance
    exact (comp_parallelComp_comp_copy).symm

end PositiveCategory
