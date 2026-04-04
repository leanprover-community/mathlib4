/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Fabian Odermatt
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.TopCat.ToSSet

/-!
# Homotopy invariance of singular homology

In this file, we show that for any homotopy `H : TopCat.Homotopy f g`
between two morphisms `f : X ⟶ Y` and `g : X ⟶ Y` in `TopCat`,
the corresponding morphisms on the singular chain complexes
are homotopic, and in particular the induced morphisms
on singular homology are equal.

The proof proceeds by observing that this result is a particular
case of the homotopy invariance of the homology of simplicial sets
(see the file `Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean`),
applied to the morphisms `TopCat.toSSet.map f` and `TopCat.toSSet.map g`
between the singular simplicial sets of `X` and `Y`. That the homotopy `H`
induces a homotopy between these morphisms of simplicial sets
is the definition `TopCat.Homotopy.toSSet` which appeared in the file
`Mathlib/Topology/Homotopy/TopCat/ToSSet.lean`.

This result was first formalized in Lean 3 in 2022 by
Brendan Seamus Murphy (with a different proof).

-/

@[expose] public section

universe v u w

open AlgebraicTopology CategoryTheory Limits
open scoped ContinuousMap

namespace TopCat.Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X Y : TopCat.{w}} {f g : X ⟶ Y}

/-- Two homotopic morphisms in `TopCat` induce homotopic morphisms on the
singular chain complexes with coefficients in `R` (e.g. `R := ℤ` considered as
an object of the category of abelian groups). -/
noncomputable def singularChainComplexFunctorObjMap (H : TopCat.Homotopy f g) (R : C) :
    _root_.Homotopy (((singularChainComplexFunctor C).obj R).map f)
      (((singularChainComplexFunctor C).obj R).map g) :=
  H.toSSet.singularChainComplexFunctorObjMap R

variable [CategoryWithHomology C]

open HomologicalComplex in
/-- Two homotopic morphisms in `TopCat` induce equal morphisms on the
singular homology with coefficients in `R` (e.g. `R := ℤ` considered as
an object of the category of abelian groups). -/
lemma singularHomologyFunctor_obj_map_eq (H : TopCat.Homotopy f g) (R : C) (n : ℕ) :
    (((singularHomologyFunctor C n).obj R)).map f =
    (((singularHomologyFunctor C n).obj R)).map g :=
  (H.singularChainComplexFunctorObjMap R).homologyMap_eq n

@[deprecated (since := "2026-04-01")]
alias congr_homologyMap_singularChainComplexFunctor :=
  singularHomologyFunctor_obj_map_eq

end TopCat.Homotopy

namespace AlgebraicTopology

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X Y : TopCat.{w}} {f g : X ⟶ Y} [CategoryWithHomology C]

/-- A homotopy equivalence between topological spaces induces an isomorphism between the
singular homology groups. -/
@[simps] noncomputable
def singularHomologyFunctorHomotopyEquiv (H : X ≃ₕ Y) (R : C) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj X ≅ ((singularHomologyFunctor C n).obj R).obj Y where
  hom := ((singularHomologyFunctor C n).obj R).map (TopCat.ofHom H.toFun)
  inv := ((singularHomologyFunctor C n).obj R).map (TopCat.ofHom H.symm.toFun)
  hom_inv_id := by
    rw [← Functor.map_comp, ← TopCat.ofHom_comp,
      TopCat.Homotopy.singularHomologyFunctor_obj_map_eq (g := 𝟙 X) (by exact H.left_inv.some)]
    simp
  inv_hom_id := by
    rw [← Functor.map_comp, ← TopCat.ofHom_comp,
      TopCat.Homotopy.singularHomologyFunctor_obj_map_eq (g := 𝟙 Y) (by exact H.right_inv.some)]
    simp

theorem isZero_singularHomologyFunctor_of_contractibleSpace
    (X : TopCat.{w}) [ContractibleSpace X] (R : C) (n : ℕ) (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj X) := by
  rw [(singularHomologyFunctorHomotopyEquiv (X := X) (Y := .of PUnit.{w + 1})
    ((ContractibleSpace.hequiv X PUnit.{w + 1}).some) R n).isZero_iff]
  exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ _ _ _ hn

-- TODO: Relax to `PathConnectedSpace` when `n = 0`.
instance (X : TopCat.{w}) [ContractibleSpace X] (R : C) (n : ℕ) :
    IsIso (((singularHomologyFunctor C n).obj R).map (terminal.from X)) := by
  convert (singularHomologyFunctorHomotopyEquiv (X := X) (Y := ⊤_ TopCat)
    ((ContractibleSpace.hequiv X (⊤_ TopCat)).some) R n).isIso_hom
  dsimp [singularHomologyFunctorHomotopyEquiv]
  congr
  exact terminal.hom_ext _ _

-- TODO(@joelriou): relax to `PathConnectedSpace`.
/-- The isomorphism `H₀(X, R) ≅ R` for a contractible space `X`. -/
noncomputable def singularHomologyFunctorZeroOfContractibleSpace
    (X : TopCat.{w}) [ContractibleSpace X] (R : C) :
    ((singularHomologyFunctor C 0).obj R).obj X ≅ R :=
    asIso (((singularHomologyFunctor C 0).obj R).map (terminal.from X)) ≪≫
    singularHomologyFunctorZeroOfTotallyDisconnectedSpace _ _ _ ≪≫ coproductUniqueIso _

end AlgebraicTopology
