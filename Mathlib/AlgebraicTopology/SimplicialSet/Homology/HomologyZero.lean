/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Homology of simplicial sets in degree 0

The main definition in this file is `SSet.homology₀Iso` which is
an isomorphism `X.homology R 0 ≅ ∐ (fun (_ : π₀ X) ↦ R)` for any simplicial
set `X`.

-/

@[expose] public section

universe w v v' u u'

open CategoryTheory Limits AlgebraicTopology Simplicial TypeCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

namespace SSet

variable (X : SSet) (R : C)

/-- Given a simplicial set `X`, this is the morphism from
`0`-chains with coefficients in `R` to coproduct of copies
of `R` indexed by `π₀ X`. -/
noncomputable def π₀.fromChainComplexXZero :
    (X.chainComplex R).X 0 ⟶ ∐ (fun (_ : π₀ X) ↦ R) :=
  (sigmaConst.obj _).map (↾π₀.mk)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma π₀.comp_fromChainComplexXZero (x : X _⦋0⦌) :
    X.ιChainComplex x ≫ π₀.fromChainComplexXZero X R =
    Sigma.ι (fun (_ : π₀ X) ↦ R) (π₀.mk x) := by
  simp [π₀.fromChainComplexXZero, ιChainComplex]

@[reassoc (attr := simp)]
lemma π₀.d_fromChainComplexXZero (n : ℕ) :
    (X.chainComplex R).d n 0 ≫ π₀.fromChainComplexXZero X R = 0 := by
  by_cases! hn : n ≠ 1
  · rw [HomologicalComplex.shape _ _ _ (by simp; lia), zero_comp]
  · subst hn
    ext x
    simp [π₀.sound (Edge.mk' x)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a simplicial set `X`, the cokernel of the differential `d 1 0`
of the chain complex of `X` with coefficients in `R` identifies
to the coproduct of copies of `R` indexed by `π₀ X`. -/
noncomputable def isColimitCokernelCoforkChainComplexDOneZero :
    IsColimit (CokernelCofork.ofπ _ (π₀.d_fromChainComplexXZero X R 1)) := by
  refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).1
    (Preadditive.isColimitCokernelCoforkOfCofork
      ((isColimitMapCoconeCoforkEquiv _ _).1
        (isColimitOfPreserves (sigmaConst.obj R) X.isColimitCoforkπ₀)))
  · refine parallelPair.ext (-Iso.refl _) (Iso.refl _) ?_ (by simp)
    simp [chainComplex, SSet.chainComplexFunctor, sub_eq_neg_add]
  · refine Cofork.ext (Iso.refl _) ?_
    ext
    simp [chainComplex, SSet.chainComplexFunctor, π₀.fromChainComplexXZero]

/-- A homology data saying that the singular homology in degree `0`
of a simplicial set with coefficients in `R` identify to a coproduct
of copies of `X` indexed by `π₀ X`. -/
@[simps! left_K left_H right_Q right_H]
noncomputable def homologyData₀ :
    ((X.chainComplex R).sc' 1 0 0).HomologyData :=
  ShortComplex.HomologyData.ofIsColimitCokernelCofork _ (by cat_disch) _
    (isColimitCokernelCoforkChainComplexDOneZero X R)

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma homologyData₀_left_π :
    dsimp% (X.homologyData₀ R).left.π = π₀.fromChainComplexXZero X R := rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma homologyData₀_left_i :
    dsimp% (X.homologyData₀ R).left.i = 𝟙 _ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma homologyData₀_left_liftK {T : C} (f : T ⟶ (X.chainComplex R).X 0) :
    dsimp% (X.homologyData₀ R).left.liftK f (by cat_disch) = f :=
  ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork_liftK ..

variable [CategoryWithHomology C]

/-- The homology of a simplicial set in degree `0` with coefficients
in `R` identifies to a coproduct of copies of `R` indexed by `π₀ X`. -/
noncomputable def homology₀Iso :
    X.homology R 0 ≅ ∐ (fun (_ : π₀ X) ↦ R) :=
  ShortComplex.homologyMapIso (HomologicalComplex.isoSc' _ 1 0 0 (by simp) (by simp)) ≪≫
    (X.homologyData₀ R).left.homologyIso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom (x : X _⦋0⦌) :
    (X.chainComplex R).liftCycles (k := X.ιChainComplex x) 0 (by simp) (by simp) ≫
      (X.chainComplex R).homologyπ 0 ≫ (X.homology₀Iso R).hom =
    Sigma.ι (fun (_ : π₀ X) ↦ R) (π₀.mk x) := by
  simp [homology₀Iso, HomologicalComplex.homologyπ, SSet.homology,
    HomologicalComplex.liftCycles]

/-- The augmentation map `X.homology R 0 ⟶ R`. -/
noncomputable def homology₀ε : X.homology R 0 ⟶ R :=
  (X.homology₀Iso R).hom ≫ Sigma.desc (fun _ ↦ 𝟙 R)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma liftCycles_ιChainComplex_homologyπ_homology₀ε (x : X _⦋0⦌) :
    (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
      (X.chainComplex R).homologyπ 0 ≫ X.homology₀ε R = 𝟙 R := by
  simp [homology₀ε]

set_option backward.isDefEq.respectTransparency false in
instance [X.IsConnected] : IsIso (X.homology₀ε R) := by
  dsimp [homology₀ε]
  simp only [isIso_comp_left_iff]
  let x : π₀ X := Classical.arbitrary _
  refine ⟨Sigma.ι (fun _ ↦ R) x, ?_, by simp⟩
  ext y
  obtain rfl : x = y := by subsingleton
  simp

end SSet
