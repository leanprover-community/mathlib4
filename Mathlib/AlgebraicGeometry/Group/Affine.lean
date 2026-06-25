/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# The equivalence between Hopf algebras and affine group schemes

This file constructs `Spec` as a functor from `R`-Hopf algebras to group schemes over `Spec R`,
shows it is full and faithful, and has affine group schemes as essential image.

We want to show that Hopf algebras correspond to affine group schemes. This can easily be done
categorically assuming both categories on either side are defined thoughtfully. However, the
categorical version will not be workable with if we do not also have links to the non-categorical
notions. Therefore, one solution would be to build the left, top and right edges of the following
diagram so that the bottom edge can be obtained by composing the three.

```
  Cogrp Mod_R ≌ Grp AffSch_{Spec R} ≌ Aff Grp Sch_{Spec R}
      ↑ ↓                                      ↑ ↓
R-Hopf algebras         ≃       Affine group schemes over Spec R
```

If we do not care about going back from affine group schemes over `Spec R` to `R`-Hopf algebras
(eg because all our affine group schemes are given as the `Spec` of some algebra), then we can
follow the following simpler diagram:

```
  Cogrp Mod_R   ⥤        Grp Sch_{Spec R}
      ↑ ↓                        ↓
R-Hopf algebras → Affine group schemes over Spec R
```
where the top `≌` comes from the essentially surjective functor `Cogrp Mod_R ⥤ Grp Sch_{Spec R}`,
so that in particular we do not easily know that its inverse is given by `Γ`.
-/

@[expose] public section

suppress_compilation

open AlgebraicGeometry Coalgebra Scheme CategoryTheory MonoidalCategory Functor Monoidal Opposite
  Limits TensorProduct MonObj GrpObj
open scoped SpecOfNotation

universe w v u
variable {R : CommRingCat.{u}}

/-!
### Left edge: `R`-Hopf algebras correspond to cogroup objects under `R`

Ways to turn an unbundled `R`-Hopf algebra into a bundled cogroup object under `R`, and vice versa,
are already provided in `Mathlib.Algebra.Category.CommHopfAlgCat`.

### Top edge: `Spec` as a functor on Hopf algebras

In this section we construct `Spec` as a functor from `R`-Hopf algebras to affine group schemes over
`Spec R`.
-/

namespace AlgebraicGeometry

section topEdge

variable (R) in
/-- `Spec` as a functor from `R`-algebras to schemes over `Spec R`. -/
abbrev algSpec : (CommAlgCat R)ᵒᵖ ⥤ Over (Spec R) :=
  (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

variable (R) in
/-- The Gamma functor as a functor from schemes over `Spec R` to `R`-algebras. -/
abbrev algΓ : Over (Spec R) ⥤ (CommAlgCat R)ᵒᵖ :=
  Over.post Γ.rightOp ⋙ Over.map (ΓSpecIso R).inv.op ⋙
    (Over.opEquivOpUnder R).functor ⋙ (commAlgCatEquivUnder R).inverse.op

instance preservesLimitsOfSize_algSpec : PreservesLimitsOfSize.{w, v} (algSpec R) :=
  inferInstanceAs <| PreservesLimitsOfSize.{w, v} <|
    (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

set_option backward.isDefEq.respectTransparency false in
instance preservesColimitsOfSize_algΓ : PreservesColimitsOfSize.{w, v} (algΓ R) := by
  unfold algΓ; infer_instance

instance braidedAlgSpec : (algSpec R).Braided := .ofChosenFiniteProducts _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp] lemma algSpec_ε_left : (LaxMonoidal.ε (algSpec R)).left = 𝟙 (Spec R) := by
  convert! (LaxMonoidal.ε (algSpec R)).w
  simpa [-Category.comp_id] using! (Category.comp_id _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp] lemma algSpec_η_left : (OplaxMonoidal.η (algSpec R)).left = 𝟙 (Spec R) := by
  simpa using (OplaxMonoidal.η (algSpec R)).w

@[simp] lemma algSpec_δ_left (X Y : (CommAlgCat R)ᵒᵖ) :
    (OplaxMonoidal.δ (algSpec R) X Y).left = (pullbackSpecIso R X.unop Y.unop).inv :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma algSpec_μ_left (X Y : (CommAlgCat R)ᵒᵖ) :
    (LaxMonoidal.μ (algSpec R) X Y).left = (pullbackSpecIso R X.unop Y.unop).hom := by
  rw [← cancel_epi (pullbackSpecIso R X.unop Y.unop).inv, Iso.inv_hom_id, ← algSpec_δ_left,
    ← Over.comp_left]
  simp [-Over.comp_left]
  rfl

@[simp]
lemma prodComparison_algSpec_left (A B : (CommAlgCat R)ᵒᵖ) :
    (CartesianMonoidalCategory.prodComparison (algSpec R) A B).left =
      (pullbackSpecIso R A.unop B.unop).inv := rfl

@[simp]
lemma prodComparisonIso_algSpec_inv_left (A B : (CommAlgCat R)ᵒᵖ) :
    (CartesianMonoidalCategory.prodComparisonIso (algSpec R) A B).inv.left =
      (pullbackSpecIso R A.unop B.unop).hom := by
  rw [← Iso.comp_inv_eq_id, ← prodComparison_algSpec_left, ← Over.comp_left,
    ← CartesianMonoidalCategory.prodComparisonIso_hom, Iso.inv_hom_id, Over.id_left]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma preservesTerminalIso_algSpec :
    CartesianMonoidalCategory.preservesTerminalIso (algSpec R) =
      Over.isoMk (Iso.refl (Spec R)) (by simp) := by
  ext1; exact CartesianMonoidalCategory.toUnit_unique _ _

@[simp]
lemma preservesTerminalIso_algSpec_inv_left :
    (CartesianMonoidalCategory.preservesTerminalIso (algSpec R)).inv.left = 𝟙 (Spec R) := by
  simp [preservesTerminalIso_algSpec]

/-- `Spec` is full on `R`-algebras. -/
instance algSpec.instFull : (algSpec R).Full :=
  inferInstanceAs <| Functor.Full <|
    (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

/-- `Spec` is faithful on `R`-algebras. -/
instance algSpec.instFaithful : (algSpec R).Faithful :=
  inferInstanceAs <| Functor.Faithful <|
    (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

/-- `Spec` is fully faithful on `R`-algebras, with inverse `Gamma`. -/
def algSpec.fullyFaithful : (algSpec R).FullyFaithful :=
  ((commAlgCatEquivUnder R).op.trans (Over.opEquivOpUnder R).symm).fullyFaithfulFunctor.comp <|
    Spec.fullyFaithful.over _

variable (R) in
/-- `Spec` as a functor from `R`-bialgebras to monoid schemes over `Spec R`. -/
abbrev bialgSpec : (CommBialgCat R)ᵒᵖ ⥤ Mon (Over <| Spec R) :=
  (commBialgCatEquivComonCommAlgCat R).functor.leftOp ⋙ (algSpec R).mapMon

/-- `Spec` is full on `R`-bialgebras. -/
instance bialgSpec.instFull : (bialgSpec R).Full := inferInstance

/-- `Spec` is faithful on `R`-bialgebras. -/
instance bialgSpec.instFaithful : (bialgSpec R).Faithful := inferInstance

/-- `Spec` is fully faithful on `R`-bialgebras, with inverse `Gamma`. -/
def bialgSpec.fullyFaithful : (bialgSpec R).FullyFaithful :=
  (commBialgCatEquivComonCommAlgCat R).fullyFaithfulFunctor.leftOp.comp
    algSpec.fullyFaithful.mapMon

variable (R) in
/-- `Spec` as a functor from `R`-Hopf algebras to group schemes over `Spec R`. -/
abbrev hopfSpec : (CommHopfAlgCat R)ᵒᵖ ⥤ Grp (Over <| Spec R) :=
  (commHopfAlgCatEquivCogrpCommAlgCat R).functor.leftOp ⋙ (algSpec R).mapGrp

/-- `Spec` is full on `R`-Hopf algebras. -/
instance hopfSpec.instFull : (hopfSpec R).Full := inferInstance

/-- `Spec` is faithful on `R`-Hopf algebras. -/
instance hopfSpec.instFaithful : (hopfSpec R).Faithful := inferInstance

/-- `Spec` is fully faithful on `R`-Hopf algebras, with inverse `Gamma`. -/
def hopfSpec.fullyFaithful : (hopfSpec R).FullyFaithful :=
  (commHopfAlgCatEquivCogrpCommAlgCat R).fullyFaithfulFunctor.leftOp.comp
    algSpec.fullyFaithful.mapGrp

namespace Scheme
section universe_polymorphic
variable {R A : CommRingCat.{u}} {X M G : Scheme.{v}}

@[simps -isSimp]
instance specOverSpec [Algebra R A] : (Spec A).Over (Spec R) where
  hom := Spec.map <| CommRingCat.ofHom <| algebraMap ..

instance locallyOfFiniteType_specOverSpec [Algebra R A] [Algebra.FiniteType R A] :
    LocallyOfFiniteType (Spec A ↘ Spec R) := by
  rw [specOverSpec_over, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  simpa [RingHom.finiteType_algebraMap]

attribute [local simp] AlgHom.toUnder in
@[simps! one]
instance asOver.instMonObj [Bialgebra R A] : MonObj ((Spec A).asOver (Spec R)) :=
  ((bialgSpec R).obj <| .op <| .of R A).mon

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma specOverSpec_one [Bialgebra R A] :
    η[(Spec A).asOver (Spec R)] = LaxMonoidal.ε (algSpec R) ≫
      Over.homMk (V := (Spec A).asOver (Spec R))
        (Spec.map <| CommRingCat.ofHom <| Bialgebra.counitAlgHom R A)
          (by simp [specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) := rfl

set_option backward.isDefEq.respectTransparency false in
lemma specOverSpec_one_left [Bialgebra R A] :
    η[(Spec A).asOver (Spec R)].left =
      (Spec.map <| CommRingCat.ofHom <| Bialgebra.counitAlgHom R A) := by simp

lemma μIso_algSpec_inv_left [Algebra R A] :
    (μIso (algSpec R) (op (.of R A)) (op (.of R A))).inv.left = (pullbackSpecIso R A A).inv := rfl

-- Arguably, this should be defeq.
lemma μ_algSpec_left [Algebra R A] :
    (LaxMonoidal.μ (algSpec R) (op (.of R A)) (op (.of R A))).left =
      (pullbackSpecIso R A A).hom := by
  rw [← Iso.comp_inv_eq_id, ← μIso_algSpec_inv_left, ← Over.comp_left, Monoidal.μIso_inv,
    Monoidal.μ_δ, Over.id_left]

lemma mul_left [Bialgebra R A] :
    μ[(Spec A).asOver (Spec R)].left =
      (pullbackSpecIso R A A).hom ≫ Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R A)) := by
  rw [← μ_algSpec_left]; rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance asOver.instIsCommMonObj [Bialgebra R A] [IsCocomm R A] :
    IsCommMonObj ((Spec A).asOver (Spec R)) where
  mul_comm := by
    ext
    have := LaxMonoidal.μ (algSpec R) (.op <| .of R A) (.op <| .of R A)
    have := congr((pullbackSpecIso R A A).hom ≫ ((bialgSpec R).map <| .op <| CommBialgCat.ofHom <|
      $(Bialgebra.comm_comp_comulBialgHom (R := R) (A := A))).hom.left)
    dsimp [commBialgCatEquivComonCommAlgCat] at this ⊢
    have h₁ : (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A) =
      (RingHomClass.toRingHom (Bialgebra.TensorProduct.comm R A A)).comp
        Algebra.TensorProduct.includeLeftRingHom := by ext; rfl
    have h₂ : (Algebra.TensorProduct.includeLeftRingHom) =
      (RingHomClass.toRingHom (Bialgebra.TensorProduct.comm R A A)).comp
       (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A) := by ext; rfl
    convert! this using 1
    · simp only [Spec.map_comp, ← Category.assoc, mul_left]
      congr 1
      rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
      ext
      · simp [AlgHom.toUnder, specOverSpec, over, OverClass.hom, h₁]; rfl
      · simp [AlgHom.toUnder, specOverSpec, over, OverClass.hom, h₂]; rfl
    · exact mul_left ..

instance asOver.instGrpObj [HopfAlgebra R A] : GrpObj ((Spec A).asOver (Spec R)) :=
  ((hopfSpec R).obj <| .op <| .of R A).grp

set_option backward.isDefEq.respectTransparency false in
instance asOver.instCommGrpObj [HopfAlgebra R A] [IsCocomm R A] :
    CommGrpObj ((Spec A).asOver (Spec R)) where

instance {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) : (Spec.map (CommRingCat.ofHom f.toRingHom)).IsOver Spec(R) where
  comp_over := by simp [specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

-- TODO: Fix in mathlib
set_option allowUnsafeReducibility true in
attribute [implicit_reducible] OverClass.asOver

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `Spec.map` as a `MulEquiv` on hom-sets. -/
def Spec.mapMulEquiv {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Bialgebra R S]
    [Algebra R T] :
    WithConv (S →ₐ[R] T) ≃* (Spec(T).asOver Spec(R) ⟶ Spec(S).asOver Spec(R)) where
  toFun f := (Spec.map (CommRingCat.ofHom f.ofConv.toRingHom)).asOver _
  invFun f := ⟨(Spec.preimage f.left).hom, by
    suffices CommRingCat.ofHom (algebraMap R S) ≫ Spec.preimage f.left =
      CommRingCat.ofHom (algebraMap R T) from fun r ↦ congr($this r)
    apply Spec.map_injective
    simpa [-comp_over] using! f.w⟩
  left_inv f := by
    apply WithConv.ofConv_injective
    apply AlgHom.coe_ringHom_injective
    simp
  right_inv f := by ext1; simp
  map_mul' f g := by
    ext1
    dsimp [AlgHom.convMul_def, AlgHom.comp_toRingHom, Hom.mul_def]
    simp only [← Category.assoc, Spec.map_comp, AlgebraicGeometry.Scheme.mul_left]
    congr 1
    rw [← Iso.comp_inv_eq]
    ext <;> simp only [specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← AlgHom.comp_toRingHom, Category.assoc, pullbackSpecIso_inv_fst, pullbackSpecIso_inv_snd,
      limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
    · congr 3
      ext; simp
    · congr 3
      ext; simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The adjunction between `Spec` and `Γ` as functors between commutative `R`-algebras and
schemes over `Spec R`. -/
def algΓAlgSpecAdjunction (R : CommRingCat) : algΓ R ⊣ algSpec R := by
  have overAdjunction := Over.postAdjunctionRight (Y := .op <| R) ΓSpec.adjunction
  have overEquivAlg := ((Over.opEquivOpUnder R).trans (commAlgCatEquivUnder R).op.symm).toAdjunction
  simpa using! overAdjunction.comp overEquivAlg

end universe_polymorphic

section universe_monomorphic
variable {R A : CommRingCat.{u}} {X M G : Scheme.{u}}

/-- The global sections of an affine scheme over `Spec R` are a `R`-algebra. -/
instance [X.Over (Spec R)] [IsAffine X] : Algebra R Γ(X, ⊤) :=
  ((commAlgCatEquivUnder R).inverse.obj <|
    .mk (Spec.fullyFaithful.preimage <| X.isoSpec.inv ≫ X ↘ Spec R).unop).algebra

lemma algebraMap_Γ [X.Over (Spec R)] [IsAffine X] :
    algebraMap R Γ(X, ⊤) = (Spec.fullyFaithful.preimage <| X.isoSpec.inv ≫ X ↘ Spec R).unop.hom :=
  rfl

attribute [local simp] specOverSpec_over algebraMap_Γ in
instance [X.Over (Spec R)] [IsAffine X] : X.isoSpec.inv.IsOver (Spec R) where

/-- The global sections of an affine monoid scheme over `Spec R` are a `R`-bialgebra. -/
instance [M.Over (Spec R)] [MonObj (M.asOver (Spec R))] [IsAffine M] :
    Bialgebra R Γ(M, ⊤) := by
  have : MonObj ((algSpec R).obj <| .op <| CommAlgCat.of R Γ(M, ⊤)) :=
    .ofIso <| M.isoSpec.asOver (Spec R)
  have : MonObj (op <| CommAlgCat.of R Γ(M, ⊤)) := algSpec.fullyFaithful.monObj _
  exact ((commBialgCatEquivComonCommAlgCat R).inverse.obj <|
    .op <| .mk <| .op <| .of R Γ(M, ⊤)).bialgebra

/-- The global sections of an affine group scheme over `Spec R` are a `R`-Hopf algebra. -/
instance [G.Over (Spec R)] [GrpObj (G.asOver (Spec R))] [IsAffine G] :
    HopfAlgebra R Γ(G, ⊤) := by
  have : GrpObj ((algSpec R).obj <| .op <| CommAlgCat.of R Γ(G, ⊤)) :=
    .ofIso <| G.isoSpec.asOver (Spec R)
  have : GrpObj (op <| CommAlgCat.of R Γ(G, ⊤)) := algSpec.fullyFaithful.grpObj _
  exact ((commHopfAlgCatEquivCogrpCommAlgCat R).inverse.obj <|
    .op <| .mk <| .op <| .of R Γ(G, ⊤)).hopfAlgebra

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]

open TensorProduct Algebra.TensorProduct CommRingCat RingHomClass

variable (R S T) in
/-- The isomorphism between the fiber product of two schemes `Spec S` and `Spec T`
over a scheme `Spec R` and the `Spec` of the tensor product `S ⊗[R] T`. -/
def pullbackSpecIso' [Algebra R T] :
    pullback (Spec(S) ↘ Spec(R)) (Spec(T) ↘ Spec(R)) ≅ Spec (.of <| S ⊗[R] T) := pullbackSpecIso ..

set_option backward.defeqAttrib.useBackward true in
lemma pullbackSpecIso'_symmetry [Algebra R T] :
    (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom =
      (pullbackSpecIso' ..).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.comm R S T)) := by
  simp_rw [Iso.trans_hom, ← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
  ext
  · have : (RingHomClass.toRingHom (Algebra.TensorProduct.comm R S T)).comp
      Algebra.TensorProduct.includeLeftRingHom = Algebra.TensorProduct.includeRight.toRingHom := rfl
    simp [specOverSpec_over, pullbackSpecIso', ← Spec.map_comp, ← CommRingCat.ofHom_comp, this]
  have : (RingHomClass.toRingHom (Algebra.TensorProduct.comm R S T)).comp
      (RingHomClass.toRingHom Algebra.TensorProduct.includeRight) =
      Algebra.TensorProduct.includeLeftRingHom := rfl
  simp [specOverSpec_over, pullbackSpecIso', ← Spec.map_comp, ← CommRingCat.ofHom_comp, this]

set_option backward.defeqAttrib.useBackward true in
instance [Algebra R T] : (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.IsOver Spec(S) where
  comp_over := by
    rw [← cancel_epi (pullbackSymmetry .. ≪≫ pullbackSpecIso' ..).inv,
      Scheme.canonicallyOverPullback_over]
    simp [specOverSpec_over, pullbackSpecIso']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in
variable (R S T) in
lemma μ_pullback_left_fst [Algebra R T] :
    (LaxMonoidal.μ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))))
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R T))))
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R T))))).left ≫
        pullback.fst _ _ =
    (((pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.asOver Spec(S) ⊗ₘ
        ((pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.asOver Spec(S))).left) ≫
          (pullbackSpecIso S (S ⊗[R] T) (S ⊗[R] T)).hom ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.mapRingHom (algebraMap _ _)
              Algebra.TensorProduct.includeRight.toRingHom
              Algebra.TensorProduct.includeRight.toRingHom
              (by simp [← IsScalarTower.algebraMap_eq])
              (by simp [← IsScalarTower.algebraMap_eq]))) ≫ (pullbackSpecIso R T T).inv := by
  simp
  ext <;> simp
  · simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Algebra.TensorProduct.mapRingHom_comp_includeLeftRingHom]
    simp [specOverSpec_over]
    erw [Over.tensorHom_left_fst_assoc]
    simp [pullbackSpecIso']
    rfl
  · simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Algebra.TensorProduct.mapRingHom_comp_includeRight]
    simp [specOverSpec_over]
    erw [Over.tensorHom_left_snd_assoc]
    simp [pullbackSpecIso']
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance [Bialgebra R T] :
    IsMonHom <| (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.asOver Spec(S) where
  one_hom := by
    ext
    rw [← cancel_mono (pullbackSpecIso' ..).inv]
    ext
    · simp [Scheme.monObjAsOverPullback_one, algSpec_ε_left (R := CommRingCat.of _),
        pullbackSpecIso', specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        Bialgebra.TensorProduct.counitAlgHom_def, AlgHom.comp_toRingHom, RingHom.comp_assoc]
    · simp [Scheme.monObjAsOverPullback_one, algSpec_ε_left (R := CommRingCat.of _),
        pullbackSpecIso', specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← AlgHom.coe_restrictScalars R (Bialgebra.counitAlgHom S _), - AlgHom.coe_restrictScalars,
        ← AlgHom.comp_toRingHom, Bialgebra.counitAlgHom_comp_includeRight]
      rfl
  mul_hom := by
    ext
    rw [← cancel_mono (pullbackSpecIso' ..).inv]
    ext
    · have : includeLeftRingHom = algebraMap S (S ⊗[R] T) := rfl
      simp [Scheme.monObjAsOverPullback_mul, pullbackSpecIso', specOverSpec_over, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, OverClass.asOver, Scheme.mul_left, this, Hom.asOver,
        OverClass.asOverHom, pullback.condition]
      rfl
    · convert! congr($(μ_pullback_left_fst R S T) ≫ (pullbackSpecIso R T T).hom ≫
        Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R T).toRingHom)) using 1
      · simp [Scheme.monObjAsOverPullback_mul, pullbackSpecIso', specOverSpec_over,
          OverClass.asOver, Hom.asOver, OverClass.asOverHom, mul_left]
      · simp [pullbackSpecIso', specOverSpec_over, OverClass.asOver, Hom.asOver, ← Spec.map_comp,
          OverClass.asOverHom, mul_left, ← CommRingCat.ofHom_comp, ← Bialgebra.comul_includeRight]

end universe_monomorphic
end Scheme
end topEdge

/-!
### Right edge: The essential image of `Spec` on Hopf algebras

In this section we show that the essential image of `R`-Hopf algebras under `Spec` is precisely
affine group schemes over `Spec R`.
-/

section rightEdge

set_option backward.isDefEq.respectTransparency false in
/-- The essential image of `R`-algebras under `Spec` is precisely affine schemes over `Spec R`. -/
@[simp]
lemma essImage_algSpec {G : Over <| Spec R} : (algSpec R).essImage G ↔ IsAffine G.left := by
  simp [algSpec, Functor.essImage_overPost (F := Scheme.Spec)]

/-- The essential image of `R`-bialgebras under `Spec` is precisely affine monoid schemes over
`Spec R`. -/
@[simp]
lemma essImage_bialgSpec {G : Mon <| Over <| Spec R} :
    (bialgSpec R).essImage G ↔ IsAffine G.X.left := by simp

/-- The essential image of `R`-Hopf algebras under `Spec` is precisely affine group schemes over
`Spec R`. -/
@[simp]
lemma essImage_hopfSpec {G : Grp <| Over <| Spec R} :
    (hopfSpec R).essImage G ↔ IsAffine G.X.left := by simp

end rightEdge

end AlgebraicGeometry
