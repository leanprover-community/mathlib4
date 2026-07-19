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

We want to show that affine group schemes correspond to Hopf algebras. This can easily be done
categorically assuming both categories on either side are defined thoughtfully. However, the
categorical version will not be workable with if we do not also have links to the non-categorical
notions. Therefore, one solution would be to build the left, top and right edges of the following
diagram so that the bottom edge can be obtained by composing the three.

```
  Cogrp Mod_R ≌ Grp AffSch_{Spec R} ≌ Aff Grp Sch_{Spec R}
      ↑ ↓                                      ↑ ↓
R-Hopf algebras         ⇄       Affine group schemes over Spec R
```

If we do not care about going back from affine group schemes over `Spec R` to `R`-Hopf algebras
(e.g. because all our affine group schemes are given as the `Spec` of some algebra), then we can
follow the following simpler diagram:

```
  Cogrp Mod_R   ⥤        Grp Sch_{Spec R}
      ↑ ↓                        ↓
R-Hopf algebras → Affine group schemes over Spec R
```
where the top `⥤` comes from the essentially surjective functor `Cogrp Mod_R ⥤ Grp Sch_{Spec R}`,
so that in particular we do not easily know that its inverse is given by `Γ`.
-/

@[expose] public section

suppress_compilation

open AlgebraicGeometry Coalgebra Scheme CategoryTheory MonoidalCategory CartesianMonoidalCategory
  Functor Monoidal Opposite TensorProduct MonObj GrpObj
open Limits hiding prodComparison

universe w v u
variable {R : CommRingCat.{u}}

/-!
### Left edge: `R`-Hopf algebras correspond to cogroup objects under `R`

Ways to turn an unbundled `R`-Hopf algebra into a bundled cogroup object under `R`, and vice versa,
are already provided in `Mathlib.Algebra.Category.CommHopfAlgCat`.

### Top edge: `Spec` as a functor on Hopf algebras

In this section we bundle `Spec` as a functor from `R`-Hopf algebras to affine group schemes over
`Spec R`.
-/

namespace AlgebraicGeometry

section topEdge

variable (R) in
/-- `Spec` as a functor from `R`-algebras to schemes over `Spec R`. -/
@[implicit_reducible] def algSpec : (CommAlgCat R)ᵒᵖ ⥤ Over (Spec R) :=
  (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

variable (R) in
/-- The Gamma functor as a functor from schemes over `Spec R` to `R`-algebras. -/
@[implicit_reducible] def algΓ : Over (Spec R) ⥤ (CommAlgCat R)ᵒᵖ :=
  Over.post Γ.rightOp ⋙ Over.map (ΓSpecIso R).inv.op ⋙
    (Over.opEquivOpUnder R).functor ⋙ (commAlgCatEquivUnder R).inverse.op

instance preservesLimitsOfSize_algSpec : PreservesLimitsOfSize.{w, v} (algSpec R) :=
  inferInstanceAs <| PreservesLimitsOfSize.{w, v} <|
    (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

set_option backward.isDefEq.respectTransparency false in
instance preservesColimitsOfSize_algΓ : PreservesColimitsOfSize.{w, v} (algΓ R) := by
  unfold algΓ; infer_instance

@[simp] lemma algSpec_obj_hom (X : (CommAlgCat R)ᵒᵖ) :
    ((algSpec R).obj X).hom = Spec.map (CommRingCat.ofHom (algebraMap R X.unop)) := rfl

@[simp] lemma algSpec_map_left {X Y : (CommAlgCat R)ᵒᵖ} (f : X ⟶ Y) :
    ((algSpec R).map f).left = Spec.map ((commAlgCatEquivUnder R).functor.map f.unop).right := rfl

lemma preservesTerminalIso_algSpec :
    preservesTerminalIso (algSpec R) = Over.isoMk (.refl (Spec R)) := by
  ext : 1; exact toUnit_unique ..

@[simp] lemma preservesTerminalIso_algSpec_inv_left :
    (preservesTerminalIso (algSpec R)).inv.left = 𝟙 (Spec R) := by
  rw [preservesTerminalIso_algSpec]; rfl

@[simp]
lemma prodComparison_algSpec_left (X Y : (CommAlgCat R)ᵒᵖ) :
    (prodComparison (algSpec R) X Y).left = (pullbackSpecIso R X.unop Y.unop).inv := rfl

@[simp]
lemma prodComparisonIso_algSpec_inv_left (X Y : (CommAlgCat R)ᵒᵖ) :
    (prodComparisonIso (algSpec R) X Y).inv.left = (pullbackSpecIso R X.unop Y.unop).hom := by
  have : (Over.forget (Spec R)).mapIso (prodComparisonIso (algSpec R) X Y) =
      (pullbackSpecIso R X.unop Y.unop).symm :=
    Iso.ext (prodComparison_algSpec_left X Y)
  exact congrArg Iso.inv this

attribute [local simp] ε_of_cartesianMonoidalCategory μ_of_cartesianMonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
/-- `Spec` as a functor from `R`-algebras to schemes over `Spec R` is braided.

The monoidal data is copied from `Functor.Braided.ofChosenFiniteProducts` so that `ε`, `η` are
definitionally `𝟙 (Spec R)` and `μ`, `δ` are definitionally `pullbackSpecIso`. -/
instance braidedAlgSpec : (algSpec R).Braided :=
  .copy (.ofChosenFiniteProducts _)
    (Over.homMk <| 𝟙 <| Spec R)
    (fun X Y ↦ Over.homMk (pullbackSpecIso R X.unop Y.unop).hom)
    (Over.homMk <| 𝟙 <| Spec R)
    (fun X Y ↦ Over.homMk (pullbackSpecIso R X.unop Y.unop).inv <| by
      simpa using Over.w (prodComparison (algSpec R) X Y))
    (Over.OverMorphism.ext (by simp))
    (funext fun X ↦ funext fun Y ↦ Over.OverMorphism.ext (by simp))
    (Over.OverMorphism.ext (by
      rw [Functor.OplaxMonoidal.η_of_cartesianMonoidalCategory, ← preservesTerminalIso_hom,
        preservesTerminalIso_algSpec]; rfl))
    (funext fun X ↦ funext fun Y ↦ Over.OverMorphism.ext (by
      rw [Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory, prodComparison_algSpec_left]; rfl))

@[simp] lemma ε_algSpec_left : (LaxMonoidal.ε (algSpec R)).left = 𝟙 (Spec R) := rfl
@[simp] lemma η_algSpec_left : (OplaxMonoidal.η (algSpec R)).left = 𝟙 (Spec R) := rfl

@[simp] lemma δ_algSpec_left (X Y : (CommAlgCat R)ᵒᵖ) :
    (OplaxMonoidal.δ (algSpec R) X Y).left = (pullbackSpecIso R X.unop Y.unop).inv := rfl

@[simp] lemma μ_algSpec_left (X Y : (CommAlgCat R)ᵒᵖ) :
    (LaxMonoidal.μ (algSpec R) X Y).left = (pullbackSpecIso R X.unop Y.unop).hom := rfl

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
  (commBialgCatEquivComonCommAlgCat R).fullyFaithfulFunctor.leftOp.comp algSpec.fullyFaithful.mapMon

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

section universe_polymorphic
variable {R A : CommRingCat.{u}}

-- Note that this creates a diamond with `instOverClass`. We keep it for convenience.
-- Once `OverClass` is refactored (see https://github.com/leanprover-community/mathlib4/pull/41542),
-- the diamond will be downgraded to the invariant about the `outParam` argument of `OverClass`
-- being determined by the first two arguments being broken.
@[simps -isSimp]
instance specOverSpec [Algebra R A] : (Spec A).Over (Spec R) where
  hom := Spec.map <| CommRingCat.ofHom <| algebraMap ..

instance locallyOfFiniteType_specOverSpec [Algebra R A] [Algebra.FiniteType R A] :
    LocallyOfFiniteType (Spec A ↘ Spec R) := by
  rw [specOverSpec_over, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  simpa [RingHom.finiteType_algebraMap]

attribute [local simp] AlgHom.toUnder in
@[simps! one]
instance instMonObjSpecAsOverSpec [Bialgebra R A] : MonObj ((Spec A).asOver (Spec R)) :=
  ((bialgSpec R).obj <| .op <| .of R A).mon

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma one_spec_asOver_spec [Bialgebra R A] :
    η[(Spec A).asOver (Spec R)] = LaxMonoidal.ε (algSpec R) ≫
      Over.homMk (V := (Spec A).asOver (Spec R))
        (Spec.map <| CommRingCat.ofHom <| Bialgebra.counitAlgHom R A)
          (by simp [specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            CommRingCat.of_carrier]) := rfl

lemma one_spec_asOver_spec_left [Bialgebra R A] :
    η[(Spec A).asOver (Spec R)].left =
      (Spec.map <| CommRingCat.ofHom <| Bialgebra.counitAlgHom R A) := rfl

lemma mul_spec_asOver_spec_left [Bialgebra R A] :
    μ[(Spec A).asOver (Spec R)].left =
      (pullbackSpecIso R A A).hom ≫ Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R A)) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance isCommMonObj_spec_asOver_spec [Bialgebra R A] [IsCocomm R A] :
    IsCommMonObj ((Spec A).asOver (Spec R)) where
  mul_comm := by
    ext
    have := congr((pullbackSpecIso R A A).hom ≫ ((bialgSpec R).map <| .op <| CommBialgCat.ofHom <|
      $(Bialgebra.comm_comp_comulBialgHom (R := R) (A := A))).hom.left)
    dsimp [commBialgCatEquivComonCommAlgCat] at this ⊢
    have h₁ : (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A) =
      (RingHomClass.toRingHom (Bialgebra.TensorProduct.comm R A A)).comp
        Algebra.TensorProduct.includeLeftRingHom := rfl
    have h₂ : (Algebra.TensorProduct.includeLeftRingHom) =
      (RingHomClass.toRingHom (Bialgebra.TensorProduct.comm R A A)).comp
       (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A) := rfl
    convert! this using 1
    simp only [mul_spec_asOver_spec_left, ← Category.assoc, algSpec, Equivalence.op_functor,
      comp_obj, op_obj, commAlgCatEquivUnder_functor_obj, Over.opEquivOpUnder_inverse_obj,
      CommRingCat.mkUnder_hom, Over.post_obj, Spec_obj, Over.mk_left, Over.mk_hom, Spec_map,
      Quiver.Hom.unop_op, Spec.map_comp]
    congr 1
    rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
    ext
    · simp [AlgHom.toUnder, specOverSpec, over, OverClass.hom, h₁]; rfl
    · simp [AlgHom.toUnder, specOverSpec, over, OverClass.hom, h₂]; rfl

instance instGrpObjSpecAsOverSpec [HopfAlgebra R A] : GrpObj ((Spec A).asOver (Spec R)) where
  __ := instMonObjSpecAsOverSpec
  __ := ((hopfSpec R).obj <| .op <| .of R A).grp

instance instCommGrpObjSpecAsOverSpec [HopfAlgebra R A] [IsCocomm R A] :
    CommGrpObj ((Spec A).asOver (Spec R)) where

instance {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) : (Spec.map (CommRingCat.ofHom f.toRingHom)).IsOver (Spec (.of R)) where
  comp_over := by simp [specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `Spec.map` as a `MulEquiv` on hom-sets. -/
def Spec.mapMulEquiv {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Bialgebra R S]
    [Algebra R T] :
    WithConv (S →ₐ[R] T) ≃*
      ((Spec (.of T)).asOver (Spec (.of R)) ⟶ (Spec (.of S)).asOver (Spec (.of R))) where
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
    simp only [← Category.assoc, Spec.map_comp, mul_spec_asOver_spec_left]
    congr 1
    rw [← Iso.comp_inv_eq]
    ext
    all_goals
    · simp only [specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← AlgHom.comp_toRingHom, Category.assoc, pullbackSpecIso_inv_fst, pullbackSpecIso_inv_snd,
      limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
      congr 3
      ext; simp

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

lemma algebraMap_presheafObj [X.Over (Spec R)] [IsAffine X] :
    algebraMap R Γ(X, ⊤) = (Spec.fullyFaithful.preimage <| X.isoSpec.inv ≫ X ↘ Spec R).unop.hom :=
  rfl

attribute [local simp] specOverSpec_over algebraMap_presheafObj in
attribute [-simp] Hom.isOver_iff in
instance [X.Over (Spec R)] [IsAffine X] : X.toSpecΓ.IsOver (Spec R) where

instance [X.Over (Spec R)] [IsAffine X] : X.isoSpec.hom.IsOver (Spec R) :=
  inferInstanceAs (X.toSpecΓ.IsOver (Spec R))

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
over a scheme `Spec R` and the `Spec` of the tensor product `S ⊗[R] T`.

This is a version of `pullbackSpecIso` stated in terms of `specOverSpec`.
TODO: Unify with `pullbackSpecIso` once `OverClass` is refactored to not bundle the morphism. -/
def pullbackSpecIso' [Algebra R T] :
    pullback (Spec (.of S) ↘ Spec (.of R)) (Spec (.of T) ↘ Spec (.of R)) ≅
      Spec (.of <| S ⊗[R] T) := pullbackSpecIso ..

set_option backward.defeqAttrib.useBackward true in
lemma pullbackSpecIso'_symmetry [Algebra R T] :
    (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom =
      (pullbackSpecIso' ..).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.comm R S T)) := by
  simp_rw [Iso.trans_hom, ← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
  ext
  · have : (RingHomClass.toRingHom (Algebra.TensorProduct.comm R S T)).comp
      Algebra.TensorProduct.includeLeftRingHom =
      RingHomClass.toRingHom Algebra.TensorProduct.includeRight := rfl
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
    simp only [pullbackSpecIso', specOverSpec_over, pullbackSpecIso_inv_snd, Category.assoc,
      pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp, this]
  have : (RingHomClass.toRingHom (Algebra.TensorProduct.comm R S T)).comp
      (RingHomClass.toRingHom Algebra.TensorProduct.includeRight) =
      Algebra.TensorProduct.includeLeftRingHom := rfl
  rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
  simp only [pullbackSpecIso', specOverSpec_over, pullbackSpecIso_inv_fst, Category.assoc,
    pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, this]

set_option backward.defeqAttrib.useBackward true in
instance [Algebra R T] :
    (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.IsOver (Spec (.of S)) where
  comp_over := by
    rw [← cancel_epi (pullbackSymmetry .. ≪≫ pullbackSpecIso' ..).inv,
      Scheme.canonicallyOverPullback_over, Iso.inv_hom_id_assoc, Iso.trans_inv, Category.assoc,
      pullbackSymmetry_inv_comp_snd]
    exact (pullbackSpecIso_inv_fst ..).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in
-- The `simp` calls are non-terminal merely because the `erw` calls are necessary.
-- If this proof breaks because of a non-terminal `simp` in the future, it is likely that one can
-- simply remove the following `erw`.
variable (R S T) in
lemma μ_pullback_left_fst [Algebra R T] :
    (LaxMonoidal.μ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))))
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R T))))
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R T))))).left ≫
        pullback.fst _ _ =
    (((pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.asOver (Spec (.of S)) ⊗ₘ
        ((pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.asOver (Spec (.of S)))).left) ≫
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
    IsMonHom <| (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.asOver (Spec (.of S)) where
  one_hom := by
    ext
    rw [← cancel_mono (pullbackSpecIso' ..).inv]
    ext
    · simp [Scheme.monObjAsOverPullback_one, ε_algSpec_left (R := CommRingCat.of _),
        pullbackSpecIso', specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        AlgHom.toUnder, Under.homMk_right, Bialgebra.TensorProduct.counitAlgHom_def,
        AlgHom.comp_toRingHom, RingHom.comp_assoc]
    · simp [Scheme.monObjAsOverPullback_one, ε_algSpec_left (R := CommRingCat.of _),
        pullbackSpecIso', specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        AlgHom.toUnder, Under.homMk_right,
        ← AlgHom.coe_restrictScalars R (Bialgebra.counitAlgHom S _), -AlgHom.coe_restrictScalars,
        ← AlgHom.comp_toRingHom, Bialgebra.counitAlgHom_comp_includeRight]
      simp [AlgHom.comp_toRingHom, Algebra.toRingHom_ofId]
  mul_hom := by
    ext
    rw [← cancel_mono (pullbackSpecIso' ..).inv]
    ext
    · have : includeLeftRingHom = algebraMap S (S ⊗[R] T) := rfl
      simp [Scheme.monObjAsOverPullback_mul, pullbackSpecIso', specOverSpec_over, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, OverClass.asOver, mul_spec_asOver_spec_left, this, Hom.asOver,
        OverClass.asOverHom, pullback.condition]
      rfl
    · convert! congr($(μ_pullback_left_fst R S T) ≫ (pullbackSpecIso R T T).hom ≫
        Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R T).toRingHom)) using 1
      · simp [Scheme.monObjAsOverPullback_mul, pullbackSpecIso', specOverSpec_over,
          OverClass.asOver, Hom.asOver, OverClass.asOverHom, mul_spec_asOver_spec_left]
      · simp [pullbackSpecIso', specOverSpec_over, OverClass.asOver, Hom.asOver, ← Spec.map_comp,
          OverClass.asOverHom, mul_spec_asOver_spec_left, ← CommRingCat.ofHom_comp,
          ← Bialgebra.comul_includeRight]

end universe_monomorphic
end topEdge

/-!
### Right edge: The essential image of `Spec` on Hopf algebras

In this section we show that the essential image of `R`-Hopf algebras under `Spec` is precisely
affine group schemes over `Spec R`.
-/

section rightEdge

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
