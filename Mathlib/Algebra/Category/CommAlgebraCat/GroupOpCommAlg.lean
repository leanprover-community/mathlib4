import Mathlib.Algebra.Category.CommAlgebraCat.Basic
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.GroupObjects.PreservesFiniteProducts
universe v u w u' v' w'

open CategoryTheory

variable {R : Type u} [CommRing R]

def commRingIsoToCommAlgebraIso {X Y : CommAlgebraCat R} (f : CommRingCat.of X ≅ CommRingCat.of Y)
    (hf : ∀ r, f.hom (algebraMap R X r) = algebraMap R Y r) : X ≅ Y :=
  AlgEquiv.toCommAlgebraIso {
    f.commRingCatIsoToRingEquiv with
    commutes' := hf }

variable (R)

@[simps]
def CommAlgebraCat.toUnderCommRingCat : CommAlgebraCat R ⥤ Under (CommRingCat.of R) :=
  { obj := fun A => Under.mk (CommRingCat.ofHom (algebraMap R A))
    map := fun f => Under.homMk (CommRingCat.ofHom f.toAlgHom)
      (by ext; exact f.toAlgHom.commutes _) }

@[simps! obj map_toAlgHom_toRingHom]
def CommRingCat.underToCommAlgebraCat : Under (CommRingCat.of R) ⥤ CommAlgebraCat R :=
  { obj := fun A =>
      let I : Algebra R A.right := RingHom.toAlgebra A.hom
      CommAlgebraCat.of R A.right
    map := fun f =>
      { toAlgHom := {
        toRingHom := f.right
        commutes' := fun r => (RingHom.congr_fun f.3 r).symm }}}

@[simps]
def commAlgebraCatUnderEquivalence : CommAlgebraCat R ≌ Under (CommRingCat.of R) where
  functor := CommAlgebraCat.toUnderCommRingCat R
  inverse := CommRingCat.underToCommAlgebraCat R
  unitIso := NatIso.ofComponents
    (fun _ => commRingIsoToCommAlgebraIso (Iso.refl _) fun r => by rfl) fun _ => rfl
  counitIso := NatIso.ofComponents (fun _ => Under.isoMk (Iso.refl _) (by ext; rfl)) fun _ => rfl
  functor_unitIso_comp := fun _ => by ext; rfl

def opOverUnderOpEquivalence {C : Type*} [Category C] {X : C} :
    (Over X)ᵒᵖ ≌ Under (Opposite.op X) :=
  costructuredArrowOpEquivalence _ _

def opUnderOverOpEquivalence {C : Type*} [Category C] (X : C) :
    (Under X)ᵒᵖ ≌ Over (Opposite.op X) :=
  structuredArrowOpEquivalence _ _
open Limits AlgebraicGeometry

instance : HasCoequalizers (CommAlgebraCat R) :=
  Adjunction.hasColimitsOfShape_of_equivalence (commAlgebraCatUnderEquivalence R).functor

attribute [local instance] Under.ConstructCoproducts.under_coproducts_of_widePushouts in
instance : HasCoproducts (CommAlgebraCat R) :=
  fun _ => Adjunction.hasColimitsOfShape_of_equivalence
    (commAlgebraCatUnderEquivalence R).functor

instance : HasColimits (CommAlgebraCat R) :=
  has_colimits_of_hasCoequalizers_and_coproducts

open Limits AlgebraicGeometry

noncomputable def opCommAlgebraCatToSchemeOver :
    (CommAlgebraCat R)ᵒᵖ ⥤ Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of R))) :=
  ((commAlgebraCatUnderEquivalence R).op.trans
    (opUnderOverOpEquivalence (CommRingCat.of R))).functor ⋙ Over.post Scheme.Spec

noncomputable def opCommAlgebraCatAffineSchemeOverEquivalence :
    (CommAlgebraCat R)ᵒᵖ ≌ Over (AffineScheme.Spec.obj (Opposite.op (CommRingCat.of R))) :=
  ((commAlgebraCatUnderEquivalence R).op.trans
    (opUnderOverOpEquivalence (CommRingCat.of R))).trans
    (Over.postEquivalence AffineScheme.equivCommRingCat.symm)

noncomputable instance :
    PreservesLimits (Over.post (X := Opposite.op (CommRingCat.of R)) Scheme.Spec) :=
  Over.postPreservesLimits _ (B := Opposite.op (CommRingCat.of R))

noncomputable instance : PreservesLimits (opCommAlgebraCatToSchemeOver R) :=
  compPreservesLimits _ _

attribute [local instance] hasFiniteProducts_of_has_binary_and_terminal Over.over_hasTerminal
  Over.ConstructProducts.over_binaryProduct_of_pullback in
noncomputable def yay : GroupObject ((CommAlgebraCat R)ᵒᵖ)
    ⥤ GroupObject (Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of R)))) :=
  (opCommAlgebraCatToSchemeOver R).mapGroupObject
