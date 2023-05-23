import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Finiteness
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.Algebra.DirectSum.Module
--import Mathlib.CategoryTheory.Preadditive.Projective


open CategoryTheory Limits


namespace CategoryTheory

section

variable (C : Type _) [Category C] [HasFiniteCoproducts C] (sk : Skeletal C)

noncomputable
def Skeletal.CommMonoid : CommMonoid C where
  mul X Y := X ⨿ Y
  mul_assoc _ _ _ := sk <| ⟨coprod.associator _ _ _⟩
  mul_comm _ _  := sk <| ⟨coprod.braiding _ _⟩
  one := ⊥_ _
  one_mul _ := sk <| ⟨coprod.leftUnitor _⟩
  mul_one _ := sk <| ⟨coprod.rightUnitor _⟩
  npow_zero _ := rfl
  npow_succ _ _ := rfl

end

section

variable (C : Type _) [Category C] [HasFiniteCoproducts C]

noncomputable
instance CommMonoid : CommMonoid (Skeleton C) :=
  haveI : HasFiniteCoproducts (Skeleton C) := ⟨fun n =>
    hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
    (skeletonEquivalence _).functor⟩
  Skeletal.CommMonoid _ (by exact skeleton_skeletal C)

end

end CategoryTheory

namespace ModuleCat

variable (R : Type _) [Ring R]

def ProjFG := FullSubcategory fun (M : ModuleCat R) => Module.Finite R M ∧ Projective M

instance : Category (ProjFG R) :=
  show Category (FullSubcategory _) from inferInstance

def ProjFG.inclusion : ProjFG R ⥤ ModuleCat R :=
  fullSubcategoryInclusion _

def finite_of_iso (A B : ModuleCat R) (e : A ≅ B) (_ : Module.Finite R A) :
    Module.Finite R B :=
  let e : A ≃ₗ[R] B := Iso.toLinearEquiv e
  Module.Finite.of_surjective e.toLinearMap e.surjective

def directSumCocone (n : ℕ) (K : Discrete (Fin n) ⥤ ModuleCat R) : Cocone K where
  pt := ModuleCat.of R <| DirectSum (Discrete (Fin n)) <| fun i => K.obj i
  ι := Discrete.natTrans <| fun j => DirectSum.lof R (Discrete (Fin n)) (fun i => K.obj i) j

def productCocone (n : ℕ) (K : Discrete (Fin n) ⥤ ModuleCat R) : Cocone K where
  pt := ModuleCat.of R <| (i : Discrete (Fin n)) → K.obj i
  ι := Discrete.natTrans <| fun j =>
      LinearMap.single (φ := fun (i : Discrete (Fin n)) => K.obj i) j

def isColimitProductCocone (n : ℕ) (K : Discrete (Fin n) ⥤ ModuleCat R) :
  IsColimit (productCocone R n K) where
    desc := fun S => (LinearMap.lsum R (fun i => K.obj i) ℤ) S.ι.app
    fac := fun S j => by
      ext t
      dsimp only [productCocone, Functor.const_obj_obj, Discrete.natTrans_app, coe_comp,
        Function.comp_apply]
      sorry
    uniq := sorry

lemma proj_and_fg_of_isColimit (n : ℕ) (K : Discrete (Fin n) ⥤ ProjFG R)
    (S: Cocone (K ⋙ ProjFG.inclusion R)) (hS: IsColimit S) :
    Module.Finite R S.pt ∧ Projective S.pt := by
  constructor
  · let w : S.pt ≅ (productCocone _ n (K ⋙ ProjFG.inclusion R)).pt :=
      hS.coconePointUniqueUpToIso (isColimitProductCocone _ _ _)
    apply finite_of_iso (e := w.symm)
    have : ∀ (i : Discrete (Fin n)), Module.Finite R ((K ⋙ ProjFG.inclusion R).obj i) := by
      intro i
      exact (K.obj i).2.1
    apply Module.Finite.pi
  · constructor
    -- TODO: This works more generally for arbitrary coproducts of
    -- projective objects in arbitrary categories.
    intro E X f g _
    have : ∀ (j : Discrete (Fin n)),
      Projective ((ProjFG.inclusion R).obj (K.obj j)) :=
      fun j => (K.obj j).2.2
    let es : (j : Discrete (Fin n)) →
      (ProjFG.inclusion R).obj (K.obj j) ⟶ E := fun j =>
      Projective.factorThru (S.ι.app j ≫ f) g
    let e : S.pt ⟶ E := hS.desc ⟨_, Discrete.natTrans <| fun i => es i⟩
    refine ⟨e, ?_⟩
    apply hS.hom_ext
    intro j
    simp

instance (n : ℕ) (K : Discrete (Fin n) ⥤ ProjFG R) : CreatesColimit K
    (ProjFG.inclusion R) where
  reflects hE := {
    desc := fun S => hE.desc <| (ProjFG.inclusion R).mapCocone S
    fac := fun _ _ => hE.fac _ _
    uniq := fun S _ hm => hE.uniq ((ProjFG.inclusion R).mapCocone S) _ hm }
  lifts := fun S hS => {
    liftedCocone := {
      pt := ⟨S.pt, proj_and_fg_of_isColimit  _ _ _ _ hS⟩
      ι := {
        app := fun j => S.ι.app j
        naturality := fun _ _ e => S.ι.naturality e } }
    validLift := Cocones.ext (Iso.refl _) <| fun _ => rfl }

instance (n : ℕ) :
    CreatesColimitsOfShape (Discrete (Fin n)) (ProjFG.inclusion R) := by
  constructor ; intro K ; infer_instance

instance (n : ℕ) :
  HasColimitsOfShape (Discrete (Fin n)) (ModuleCat R) := sorry

instance : HasFiniteCoproducts (ProjFG R) :=
  ⟨fun _ => hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
    (ProjFG.inclusion _)⟩

end ModuleCat
