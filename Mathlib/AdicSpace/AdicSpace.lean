import Mathlib.AdicSpace.Spa.StalkValuation
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Geometry.RingedSpace.OpenImmersion

universe u

open Topology CategoryTheory TopologicalSpace UniformSpace TopCat

open AlgebraicGeometry Opposite

structure PreValuedRingedSpace extends PresheafedSpace TopCommRingCat where
  valuation : ∀ x : carrier, Spv (presheaf.forgetToRing.stalk x)

def PreValuedRingedSpace.forgetToRing (X : PreValuedRingedSpace.{u}) :
    PresheafedSpace CommRingCat.{u} :=
  (forget₂ TopCommRingCat CommRingCat).mapPresheaf.obj X.toPresheafedSpace

instance PreValuedRingedSpace.coeCarrier :
    CoeOut PreValuedRingedSpace TopCat where coe X :=
  X.carrier

instance PreValuedRingedSpace.coeSort : CoeSort PreValuedRingedSpace Type* where
  coe X := X.1

def PreValuedRingedSpace.toTopCat (X : PreValuedRingedSpace.{u}) : TopCat.{u} :=
  of X

instance : Category.{u} PreValuedRingedSpace.{u} :=
  InducedCategory.category PreValuedRingedSpace.toPresheafedSpace

attribute [local instance] TopCommRingCat.uniformSpace

instance (X : TopCat) (P : TopCat.Presheaf TopCommRingCat X) (U : Opens X) :
    TopologicalSpace (P.forgetToRing.obj (op U)) :=
  inferInstanceAs (TopologicalSpace (P.obj (op U)))

structure PreLVCRS extends PresheafedSpace TopCommRingCat where
  complete (U : Opens carrier) : CompleteSpace (presheaf.obj (op U))
  isLocalRing (x : carrier) : presheaf.forgetToRing.stalk x
  valuation (x : carrier) : Spv (presheaf.forgetToRing.stalk x)
  valuation_continuous (U : Opens carrier) (x : carrier) (hx : x ∈ U) :
    ((valuation x).comap (presheaf.forgetToRing.germ U x hx).hom').IsContinuous
  supp_maximal (x : carrier) : Ideal.IsMaximal (valuation x).out.supp

instance PreLVCRS.coeCarrier :
    CoeOut PreLVCRS TopCat where coe X :=
  X.carrier

instance PreLVCRS.coeSort : CoeSort PreLVCRS Type* where
  coe X := X.1

structure LVCRS extends SheafedSpace TopCommRingCat where
  complete (U : Opens carrier) : CompleteSpace (presheaf.obj (op U))
  isLocalRing (x : carrier) : presheaf.forgetToRing.stalk x
  valuation (x : carrier) : Spv (presheaf.forgetToRing.stalk x)
  valuation_continuous (U : Opens carrier) (x : carrier) (hx : x ∈ U) :
    ((valuation x).comap (presheaf.forgetToRing.germ U x hx).hom').IsContinuous
  supp_maximal (x : carrier) : Ideal.IsMaximal (valuation x).out.supp

def LVCRS.toPreLVCRS (X : LVCRS.{u}) : PreLVCRS.{u} where
  toPresheafedSpace := X.toPresheafedSpace
  valuation := X.valuation
  supp_maximal := X.supp_maximal
  complete := X.complete
  valuation_continuous := X.valuation_continuous
  isLocalRing := X.isLocalRing

instance LVCRS.coeCarrier :
    CoeOut LVCRS TopCat where coe X :=
  X.carrier

instance LVCRS.coeSort : CoeSort LVCRS Type* where
  coe X := X.1

def LVCRS.toPreValuedRingedSpace (X : LVCRS.{u}) : PreValuedRingedSpace.{u} where
  toPresheafedSpace := X.toPresheafedSpace
  valuation := X.valuation

noncomputable def PreValuedRingedSpace.restrictStalkMap {U : TopCat.{u}}
    (X : PreValuedRingedSpace.{u}) {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f) (x : U) :
    X.toPresheafedSpace.presheaf.forgetToRing.stalk (f x) ⟶
    (X.toPresheafedSpace.restrict h).presheaf.forgetToRing.stalk x :=
  (PresheafedSpace.Hom.stalkMap (PresheafedSpace.ofRestrict X.forgetToRing h) x)

noncomputable def PreValuedRingedSpace.restrictStalkMapInv {U : TopCat.{u}}
    (X : PreValuedRingedSpace.{u}) {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f) (x : U) :
    (X.toPresheafedSpace.restrict h).presheaf.forgetToRing.stalk x ⟶
      X.toPresheafedSpace.presheaf.forgetToRing.stalk (f x) :=
  inv (PresheafedSpace.Hom.stalkMap (PresheafedSpace.ofRestrict X.forgetToRing h) x)

def PreValuedRingedSpace.restrict {U : TopCat.{u}} (X : PreValuedRingedSpace.{u})
    {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f) : PreValuedRingedSpace where
  toPresheafedSpace := X.toPresheafedSpace.restrict h
  valuation x := by
    refine ValuativeRel.ofValuation ((X.valuation (f x)).valuation.comap ?_)
    exact ConcreteCategory.hom (X.restrictStalkMapInv h x)

def PreLVCRS.restrict {U : TopCat.{u}} (X : PreLVCRS.{u})
    {f : U ⟶ (X : TopCat)} (h : IsOpenEmbedding f) : PreLVCRS where
  toPresheafedSpace := X.toPresheafedSpace.restrict h
  complete := sorry
  isLocalRing := sorry
  valuation := sorry
  valuation_continuous := sorry
  supp_maximal := sorry
  -- valuation x := by
  --   refine ValuativeRel.ofValuation ((X.valuation (f x)).valuation.comap ?_)
  --   exact ConcreteCategory.hom (X.restrictStalkMapInv h x)

noncomputable def Spa (A : HuberPair.{u}) : PreLVCRS.{u} where
  carrier := of (spa A)
  presheaf := spa.presheaf A
  complete := sorry
  isLocalRing := sorry
  valuation := spa.presheaf.stalk_valuation A
  valuation_continuous := sorry
  supp_maximal := sorry

open TopologicalSpace

noncomputable def PreLVCRS.Hom.stalkMap {X Y : PreLVCRS.{u}}
    (f : X.toPresheafedSpace ⟶ Y.toPresheafedSpace) (x : X) :=
  PresheafedSpace.Hom.stalkMap
    ((Functor.mapPresheaf (forget₂ TopCommRingCat.{u} CommRingCat.{u})).map f) x

structure PreLVCRS.Hom (X Y : PreLVCRS.{u}) where
  hom : X.toPresheafedSpace ⟶ Y.toPresheafedSpace
  -- isLocal (x : X) : IsLocalHom (PreLVCRS.Hom.stalkMap hom x).hom'
  -- follows from `valuedCondition`
  valuativeCondition (x : X) : (X.valuation x).comap (PreLVCRS.Hom.stalkMap hom x).hom' =
    (Y.valuation (hom.base x))

@[simps]
def PreLVCRS.Hom.id (X : PreLVCRS.{u}) : PreLVCRS.Hom X X where
  hom := 𝟙 _
  valuativeCondition x := by
    dsimp [stalkMap]
    erw [AlgebraicGeometry.PresheafedSpace.stalkMap.id]
    rfl

@[simps]
def PreLVCRS.Hom.comp {X Y Z : PreLVCRS.{u}} (f : PreLVCRS.Hom X Y) (g : PreLVCRS.Hom Y Z) :
    PreLVCRS.Hom X Z where
  hom := f.hom ≫ g.hom
  valuativeCondition x := by
    sorry

-- def PreLVCRS.Hom.c {X Y : PreLVCRS.{u}} (f : PreLVCRS.Hom X Y) :

instance : Category.{u} PreLVCRS.{u} where
  Hom := PreLVCRS.Hom
  id := PreLVCRS.Hom.id
  comp := PreLVCRS.Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

def LVCRS.IsAdicSpace (X : LVCRS.{u}) : Prop :=
  ∀ x : X, ∃ (U : OpenNhds x) (A : HuberPair.{u}),
    (Nonempty (Spa.{u} A ≅ (X.toPreLVCRS.restrict U.isOpenEmbedding)) ∧
      (Spa A).presheaf.IsSheaf) -- not in the perfectoid project, but Wedhorn requires this

structure AdicSpace extends LVCRS where
  isAdic : toLVCRS.IsAdicSpace

namespace AdicSpace

@[ext]
structure Hom (X Y : AdicSpace.{u}) extends
    PreLVCRS.Hom X.toPreLVCRS Y.toPreLVCRS where

def Hom.comp {X Y Z : AdicSpace.{u}} (f : X.Hom Y) (g : Y.Hom Z) : X.Hom Z where
  __ := PreLVCRS.Hom.comp f.1 g.1

def Hom.id (X : AdicSpace.{u}) : X.Hom X where
  __ := PreLVCRS.Hom.id X.toPreLVCRS

instance : Category.{u} AdicSpace.{u} where
  Hom := AdicSpace.Hom
  id := Hom.id
  comp := Hom.comp

def forgetToPreLVCRS : AdicSpace.{u} ⥤ PreLVCRS.{u} where
  obj X := X.toPreLVCRS
  map {X Y} f := f.1

def PreLVCRS.forgetToPresheafedSpace : PreLVCRS.{u} ⥤ PresheafedSpace TopCommRingCat.{u} where
  obj X := X.toPresheafedSpace
  map f := f.hom

def forgetToPresheafedSpace : AdicSpace.{u} ⥤ PresheafedSpace TopCommRingCat.{u} :=
  forgetToPreLVCRS ⋙ PreLVCRS.forgetToPresheafedSpace

abbrev PreLVCRS.IsOpenImmersion : MorphismProperty PreLVCRS := fun _ _ f ↦
  PresheafedSpace.IsOpenImmersion (PreLVCRS.forgetToPresheafedSpace.map f)

abbrev IsOpenImmersion : MorphismProperty AdicSpace := fun _ _ f ↦
  PreLVCRS.IsOpenImmersion (forgetToPreLVCRS.map f)

def Hom.base {X Y : AdicSpace.{u}} (f : X ⟶ Y) : X.1.carrier ⟶ Y.1.carrier :=
  f.1.1.1

instance : CoeSort AdicSpace.{u} (Type u) where
  coe X := X.1.1

abbrev Opens (X : AdicSpace.{u}) := TopologicalSpace.Opens X.1

scoped[AdicSpace] notation3 "Γ(" X ", " U ")" =>
  (PresheafedSpace.presheaf (PreLVCRS.toPresheafedSpace
    (LVCRS.toPreLVCRS (AdicSpace.toLVCRS X)))).obj
    (op (α := AdicSpace.Opens _) U)

variable {X Y : AdicSpace.{u}}

def Opens.adicSpace (U : X.Opens) : AdicSpace.{u} :=
  sorry

instance : CoeOut X.Opens AdicSpace.{u} where
  coe U := U.adicSpace

def Opens.ι (U : X.Opens) : (U : AdicSpace.{u}) ⟶ X :=
  sorry

def Opens.preimage (f : X ⟶ Y) (U : Y.Opens) : X.Opens :=
  U.comap f.hom.base.1

def Hom.restrict (f : X ⟶ Y) (U : Y.Opens) : (U.preimage f : AdicSpace.{u}) ⟶ U :=
  sorry

@[reassoc (attr := simp)]
lemma Hom.restrict_ι (f : X ⟶ Y) (U : Y.Opens) :
    f.restrict U ≫ U.ι = (U.preimage f).ι ≫ f :=
  sorry

end AdicSpace

open CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type*} [Category C]
variable {D : Type*} [Category D]

def mapSheaf (F : C ⥤ D)
    [∀ X : SheafedSpace C, (Opens.grothendieckTopology X).HasSheafCompose F] :
    SheafedSpace C ⥤ SheafedSpace D where
  obj X :=
    { carrier := X.carrier
      presheaf := X.presheaf ⋙ F
      IsSheaf := GrothendieckTopology.HasSheafCompose.isSheaf _ X.IsSheaf }
  map f :=
    { base := f.base
      c := whiskerRight f.c F }
  map_id X := by
    ext U
    · rfl
    · simp
  map_comp f g := by
    ext U
    · rfl
    · simp

variable (F : C ⥤ D) [∀ X : SheafedSpace C, (Opens.grothendieckTopology X).HasSheafCompose F]

@[simp]
lemma mapSheaf_obj_X (X : SheafedSpace C) :
    (F.mapSheaf.obj X : TopCat) = (X : TopCat) :=
  rfl

@[simp]
lemma mapSheaf_obj_presheaf (X : SheafedSpace C) :
    (F.mapSheaf.obj X).presheaf = X.presheaf ⋙ F :=
  rfl

@[simp]
lemma mapSheaf_map_f {X Y : SheafedSpace C} (f : X ⟶ Y) :
    (F.mapSheaf.map f).base = f.base :=
  rfl

@[simp]
lemma mapSheaf_map_c {X Y : SheafedSpace C} (f : X ⟶ Y) :
    (F.mapSheaf.map f).c = whiskerRight f.c F :=
  rfl

end Functor

end CategoryTheory
