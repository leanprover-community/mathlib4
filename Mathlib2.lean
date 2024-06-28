import Mathlib
import Mathlib.AlgebraicGeometry.Morphisms.StandardSmooth

noncomputable section

universe u

open AlgebraicGeometry TopologicalSpace Opposite CategoryTheory AlgebraicGeometry.Scheme

@[simps]
def PresheafOfModules.self {C} [Category C] (R : Cᵒᵖ ⥤ RingCat) : PresheafOfModules R where
  presheaf := R ⋙ forget₂ _ _
  module X := inferInstanceAs (Module (R.obj X) (R.obj X))
  map_smul {X _Y} f r (x : R.obj X) := (R.map f).map_mul r x

@[simps]
def SheafOfModules.self {C} [Category C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat) : SheafOfModules R where
  val := .self R.1
  isSheaf := ((sheafCompose _ (forget₂ _ _)).obj R).2

section PresheafOfSubmodules

variable {C} [Category C] {R : Cᵒᵖ ⥤ RingCat} (M : PresheafOfModules R)

structure PresheafOfSubmodules where
  obj : ∀ X, Submodule (R.obj X) (M.obj X)
  map : ∀ {X Y : Cᵒᵖ} (i : X ⟶ Y), obj _ ≤ (obj _).comap (M.map i)

instance : Preorder (PresheafOfSubmodules M) := Preorder.lift PresheafOfSubmodules.obj

def PresheafOfSubmodules.mul {C} [Category C] {R : Cᵒᵖ ⥤ CommRingCat}
    (M N : PresheafOfSubmodules (.self (R ⋙ forget₂ _ _))) : PresheafOfSubmodules (.self (R ⋙ forget₂ _ _)) where
  obj X := HMul.hMul (α := Ideal (R.obj X)) (β := Ideal (R.obj X)) (γ := Ideal (R.obj X)) (M.obj X) (N.obj X)
  map {X Y} i := by
    refine (@Ideal.mul_le _ _ _).mpr ?_
    intros r hr s hs
    show R.map i (r * s) ∈
      (HMul.hMul (α := Ideal (R.obj Y)) (β := Ideal (R.obj Y)) (γ := Ideal (R.obj Y)) (M.obj Y) (N.obj Y))
    rw [map_mul]
    exact Ideal.mul_mem_mul (M.map _ hr) (N.map _ hs)

def PresheafOfSubmodules.toModule (N : PresheafOfSubmodules M) : PresheafOfModules R where
  presheaf :=
  { obj := fun X ↦ AddCommGrp.of (N.obj X)
    map := fun {X Y} f ↦ AddCommGrp.ofHom (((M.map f).toAddMonoidHom.restrict _).codRestrict _ (fun x ↦ N.map f x.2)) }
  module X := inferInstanceAs (Module (R.obj X) (N.obj X))
  map_smul {X Y} i r x := Subtype.ext (M.map_smul i r x.1)

def PresheafOfSubmodules.homOfLE {N₁ N₂ : PresheafOfSubmodules M} (e : N₁ ≤ N₂) : N₁.toModule ⟶ N₂.toModule where
  hom :=
  { app := fun X ↦ AddCommGrp.ofHom (Submodule.inclusion (e X)).toAddMonoidHom
    naturality := fun _ _ _ ↦ rfl }
  map_smul _ _ _ := rfl

def PresheafOfModules.ker {M N : PresheafOfModules R} (f : M ⟶ N) : PresheafOfSubmodules M where
  obj X := LinearMap.ker (f.app X)
  map {X Y} i x (hx : f.app _ x = 0) := show f.app _ (M.map _ x) = 0 by
    rw [PresheafOfModules.naturality_apply, hx, (N.map i).map_zero]

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : Scheme.Hom X Y)

def RingHom.IsSmooth {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.Smooth R S

class IsSmooth : Prop where
  cond : ∀ (U : Y.affineOpens) (V : X.affineOpens) (e), RingHom.IsSmooth (f.appLE U V e)

class IsProper extends UniversallyClosed f, LocallyOfFiniteType f, IsSeparated f : Prop where

def Scheme.Hom.sheafMap : Y.sheaf ⟶ ((Opens.map f.1.base).sheafPushforwardContinuous _ _ _).obj X.sheaf := ⟨f.1.c⟩

def Scheme.Hom.pushforwardModule : SheafOfModules X.ringCatSheaf ⥤ SheafOfModules Y.ringCatSheaf :=
  SheafOfModules.pushforward (S := Y.ringCatSheaf) (R := X.ringCatSheaf)
    (F := Opens.map f.1.base) ((sheafCompose _ (forget₂ _ _)).map (Scheme.Hom.sheafMap f))

instance : HasForget₂ CommRingCat AddCommGrp :=
  HasForget₂.mk' (fun R : CommRingCat => AddCommGrp.of R) (fun R => rfl) (fun {R₁ R₂} f => f.toAddMonoidHom) (by rfl)

def Scheme.Hom.toModuleHom : SheafOfModules.self Y.ringCatSheaf ⟶ f.pushforwardModule.obj (.self X.ringCatSheaf) where
  val := ⟨whiskerRight f.1.c (forget₂ CommRingCat AddCommGrp), fun U x y ↦ (f.val.c.app U).map_mul x y⟩

/--
Beware: This is a sheaf on `Δ[X/S]` we should pullback it to `X` when we are able to
-/
def SheafOfDifferentials {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SheafOfModules (Limits.pullback.diagonalObj f).ringCatSheaf :=
  let I := PresheafOfModules.ker (Limits.pullback.diagonal f).toModuleHom.1 -- kernel of `X ⟶ Δ[X/K]`
  have : I.mul I ≤ I := by intro x; exact Ideal.mul_le_left
  have := Limits.cokernel (PresheafOfSubmodules.homOfLE _ this) -- I/I^2 as presheaf
  (PresheafOfModules.sheafification (𝟙 _)).obj this -- I/I^2 as sheaf

def globalDifferentials {X : Scheme.{u}} {K : CommRingCat} (f : X ⟶ Spec K) :
    ModuleCat K :=
  have := (Scheme.Hom.pushforwardModule (Limits.pullback.fst ≫ f : _)).obj (SheafOfDifferentials f)
  (ModuleCat.restrictScalars (ΓSpecIso K).inv).obj (this.1.obj (op ⊤))

def SheafOfDifferentials.SpecEquiv {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
  globalDifferentials (Spec.map (CommRingCat.ofHom <| algebraMap R S)) ≅ ModuleCat.of R (Ω[S⁄R]) := sorry

abbrev Scheme.residueField (X : Scheme) (x : X) : CommRingCat := CommRingCat.of <| LocalRing.ResidueField (X.presheaf.stalk x)

def Scheme.SpecStalkTo (X : Scheme) (x : X) : Spec (X.presheaf.stalk x) ⟶ X :=
  let hU := isAffineOpen_opensRange (X.affineCover.map x)
  Spec.map (X.presheaf.germ ⟨x, X.affineCover.covers x⟩) ≫ hU.fromSpec

def Scheme.ofPoint (X : Scheme) (x : X) : Spec (X.residueField x) ⟶ X :=
  Spec.map (LocalRing.residue _) ≫ X.SpecStalkTo x

def Scheme.Hom.fiber {X Y : Scheme} (f : Hom X Y) (y : Y) : Scheme :=
  Limits.pullback f (Y.ofPoint y)

def Scheme.Hom.fiberι {X Y : Scheme} (f : Hom X Y) (y : Y) : f.fiber y ⟶ X :=
  Limits.pullback.fst

def Scheme.Hom.fiberTo {X Y : Scheme} (f : Hom X Y) (y : Y) : f.fiber y ⟶ Spec (Y.residueField y) :=
  Limits.pullback.snd

-- only works for fields despite taking any CommRingCat.
structure IsEllipticCurveOverField
    {X : Scheme.{u}} {K : CommRingCat.{u}} (f : X ⟶ Spec K) (e : Spec K ⟶ X) : Prop where
  isProper : IsProper f
  isSmooth : IsStandardSmoothOfRelativeDimension 1 f
  dimFunctionSpace :
    letI alg : K ⟶ Γ(X, ⊤) := ((ΓSpec.adjunction.homEquiv _ _).symm f).unop
    letI := alg.toAlgebra
    FiniteDimensional.finrank K Γ(X, ⊤) = 1
  genus : FiniteDimensional.finrank K (globalDifferentials f) = 1
  isSection : e ≫ f = 𝟙 _

structure IsEllipticCurve
    {X S : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X) : Prop where
  isSection : e ≫ f = 𝟙 _
  cond : ∀ s : S, IsEllipticCurveOverField (f.fiberTo s)
    (Limits.pullback.lift (S.ofPoint s ≫ e) (𝟙 _) (by simp [isSection]))

theorem isEllipticCurveOverField_iff
    {X : Scheme.{u}} {K : CommRingCat.{u}} (f : X ⟶ Spec K) (e : Spec K ⟶ X) :
  IsEllipticCurveOverField f e ↔ IsEllipticCurve f e := sorry

theorem isProper_iff {R S} [CommRing R] [CommRing S] (f : R →+* S) :
  IsProper (Spec.map (CommRingCat.ofHom f)) ↔ RingHom.IsIntegral f ∧ RingHom.FiniteType f := sorry
