import Mathlib.AlgebraicTopology.Nerve
import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Limits.Shapes.CommSq
import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.AlgebraicTopology.Quasicategory

noncomputable section

namespace CategoryTheory
open Category Limits Functor
universe v v₁ v₂ u u₁ u₂

variable (K : Type u) [Category.{v} K]

instance : MonoidalClosed SSet := sorry

namespace SimplicialCategory
variable [SimplicialCategory K]
variable {K}

instance : CartesianClosed SSet := sorry
-- instance : HasBinaryProducts SSet := by infer_instance

-- ER: Should work but can't figure out the monoidal product is the cartesian product.
-- ER: Also I can't get the × notation to work for the product.
def sComp (X Y Z : K) : Limits.prod (sHom X Y) (sHom Y Z) ⟶ sHom X Z := by sorry
--  have := sHomComp X Y Z

def coneNatTrans {A : SSet} {AX X : K} (Y : K) (cone : A ⟶ sHom AX X) : sHom Y AX ⟶ (A ⟹ sHom Y X) :=
  let map := (prod.map (𝟙 (sHom Y AX)) cone) ≫ (sComp Y AX X)
  (CartesianClosed.curry ((prod.braiding A (sHom Y AX)).hom ≫ map))

structure IsCotensor {A : SSet} {X : K} (AX : K) (cone : A ⟶ sHom AX X) where
  uniq : ∀ (Y : K), (IsIso (coneNatTrans Y cone))

structure CotensorCone (A : SSet) (X : K) where
  /-- The object -/
  obj : K
  /-- The cone itself -/
  cone : A ⟶ sHom obj X
  /-- The universal property of the limit cone -/
  is_cotensor : IsCotensor obj cone

/-- `HasCotensor F` represents the mere existence of a simplicial cotensor. -/
class HasCotensor (A : SSet) (X : K) : Prop where mk' ::
  /-- There is some limit cone for `F` -/
  exists_cotensor : Nonempty (CotensorCone A X)

theorem HasCotensor.mk {A : SSet} {X : K} (c : CotensorCone A X) : HasCotensor A X :=
  ⟨Nonempty.intro c⟩

/-- Use the axiom of choice to extract explicit `CotensorCone A X` from `HasCotensor A X`. -/
def getCotensorCone (A : SSet) (X : K) [HasCotensor A X] : CotensorCone A X :=
  Classical.choice <| HasCotensor.exists_cotensor

variable (K) in
/-- `K` has simplicial cotensors  -/
class HasCotensors : Prop where
  /-- All `A : SSet` and `X : K` have a cotensor. -/
  has_cotensors : ∀ A : SSet, ∀ X : K, HasCotensor A X := by infer_instance -- ER: I don't get what this means.

-- ER: copied; not sure what this is.
instance (priority := 100) hasCotensorsOfHasCotensors {K : Type u} [Category.{v} K] [SimplicialCategory K] [HasCotensors K] (A : SSet) (X : K) : HasCotensor A X := HasCotensors.has_cotensors A X

-- Interface to the `HasCotensor` class.
/-- An arbitrary choice of cotensor obj. -/
def cotensor.obj (A : SSet) (X : K) [HasCotensor A X] : K :=
  (getCotensorCone A X).obj

infixr:60 " ⋔ " => cotensor.obj

/-- The associated cotensor cone. -/
def cotensor.cone (A : SSet) (X : K) [HasCotensor A X] : A ⟶ sHom (A ⋔ X) X :=
  (getCotensorCone A X).cone

/-- The universal property of this cone.  -/
def cotensor.is_cotensor (A : SSet) (X : K) [HasCotensor A X] :
    IsCotensor (A ⋔ X) (cotensor.cone A X) := (getCotensorCone A X).is_cotensor

def cotensor.iso (A : SSet) (X : K) [HasCotensor A X] (Y : K) :
    (sHom Y (A ⋔ X)) ≅ (A ⟹ sHom Y X) := by
  have := (cotensor.is_cotensor A X).uniq Y
  exact asIso (coneNatTrans Y (cone A X))

-- ER: Finish by applying ev0 to cotensor.iso and using a similar equivalence that calculates the 0-simplicies in the cartesian closed structure.
def cotensor.iso.underlying (A : SSet) (X : K) [HasCotensor A X] (Y : K) :
  (Y ⟶ (A ⋔ X)) ≃ (A ⟶ sHom Y X) := by
  have := SimplicialCategory.homEquiv' Y (A ⋔ X)
  sorry

def cotensorCovMap [HasCotensors K] (A : SSet) {X Y : K} (f : X ⟶ Y) : A ⋔ X ⟶ A ⋔ Y :=
  (cotensor.iso.underlying A Y (A ⋔ X)).symm
    ((cotensor.cone A X) ≫ (sHomWhiskerLeft (A ⋔ X) f))

def cotensorContraMap [HasCotensors K] {A B : SSet} (i : A ⟶ B) (X : K) : B ⋔ X ⟶ A ⋔ X :=
  (cotensor.iso.underlying A X (B ⋔ X)).symm (i ≫ (cotensor.cone B X))

theorem cotensor_bifunctoriality [HasCotensors K] {A B : SSet} (i : A ⟶ B) {X Y : K} (f : X ⟶ Y) :
    (cotensorCovMap B f) ≫ (cotensorContraMap i Y) =
    (cotensorContraMap i X) ≫ (cotensorCovMap A f) := by sorry

-- noncomputable def cotensor [SimplicialCategory K] : SSetᵒᵖ ⥤ K ⥤ K := sorry

-- abbrev cotensorObj (A : SSet) (X : K) : K := (cotensor.obj (.op A)).obj X

-- infixr:60 " ⋔⋔ " => cotensorObj

-- def foo (X : K) : IsTerminal ((⊥_ SSet) ⋔⋔ X) := sorry


end SimplicialCategory

open SimplicialCategory

class InfinityCosmosBase extends SimplicialCategory K where
  IsIsoFibration {X Y : K} : (X ⟶ Y) → Prop
  [has_qcat_homs : ∀ {X Y : K}, SSet.Quasicategory (EnrichedCategory.Hom X Y)]
  comp_isIsoFibration {X Y Z : K} {f : X ⟶ Y} {g : Y ⟶ Z} :
    IsIsoFibration f → IsIsoFibration g → IsIsoFibration (f ≫ g)
  iso_isIsoFibration {X Y : K} (e : X ≅ Y) : IsIsoFibration e.hom
  has_terminal : HasTerminal K
  all_objects_fibrant {X Y : K} (hY : IsTerminal Y) (f : X ⟶ Y) : IsIsoFibration f
  has_products : HasBinaryProducts K
  prod_map_fibrant {X Y X' Y' : K} {f : X ⟶ Y} {g : X' ⟶ Y'} :
    IsIsoFibration f → IsIsoFibration g → IsIsoFibration (prod.map f g)
  [has_isoFibration_pullbacks {X Y Z : K} (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsIsoFibration g → HasPullback f g]
  pullback_is_isoFibration {X Y Z P : K} (f : X ⟶ Z) (g : Y ⟶ Z)
    (fst : P ⟶ X) (snd : P ⟶ Y) (h : IsPullback fst snd f g) :
    IsIsoFibration g → IsIsoFibration fst
  has_limits_of_towers (F : ℕᵒᵖ ⥤ K) :
    (∀ n : ℕ, IsIsoFibration (F.map (homOfLE (Nat.le_succ n)).op)) → HasLimit F
  has_limits_of_towers_isIsoFibration (F : ℕᵒᵖ ⥤ K) (hf) :
    haveI := has_limits_of_towers F hf
    IsIsoFibration (limit.π F (.op 0))
  [has_cotensors : HasCotensors K] -- ER: Added
  -- leibniz_cotensor {X Y : K} (f : X ⟶ Y) (A B : SSet) (i : A ⟶ B) [Mono i]
  --   (hf : IsIsoFibration f) {P : K} (fst : P ⟶ B ⋔⋔ Y) (snd : P ⟶ A ⋔⋔ X)
  --   (h : IsPullback fst snd ((cotensor.map (.op i)).app Y) ((cotensor.obj (.op A)).map f)) :
  --   IsIsoFibration (h.isLimit.lift <|
  --     PullbackCone.mk ((cotensor.obj (.op B)).map f) ((cotensor.map (.op i)).app X) (by aesop_cat))
  leibniz_cotensor {X Y : K} (f : X ⟶ Y) (A B : SSet) (i : A ⟶ B) [Mono i]
    (hf : IsIsoFibration f) {P : K} (fst : P ⟶ B ⋔ Y) (snd : P ⟶ A ⋔ X)
    (h : IsPullback fst snd (cotensorContraMap i Y) (cotensorCovMap A f)) :
    IsIsoFibration (h.isLimit.lift <|
      PullbackCone.mk (cotensorCovMap B f) (cotensorContraMap i X) (cotensor_bifunctoriality i f))
  local_isoFibration {X Y Z : K} (f : Y ⟶ Z) (hf : IsIsoFibration f) :
    -- FIXME (V := SSet)
    ∀ (_ : MonoidalClosed.curry (EnrichedCategory.comp (V := SSet) X Y Z) = _), sorry
namespace InfinityCosmosBase
variable [InfinityCosmosBase.{v} K]

def IsoFibration (X Y : K) : Type v := {f : X ⟶ Y // IsIsoFibration f}

infixr:25  " ↠ " => IsoFibration


class InfinityCosmos extends InfinityCosmosBase K where
  IsIsoFibration {X Y : K} : (X ⟶ Y) → Prop
  [has_qcat_homs : ∀ {X Y : K}, SSet.Quasicategory (EnrichedCategory.Hom X Y)]

section preservesProducts

open Limits

/-- ER: This should be an instance of a theorem in mathlib about evaluation in functor categories preserving limits that exist. Statement has a universe level error.-/
-- def simplexBinaryProducts (X Y : SSet) (n : ℕ) : (X × Y) _[n] ≅ X _[n] × Y _[n] := by sorry

def hoFunctorPreservesExplicitBinaryProduct {X Y : SSet.{u}}
    (s : BinaryFan X Y) (hyp : IsLimit s) :
    IsLimit (BinaryFan.mk (SSet.hoFunctor.map (BinaryFan.fst s)) (SSet.hoFunctor.map (BinaryFan.snd s))) := by
  have := limitObjIsoLimitCompEvaluation (pair X Y) (op [0])
  simp at this
  refine BinaryFan.isLimitMk ?lift ?fac_left ?fac_right ?uniq
  · sorry
  · sorry
  · sorry
  · sorry



def hoFunctorPreservesBinaryProduct {X Y : SSet.{u}} : PreservesLimit (pair X Y) SSet.hoFunctor where
  preserves := by
    intro c clim
    sorry

def hoFunctorPreservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) SSet.hoFunctor where
      preservesLimit := by
        rintro K
        have := diagramIsoPair K
        sorry


end preservesProducts
