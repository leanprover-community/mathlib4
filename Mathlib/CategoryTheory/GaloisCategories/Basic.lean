import Mathlib.CategoryTheory.Functor.Hom
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.RepresentationTheory.Action
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.GaloisCategories.Generalities
import Mathlib.Data.Finite.Card

universe u v w v₁ u₁ u₂

open CategoryTheory Limits Functor

namespace Galois

section Def

/- Lenstra (G1)-(G3) -/
class PreGaloisCategory (C : Type u) [Category.{v, u} C] : Prop where
  -- (G1)
  hasTerminalObject : HasTerminal C
  hasPullbacks : HasPullbacks C
  -- (G2)
  hasFiniteCoproducts : HasFiniteCoproducts C
  hasQuotientsByFiniteGroups (G : Type w) [Group G] [Finite G] : HasColimitsOfShape C (SingleObj G ⥤ C)
  -- (G3)
  epiMonoFactorisation {X Z : C} (f : X ⟶ Z) : ∃ (Y : C) (p : X ⟶ Y) (i : Y ⟶ Z),
    Epi p ∧ Mono i ∧ p ≫ i = f
  monoInducesIsoOnDirectSummand {X Y : C} (i : X ⟶ Y) [Mono i] : ∃ (Z : C) (u : Z ⟶ Y),
    Nonempty (IsColimit (BinaryCofan.mk i u))

/- Lenstra (G4)-(G6) -/
class FibreFunctor {C : Type u} [Category.{v, u} C] [PreGaloisCategory C] (F : C ⥤ FintypeCat.{w}) where
  -- (G4)
  preservesTerminalObjects : PreservesLimitsOfShape (CategoryTheory.Discrete PEmpty.{1}) F
  --preservesTerminalObjects : IsIsomorphic (F.obj (⊤_ C)) PUnit
  preservesPullbacks : PreservesLimitsOfShape WalkingCospan F
  -- (G5)
  preservesFiniteCoproducts : PreservesFiniteCoproducts F
  preservesEpis : Functor.PreservesEpimorphisms F
  preservesQuotientsByFiniteGroups (G : Type w) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) F
 -- (G6)
  reflectsIsos : ReflectsIsomorphisms F

class ConnectedObject {C : Type u} [Category.{v, u} C] (X : C) : Prop where
  notInitial : IsInitial X → False
  noTrivialComponent (Y : C) (i : Y ⟶ X) [Mono i] : (IsInitial Y → False) → IsIso i

variable {C : Type u} [Category.{v, u} C] [PreGaloisCategory C]

instance : HasTerminal C := PreGaloisCategory.hasTerminalObject
instance : HasPullbacks C := PreGaloisCategory.hasPullbacks
instance : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
instance : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
instance : HasEqualizers C := hasEqualizers_of_hasPullbacks_and_binary_products
instance : HasFiniteCoproducts C := PreGaloisCategory.hasFiniteCoproducts
instance (ι : Type*) [Finite ι] : HasColimitsOfShape (Discrete ι) C :=
  hasColimitsOfShape_discrete C ι
instance : HasInitial C := inferInstance

variable {C : Type u} [Category.{v, u} C] {F : C ⥤ FintypeCat.{w}} [PreGaloisCategory C] [FibreFunctor F]

instance : PreservesLimitsOfShape (CategoryTheory.Discrete PEmpty.{1}) F :=
  FibreFunctor.preservesTerminalObjects
instance : PreservesLimitsOfShape WalkingCospan F :=
  FibreFunctor.preservesPullbacks
instance : PreservesFiniteCoproducts F :=
  FibreFunctor.preservesFiniteCoproducts
instance : PreservesColimitsOfShape (Discrete PEmpty.{1}) F :=
  FibreFunctor.preservesFiniteCoproducts.preserves PEmpty
instance : ReflectsIsomorphisms F :=
  FibreFunctor.reflectsIsos
noncomputable instance reflectsEmptyColimits : ReflectsColimitsOfShape (Discrete PEmpty.{1}) F :=
  reflectsColimitsOfShapeOfReflectsIsomorphisms

noncomputable instance preservesFiniteLimits : PreservesFiniteLimits F :=
  preservesFiniteLimitsOfPreservesTerminalAndPullbacks F

def preservesInitialObject (O : C) : IsInitial O → IsInitial (F.obj O) :=
  IsInitial.isInitialObj F O

noncomputable def reflectsInitialObject (O : C) : IsInitial (F.obj O) → IsInitial O :=
  IsInitial.isInitialOfObj F O  

lemma initialIffFibreEmpty (X : C) : Nonempty (IsInitial X) ↔ IsEmpty (F.obj X) := by
  rw [IsInitial.isInitialIffObj F X]
  exact FintypeCat.initialIffEmpty (F.obj X)

instance preservesMonomorphisms : PreservesMonomorphisms F :=
  preservesMonomorphisms_of_preservesLimitsOfShape F

lemma monoFromPullbackIso {X Y : C} (f : X ⟶ Y) [HasPullback f f]
    [Mono (pullback.fst : pullback f f ⟶ X)] : Mono f where
  right_cancellation g h heq := by
    let u : _ ⟶ pullback f f := pullback.lift g h heq
    let u' : _ ⟶ pullback f f := pullback.lift g g rfl
    trans
    show g = u' ≫ pullback.snd
    exact (pullback.lift_snd g g rfl).symm
    have h2 : u = u' := (cancel_mono pullback.fst).mp (by simp only [limit.lift_π, PullbackCone.mk_π_app])
    rw [←h2]
    simp only [limit.lift_π, PullbackCone.mk_π_app]

private noncomputable instance : PreservesLimitsOfShape (WalkingCospan) (forget FintypeCat) := by
  have h : forget FintypeCat = FintypeCat.incl := rfl
  rw [h]
  infer_instance

instance : ReflectsMonomorphisms F := ReflectsMonomorphisms.mk <| by
  intro X Y f _
  have : IsIso (pullback.fst : pullback (F.map f) (F.map f) ⟶ F.obj X) :=
    fst_iso_of_mono_eq (F.map f)
  let ϕ : F.obj (pullback f f) ≅ pullback (F.map f) (F.map f) := PreservesPullback.iso F f f

  have : ϕ.hom ≫ pullback.fst = F.map pullback.fst := PreservesPullback.iso_hom_fst F f f
  have : IsIso (F.map (pullback.fst : pullback f f ⟶ X)) := by
    rw [←this]
    exact IsIso.comp_isIso
  have : IsIso (pullback.fst : pullback f f ⟶ X) := isIso_of_reflects_iso pullback.fst F
  exact monoFromPullbackIso f

lemma monomorphismIffInducesInjective {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective (F.map f) := by
  constructor
  intro hfmono
  exact ConcreteCategory.injective_of_mono_of_preservesPullback (F.map f)
  intro hfinj
  exact mono_of_mono_map F (ConcreteCategory.mono_of_injective (F.map f) hfinj)

lemma isIso_of_mono_of_eqCardFibre {X Y : C} (f : X ⟶ Y) [Mono f] :
    Nat.card (F.obj X) = Nat.card (F.obj Y) → IsIso f := by
  intro h
  have : Function.Injective (F.map f) := (monomorphismIffInducesInjective f).mp inferInstance
  have : Function.Bijective (F.map f) := by
    apply (Fintype.bijective_iff_injective_and_card (F.map f)).mpr
    constructor
    exact (monomorphismIffInducesInjective f).mp inferInstance
    simp only [←Nat.card_eq_fintype_card]
    exact h
  have : IsIso (F.map f) := (FintypeCat.isIso_iff_bijective (F.map f)).mpr this
  exact isIso_of_reflects_iso f F

lemma ltCardFibre_of_mono_of_notIso {X Y : C} (f : X ⟶ Y) [Mono f] :
    ¬ IsIso f → Nat.card (F.obj X) < Nat.card (F.obj Y) := by
  intro h
  have : Nat.card (F.obj X) ≤ Nat.card (F.obj Y) :=
    Finite.card_le_of_injective
      (F.map f)
      ((monomorphismIffInducesInjective f).mp inferInstance)
  by_contra h2
  simp only [gt_iff_lt, not_lt] at h2
  apply h
  have : Nat.card (F.obj X) = Nat.card (F.obj Y) := Nat.le_antisymm this h2
  exact isIso_of_mono_of_eqCardFibre f this

lemma cardFibre_eq_sum_of_coprod (X Y : C)
    : Nat.card (F.obj (X ⨿ Y)) = Nat.card (F.obj X) + Nat.card (F.obj Y) := by
  have hh2 : F.obj (X ⨿ Y) ≅ (F.obj X) ⨿ (F.obj Y) := by
    symm
    exact PreservesColimitPair.iso F X Y
  have hh3 : F.obj (X ⨿ Y) ≃ F.obj X ⊕ F.obj Y := by
    apply Iso.toEquiv
    trans
    show FintypeCat.incl.obj (F.obj (X ⨿ Y)) ≅ FintypeCat.incl.obj (F.obj X ⨿ F.obj Y)
    exact Functor.mapIso FintypeCat.incl hh2
    trans
    show FintypeCat.incl.obj (F.obj X ⨿ F.obj Y) ≅
      FintypeCat.incl.obj (F.obj X) ⨿ FintypeCat.incl.obj (F.obj Y)
    exact (PreservesColimitPair.iso FintypeCat.incl (F.obj X) (F.obj Y)).symm
    exact Types.binaryCoproductIso (FintypeCat.incl.obj (F.obj X)) (FintypeCat.incl.obj (F.obj Y))
  rw [←Nat.card_sum]
  exact Nat.card_eq_of_bijective hh3.toFun (Equiv.bijective hh3)

lemma cardFibre_eq_of_iso { X Y : C } (i : X ≅ Y) : Nat.card (F.obj X) = Nat.card (F.obj Y) := by
  have e : F.obj X ≃ F.obj Y := Iso.toEquiv (mapIso (F ⋙ FintypeCat.incl) i)
  exact Nat.card_eq_of_bijective e (Equiv.bijective e)

def evaluation (A X : C) (a : F.obj A) (f : A ⟶ X) : F.obj X := F.map f a

/- The evaluation map is injective for connected objects. -/
lemma evaluationInjectiveOfConnected (A X : C) [ConnectedObject A] (a : F.obj A) :
    Function.Injective (evaluation A X a) := by
  intro f g (h : F.map f a = F.map g a)
  let E := equalizer f g
  have : IsIso (equalizer.ι f g) := by
    apply ConnectedObject.noTrivialComponent E (equalizer.ι f g)
    intro hEinitial
    have hFEinitial : IsInitial ((F ⋙ FintypeCat.incl).obj E) :=
      IsInitial.isInitialObj (F ⋙ FintypeCat.incl) E hEinitial
    have h2 : F.obj E ≃ { x : F.obj A // F.map f x = F.map g x } := by
      apply Iso.toEquiv
      trans
      exact PreservesEqualizer.iso (F ⋙ FintypeCat.incl) f g
      exact Types.equalizerIso (F.map f) (F.map g)
    have h3 : F.obj E ≃ PEmpty := (IsInitial.uniqueUpToIso hFEinitial (Types.isInitialPunit)).toEquiv
    apply not_nonempty_pempty
    apply (Equiv.nonempty_congr h3).mp
    apply (Equiv.nonempty_congr h2).mpr
    use a
  exact eq_of_epi_equalizer

/- The fibre functor is faithful. -/
lemma fibreFunctorFaithful : Faithful F where
  map_injective {X Y} := by
    intro f g h 
    have : IsIso (equalizerComparison f g F) :=
      instIsIsoObjToQuiverToCategoryStructToQuiverToCategoryStructToPrefunctorEqualizerEqualizerMapEqualizerComparison F f g
    have : IsIso (equalizer.ι (F.map f) (F.map g)) := equalizer.ι_of_eq h
    have : IsIso (F.map (equalizer.ι f g)) := by
      rw [←equalizerComparison_comp_π f g F]
      exact IsIso.comp_isIso
    have : IsIso (equalizer.ι f g) := isIso_of_reflects_iso _ F
    exact eq_of_epi_equalizer

end Def

end Galois
