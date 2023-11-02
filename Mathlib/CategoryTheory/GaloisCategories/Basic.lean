import Mathlib.CategoryTheory.Functor.Hom
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.RepresentationTheory.Action
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Category.Preorder

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
noncomputable instance : ReflectsColimitsOfShape (Discrete PEmpty.{1}) F :=
  reflectsColimitsOfShapeOfReflectsIsomorphisms

noncomputable instance preservesFiniteLimits : PreservesFiniteLimits F :=
  preservesFiniteLimitsOfPreservesTerminalAndPullbacks F

def preservesInitialObject (O : C) : IsInitial O → IsInitial (F.obj O) :=
  IsInitial.isInitialObj F O

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

instance : PreservesLimitsOfShape WalkingCospan (forget FintypeCat) := by exact?

lemma monomorphismIffInducesInjective {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective (F.map f) := by
  constructor
  intro hfmono
  exact ConcreteCategory.injective_of_mono_of_preservesPullback (F.map f)
  intro hfinj
  have : Mono (F.map f) := ConcreteCategory.mono_of_injective (F.map f) hfinj
  have h2 : IsIso (pullback.fst : pullback (F.map f) (F.map f) ⟶ F.obj X) := fst_iso_of_mono_eq (F.map f)
  let ϕ : F.obj (pullback f f) ≅ pullback (F.map f) (F.map f) := PreservesPullback.iso F f f

  have : ϕ.hom ≫ pullback.fst = F.map pullback.fst := PreservesPullback.iso_hom_fst F f f
  have : IsIso (F.map (pullback.fst : pullback f f ⟶ X)) := by
    rw [←this]
    exact IsIso.comp_isIso
  have : IsIso (pullback.fst : pullback f f ⟶ X) := isIso_of_reflects_iso pullback.fst F
  have : Mono f := monoFromPullbackIso f
  assumption

def evaluation (A X : C) (a : F.obj A) (f : A ⟶ X) : F.obj X := F.map f a

/- The evaluation map is injective for connected objects. -/
lemma evaluationInjectiveOfConnected (A X : C) [ConnectedObject A] (a : F.obj A) :
    Function.Injective (evaluation A X a) := by
  intro f g (h : F.map f a = F.map g a)
  let E := equalizer f g
  have : IsIso (equalizer.ι f g) := by
    apply ConnectedObject.noTrivialComponent E (equalizer.ι f g)
    intro hEinitial
    have hFEinitial : IsInitial (F.obj E) := preservesInitialObject E hEinitial
    have h2 : F.obj E ≃ { x : F.obj A // F.map f x = F.map g x } := by
      apply Iso.toEquiv
      trans
      exact PreservesEqualizer.iso F f g
      exact Types.equalizerIso (F.map f) (F.map g)
    have h3 : F.obj E ≃ PEmpty := (IsInitial.uniqueUpToIso hFEinitial (FintypeCat.isInitialPunit)).toEquiv
    apply not_nonempty_pempty
    apply (Equiv.nonempty_congr h3).mp
    apply (Equiv.nonempty_congr h2).mpr
    use a
  exact eq_of_epi_equalizer

end Def

end Galois
