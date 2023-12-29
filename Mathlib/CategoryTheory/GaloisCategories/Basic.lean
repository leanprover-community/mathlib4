import Mathlib.CategoryTheory.Functor.Hom
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.RepresentationTheory.Action.Limits
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
  hasQuotientsByFiniteGroups (G : Type v) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) C
  -- (G3)
  --epiMonoFactorisation {X Z : C} (f : X ⟶ Z) : ∃ (Y : C) (p : X ⟶ Y) (i : Y ⟶ Z),
  --  Epi p ∧ Mono i ∧ p ≫ i = f
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
  preservesQuotientsByFiniteGroups (G : Type v) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) F
  -- (G6)
  reflectsIsos : ReflectsIsomorphisms F

class ConnectedObject {C : Type u} [Category.{v, u} C] (X : C) : Prop where
  notInitial : IsInitial X → False
  noTrivialComponent (Y : C) (i : Y ⟶ X) [Mono i] : (IsInitial Y → False) → IsIso i

class PreservesConnectedObjects {C : Type u} [Category.{v, u} C] {D : Type u₁}
    [Category.{v₁, u₁} D] (F : C ⥤ D) : Prop where
  preserves : ∀ {X : C} [ConnectedObject X], ConnectedObject (F.obj X)

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
instance (G : Type v) [Group G] [Finite G] : HasColimitsOfShape (SingleObj G) C :=
  PreGaloisCategory.hasQuotientsByFiniteGroups G 

variable {C : Type u} [Category.{v, u} C] {F : C ⥤ FintypeCat.{w}} [PreGaloisCategory C] [FibreFunctor F]

instance : PreservesLimitsOfShape (CategoryTheory.Discrete PEmpty.{1}) F :=
  FibreFunctor.preservesTerminalObjects
instance : PreservesLimitsOfShape WalkingCospan F :=
  FibreFunctor.preservesPullbacks
instance : PreservesEpimorphisms F :=
  FibreFunctor.preservesEpis
instance : PreservesFiniteCoproducts F :=
  FibreFunctor.preservesFiniteCoproducts
instance : PreservesColimitsOfShape (Discrete PEmpty.{1}) F :=
  FibreFunctor.preservesFiniteCoproducts.preserves PEmpty
instance : ReflectsIsomorphisms F :=
  FibreFunctor.reflectsIsos
noncomputable instance reflectsEmptyColimits : ReflectsColimitsOfShape (Discrete PEmpty.{1}) F :=
  reflectsColimitsOfShapeOfReflectsIsomorphisms
instance (G : Type v) [Group G] [Finite G] : PreservesColimitsOfShape (SingleObj G) F :=
  FibreFunctor.preservesQuotientsByFiniteGroups G

noncomputable instance preservesFiniteLimits : PreservesFiniteLimits F :=
  preservesFiniteLimitsOfPreservesTerminalAndPullbacks F

def preservesInitialObject (O : C) : IsInitial O → IsInitial (F.obj O) :=
  IsInitial.isInitialObj F O

noncomputable def reflectsInitialObject (O : C) : IsInitial (F.obj O) → IsInitial O :=
  IsInitial.isInitialOfObj F O  

lemma initialIffFibreEmpty (X : C) : Nonempty (IsInitial X) ↔ IsEmpty (F.obj X) := by
  rw [IsInitial.isInitialIffObj F X]
  exact FintypeCat.initialIffEmpty (F.obj X)

lemma notinitial_of_inhabited {X : C} (x : F.obj X) : IsInitial X → False := by
  intro hin
  exact ((initialIffFibreEmpty X).mp ⟨hin⟩).false x

lemma nonempty_fibre_of_connected (X : C) [ConnectedObject X] : Nonempty (F.obj X) := by
  by_contra h
  have ⟨hin⟩ : Nonempty (IsInitial X) := (initialIffFibreEmpty X).mpr (not_nonempty_iff.mp h)
  exact ConnectedObject.notInitial hin

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

/- The evaluation map on automorphisms is injective for connected objects. -/
lemma evaluation_aut_injective_of_connected (A : C) [ConnectedObject A] (a : F.obj A) :
    Function.Injective (fun f : Aut A => F.map (f.hom) a) := by
  show Function.Injective ((fun f : A ⟶ A => F.map f a) ∘ (fun f : Aut A => f.hom))
  apply Function.Injective.comp
  exact evaluationInjectiveOfConnected A A a
  exact @Aut.ext _ _ A

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

section GaloisObjects

variable {C : Type u} [Category.{v, u} C]

variable (F : C ⥤ FintypeCat.{w}) [PreGaloisCategory C] [FibreFunctor F]

instance autMulFibre (X : C) : SMul (Aut X) (F.obj X) := ⟨fun σ a => F.map σ.hom a⟩

class GaloisObject (X : C) : Prop where
  connected : ConnectedObject X
  transitiveAction : MulAction.IsPretransitive (Aut X) (F.obj X)

instance autMulFibreTransitiveOfGalois (X : C) [GaloisObject F X] :
    MulAction.IsPretransitive (Aut X) (F.obj X) :=
  GaloisObject.transitiveAction

--instance (X : C) [GaloisObject F X] : ConnectedObject X := sorry

lemma evaluation_bijective_of_galois (X : C) [GaloisObject F X] (x : F.obj X) :
    Function.Bijective (fun f : Aut X => F.map (f.hom) x) := by
  constructor
  have : ConnectedObject X := GaloisObject.connected F
  exact evaluation_aut_injective_of_connected X x
  intro y
  exact MulAction.IsPretransitive.exists_smul_eq x y

lemma galois_iff_card_aut_eq_fibre_of_connected (X : C) [ConnectedObject X] :
    GaloisObject F X ↔ Nat.card (Aut X) = Nat.card (F.obj X) := by
  constructor
  intro _
  obtain ⟨x⟩ := @nonempty_fibre_of_connected _ _ F _ _ X _
  exact Nat.card_eq_of_bijective _ (evaluation_bijective_of_galois F X x)
  intro h
  refine ⟨?_, ⟨?_⟩⟩
  infer_instance
  intro x y
  refine Function.Bijective.surjective ?_ y
  apply bijective_of_injective_of_card_eq _
  exact evaluation_aut_injective_of_connected X x
  assumption

def ConnectedObjects := { A : C | ConnectedObject A }

def GaloisObjects := { A : C | GaloisObject F A }

end GaloisObjects

section More

variable {C : Type u} [Category.{v, u} C]

variable (F : C ⥤ FintypeCat.{w}) [PreGaloisCategory C] [FibreFunctor F]

lemma card_hom_le_fibre_of_connected (A X : C) [ConnectedObject A]
    : Nat.card (A ⟶ X) ≤ Nat.card (F.obj X) := by
  obtain ⟨a⟩ := @nonempty_fibre_of_connected _ _ F _ _ A _
  apply Finite.card_le_of_injective (evaluation A X a)
  exact evaluationInjectiveOfConnected A X a

lemma card_aut_le_fibre_of_connected (A : C) [ConnectedObject A]
    : Nat.card (Aut A) ≤ Nat.card (F.obj A) := by
  obtain ⟨a⟩ := @nonempty_fibre_of_connected _ _ F _ _ A _
  apply Finite.card_le_of_injective (fun f : Aut A => F.map f.hom a)
  exact evaluation_aut_injective_of_connected A a

def finite_aut_of_connected (X : C) [ConnectedObject X] : Finite (Aut X) := by
  obtain ⟨x⟩ := @nonempty_fibre_of_connected _ _ F _ _ X _
  apply Finite.of_injective (fun σ => F.map σ.hom x)
  exact evaluation_aut_injective_of_connected X x

lemma epi_of_nonempty_to_connected {X A : C} [ConnectedObject A] (h : Nonempty (F.obj X))
    (f : X ⟶ A) : Epi f := by
  constructor
  intro Z u v huv
  obtain ⟨x⟩ := h
  apply evaluationInjectiveOfConnected A Z (F.map f x)
  convert_to F.map (f ≫ u) x = F.map (f ≫ v) x
  rw [F.map_comp]
  rfl
  rw [F.map_comp]
  rfl
  rw [huv]

lemma surjective_on_fibre_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : Function.Surjective (F.map f) :=
  surjective_of_epi (FintypeCat.incl.map (F.map f))

lemma surject_to_connected_of_nonempty_fibre {A X : C} (h : Nonempty (F.obj A))
    [ConnectedObject X] (f : A ⟶ X) :
    Function.Surjective (F.map f) := by
  have : Epi f := epi_of_nonempty_to_connected F h f
  exact surjective_on_fibre_of_epi F f

instance (X : C) : MulAction (Aut F) (F.obj X) where
  smul σ x := σ.hom.app X x
  one_smul := by aesop
  mul_smul := by aesop

end More

section Examples

variable {G : Type*} [Group G]

instance : PreGaloisCategory (Action FintypeCat (MonCat.of G)) where
  hasTerminalObject := inferInstance
  hasPullbacks := inferInstance
  hasFiniteCoproducts := inferInstance
  hasQuotientsByFiniteGroups := sorry
  monoInducesIsoOnDirectSummand := by
    -- maybe use CategoryTheory.Limits.Types.isCoprodOfMono
    intro X Y ⟨i, hi⟩ h
    let Z₁ : Set Y.V := Set.range i
    let Z₂ : Set Y.V := (Set.range i)ᶜ
    have : Fintype Z₂ := Fintype.ofFinite Z₂
    let Z : FintypeCat := FintypeCat.of Z₂
    --let j : X.V → Z₁ := Set.codRestrict i Z₁ (by simp)
    --have hinj : Function.Injective i := by exact?
    --have h1 : Function.Injective j := Function.Injective.codRestrict _ hinj
    --have h2 : Function.Surjective j := by
    --  intro ⟨b, a, hab⟩
    --  use a
    --  ext
    --  exact hab
    --have : Function.Bijective j := ⟨h1, h2⟩
    let ac (g : G) : Z → Z := by
      let f : Y.V → Y.V := Y.ρ g
      apply Set.MapsTo.restrict f Z₂ Z₂
      intro z hz
      by_contra hc
      simp at hc
      obtain ⟨x, hx⟩ := hc
      have hx' : Y.ρ g⁻¹ (i x) = Y.ρ g⁻¹ (Y.ρ g z) := congrArg (Y.ρ g⁻¹) hx
      have := congrFun (hi g⁻¹) x
      simp at this
      rw [←this] at hx'
      have : Y.ρ g⁻¹ (Y.ρ g z) = z := by
        show (Y.ρ g⁻¹ * Y.ρ g) z = z
        rw [←MonoidHom.map_mul Y.ρ g⁻¹ g]
        simp
      rw [this] at hx'
      apply hz
      use X.ρ g⁻¹ x
    let a : G →* End Z := by
      apply MonoidHom.mk
      swap
      constructor
      swap
      exact ac
      show Set.MapsTo.restrict (Y.ρ 1) Z₂ Z₂ _ = 𝟙 Z
      ext
      simp
      intro g h
      show ac (g * h) = ac g ∘ ac h
      ext ⟨z, _⟩
      apply Subtype.ext
      show Y.ρ (g * h) z = Y.ρ g (Y.ρ h z)
      rw [MonoidHom.map_mul]
      show (Y.ρ g ∘ Y.ρ h) z = Y.ρ g (Y.ρ h z)
      simp
    let Z : Action FintypeCat (MonCat.of G) := {
      V := Z
      ρ := a
    }
    use Z
    let u : Z ⟶ Y := by
      constructor
      swap
      show Z₂ → Y.V
      exact (↑)
      intro g
      aesop
    use u
    let s : BinaryCofan X Z := BinaryCofan.mk ⟨i, hi⟩ u
    let t : IsColimit s := {
      desc := by
        intro s
        show Y ⟶ s.pt
        constructor
        swap
        --let v1 : Z.V ⟶ s.pt.V := (BinaryCofan.inl s).hom
        admit
        admit
      fac := sorry
      uniq := sorry
    }
    admit

instance : FibreFunctor (forget₂ (Action FintypeCat (MonCat.of G)) FintypeCat) := sorry

instance (X : Action FintypeCat (MonCat.of G)) : MulAction G X.V where
  smul g x := X.ρ g x
  one_smul x := by
    show X.ρ 1 x = x
    simp only [MonCat.one_of, Action.ρ_one, FintypeCat.id_apply]
  mul_smul g h x := by
    show X.ρ (g * h) x = (X.ρ g * X.ρ h) x
    rw [MonoidHom.map_mul X.ρ g h]

lemma Action.connected_iff_transitive (X : Action FintypeCat (MonCat.of G)) :
    ConnectedObject X ↔ MulAction.IsPretransitive G X.V :=
  sorry

lemma Action.pretransitive_of_connected (X : Action FintypeCat (MonCat.of G))
    [ConnectedObject X] : MulAction.IsPretransitive G X.V :=
  sorry

variable (G)

def Action.ofMulAction (X : FintypeCat) [MulAction G X] : Action FintypeCat (MonCat.of G) where
  V := X
  ρ := MonCat.ofHom {
    toFun := fun (g : G) (x : X) => g • x
    map_one' := by simp only [one_smul, End.one_def]; rfl
    map_mul' := by
      intro σ τ 
      apply FintypeCat.hom_ext
      intro y
      show (σ * τ) • y = σ • τ • y
      rw [MulAction.mul_smul]
  }

def Action.ofMulAction' (X : Type _) [Fintype X] [MulAction G X] :
    Action FintypeCat (MonCat.of G) where
  V := FintypeCat.of X
  ρ := MonCat.ofHom {
    toFun := fun (g : G) (x : X) => g • x
    map_one' := by simp only [one_smul, End.one_def]; rfl
    map_mul' := by
      intro σ τ 
      apply FintypeCat.hom_ext
      intro (y : X)
      show (σ * τ) • y = σ • τ • y
      rw [MulAction.mul_smul]
  }

lemma connected_of_transitive (X : FintypeCat) [MulAction G X]
    [MulAction.IsPretransitive G X] : ConnectedObject (Action.ofMulAction G X) :=
  sorry

end Examples

end Galois
