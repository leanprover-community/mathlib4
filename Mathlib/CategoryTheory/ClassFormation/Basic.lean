/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

--public import Mathlib
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Connected
public import Mathlib.CategoryTheory.Galois.Equivalence
public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import Mathlib.CategoryTheory.Galois.ContAction
public import Mathlib.CategoryTheory.Sites.Coherent.RegularTopology
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-!
# ...

-/

-- #42397, #42396, #42320, #42568

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite
open scoped FintypeCatDiscrete

namespace FintypeCat

variable {S : FintypeCat.{w}} (s : S)

@[implicit_reducible, simps]
def overFiber : Over S ⥤ FintypeCat.{w} where
  obj X := of (X.hom ⁻¹' {s})
  map f := homMk (fun x ↦ ⟨f.left x, by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff,
      ← ConcreteCategory.comp_apply, f.w] using x.prop⟩)

@[implicit_reducible, simps]
def overFiberLeftAdjoint : FintypeCat.{w} ⥤ Over S where
  obj Y := Over.mk (Y := Y) (homMk (fun _ ↦ s))
  map f := Over.homMk f

def overFiberLeftAdjunction :
    overFiberLeftAdjoint s ⊣ overFiber s where
  unit.app Y := homMk (fun y ↦ ⟨y, by simp⟩)
  counit.app X := Over.homMk (homMk (fun x ↦ x.val))
    (by ext ⟨_, _⟩; simpa)


@[implicit_reducible, simps]
def overFiberRightAdjoint : FintypeCat.{w} ⥤ Over S where
  obj X :=
    Over.mk (Y := of (Σ (t : S), (Subtype.val (p := (· ∈ Set.singleton s))) ⁻¹' {t} → X))
      (homMk Sigma.fst)
  map f := Over.homMk (homMk (fun ⟨t, g⟩ ↦ ⟨t, f ∘ g⟩))

private lemma overFiberRightAdjunction_obj_left_ext_iff (X : FintypeCat.{w})
    (a b : Σ (t : S), (Subtype.val (p := (· ∈ Set.singleton s))) ⁻¹' {t} → X) :
    a = b ↔ ∃ (h : a.1 = b.1),
      ∀ (h' : a.1 = s), a.2 ⟨⟨s, by aesop⟩, by aesop⟩ = b.2 ⟨⟨s, by aesop⟩, by aesop⟩ := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact ⟨rfl, fun _ ↦ rfl⟩
  · rintro ⟨eq, h⟩
    obtain ⟨a, a'⟩ := a
    obtain ⟨b, b'⟩ := b
    obtain rfl : a = b := eq
    obtain rfl : a' = b' := by ext ⟨⟨t, rfl⟩, rfl⟩; exact h rfl
    rfl

def overFiberRightAdjunction :
    overFiber s ⊣ overFiberRightAdjoint s where
  unit.app X :=
    Over.homMk (homMk (fun x ↦ ⟨X.hom x, fun h ↦ ⟨x, by aesop⟩⟩)) (by aesop)
  unit.naturality X X' f := by
    ext x
    rw [overFiberRightAdjunction_obj_left_ext_iff]
    exact ⟨ConcreteCategory.congr_hom f.w x, fun _ ↦ rfl⟩
  counit.app Y :=
    homMk (fun y ↦ y.val.2 ⟨⟨s, Set.mem_singleton _⟩, y.prop.symm⟩)
  right_triangle_components X := by
    ext ⟨x, hx⟩
    rw [overFiberRightAdjunction_obj_left_ext_iff]
    exact ⟨rfl, fun _ ↦ rfl⟩

instance : (overFiber s).IsRightAdjoint :=
  (overFiberLeftAdjunction s).isRightAdjoint

instance : (overFiber s).IsLeftAdjoint :=
  (overFiberRightAdjunction s).isLeftAdjoint

end FintypeCat

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

lemma Aut.one_def (X : C) : (1 : Aut X) = Iso.refl _ := rfl

@[simp]
lemma ObjectProperty.homMk_id {P : ObjectProperty C} (X : P.FullSubcategory) :
    (homMk (𝟙 _) : X ⟶ X) = 𝟙 _ := rfl

noncomputable def Over.isInitialEquiv {S : C} {X : Over S}
    [PreservesColimit (Functor.empty (Over S)) (Over.forget S)] :
    IsInitial X ≃ IsInitial X.left where
  toFun h := IsInitial.isInitialObj (G := Over.forget S)  _  h
  invFun h :=
    IsInitial.ofUniqueHom (fun Z ↦ Over.homMk (h.to _) (h.hom_ext _ _))
      (fun Z m ↦ by ext; apply h.hom_ext)
  left_inv _ := by subsingleton
  right_inv _ := by subsingleton

lemma PreGaloisCategory.IsConnected.of_iso
    {X Y : C} [PreGaloisCategory.IsConnected X] (e : X ≅ Y) :
    IsConnected Y where
  notInitial h := notInitial (h.ofIso e.symm)
  noTrivialComponent Z i _ hZ := by
    rw [← isIso_comp_right_iff _ e.inv]
    exact noTrivialComponent _ _ hZ

lemma PreGaloisCategory.smul_def
    (F : C ⥤ FintypeCat.{w}) {X : C} (g : Aut X) (x : F.obj X) :
    g • x = F.map g.hom x := rfl

lemma Aut.autMulEquivOfIso_apply_hom {X Y : C} (e : X ≅ Y) (g : Aut X) :
    (autMulEquivOfIso e g).hom = e.inv ≫ g.hom ≫ e.hom := rfl

open GaloisCategory in
open ConcreteCategory in
lemma PreGaloisCategory.IsGalois.of_iso [GaloisCategory C]
    {X Y : C} [hX : PreGaloisCategory.IsGalois X] (e : X ≅ Y) :
    IsGalois Y := by
  have := IsConnected.of_iso e
  let F := getFiberFunctor C
  rw [isGalois_iff_pretransitive F, MulAction.isPretransitive_iff] at hX ⊢
  intro x y
  obtain ⟨x, rfl⟩ := (bijective_of_isIso (F.map e.hom)).surjective x
  obtain ⟨y, rfl⟩ := (bijective_of_isIso (F.map e.hom)).surjective y
  obtain ⟨g, rfl⟩ := hX x y
  refine ⟨Aut.autMulEquivOfIso e g, ?_⟩
  simp only [PreGaloisCategory.smul_def, Aut.autMulEquivOfIso_apply_hom,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp, Iso.hom_inv_id_assoc]

variable (C) in
abbrev PreGaloisCategory.isConnected : ObjectProperty C :=
  IsConnected

instance : (PreGaloisCategory.isConnected C).IsClosedUnderIsomorphisms where
  of_iso e _ := PreGaloisCategory.IsConnected.of_iso e

instance (X : (PreGaloisCategory.isConnected C).FullSubcategory) :
    PreGaloisCategory.IsConnected X.obj :=
  X.property

open PreGaloisCategory

namespace PreGaloisCategory

variable (F : C ⥤ FintypeCat.{w}) [GaloisCategory C] [FiberFunctor F]

end PreGaloisCategory

instance (G : Type*) [Group G] : HasFiniteColimits (Action FintypeCat.{w} G) where
  out _ _ _ := inferInstance

namespace GaloisCategory

instance [GaloisCategory C] : HasFiniteLimits C := by
  infer_instance

instance [GaloisCategory C] : HasFiniteColimits C where
  out _ _ _ :=
    Adjunction.hasColimitsOfShape_of_equivalence
      (functorToContAction (getFiberFunctor C))

-- ???
attribute [local instance] comp_preservesFiniteColimits comp_preservesFiniteLimits

instance [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] :
    PreservesFiniteColimits F := by
  change (PreservesFiniteColimits
    (functorToContAction F ⋙ ObjectProperty.ι _ ⋙ Action.forget _ _))
  infer_instance

open PreGaloisCategory

section

variable {D : Type*} [Category* D] [GaloisCategory C] [GaloisCategory D]
  (F : C ⥤ D) [F.IsEquivalence]

instance (X : C) [PreGaloisCategory.IsConnected X] :
    PreGaloisCategory.IsConnected (F.obj X) where
  notInitial h :=
    IsConnected.notInitial (X := X)
      ((IsInitial.isInitialObj F.inv _ h).ofIso
        (F.asEquivalence.unitIso.symm.app X))
  noTrivialComponent Y i _ hY := by
    obtain ⟨i', hi'⟩ := F.map_surjective ((F.objObjPreimageIso Y).hom ≫ i)
    have : Mono i' := Functor.mono_of_mono_map F (by rw [hi']; infer_instance)
    have := IsConnected.noTrivialComponent _ i' (fun hY' ↦ hY
      ((IsInitial.isInitialObj F _ hY').ofIso (F.objObjPreimageIso Y)))
    rw [← isIso_comp_left_iff (F.objObjPreimageIso Y).hom, ← hi']
    infer_instance

instance (G : D ⥤ FintypeCat.{w}) [FiberFunctor G] :
    FiberFunctor (F ⋙ G) where
  preservesQuotientsByFiniteGroups G _ _:= by
    obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{_, 0} G
    exact preservesColimitsOfShape_of_equiv e.toSingleObjEquiv.symm _

instance (X : C) [PreGaloisCategory.IsGalois X] :
    IsGalois (F.obj X) := by
  let G := getFiberFunctor D
  have : F.IsEquivalence := inferInstance
  have hX := (isGalois_iff_pretransitive (F ⋙ G) X).1 inferInstance
  rw [isGalois_iff_pretransitive G]
  rw [MulAction.isPretransitive_iff] at hX ⊢
  intro x y
  obtain ⟨g, rfl⟩ := hX x y
  exact ⟨F.mapAut X g, rfl⟩

lemma isConnected_iff_of_isEquivalence
    (F : C ⥤ D) [F.IsEquivalence] (X : C) :
    PreGaloisCategory.IsConnected (F.obj X) ↔ PreGaloisCategory.IsConnected X :=
  ⟨fun _ ↦ PreGaloisCategory.IsConnected.of_iso (X := F.inv.obj (F.obj X))
    (F.asEquivalence.unitIso.symm.app X), fun _ ↦ inferInstance⟩

lemma isGalois_iff_of_isEquivalence
    (F : C ⥤ D) [F.IsEquivalence] (X : C) :
    IsGalois (F.obj X) ↔ IsGalois X :=
  ⟨fun _ ↦ PreGaloisCategory.IsGalois.of_iso (X := F.inv.obj (F.obj X))
    (F.asEquivalence.unitIso.symm.app X), fun _ ↦ inferInstance⟩

end

lemma has_connected_component [GaloisCategory C] (X : C) (hX : IsInitial X → False) :
    ∃ (X₀ : C) (f : X₀ ⟶ X), Mono f ∧ PreGaloisCategory.IsConnected X₀ := by
  obtain ⟨ι, W, a, ha, _, _⟩ := has_decomp_connected_components X
  have : Nonempty ι := by
    by_contra!
    exact hX (IsInitial.ofUniqueHom
      (fun _ ↦ Cofan.IsColimit.desc ha (fun i ↦ (IsEmpty.false i).elim))
      (fun _ _ ↦ Cofan.IsColimit.hom_ext ha _ _ (fun i ↦ (IsEmpty.false i).elim)))
  exact ⟨W (Classical.arbitrary _), a _, MonoCoprod.mono_inj _ _ ha _, inferInstance⟩

instance [GaloisCategory C] {X Y : (isConnected C).FullSubcategory} (f : X ⟶ Y) :
    Epi f.hom := by
  let F := getFiberFunctor C
  exact epi_of_nonempty_of_isConnected F _

instance [GaloisCategory C] {X Y : (isConnected C).FullSubcategory} (f : X ⟶ Y) :
    Epi f where
  left_cancellation {Z} g₁ g₂ h := by
    ext
    simp only [← cancel_epi f.hom, ← InducedCategory.comp_hom, h]

instance : SplitEpiCategory FintypeCat.{w} where
  isSplitEpi_of_epi f hf := by
    replace hf : Function.Surjective f := by
      change Function.Surjective (FintypeCat.incl.map f)
      rw [← CategoryTheory.epi_iff_surjective]
      infer_instance
    exact ⟨⟨ SplitEpi.mk (FintypeCat.homMk (Function.surjInv hf)) (by
      ext x
      simp [Function.rightInverse_surjInv hf x])⟩⟩

instance : IsRegularEpiCategory FintypeCat.{w} := by
  infer_instance

lemma effectiveEpi_of_epi [GaloisCategory C] {X Y : C} (f : X ⟶ Y) [Epi f] :
    EffectiveEpi f := by
  let F := getFiberFunctor C
  rw [← isRegularEpi_iff_effectiveEpi]
  exact ⟨⟨{
    W := pullback f f
    left := pullback.fst _ _
    right := pullback.snd _ _
    w := pullback.condition
    isColimit := isColimitOfReflects F (by
      have : EffectiveEpi (F.map f) := by
        rw [← isRegularEpi_iff_effectiveEpi]
        exact IsRegularEpiCategory.regularEpiOfEpi _
      exact (isColimitMapCoconeCoforkEquiv _ _).2
        (isColimitCoforkOfEffectiveEpi _
        ((PullbackCone.mk _ _ pullback.condition).map F)
        (isLimitPullbackConeMapOfIsLimit F pullback.condition (pullbackIsPullback _ _))))
  }⟩⟩

instance [GaloisCategory C] {X Y : (isConnected C).FullSubcategory} (f : X ⟶ Y) :
    EffectiveEpi f := by
  have := effectiveEpi_of_epi f.hom
  let h := EffectiveEpi.getStruct f.hom
  have {W : (isConnected C).FullSubcategory} (e : X ⟶ W)
      (he : ∀ {Z : (isConnected C).FullSubcategory} (g₁ g₂ : Z ⟶ X),
        g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) {Z : C}
      (g₁ g₂ : Z ⟶ X.obj) (hf : g₁ ≫ f.hom = g₂ ≫ f.hom) :
      g₁ ≫ e.hom = g₂ ≫ e.hom := by
    obtain ⟨ι, T, a, ha, _, _⟩ := has_decomp_connected_components Z
    refine Cofan.IsColimit.hom_ext ha _ _ (fun i ↦ ?_)
    simpa [ObjectProperty.hom_ext_iff] using
      he (Z := ⟨T i, inferInstance⟩) (ObjectProperty.homMk (a i ≫ g₁))
        (ObjectProperty.homMk (a i ≫ g₂)) (by cat_disch)
  exact ⟨⟨{
    desc e he := ObjectProperty.homMk (h.desc e.hom (this e he))
    fac e he := by ext; exact h.fac e.hom (this e he)
    uniq e he m hm := by
      ext
      exact h.uniq e.hom _ _ (by simp [← hm])
  }⟩⟩

instance [GaloisCategory C] : Preregular (isConnected C).FullSubcategory where
  exists_fac {X Y Z} f g _ := by
    obtain ⟨X₀, a, _, _⟩ := has_connected_component (pullback f.hom g.hom) (by
      let F := getFiberFunctor C
      rw [not_initial_iff_fiber_nonempty F]
      let x : F.obj X.obj := Classical.arbitrary _
      have ⟨z, hz⟩ := surjective_on_fiber_of_epi F g.hom (F.map f.hom x)
      exact ⟨(fiberPullbackEquiv F f.hom g.hom).symm ⟨⟨x, z⟩, hz.symm⟩⟩)
    refine ⟨⟨X₀, inferInstance⟩, ObjectProperty.homMk (a ≫ pullback.fst _ _),
      inferInstance, ObjectProperty.homMk (a ≫ pullback.snd _ _), ?_⟩
    ext
    simp [pullback.condition]

variable (C) in
abbrev isConnectedTopology [GaloisCategory C] :
    GrothendieckTopology (isConnected C).FullSubcategory :=
  regularTopology (isConnected C).FullSubcategory

def isConnectedTopologyFiberFunctor [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [EssentiallySmall.{w} C] [FiberFunctor F] :
    GrothendieckTopology.Point.{w} (isConnectedTopology C) where
  fiber := ObjectProperty.ι _ ⋙ F ⋙ ObjectProperty.ι _
  jointly_surjective {X} R hR x := by
    rw [regularTopology.mem_sieves_iff_hasEffectiveEpi] at hR
    obtain ⟨Y, f, _, hR⟩ := hR
    obtain ⟨y, rfl⟩ := surjective_of_epi ((forget _).map (F.map f.hom)) x
    exact ⟨Y, f, hR, y, rfl⟩
  initiallySmall := by
    sorry
  isCofiltered := sorry

lemma isConnected_over_iff
    {S : C} (X : Over S)
    [(Over.forget S).PreservesMonomorphisms]
    [PreservesColimit (Functor.empty.{0} (Over S)) (Over.forget S)] :
    PreGaloisCategory.IsConnected X ↔
      PreGaloisCategory.IsConnected X.left := by
  refine ⟨fun _ ↦ ⟨fun h ↦ IsConnected.notInitial (Over.isInitialEquiv.symm h),
    fun Y i _ h ↦ ?_⟩,
    fun _ ↦ ⟨fun h ↦ IsConnected.notInitial (Over.isInitialEquiv h), fun Y i _ h ↦ ?_⟩⟩
  · let f : Over.mk (i ≫ X.hom) ⟶ X := Over.homMk i
    have := IsConnected.noTrivialComponent _ f (fun h' ↦ h (Over.isInitialEquiv h'))
    exact inferInstanceAs (IsIso ((Over.forget S).map f))
  · have : Mono i.left := inferInstanceAs (Mono ((Over.forget S).map i))
    have : IsIso ((Over.forget S).map i) :=
      IsConnected.noTrivialComponent Y.left i.left
        (fun h' ↦ h (Over.isInitialEquiv.symm h'))
    exact isIso_of_reflects_iso _ (Over.forget _)

instance {X S : C} (f : X ⟶ S)
    [(Over.forget S).PreservesMonomorphisms]
    [PreservesColimit (Functor.empty.{0} (Over S)) (Over.forget S)]
    [PreGaloisCategory.IsConnected X] :
    PreGaloisCategory.IsConnected (Over.mk f) := by
  rwa [isConnected_over_iff]

instance (S : C)
    [(Over.forget S).PreservesMonomorphisms]
    [PreservesColimit (Functor.empty.{0} (Over S)) (Over.forget S)] :
    PreservesIsConnected (Over.forget S) where
  preserves {X} _ := by
    rw [Over.forget_obj, ← isConnected_over_iff]
    infer_instance

section

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (S : C)
  [PreGaloisCategory.IsConnected S]

variable {S} in
lemma exists_aut_of_isConnected
    {X : C} (f : X ⟶ S) (x : F.obj X) (s : F.obj S) :
    ∃ (g : Aut F), F.map f (g.hom.app _ x) = s := by
  obtain ⟨g, hg⟩ :=
    (FiberFunctor.isPretransitive_of_isConnected F S).exists_smul_eq (F.map f x) s
  refine ⟨g, ?_⟩
  rwa [← NatTrans.naturality_apply]

set_option backward.privateInPublic true in
@[implicit_reducible, simps]
def fiberFunctorOver (s : F.obj S) : Over S ⥤ FintypeCat.{w} where
  obj X := .of ((F.map X.hom) ⁻¹' {s})
  map f := FintypeCat.homMk (fun x ↦⟨F.map f.left x, by
    simpa only [← ConcreteCategory.comp_apply, ← F.map_comp, f.w,
      Set.mem_preimage, Set.mem_singleton_iff] using x.prop⟩)

instance : PreGaloisCategory (Over S) where
  monoInducesIsoOnDirectSummand {X Y} i _ := by
    have : PreGaloisCategory.IsConnected S := inferInstance
    obtain ⟨Z, u, ⟨h⟩⟩ := monoInducesIsoOnDirectSummand i.left
    exact ⟨Over.mk (u ≫ Y.hom), Over.homMk u,
      ⟨isColimitOfReflects (Over.forget _)
        ((isColimitMapCoconeBinaryCofanEquiv ..).2 h)⟩⟩

instance : PreservesFiniteColimits (Over.post F (X := S)) where
  preservesFiniteColimits J _ _ := by
    have : PreservesColimitsOfShape J (Over.post F ⋙ Over.forget (F.obj S)) :=
      inferInstanceAs (PreservesColimitsOfShape J (Over.forget _ ⋙ F))
    exact preservesColimitsOfShape_of_reflects_of_preserves _ (Over.forget _)

instance (s : F.obj S) : PreservesFiniteColimits (fiberFunctorOver F S s) :=
  inferInstanceAs (PreservesFiniteColimits (Over.post F ⋙ FintypeCat.overFiber s))

instance (s : F.obj S) : PreservesFiniteLimits (fiberFunctorOver F S s) :=
  inferInstanceAs (PreservesFiniteLimits (Over.post F ⋙ FintypeCat.overFiber s))

set_option backward.isDefEq.respectTransparency false in
instance (s : F.obj S) : FiberFunctor (fiberFunctorOver F S s) where
  preservesQuotientsByFiniteGroups G _ _ := by
    obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{_, 0} G
    exact preservesColimitsOfShape_of_equiv e.toSingleObjEquiv.symm _
  reflectsIsos := ⟨fun {X Y} f hf ↦ by
    rw [← isIso_iff_of_reflects_iso _ (Over.forget S),
      ← isIso_iff_of_reflects_iso _ F, ConcreteCategory.isIso_iff_bijective]
    rw [ConcreteCategory.isIso_iff_bijective] at hf
    refine ⟨fun x₁ x₂ h ↦ ?_, fun y ↦ ?_⟩
    · dsimp at h
      obtain ⟨g, hg⟩ := exists_aut_of_isConnected F X.hom x₁ s
      refine ConcreteCategory.injective_of_mono_of_preservesPullback (g.hom.app _)
        (Subtype.ext_iff.1 (hf.injective (a₁ := ⟨_, hg⟩) (a₂ := ⟨_, ?_⟩) ?_))
      · simp only [Over.forget_obj, Set.mem_preimage, Set.mem_singleton_iff]
        rwa [← NatTrans.naturality_apply, ← f.w,
          Functor.map_comp, ConcreteCategory.comp_apply, ← h,
          ← Functor.map_comp_apply, f.w, NatTrans.naturality_apply]
      · dsimp
        ext
        change F.map f.left (g.hom.app _ x₁) = F.map f.left (g.hom.app _ x₂)
        simp only [← NatTrans.naturality_apply, h]
    · dsimp at y
      obtain ⟨g, hg⟩ := exists_aut_of_isConnected F Y.hom y s
      obtain ⟨x, hx⟩ := hf.surjective ⟨_, hg⟩
      replace hx : F.map f.left x.val = g.hom.app _ y := by
        simpa [Subtype.ext_iff] using! hx
      refine ⟨g.inv.app _ x.val,
        (ConcreteCategory.injective_of_mono_of_preservesPullback (g.hom.app _) ?_)⟩
      dsimp
      simp only [← hx, ← ConcreteCategory.comp_apply, Category.assoc,
        NatTrans.naturality, Iso.inv_hom_id_app_assoc]⟩

end

instance [GaloisCategory C] (S : C) [PreGaloisCategory.IsConnected S] :
    GaloisCategory (Over S) :=
  ⟨fiberFunctorOver (getFiberFunctor C) S
    (Classical.arbitrary _), inferInstance⟩

abbrev IsGaloisCover [GaloisCategory C] {Y X : C} (f : Y ⟶ X)
    [PreGaloisCategory.IsConnected X] : Prop :=
  IsGalois (Over.mk f)

lemma isGaloisCover_def {Y X : C} (f : Y ⟶ X) [GaloisCategory C]
  [PreGaloisCategory.IsConnected X] :
  IsGaloisCover f ↔ IsGalois (Over.mk f) := Iff.rfl

lemma isConnected_of_isGaloisCover [GaloisCategory C] {Y X : C} (f : Y ⟶ X)
    [PreGaloisCategory.IsConnected X] [IsGaloisCover f] :
    PreGaloisCategory.IsConnected Y := by
  rw [← dsimp% isConnected_over_iff (Over.mk f)]
  infer_instance

lemma hom_ext_of_isConnected [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    {Y X : C} [PreGaloisCategory.IsConnected Y]
    {f f' : Y ⟶ X} (y : F.obj Y) (h : F.map f y = F.map f' y) :
    f = f' :=
  F.map_injective (by
    ext z
    obtain ⟨g, rfl⟩ := (FiberFunctor.isPretransitive_of_isConnected F Y).exists_smul_eq y z
    simp only [mulAction_def, ← NatTrans.naturality_apply, h])

lemma isGaloisOver_of_isGalois [GaloisCategory C]
    {Y X : C} (f : Y ⟶ X) [PreGaloisCategory.IsConnected X]
    (hY : IsGalois Y := by infer_instance) :
    IsGaloisCover f := by
  have : PreGaloisCategory.IsConnected (Over.mk f).left := by
    dsimp
    infer_instance
  let F := getFiberFunctor C
  rw [isGaloisCover_def]
  let s : F.obj X := Classical.arbitrary _
  rw [isGalois_iff_pretransitive (fiberFunctorOver F X s),
    MulAction.isPretransitive_iff]
  rw [isGalois_iff_pretransitive F, MulAction.isPretransitive_iff] at hY
  intro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨g, rfl⟩ := hY x y
  exact ⟨Over.isoMk g (hom_ext_of_isConnected F x (by cat_disch)), rfl⟩

lemma isGaloisCover_of_comp [GaloisCategory C]
    {Z Y X : C} (g : Z ⟶ Y) (f : Y ⟶ X)
    [PreGaloisCategory.IsConnected Y]
    [PreGaloisCategory.IsConnected X]
    (hfg : IsGaloisCover (g ≫ f) := by infer_instance) :
    IsGaloisCover g := by
  rw [isGaloisCover_def] at hfg ⊢
  have : PreGaloisCategory.IsConnected (Over.mk f).left := by
    assumption
  let e := Over.iteratedSliceEquiv (Over.mk f)
  let γ := e.inverse.obj (Over.mk g)
  change IsGalois γ.left at hfg
  have := isGaloisOver_of_isGalois γ.hom
  rw [isGaloisCover_def] at this
  rwa [← isGalois_iff_of_isEquivalence e.inverse (Over.mk g)]

lemma exists_isGaloisCover [GaloisCategory C]
    {Y X : C} (f : Y ⟶ X) [PreGaloisCategory.IsConnected Y]
      [PreGaloisCategory.IsConnected X] :
    ∃ (Z : C) (g : Z ⟶ Y), IsGaloisCover (g ≫ f) := by
  obtain ⟨Z, g, _⟩ := exists_hom_from_galois_of_connected (Over.mk f)
  exact ⟨Z.left, g.left, by rwa [dsimp% g.w]⟩

end GaloisCategory

open GaloisCategory

variable (C) in
structure Formation [GaloisCategory C] [EssentiallySmall.{v} C] where
  sheaf : Sheaf (isConnectedTopology C) Ab.{v}

namespace Formation

variable [GaloisCategory C] [EssentiallySmall.{v} C] (Φ : Formation C)

section

variable {Y X : C} (f : Y ⟶ X) [PreGaloisCategory.IsConnected X]
  [PreGaloisCategory.IsConnected Y]
  [IsGaloisCover f]

def representation : Representation (ULift.{v} ℤ) (Aut (Over.mk f))
  (Φ.sheaf.obj.obj (op ⟨Y, inferInstance⟩)) where
  toFun g :=
    { toFun := (Φ.sheaf.obj.map (ObjectProperty.homMk g.inv.left).op).hom.toFun
      map_add' := by simp
      map_smul' := by simp }
  map_one' := by
    ext : 1
    dsimp [Aut.one_def]
    rw [ObjectProperty.homMk_id]
    simp
  map_mul' g h := by
    ext : 1
    dsimp
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl

abbrev rep : Rep.{v} (ULift.{v} ℤ) (Aut (Over.mk f)) := Rep.of (Φ.representation f)

end

end Formation

section

variable [GaloisCategory C] [EssentiallySmall.{v} C]

variable (C) in
structure FieldFormation extends Formation C where
  isZeroGroupCohomology {Y X : C} (f : Y ⟶ X) [PreGaloisCategory.IsConnected X]
    [PreGaloisCategory.IsConnected Y] [IsGaloisCover f] :
      IsZero (groupCohomology (toFormation.rep f) 1)

end

end CategoryTheory
