/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# The category of sheaves of modules over a scheme

In this file, we define the abelian category of sheaves of modules
`X.Modules` over a scheme `X`, and study its basic functoriality.

-/

@[expose] public section

universe t u

open CategoryTheory Limits TopologicalSpace SheafOfModules Bicategory

namespace AlgebraicGeometry.Scheme

variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

variable (X) in
/-- The category of sheaves of modules over a scheme. -/
def Modules := SheafOfModules.{u} X.ringCatSheaf

namespace Modules

/-- Morphisms between `𝒪ₓ`-modules. Use `Hom.app` to act on sections. -/
def Hom (M N : X.Modules) : Type u := SheafOfModules.Hom M N

instance : Category X.Modules where
  Hom := Modules.Hom
  __ := inferInstanceAs (Category (SheafOfModules.{u} X.ringCatSheaf))

instance : Abelian X.Modules := inferInstanceAs (Abelian (SheafOfModules.{u} X.ringCatSheaf))
instance : HasLimits X.Modules := inferInstanceAs (HasLimits (SheafOfModules X.ringCatSheaf))
instance : HasColimits X.Modules := inferInstanceAs (HasColimits (SheafOfModules X.ringCatSheaf))

section Functor

variable (X) in
/-- The forgetful functor from `𝒪ₓ`-modules to presheaves of modules.
This is mostly useful to transport results from (pre)sheaves of modules to `𝒪ₓ`-modules and
usually shouldn't be used directly when working with actual `𝒪ₓ`-modules. -/
def toPresheafOfModules : X.Modules ⥤ X.PresheafOfModules := SheafOfModules.forget _

/-- The forgetful functor from `𝒪ₓ`-modules to presheaves of modules is fully faithful. -/
def fullyFaithfulToPresheafOfModules : (Modules.toPresheafOfModules X).FullyFaithful :=
  SheafOfModules.fullyFaithfulForget _

instance : (toPresheafOfModules X).Full := fullyFaithfulToPresheafOfModules.full
instance : (toPresheafOfModules X).Faithful := fullyFaithfulToPresheafOfModules.faithful
instance : (toPresheafOfModules X).IsRightAdjoint :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).isRightAdjoint

variable (X) in
/-- The forgetful functor from `𝒪ₓ`-modules to presheaves of abelian groups. -/
noncomputable def toPresheaf : X.Modules ⥤ TopCat.Presheaf Ab X :=
  toPresheafOfModules X ⋙ PresheafOfModules.toPresheaf _

instance : (toPresheaf X).Faithful := .comp _ (PresheafOfModules.toPresheaf _)
instance : PreservesLimits (toPresheaf X) := comp_preservesLimits _ (PresheafOfModules.toPresheaf _)
instance : (toPresheaf X).ReflectsIsomorphisms :=
  reflectsIsomorphisms_comp _ (PresheafOfModules.toPresheaf _)

end Functor

variable {M N K : X.Modules} {φ : M ⟶ N} {U V : X.Opens}

section Presheaf

/-- The underlying abelian presheaf of an `𝒪ₓ`-module. -/
noncomputable def presheaf (M : X.Modules) : TopCat.Presheaf Ab X := M.1.presheaf

/-- Notation for sections of a presheaf of module. -/
scoped[AlgebraicGeometry] notation3 "Γ(" M ", " U ")" => (Scheme.Modules.presheaf M).obj (.op U)

instance : Module Γ(X, U) Γ(M, U) := (M.val.obj (.op U)).isModule

variable (M) in
@[simp] lemma map_smul (i : U ⟶ V) (r : Γ(X, V)) (x : Γ(M, V)) :
    M.presheaf.map i.op (r • x) = X.presheaf.map i.op r • M.presheaf.map i.op x :=
  M.val.map_smul _ _ _

/-- The underlying map between abelian presheaves of a morphism of `𝒪ₓ`-modules. -/
noncomputable def Hom.mapPresheaf (φ : M ⟶ N) : M.presheaf ⟶ N.presheaf :=
  (toPresheaf X).map φ

/-- The application of a morphism of `𝒪ₓ`-modules to sections. -/
def Hom.app (φ : M ⟶ N) (U : X.Opens) : Γ(M, U) ⟶ Γ(N, U) :=
  (forget₂ _ _).map (φ.val.app (.op U))

@[simp] lemma mapPresheaf_app (φ : M ⟶ N) (U) : φ.mapPresheaf.app U = φ.app U.unop := rfl

@[simp]
lemma Hom.app_smul (φ : M ⟶ N) (r : Γ(X, U)) (x : Γ(M, U)) :
    φ.app U (r • x) = r • φ.app U x :=
  (φ.val.app (.op U)).hom.map_smul r x

@[simp] lemma Hom.add_app (φ ψ : M ⟶ N) : (φ + ψ).app U = φ.app U + ψ.app U := rfl
@[simp] lemma Hom.sub_app (φ ψ : M ⟶ N) : (φ - ψ).app U = φ.app U - ψ.app U := rfl
@[simp] lemma Hom.zero_app : (0 : M ⟶ N).app U = 0 := rfl
@[simp] lemma Hom.id_app (M : X.Modules) : (𝟙 M :).app U = 𝟙 _ := rfl
@[simp] lemma Hom.comp_app (φ : M ⟶ N) (ψ : N ⟶ K) : (φ ≫ ψ).app U = φ.app U ≫ ψ.app U := rfl

@[ext]
lemma hom_ext (f g : M ⟶ N) (H : ∀ U, f.app U = g.app U) : f = g := by
  apply SheafOfModules.hom_ext
  ext U x
  exact congr($(H U.unop) x)

lemma isSheaf (M : X.Modules) : M.presheaf.IsSheaf := SheafOfModules.isSheaf M

@[simp] lemma toPresheaf_obj : (toPresheaf X).obj M = M.presheaf := rfl
@[simp] lemma toPresheaf_map : (toPresheaf X).map φ = φ.mapPresheaf := rfl

lemma Hom.isIso_iff_isIso_app {M N : X.Modules} {φ : M ⟶ N} :
    IsIso φ ↔ ∀ U, IsIso (φ.app U) := by
  rw [← isIso_iff_of_reflects_iso _ (toPresheaf X), NatTrans.isIso_iff_isIso_app]
  simp [Opposite.op_surjective.forall]

instance [IsIso φ] : IsIso (φ.app U) := Hom.isIso_iff_isIso_app.mp ‹_› _

@[simp, push ←]
lemma inv_app [IsIso φ] : (inv φ).app U = inv (φ.app U) := by
  apply IsIso.eq_inv_of_hom_inv_id
  simp [← Hom.comp_app]

end Presheaf

noncomputable section Functorial

variable (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- The pushforward functor for categories of sheaves of modules over schemes. -/
def pushforward : X.Modules ⥤ Y.Modules :=
  SheafOfModules.pushforward f.toRingCatSheafHom

@[simp]
lemma pushforward_obj_obj (M : X.Modules) (U : Y.Opens) :
    Γ((pushforward f).obj M, U) = Γ(M, f ⁻¹ᵁ U) := rfl

@[simp]
lemma pushforward_obj_presheaf_map {U V : Y.Opens} (i : U ⟶ V) :
    ((pushforward f).obj M).presheaf.map i.op = M.presheaf.map ((Opens.map f.base).map i).op := rfl

@[simp]
lemma pushforward_map_app (φ : M ⟶ N) (U : Y.Opens) :
    ((pushforward f).map φ).app U = φ.app (f ⁻¹ᵁ U) := rfl

/-- The pullback functor for categories of sheaves of modules over schemes. -/
def pullback : Y.Modules ⥤ X.Modules :=
  SheafOfModules.pullback f.toRingCatSheafHom

/-- The pullback functor for categories of sheaves of modules over schemes
is left adjoint to the pushforward functor. -/
def pullbackPushforwardAdjunction : pullback f ⊣ pushforward f :=
  SheafOfModules.pullbackPushforwardAdjunction _

section

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts
  preservesBinaryBiproducts_of_preservesBinaryProducts

instance : (pullback f).IsLeftAdjoint := (pullbackPushforwardAdjunction f).isLeftAdjoint
instance : (pushforward f).IsRightAdjoint := (pullbackPushforwardAdjunction f).isRightAdjoint
instance : (pushforward f).Additive := Functor.additive_of_preservesBinaryBiproducts _
instance : (pullback f).Additive := Functor.additive_of_preservesBinaryBiproducts _

end

variable (X) in
/-- The pushforward of sheaves of modules by the identity morphism identifies
to the identity functor. -/
def pushforwardId : pushforward (𝟙 X) ≅ 𝟭 _ :=
  SheafOfModules.pushforwardId _

@[simp] lemma pushforwardId_hom_app_app : ((pushforwardId X).hom.app M).app U = 𝟙 _ := rfl
@[simp] lemma pushforwardId_inv_app_app : ((pushforwardId X).inv.app M).app U = 𝟙 _ := rfl

variable (X) in
/-- The pullback of sheaves of modules by the identity morphism identifies
to the identity functor. -/
def pullbackId : pullback (𝟙 X) ≅ 𝟭 _ :=
  SheafOfModules.pullbackId _

variable (X) in
lemma conjugateEquiv_pullbackId_hom :
    conjugateEquiv .id (pullbackPushforwardAdjunction (𝟙 X)) (pullbackId X).hom =
      (pushforwardId X).inv :=
  SheafOfModules.conjugateEquiv_pullbackId_hom _

/-- The composition of two pushforward functors for sheaves of modules on schemes
identify to the pushforward for the composition. -/
def pushforwardComp :
    pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g) :=
  SheafOfModules.pushforwardComp _ _

@[simp] lemma pushforwardComp_hom_app_app (U) : ((pushforwardComp f g).hom.app M).app U = 𝟙 _ := rfl
@[simp] lemma pushforwardComp_inv_app_app (U) : ((pushforwardComp f g).inv.app M).app U = 𝟙 _ := rfl

/-- The composition of two pullback functors for sheaves of modules on schemes
identify to the pullback for the composition. -/
def pullbackComp :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  SheafOfModules.pullbackComp _ _

/-- Pushforwards along equal morphisms are isomorphic. -/
def pushforwardCongr {f g : X ⟶ Y} (hf : f = g) : pushforward f ≅ pushforward g :=
    pushforwardNatIso _ (Opens.mapIso _ _ (hf ▸ rfl)) ≪≫
      SheafOfModules.pushforwardCongr (by cat_disch)

@[simp] lemma pushforwardCongr_hom_app_app {f g : X ⟶ Y} (hf : f = g) (U : Y.Opens) :
    ((pushforwardCongr hf).hom.app M).app U = M.presheaf.map (eqToHom (hf ▸ rfl)).op := rfl

@[simp] lemma pushforwardCongr_inv_app_app {f g : X ⟶ Y} (hf : f = g) (U : Y.Opens) :
    ((pushforwardCongr hf).inv.app M).app U = M.presheaf.map (eqToHom (hf ▸ rfl)).op := rfl

/-- Inverse images along equal morphisms are isomorphic. -/
def pullbackCongr {f g : X ⟶ Y} (hf : f = g) : pullback f ≅ pullback g :=
  eqToIso (hf ▸ rfl)

lemma conjugateEquiv_pullbackComp_inv :
    conjugateEquiv ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv =
    (pushforwardComp f g).hom :=
  SheafOfModules.conjugateEquiv_pullbackComp_inv _ _

@[reassoc]
lemma pseudofunctor_associativity :
    (pullbackComp f (g ≫ h)).inv ≫
      Functor.whiskerRight (pullbackComp g h).inv _ ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (pullbackComp f g).hom ≫ (pullbackComp (f ≫ g) h).hom =
    eqToHom (by simp) := by
  let e₁ := pullbackComp f (g ≫ h)
  let e₂ := Functor.isoWhiskerRight (pullbackComp g h) (pullback f)
  let e₃ := Functor.isoWhiskerLeft (pullback h) (pullbackComp f g)
  let e₄ := pullbackComp (f ≫ g) h
  change e₁.inv ≫ e₂.inv ≫ (Functor.associator _ _ _).hom ≫ e₃.hom ≫ e₄.hom = _
  have : e₃.hom ≫ e₄.hom = (Functor.associator _ _ _).inv ≫ e₂.hom ≫ e₁.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_assoc.{u}
      h.toRingCatSheafHom g.toRingCatSheafHom f.toRingCatSheafHom)
  simp [this]

@[reassoc]
lemma pseudofunctor_left_unitality :
    (pullbackComp f (𝟙 Y)).inv ≫
      Functor.whiskerRight (pullbackId Y).hom (pullback f) ≫ (Functor.leftUnitor _).hom =
        eqToHom (by simp) := by
  let e₁ := pullbackComp f (𝟙 _)
  let e₂ := Functor.isoWhiskerRight (pullbackId Y) (pullback f)
  let e₃ := (pullback f).leftUnitor
  change e₁.inv ≫ e₂.hom ≫ e₃.hom = _
  have : e₁.hom = e₂.hom ≫ e₃.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_id_comp.{u} f.toRingCatSheafHom)
  simp [← this]

@[reassoc]
lemma pseudofunctor_right_unitality :
    (pullbackComp (𝟙 X) f).inv ≫
      Functor.whiskerLeft (pullback f) (pullbackId X).hom ≫ (Functor.rightUnitor _).hom =
        eqToHom (by simp) := by
  let e₁ := pullbackComp (𝟙 _) f
  let e₂ := Functor.isoWhiskerLeft (pullback f) (pullbackId _)
  let e₃ := (pullback f).rightUnitor
  change e₁.inv ≫ e₂.hom ≫ e₃.hom = _
  have : e₁.hom = e₂.hom ≫ e₃.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_comp_id.{u} f.toRingCatSheafHom)
  simp [← this]

attribute [local simp] pseudofunctor_associativity pseudofunctor_left_unitality
  pseudofunctor_right_unitality Bicategory.toNatTrans_conjugateEquiv
  conjugateEquiv_pullbackId_hom Adjunction.ofCat_comp conjugateEquiv_pullbackComp_inv in
/-- The pseudofunctor from `Schemeᵒᵖ` to the bicategory of adjunctions which sends
a scheme `X` to the category `X.Modules` of sheaves of modules over `X`.
(This contains both the covariant and the contravariant functorialities of
these categories.) -/
@[simps! obj_obj map_l map_r map_adj
  mapId_hom_τl mapId_hom_τr mapId_inv_τl mapId_inv_τr
  mapComp_hom_τl mapComp_hom_τr mapComp_inv_τl mapComp_inv_τr]
def pseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Adj Cat) :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Adj.mk (Cat.of X.unop.Modules))
    (fun f ↦ .mk (pullbackPushforwardAdjunction f.unop).toCat)
    (fun _ ↦ Adj.iso₂Mk (Cat.Hom.isoMk (pullbackId _))
        (Cat.Hom.isoMk (pushforwardId _).symm))
    (fun _ _ ↦ Adj.iso₂Mk (Cat.Hom.isoMk (pullbackComp _ _).symm)
        (Cat.Hom.isoMk (pushforwardComp _ _)))

end Functorial

noncomputable section Restriction

variable [IsOpenImmersion f]

/-- Restriction of an `𝒪ₓ`-module along an open immersion.
This is isomorphic to the pullback functor (see `restrictFunctorIsoPullback`)
but has better defeqs. -/
def restrictFunctor :
    Y.Modules ⥤ X.Modules :=
  letI α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf := { app U := (f.appIso U.unop).inv }
  SheafOfModules.pushforward (F := f.opensFunctor)
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩

/-- The restriction of a module along an open immersion. -/
abbrev restrict (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f] : X.Modules :=
  (restrictFunctor f).obj M

@[simp] lemma restrict_obj (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f] (U) :
    Γ(M.restrict f, U) = Γ(M, f ''ᵁ U) := rfl

@[simp] lemma restrict_map (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f] {U V} (i : U ⟶ V) :
    (M.restrict f).presheaf.map i.op = M.presheaf.map (f.opensFunctor.map i).op := rfl

/-- The restriction of a module along an open immersion. -/
def restrictFunctorAdjCounitIso : pushforward f ⋙ restrictFunctor f ≅ 𝟭 _ :=
  letI := CategoryTheory.Functor.isContinuous_comp.{u} f.opensFunctor (Opens.map f.base)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  (SheafOfModules.pushforwardComp _ _) ≪≫ pushforwardNatIso _ (NatIso.ofComponents
      (fun U ↦ eqToIso (f.preimage_image_eq U).symm) fun _ ↦ rfl) ≪≫
    SheafOfModules.pushforwardCongr (by ext U x; exact
      congr($(f.appIso_inv_app_presheafMap U.unop) x)) ≪≫ SheafOfModules.pushforwardId _

/-- Restriction is right adjoint to pushforward. -/
def restrictAdjunction : restrictFunctor f ⊣ pushforward f := by
  refine pushforwardPushforwardAdj (by exact f.isOpenEmbedding.isOpenMap.adjunction) _ _ ?_ ?_
  · ext U x; exact congr($((f.app_appIso_inv _).symm).hom x)
  · ext U x
    have : (f.appIso U.unop).inv ≫ f.app _ ≫
      X.presheaf.map (eqToHom (f.preimage_image_eq U.unop).symm).op = 𝟙 _ := by
      rw [Scheme.Hom.appIso_inv_app_assoc, ← Functor.map_comp, ← X.presheaf.map_id]; rfl
    exact congr($this x)

instance : IsIso (restrictAdjunction f).counit :=
  inferInstanceAs (IsIso <| (restrictFunctorAdjCounitIso f).hom)

instance : (restrictFunctor f).IsLeftAdjoint := (restrictAdjunction f).isLeftAdjoint
instance : (pushforward f).Full := (restrictAdjunction f).fullyFaithfulROfIsIsoCounit.full
instance : (pushforward f).Faithful := (restrictAdjunction f).fullyFaithfulROfIsIsoCounit.faithful

@[simp]
lemma restrictAdjunction_unit_app_app (M : Y.Modules) (U : Y.Opens) :
    ((restrictAdjunction f).unit.app M).app U =
      M.presheaf.map (homOfLE (f.image_preimage_le U)).op := rfl

@[simp]
lemma restrictAdjunction_counit_app_app (M : X.Modules) (U : X.Opens) :
    ((restrictAdjunction f).counit.app M).app U =
      M.presheaf.map (eqToHom (f.preimage_image_eq U).symm).op := rfl

/-- Restriction is naturally isomorphic to the inverse image. -/
def restrictFunctorIsoPullback : restrictFunctor f ≅ pullback f :=
  (restrictAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)

/-- Restriction along the identity is isomorphic to the identity. -/
def restrictFunctorId : restrictFunctor (𝟙 X) ≅ 𝟭 _ :=
  SheafOfModules.pushforwardNatIso _ (NatIso.ofComponents (fun _ ↦ eqToIso (by simp))) ≪≫
    SheafOfModules.pushforwardCongr
      (by ext : 3; simp [← Functor.map_comp, SheafedSpace.sheaf]) ≪≫
    SheafOfModules.pushforwardId _

@[simp]
lemma restrictFunctorId_hom_app_app :
    (restrictFunctorId.hom.app M).app U =
      M.presheaf.map (eqToHom (show U = 𝟙 X ''ᵁ U by simp)).op := rfl

@[simp]
lemma restrictFunctorId_inv_app_app :
    (restrictFunctorId.inv.app M).app U =
      M.presheaf.map (eqToHom (show 𝟙 X ''ᵁ U = U by simp)).op := rfl

/-- Restriction along the composition is isomorphic to the composition of restrictions. -/
def restrictFunctorComp [IsOpenImmersion f] [IsOpenImmersion g] :
    restrictFunctor (f ≫ g) ≅ restrictFunctor g ⋙ restrictFunctor f :=
  have : (f.opensFunctor ⋙ g.opensFunctor).IsContinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology _) _
  SheafOfModules.pushforwardNatIso _ (NatIso.ofComponents fun _ ↦ eqToIso (by simp)) ≪≫
    SheafOfModules.pushforwardCongr (by ext : 3; simp [← Functor.map_comp, SheafedSpace.sheaf]) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

@[simp]
lemma restrictFunctorComp_hom_app_app [IsOpenImmersion g] (M : Z.Modules) :
    ((restrictFunctorComp f g).hom.app M).app U = M.presheaf.map (eqToHom (by simp)).op := rfl

@[simp]
lemma restrictFunctorComp_inv_app_app [IsOpenImmersion g] (M : Z.Modules) :
    ((restrictFunctorComp f g).inv.app M).app U = M.presheaf.map (eqToHom (by simp)).op := rfl

/-- Restriction along equal morphisms are isomorphic. -/
def restrictFunctorCongr {f g : X ⟶ Y} (hf : f = g) [IsOpenImmersion f] [IsOpenImmersion g] :
    restrictFunctor f ≅ restrictFunctor g :=
  SheafOfModules.pushforwardNatIso _ (NatIso.ofComponents fun _ ↦ eqToIso (by simp [hf])) ≪≫
    SheafOfModules.pushforwardCongr (by ext : 3; subst hf; simp)

@[simp]
lemma restrictFunctorCongr_hom_app_app {f g : X ⟶ Y} (hf : f = g) [IsOpenImmersion f]
    [IsOpenImmersion g] (M : Y.Modules) :
    ((restrictFunctorCongr hf).hom.app M).app U = M.presheaf.map (eqToHom (by simp [hf])).op := rfl

@[simp]
lemma restrictFunctorCongr_inv_app_app {f g : X ⟶ Y} (hf : f = g) [IsOpenImmersion f]
    [IsOpenImmersion g] (M : Y.Modules) :
    ((restrictFunctorCongr hf).inv.app M).app U = M.presheaf.map (eqToHom (by simp [hf])).op := rfl

/-- Restriction along open immersions commutes with taking stalks. -/
def restrictStalkNatIso (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    restrictFunctor f ⋙ toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor _ x ≅
    toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor _ (f x) :=
  haveI := Functor.initial_of_adjunction (f.isOpenEmbedding.isOpenMap.adjunctionNhds x)
  (toPresheaf _ ⋙ (Functor.whiskeringLeft (OpenNhds (f x))ᵒᵖ Y.Opensᵒᵖ Ab).obj
      (OpenNhds.inclusion (f x)).op).isoWhiskerLeft
      (Functor.Final.colimIso (f.isOpenEmbedding.isOpenMap.functorNhds x).op)

@[simp]
lemma germ_restrictStalkNatIso_hom_app (f : X ⟶ Y) [IsOpenImmersion f]
    (x : X) (M : Y.Modules) (hxU : x ∈ U) :
    ((restrictFunctor f).obj M).presheaf.germ U _ hxU ≫
      (restrictStalkNatIso f x).hom.app M = M.presheaf.germ _ _ (by simpa) :=
  haveI := Functor.initial_of_adjunction (f.isOpenEmbedding.isOpenMap.adjunctionNhds x)
  Functor.Final.ι_colimitIso_hom
    (f.isOpenEmbedding.isOpenMap.functorNhds x).op
    ((OpenNhds.inclusion ((ConcreteCategory.hom f.base) x)).op ⋙ M.presheaf) _

@[simp]
lemma germ_restrictStalkNatIso_inv_app (f : X ⟶ Y) [IsOpenImmersion f]
    (x : X) (M : Y.Modules) (hxU : x ∈ U) :
    M.presheaf.germ _ _ (by simpa) ≫ (restrictStalkNatIso f x).inv.app M =
      ((restrictFunctor f).obj M).presheaf.germ U _ hxU := by
  rw [← germ_restrictStalkNatIso_hom_app f x M hxU, Category.assoc, ← NatTrans.comp_app,
    Iso.hom_inv_id]
  simp

end Restriction

end AlgebraicGeometry.Scheme.Modules
