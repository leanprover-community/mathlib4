/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill, Andrew Yang
-/
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# The category `TopModuleCat R` of topological modules

We define `TopModuleCat R`, the category of topological modules, and show that
it has all limits and colimits.

We also provide various adjunctions:
- `TopModuleCat.withModuleTopologyAdj`:
  equipping the module topology is left adjoint to the forgetful functor into `ModuleCat R`.
- `TopModuleCat.indiscreteAdj`:
  equipping the indiscrete topology is right adjoint to the forgetful functor into `ModuleCat R`.
- `TopModuleCat.freeAdj`:
  the free-forgetful adjunction between `TopModuleCat R` and `TopCat`.

## Future projects
Show that the forgetful functor to `TopCat` preserves filtered colimits.
-/

universe v u

variable (R : Type u) [Ring R] [TopologicalSpace R]

open CategoryTheory ConcreteCategory

/-- The category of topological modules. -/
structure TopModuleCat extends ModuleCat.{v} R where
  /-- The underlying topological space. -/
  [topologicalSpace : TopologicalSpace carrier]
  [isTopologicalAddGroup : IsTopologicalAddGroup carrier]
  [continuousSMul : ContinuousSMul R carrier]

namespace TopModuleCat

noncomputable instance : CoeSort (TopModuleCat.{v} R) (Type v) := ⟨fun M ↦ M.toModuleCat⟩

attribute [instance] topologicalSpace isTopologicalAddGroup continuousSMul

/-- Make an object in `TopModuleCat R` from an unbundled topological module. -/
abbrev of (M : Type v) [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] : TopModuleCat R :=
  have : ContinuousNeg M := ⟨by convert continuous_const_smul (-1 : R) (T := M); ext; simp⟩
  have : IsTopologicalAddGroup M := ⟨⟩
  ⟨.of R M⟩

lemma coe_of (M : Type v) [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] : (of R M) = M := rfl

variable {R} in
/-- Homs in `TopModuleCat` as one field structures over `ContinuousLinearMap`. -/
structure Hom (X Y : TopModuleCat.{v} R) where
  -- use `ofHom` instead
  private ofHom' ::
  /-- The underlying continuous linear map. Use `hom` instead. -/
  hom' : X →L[R] Y

instance : Category (TopModuleCat R) where
  Hom := Hom
  id M := ⟨ContinuousLinearMap.id R M⟩
  comp φ ψ := ⟨ψ.hom' ∘L φ.hom'⟩

instance : ConcreteCategory (TopModuleCat R) (· →L[R] ·) where
  hom   := Hom.hom'
  ofHom := Hom.ofHom'

variable {R} in
/-- Cast a hom in `TopModuleCat` into a continuous linear map. -/
abbrev Hom.hom {X Y : TopModuleCat R} (f : X.Hom Y) : X →L[R] Y :=
  ConcreteCategory.hom (C := TopModuleCat R) f

variable {R} in
/-- Construct a hom in `TopModuleCat` from a continuous linear map. -/
abbrev ofHom {X Y : Type v}
    [AddCommGroup X] [Module R X] [TopologicalSpace X] [ContinuousAdd X] [ContinuousSMul R X]
    [AddCommGroup Y] [Module R Y] [TopologicalSpace Y] [ContinuousAdd Y] [ContinuousSMul R Y]
    (f : X →L[R] Y) : of R X ⟶ of R Y :=
  ConcreteCategory.ofHom f

@[simp] lemma hom_ofHom {X Y : Type v}
    [AddCommGroup X] [Module R X] [TopologicalSpace X] [ContinuousAdd X] [ContinuousSMul R X]
    [AddCommGroup Y] [Module R Y] [TopologicalSpace Y] [ContinuousAdd Y] [ContinuousSMul R Y]
    (f : X →L[R] Y) :
    (ofHom f).hom = f := rfl

@[simp] lemma ofHom_hom {X Y : TopModuleCat R} (f : X.Hom Y) : ofHom f.hom = f := rfl

@[simp] lemma hom_comp {X Y Z : TopModuleCat R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp] lemma hom_id (X : TopModuleCat R) : hom (𝟙 X) = .id _ _ := rfl

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : TopModuleCat.{v} R) (f : A.Hom B) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

variable {R} in
/-- Construct an iso in `TopModuleCat` from a continuous linear equiv. -/
def ofIso {X Y : TopModuleCat R} (e : X ≃L[R] Y) : X ≅ Y :=
  ⟨ofHom e.toContinuousLinearMap, ofHom e.symm.toContinuousLinearMap,
    by ext; exact e.symm_apply_apply _, by ext; exact e.apply_symm_apply _⟩

variable {R} in
/-- Cast an iso in `TopModuleCat` into a continuous linear equiv. -/
def _root_.CategoryTheory.Iso.toContinuousLinearEquiv
    {X Y : TopModuleCat R} (e : X ≅ Y) : X ≃L[R] Y where
  __ := e.hom.hom
  invFun := e.inv.hom
  left_inv x := by cat_disch
  right_inv x := by cat_disch

instance {X Y : TopModuleCat R} : AddCommGroup (X ⟶ Y) where
  add f g := ofHom (f.hom + g.hom)
  zero := ofHom 0
  __ := Equiv.addCommGroup CategoryTheory.ConcreteCategory.homEquiv

instance : Preadditive (TopModuleCat R) where
  add_comp _ _ _ _ _ _  := ConcreteCategory.ext (ContinuousLinearMap.comp_add _ _ _)
  comp_add _ _ _ _ _ _  := ConcreteCategory.ext (ContinuousLinearMap.add_comp _ _ _)

section

variable {M₁ M₂ : TopModuleCat R}

@[simp] lemma hom_zero : (0 : M₁ ⟶ M₂).hom = 0 := rfl
@[simp] lemma hom_zero_apply (m : M₁) : (0 : M₁ ⟶ M₂).hom m = 0 := rfl
@[simp] lemma hom_add (φ₁ φ₂ : M₁ ⟶ M₂) : (φ₁ + φ₂).hom = φ₁.hom + φ₂.hom := rfl
@[simp] lemma hom_neg (φ : M₁ ⟶ M₂) : (- φ).hom = - φ.hom := rfl
@[simp] lemma hom_sub (φ₁ φ₂ : M₁ ⟶ M₂) : (φ₁ - φ₂).hom = φ₁.hom - φ₂.hom := rfl
@[simp] lemma hom_nsmul (n : ℕ) (φ : M₁ ⟶ M₂) : (n • φ).hom = n • φ.hom := rfl
@[simp] lemma hom_zsmul (n : ℤ) (φ : M₁ ⟶ M₂) : (n • φ).hom = n • φ.hom := rfl

end

section CommRing

variable {S : Type*} [CommRing S] [TopologicalSpace S]

instance {X Y : TopModuleCat S} : Module S (X ⟶ Y) where
  smul r f := ofHom (r • f.hom)
  __ := Equiv.module _ CategoryTheory.ConcreteCategory.homEquiv

instance [CommRing S] : Linear S (TopModuleCat S) where
  smul_comp _ _ _ _ _ _ := ConcreteCategory.ext (ContinuousLinearMap.comp_smul _ _ _)
  comp_smul _ _ _ _ _ _ := ConcreteCategory.ext (ContinuousLinearMap.smul_comp _ _ _)

@[simp]
lemma hom_smul {M₁ M₂ : TopModuleCat S} (s : S) (φ : M₁ ⟶ M₂) : (s • φ).hom = s • φ.hom := rfl

end CommRing

instance (M : TopModuleCat R) : TopologicalSpace M := M.2
instance (M : TopModuleCat R) : IsTopologicalAddGroup M := M.3

instance : HasForget₂ (TopModuleCat R) (ModuleCat R) where
  forget₂ :=
  { obj M := ModuleCat.of R M
    map φ := ModuleCat.ofHom φ.hom }

instance : HasForget₂ (TopModuleCat R) TopCat where
  forget₂ :=
  { obj M := .of M
    map φ   := TopCat.ofHom ⟨φ, φ.1.2⟩ }

instance : (forget₂ (TopModuleCat R) TopCat).ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    let e : X ≃L[R] Y :=
      { __ := f.hom, __ := TopCat.homeoOfIso (asIso ((forget₂ (TopModuleCat R) TopCat).map f)) }
    change IsIso (ofIso e).hom
    infer_instance

@[simp]
lemma hom_forget₂_TopCat_map {X Y : TopModuleCat R} (f : X ⟶ Y) :
    ((forget₂ _ TopCat).map f).hom = f.hom := rfl

@[simp]
lemma forget₂_TopCat_obj {X : TopModuleCat R} : ((forget₂ _ TopCat).obj X : Type _) = X := rfl

open Limits

section Colimit

variable {R}

variable {M : ModuleCat R} {I : Type*} {X : I → TopModuleCat R} (f : ∀ i, (X i).toModuleCat ⟶ M)

/-- The coinduced topology on `M` from a family of continuous linear maps into `M`, which is the
finest topology that makes it into a topological module and makes every map continuous. -/
def coinduced : TopModuleCat R :=
  letI : TopologicalSpace M := sInf { t | @ContinuousSMul R M _ _ t ∧ @ContinuousAdd M t _ ∧
      ∀ i, (X i).topologicalSpace.coinduced (f i) ≤ t }
  have : ContinuousAdd M := continuousAdd_sInf fun _ hs ↦ hs.2.1
  have : ContinuousSMul R M := continuousSMul_sInf fun _ hs ↦ hs.1
  .of R M

/-- The maps into the coinduced topology as homs in `TopModuleCat R`. -/
def toCoinduced (i) : X i ⟶ coinduced f :=
  ofHom (Y := coinduced f)
    ⟨(f i).hom, continuous_iff_coinduced_le.mpr (le_sInf fun _ hτ ↦ hτ.2.2 i)⟩

/-- The cocone of topological modules associated to a cocone over the underlying modules, where
the cocone point is given the coinduced topology. This is colimiting when the given cocone is. -/
def ofCocone {J : Type*} [Category J] {F : J ⥤ TopModuleCat R}
    (c : Cocone (F ⋙ forget₂ _ (ModuleCat R))) : Cocone F where
  pt := coinduced c.ι.app
  ι :=
  { app := toCoinduced c.ι.app,
    naturality {X Y} f := by ext x; exact congr($(c.ι.naturality f).hom x) }

/-- Given a colimit cocone over the underlying modules, equipping the cocone point with
the coinduced topology gives a colimit cocone in `TopModuleCat R`. -/
def isColimit {J : Type*} [Category J] {F : J ⥤ TopModuleCat R}
    {c : Cocone (F ⋙ forget₂ _ (ModuleCat R))} (hc : IsColimit c) :
    IsColimit (ofCocone c) where
  desc s := ofHom (X := (ofCocone c).pt) ⟨(hc.desc ((forget₂ _ _).mapCocone s)).hom, by
    rw [continuous_iff_le_induced]
    refine sInf_le ⟨continuousSMul_induced (M₂ := s.pt) (hc.desc ((forget₂ _ _).mapCocone s)).hom,
      continuousAdd_induced (N := s.pt) (hc.desc ((forget₂ _ _).mapCocone s)).hom, fun i ↦ ?_⟩
    rw [coinduced_le_iff_le_induced, induced_compose, ← continuous_iff_le_induced]
    change Continuous (X := F.obj i) (Y := s.pt)
      (c.ι.app i ≫ hc.desc ((forget₂ _ (ModuleCat R)).mapCocone s)).hom
    rw [hc.fac]
    exact (s.ι.app i).hom.2⟩
  fac s i := by ext x; exact congr($(hc.fac ((forget₂ _ _).mapCocone s) i).hom x)
  uniq s m H := by
    ext x
    refine congr($(hc.uniq ((forget₂ _ _).mapCocone s) ((forget₂ _ _).map m) fun j ↦ ?_).hom x)
    ext y
    exact congr($(H j).hom y)

instance {J : Type*} [Category J] {F : J ⥤ TopModuleCat R}
    [HasColimit (F ⋙ forget₂ _ (ModuleCat R))] : HasColimit F :=
  ⟨_, isColimit (colimit.isColimit _)⟩

instance {J : Type*} [Category J] [HasColimitsOfShape J (ModuleCat.{v} R)] :
    HasColimitsOfShape J (TopModuleCat.{v} R) where

instance : HasColimits (TopModuleCat.{v} R) where

end Colimit

section Limit

variable {R}

variable {M : ModuleCat R} {I : Type*} {X : I → TopModuleCat R} (f : ∀ i, M ⟶ (X i).toModuleCat)

/-- The induced topology on `M` from a family of continuous linear maps from `M`, which is the
coarsest topology that makes every map continuous. -/
def induced : TopModuleCat R :=
  letI : TopologicalSpace M := ⨅ i, (X i).topologicalSpace.induced (f i)
  have : ContinuousAdd M := continuousAdd_iInf fun _ ↦ continuousAdd_induced _
  have : ContinuousSMul R M := continuousSMul_iInf fun _ ↦ continuousSMul_induced _
  .of R M

/-- The maps from the induced topology as homs in `TopModuleCat R`. -/
def fromInduced (i) : induced f ⟶ X i :=
  ofHom (X := induced f) ⟨(f i).hom, continuous_iff_le_induced.mpr (iInf_le _ i)⟩

open Limits

/-- The cone of topological modules associated to a cone over the underlying modules, where
the cone point is given the induced topology. This is limiting when the given cone is. -/
def ofCone {J : Type*} [Category J] {F : J ⥤ TopModuleCat R}
    (c : Cone (F ⋙ forget₂ _ (ModuleCat R))) : Cone F where
  pt := induced c.π.app
  π :=
  { app := fromInduced c.π.app,
    naturality {X Y} f := by ext x; exact congr($(c.π.naturality f).hom x) }

/-- Given a limit cone over the underlying modules, equipping the cone point with
the induced topology gives a limit cone in `TopModuleCat R`. -/
def isLimit {J : Type*} [Category J] {F : J ⥤ TopModuleCat R}
    {c : Cone (F ⋙ forget₂ _ (ModuleCat R))} (hc : IsLimit c) :
    IsLimit (ofCone c) where
  lift s := ofHom (Y := (ofCone c).pt) ⟨(hc.lift ((forget₂ _ _).mapCone s)).hom, by
    rw [continuous_iff_coinduced_le]
    refine le_iInf fun i ↦ ?_
    rw [coinduced_le_iff_le_induced, induced_compose, ← continuous_iff_le_induced]
    change Continuous (X := s.pt) (Y := F.obj i)
      (hc.lift ((forget₂ _ (ModuleCat R)).mapCone s) ≫ c.π.app i).hom
    rw [hc.fac]
    exact (s.π.app i).hom.2⟩
  fac s i := by ext x; exact congr($(hc.fac ((forget₂ _ _).mapCone s) i).hom x)
  uniq s m H := by
    ext x
    refine congr($(hc.uniq ((forget₂ _ _).mapCone s) ((forget₂ _ _).map m) fun j ↦ ?_).hom x)
    ext y
    exact congr($(H j).hom y)

instance hasLimit_of_hasLimit_forget₂ {J : Type*} [Category J] {F : J ⥤ TopModuleCat.{v} R}
    [HasLimit (F ⋙ forget₂ _ (ModuleCat.{v} R))] : HasLimit F :=
  ⟨_, isLimit (limit.isLimit _)⟩

instance {J : Type*} [Category J] [HasLimitsOfShape J (ModuleCat.{v} R)] :
    HasLimitsOfShape J (TopModuleCat.{v} R) where
  has_limit _ := hasLimit_of_hasLimit_forget₂

instance : HasLimits (TopModuleCat.{v} R) where
  has_limits_of_shape _ _ := ⟨fun _ ↦ hasLimit_of_hasLimit_forget₂⟩

instance {J : Type*} [Category J] {F : J ⥤ TopModuleCat.{v} R}
    [HasLimit (F ⋙ forget₂ _ (ModuleCat.{v} R))]
    [PreservesLimit (F ⋙ forget₂ _ (ModuleCat.{v} R)) (forget _)] :
    PreservesLimit F (forget₂ _ TopCat) :=
  preservesLimit_of_preserves_limit_cone (isLimit (limit.isLimit _))
    (TopCat.isLimitConeOfForget (F := F ⋙ forget₂ _ TopCat)
      ((forget _).mapCone (getLimitCone (F ⋙ forget₂ _ (ModuleCat.{v} R))).1:)
      (isLimitOfPreserves (forget (ModuleCat R)) (limit.isLimit _)))

instance {J : Type*} [Category J]
    [HasLimitsOfShape J (ModuleCat.{v} R)]
    [PreservesLimitsOfShape J (forget (ModuleCat.{v} R))] :
    PreservesLimitsOfShape J (forget₂ (TopModuleCat.{v} R) TopCat) where

instance : PreservesLimits (forget₂ (TopModuleCat.{v} R) TopCat.{v}) where

end Limit

section Adjunction

/-- The functor equipping a module over a topological ring with the finest possible
topology making it into a topological module. This is left adjoint to the forgetful functor. -/
def withModuleTopology : ModuleCat R ⥤ TopModuleCat R where
  obj X :=
    letI := moduleTopology R X
    letI := IsModuleTopology.topologicalAddGroup R X
    .of R X
  map {X Y} f :=
    letI := moduleTopology R X
    letI := moduleTopology R Y
    letI := IsModuleTopology.topologicalAddGroup R Y
    ⟨f.hom, IsModuleTopology.continuous_of_linearMap f.hom⟩

/-- The adjunction between `withModuleTopology` and the forgetful functor. -/
def withModuleTopologyAdj : withModuleTopology R ⊣ forget₂ (TopModuleCat R) (ModuleCat R) where
  unit := 𝟙 _
  counit :=
  { app X := ofHom (X := (withModuleTopology R).obj (.of R X))
      ⟨.id, IsModuleTopology.continuous_of_linearMap _⟩ }

instance : (forget₂ (TopModuleCat R) (ModuleCat R)).IsRightAdjoint := ⟨_, ⟨withModuleTopologyAdj R⟩⟩
instance : (withModuleTopology R).IsLeftAdjoint := ⟨_, ⟨withModuleTopologyAdj R⟩⟩

/-- The functor equipping a module with the indiscrete topology.
This is right adjoint to the forgetful functor. -/
def indiscrete : ModuleCat.{v} R ⥤ TopModuleCat.{v} R where
  obj X :=
    letI : TopologicalSpace X := ⊤
    haveI : ContinuousAdd X := ⟨by rw [continuous_iff_coinduced_le]; exact le_top⟩
    haveI : ContinuousSMul R X := ⟨by rw [continuous_iff_coinduced_le]; exact le_top⟩
    .of R X
  map {X Y} f :=
    letI : TopologicalSpace X := ⊤
    letI : TopologicalSpace Y := ⊤
    ConcreteCategory.ofHom (C := TopModuleCat R)
      ⟨f.hom, by rw [continuous_iff_coinduced_le]; exact le_top⟩

/-- The adjunction between the forgetful functor and the indiscrete topology functor. -/
def indiscreteAdj : forget₂ (TopModuleCat.{v} R) (ModuleCat.{v} R) ⊣ indiscrete.{v} R where
  counit := 𝟙 _
  unit := { app X := ConcreteCategory.ofHom (C := TopModuleCat R)
              ⟨.id, by rw [continuous_iff_coinduced_le]; exact le_top⟩ }

instance : (forget₂ (TopModuleCat.{v} R) (ModuleCat.{v} R)).IsLeftAdjoint := ⟨_, ⟨indiscreteAdj R⟩⟩
instance : (indiscrete.{v} R).IsRightAdjoint := ⟨_, ⟨indiscreteAdj R⟩⟩

/-- The free topological module over a topological space. -/
noncomputable
def freeObj (X : TopCat.{v}) : TopModuleCat.{max v u} R :=
  letI : TopologicalSpace (X →₀ R) := sInf
    { t | @ContinuousSMul R _ _ _ t ∧ @ContinuousAdd _ t _ ∧
      X.str.coinduced (Finsupp.single · 1) ≤ t }
  letI : ContinuousAdd (X →₀ R) := continuousAdd_sInf fun _ h ↦ h.2.1
  letI : ContinuousSMul R (X →₀ R) := continuousSMul_sInf fun _ h ↦ h.1
  of R (X →₀ R)

lemma coe_freeObj (X : TopCat.{v}) : freeObj R X = (X →₀ R) := rfl

/-- The free topological module over a topological space is functorial. -/
noncomputable
def freeMap {X Y : TopCat.{v}} (f : X ⟶ Y) : freeObj R X ⟶ freeObj R Y :=
  ConcreteCategory.ofHom ⟨Finsupp.lmapDomain _ _ f.hom, by
    rw [continuous_iff_coinduced_le]
    refine le_sInf fun (τ : TopologicalSpace (_ →₀ R)) ⟨hτ₁, hτ₂, hτ₃⟩ ↦ ?_
    rw [coinduced_le_iff_le_induced]
    refine sInf_le ⟨continuousSMul_induced (Finsupp.lmapDomain _ _ f.hom),
      continuousAdd_induced (Finsupp.lmapDomain _ _ f.hom), ?_⟩
    rw [← coinduced_le_iff_le_induced]
    grw [← hτ₃, ← coinduced_mono (continuous_iff_coinduced_le.mp f.hom.2)]
    rw [coinduced_compose, coinduced_compose]
    congr! 1
    ext x
    simp [coe_freeObj]⟩

lemma freeMap_map {X Y : TopCat} (f : X ⟶ Y) (v : X →₀ R) :
    (freeMap R f : (X →₀ R) → (Y →₀ R)) v = Finsupp.mapDomain f.hom v := rfl

/-- The free topological module over a topological space as a functor.
This is left adjoint to the forgetful functor. -/
@[simps] noncomputable
def free : TopCat.{v} ⥤ TopModuleCat.{max v u} R :=
  { obj := freeObj R
    map f := freeMap R f
    map_id M := by ext x; exact DFunLike.congr_fun (Finsupp.lmapDomain_id _ _) x
    map_comp f g := by ext; exact DFunLike.congr_fun (Finsupp.lmapDomain_comp _ _ f.hom g.hom) _ }

/-- The free-forgetful adjoint for `TopModuleCat R`. -/
noncomputable
def freeAdj : free.{max v u} R ⊣ forget₂ (TopModuleCat.{max v u} R) TopCat.{max v u} where
  unit :=
  { app X := TopCat.ofHom ⟨(Finsupp.single · 1),
      continuous_iff_coinduced_le.mpr (le_sInf fun _ h ↦ h.2.2)⟩,
    naturality {X Y} f := by ext x; simp [freeMap_map] }
  counit :=
  { app X := ConcreteCategory.ofHom (C := TopModuleCat R) ⟨Finsupp.lift _ R X id, by
      rw [continuous_iff_le_induced]
      refine sInf_le ⟨continuousSMul_induced (Finsupp.lift _ R X id),
        continuousAdd_induced (Finsupp.lift _ R X id), ?_⟩
      rw [coinduced_le_iff_le_induced, induced_compose]
      convert induced_id.symm.le
      ext
      simp [coe_freeObj]⟩,
    naturality {X Y} f := by
      ext1
      apply ContinuousLinearMap.coe_injective
      refine Finsupp.lhom_ext' fun a ↦ LinearMap.ext_ring ?_
      dsimp [freeObj, freeMap]
      simp }
  left_triangle_components X := by
    ext1
    apply ContinuousLinearMap.coe_injective
    refine Finsupp.lhom_ext' fun a ↦ LinearMap.ext_ring ?_
    simp [freeMap, freeObj]
  right_triangle_components X := by
    ext
    simp [freeObj]

instance : (forget₂ (TopModuleCat.{max v u} R) TopCat).IsRightAdjoint := ⟨_, ⟨freeAdj R⟩⟩
instance : (free.{max v u} R).IsLeftAdjoint := ⟨_, ⟨freeAdj R⟩⟩

end Adjunction

end TopModuleCat
