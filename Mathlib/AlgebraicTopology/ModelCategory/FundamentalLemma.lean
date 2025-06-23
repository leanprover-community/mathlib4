/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
import Mathlib.CategoryTheory.Localization.Quotient
import Mathlib.CategoryTheory.MorphismProperty.Quotient

/-!
# The fundamental lemma of homotopical algebra

-/

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable (C : Type*) [Category C] [ModelCategory C]

namespace CofibrantObject

def homRel : HomRel (CofibrantObject C) :=
  fun X Y ↦ RightHomotopyRel (X := X.1) (Y := Y.1)

lemma homRel_iff_rightHomotopyRel {X Y : CofibrantObject C} {f g : X ⟶ Y} :
    homRel C f g ↔ RightHomotopyRel (ι.map f) (ι.map g) := Iff.rfl

lemma compClosure_homRel :
    Quotient.CompClosure (homRel C) = homRel C := by
  ext X Y f g
  refine ⟨?_, Quotient.CompClosure.of _ _ _⟩
  rintro ⟨i, f', g', p, h⟩
  exact (h.postcomp p).precomp i

abbrev π := Quotient (CofibrantObject.homRel C)

variable {C}

def toπ : CofibrantObject C ⥤ π C := Quotient.functor _

lemma toπ_obj_surjective : Function.Surjective (toπ (C := C)).obj :=
  fun ⟨_⟩ ↦ ⟨_, rfl⟩

instance : Functor.Full (toπ (C := C)) := by dsimp [toπ]; infer_instance

lemma toπ_map_eq {X Y : CofibrantObject C} {f g : X ⟶ Y}
    (h : homRel C f g) :
    toπ.map f = toπ.map g :=
  CategoryTheory.Quotient.sound _ h

lemma toπ_map_eq_iff {X Y : CofibrantObject C} [IsFibrant Y.1] (f g : X ⟶ Y) :
    toπ.map f = toπ.map g ↔ homRel C f g := by
  dsimp [toπ]
  rw [← Functor.homRel_iff, Quotient.functor_homRel_eq_compClosure_eqvGen,
    compClosure_homRel]
  exact (RightHomotopyRel.equivalence _ _).eqvGen_iff

end CofibrantObject

namespace FibrantObject

def homRel : HomRel (FibrantObject C) :=
  fun X Y ↦ LeftHomotopyRel (X := X.1) (Y := Y.1)

lemma homRel_iff_leftHomotopyRel {X Y : FibrantObject C} {f g : X ⟶ Y} :
    homRel C f g ↔ LeftHomotopyRel (ι.map f) (ι.map g) := Iff.rfl

lemma compClosure_homRel :
    Quotient.CompClosure (homRel C) = homRel C := by
  ext X Y f g
  refine ⟨?_, Quotient.CompClosure.of _ _ _⟩
  rintro ⟨i, f', g', p, h⟩
  exact (h.postcomp p).precomp i

abbrev π := Quotient (FibrantObject.homRel C)

variable {C}

def toπ : FibrantObject C ⥤ π C := Quotient.functor _

lemma toπ_obj_surjective : Function.Surjective (toπ (C := C)).obj :=
  fun ⟨_⟩ ↦ ⟨_, rfl⟩

instance : Functor.Full (toπ (C := C)) := by dsimp [toπ]; infer_instance

lemma toπ_map_eq {X Y : FibrantObject C} {f g : X ⟶ Y}
    (h : homRel C f g) :
    toπ.map f = toπ.map g :=
  CategoryTheory.Quotient.sound _ h

lemma toπ_map_eq_iff {X Y : FibrantObject C} [IsCofibrant X.1] (f g : X ⟶ Y) :
    toπ.map f = toπ.map g ↔ homRel C f g := by
  dsimp [toπ]
  rw [← Functor.homRel_iff, Quotient.functor_homRel_eq_compClosure_eqvGen,
    compClosure_homRel]
  exact (LeftHomotopyRel.equivalence _ _).eqvGen_iff

end FibrantObject

namespace BifibrantObject

def homRel : HomRel (BifibrantObject C) :=
  fun X Y ↦ RightHomotopyRel (X := X.1) (Y := Y.1)

instance : Congruence (homRel C) where
  equivalence := RightHomotopyRel.equivalence _ _
  compLeft p _ _ h := h.precomp p
  compRight p h := h.postcomp p

variable {C} {X Y : BifibrantObject C} (f g : X ⟶ Y)

lemma homRel_iff_rightHomotopyRel :
    homRel C f g ↔ RightHomotopyRel (ι.map f) (ι.map g) := Iff.rfl

lemma homRel_iff_leftHomotopyRel :
    homRel C f g ↔ LeftHomotopyRel (ι.map f) (ι.map g) := by
  rw [homRel_iff_rightHomotopyRel, leftHomotopyRel_iff_rightHomotopyRel]

variable (C) in
abbrev π := Quotient (BifibrantObject.homRel C)

def toπ : BifibrantObject C ⥤ π C := Quotient.functor _

lemma toπ_obj_surjective : Function.Surjective (toπ (C := C)).obj :=
  fun ⟨_⟩ ↦ ⟨_, rfl⟩

instance : Functor.Full (toπ (C := C)) := by dsimp [toπ]; infer_instance

lemma toπ_map_eq_iff {X Y : BifibrantObject C} (f g : X ⟶ Y) :
    toπ.map f = toπ.map g ↔ homRel C f g :=
  Quotient.functor_map_eq_iff _ _ _

section

variable (E : Type*) [Category E]

lemma inverts_iff_factors (F : BifibrantObject C ⥤ E) :
    (weakEquivalences _).IsInvertedBy F ↔
    ∀ ⦃K L : BifibrantObject C⦄ (f g : K ⟶ L),
      homRel C f g → F.map f = F.map g := by
  constructor
  · intro H K L f g h
    obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good
    have := isCofibrant_of_cofibration P.ι
    let γ : K ⟶ mk P.P := h.h
    let p₀ : mk P.P ⟶ L := P.p₀
    let p₁ : mk P.P ⟶ L := P.p₁
    let s : L ⟶ mk P.P := P.ι
    have : IsIso (F.map s) := H _ (by
      rw [← weakEquivalence_iff, weakEquivalence_iff_ι_map]
      exact inferInstanceAs (WeakEquivalence P.ι))
    simp only [← h.h₀, ← h.h₁]
    change F.map (γ ≫ p₀) = F.map (γ ≫ p₁)
    simp only [Functor.map_comp]
    congr 1
    simp only [← cancel_epi (F.map s), ← Functor.map_comp]
    congr 1
    exact ι.map_injective (P.ι_p₀.trans P.ι_p₁.symm)
  · intro h X Y f hf
    rw [← weakEquivalence_iff, weakEquivalence_iff_ι_map] at hf
    let f' := (bifibrantObjects C).ι.map f
    obtain ⟨g', h₁, h₂⟩ := RightHomotopyClass.exists_homotopy_inverse f'
    refine ⟨F.map g', ?_, ?_⟩
    all_goals
    · rw [← F.map_comp, ← F.map_id]
      apply h
      assumption

def strictUniversalPropertyFixedTargetToπ :
    Localization.StrictUniversalPropertyFixedTarget
    toπ (weakEquivalences (BifibrantObject C)) E where
  inverts := by
    rw [inverts_iff_factors]
    intro K L f g h
    exact CategoryTheory.Quotient.sound _ h
  lift F hF := CategoryTheory.Quotient.lift _ F
    (by rwa [inverts_iff_factors] at hF)
  fac F hF := rfl
  uniq _ _ h := Quotient.lift_unique' _ _ _ h

end

instance : toπ.IsLocalization (weakEquivalences (BifibrantObject C)) :=
  .mk' _ _ (strictUniversalPropertyFixedTargetToπ _)
    (strictUniversalPropertyFixedTargetToπ _)

instance {X Y : BifibrantObject C} (f : X ⟶ Y) [hf : WeakEquivalence f] :
    IsIso (toπ.map f) :=
  Localization.inverts toπ (weakEquivalences _) f (by rwa [weakEquivalence_iff] at hf)

abbrev ιCofibrantObject : BifibrantObject C ⥤ CofibrantObject C :=
  ObjectProperty.ιOfLE (bifibrantObjects_le_cofibrantObject C)

abbrev ιFibrantObject : BifibrantObject C ⥤ FibrantObject C :=
  ObjectProperty.ιOfLE (bifibrantObjects_le_fibrantObject C)

instance (X : BifibrantObject C) :
    IsFibrant (BifibrantObject.ιCofibrantObject.obj X).obj := X.2.2

instance (X : BifibrantObject C) :
    IsCofibrant (BifibrantObject.ιFibrantObject.obj X).obj := X.2.1

protected def π.ιCofibrantObject : π C ⥤ CofibrantObject.π C :=
  CategoryTheory.Quotient.lift _
    (ιCofibrantObject ⋙ CofibrantObject.toπ)
    (fun _ _ _ _ h ↦ CategoryTheory.Quotient.sound _ h)

protected def π.ιFibrantObject : π C ⥤ FibrantObject.π C :=
  CategoryTheory.Quotient.lift _
    (ιFibrantObject ⋙ FibrantObject.toπ)
    (fun _ _ _ _ h ↦ CategoryTheory.Quotient.sound _ (by
      simpa [FibrantObject.homRel, leftHomotopyRel_iff_rightHomotopyRel]))

end BifibrantObject

namespace CofibrantObject

variable {C}

lemma exists_bifibrant (X : CofibrantObject C) :
    ∃ (Y : BifibrantObject C) (i : X ⟶ BifibrantObject.ιCofibrantObject.obj Y),
      Cofibration (ι.map i) ∧ WeakEquivalence (ι.map i) := by
  have h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
      (terminal.from X.obj)
  have := isCofibrant_of_cofibration h.i
  have : IsFibrant h.Z := by
    rw [isFibrant_iff_of_isTerminal h.p terminalIsTerminal]
    infer_instance
  exact ⟨BifibrantObject.mk h.Z, h.i, inferInstanceAs (Cofibration h.i),
    inferInstanceAs (WeakEquivalence h.i)⟩

noncomputable def bifibrantResolutionObj (X : CofibrantObject C) :
    BifibrantObject C :=
  (exists_bifibrant X).choose

noncomputable def iBifibrantResolutionObj (X : CofibrantObject C) :
    X ⟶ BifibrantObject.ιCofibrantObject.obj (bifibrantResolutionObj X) :=
  (exists_bifibrant X).choose_spec.choose

instance (X : CofibrantObject C) :
    Cofibration (ι.map (iBifibrantResolutionObj X)) :=
  (exists_bifibrant X).choose_spec.choose_spec.1

instance (X : CofibrantObject C) :
    WeakEquivalence (ι.map (iBifibrantResolutionObj X)) :=
  (exists_bifibrant X).choose_spec.choose_spec.2

instance (X : BifibrantObject C) :
    IsFibrant (ι.obj (BifibrantObject.ιCofibrantObject.obj X)) := X.2.2

lemma exists_bifibrant_map {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    ∃ (g : bifibrantResolutionObj X₁ ⟶ bifibrantResolutionObj X₂),
      iBifibrantResolutionObj X₁ ≫ (BifibrantObject.ιCofibrantObject.map g) =
      f ≫ iBifibrantResolutionObj X₂ := by
  have sq : CommSq (ι.map (f ≫ iBifibrantResolutionObj X₂))
    (ι.map (iBifibrantResolutionObj X₁)) (terminal.from _) (terminal.from _) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_left⟩

noncomputable def bifibrantResolutionMap {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    bifibrantResolutionObj X₁ ⟶ bifibrantResolutionObj X₂ :=
  (exists_bifibrant_map f).choose

@[reassoc (attr := simp)]
noncomputable def bifibrantResolutionMap_fac {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    iBifibrantResolutionObj X₁ ≫
      (BifibrantObject.ιCofibrantObject.map (bifibrantResolutionMap f)) =
      f ≫ iBifibrantResolutionObj X₂ :=
  (exists_bifibrant_map f).choose_spec

@[reassoc (attr := simp)]
noncomputable def bifibrantResolutionMap_fac' {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    toπ.map X₁.iBifibrantResolutionObj ≫
      BifibrantObject.π.ιCofibrantObject.map
        (BifibrantObject.toπ.map (bifibrantResolutionMap f)) =
    toπ.map f ≫ toπ.map X₂.iBifibrantResolutionObj :=
  toπ.congr_map (bifibrantResolutionMap_fac f)

lemma bifibrantResolutionObj_hom_ext
    {X : CofibrantObject C} {Y : BifibrantObject.π C} {f g :
      BifibrantObject.toπ.obj (bifibrantResolutionObj X) ⟶ Y}
    (h : CofibrantObject.toπ.map (iBifibrantResolutionObj X) ≫
      BifibrantObject.π.ιCofibrantObject.map f =
      CofibrantObject.toπ.map (iBifibrantResolutionObj X) ≫
        BifibrantObject.π.ιCofibrantObject.map g) :
    f = g := by
  obtain ⟨Y, rfl⟩ := BifibrantObject.toπ_obj_surjective Y
  obtain ⟨f, rfl⟩ := BifibrantObject.toπ.map_surjective f
  obtain ⟨g, rfl⟩ := BifibrantObject.toπ.map_surjective g
  change toπ.map (X.iBifibrantResolutionObj ≫ BifibrantObject.ιCofibrantObject.map f) =
    toπ.map (X.iBifibrantResolutionObj ≫ BifibrantObject.ιCofibrantObject.map g) at h
  rw [CofibrantObject.toπ_map_eq_iff,
    CofibrantObject.homRel_iff_rightHomotopyRel,
    ← RightHomotopyClass.mk_eq_mk_iff] at h
  rw [BifibrantObject.toπ_map_eq_iff,
    BifibrantObject.homRel_iff_rightHomotopyRel,
    ← RightHomotopyClass.mk_eq_mk_iff]
  apply (RightHomotopyClass.bijective_precomp_of_cofibration_of_weakEquivalence
    _ (ι.map (iBifibrantResolutionObj X))).1
  simpa only [ObjectProperty.ι_obj, ObjectProperty.ιOfLE_obj_obj, ObjectProperty.ι_map,
    RightHomotopyClass.precomp_mk] using h

@[simps]
noncomputable def bifibrantResolution : CofibrantObject C ⥤ BifibrantObject.π C where
  obj X := BifibrantObject.toπ.obj (bifibrantResolutionObj X)
  map f := BifibrantObject.toπ.map (bifibrantResolutionMap f)
  map_id X := by
    apply bifibrantResolutionObj_hom_ext
    simp only [bifibrantResolutionMap_fac', CategoryTheory.Functor.map_id,
      Category.id_comp]
    exact (Category.comp_id _).symm
  map_comp {X₁ X₂ X₃} f g := by
    apply bifibrantResolutionObj_hom_ext
    simp

noncomputable def π.bifibrantResolution :
    CofibrantObject.π C ⥤ BifibrantObject.π C :=
  CategoryTheory.Quotient.lift _ CofibrantObject.bifibrantResolution (by
    intro X Y f g h
    dsimp
    apply bifibrantResolutionObj_hom_ext
    simp only [bifibrantResolutionMap_fac', toπ_map_eq h])

@[simp]
lemma π.bifibrantResolution_obj (X : CofibrantObject C) :
    π.bifibrantResolution.obj (CofibrantObject.toπ.obj X) =
      BifibrantObject.toπ.obj (bifibrantResolutionObj X) := rfl

@[simp]
lemma π.bifibrantResolution_map {X Y : CofibrantObject C} (f : X ⟶ Y) :
    π.bifibrantResolution.map (CofibrantObject.toπ.map f) =
      BifibrantObject.toπ.map (bifibrantResolutionMap f) := rfl

noncomputable def π.adj.unit :
    𝟭 (π C) ⟶ bifibrantResolution ⋙ BifibrantObject.π.ιCofibrantObject :=
  Quotient.natTransLift _
    { app X := toπ.map (iBifibrantResolutionObj X)
      naturality _ _ f := (bifibrantResolutionMap_fac' f).symm }

lemma π.adj.unit_app (X : CofibrantObject C) :
    π.adj.unit.app (toπ.obj X) =
      toπ.map (iBifibrantResolutionObj X) := rfl

noncomputable def π.adj.counit' :
    𝟭 (BifibrantObject.π C) ⟶ BifibrantObject.π.ιCofibrantObject ⋙ bifibrantResolution :=
  Quotient.natTransLift _
    { app X := BifibrantObject.toπ.map (iBifibrantResolutionObj (.mk X.obj))
      naturality X₁ X₂ f := BifibrantObject.toπ.congr_map
        (bifibrantResolutionMap_fac (f : .mk X₁.obj ⟶ .mk X₂.obj )).symm }

lemma π.adj.counit'_app (X : BifibrantObject C) :
    π.adj.counit'.app (BifibrantObject.toπ.obj X) =
      BifibrantObject.toπ.map (iBifibrantResolutionObj (.mk X.obj)) := rfl

instance (X : BifibrantObject.π C) : IsIso (π.adj.counit'.app X) := by
  obtain ⟨X, rfl⟩ := BifibrantObject.toπ_obj_surjective X
  rw [π.adj.counit'_app]
  have : WeakEquivalence (C := BifibrantObject C) ((mk X.obj).iBifibrantResolutionObj) := by
    rw [weakEquivalence_iff_ι_map]
    change WeakEquivalence (ι.map (CofibrantObject.mk X.obj).iBifibrantResolutionObj)
    infer_instance
  infer_instance

instance : IsIso (π.adj.counit' (C := C)) := NatIso.isIso_of_isIso_app _

noncomputable def π.adj.counitIso :
    BifibrantObject.π.ιCofibrantObject ⋙ bifibrantResolution ≅ 𝟭 (BifibrantObject.π C) :=
  (asIso π.adj.counit').symm

lemma π.adj.counitIso_inv_app (X : BifibrantObject C) :
    π.adj.counitIso.inv.app (BifibrantObject.toπ.obj X) =
      BifibrantObject.toπ.map (iBifibrantResolutionObj (.mk X.obj)) := rfl

noncomputable def π.adj :
    π.bifibrantResolution (C := C) ⊣ BifibrantObject.π.ιCofibrantObject where
  unit := π.adj.unit
  counit := π.adj.counitIso.hom
  left_triangle_components X := by
    obtain ⟨X, rfl⟩ := toπ_obj_surjective X
    rw [← cancel_mono (π.adj.counitIso.inv.app _), Category.assoc, Iso.hom_inv_id_app]
    dsimp
    apply bifibrantResolutionObj_hom_ext
    rw [Category.comp_id, Category.id_comp, π.adj.unit_app,
      bifibrantResolution_map, π.adj.counitIso_inv_app,
      bifibrantResolutionMap_fac']
    rfl
  right_triangle_components X := by
    obtain ⟨X, rfl⟩ := BifibrantObject.toπ_obj_surjective X
    rw [← cancel_mono (BifibrantObject.π.ιCofibrantObject.map (π.adj.counitIso.inv.app _)),
      Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    simp only [Functor.id_obj, Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id,
      Category.id_comp]
    rfl

end CofibrantObject

namespace FibrantObject

variable {C}

lemma exists_bifibrant (X : FibrantObject C) :
    ∃ (Y : BifibrantObject C) (p : BifibrantObject.ιFibrantObject.obj Y ⟶ X),
      Fibration (ι.map p) ∧ WeakEquivalence (ι.map p) := by
  have h := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C)
      (initial.to X.obj)
  have := isFibrant_of_fibration h.p
  have : IsCofibrant h.Z := by
    rw [isCofibrant_iff_of_isInitial h.i initialIsInitial]
    infer_instance
  exact ⟨BifibrantObject.mk h.Z, h.p, inferInstanceAs (Fibration h.p),
    inferInstanceAs (WeakEquivalence h.p)⟩

-- TODO: dualize

end FibrantObject

namespace CofibrantObject

instance : (weakEquivalences (CofibrantObject C)).HasQuotient (homRel C) where
  iff X Y f g h := by
    rw [← weakEquivalence_iff, ← weakEquivalence_iff, weakEquivalence_iff_ι_map,
      weakEquivalence_iff_ι_map]
    obtain ⟨P, ⟨h⟩⟩ := h
    apply h.weakEquivalence_iff
  compClosure_eq_self := compClosure_homRel C

instance : CategoryWithWeakEquivalences (CofibrantObject.π C) where
  weakEquivalences := (weakEquivalences _).quotient _

variable {C} in
lemma weakEquivalence_toπ_map_iff {X Y : CofibrantObject C} (f : X ⟶ Y) :
    WeakEquivalence (toπ.map f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  apply MorphismProperty.quotient_iff

def toπLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (CofibrantObject C))
      (weakEquivalences (CofibrantObject.π C)) where
  functor := toπ
  map _ _ _ h := by
    simp only [← weakEquivalence_iff] at h
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff,
      weakEquivalence_toπ_map_iff]

lemma factorsThroughLocalization :
    (homRel C).FactorsThroughLocalization (weakEquivalences (CofibrantObject C)) := by
  rintro X Y f g h
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good
  let L := (weakEquivalences (CofibrantObject C)).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map (homMk P.p₀) = L.map (homMk P.p₁) by
    simp only [← h.h₀, ← h.h₁]
    change L.map (homMk h.h ≫ homMk P.p₀) = L.map (homMk h.h ≫ homMk P.p₁)
    simp only [Functor.map_comp, this]
  have := Localization.inverts L (weakEquivalences _) (homMk P.ι) (by
    rw [← weakEquivalence_iff]
    rw [weakEquivalence_iff_ι_map]
    change WeakEquivalence P.ι
    infer_instance)
  simp only [← cancel_epi (L.map (homMk P.ι)), ← L.map_comp, homMk_homMk, P.ι_p₀, P.ι_p₁]

instance : (toπLocalizerMorphism C).IsLocalizedEquivalence := by
  apply (factorsThroughLocalization C).isLocalizedEquivalence
  apply MorphismProperty.eq_inverseImage_quotientFunctor

instance {D : Type*} [Category D] (L : CofibrantObject.π C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    (toπ ⋙ L).IsLocalization (weakEquivalences _) := by
  change ((toπLocalizerMorphism C).functor ⋙ L).IsLocalization (weakEquivalences _)
  infer_instance

end CofibrantObject

namespace FibrantObject

-- dualize

end FibrantObject


namespace CofibrantObject

variable {C}

def π.exists_resolution (X : C) :
    ∃ (X' : C) (_ : IsCofibrant X') (p : X' ⟶ X), Fibration p ∧ WeakEquivalence p := by
  have h := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C)
    (initial.to X)
  refine ⟨h.Z, ?_, h.p, inferInstance, inferInstance⟩
  rw [isCofibrant_iff_of_isInitial h.i initialIsInitial]
  infer_instance

noncomputable def π.resolutionObj (X : C) : CofibrantObject C :=
    ⟨(exists_resolution X).choose,
      (exists_resolution X).choose_spec.choose⟩

noncomputable def π.pResolutionObj (X : C) : ι.obj (resolutionObj X) ⟶ X :=
  (exists_resolution X).choose_spec.choose_spec.choose

instance (X : C) : Fibration (π.pResolutionObj X) :=
  (π.exists_resolution X).choose_spec.choose_spec.choose_spec.1

instance (X : C) : WeakEquivalence (π.pResolutionObj X) :=
  (π.exists_resolution X).choose_spec.choose_spec.choose_spec.2

def π.exists_resolution_map {X Y : C} (f : X ⟶ Y) :
    ∃ (g : resolutionObj X ⟶ resolutionObj Y),
      ι.map g ≫ pResolutionObj Y = pResolutionObj X ≫ f := by
  have sq : CommSq (initial.to _) (initial.to _) (pResolutionObj Y)
    (pResolutionObj X ≫ f) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_right⟩

noncomputable def π.resolutionMap {X Y : C} (f : X ⟶ Y) :
    resolutionObj X ⟶ resolutionObj Y :=
  (exists_resolution_map f).choose

@[reassoc (attr := simp)]
lemma π.resolutionMap_fac {X Y : C} (f : X ⟶ Y) :
    ι.map (resolutionMap f) ≫ pResolutionObj Y =
      pResolutionObj X ≫ f :=
  (exists_resolution_map f).choose_spec

@[simp]
lemma π.weakEquivalence_resolutionMap_iff {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence (resolutionMap f) ↔ WeakEquivalence f := by
  rw [weakEquivalence_iff_ι_map,
    ← weakEquivalence_postcomp_iff _ (pResolutionObj Y),
    π.resolutionMap_fac, weakEquivalence_precomp_iff]

lemma π.resolutionObj_hom_ext {X : CofibrantObject C} {Y : C} {f g : X ⟶ resolutionObj Y}
    (h : LeftHomotopyRel (ι.map f ≫ pResolutionObj Y) (ι.map g ≫ pResolutionObj Y)) :
    toπ.map f = toπ.map g := by
  apply toπ_map_eq
  rw [homRel_iff_rightHomotopyRel]
  apply LeftHomotopyRel.rightHomotopyRel
  rw [← LeftHomotopyClass.mk_eq_mk_iff] at h ⊢
  exact (LeftHomotopyClass.bijective_postcomp_of_fibration_of_weakEquivalence
    (X := X.obj) (g := pResolutionObj Y)).1 h

noncomputable def π.resolution : C ⥤ CofibrantObject.π C where
  obj X := toπ.obj (resolutionObj X)
  map f := toπ.map (resolutionMap f)
  map_id X := by
    rw [← toπ.map_id]
    apply resolutionObj_hom_ext
    rw [resolutionMap_fac, Category.comp_id, ι.map_id, Category.id_comp]
    exact .refl _
  map_comp {X₁ X₂ X₃} f g := by
    rw [← toπ.map_comp]
    apply resolutionObj_hom_ext
    rw [resolutionMap_fac, ι.map_comp_assoc, resolutionMap_fac, resolutionMap_fac_assoc]
    exact .refl _

variable (C) in
@[simps]
noncomputable def π.localizerMorphismResolution :
    LocalizerMorphism (weakEquivalences C)
      (weakEquivalences (CofibrantObject.π C)) where
  functor := π.resolution
  map _ _ _ h := by
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff, π.resolution,
      weakEquivalence_toπ_map_iff, weakEquivalence_resolutionMap_iff] using h

@[simps]
noncomputable def π.ιCompResolutionNatTrans : ι ⋙ π.resolution (C := C) ⟶ toπ where
  app X := toπ.map (pResolutionObj (ι.obj X))
  naturality _ _ f := toπ.congr_map (π.resolutionMap_fac (ι.map f))

instance π.weakEquivalence_ιCompResolutionNatTrans_app (X : CofibrantObject C) :
    WeakEquivalence (ιCompResolutionNatTrans.app X) := by
  dsimp
  rw [weakEquivalence_toπ_map_iff, weakEquivalence_iff_ι_map]
  dsimp
  infer_instance

instance {D : Type*} [Category D] (L : CofibrantObject.π C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    IsIso (whiskerRight π.ιCompResolutionNatTrans L) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  apply Localization.inverts L (weakEquivalences _)
  rw [← weakEquivalence_iff]
  infer_instance

section

variable {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]

def π.toLocalization : π C ⥤ D :=
  CategoryTheory.Quotient.lift _ (ι ⋙ L) (by
    have : L.IsLocalization (weakEquivalences C) := inferInstance
    sorry)

def π.toπCompToLocalizationIso : toπ ⋙ toLocalization L ≅ ι ⋙ L := Iso.refl _

end

end CofibrantObject

namespace FibrantObject

-- dualize

end FibrantObject

namespace BifibrantObject

@[simps]
def ιCofibrantObjectLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (BifibrantObject C))
      (weakEquivalences (CofibrantObject C)) where
  functor := ιCofibrantObject
  map _ _ _ h := h

@[simps]
def ιFibrantObjectLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (BifibrantObject C))
      (weakEquivalences (FibrantObject C)) where
  functor := ιFibrantObject
  map _ _ _ h := h

--instance : (ιCofibrantObjectLocalizerMorphism C).IsLocalizedEquivalence := sorry

end BifibrantObject

namespace CofibrantObject

@[simps]
def localizerMorphism : LocalizerMorphism (weakEquivalences (CofibrantObject C))
    (weakEquivalences C) where
  functor := ι
  map := by rfl

instance : (localizerMorphism C).IsLocalizedEquivalence := by
  let Hcof := (weakEquivalences (π C)).Localization
  let Lcofπ : π C ⥤ Hcof := (weakEquivalences (CofibrantObject.π C)).Q
  let Lcof : CofibrantObject C ⥤ Hcof := toπ ⋙ Lcofπ
  let H := (weakEquivalences C).Localization
  let L : C ⥤ H := (weakEquivalences C).Q
  let F := (localizerMorphism C).localizedFunctor Lcof L
  let eF : ι ⋙ L ≅ Lcof ⋙ F := CatCommSq.iso (localizerMorphism C).functor Lcof L F
  let G : H ⥤ Hcof := (π.localizerMorphismResolution C).localizedFunctor L Lcofπ
  let eG : π.resolution ⋙ Lcofπ ≅ L ⋙ G :=
    CatCommSq.iso (π.localizerMorphismResolution C).functor L Lcofπ G
  have : Localization.Lifting Lcof (weakEquivalences (CofibrantObject C)) Lcof (F ⋙ G) :=
    ⟨(Functor.associator _ _ _).symm ≪≫ isoWhiskerRight eF.symm _ ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ eG.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
        asIso (whiskerRight π.ιCompResolutionNatTrans Lcofπ) ≪≫ Iso.refl _⟩
  let I : π C ⥤ H := sorry
  have iso₁ : toπ ⋙ I ≅ ι ⋙ L := sorry
  have iso₂ : I ≅ Lcofπ ⋙ F := sorry
  let iso : π.resolution ⋙ Lcofπ ⋙ F ≅ L := by
    refine isoWhiskerLeft _ iso₂.symm ≪≫ ?_
    sorry
  have : Localization.Lifting L (weakEquivalences C) L (G ⋙ F) := ⟨
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight eG.symm _ ≪≫
      Functor.associator _ _ _ ≪≫ iso⟩
  let E : Hcof ≌ H := CategoryTheory.Equivalence.mk F G
    (Localization.liftNatIso Lcof (weakEquivalences _) Lcof Lcof _ _ (Iso.refl _))
    (Localization.liftNatIso L (weakEquivalences _) L L _ _ (Iso.refl _))
  have : F.IsEquivalence := E.isEquivalence_functor
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' (localizerMorphism C) Lcof L F

end CofibrantObject

namespace FibrantObject

-- dualize

end FibrantObject

end HomotopicalAlgebra
