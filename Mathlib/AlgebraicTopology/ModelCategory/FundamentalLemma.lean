/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
import Mathlib.CategoryTheory.Localization.Predicate

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

abbrev ιCofibrantObject : BifibrantObject C ⥤ CofibrantObject C :=
  ObjectProperty.ιOfLE (bifibrantObjects_le_cofibrantObject C)

abbrev ιFibrantObject : BifibrantObject C ⥤ FibrantObject C :=
  ObjectProperty.ιOfLE (bifibrantObjects_le_fibrantObject C)

instance (X : BifibrantObject C) :
    IsFibrant (BifibrantObject.ιCofibrantObject.obj X).obj := X.2.2

instance (X : BifibrantObject C) :
    IsCofibrant (BifibrantObject.ιFibrantObject.obj X).obj := X.2.1

def ιCofibrantObjectπ : π C ⥤ CofibrantObject.π C :=
  CategoryTheory.Quotient.lift _
    (ιCofibrantObject ⋙ CofibrantObject.toπ)
    (fun _ _ _ _ h ↦ CategoryTheory.Quotient.sound _ h)

def ιFibrantObjectπ : π C ⥤ FibrantObject.π C :=
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
      BifibrantObject.ιCofibrantObjectπ.map
        (BifibrantObject.toπ.map (bifibrantResolutionMap f)) =
    toπ.map f ≫ toπ.map X₂.iBifibrantResolutionObj :=
  toπ.congr_map (bifibrantResolutionMap_fac f)

lemma bifibrantResolutionObj_hom_ext
    {X : CofibrantObject C} {Y : BifibrantObject.π C} {f g :
      BifibrantObject.toπ.obj (bifibrantResolutionObj X) ⟶ Y}
    (h : CofibrantObject.toπ.map (iBifibrantResolutionObj X) ≫
      BifibrantObject.ιCofibrantObjectπ.map f =
      CofibrantObject.toπ.map (iBifibrantResolutionObj X) ≫
        BifibrantObject.ιCofibrantObjectπ.map g) :
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

end FibrantObject

end HomotopicalAlgebra
