/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# The strict bicategory associated to a Cat-enriched category

If `C` is a type with a `EnrichedCategory Cat C` structure, then it has hom-categories, whose
objects define 1-dimensional arrows on `C` and whose morphisms define 2-dimensional arrows between
these. The enriched category axioms equip this data with the structure of a strict bicategory.

We define a type alias `CatEnriched C` for a type `C` with a `EnrichedCategory Cat C` structure. We
provide this with an instance of a strict bicategory structure constructing
`Bicategory.Strict (CatEnriched C)`.

If `C` is a type with a `EnrichedOrdinaryCategory Cat C` structure, then it has an `Enrichred Cat C`
structure, so the previous construction would again produce a strict bicategory. However, in this
setting `C` is also given a `Category C` structure, together with an equivalence between this
category and the underlying category of the `Enriched Cat C`, and in examples the given category
structure is the preferred one.

Thus, we define a type alias `CatEnrichedOrdinary C` for a type `C` with an
`EnrichedOrdinaryCategory Cat C` structure. We provide this with an instance of a strict bicategory
structure extending the category structure provided by the given instance `Category C` constructing
`Bicategory.Strict (CatEnrichedOrdinary C)`.

-/

universe u v u' v'
namespace CategoryTheory
open Category

section
variable {C : Type*} [EnrichedCategory Cat C]

/-- A type synonym for `C`, which should come equipped with a `Cat`-enriched category structure.
This converts it to a strict bicategory where `Category (X ⟶ Y)` is `(X ⟶[Cat] Y)`. -/
def CatEnriched (C : Type*) := C

namespace CatEnriched

instance : EnrichedCategory Cat (CatEnriched C) := inferInstanceAs (EnrichedCategory Cat C)

/-- Any enriched category has an underlying category structure defined by `ForgetEnrichment`.
This is equivalent but not definitionally equal the category structure constructed here, which is
more canonically associated to the data of an `EnrichedCategory Cat` structure. -/
instance : CategoryStruct (CatEnriched C) where
  Hom X Y := X ⟶[Cat] Y
  id X := (eId Cat X).obj ⟨⟨()⟩⟩
  comp {X Y Z} f g := (eComp Cat X Y Z).obj (f, g)

theorem id_eq (X : CatEnriched C) : 𝟙 X = (eId Cat X).obj ⟨⟨()⟩⟩ := rfl

theorem comp_eq {X Y Z : CatEnriched C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = (eComp Cat X Y Z).obj (f, g) := rfl

instance {X Y : CatEnriched C} : Category (X ⟶ Y) := inferInstanceAs (Category (X ⟶[Cat] Y).α)

/-- The horizontal composition on 2-morphisms is defined using the action on arrows of the
composition bifunctor from the enriched category structure. -/
def hComp {a b c : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c}
    (η : f ⟶ f') (θ : g ⟶ g') : f ≫ g ⟶ f' ≫ g' := (eComp Cat a b c).map (η, θ)

@[simp]
theorem id_hComp_id {a b c : CatEnriched C} (f : a ⟶ b) (g : b ⟶ c) :
    hComp (𝟙 f) (𝟙 g) = 𝟙 (f ≫ g) := Functor.map_id ..

@[simp]
theorem eqToHom_hComp_eqToHom {a b c : CatEnriched C}
    {f f' : a ⟶ b} (α : f = f') {g g' : b ⟶ c} (β : g = g') :
    hComp (eqToHom α) (eqToHom β) = eqToHom (α ▸ β ▸ rfl) := by cases α; cases β; simp

/-- The interchange law for horizontal and vertical composition of 2-cells in a bicategory. -/
@[simp]
theorem hComp_comp {a b c : CatEnriched C} {f₁ f₂ f₃ : a ⟶ b} {g₁ g₂ g₃ : b ⟶ c}
    (η : f₁ ⟶ f₂) (η' : f₂ ⟶ f₃) (θ : g₁ ⟶ g₂) (θ' : g₂ ⟶ g₃) :
    hComp η θ ≫ hComp η' θ' = hComp (η ≫ η') (θ ≫ θ') :=
  ((eComp Cat a b c).map_comp (Y := (_, _)) (_, _) (_, _)).symm

/-- The action on objects of the `EnrichedCategory Cat` coherences proves the category axioms. -/
instance : Category (CatEnriched C) where
  id_comp {X Y} f := congrArg (·.obj f) (e_id_comp (V := Cat) X Y)
  comp_id {X Y} f := congrArg (·.obj f) (e_comp_id (V := Cat) X Y)
  assoc {X Y Z W} f g h := congrArg (·.obj (f, g, h)) (e_assoc (V := Cat) X Y Z W)

/-- The category instance on `CatEnriched C` promotes it to a `Cat` enriched ordinary
category. -/
instance : EnrichedOrdinaryCategory Cat (CatEnriched C) where
  homEquiv := Cat.fromChosenTerminalEquiv.symm
  homEquiv_comp _ _ := (Equiv.symm_apply_eq Cat.fromChosenTerminalEquiv).mpr rfl
  homEquiv_id _ := (Equiv.symm_apply_eq Cat.fromChosenTerminalEquiv).mpr rfl

theorem id_hComp_heq {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    HEq (hComp (𝟙 (𝟙 a)) η) η := by
  rw [id_eq, ← Functor.map_id]
  exact congr_arg_heq (·.map η) (e_id_comp (V := Cat) a b)

theorem id_hComp {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    hComp (𝟙 (𝟙 a)) η = eqToHom (id_comp f) ≫ η ≫ eqToHom (id_comp f').symm := by
  simp [← heq_eq_eq, id_hComp_heq]

theorem hComp_id_heq {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    HEq (hComp η (𝟙 (𝟙 b))) η := by
  rw [id_eq, ← Functor.map_id]
  exact congr_arg_heq (·.map η) (e_comp_id (V := Cat) a b)

theorem hComp_id {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    hComp η (𝟙 (𝟙 b)) = eqToHom (comp_id f) ≫ η ≫ eqToHom (comp_id f').symm := by
  simp [← heq_eq_eq, hComp_id_heq]

theorem hComp_assoc_heq {a b c d : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') :
    HEq (hComp (hComp η θ) κ) (hComp η (hComp θ κ)) :=
  congr_arg_heq (·.map (X := (_, _, _)) (Y := (_, _, _)) (η, θ, κ)) (e_assoc (V := Cat) a b c d)

theorem hComp_assoc {a b c d : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') :
    hComp (hComp η θ) κ =
      eqToHom (assoc f g h) ≫ hComp η (hComp θ κ) ≫ eqToHom (assoc f' g' h').symm := by
  simp [← heq_eq_eq, hComp_assoc_heq]

instance : Bicategory (CatEnriched C) where
  homCategory := inferInstance
  whiskerLeft {_ _ _} f {_ _} η := hComp (𝟙 f) η
  whiskerRight η h := hComp η (𝟙 h)
  associator f g h := eqToIso (assoc f g h)
  leftUnitor f := eqToIso (id_comp f)
  rightUnitor f := eqToIso (comp_id f)
  id_whiskerLeft := id_hComp
  comp_whiskerLeft := by simp [← id_hComp_id, hComp_assoc]
  whiskerRight_id := hComp_id
  whiskerRight_comp := by simp [hComp_assoc]
  whisker_assoc := by simp [hComp_assoc]
  pentagon f g h i := by
    generalize_proofs h1 h2 h3 h4; revert h1 h2 h3 h4
    generalize (f ≫ g) ≫ h = x, (g ≫ h) ≫ i = w
    rintro rfl _ rfl _; simp
  triangle f g := by
    generalize_proofs h1 h2 h3; revert h1 h2 h3
    generalize 𝟙 _ ≫ g = g, f ≫ 𝟙 _ = f
    rintro _ rfl rfl; simp

/-- As the associator and left and right unitors are defined as eqToIso of category axioms, the
bicategory structure on `CatEnriched C` is strict. -/
instance : Bicategory.Strict (CatEnriched C) where

end CatEnriched

end

section
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory Cat.{v', u'} C]

/-- A type synonym for `C`, which should come equipped with a `Cat`-enriched category structure.
This converts it to a strict bicategory where `Category (X ⟶ Y)` is `(X ⟶[Cat] Y)`. -/
def CatEnrichedOrdinary (C : Type*) := C

namespace CatEnrichedOrdinary

instance : Category (CatEnrichedOrdinary C) := inferInstanceAs (Category C)

instance : EnrichedCategory Cat (CatEnrichedOrdinary C) := inferInstanceAs (EnrichedCategory Cat C)

instance : EnrichedOrdinaryCategory Cat (CatEnrichedOrdinary C) :=
  inferInstanceAs (EnrichedOrdinaryCategory Cat C)

/-- The forgetful map from the type alias associated to `EnrichedOrdinaryCategory Cat C` and the
type alias associated to `EnrichedCategory Cat C` is the identity on underlying types. -/
def toBase (a : CatEnrichedOrdinary C) : CatEnriched C := a

/-- The hom-types in a `Cat`-enriched ordinary category are equivalent to the types underlying the
hom-categories. -/
def homEquiv {a b : CatEnrichedOrdinary C} : (a ⟶ b) ≃ (a.toBase ⟶ b.toBase) :=
  (eHomEquiv (V := Cat)).trans Cat.fromChosenTerminalEquiv

theorem homEquiv_id {a : CatEnrichedOrdinary C} : homEquiv (𝟙 a) = 𝟙 a.toBase := by
  unfold homEquiv
  simp only [Equiv.trans_apply]
  rw [eHomEquiv_id]
  rfl

theorem homEquiv_comp {a b c : CatEnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c) :
    homEquiv (f ≫ g) = homEquiv f ≫ homEquiv g := by
  unfold homEquiv
  simp only [Equiv.trans_apply]
  rw [eHomEquiv_comp]
  rfl

/-- The 2-cells between a parallel pair of 1-cells `f g` in `CatEnrichedOrdinary C` are defined to
be the morphisms in the hom-categories provided by the `EnrichedCategory Cat C` structure between
the corresponding objects. -/
structure Hom {X Y : CatEnrichedOrdinary C} (f g : X ⟶ Y) where mk' ::
  /-- A 2-cell from `f` to `g` is a 2-cell from `homEquiv f` to `homEquiv g`. -/
  base' : homEquiv f ⟶ homEquiv g

instance {X Y : CatEnrichedOrdinary C} : Quiver (X ⟶ Y) where
  Hom f g := Hom f g

/-- A 2-cell in `CatEnrichedOrdinary C` has a corresponding "base" 2-cell in `CatEnriched C`. -/
def Hom.base {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : f ⟶ g) :
    homEquiv f ⟶ homEquiv g := α.base'

/-- A 2-cell in `CatEnriched C` can be "made" into a 2-cell in `CatEnrichedOrdinary C`. -/
def Hom.mk {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : homEquiv f ⟶ homEquiv g) :
    f ⟶ g := .mk' α

@[simp] theorem mk_base {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : f ⟶ g) :
    Hom.mk (Hom.base α) = α := rfl

@[simp] theorem base_mk {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : homEquiv f ⟶ homEquiv g) :
    Hom.base (Hom.mk α) = α := rfl

instance {X Y : CatEnrichedOrdinary C} : CategoryStruct (X ⟶ Y) where
  id f := Hom.mk (𝟙 (homEquiv f))
  comp α β := Hom.mk (Hom.base α ≫ Hom.base β)

theorem Hom.id_eq {X Y : CatEnrichedOrdinary C} (f : X ⟶ Y) :
    𝟙 f = Hom.mk (𝟙 (homEquiv f)) := rfl

@[simp] theorem Hom.base_id {X Y : CatEnrichedOrdinary C} (f : X ⟶ Y) :
    Hom.base (𝟙 f) = 𝟙 (homEquiv f) := rfl

theorem Hom.comp_eq {X Y : CatEnrichedOrdinary C} {f g h : X ⟶ Y}
    (α : f ⟶ g) (β : g ⟶ h) : (α ≫ β) = Hom.mk (Hom.base α ≫ Hom.base β) := rfl

@[simp] theorem Hom.base_comp {X Y : CatEnrichedOrdinary C} {f g h : X ⟶ Y}
    (α : f ⟶ g) (β : g ⟶ h) : Hom.base (α ≫ β) = Hom.base α ≫ Hom.base β := rfl

theorem Hom.mk_comp {X Y : CatEnrichedOrdinary C} {f g h : X ⟶ Y}
    (α : homEquiv f ⟶ homEquiv g) (β : homEquiv g ⟶ homEquiv h) :
    Hom.mk (α ≫ β) = Hom.mk α ≫ Hom.mk β := rfl

@[ext] theorem Hom.ext {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α β : f ⟶ g)
    (H : Hom.base α = Hom.base β) : α = β := by cases α; cases β; cases H; rfl

/-- A `Cat`-enriched ordinary category comes with hom-categories `X ⟶[Cat] Y` whose underlying type
of objects is equivalent to the type `X ⟶ Y` defined by the category structure on `C`. The following
definition transfers the category structure to the latter type of objects. -/
instance {X Y : CatEnrichedOrdinary C} : Category (X ⟶ Y) where

@[simp] theorem Hom.base_eqToHom {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : f = g) :
    Hom.base (eqToHom α) = eqToHom (congrArg _ α) := by cases α; rfl

/-- The horizontal composition on 2-morphisms is defined using the action on arrows of the
composition bifunctor from the enriched category structure. -/
def hComp {a b c : CatEnrichedOrdinary C} {f f' : a ⟶ b} {g g' : b ⟶ c}
    (η : f ⟶ f') (θ : g ⟶ g') : f ≫ g ⟶ f' ≫ g' :=
  .mk <|
    eqToHom (homEquiv_comp f g) ≫ CatEnriched.hComp (Hom.base η) (Hom.base θ) ≫
    eqToHom (homEquiv_comp f' g').symm

@[simp]
theorem id_hComp_id {a b c : CatEnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c) :
    hComp (𝟙 f) (𝟙 g) = 𝟙 (f ≫ g) := by simp [hComp, Hom.id_eq]

@[simp]
theorem eqToHom_hComp_eqToHom {a b c : CatEnrichedOrdinary C}
    {f f' : a ⟶ b} (α : f = f') {g g' : b ⟶ c} (β : g = g') :
    hComp (eqToHom α) (eqToHom β) = eqToHom (α ▸ β ▸ rfl) := by cases α; cases β; simp

/-- The interchange law for horizontal and vertical composition of 2-cells in a bicategory. -/
@[simp]
theorem hComp_comp {a b c : CatEnrichedOrdinary C} {f₁ f₂ f₃ : a ⟶ b} {g₁ g₂ g₃ : b ⟶ c}
    (η : f₁ ⟶ f₂) (η' : f₂ ⟶ f₃) (θ : g₁ ⟶ g₂) (θ' : g₂ ⟶ g₃) :
    hComp η θ ≫ hComp η' θ' = hComp (η ≫ η') (θ ≫ θ') := by
  simp [hComp, ← CatEnriched.hComp_comp, Hom.comp_eq]

theorem id_hComp {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f') :
    hComp (𝟙 (𝟙 a)) η = eqToHom (id_comp f) ≫ η ≫ eqToHom (id_comp f').symm := by
  ext
  simp only [hComp, Hom.base_id, base_mk, ← heq_eq_eq, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rw [homEquiv_id]; simp [CatEnriched.id_hComp_heq]

theorem id_hComp_heq {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f') :
    HEq (hComp (𝟙 (𝟙 a)) η) η := by simp [id_hComp]

theorem hComp_id {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f') :
    hComp η (𝟙 (𝟙 b)) = eqToHom (comp_id f) ≫ η ≫ eqToHom (comp_id f').symm := by
  ext
  simp only [hComp, Hom.base_id, base_mk, ← heq_eq_eq, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rw [homEquiv_id]
  simp [CatEnriched.hComp_id_heq]

theorem hComp_id_heq {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f') :
    HEq (hComp η (𝟙 (𝟙 b))) η := by simp [hComp_id]

theorem id_eq_eqToHom {C} [Category C] (X : C) : 𝟙 X = eqToHom rfl := rfl

theorem hComp_assoc {a b c d : CatEnrichedOrdinary C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') :
    hComp (hComp η θ) κ =
      eqToHom (assoc f g h) ≫ hComp η (hComp θ κ) ≫ eqToHom (assoc f' g' h').symm := by
  ext
  simp only [hComp, base_mk, Hom.base_comp, Hom.base_eqToHom,
    ← heq_eq_eq, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  conv => enter [1,2]; exact ((id_comp _).trans (comp_id _)).symm
  conv => enter [2,1]; exact ((id_comp _).trans (comp_id _)).symm
  iterate 4 rw [← CatEnriched.hComp_comp, id_eq_eqToHom, CatEnriched.eqToHom_hComp_eqToHom]
  simp [CatEnriched.hComp_assoc_heq]

theorem hComp_assoc_heq {a b c d : CatEnrichedOrdinary C}
    {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d} (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') :
    HEq (hComp (hComp η θ) κ) (hComp η (hComp θ κ)) := by simp [hComp_assoc]

instance : Bicategory (CatEnrichedOrdinary C) where
  homCategory := inferInstance
  whiskerLeft {_ _ _} f {_ _} η := hComp (𝟙 f) η
  whiskerRight η h := hComp η (𝟙 h)
  associator f g h := eqToIso (assoc f g h)
  leftUnitor f := eqToIso (id_comp f)
  rightUnitor f := eqToIso (comp_id f)
  id_whiskerLeft := by simp [id_hComp]
  comp_whiskerLeft := by simp [← hComp_assoc]
  whiskerRight_id := by simp [hComp_id]
  whiskerRight_comp := by simp [hComp_assoc]
  whisker_assoc := by simp [hComp_assoc]
  pentagon := by simp [id_eq_eqToHom, -eqToHom_refl]
  triangle := by simp [id_eq_eqToHom, -eqToHom_refl]

/-- As the associator and left and right unitors are defined as eqToIso of category axioms, the
bicategory structure on `CatEnrichedOrdinary C` is strict. -/
instance : Bicategory.Strict (CatEnrichedOrdinary C) where

end CatEnrichedOrdinary

end

end CategoryTheory
