/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl
-/
module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Category.Quiv

/-!
# The category of refl quivers

The category `ReflQuiv` of (bundled) reflexive quivers, and the free/forgetful adjunction between
`Cat` and `ReflQuiv`.
-/

@[expose] public section

namespace CategoryTheory
universe v u v₁ v₂ u₁ u₂

/-- Category of refl quivers. -/
@[nolint checkUnivs]
def ReflQuiv :=
  Bundled ReflQuiver.{v + 1, u}

namespace ReflQuiv

instance : CoeSort ReflQuiv (Type u) where coe := Bundled.α

instance (C : ReflQuiv.{v, u}) : ReflQuiver.{v + 1, u} C := C.str

/-- The underlying quiver of a reflexive quiver -/
def toQuiv (C : ReflQuiv.{v, u}) : Quiv.{v, u} := Quiv.of C.α

/-- Construct a bundled `ReflQuiv` from the underlying type and the typeclass. -/
def of (C : Type u) [ReflQuiver.{v + 1} C] : ReflQuiv.{v, u} := Bundled.of C

instance : Inhabited ReflQuiv := ⟨ReflQuiv.of (Discrete default)⟩

@[simp] theorem of_val (C : Type u) [ReflQuiver C] : (ReflQuiv.of C) = C := rfl

/-- Category structure on `ReflQuiv` -/
instance category : LargeCategory.{max v u} ReflQuiv.{v, u} where
  Hom C D := ReflPrefunctor C D
  id C := ReflPrefunctor.id C
  comp F G := ReflPrefunctor.comp F G

theorem id_eq_id (X : ReflQuiv) : 𝟙 X = 𝟭rq X := rfl
theorem comp_eq_comp {X Y Z : ReflQuiv} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙rq G := rfl

@[simp]
lemma id_obj (X : ReflQuiv) (x : X) : (ReflPrefunctor.toPrefunctor (𝟙 X)).obj x = x := rfl

@[simp]
lemma id_map {X : ReflQuiv} {x y : X} (f : x ⟶ y) :
    (ReflPrefunctor.toPrefunctor (𝟙 X)).map f = f := rfl

@[simp]
lemma comp_obj {X Y Z : ReflQuiv} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).obj x = g.obj (f.obj x) := rfl

@[simp]
lemma comp_map {X Y Z : ReflQuiv} (f : X ⟶ Y) (g : Y ⟶ Z) {x y : X} (a : x ⟶ y) :
    (f ≫ g).map a = g.map (f.map a) := rfl

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forget : Cat.{v, u} ⥤ ReflQuiv.{v, u} where
  obj C := ReflQuiv.of C
  map F := F.toReflPrefunctor

theorem forget_faithful {C D : Cat.{v, u}} (F G : C ⥤ D)
    (hyp : forget.map F = forget.map G) : F = G := by
  cases F; cases G; cases hyp; rfl

instance forget.Faithful : Functor.Faithful (forget) where
  map_injective := fun hyp ↦ forget_faithful _ _ hyp

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forgetToQuiv : ReflQuiv.{v, u} ⥤ Quiv.{v, u} where
  obj V := Quiv.of V
  map F := F.toPrefunctor

theorem forgetToQuiv_faithful {V W : ReflQuiv} (F G : V ⥤rq W)
    (hyp : forgetToQuiv.map F = forgetToQuiv.map G) : F = G := by
  cases F; cases G; cases hyp; rfl

instance forgetToQuiv.Faithful : Functor.Faithful forgetToQuiv where
  map_injective := fun hyp ↦ forgetToQuiv_faithful _ _ hyp

theorem forget_forgetToQuiv : forget ⋙ forgetToQuiv = Quiv.forget := rfl

/-- An isomorphism of quivers lifts to an isomorphism of reflexive quivers given a suitable
compatibility with the identities. -/
def isoOfQuivIso {V W : Type u} [ReflQuiver V] [ReflQuiver W]
    (e : Quiv.of V ≅ Quiv.of W)
    (h_id : ∀ (X : V), e.hom.map (𝟙rq X) = ReflQuiver.id (obj := W) (e.hom.obj X)) :
    ReflQuiv.of V ≅ ReflQuiv.of W where
  hom := ReflPrefunctor.mk e.hom h_id
  inv := ReflPrefunctor.mk e.inv
    (fun Y => (Quiv.homEquivOfIso e).injective (by simp [Quiv.hom_map_inv_map_of_iso, h_id]))
  hom_inv_id := by
    apply forgetToQuiv.map_injective
    exact e.hom_inv_id
  inv_hom_id := by
    apply forgetToQuiv.map_injective
    exact e.inv_hom_id

/-- Compatible equivalences of types and hom-types induce an isomorphism of reflexive quivers. -/
def isoOfEquiv {V W : Type u} [ReflQuiver V] [ReflQuiver W] (e : V ≃ W)
    (he : ∀ (X Y : V), (X ⟶ Y) ≃ (e X ⟶ e Y))
    (h_id : ∀ (X : V), he _ _ (𝟙rq X) = ReflQuiver.id (obj := W) (e X)) :
    ReflQuiv.of V ≅ ReflQuiv.of W := isoOfQuivIso (Quiv.isoOfEquiv e he) h_id

end ReflQuiv

namespace ReflPrefunctor

/-- A refl prefunctor can be promoted to a functor if it respects composition. -/
def toFunctor {C D : Cat} (F : (ReflQuiv.of C) ⟶ (ReflQuiv.of D))
    (hyp : ∀ {X Y Z : ↑C} (f : X ⟶ Y) (g : Y ⟶ Z),
      F.map (CategoryStruct.comp (obj := C) f g) =
        CategoryStruct.comp (obj := D) (F.map f) (F.map g)) : C ⥤ D where
  obj := F.obj
  map := F.map
  map_id := F.map_id
  map_comp := hyp

end ReflPrefunctor

namespace Cat

variable (V : Type*) [ReflQuiver V]

/-- The hom relation that identifies the specified reflexivity arrows with the nil paths -/
inductive FreeReflRel : (X Y : Paths V) → (f g : X ⟶ Y) → Prop
  | mk {X : V} : FreeReflRel X X (Quiver.Hom.toPath (𝟙rq X)) .nil

/-- A reflexive quiver generates a free category, defined as a quotient of the free category
on its underlying quiver (called the "path category") by the hom relation that uses the specified
reflexivity arrows as the identity arrows. -/
def FreeRefl := Quotient (C := Paths V) (FreeReflRel V)

namespace FreeRefl

variable {V}

instance : Category (FreeRefl V) :=
  inferInstanceAs (Category (Quotient _))

/-- Constructor for objects in the free category on a reflexive quiver. -/
def mk (v : V) : FreeRefl V := (Quotient.functor _).obj v

/-- Induction principle for the objects of the free category on a reflexive quiver. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def induction {motive : FreeRefl V → Sort*} (mk : ∀ v, motive (mk v)) (x : FreeRefl V) :
    motive x :=
  mk _

variable (V) in
/-- The quotient functor associated to a quotient category defines a natural map from the free
category on the underlying quiver of a refl quiver to the free category on the reflexive quiver. -/
def quotientFunctor : Paths V ⥤ FreeRefl V :=
  Quotient.functor (C := Paths V) (FreeReflRel (V := V))

instance : (FreeRefl.quotientFunctor V).Full :=
  Quotient.full_functor _

/-- Constructor for morphisms in `FreeRefl`. -/
def homMk {v w : V} (f : v ⟶ w) : mk v ⟶ mk w := (quotientFunctor V).map f.toPath

@[simp]
lemma homMk_id (v : V) : homMk (𝟙rq v) = 𝟙 _ :=
  Quotient.sound _ ⟨⟩

@[simp]
lemma quotientFunctor_map_nil (x : Paths V) :
    (quotientFunctor V).map (.nil : x ⟶ x) = 𝟙 _ :=
  Functor.map_id _ _

@[simp]
lemma quotientFunctor_map_cons {x y z : Paths V}
    (p : x ⟶ y) (q : Quiver.Hom (V := V) y z) :
    (quotientFunctor V).map (p.cons q : x ⟶ z) =
      (quotientFunctor V).map p ≫ homMk q :=
  rfl

variable (V) in
/-- The property of morphisms in `FreeRefl V` which are of the form `homMk f`
for some morphism `f : x ⟶ y` in `V`. -/
def morphismPropertyHomMk : MorphismProperty (FreeRefl V) :=
    .ofHoms (fun (e : Σ (x y : V), x ⟶ y) ↦ homMk e.2.2)

lemma morphismPropertyHomMk_homMk {x y : V} (e : x ⟶ y) :
    morphismPropertyHomMk V (homMk e) := by
  dsimp only [morphismPropertyHomMk]
  rw [MorphismProperty.ofHoms_iff]
  exact ⟨⟨x, y, e⟩, rfl⟩

@[elab_as_elim, induction_eliminator]
lemma hom_induction {motive : ∀ {x y : FreeRefl V} (_ : x ⟶ y), Prop}
    (id : ∀ (x : V), motive (homMk (𝟙rq x)))
    (comp_homMk : ∀ {x y z : V} (f : mk x ⟶ mk y) (g : y ⟶ z),
      motive f → motive (f ≫ homMk g)) {x y : FreeRefl V} (f : x ⟶ y) :
  motive f := by
    induction x using induction with | _ x
    induction y using induction with | _ y
    obtain ⟨f, rfl⟩ := (quotientFunctor _).map_surjective f
    induction f with
    | nil => simpa using id x
    | cons _ f h => simpa using comp_homMk _ f h

open MorphismProperty in
lemma multiplicativeClosure_morphismPropertyHomMk :
    (morphismPropertyHomMk V).multiplicativeClosure = ⊤ :=
  le_antisymm (by simp) (by
    intro _ _ f hf
    clear hf
    induction f using hom_induction with
    | id => exact le_multiplicativeClosure _ _ (morphismPropertyHomMk_homMk _)
    | comp_homMk _ _ h =>
      exact comp_mem _ _ _ h (le_multiplicativeClosure _ _ (morphismPropertyHomMk_homMk _)))

lemma morphismProperty_eq_top {W : MorphismProperty (FreeRefl V)}
    [W.IsMultiplicative] (hW : ∀ {x y : V} (e : x ⟶ y), W (homMk e)) :
    W = ⊤ :=
  le_antisymm (by simp) (by
    rw [← multiplicativeClosure_morphismPropertyHomMk,
      MorphismProperty.multiplicativeClosure_le_iff]
    rintro _ _ _ ⟨h⟩
    apply hW)

section

variable {D : Type*} [Category* D] (F : V ⥤rq D)

/-- Constructor for functors from `FreeRefl`.
(See also `lift'` for which the data is unbundled.) -/
def lift : FreeRefl V ⥤ D :=
  Quotient.lift _ (Paths.lift F.toPrefunctor) (by
    rintro _ _ _ _ ⟨h⟩
    simp)

@[simp]
lemma lift_obj (v : V) : (lift F).obj (mk v) = F.obj v := rfl

@[simp]
lemma lift_map {v w : V} (f : v ⟶ w) : (lift F).map (homMk f) = F.map f :=
  Category.id_comp _

end

section

variable {D : Type*} [Category* D]
  (obj : V → D) (map : ∀ {v w : V}, (v ⟶ w) → (obj v ⟶ obj w))
  (map_id : ∀ (v : V), map (𝟙rq v) = 𝟙 _)

/-- Constructor for functors from `FreeRefl`.
(See also `lift` for which the data is bundled.) -/
def lift' : FreeRefl V ⥤ D :=
  lift { obj := obj, map := map, map_id := map_id }

@[simp]
lemma lift'_obj (v : V) :
    (lift' obj map map_id).obj (mk v) = obj v := rfl

@[simp]
lemma lift'_map {v w : V} (f : v ⟶ w) :
    (lift' obj map map_id).map (homMk f) = map f := by
  simp [lift']

end

/-- This is a specialization of `Quotient.lift_unique'` rather than `Quotient.lift_unique`, hence
the prime in the name. -/
theorem lift_unique' {V} [ReflQuiver V] {D} [Category* D] (F₁ F₂ : FreeRefl V ⥤ D)
    (h : quotientFunctor V ⋙ F₁ = quotientFunctor V ⋙ F₂) :
    F₁ = F₂ :=
  Quotient.lift_unique' (C := Cat.free.obj (Quiv.of V)) (FreeReflRel (V := V)) _ _ h

lemma functor_ext {D : Type*} [Category* D]
    {F G : FreeRefl V ⥤ D} (h₁ : ∀ v, F.obj (mk v) = G.obj (mk v))
    (h₂ : ∀ {v w : V} (f : v ⟶ w), F.map (homMk f) =
      eqToHom (h₁ v) ≫ G.map (homMk f) ≫ eqToHom (h₁ w).symm) : F = G :=
  lift_unique' _ _ (Paths.ext_functor (by ext; apply h₁) (fun _ _ _ ↦ h₂ _))

@[simp]
lemma quotientFunctor_map_id (V) [ReflQuiver V] (X : V) :
    (FreeRefl.quotientFunctor V).map (𝟙rq X).toPath = 𝟙 _ :=
  Quotient.sound _ .mk

instance (V : Type*) [ReflQuiver V] [Unique V] : Unique (FreeRefl V) :=
  inferInstanceAs (Unique (Quotient _))

instance (V : Type*) [ReflQuiver V] [Unique V]
    [∀ (x y : V), Unique (x ⟶ y)] (x y : FreeRefl V) :
    Unique (x ⟶ y) where
  default := homMk default
  uniq f := by
    induction f using hom_induction with
    | id => congr; subsingleton
    | @comp_homMk x y z _ g h =>
      obtain rfl := Subsingleton.elim y z
      obtain rfl := Subsingleton.elim g (𝟙rq _)
      simp [h]

end FreeRefl

/-- Given a refl quiver `V`, this is the refl functor `V ⥤rq FreeRefl V` which
is the counit of the adjunction between reflexive quivers and categories. -/
@[simps]
def toFreeRefl : V ⥤rq FreeRefl V where
  obj := .mk
  map := FreeRefl.homMk

attribute [local simp] Functor.toReflPrefunctor in
variable {V} in
/-- Constructor for functors from `FreeRefl`. -/
lemma FreeRefl.lift_spec {D : Type*} [Category* D] (F : V ⥤rq D) :
    Cat.toFreeRefl V ⋙rq (Cat.FreeRefl.lift F).toReflPrefunctor = F :=
  ReflPrefunctor.ext (fun v ↦ by simp) (by simp)

variable {V} {W : Type*} [ReflQuiver W] (F : V ⥤rq W)
/-- A refl prefunctor `V ⥤rq W` induces a functor `FreeRefl V ⥤ FreeRefl W` defined using
`freeMap` and the quotient functor. -/
def freeReflMap : FreeRefl V ⥤ FreeRefl W :=
  FreeRefl.lift' (fun v ↦ .mk (F.obj v)) (fun f ↦ FreeRefl.homMk (F.map f))
    (fun v ↦ by simp)

@[simp]
lemma freeReflMap_obj (v : V) : (freeReflMap F).obj (.mk v) = .mk (F.obj v) := rfl

@[simp]
lemma freeReflMap_map {v w : V} (f : v ⟶ w) :
    (freeReflMap F).map (FreeRefl.homMk f) = FreeRefl.homMk (F.map f) := rfl

theorem freeReflMap_naturality
    {V W : Type*} [ReflQuiver.{v₁ + 1} V] [ReflQuiver.{v₂ + 1} W] (F : V ⥤rq W) :
    FreeRefl.quotientFunctor V ⋙ freeReflMap F =
    freeMap F.toPrefunctor ⋙ FreeRefl.quotientFunctor W :=
  Paths.ext_functor rfl (by cat_disch)

/-- The functor sending a reflexive quiver to the free category it generates, a quotient of
its path category -/
@[simps]
def freeRefl : ReflQuiv.{v, u} ⥤ Cat.{max u v, u} where
  obj V := Cat.of (FreeRefl V)
  map F := freeReflMap F
  map_id X := FreeRefl.functor_ext (by simp) (by simp)
  map_comp {X Y Z} f g := FreeRefl.functor_ext (by simp) (by simp)

/-- We will make use of the natural quotient map from the free category on the underlying
quiver of a refl quiver to the free category on the reflexive quiver. -/
def freeReflNatTrans : ReflQuiv.forgetToQuiv ⋙ Cat.free ⟶ freeRefl where
  app V := FreeRefl.quotientFunctor V
  naturality v w f := Paths.ext_functor (V := Quiv.of v) (by cat_disch) (by cat_disch)

end Cat

namespace ReflQuiv
open Category Functor

namespace adj

variable {V W : Type*} [ReflQuiver W] [ReflQuiver V]
  {C D : Type*} [Category* C] [Category* D]

/-- Given a reflexive quiver `V` and a category `C`, this is the bijection
between functors `Cat.FreeRefl V ⥤ C` and refl functors `V ⥤rq C`. -/
@[simps]
def homEquiv : (Cat.FreeRefl V ⥤ C) ≃ V ⥤rq C where
  toFun F := Cat.toFreeRefl V ⋙rq F.toReflPrefunctor
  invFun := Cat.FreeRefl.lift
  left_inv F := Cat.FreeRefl.functor_ext (by cat_disch) (by cat_disch)
  right_inv := Cat.FreeRefl.lift_spec

lemma homEquiv_naturality_left_symm (F : V ⥤rq W) (G : W ⥤rq C) :
    homEquiv.symm (F ⋙rq G) = Cat.freeReflMap F ⋙ homEquiv.symm G :=
  Cat.FreeRefl.functor_ext (by simp) (by simp)

lemma homEquiv_naturality_right (F : Cat.FreeRefl V ⥤ C) (G : C ⥤ D) :
    homEquiv (F ⋙ G) = homEquiv F ⋙rq G.toReflPrefunctor := rfl

end adj

/--
The adjunction between forming the free category on a reflexive quiver, and forgetting a category
to a reflexive quiver.
-/
def adj : Cat.freeRefl.{max u v, u} ⊣ ReflQuiv.forget :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := adj.homEquiv
      homEquiv_naturality_left_symm _ _ := adj.homEquiv_naturality_left_symm _ _
      homEquiv_naturality_right _ _ := adj.homEquiv_naturality_right _ _ }

@[simp]
lemma adj_unit_app (V) [ReflQuiver V] :
    adj.unit.app (ReflQuiv.of V) = Cat.toFreeRefl V := rfl

lemma adj_counit_app (D : Type u) [Category.{max u v} D] :
    adj.counit.app (Cat.of D) = Cat.FreeRefl.lift (𝟭rq D) := rfl

variable {V : Type*} [ReflQuiver V]
  {C : Type*} [Category* C]

lemma adj_homEquiv (V : Type u) [ReflQuiver.{max u v + 1} V] (C : Type u) [Category.{max u v} C] :
    (adj).homEquiv (.of V) (.of C) = adj.homEquiv := by
  ext F
  apply Adjunction.homEquiv_unit

lemma adj.unit.map_app_eq (V : Type u) [ReflQuiver.{max u v + 1} V] :
    (adj.unit.app (.of V)).toPrefunctor = Quiv.adj.unit.app (.of V) ⋙q
      (Cat.FreeRefl.quotientFunctor V).toPrefunctor := rfl

lemma adj.counit.comp_app_eq (C : Type u) [Category.{max u v} C] :
    Cat.FreeRefl.quotientFunctor C ⋙ adj.counit.app (.of C) =
      pathComposition _ :=
  Paths.ext_functor rfl (fun _ _ f ↦ by
    dsimp
    simp only [adj_counit_app, composePath_toPath, comp_id, id_comp]
    apply Cat.FreeRefl.lift_map)

end ReflQuiv

end CategoryTheory
