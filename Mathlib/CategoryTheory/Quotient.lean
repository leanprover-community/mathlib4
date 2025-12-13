/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Groupoid

/-!
# Quotient category

Constructs the quotient of a category by an arbitrary family of relations on its hom-sets,
by introducing a type synonym for the objects, and identifying homs as necessary.

This is analogous to 'the quotient of a group by the normal closure of a subset', rather
than 'the quotient of a group by a normal subgroup'. When taking the quotient by a congruence
relation, `functor_map_eq_iff` says that no unnecessary identifications have been made.
-/

@[expose] public section


/-- A `HomRel` on `C` consists of a relation on every hom-set. -/
def HomRel (C) [Quiver C] :=
  ∀ ⦃X Y : C⦄, (X ⟶ Y) → (X ⟶ Y) → Prop
deriving Inhabited

namespace CategoryTheory

open Functor

section

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

/-- A functor induces a `HomRel` on its domain, relating those maps that have the same image. -/
def Functor.homRel : HomRel C :=
  fun _ _ f g ↦ F.map f = F.map g

@[simp]
lemma Functor.homRel_iff {X Y : C} (f g : X ⟶ Y) :
    F.homRel f g ↔ F.map f = F.map g := Iff.rfl

end

variable {C : Type _} [Category* C] (r : HomRel C)

/-- A `HomRel` is a congruence when it's an equivalence on every hom-set, and it can be composed
from left and right. -/
class Congruence : Prop where
  /-- `r` is an equivalence on every hom-set. -/
  equivalence : ∀ {X Y}, _root_.Equivalence (@r X Y)
  /-- Precomposition with an arrow respects `r`. -/
  compLeft : ∀ {X Y Z} (f : X ⟶ Y) {g g' : Y ⟶ Z}, r g g' → r (f ≫ g) (f ≫ g')
  /-- Postcomposition with an arrow respects `r`. -/
  compRight : ∀ {X Y Z} {f f' : X ⟶ Y} (g : Y ⟶ Z), r f f' → r (f ≫ g) (f' ≫ g)

/-- For `F : C ⥤ D`, `F.homRel` is a congruence. -/
instance Functor.congruence_homRel {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) :
    Congruence F.homRel where
  equivalence :=
    { refl := fun _ ↦ rfl
      symm := by aesop
      trans := by aesop }
  compLeft := by aesop
  compRight := by aesop

/-- A type synonym for `C`, thought of as the objects of the quotient category. -/
@[ext]
structure Quotient (r : HomRel C) where
  /-- The object of `C`. -/
  as : C

instance [Inhabited C] : Inhabited (Quotient r) :=
  ⟨{ as := default }⟩

namespace Quotient

/-- Generates the closure of a family of relations w.r.t. composition from left and right. -/
inductive CompClosure (r : HomRel C) ⦃s t : C⦄ : (s ⟶ t) → (s ⟶ t) → Prop
  | intro {a b : C} (f : s ⟶ a) (m₁ m₂ : a ⟶ b) (g : b ⟶ t) (h : r m₁ m₂) :
    CompClosure r (f ≫ m₁ ≫ g) (f ≫ m₂ ≫ g)

theorem CompClosure.of {a b : C} (m₁ m₂ : a ⟶ b) (h : r m₁ m₂) : CompClosure r m₁ m₂ := by
  simpa using CompClosure.intro (𝟙 _) m₁ m₂ (𝟙 _) h

theorem comp_left {a b c : C} (f : a ⟶ b) :
    ∀ (g₁ g₂ : b ⟶ c) (_ : CompClosure r g₁ g₂), CompClosure r (f ≫ g₁) (f ≫ g₂)
  | _, _, ⟨x, m₁, m₂, y, h⟩ => by simpa using CompClosure.intro (f ≫ x) m₁ m₂ y h

theorem comp_right {a b c : C} (g : b ⟶ c) :
    ∀ (f₁ f₂ : a ⟶ b) (_ : CompClosure r f₁ f₂), CompClosure r (f₁ ≫ g) (f₂ ≫ g)
  | _, _, ⟨x, m₁, m₂, y, h⟩ => by simpa using CompClosure.intro x m₁ m₂ (y ≫ g) h

/-- Hom-sets of the quotient category. -/
def Hom (s t : Quotient r) :=
  Quot <| @CompClosure C _ r s.as t.as

instance (a : Quotient r) : Inhabited (Hom r a a) :=
  ⟨Quot.mk _ (𝟙 a.as)⟩

/-- Composition in the quotient category. -/
def comp ⦃a b c : Quotient r⦄ : Hom r a b → Hom r b c → Hom r a c := fun hf hg ↦
  Quot.liftOn hf
    (fun f ↦
      Quot.liftOn hg (fun g ↦ Quot.mk _ (f ≫ g)) fun g₁ g₂ h ↦
        Quot.sound <| comp_left r f g₁ g₂ h)
    fun f₁ f₂ h ↦ Quot.inductionOn hg fun g ↦ Quot.sound <| comp_right r g f₁ f₂ h

@[simp]
theorem comp_mk {a b c : Quotient r} (f : a.as ⟶ b.as) (g : b.as ⟶ c.as) :
    comp r (Quot.mk _ f) (Quot.mk _ g) = Quot.mk _ (f ≫ g) :=
  rfl

instance category : Category (Quotient r) where
  Hom := Hom r
  id a := Quot.mk _ (𝟙 a.as)
  comp := @comp _ _ r
  comp_id f := Quot.inductionOn f <| by simp
  id_comp f := Quot.inductionOn f <| by simp
  assoc f g h := Quot.inductionOn f <| Quot.inductionOn g <| Quot.inductionOn h <| by simp

/-- An equivalence between the type synonym for a quotient category and the type alias
for the original category. -/
def equiv {C : Type _} [Category* C] (r : HomRel C) : Quotient r ≃ C where
  toFun x := x.1
  invFun x := ⟨x⟩

noncomputable section

variable {G : Type*} [Groupoid G] (r : HomRel G)

/-- Inverse of a map in the quotient category of a groupoid. -/
protected def inv {X Y : Quotient r} (f : X ⟶ Y) : Y ⟶ X :=
  Quot.liftOn f (fun f' => Quot.mk _ (Groupoid.inv f')) (fun _ _ con => by
    rcases con with ⟨_, f, g, _, hfg⟩
    have := Quot.sound <| CompClosure.intro (Groupoid.inv g) f g (Groupoid.inv f) hfg
    simp only [Groupoid.inv_eq_inv, IsIso.hom_inv_id, Category.comp_id,
      IsIso.inv_hom_id_assoc] at this
    simp only [Groupoid.inv_eq_inv, IsIso.inv_comp, Category.assoc]
    repeat rw [← comp_mk]
    rw [this])

@[simp]
theorem inv_mk {X Y : Quotient r} (f : X.as ⟶ Y.as) :
    Quotient.inv r (Quot.mk _ f) = Quot.mk _ (Groupoid.inv f) :=
  rfl

/-- The quotient of a groupoid is a groupoid. -/
instance groupoid : Groupoid (Quotient r) where
  inv f := Quotient.inv r f
  inv_comp f := Quot.inductionOn f <| by simp [CategoryStruct.comp, CategoryStruct.id]
  comp_inv f := Quot.inductionOn f <| by simp [CategoryStruct.comp, CategoryStruct.id]

end

/-- The functor from a category to its quotient. -/
def functor : C ⥤ Quotient r where
  obj a := { as := a }
  map f := Quot.mk _ f

instance full_functor : (functor r).Full where
  map_surjective f := ⟨Quot.out f, by simp [functor]⟩

instance essSurj_functor : (functor r).EssSurj where
  mem_essImage Y := ⟨Y.as, ⟨eqToIso rfl⟩⟩

instance [Unique C] : Unique (Quotient r) where
  uniq a := by ext; subsingleton

instance [∀ (x y : C), Subsingleton (x ⟶ y)] (x y : Quotient r) :
    Subsingleton (x ⟶ y) := (full_functor r).map_surjective.subsingleton

protected theorem induction {P : ∀ {a b : Quotient r}, (a ⟶ b) → Prop}
    (h : ∀ {x y : C} (f : x ⟶ y), P ((functor r).map f)) :
    ∀ {a b : Quotient r} (f : a ⟶ b), P f := by
  rintro ⟨x⟩ ⟨y⟩ ⟨f⟩
  exact h f

protected theorem sound {a b : C} {f₁ f₂ : a ⟶ b} (h : r f₁ f₂) :
    (functor r).map f₁ = (functor r).map f₂ := by
  simpa using Quot.sound (CompClosure.intro (𝟙 a) f₁ f₂ (𝟙 b) h)

lemma compClosure_iff_self [h : Congruence r] {X Y : C} (f g : X ⟶ Y) :
    CompClosure r f g ↔ r f g := by
  constructor
  · rintro ⟨hfg⟩
    exact Congruence.compLeft _ (Congruence.compRight _ (by assumption))
  · exact CompClosure.of _ _ _

@[simp]
theorem compClosure_eq_self [h : Congruence r] :
    CompClosure r = r := by
  ext
  simp only [compClosure_iff_self]

theorem functor_map_eq_iff [h : Congruence r] {X Y : C} (f f' : X ⟶ Y) :
    (functor r).map f = (functor r).map f' ↔ r f f' := by
  dsimp [functor]
  rw [Equivalence.quot_mk_eq_iff, compClosure_eq_self r]
  simpa only [compClosure_eq_self r] using h.equivalence

theorem functor_homRel_eq_compClosure_eqvGen {X Y : C} (f g : X ⟶ Y) :
    (functor r).homRel f g ↔ Relation.EqvGen (@CompClosure C _ r X Y) f g :=
  Quot.eq

theorem compClosure.congruence :
    Congruence fun X Y => Relation.EqvGen (@CompClosure C _ r X Y) := by
  convert inferInstanceAs (Congruence (functor r).homRel)
  ext
  rw [functor_homRel_eq_compClosure_eqvGen]

variable {D : Type _} [Category* D] (F : C ⥤ D)

/-- The induced functor on the quotient category. -/
def lift (H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂) : Quotient r ⥤ D where
  obj a := F.obj a.as
  map hf :=
    Quot.liftOn hf (fun f ↦ F.map f)
      (by
        rintro _ _ ⟨_, _, _, _, h⟩
        simp [H _ _ _ _ h])
  map_id a := F.map_id a.as
  map_comp := by
    rintro a b c ⟨f⟩ ⟨g⟩
    exact F.map_comp f g

variable (H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂)

theorem lift_spec : functor r ⋙ lift r F H = F := by
  tauto

theorem lift_unique (Φ : Quotient r ⥤ D) (hΦ : functor r ⋙ Φ = F) : Φ = lift r F H := by
  subst_vars
  fapply Functor.hext
  · rintro X
    dsimp [lift, Functor]
    congr
  · rintro _ _ f
    dsimp [lift, Functor]
    refine Quot.inductionOn f fun _ ↦ ?_
    simp only [heq_eq_eq]
    congr

lemma lift_unique' (F₁ F₂ : Quotient r ⥤ D) (h : functor r ⋙ F₁ = functor r ⋙ F₂) :
    F₁ = F₂ := by
  rw [lift_unique r (functor r ⋙ F₂) _ F₂ rfl]; swap
  · rintro X Y f g h
    dsimp
    rw [Quotient.sound r h]
  apply lift_unique
  rw [h]

/-- The original functor factors through the induced functor. -/
def lift.isLift : functor r ⋙ lift r F H ≅ F :=
  NatIso.ofComponents fun _ ↦ Iso.refl _

@[simp]
theorem lift.isLift_hom (X : C) : (lift.isLift r F H).hom.app X = 𝟙 (F.obj X) :=
  rfl

@[simp]
theorem lift.isLift_inv (X : C) : (lift.isLift r F H).inv.app X = 𝟙 (F.obj X) :=
  rfl

theorem lift_obj_functor_obj (X : C) :
    (lift r F H).obj ((functor r).obj X) = F.obj X := rfl

theorem lift_map_functor_map {X Y : C} (f : X ⟶ Y) :
    (lift r F H).map ((functor r).map f) = F.map f :=
  rfl

variable {r}

lemma natTrans_ext {F G : Quotient r ⥤ D} (τ₁ τ₂ : F ⟶ G)
    (h : whiskerLeft (Quotient.functor r) τ₁ = whiskerLeft (Quotient.functor r) τ₂) : τ₁ = τ₂ :=
  NatTrans.ext (by ext1 ⟨X⟩; exact NatTrans.congr_app h X)

variable (r)

/-- In order to define a natural transformation `F ⟶ G` with `F G : Quotient r ⥤ D`, it suffices
to do so after precomposing with `Quotient.functor r`. -/
def natTransLift {F G : Quotient r ⥤ D} (τ : Quotient.functor r ⋙ F ⟶ Quotient.functor r ⋙ G) :
    F ⟶ G where
  app := fun ⟨X⟩ => τ.app X
  naturality := fun ⟨X⟩ ⟨Y⟩ => by
    rintro ⟨f⟩
    exact τ.naturality f

@[simp]
lemma natTransLift_app (F G : Quotient r ⥤ D)
    (τ : Quotient.functor r ⋙ F ⟶ Quotient.functor r ⋙ G) (X : C) :
    (natTransLift r τ).app ((Quotient.functor r).obj X) = τ.app X := rfl

@[reassoc]
lemma comp_natTransLift {F G H : Quotient r ⥤ D}
    (τ : Quotient.functor r ⋙ F ⟶ Quotient.functor r ⋙ G)
    (τ' : Quotient.functor r ⋙ G ⟶ Quotient.functor r ⋙ H) :
    natTransLift r τ ≫ natTransLift r τ' =  natTransLift r (τ ≫ τ') := by cat_disch

@[simp]
lemma natTransLift_id (F : Quotient r ⥤ D) :
    natTransLift r (𝟙 (Quotient.functor r ⋙ F)) = 𝟙 _ := by cat_disch

/-- In order to define a natural isomorphism `F ≅ G` with `F G : Quotient r ⥤ D`, it suffices
to do so after precomposing with `Quotient.functor r`. -/
@[simps]
def natIsoLift {F G : Quotient r ⥤ D} (τ : Quotient.functor r ⋙ F ≅ Quotient.functor r ⋙ G) :
    F ≅ G where
  hom := natTransLift _ τ.hom
  inv := natTransLift _ τ.inv
  hom_inv_id := by rw [comp_natTransLift, τ.hom_inv_id, natTransLift_id]
  inv_hom_id := by rw [comp_natTransLift, τ.inv_hom_id, natTransLift_id]

variable (D)

instance full_whiskeringLeft_functor :
    ((whiskeringLeft C _ D).obj (functor r)).Full where
  map_surjective f := ⟨natTransLift r f, by cat_disch⟩

instance faithful_whiskeringLeft_functor :
    ((whiskeringLeft C _ D).obj (functor r)).Faithful := ⟨by apply natTrans_ext⟩

end Quotient

end CategoryTheory
