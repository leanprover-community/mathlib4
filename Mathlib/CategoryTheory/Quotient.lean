/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.EqToHom

/-!
# Quotient category

Constructs the quotient of a category by an arbitrary family of relations on its hom-sets,
by introducing a type synonym for the objects, and identifying homs as necessary.

This is analogous to 'the quotient of a group by the normal closure of a subset', rather
than 'the quotient of a group by a normal subgroup'. When taking the quotient by a congruence
relation, `functor_map_eq_iff` says that no unnecessary identifications have been made.
-/


/-- A `HomRel` on `C` consists of a relation on every hom-set. -/
def HomRel (C) [Quiver C] :=
  ∀ ⦃X Y : C⦄, (X ⟶ Y) → (X ⟶ Y) → Prop

-- Porting Note: `deriving Inhabited` was not able to deduce this typeclass
instance (C) [Quiver C] : Inhabited (HomRel C) where
  default := fun _ _ _ _ ↦ PUnit

namespace CategoryTheory


/-- A functor induces a `HomRel` on its domain, relating those maps that have the same image. -/
def Functor.homRel {C D : Type*} [Category C] [Category D] (F : C ⥤ D) : HomRel C :=
  fun _ _ f g ↦ F.map f = F.map g

variable {C : Type _} [Category C] (r : HomRel C)

/-- A `HomRel` is a congruence when it's an equivalence on every hom-set, and it can be composed
from left and right. -/
class Congruence : Prop where
  /-- `r` is an equivalence on every hom-set. -/
  equivalence : ∀ {X Y}, _root_.Equivalence (@r X Y)
  /-- Precomposition with an arrow respects `r`. -/
  compLeft : ∀ {X Y Z} (f : X ⟶ Y) {g g' : Y ⟶ Z}, r g g' → r (f ≫ g) (f ≫ g')
  /-- Postcomposition with an arrow respects `r`. -/
  compRight : ∀ {X Y Z} {f f' : X ⟶ Y} (g : Y ⟶ Z), r f f' → r (f ≫ g) (f' ≫ g)

/-- For `F : C ⥤ D`, `F.homRel` is a congruence.-/
theorem Functor.homRelCongruence {C D : Type*} [Category C] [Category D] (F : C ⥤ D) :
    Congruence (F.homRel) where
  equivalence := by
    intro X Y
    unfold homRel
    exact {
      refl := fun _ => rfl
      symm := by aesop
      trans := by aesop
    }
  compLeft f g g' := by
    unfold homRel
    aesop
  compRight := by
    intro _ _ _ f f' g
    unfold homRel
    aesop

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

-- Porting note: Had to manually add the proofs of `comp_id` `id_comp` and `assoc`
instance category : Category (Quotient r) where
  Hom := Hom r
  id a := Quot.mk _ (𝟙 a.as)
  comp := @comp _ _ r
  comp_id f := Quot.inductionOn f <| by simp
  id_comp f := Quot.inductionOn f <| by simp
  assoc f g h := Quot.inductionOn f <| Quot.inductionOn g <| Quot.inductionOn h <| by simp

/-- The functor from a category to its quotient. -/
def functor : C ⥤ Quotient r where
  obj a := { as := a }
  map := @fun _ _ f ↦ Quot.mk _ f

instance full_functor : (functor r).Full where
  map_surjective f := ⟨Quot.out f, by simp [functor]⟩

instance essSurj_functor : (functor r).EssSurj where
  mem_essImage Y :=
    ⟨Y.as, ⟨eqToIso (by
            ext
            rfl)⟩⟩

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
  · intro hfg
    induction' hfg with m m' hm
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

theorem functorHomRel_eq_compClosureEqvGen {X Y : C} (f g : X ⟶ Y) :
    (functor r).homRel f g ↔ Relation.EqvGen (@CompClosure C _ r X Y) f g where
  mp := fun a ↦ Quot.eqvGen_exact a
  mpr := by
    have : Relation.EqvGen (Functor.homRel (functor r) (X := X) (Y := Y)) =
      Functor.homRel (functor r) (X := X) (Y := Y) :=
        Equivalence.eqvGen_eq
        ((Functor.homRelCongruence (functor r)).equivalence (X := X) (Y := Y))
    rw [← this]
    apply Relation.EqvGen.mono
    intro f g
    have := (Functor.homRelCongruence (functor r)).equivalence (X := X) (Y := Y)
    intro rel
    induction rel
    unfold Functor.homRel
    apply (Functor.homRelCongruence (functor r)).compLeft
    apply (Functor.homRelCongruence (functor r)).compRight
    unfold Functor.homRel
    apply Quotient.sound
    assumption

theorem compClosure.congruence :
    Congruence fun X Y => Relation.EqvGen (@CompClosure C _ r X Y) := by
  have : (fun X Y => Relation.EqvGen (@CompClosure C _ r X Y)) =
    (fun X Y => @Functor.homRel _ _ _ _ (functor r) X Y) := by
    funext
    ext
    exact Iff.symm (functorHomRel_eq_compClosureEqvGen r _ _)
  rw [this]
  exact Functor.homRelCongruence (functor r)

variable {D : Type _} [Category D] (F : C ⥤ D)

/-- The induced functor on the quotient category. -/
def lift (H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂) : Quotient r ⥤ D where
  obj a := F.obj a.as
  map := @fun a b hf ↦
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
  apply Functor.ext; rotate_left
  · rintro X
    rfl
  · rintro X Y f
    dsimp [lift, functor]
    simp

theorem lift_unique (Φ : Quotient r ⥤ D) (hΦ : functor r ⋙ Φ = F) : Φ = lift r F H := by
  subst_vars
  fapply Functor.hext
  · rintro X
    dsimp [lift, Functor]
    congr
  · rintro _ _ f
    dsimp [lift, Functor]
    refine Quot.inductionOn f (fun _ ↦ ?_) -- Porting note: this line was originally an `apply`
    simp only [Quot.liftOn_mk, Functor.comp_map]
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
    (lift r F H).map ((functor r).map f) = F.map f := by
  rw [← NatIso.naturality_1 (lift.isLift r F H)]
  dsimp [lift, functor]
  simp

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
    natTransLift r τ ≫ natTransLift r τ' =  natTransLift r (τ ≫ τ') := by aesop_cat

@[simp]
lemma natTransLift_id (F : Quotient r ⥤ D) :
    natTransLift r (𝟙 (Quotient.functor r ⋙ F)) = 𝟙 _ := by aesop_cat

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
  map_surjective f := ⟨natTransLift r f, by aesop_cat⟩

instance faithful_whiskeringLeft_functor :
    ((whiskeringLeft C _ D).obj (functor r)).Faithful := ⟨by apply natTrans_ext⟩

end Quotient

end CategoryTheory
