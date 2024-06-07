import Mathlib

namespace CategoryTheory
open Category Limits Functor
universe v v₁ v₂ u u₁ u₂

section
variable {C E : Type*} [Category C] [Category E] (F : C ⥤ E)
variable {D : Type*} [Category D]

-- homRestriction L R (c, d) = (L c → R d)
@[simps!] def Functor.homRestriction (L : C ⥤ E) (R : D ⥤ E) : Cᵒᵖ × D ⥤ Type v :=
  L.op.prod R ⋙ hom E

def Functor.homRestriction.leftWhiskerIso
    {L L' : C ⥤ E} (α : L ≅ L') (R : D ⥤ E) : L'.homRestriction R ≅ L.homRestriction R :=
  isoWhiskerRight (NatIso.prod (NatIso.op α) (Iso.refl _)) (hom E)

def Adjunction.ofHomRestrictionIso (L : C ⥤ D) (R : D ⥤ C)
    (H : L.homRestriction (Functor.id _) ≅ (Functor.id _).homRestriction R) :
    L ⊣ R :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun c d => (H.app (Opposite.op c, d)).toEquiv
    homEquiv_naturality_left_symm := fun {X X' Y} f g => by
      have := congrFun (NatIso.naturality_1 H
        (X := (Opposite.op X', Y)) (Y := (Opposite.op X, Y)) (f.op, 𝟙 Y)) g
      simp [-NatTrans.naturality, Functor.homRestriction] at this
      simp [← this]
    homEquiv_naturality_right := fun {X Y Y'} f g => by
      have := congrFun (NatIso.naturality_2 H
        (X := (Opposite.op X, Y)) (Y := (Opposite.op X, Y')) (𝟙 _, g)) f
      simp [-NatTrans.naturality, Functor.homRestriction] at this
      simp [← this]
  }

end

namespace Quotient
variable {C : Type _} [Category C] (r : HomRel C)

theorem CompClosure.congruence : Congruence fun a b => EqvGen (@CompClosure C _ r a b) where
  equivalence := EqvGen.is_equivalence _
  compLeft f g g' rel := by
    induction rel with
    | rel _ _ h =>
      let .intro f' m₁ m₂ g h := h
      apply EqvGen.rel
      rw [← assoc, ← assoc f]
      exact ⟨_, _, _, _, h⟩
    | refl =>
      apply EqvGen.refl
    | symm _ _ _ ih =>
      exact EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ =>
      exact EqvGen.trans _ _ _ ih₁ ih₂
  compRight g rel := by
    induction rel with
    | rel _ _ h =>
      let .intro f' m₁ m₂ g h := h
      apply EqvGen.rel
      rw [assoc, assoc, assoc, assoc]
      exact ⟨_, _, _, _, h⟩
    | refl =>
      apply EqvGen.refl
    | symm _ _ _ ih =>
      exact EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ =>
      exact EqvGen.trans _ _ _ ih₁ ih₂

end Quotient

@[pp_with_univ]
class ReflQuiver (obj : Type u) extends Quiver.{v} obj : Type max u v where
  /-- The identity morphism on an object. -/
  id : ∀ X : obj, Hom X X

/-- Notation for the identity morphism in a category. -/
scoped notation "𝟙rq" => ReflQuiver.id  -- type as \b1

instance catToReflQuiver {C : Type u} [inst : Category.{v} C] : ReflQuiver.{v+1, u} C :=
  { inst with }

/-- A morphism of quivers. As we will later have categorical functors extend this structure,
we call it a `Prefunctor`. -/
structure ReflPrefunctor (V : Type u₁) [ReflQuiver.{v₁} V] (W : Type u₂) [ReflQuiver.{v₂} W]
    extends Prefunctor V W where
  /-- A functor preserves identity morphisms. -/
  map_id : ∀ X : V, map (𝟙rq X) = 𝟙rq (obj X) := by aesop_cat

namespace ReflPrefunctor

-- Porting note: added during port.
-- These lemmas can not be `@[simp]` because after `whnfR` they have a variable on the LHS.
-- Nevertheless they are sometimes useful when building functors.
lemma mk_obj {V W : Type*} [ReflQuiver V] [ReflQuiver W] {obj : V → W} {map} {X : V} :
    (Prefunctor.mk obj map).obj X = obj X := rfl

lemma mk_map {V W : Type*} [ReflQuiver V] [ReflQuiver W] {obj : V → W} {map} {X Y : V} {f : X ⟶ Y} :
    (Prefunctor.mk obj map).map f = map f := rfl

@[ext]
theorem ext {V : Type u} [ReflQuiver.{v₁} V] {W : Type u₂} [ReflQuiver.{v₂} W] {F G : Prefunctor V W}
    (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y : V) (f : X ⟶ Y),
      F.map f = Eq.recOn (h_obj Y).symm (Eq.recOn (h_obj X).symm (G.map f))) : F = G := by
  cases' F with F_obj _
  cases' G with G_obj _
  obtain rfl : F_obj = G_obj := by
    ext X
    apply h_obj
  congr
  funext X Y f
  simpa using h_map X Y f

/-- The identity morphism between quivers. -/
@[simps!]
def id (V : Type*) [ReflQuiver V] : ReflPrefunctor V V where
  __ := Prefunctor.id _
  map_id _ := rfl

instance (V : Type*) [ReflQuiver V] : Inhabited (ReflPrefunctor V V) :=
  ⟨id V⟩

/-- Composition of morphisms between quivers. -/
@[simps!]
def comp {U : Type*} [ReflQuiver U] {V : Type*} [ReflQuiver V] {W : Type*} [ReflQuiver W]
    (F : ReflPrefunctor U V) (G : ReflPrefunctor V W) : ReflPrefunctor U W where
  __ := F.toPrefunctor.comp G.toPrefunctor
  map_id _ := by simp [F.map_id, G.map_id]

@[simp]
theorem comp_id {U V : Type*} [ReflQuiver U] [ReflQuiver V] (F : ReflPrefunctor U V) :
    F.comp (id _) = F := rfl

@[simp]
theorem id_comp {U V : Type*} [ReflQuiver U] [ReflQuiver V] (F : ReflPrefunctor U V) :
    (id _).comp F = F := rfl

@[simp]
theorem comp_assoc {U V W Z : Type*} [ReflQuiver U] [ReflQuiver V] [ReflQuiver W] [ReflQuiver Z]
    (F : ReflPrefunctor U V) (G : ReflPrefunctor V W) (H : ReflPrefunctor W Z) :
    (F.comp G).comp H = F.comp (G.comp H) :=
  rfl

/-- Notation for a prefunctor between quivers. -/
infixl:50 " ⥤rq " => ReflPrefunctor

/-- Notation for composition of prefunctors. -/
infixl:60 " ⋙rq " => ReflPrefunctor.comp

/-- Notation for the identity prefunctor on a quiver. -/
notation "𝟭rq" => id

theorem congr_map {U V : Type*} [Quiver U] [Quiver V] (F : U ⥤q V) {X Y : U} {f g : X ⟶ Y}
    (h : f = g) : F.map f = F.map g := by
  rw [h]

end ReflPrefunctor

def Functor.toReflPrefunctor {C D} [Category C] [Category D] (F : C ⥤ D) : C ⥤rq D := { F with }

namespace ReflQuiver
open Opposite

/-- `Vᵒᵖ` reverses the direction of all arrows of `V`. -/
instance opposite {V} [ReflQuiver V] : ReflQuiver Vᵒᵖ where
   id X := op (𝟙rq X.unop)

instance discreteQuiver (V : Type u) : ReflQuiver.{u+1} (Discrete V) := { discreteCategory V with }

end ReflQuiver

@[nolint checkUnivs]
def ReflQuiv :=
  Bundled ReflQuiver.{v + 1, u}

namespace ReflQuiv

instance : CoeSort ReflQuiv (Type u) where coe := Bundled.α

instance str' (C : ReflQuiv.{v, u}) : ReflQuiver.{v + 1, u} C :=
  C.str

def toQuiv (C : ReflQuiv.{v, u}) : Quiv.{v, u} := Quiv.of C.α

/-- Construct a bundled `ReflQuiv` from the underlying type and the typeclass. -/
def of (C : Type u) [ReflQuiver.{v + 1} C] : ReflQuiv.{v, u} :=
  Bundled.of C

instance : Inhabited ReflQuiv :=
  ⟨ReflQuiv.of (Discrete default)⟩

/-- Category structure on `ReflQuiv` -/
instance category : LargeCategory.{max v u} ReflQuiv.{v, u} where
  Hom C D := ReflPrefunctor C D
  id C := ReflPrefunctor.id C
  comp F G := ReflPrefunctor.comp F G

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forget : Cat.{v, u} ⥤ ReflQuiv.{v, u} where
  obj C := ReflQuiv.of C
  map F := F.toReflPrefunctor

end ReflQuiv

namespace Cat

inductive FreeReflRel {V} [ReflQuiver V] : (X Y : Paths V) → (f g : X ⟶ Y) → Prop
  | mk {X : V} : FreeReflRel X X (Quiver.Hom.toPath (𝟙rq X)) .nil

/-- The functor sending each quiver to its path category. -/
@[simps!]
def freeRefl : ReflQuiv.{v, u} ⥤ Cat.{max u v, u} where
  obj V := Cat.of (Quotient (C := Cat.free.obj V.toQuiv) (FreeReflRel (V := V)))
  map f := Quotient.lift _ ((by exact Cat.free.map f.toPrefunctor) ⋙ Quotient.functor _)
    (fun X Y f g hfg => by
      apply Quotient.sound
      cases hfg
      simp [ReflPrefunctor.map_id]
      constructor)
  map_id X := by
    simp
    symm
    apply Quotient.lift_unique
    refine (Functor.comp_id _).trans ?_
    refine Eq.trans (Functor.id_comp _).symm ?_
    congr 1
    exact (free.map_id X.toQuiv).symm
  map_comp {X Y Z} f g := by
    simp
    symm
    apply Quotient.lift_unique
    have : free.map (f ≫ g).toPrefunctor =
        free.map (X := X.toQuiv) (Y := Y.toQuiv) f.toPrefunctor ⋙
        free.map (X := Y.toQuiv) (Y := Z.toQuiv) g.toPrefunctor := by
      done
    rw [this]; simp [Functor.assoc]
    show _ ⋙ _ ⋙ _ = _
    rw [← Functor.assoc, Quotient.lift_spec, Functor.assoc, Quotient.lift_spec]

end Cat

namespace Quiv

/-- Any prefunctor into a category lifts to a functor from the path category. -/
@[simps]
def lift {V : Type u} [Quiver.{v + 1} V] {C : Type*} [Category C] (F : Prefunctor V C) :
    Paths V ⥤ C where
  obj X := F.obj X
  map f := composePath (F.mapPath f)

-- We might construct `of_lift_iso_self : Paths.of ⋙ lift F ≅ F`
-- (and then show that `lift F` is initial amongst such functors)
-- but it would require lifting quite a bit of machinery to quivers!
/--
The adjunction between forming the free category on a quiver, and forgetting a category to a quiver.
-/
def adj : Cat.free ⊣ Quiv.forget :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun V C =>
        { toFun := fun F => Paths.of.comp F.toPrefunctor
          invFun := fun F => @lift V _ C _ F
          left_inv := fun F => Paths.ext_functor rfl (by simp)
          right_inv := by
            rintro ⟨obj, map⟩
            dsimp only [Prefunctor.comp]
            congr
            funext X Y f
            exact Category.id_comp _ }
      homEquiv_naturality_left_symm := fun {V _ _} f g => by
        change (show Paths V ⥤ _ from _) = _
        ext; swap
        · apply eq_conj_eqToHom
        · rfl }

end Quiv

end CategoryTheory

-- -- nerve E c = (F c → E)
-- def Functor.nerve : E ⥤ Cᵒᵖ ⥤ Type v :=
--   .flip <| curryObj (F.homRestriction (Functor.id E))
-- end
-- namespace Something
-- variable {C : Type} {E : Type} [Category C] [Category E] (F : C ⥤ E)

-- variable [lkan : yoneda.HasPointwiseLeftKanExtension F]

-- -- (lan.right.obj (yoneda.obj c) ⟶ Y)
-- noncomputable def lan : (Cᵒᵖ ⥤ Type) ⥤ E :=
--   (LeftExtension.mk _ (yoneda.pointwiseLeftKanExtensionUnit F)).right

-- noncomputable def lanIso : F ≅ yoneda ⋙ lan F :=
--   have := LeftExtension.IsPointwiseLeftKanExtension.isIso_hom
--    (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension yoneda F)
--   asIso (LeftExtension.mk _ (yoneda.pointwiseLeftKanExtensionUnit F)).hom

-- #print ColimitAdj.yonedaAdjunction
-- noncomputable def nerveIsRightAdjointRepresentable :
--     (yoneda ⋙ lan F).homRestriction (Functor.id _) ≅ yoneda.homRestriction F.nerve := by
--   have := (yoneda ⋙ lan F).homRestriction (Functor.id _)
--   have := yoneda.homRestriction F.nerve

--   -- have := (yoneda (C := C)).homRestriction (Functor.id (Cᵒᵖ ⥤ Type _))
--   refine .trans ?_ (isoWhiskerLeft ((Functor.id Cᵒᵖ).prod F.nerve) (yonedaLemma C)).symm
--   refine .trans (homRestriction.leftWhiskerIso (lanIso F) (𝟭 E)) ?_
--   refine .trans ?_ (isoWhiskerLeft ((𝟭 Cᵒᵖ).prod F.nerve ⋙ _) uliftFunctorTrivial)
--   have (c e) :
--       ((𝟭 Cᵒᵖ).prod F.nerve ⋙ yoneda.homRestriction (Functor.id (Cᵒᵖ ⥤ Type _))).obj (Opposite.op c, e) =
--       ULift.{0, 0} (F.obj c ⟶ e) :=
--     by simp [Functor.nerve]
--   have (c e) :
--       ((𝟭 Cᵒᵖ).prod F.nerve ⋙ yonedaEvaluation C).obj (Opposite.op c, e) =
--       ULift.{0, 0} (F.obj c ⟶ e) :=
--     rfl


--   have := yonedaPairing C
--   have := yonedaEvaluation C
--   -- #simp [yonedaPairing] => (yonedaPairing C).obj

-- def nerveIsRightAdjoint : lan F ⊣ F.nerve :=
--   Adjunction.mkOfHomEquiv {
--     homEquiv := _
--   }
#print ColimitAdj.yonedaAdjunction

-- variable {C E : Type*} [Category C] [Category E] (F : C ⥤ E)
-- variable {D : Type*} [Category D]

#print nerveFunctor

def hoFunctor : SSet ⥤ Cat :=
  ColimitAdj.extendAlongYoneda SimplexCategory.toCat
