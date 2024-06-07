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

universe u
@[pp_with_univ]
class ReflQuiver (obj : Type u) extends Quiver.{v} obj : Type max u (v + 1) where
  /-- The identity morphism on an object. -/
  id : ∀ X : obj, Hom X X

/-- A morphism of quivers. As we will later have categorical functors extend this structure,
we call it a `Prefunctor`. -/
structure ReflPrefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] extends Prefunctor V W where
  /-- The action of a (pre)functor on vertices/objects. -/
  obj : V → W
  /-- The action of a (pre)functor on edges/arrows/morphisms. -/
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)

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
#align prefunctor.ext Prefunctor.ext

/-- The identity morphism between quivers. -/
@[simps]
def id (V : Type*) [Quiver V] : Prefunctor V V where
  obj := fun X => X
  map f := f
#align prefunctor.id Prefunctor.id
#align prefunctor.id_obj Prefunctor.id_obj
#align prefunctor.id_map Prefunctor.id_map

instance (V : Type*) [Quiver V] : Inhabited (Prefunctor V V) :=
  ⟨id V⟩

/-- Composition of morphisms between quivers. -/
@[simps]
def comp {U : Type*} [Quiver U] {V : Type*} [Quiver V] {W : Type*} [Quiver W]
    (F : Prefunctor U V) (G : Prefunctor V W) : Prefunctor U W where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)
#align prefunctor.comp Prefunctor.comp
#align prefunctor.comp_obj Prefunctor.comp_obj
#align prefunctor.comp_map Prefunctor.comp_map

@[simp]
theorem comp_id {U V : Type*} [Quiver U] [Quiver V] (F : Prefunctor U V) :
    F.comp (id _) = F := rfl
#align prefunctor.comp_id Prefunctor.comp_id

@[simp]
theorem id_comp {U V : Type*} [Quiver U] [Quiver V] (F : Prefunctor U V) :
    (id _).comp F = F := rfl
#align prefunctor.id_comp Prefunctor.id_comp

@[simp]
theorem comp_assoc {U V W Z : Type*} [Quiver U] [Quiver V] [Quiver W] [Quiver Z]
    (F : Prefunctor U V) (G : Prefunctor V W) (H : Prefunctor W Z) :
    (F.comp G).comp H = F.comp (G.comp H) :=
  rfl
#align prefunctor.comp_assoc Prefunctor.comp_assoc

/-- Notation for a prefunctor between quivers. -/
infixl:50 " ⥤q " => Prefunctor

/-- Notation for composition of prefunctors. -/
infixl:60 " ⋙q " => Prefunctor.comp

/-- Notation for the identity prefunctor on a quiver. -/
notation "𝟭q" => id

theorem congr_map {U V : Type*} [Quiver U] [Quiver V] (F : U ⥤q V) {X Y : U} {f g : X ⟶ Y}
    (h : f = g) : F.map f = F.map g := by
  rw [h]

end Prefunctor

namespace Quiver

/-- `Vᵒᵖ` reverses the direction of all arrows of `V`. -/
instance opposite {V} [Quiver V] : Quiver Vᵒᵖ :=
  ⟨fun a b => (unop b ⟶ unop a)ᵒᵖ⟩
#align quiver.opposite Quiver.opposite

/-- The opposite of an arrow in `V`. -/
def Hom.op {V} [Quiver V] {X Y : V} (f : X ⟶ Y) : op Y ⟶ op X := ⟨f⟩
#align quiver.hom.op Quiver.Hom.op

/-- Given an arrow in `Vᵒᵖ`, we can take the "unopposite" back in `V`. -/
def Hom.unop {V} [Quiver V] {X Y : Vᵒᵖ} (f : X ⟶ Y) : unop Y ⟶ unop X := Opposite.unop f
#align quiver.hom.unop Quiver.Hom.unop

/-- A type synonym for a quiver with no arrows. -/
-- Porting note(#5171): this linter isn't ported yet.
-- @[nolint has_nonempty_instance]
def Empty (V : Type u) : Type u := V
#align quiver.empty Quiver.Empty

instance emptyQuiver (V : Type u) : Quiver.{u} (Empty V) := ⟨fun _ _ => PEmpty⟩
#align quiver.empty_quiver Quiver.emptyQuiver

@[simp]
theorem empty_arrow {V : Type u} (a b : Empty V) : (a ⟶ b) = PEmpty := rfl
#align quiver.empty_arrow Quiver.empty_arrow

/-- A quiver is thin if it has no parallel arrows. -/
abbrev IsThin (V : Type u) [Quiver V] : Prop := ∀ a b : V, Subsingleton (a ⟶ b)
#align quiver.is_thin Quiver.IsThin

end Quiver

@[nolint checkUnivs]
def ReflQuiv :=
  Bundled ReflQuiver.{v + 1, u}


namespace ReflQuiv

instance : CoeSort ReflQuiv (Type u) where coe := Bundled.α

instance str' (C : ReflQuiv.{v, u}) : ReflQuiver.{v + 1, u} C :=
  C.str
set_option linter.uppercaseLean3 false in

/-- Construct a bundled `ReflQuiv` from the underlying type and the typeclass. -/
def of (C : Type u) [ReflQuiver.{v + 1} C] : ReflQuiv.{v, u} :=
  Bundled.of C
set_option linter.uppercaseLean3 false in

instance : Inhabited ReflQuiv :=
  ⟨ReflQuiv.of (ReflQuiver.Empty PEmpty)⟩

/-- Category structure on `ReflQuiv` -/
instance category : LargeCategory.{max v u} ReflQuiv.{v, u} where
  Hom C D := Prefunctor C D
  id C := Prefunctor.id C
  comp F G := Prefunctor.comp F G
set_option linter.uppercaseLean3 false in

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forget : Cat.{v, u} ⥤ ReflQuiv.{v, u} where
  obj C := ReflQuiv.of C
  map F := F.toPrefunctor
set_option linter.uppercaseLean3 false in

end ReflQuiv

namespace Cat

/-- The functor sending each quiver to its path category. -/
@[simps]
def free : ReflQuiv.{v, u} ⥤ Cat.{max u v, u} where
  obj V := Cat.of (Paths V)
  map F :=
    { obj := fun X => F.obj X
      map := fun f => F.mapPath f
      map_comp := fun f g => F.mapPath_comp f g }
  map_id V := by
    change (show Paths V ⥤ _ from _) = _
    ext; swap
    · apply eq_conj_eqToHom
    · rfl
  map_comp {U _ _} F G := by
    change (show Paths U ⥤ _ from _) = _
    ext; swap
    · apply eq_conj_eqToHom
    · rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.free CategoryTheory.Cat.free

end Cat

namespace Quiv

/-- Any prefunctor into a category lifts to a functor from the path category. -/
@[simps]
def lift {V : Type u} [Quiver.{v + 1} V] {C : Type*} [Category C] (F : Prefunctor V C) :
    Paths V ⥤ C where
  obj X := F.obj X
  map f := composePath (F.mapPath f)
set_option linter.uppercaseLean3 false in
#align category_theory.Quiv.lift CategoryTheory.Quiv.lift

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
set_option linter.uppercaseLean3 false in
#align category_theory.Quiv.adj CategoryTheory.Quiv.adj

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
