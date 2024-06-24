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
    refine (Functor.comp_id _).trans <| (Functor.id_comp _).symm.trans ?_
    congr 1
    exact (free.map_id X.toQuiv).symm
  map_comp {X Y Z} f g := by
    simp
    symm
    apply Quotient.lift_unique
    have : free.map (f ≫ g).toPrefunctor =
        free.map (X := X.toQuiv) (Y := Y.toQuiv) f.toPrefunctor ⋙
        free.map (X := Y.toQuiv) (Y := Z.toQuiv) g.toPrefunctor := by
      show _ = _ ≫ _
      rw [← Functor.map_comp]; rfl
    rw [this]; simp [Functor.assoc]
    show _ ⋙ _ ⋙ _ = _
    rw [← Functor.assoc, Quotient.lift_spec, Functor.assoc, Quotient.lift_spec]

end Cat

namespace ReflQuiv

-- We might construct `of_lift_iso_self : Paths.of ⋙ lift F ≅ F`
-- (and then show that `lift F` is initial amongst such functors)
-- but it would require lifting quite a bit of machinery to quivers!
/--
The adjunction between forming the free category on a quiver, and forgetting a category to a quiver.
-/
def adj : Cat.freeRefl ⊣ ReflQuiv.forget :=
  Adjunction.mkOfHomEquiv
    { homEquiv := sorry
      homEquiv_naturality_left_symm := sorry }

end ReflQuiv

open Opposite Simplicial
local notation3:1000 (priority := high) X " _[" n "]" =>
    (X : CategoryTheory.SimplicialObject _).obj (Opposite.op (SimplexCategory.mk n))

def OneTruncation (S : SSet) := S _[0]

instance (S : SSet) : ReflQuiver (OneTruncation S) where
  Hom X Y := {p : S _[1] //
    S.map (op (SimplexCategory.δ (n := 0) 1)) p = X ∧
    S.map (op (SimplexCategory.δ (n := 0) 0)) p = Y}
  id X := by
    refine ⟨S.map (op (SimplexCategory.σ (n := 0) 0)) X, ?_, ?_⟩ <;>
    · change (S.map _ ≫ S.map _) X = X
      rw [← map_comp]
      rw [(_ : _ ≫ _ = 𝟙 _)]; simp
      show ({..} : Opposite _) = _; congr; ext i
      let 0 := i
      rfl

def SSet.oneTruncation : SSet.{u} ⥤ ReflQuiv.{u,u} where
  obj S := ReflQuiv.of (OneTruncation S)
  map {S T} F := {
    obj := F.app (op [0])
    map := fun f => by
      refine ⟨F.app (op [1]) f.1, ?_, ?_⟩
      · change (F.app _ ≫ _) _ = _
        rw [← F.naturality]
        exact congrArg (F.app _) f.2.1
      · change (F.app _ ≫ _) _ = _
        rw [← F.naturality]
        exact congrArg (F.app _) f.2.2
    map_id := fun X => by
      change ({..} : Subtype _) = {..}
      congr
      change _ = (F.app _ ≫ _) _
      rw [← F.naturality]
      rfl
  }
  map_id X := by simp; rfl
  map_comp f g := by simp; rfl

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

theorem opstuff (V : SSet) {m n p} {α : [m] ⟶ [n]} {β : [n] ⟶ [p]} {γ : [m] ⟶ [p]} {φ} :
      α ≫ β = γ → V.map (op α) (V.map (op β) φ) = V.map (op γ) φ := by
    rintro rfl
    change (V.map _ ≫ V.map _) _ = _
    rw [← map_comp]; rfl

def ι0 : [0] ⟶ [2] := SimplexCategory.δ (n := 0) 1 ≫ SimplexCategory.δ (n := 1) 1
def ι1 : [0] ⟶ [2] := SimplexCategory.δ (n := 0) 0 ≫ SimplexCategory.δ (n := 1) 2
def ι2 : [0] ⟶ [2] := SimplexCategory.δ (n := 0) 0 ≫ SimplexCategory.δ (n := 1) 1

def φ0 {V : SSet} (φ : V _[2]) : OneTruncation V := V.map (op ι0) φ
def φ1 {V : SSet} (φ : V _[2]) : OneTruncation V := V.map (op ι1) φ
def φ2 {V : SSet} (φ : V _[2]) : OneTruncation V := V.map (op ι2) φ

def δ1 : [1] ⟶ [2] := SimplexCategory.δ (n := 1) 1
def δ2 : [1] ⟶ [2] := SimplexCategory.δ (n := 1) 2
def δ0 : [1] ⟶ [2] := SimplexCategory.δ (n := 1) 0

def φ02 {V : SSet} (φ : V _[2]) : φ0 φ ⟶ φ2 φ :=
  ⟨V.map (op δ1) φ, opstuff V rfl, opstuff V rfl⟩
def φ01 {V : SSet} (φ : V _[2]) : φ0 φ ⟶ φ1 φ :=
  ⟨V.map (op δ2) φ, opstuff V (SimplexCategory.δ_comp_δ (j := 1) le_rfl), opstuff V rfl⟩
def φ12 {V : SSet} (φ : V _[2]) : φ1 φ ⟶ φ2 φ :=
  ⟨V.map (op δ0) φ,
    opstuff V (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide)).symm,
    opstuff V rfl⟩

inductive HoRel {V : SSet} :
    (X Y : Cat.freeRefl.obj (ReflQuiv.of (OneTruncation V))) → (f g : X ⟶ Y) → Prop
  | mk (φ : V _[2]) :
    HoRel _ _
      (Quot.mk _ (.cons .nil (φ02 φ)))
      (Quot.mk _ (.cons (.cons .nil (φ01 φ)) (φ12 φ)))

theorem HoRel.ext_triangle {V} (X X' Y Y' Z Z' : OneTruncation V)
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (f : X ⟶ Z) (f' : X' ⟶ Z') (hf : f.1 = f'.1)
    (g : X ⟶ Y) (g' : X' ⟶ Y') (hg : g.1 = g'.1)
    (h : Y ⟶ Z) (h' : Y' ⟶ Z') (hh : h.1 = h'.1) :
    HoRel _ _ ((Quotient.functor _).map (.cons .nil f)) ((Quotient.functor _).map (.cons (.cons .nil g) h)) ↔
    HoRel _ _ ((Quotient.functor _).map (.cons .nil f')) ((Quotient.functor _).map (.cons (.cons .nil g') h')) := by
  cases hX
  cases hY
  cases hZ
  congr! <;> apply Subtype.ext <;> assumption

def SSet.hoFunctor : SSet.{u} ⥤ Cat.{u,u} where
  obj V := Cat.of (Quotient (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation V))) (HoRel (V := V)))
  map {S T} F := Quotient.lift _ ((by exact (SSet.oneTruncation ⋙ Cat.freeRefl).map F) ⋙ Quotient.functor _)
    (fun X Y f g hfg => by
      let .mk φ := hfg
      clear f g hfg
      simp [Quot.liftOn]
      apply Quotient.sound
      convert HoRel.mk (F.app (op [2]) φ) using 0
      apply HoRel.ext_triangle
      · exact congrFun (F.naturality (op ι0)) φ
      · exact congrFun (F.naturality (op ι1)) φ
      · exact congrFun (F.naturality (op ι2)) φ
      · exact congrFun (F.naturality (op δ1)) φ
      · exact congrFun (F.naturality (op δ2)) φ
      · exact congrFun (F.naturality (op δ0)) φ)
  map_id X := by
    stop
    simp
    symm
    apply Quotient.lift_unique
    refine (Functor.comp_id _).trans <| (Functor.id_comp _).symm.trans ?_
    congr 1
    exact (free.map_id X.toQuiv).symm
  map_comp {X Y Z} f g := by
    stop
    simp
    symm
    apply Quotient.lift_unique
    have : free.map (f ≫ g).toPrefunctor =
        free.map (X := X.toQuiv) (Y := Y.toQuiv) f.toPrefunctor ⋙
        free.map (X := Y.toQuiv) (Y := Z.toQuiv) g.toPrefunctor := by
      show _ = _ ≫ _
      rw [← Functor.map_comp]; rfl
    rw [this]; simp [Functor.assoc]
    show _ ⋙ _ ⋙ _ = _
    rw [← Functor.assoc, Quotient.lift_spec, Functor.assoc, Quotient.lift_spec]

def reflectiveOfCounitIso {C D} [Category C] [Category D] (R : D ⥤ C) (L : C ⥤ D) (adj : L ⊣ R)
  (h : IsIso adj.counit) : Reflective R where
  L := L
  adj := adj
  map_injective := sorry
  map_surjective := sorry

def nerveAdjunction : SSet.hoFunctor ⊣ nerveFunctor := sorry

instance : Reflective nerveFunctor.{u,u} :=
  reflectiveOfCounitIso _ SSet.hoFunctor.{u,u} nerveAdjunction <| by
    sorry

instance : HasColimits Cat :=
  hasColimits_of_reflective nerveFunctor
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
