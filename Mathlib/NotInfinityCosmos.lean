import Mathlib.AlgebraicTopology.Nerve
import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Opposites

noncomputable section

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

theorem Functor.id_eq_id (X : Cat) : 𝟙 X = 𝟭 X := rfl
theorem Functor.comp_eq_comp {X Y Z : Cat} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙ G := rfl

theorem Quiv.id_eq_id (X : Quiv) : 𝟙 X = 𝟭q X := rfl
theorem Quiv.comp_eq_comp {X Y Z : Quiv} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙q G := rfl

@[simp] theorem Cat.of_α (C) [Category C] : (of C).α = C := rfl

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

@[simp] theorem ReflQuiver.id_eq_id {C : Type*} [Category C] (X : C) : 𝟙rq X = 𝟙 X := rfl

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
theorem ext {V : Type u} [ReflQuiver.{v₁} V] {W : Type u₂} [ReflQuiver.{v₂} W] {F G : ReflPrefunctor V W}
    (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y : V) (f : X ⟶ Y),
      F.map f = Eq.recOn (h_obj Y).symm (Eq.recOn (h_obj X).symm (G.map f))) : F = G := by
  obtain ⟨⟨F_obj⟩⟩ := F
  obtain ⟨⟨G_obj⟩⟩ := G
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

@[simp]
theorem Functor.toReflPrefunctor_toPrefunctor {C D : Cat} (F : C ⥤ D) :
    (Functor.toReflPrefunctor F).toPrefunctor = F.toPrefunctor := rfl

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

@[simp] theorem of_val (C : Type u) [ReflQuiver C] : (ReflQuiv.of C) = C := rfl

/-- Category structure on `ReflQuiv` -/
instance category : LargeCategory.{max v u} ReflQuiv.{v, u} where
  Hom C D := ReflPrefunctor C D
  id C := ReflPrefunctor.id C
  comp F G := ReflPrefunctor.comp F G

theorem id_eq_id (X : ReflQuiv) : 𝟙 X = 𝟭rq X := rfl
theorem comp_eq_comp {X Y Z : ReflQuiv} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙rq G := rfl

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forget : Cat.{v, u} ⥤ ReflQuiv.{v, u} where
  obj C := ReflQuiv.of C
  map F := F.toReflPrefunctor

theorem forget_faithful {C D : Cat.{v, u}} (F G : C ⥤ D)
    (hyp : forget.map F = forget.map G) : F = G := by
  cases F
  cases G
  cases hyp
  rfl

theorem forget.Faithful : Functor.Faithful (forget) where
  map_injective := by
    intro V W f g hyp
    exact forget_faithful _ _ hyp

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forgetToQuiv : ReflQuiv.{v, u} ⥤ Quiv.{v, u} where
  obj V := Quiv.of V
  map F := F.toPrefunctor

theorem forgetToQuiv_faithful {V W : ReflQuiv} (F G : V ⥤rq W)
    (hyp : forgetToQuiv.map F = forgetToQuiv.map G) : F = G := by
  cases F
  cases G
  cases hyp
  rfl

theorem forgetToQuiv.Faithful : Functor.Faithful (forgetToQuiv) where
  map_injective := by
    intro V W f g hyp
    exact forgetToQuiv_faithful _ _ hyp

theorem forget_forgetToQuiv : forget ⋙ forgetToQuiv = Quiv.forget := rfl

end ReflQuiv

namespace Cat

inductive FreeReflRel {V} [ReflQuiver V] : (X Y : Paths V) → (f g : X ⟶ Y) → Prop
  | mk {X : V} : FreeReflRel X X (Quiver.Hom.toPath (𝟙rq X)) .nil

def FreeReflObj (V) [ReflQuiver V] :=
  Quotient (C := Cat.free.obj (Quiv.of V)) (FreeReflRel (V := V))

instance (V) [ReflQuiver V] : Category (FreeReflObj V) :=
  inferInstanceAs (Category (Quotient _))

def FreeReflObj.quotientFunctor (V) [ReflQuiver V] : Cat.free.obj (Quiv.of V) ⥤ FreeReflObj V :=
  Quotient.functor (C := Cat.free.obj (Quiv.of V)) (FreeReflRel (V := V))

theorem FreeReflObj.lift_unique' {V} [ReflQuiver V] {D} [Category D] (F₁ F₂ : FreeReflObj V ⥤ D)
    (h : quotientFunctor V ⋙ F₁ = quotientFunctor V ⋙ F₂) :
    F₁ = F₂ :=
  Quotient.lift_unique' (C := Cat.free.obj (Quiv.of V)) (FreeReflRel (V := V)) _ _ h

@[simps!]
def freeRefl : ReflQuiv.{v, u} ⥤ Cat.{max u v, u} where
  obj V := Cat.of (FreeReflObj V)
  map f := Quotient.lift _ ((by exact Cat.free.map f.toPrefunctor) ⋙ FreeReflObj.quotientFunctor _)
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
    rw [← Functor.assoc, Quotient.lift_spec, Functor.assoc,
      FreeReflObj.quotientFunctor, Quotient.lift_spec]

theorem freeRefl_naturality {X Y} [ReflQuiver X] [ReflQuiver Y] (f : X ⥤rq Y) :
    free.map (X := Quiv.of X) (Y := Quiv.of Y) f.toPrefunctor ⋙
    FreeReflObj.quotientFunctor ↑Y =
    FreeReflObj.quotientFunctor ↑X ⋙ freeRefl.map (X := ReflQuiv.of X) (Y := ReflQuiv.of Y) f := by
  simp [freeRefl, FreeReflObj.quotientFunctor]
  rw [Quotient.lift_spec]

def freeReflNatTrans : ReflQuiv.forgetToQuiv ⋙ Cat.free ⟶ freeRefl where
  app V := FreeReflObj.quotientFunctor V
  naturality _ _ f := freeRefl_naturality f

end Cat

namespace ReflQuiv

-- We might construct `of_lift_iso_self : Paths.of ⋙ lift F ≅ F`
-- (and then show that `lift F` is initial amongst such functors)
-- but it would require lifting quite a bit of machinery to quivers!

/-- ER: Universe error is why this is for u u.-/
@[simps! toPrefunctor obj map]
def adj.unit.app (V : ReflQuiv.{max u v, u}) : V ⥤rq forget.obj (Cat.freeRefl.obj V) where
  toPrefunctor := Quiv.adj.unit.app (V.toQuiv) ⋙q
    Quiv.forget.map (Cat.FreeReflObj.quotientFunctor V)
  map_id := fun X => by
    apply Quotient.sound
    simp [ReflPrefunctor.map_id]
    constructor

/-- ER: This is used in the proof of both triangle equalities. Should we simp?-/
theorem adj.unit.app_eq (V : ReflQuiv.{max u v, u}) :
    forgetToQuiv.map (adj.unit.app V) =
    Quiv.adj.unit.app (V.toQuiv) ≫
    Quiv.forget.map (Y := Cat.of _) (Cat.FreeReflObj.quotientFunctor V)
      := rfl

@[simps!]
def adj.counit.app (C : Cat) : Cat.freeRefl.obj (forget.obj C) ⥤ C := by
  fapply Quotient.lift
  · exact Quiv.adj.counit.app C
  · intro x y f g rel
    cases rel
    unfold Quiv.adj
    simp only [id_obj, forget_obj, Cat.free_obj, Quiv.forget_obj,
      Adjunction.mkOfHomEquiv_counit_app, Equiv.invFun_as_coe, Equiv.coe_fn_symm_mk, Quiv.lift_obj,
      ReflQuiver.id_eq_id, Quiv.lift_map, Prefunctor.mapPath_toPath, composePath_toPath,
      Prefunctor.mapPath_nil, composePath_nil]
    exact rfl

/-- ER: This is used in the proof of both triangle equalities. Should we simp?-/
@[simp]
theorem adj.counit.app_eq (C : Cat) :
    Cat.FreeReflObj.quotientFunctor C ⋙ adj.counit.app C =
    Quiv.adj.counit.app C := rfl

@[simp]
theorem adj.counit.app_eq' (C) [Category C] :
    Cat.FreeReflObj.quotientFunctor C ⋙ adj.counit.app (Cat.of C) =
    Quiv.adj.counit.app (Cat.of C) := rfl

/--
The adjunction between forming the free category on a quiver, and forgetting a category to a quiver.
-/
nonrec def adj : Cat.freeRefl.{max u v, u} ⊣ ReflQuiv.forget := by
  refine
    Adjunction.mkOfUnitCounit {
      unit := {
        app := adj.unit.app
        naturality := by
          intro V W f
          exact rfl
      }
      counit := {
        app := adj.counit.app
        naturality := by
          intro C D F
          apply Quotient.lift_unique'
          unfold adj.counit.app
          exact (Quiv.adj.counit.naturality F)
      }
      left_triangle := ?_
      right_triangle := ?_
    }
  · ext V
    apply Cat.FreeReflObj.lift_unique'
    simp only [id_obj, Cat.free_obj, Cat.of_α, comp_obj, Cat.freeRefl_obj_α, NatTrans.comp_app,
      forget_obj, whiskerRight_app, associator_hom_app, whiskerLeft_app, id_comp, NatTrans.id_app']
    rw [Functor.id_eq_id, Functor.comp_eq_comp]
    simp only [Cat.freeRefl_obj_α, Functor.comp_id]
    rw [← Functor.assoc, ← Cat.freeRefl_naturality, Functor.assoc]
    dsimp [Cat.freeRefl]
    rw [adj.counit.app_eq' (Cat.FreeReflObj V)]
    conv =>
      enter [1, 1, 2]
      apply (Quiv.comp_eq_comp (X := Quiv.of _) (Y := Quiv.of _) (Z := Quiv.of _) ..).symm
    rw [Cat.free.map_comp]
    show (_ ⋙ ((Quiv.forget ⋙ Cat.free).map (X := Cat.of _) (Y := Cat.of _)
      (Cat.FreeReflObj.quotientFunctor V))) ⋙ _ = _
    rw [Functor.assoc, ← Functor.comp_eq_comp]
    conv => enter [1, 2]; apply Quiv.adj.counit.naturality
    rw [Functor.comp_eq_comp, ← Functor.assoc, ← Functor.comp_eq_comp]
    conv => enter [1, 1]; apply Quiv.adj.left_triangle_components V.toQuiv
    simp [Functor.id_eq_id]
    exact Functor.id_comp _
  · ext C
    simp only [comp_obj, forget_obj, id_obj, NatTrans.comp_app, Cat.freeRefl_obj_α, of_val,
      whiskerLeft_app, associator_inv_app, whiskerRight_app, forget_map, id_comp,
      NatTrans.id_app']
    apply forgetToQuiv_faithful
    rw [forgetToQuiv.map_comp, adj.unit.app_eq, Category.assoc]
    dsimp
    rw [Functor.toReflPrefunctor_toPrefunctor, Quiv.comp_eq_comp, Quiv.comp_eq_comp]
    dsimp
    rw [adj.counit.app_eq C]
    exact Quiv.adj.right_triangle_components C

end ReflQuiv

open Opposite Simplicial
local notation3:1000 (priority := high) X " _[" n "]" =>
    (X : CategoryTheory.SimplicialObject _).obj (Opposite.op (SimplexCategory.mk n))

namespace SimplexCategory
def Δ (k : ℕ) := FullSubcategory fun n : SimplexCategory => n.len ≤ k

instance (k : ℕ) : Category (Δ k) := inferInstanceAs (Category (FullSubcategory ..))

end SimplexCategory

open SimplexCategory

/-- ER: The category of k-truncated simplicial sets is the category of contravariant functors from `SimplexCategory` to `Type u`. -/
def TruncSSet (k : ℕ)  : Type (u + 1) := (Δ k)ᵒᵖ ⥤ Type u

namespace TruncSSet

instance largeCategory {k : ℕ} : LargeCategory (TruncSSet k) := by
  dsimp only [TruncSSet]
  infer_instance

instance hasLimits {k : ℕ} : HasLimits (TruncSSet k) := by
  dsimp only [TruncSSet]
  infer_instance

instance hasColimits {k : ℕ} : HasColimits (TruncSSet k) := by
  dsimp only [TruncSSet]
  infer_instance

@[ext]
lemma hom_ext {k : ℕ} {X Y : TruncSSet k} {f g : X ⟶ Y} (hyp : ∀ (n : (Δ k)ᵒᵖ), f.app n = g.app n) : f = g := NatTrans.ext f g (funext hyp)

/-- The ulift functor `TruncSSet.{u} ⥤ TruncSSet.{max u v}` on truncated simplicial sets. -/
def uliftFunctor (k : ℕ) : TruncSSet.{u} k ⥤ TruncSSet.{max u v} k :=
  (whiskeringRight _ _ _).obj CategoryTheory.uliftFunctor.{v, u}

end TruncSSet

namespace SimplexCategory

def Δ.ι (k) : Δ k ⥤ SimplexCategory := fullSubcategoryInclusion _

def Δ.ι_fullyFaithful (k) : (Δ.ι k).FullyFaithful := fullyFaithfulFullSubcategoryInclusion _

instance Δ.ι_full (k) : (Δ.ι k).Full := FullyFaithful.full (ι_fullyFaithful k)

instance Δ.ι_faithful (k) : (Δ.ι k).Faithful := FullyFaithful.faithful (ι_fullyFaithful k)

instance Δ.ι.op_full (k) : (Δ.ι k).op.Full := by infer_instance

instance Δ.ι.op_faithful (k) : (Δ.ι k).op.Faithful := by infer_instance

def Δ.ι.op_fullyFaithful (k) : (Δ.ι k).op.FullyFaithful :=
  FullyFaithful.ofFullyFaithful (ι k).op

def truncation (k) : SSet ⥤ TruncSSet k := (whiskeringLeft _ _ _).obj (Δ.ι k).op

def skeletonAdj (k) : lan (Δ.ι k).op ⊣ truncation k := Lan.adjunction _ _
def coskeletonAdj (k) : truncation k ⊣ ran (Δ.ι k).op := Ran.adjunction _ _

instance coskeleton.reflective (k) : IsIso ((coskeletonAdj k).counit) :=
  Ran.reflective Type (Δ.ι k).op

instance skeleton.reflective (k) : IsIso ((skeletonAdj k).unit) :=
  Lan.coreflective Type (Δ.ι k).op

instance coskeleton.fullyfaithful (k) : (ran (D := Type) (Δ.ι k).op).FullyFaithful := by
  apply Adjunction.fullyFaithfulROfIsIsoCounit (coskeletonAdj k)

instance coskeleton.full (k) : (ran (D := Type) (Δ.ι k).op).Full := FullyFaithful.full (coskeleton.fullyfaithful k)

instance coskeleton.faithful (k) : (ran (D := Type) (Δ.ι k).op).Faithful :=
  FullyFaithful.faithful (coskeleton.fullyfaithful k)

instance coskeletonAdj.reflective (k) : Reflective (ran (D := Type) (Δ.ι k).op) :=
  Reflective.mk (truncation k) (coskeletonAdj k)

end SimplexCategory

-- open SimplexCategory -- ER: Is this a good idea?

def nerveFunctor₂ : Cat ⥤ TruncSSet 2 := nerveFunctor ⋙ SimplexCategory.truncation 2

def nerve₂ (C : Type*) [Category C] : TruncSSet 2 := nerveFunctor₂.obj (Cat.of C)

theorem nerve₂_restrictedNerve (C : Type*) [Category C] : (SimplexCategory.Δ.ι 2).op ⋙ (nerve C) = nerve₂ C := rfl

def nerve₂restrictedNerveIso (C : Type*) [Category C] : (SimplexCategory.Δ.ι 2).op ⋙ (nerve C) ≅ nerve₂ C := Iso.refl _
namespace Nerve

/-- ER: The natural map from a nerve. -/
def nerve2coskNatTrans : nerveFunctor ⟶ nerveFunctor₂ ⋙ ran (SimplexCategory.Δ.ι 2).op :=
  whiskerLeft nerveFunctor (SimplexCategory.coskeletonAdj 2).unit

/-- ER: A component of the above; universe error! -/
def nerve2coskNatTrans.component (C : Type 0) [Category.{0} C] (n : ℕ) :
    ((nerve C) _[n] ⟶ (Ran.loc (SimplexCategory.Δ.ι 2).op (nerveFunctor₂.obj (Cat.of C))) _[n]) :=
  (nerve2coskNatTrans.app (Cat.of C)).app (op [n])

/-- ER: The nerve is 2-coskeletal because the following map is an isomorphism making the
natural transformation a natural isomorphism. By construction this is a map from the type
(nerve C) _[n] into an object defined by a limit. To prove that this is an isomorphism, we will show
that this cone is a limit cone directly: showing any other cone factors uniquely through it.
The factorization will involve the explicit consruction of an n-simplex in the nerve of C from the
data in the cone. UNIVERSE ERROR!-/
theorem nerve2coskNatTrans.component_isIso (C : Type 0) [Category.{0} C] (n : ℕ) :
    IsIso (nerve2coskNatTrans.component C n) := by
  unfold component nerve2coskNatTrans whiskerLeft
  simp only [nerve_obj, SimplexCategory.len_mk, Ran.loc_obj, nerveFunctor_obj, Cat.of_α, comp_obj]
  unfold coskeletonAdj Ran.adjunction Ran.equiv
  simp only [whiskeringLeft_obj_obj, comp_obj, op_obj, Ran.loc_obj, Ran.cone, const_obj_obj,
    StructuredArrow.proj_obj, Adjunction.adjunctionOfEquivRight_unit_app, nerve_obj,
    Equiv.coe_fn_symm_mk, SimplexCategory.len_mk]
  let _ : HasLimit (Ran.diagram (SimplexCategory.Δ.ι 2).op (nerveFunctor₂.obj (Cat.of C)) { unop := [n] }) := inferInstance
  let c : Cone (Ran.diagram (Δ.ι 2).op ((truncation 2).obj (nerve C)) { unop := [n] }) :=
    { pt := ComposableArrows C n,
      π := {
        app := fun i ↦ (nerve C).map i.hom ≫ (𝟙 ((truncation 2).obj (nerve C)):).app i.right,
        naturality := sorry } }
  change IsIso (limit.lift _ c)
  let hc : IsLimit c := sorry
  exact inferInstanceAs (IsIso (hc.conePointUniqueUpToIso (limit.isLimit _)).hom)
  -- refine Iso.isIso_hom ?_
  -- refine conePointUniqueUpToIso ?_ (limit.islimit _)
  -- refine' IsLimit.hom_isIso _ (limit.isLimit _) _
  -- sorry
  /-
  C : Type
  inst✝ : Category.{0, 0} C
  n : ℕ
  ⊢ IsIso
    (limit.lift (Ran.diagram (Δ.ι 2).op ((truncation 2).obj (nerve C)) { unop := [n] })
      { pt := ComposableArrows C n,
        π := { app := fun i ↦ (nerve C).map i.hom ≫ (𝟙 ((truncation 2).obj (nerve C))).app i.right, naturality := ⋯ } })
  -/


abbrev nerve2cosk.diagram {C : Type 0} [Category.{0} C] (n : ℕ) :
    StructuredArrow { unop := [n] } (Δ.ι 2).op ⥤ Type :=
  Ran.diagram
    (SimplexCategory.Δ.ι 2).op (nerveFunctor₂.obj (Cat.of C)) (op ([n] : SimplexCategory))

abbrev nerve2cosk.cone {C : Type 0} [Category.{0} C] (n : ℕ) : Cone (nerve2cosk.diagram (C := C) n)
  := by
  refine Ran.cone (op ([n] : SimplexCategory)) (nerve₂restrictedNerveIso C).hom

  -- (nerve2coskNatTrans.app (Cat.of C))
/-- ER: Since a natural transformation is a natural isomorphism iff its components are isomorphisms: -/
theorem nerve2coskNatTrans.app_isIso (C : Type 0) [Category.{0} C] : IsIso (nerve2coskNatTrans.app (Cat.of C)) := by sorry
  -- refine Iso.isIso_hom (C := SSet) ?_
  -- apply NatIso.ofComponents


/-- ER: It follows that we have a natural isomorphism between nerveFunctor and nerveFunctor ⋙ cosk₂
whose components are the isomorphisms just established. -/
def nerve2coskIso : nerveFunctor ≅ nerveFunctor₂ ⋙ ran (SimplexCategory.Δ.ι 2).op := by sorry
--  refine asIso nerve2coskNatTrans ?_

--  refine IsIso.asIso nerve2coskNatTrans ?_



-- /-- ER: The truncated nerve of a category. -/
-- def nerve2truncated (C : Type u) [Category.{v} C] : (SimplexCategory.Δ 2)ᵒᵖ ⥤ Type (max u v) :=
--   (SimplexCategory.truncation 2).obj (nerve C)

-- /-- ER: A trivial natural transformation that induces something non-trivial. -/
-- def nerve2truncatedNatTrans (C : Type u) [Category.{v} C] :
--     ((whiskeringLeft _ _ _).obj (SimplexCategory.Δ.ι 2).op).obj (nerve C) ⟶ (nerve2truncated C) :=
--   𝟙 (nerve2truncated C)

-- def nerve2coskMap (C : Type u) [Category.{v} C] :
--     (nerve C) ⟶ Ran.loc (SimplexCategory.Δ.ι 2).op (nerve2truncated C) :=
--   (Ran.equiv (SimplexCategory.Δ.ι 2).op (nerve2truncated C) (nerve C)).symm
--     (nerve2truncatedNatTrans C)

-- /-- ER: A component of the above. -/
-- def nerve2coskMapApp (C : Type u) [Category.{v} C] (n : ℕ) :
--     ((nerve C) _[n] ⟶ (Ran.loc (SimplexCategory.Δ.ι 2).op (nerve2truncated C)) _[n]) :=
--   (nerve2coskMap C).app (op [n])

-- /-- ER: The nerve is 2-coskeletal because the following map is an isomorphism making the
-- natural transformation a natural isomorphism. By construction this is a map from the type
-- (nerve C) _[n] into an object defined by a limit. To prove that this is an isomorphism, we will show
-- that this cone is a limit cone directly: showing any other cone factors uniquely through it.
-- The factorization will involve the explicit consruction of an n-simplex in the nerve of C from the
-- data in the cone. -/
-- theorem nerve2coskMapApp.isIso (C : Type u) [Category.{v} C] (n : ℕ) :
--     IsIso (nerve2coskMapApp C n) := by
--   simp [nerve2coskMapApp, nerve2coskMap, Ran.equiv]
--   let Δ2 := StructuredArrow { unop := [n] } (SimplexCategory.Δ.ι 2).op
--   let D : Δ2 ⥤ Type (max u v) := Ran.diagram (SimplexCategory.Δ.ι 2).op (nerve2truncated C) { unop := [n] }
--   show IsIso
--     (limit.lift D
--       { pt := ComposableArrows C n,
--         π := { app := fun i ↦ (nerve C).map i.hom ≫ (nerve2truncatedNatTrans C).app i.right, naturality := _ } })
--   -- let _ : HasLimit (Ran.diagram (SimplexCategory.Δ.ι 2).op (nerve2truncated C) { unop := [n] }) := inferInstance
--   -- refine' IsLimit.hom_isIso _ (limit.isLimit _) _
--   sorry
end Nerve

section

def OneTruncation (S : SSet) := S _[0]

def OneTruncation.src {S : SSet} (f : S _[1]) : OneTruncation S :=
  S.map (op (SimplexCategory.δ (n := 0) 1)) f

def OneTruncation.tgt {S : SSet} (f : S _[1]) : OneTruncation S :=
  S.map (op (SimplexCategory.δ (n := 0) 0)) f

def OneTruncation.Hom {S : SSet} (X Y : OneTruncation S) :=
  {p : S _[1] // src p = X ∧ tgt p = Y}

instance (S : SSet) : ReflQuiver (OneTruncation S) where
  Hom X Y := OneTruncation.Hom X Y
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

section
variable {C : Type u} [Category.{v} C]
def OneTruncation.ofNerve.map {X Y : OneTruncation (nerve C)}
    (f : X ⟶ Y) : X.left ⟶ Y.left :=
  eqToHom (congrArg (·.left) f.2.1.symm) ≫ f.1.hom ≫ eqToHom (congrArg (·.left) f.2.2)

def OneTruncation.ofNerve.hom : OneTruncation (nerve C) ⥤rq C where
  obj := (·.left)
  map := OneTruncation.ofNerve.map
  map_id := fun X : ComposableArrows _ 0 => by
    simp [ofNerve.map]; exact ComposableArrows.map'_self _ 0

def OneTruncation.ofNerve.inv : C ⥤rq OneTruncation (nerve C) where
  obj := (.mk₀ ·)
  map := fun f => by
    refine ⟨.mk₁ f, ?_⟩
    constructor <;> apply ComposableArrows.ext <;>
      simp [SimplexCategory.len] <;> (intro 0; rfl)
  map_id := fun X : C => Subtype.ext <| by
    simp; apply ComposableArrows.ext <;> simp
    · rintro _ rfl; simp; rfl
    · intro; split <;> rfl

def OneTruncation.ofNerve (C : Type u) [Category.{u} C] :
    ReflQuiv.of (OneTruncation (nerve C)) ≅ ReflQuiv.of C := by
  refine {
    hom := ofNerve.hom
    inv := ofNerve.inv (C := C)
    hom_inv_id := ?_
    inv_hom_id := ?_
  }
  · have H1 {X X' Y : OneTruncation (nerve C)} (f : X ⟶ Y) (h : X = X') :
        (Eq.rec f h : X' ⟶ Y).1 = f.1 := by cases h; rfl
    have H2 {X Y Y' : OneTruncation (nerve C)} (f : X ⟶ Y) (h : Y = Y') :
        (Eq.rec f h : X ⟶ Y').1 = f.1 := by cases h; rfl
    fapply ReflPrefunctor.ext <;> simp
    · intro X
      apply ComposableArrows.ext₀
      rfl
    · intro X Y f
      obtain ⟨f, rfl, rfl⟩ := f
      apply Subtype.ext
      simp [ReflQuiv.comp_eq_comp]
      refine ((H2 _ _).trans ?_).symm
      refine (H1 _ _).trans ?_
      fapply ComposableArrows.ext₁
      · rfl
      · rfl
      · simp [ofNerve.inv, ofNerve.hom, ofNerve.map]; rfl
  · fapply ReflPrefunctor.ext <;> simp
    · intro X
      rfl
    · intro X Y f
      simp [ReflQuiv.comp_eq_comp, ReflQuiv.id_eq_id, ofNerve.inv, ofNerve.hom, ofNerve.map]

/-- ER: For use later. -/
def OneTruncation.ofNerveNatIso : nerveFunctor.{u,u} ⋙ SSet.oneTruncation ≅ ReflQuiv.forget := by
  refine NatIso.ofComponents (fun C => OneTruncation.ofNerve C) ?nat
  · intro C D F
    fapply ReflPrefunctor.ext <;> simp
    · intro X; rfl
    · intro X Y f
      obtain ⟨f, rfl, rfl⟩ := f
      unfold SSet.oneTruncation nerveFunctor mapComposableArrows toReflPrefunctor
      simp [ReflQuiv.comp_eq_comp, ofNerve, ofNerve.hom, ofNerve.map]

def helperAdj : Cat.freeRefl.{u, u} ⊣ nerveFunctor.{u, u} ⋙ SSet.oneTruncation.{u} :=
  (ReflQuiv.adj).ofNatIsoRight (OneTruncation.ofNerveNatIso.symm)

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

theorem opstuff.{w} (V : Cᵒᵖ ⥤ Type w) {X Y Z : C} {α : X ⟶ Y} {β : Y ⟶ Z} {γ : X ⟶ Z} {φ} :
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

theorem Cat.id_eq (C : Cat) : 𝟙 C = 𝟭 C := rfl
theorem Cat.comp_eq {C D E : Cat} (F : C ⟶ D) (G : D ⟶ E) : F ≫ G = F ⋙ G := rfl

def SSet.hoFunctorObj (V : SSet.{u}) : Type u :=
  Quotient (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation V))) (HoRel (V := V))

instance (V : SSet.{u}) : Category.{u} (SSet.hoFunctorObj V) :=
  inferInstanceAs (Category (Quotient ..))

def SSet.hoFunctorMap {V W : SSet.{u}} (F : V ⟶ W) : SSet.hoFunctorObj V ⥤ SSet.hoFunctorObj W :=
  Quotient.lift _ ((by exact (SSet.oneTruncation ⋙ Cat.freeRefl).map F) ⋙ Quotient.functor _)
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

def SSet.hoFunctor' : SSet.{u} ⥤ Cat.{u,u} where
  obj V := Cat.of (SSet.hoFunctorObj V)
  map {S T} F := SSet.hoFunctorMap F
  map_id S := by
    apply Quotient.lift_unique'
    simp [hoFunctorMap, Quotient.lift_spec]
    exact Eq.trans (Functor.id_comp ..) (Functor.comp_id _).symm
  map_comp {S T U} F G := by
    apply Quotient.lift_unique'
    simp [hoFunctorMap]
    rw [Quotient.lift_spec, Cat.comp_eq, Cat.comp_eq, ← Functor.assoc, Functor.assoc,
      Quotient.lift_spec, Functor.assoc, Quotient.lift_spec]
end

section

local macro:1000 (priority := high) X:term " _[" n:term "]₂" : term =>
    `(($X : TruncSSet 2).obj (Opposite.op ⟨SimplexCategory.mk $n, by decide⟩))

-- FIXME why doesn't this work?
-- local notation3:1000 (priority := high) (prettyPrint := false) " _[" n "]₂" =>
--     (X : TruncSSet 2).obj (Opposite.op ⟨SimplexCategory.mk n, by decide⟩)

set_option quotPrecheck false
local macro:max (priority := high) "[" n:term "]₂" : term =>
  `((⟨SimplexCategory.mk $n, by decide⟩ : Δ 2))

def OneTruncation₂ (S : TruncSSet 2) := S _[0]₂

abbrev δ₂ {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide) :
    (⟨[n], hn⟩ : Δ 2) ⟶ ⟨[n + 1], hn'⟩ := SimplexCategory.δ i

abbrev σ₂ {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide) :
    (⟨[n+1], hn⟩ : Δ 2) ⟶ ⟨[n], hn'⟩ := SimplexCategory.σ i

def OneTruncation₂.src {S : TruncSSet 2} (f : S _[1]₂) : OneTruncation₂ S :=
  S.map (op (δ₂ (n := 0) 1)) f

def OneTruncation₂.tgt {S : TruncSSet 2} (f : S _[1]₂) : OneTruncation₂ S :=
  S.map (op (δ₂ (n := 0) 0)) f

def OneTruncation₂.Hom {S : TruncSSet 2} (X Y : OneTruncation₂ S) :=
  {p : S _[1]₂ // src p = X ∧ tgt p = Y}

instance (S : TruncSSet 2) : ReflQuiver (OneTruncation₂ S) where
  Hom X Y := OneTruncation₂.Hom X Y
  id X := by
    refine ⟨S.map (op (σ₂ (n := 0) 0)) X, ?_, ?_⟩ <;>
    · change (S.map _ ≫ S.map _) X = X
      rw [← map_comp]
      rw [(_ : _ ≫ _ = 𝟙 _)]; simp
      show ({..} : Opposite _) = _; congr; dsimp [Δ]; ext ⟨i, _⟩
      let 0 := i
      rfl

def SSet.oneTruncation₂ : TruncSSet.{u} 2 ⥤ ReflQuiv.{u,u} where
  obj S := ReflQuiv.of (OneTruncation₂ S)
  map {S T} F := {
    obj := F.app (op [0]₂)
    map := fun f => by
      refine ⟨F.app (op [1]₂) f.1, ?_, ?_⟩
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

section
variable {V : SSet}

def OneTruncation₂.ofTwoTruncationIso (V : SSet) :
    ReflQuiv.of (OneTruncation₂ ((truncation 2).obj V)) ≅ ReflQuiv.of (OneTruncation V) := .refl _

def OneTruncation₂.nerve₂Iso (C : Cat) :
    ReflQuiv.of (OneTruncation₂ (nerve₂ C)) ≅ ReflQuiv.of (OneTruncation (nerve C)) := .refl _

def OneTruncation₂.nerve₂NatIso :
    nerveFunctor₂ ⋙ SSet.oneTruncation₂ ≅ nerveFunctor ⋙ SSet.oneTruncation := .refl _

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

def ι0₂ : [0]₂ ⟶ [2]₂ := δ₂ (n := 0) 1 ≫ δ₂ (n := 1) 1
def ι1₂ : [0]₂ ⟶ [2]₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 2
def ι2₂ : [0]₂ ⟶ [2]₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 1

def φ0₂ {V : TruncSSet 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map (op ι0₂) φ
def φ1₂ {V : TruncSSet 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map (op ι1₂) φ
def φ2₂ {V : TruncSSet 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map (op ι2₂) φ

def δ1₂ : [1]₂ ⟶ [2]₂ := δ₂ (n := 1) 1
def δ2₂ : [1]₂ ⟶ [2]₂ := δ₂ (n := 1) 2
def δ0₂ : [1]₂ ⟶ [2]₂ := δ₂ (n := 1) 0

def φ02₂ {V : TruncSSet 2} (φ : V _[2]₂) : φ0₂ φ ⟶ φ2₂ φ :=
  ⟨V.map (op δ1₂) φ, opstuff V rfl, opstuff V rfl⟩
def φ01₂ {V : TruncSSet 2} (φ : V _[2]₂) : φ0₂ φ ⟶ φ1₂ φ :=
  ⟨V.map (op δ2₂) φ, opstuff V (SimplexCategory.δ_comp_δ (j := 1) le_rfl), opstuff V rfl⟩
def φ12₂ {V : TruncSSet 2} (φ : V _[2]₂) : φ1₂ φ ⟶ φ2₂ φ :=
  ⟨V.map (op δ0₂) φ,
    opstuff V (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide)).symm,
    opstuff V rfl⟩

inductive HoRel₂ {V : TruncSSet 2} :
    (X Y : Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V))) → (f g : X ⟶ Y) → Prop
  | mk (φ : V _[2]₂) :
    HoRel₂ _ _
      (Quot.mk _ (.cons .nil (φ02₂ φ)))
      (Quot.mk _ (.cons (.cons .nil (φ01₂ φ)) (φ12₂ φ)))

theorem HoRel₂.ext_triangle {V} (X X' Y Y' Z Z' : OneTruncation₂ V)
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (f : X ⟶ Z) (f' : X' ⟶ Z') (hf : f.1 = f'.1)
    (g : X ⟶ Y) (g' : X' ⟶ Y') (hg : g.1 = g'.1)
    (h : Y ⟶ Z) (h' : Y' ⟶ Z') (hh : h.1 = h'.1) :
    HoRel₂ _ _ ((Quotient.functor _).map (.cons .nil f)) ((Quotient.functor _).map (.cons (.cons .nil g) h)) ↔
    HoRel₂ _ _ ((Quotient.functor _).map (.cons .nil f')) ((Quotient.functor _).map (.cons (.cons .nil g') h')) := by
  cases hX
  cases hY
  cases hZ
  congr! <;> apply Subtype.ext <;> assumption

def TruncSSet.hoFunctor₂Obj (V : TruncSSet.{u} 2) : Type u :=
  Quotient (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V))) (HoRel₂ (V := V))

instance (V : TruncSSet.{u} 2) : Category.{u} (TruncSSet.hoFunctor₂Obj V) :=
  inferInstanceAs (Category (Quotient ..))

def TruncSSet.hoFunctor₂Obj.quotientFunctor (V : TruncSSet.{u} 2) :
    Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V)) ⥤ TruncSSet.hoFunctor₂Obj V :=
  Quotient.functor (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V))) (HoRel₂ (V := V))

theorem TruncSSet.hoFunctor₂Obj.lift_unique' (V : TruncSSet.{u} 2)
    {D} [Category D] (F₁ F₂ : TruncSSet.hoFunctor₂Obj V ⥤ D)
    (h : quotientFunctor V ⋙ F₁ = quotientFunctor V ⋙ F₂) : F₁ = F₂ :=
  Quotient.lift_unique' (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V)))
    (HoRel₂ (V := V)) _ _ h

def TruncSSet.hoFunctor₂Map {V W : TruncSSet.{u} 2} (F : V ⟶ W) : TruncSSet.hoFunctor₂Obj V ⥤ TruncSSet.hoFunctor₂Obj W :=
  Quotient.lift _
    ((by exact (SSet.oneTruncation₂ ⋙ Cat.freeRefl).map F) ⋙
      TruncSSet.hoFunctor₂Obj.quotientFunctor _)
    (fun X Y f g hfg => by
      let .mk φ := hfg
      clear f g hfg
      simp [Quot.liftOn]
      apply Quotient.sound
      convert HoRel₂.mk (F.app (op _) φ) using 0
      apply HoRel₂.ext_triangle
      · exact congrFun (F.naturality (op ι0₂)) φ
      · exact congrFun (F.naturality (op ι1₂)) φ
      · exact congrFun (F.naturality (op ι2₂)) φ
      · exact congrFun (F.naturality (op δ1₂)) φ
      · exact congrFun (F.naturality (op δ2₂)) φ
      · exact congrFun (F.naturality (op δ0₂)) φ)

def TruncSSet.hoFunctor₂ : TruncSSet.{u} 2 ⥤ Cat.{u,u} where
  obj V := Cat.of (TruncSSet.hoFunctor₂Obj V)
  map {S T} F := TruncSSet.hoFunctor₂Map F
  map_id S := by
    apply Quotient.lift_unique'
    simp [hoFunctor₂Map, Quotient.lift_spec]
    exact Eq.trans (Functor.id_comp ..) (Functor.comp_id _).symm
  map_comp {S T U} F G := by
    apply Quotient.lift_unique'
    simp [hoFunctor₂Map, TruncSSet.hoFunctor₂Obj.quotientFunctor]
    rw [Quotient.lift_spec, Cat.comp_eq, Cat.comp_eq, ← Functor.assoc, Functor.assoc,
      Quotient.lift_spec, Functor.assoc, Quotient.lift_spec]

theorem TruncSSet.hoFunctor₂_naturality {X Y : TruncSSet.{u} 2} (f : X ⟶ Y) :
    (SSet.oneTruncation₂ ⋙ Cat.freeRefl).map f ⋙
    hoFunctor₂Obj.quotientFunctor Y =
    TruncSSet.hoFunctor₂Obj.quotientFunctor X ⋙ hoFunctor₂Map f := by
  simp [hoFunctor₂, hoFunctor₂Obj.quotientFunctor]
  exact rfl
end


/-- ER: We don't actually need this but it would be nice and potentially not too hard. -/
def hoFunctor.ofTwoTruncationIso (V : SSet) :
    TruncSSet.hoFunctor₂Obj ((truncation 2).obj V) ≅ SSet.hoFunctorObj V := sorry

/-- ER: We don't actually need this but it would be nice and potentially not too hard. -/
def hoFunctor.ofTwoTruncationNatIso : truncation 2 ⋙ TruncSSet.hoFunctor₂ ≅ SSet.hoFunctor' := sorry

def nerve₂Adj.NatIso : nerveFunctor₂ ⋙ SSet.oneTruncation₂ ≅ ReflQuiv.forget :=
  OneTruncation₂.nerve₂NatIso ≪≫ OneTruncation.ofNerveNatIso

@[simps!]
def nerve₂Adj.counit.app (C : Cat) : TruncSSet.hoFunctor₂.obj (nerveFunctor₂.obj C) ⥤ C := by
  fapply Quotient.lift
  · exact (whiskerRight (nerve₂Adj.NatIso).hom _ ≫
      ReflQuiv.adj.counit).app C
  · intro x y f g rel
    cases rel; rename_i φ
    simp [ReflQuiv.adj, Quot.liftOn, Cat.FreeReflObj.quotientFunctor, Quotient.functor,
      Quiv.adj, Quiv.id_eq_id]
    change OneTruncation.ofNerve.map (φ02₂ φ) =
      OneTruncation.ofNerve.map (φ01₂ φ) ≫ OneTruncation.ofNerve.map (φ12₂ φ)
    simp [OneTruncation.ofNerve.map]
    exact φ.map_comp (X := (0 : Fin 3)) (Y := 1) (Z := 2)
      (homOfLE (by decide)) (homOfLE (by decide))

/-- ER: This is used in the proof of both triangle equalities. Should we simp?-/
@[simp]
theorem nerve₂Adj.counit.app_eq (C : Cat.{0,0}) :
    TruncSSet.hoFunctor₂Obj.quotientFunctor (nerve₂ C) ⋙ nerve₂Adj.counit.app C =
    (whiskerRight (nerve₂Adj.NatIso).hom _ ≫
      (ReflQuiv.adj.{0,0}).counit).app C := rfl

/-- ER: Two weird things about this statement:
(i) I had to kill the universes
(ii) I had to convert one composition in cat to functor composition (but not the other)?
-/
theorem nerve₂Adj.counit.naturality ⦃C D : Cat.{0,0}⦄ (F : C ⟶ D) :
    (nerveFunctor₂ ⋙ TruncSSet.hoFunctor₂).map F ⋙ nerve₂Adj.counit.app D =
      nerve₂Adj.counit.app C ⋙ F := by
  apply TruncSSet.hoFunctor₂Obj.lift_unique'
  have := TruncSSet.hoFunctor₂_naturality (nerveFunctor₂.map F)
  conv =>
    lhs; rw [← Functor.assoc]; lhs; apply this.symm
  simp only [Cat.freeRefl_obj_α, ReflQuiv.of_val, comp_obj, Functor.comp_map]
  rw [← Functor.assoc _ _ F]
  conv =>
    rhs; lhs; apply (nerve₂Adj.counit.app_eq C)
  conv =>
    rhs
    apply ((whiskerRight (nerve₂Adj.NatIso).hom Cat.freeRefl ≫ ReflQuiv.adj.counit).naturality F).symm
  simp [Functor.comp_eq_comp, app]
  rw [Functor.assoc]
  simp [TruncSSet.hoFunctor₂Obj.quotientFunctor]
  rw [Quotient.lift_spec]

def nerve₂Adj.counit : nerveFunctor₂ ⋙ TruncSSet.hoFunctor₂ ⟶ (𝟭 Cat) where
  app := nerve₂Adj.counit.app
  naturality := by
    simp only [comp_obj, id_obj, Functor.comp_map, Functor.id_map]
    exact nerve₂Adj.counit.naturality


def toNerve₂.mk {X : TruncSSet 2} {C : Cat}
    (f : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C)
    (hyp : (φ : X _[2]₂) →
      f.map (φ02₂ φ) =
        CategoryStruct.comp (obj := C) (f.map (φ01₂ φ)) (f.map (φ12₂ φ)))
    : X ⟶ nerveFunctor₂.obj C where
      app := by
        intro ⟨ ⟨ n, hn⟩⟩
        induction' n using SimplexCategory.rec with n
        match n with
        | 0 => sorry
        | 1 => sorry
        | 2 => sorry
      naturality := sorry

/-- ER: We might prefer this version where we are missing the analogue of the hypothesis hyp conjugated by the isomorphism nerve₂Adj.NatIso.app C -/
def toNerve₂.mk' {X : TruncSSet.{0} 2} {C : Cat}
    (f : SSet.oneTruncation₂.obj X ⟶ SSet.oneTruncation₂.obj (nerveFunctor₂.obj C))
    (hyp : (φ : X _[2]₂) →
      (f ≫ (nerve₂Adj.NatIso.app C).hom).map (φ02₂ φ)
      = CategoryStruct.comp (obj := C) ((f ≫ (nerve₂Adj.NatIso.app C).hom).map (φ01₂ φ)) ((f ≫ (nerve₂Adj.NatIso.app C).hom).map (φ12₂ φ)))
    : X ⟶ nerveFunctor₂.obj C :=
  toNerve₂.mk (f ≫ (nerve₂Adj.NatIso.app C).hom) hyp

/-- Now do a case split. For n = 0 and n = 1 this is covered by the hypothesis.
         For n = 2 this is covered by the new lemma above.-/
theorem toNerve₂.ext {X : TruncSSet 2} {C : Cat} (f g : X ⟶ nerve₂ C)
    (hyp : SSet.oneTruncation₂.map f = SSet.oneTruncation₂.map g) : f = g := by
  ext ⟨ ⟨ n , hn⟩⟩
  induction' n using SimplexCategory.rec with n
  match n with
  | 0 => sorry
  | 1 => sorry
  | 2 => sorry

/-- ER: Universe error is why this is for u u.-/
-- @[simps! toPrefunctor obj map]
def nerve₂Adj.unit.app (X : TruncSSet.{u} 2) : X ⟶ nerveFunctor₂.obj (TruncSSet.hoFunctor₂.obj X) := sorry
  -- toPrefunctor := Quiv.adj.unit.app (V.toQuiv) ⋙q
  --   Quiv.forget.map (Cat.FreeReflObj.quotientFunctor V)
  -- map_id := fun X => by
  --   apply Quotient.sound
  --   simp [ReflPrefunctor.map_id]
  --   constructor

/-- ER: Universe error again-/
theorem nerve₂Adj.unit.app_eq (X : TruncSSet.{0} 2) :
    SSet.oneTruncation₂.map (nerve₂Adj.unit.app X) =
    ReflQuiv.adj.unit.app (SSet.oneTruncation₂.obj X) ⋙rq
    (TruncSSet.hoFunctor₂Obj.quotientFunctor X).toReflPrefunctor ⋙rq
    nerve₂Adj.NatIso.inv.app (TruncSSet.hoFunctor₂.obj X) := sorry

theorem nerve₂.two_simplex_property {C : Type*} [Category C] (F G : nerve₂ C _[2]₂)
    (h₀ : (nerve₂ C).map (op ι0₂) F = (nerve₂ C).map (op ι0₂) G)
    (h₁ : (nerve₂ C).map (op ι0₂) F = (nerve₂ C).map (op ι1₂) G)
    (h₂ : (nerve₂ C).map (op ι0₂) F = (nerve₂ C).map (op ι2₂) G)
    (h₀₁ : (nerve₂ C).map (op δ2₂) F = (nerve₂ C).map (op δ2₂) G)
    (h₁₂ : (nerve₂ C).map (op δ0₂) F = (nerve₂ C).map (op δ0₂) G)
    (h₀₂ : (nerve₂ C).map (op δ1₂) F = (nerve₂ C).map (op δ1₂) G)
  : F = G := sorry

/--
The adjunction between forming the free category on a quiver, and forgetting a category to a quiver.
-/
nonrec def nerve₂Adj : TruncSSet.hoFunctor₂ ⊣ nerveFunctor₂ := by
  refine
    Adjunction.mkOfUnitCounit {
      unit := {
        app := nerve₂Adj.unit.app
        naturality := by sorry
          -- intro V W f
          -- exact rfl
      }
      counit := nerve₂Adj.counit
      left_triangle := ?_
      right_triangle := ?_
    }
  · ext X
    apply TruncSSet.hoFunctor₂Obj.lift_unique'
    simp only [id_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, comp_obj, NatTrans.comp_app,
      whiskerRight_app, associator_hom_app, whiskerLeft_app, id_comp, NatTrans.id_app']
    rw [← Functor.comp_eq_comp (TruncSSet.hoFunctor₂Obj.quotientFunctor X) (𝟙 (TruncSSet.hoFunctor₂.obj X)), comp_id]
    rw [Functor.comp_eq_comp, ← Functor.assoc]
    conv =>
      lhs; lhs; apply (TruncSSet.hoFunctor₂_naturality (nerve₂Adj.unit.app X)).symm
    simp only [comp_obj, Cat.freeRefl_obj_α, Functor.comp_map]
    rw [nerve₂Adj.unit.app_eq X]
    rw [Functor.assoc]
    conv =>
      lhs; rhs
      apply (nerve₂Adj.counit.app_eq (TruncSSet.hoFunctor₂.obj X))
    simp only [comp_obj, ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val,
      ReflPrefunctor.comp_assoc, NatTrans.comp_app, id_obj, whiskerRight_app]
    rw [← Functor.comp_eq_comp, ← assoc]
    rw [← Cat.freeRefl.map_comp]
    rw [ReflQuiv.comp_eq_comp, ReflPrefunctor.comp_assoc]
    simp only [ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, ReflPrefunctor.comp_assoc]
    rw [← ReflQuiv.comp_eq_comp]
    simp only [ReflQuiv.forget_obj, comp_obj, Iso.inv_hom_id_app]
    rw [ReflQuiv.id_eq_id]
    simp_rw [ReflPrefunctor.comp_id (U := ReflQuiv.of _) (V := ReflQuiv.of ↑(TruncSSet.hoFunctor₂.obj X)) ((TruncSSet.hoFunctor₂Obj.quotientFunctor X).toReflPrefunctor)]
    rw [← ReflQuiv.comp_eq_comp (Z := ReflQuiv.of _) (ReflQuiv.adj.unit.app (SSet.oneTruncation₂.obj X)) ((TruncSSet.hoFunctor₂Obj.quotientFunctor X).toReflPrefunctor)]
    simp only [ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, map_comp, assoc]
    have nat := ReflQuiv.adj.counit.naturality
      (X := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ X)))
      (Y := TruncSSet.hoFunctor₂.obj X) (TruncSSet.hoFunctor₂Obj.quotientFunctor X)
    dsimp at nat
    rw [nat]
    rw [← assoc]
    conv => lhs; lhs; apply ReflQuiv.adj.left_triangle_components (SSet.oneTruncation₂.obj X)
    simp
  · apply NatTrans.ext
    apply funext
    intro C
    simp only [comp_obj, id_obj, NatTrans.comp_app, whiskerLeft_app, associator_inv_app,
      whiskerRight_app, id_comp, NatTrans.id_app']
    apply toNerve₂.ext
    simp only [map_comp, map_id]
    rw [nerve₂Adj.unit.app_eq]
    simp only [comp_obj, ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val,
      ReflPrefunctor.comp_assoc]
    rw [← ReflQuiv.comp_eq_comp, ← ReflQuiv.comp_eq_comp (X := ReflQuiv.of _) (Y := ReflQuiv.of _) (Z := ReflQuiv.of _), assoc, assoc]
    rw [← Functor.comp_map, ← nerve₂Adj.NatIso.inv.naturality]
    conv => lhs; rhs; rw [← assoc] --
    show _ ≫ (ReflQuiv.forget.map _ ≫ ReflQuiv.forget.map _) ≫ _ = _
    rw [← ReflQuiv.forget.map_comp]
    show _ ≫ ReflQuiv.forget.map (TruncSSet.hoFunctor₂Obj.quotientFunctor (nerve₂ ↑C) ⋙ nerve₂Adj.counit.app C) ≫ _ = _
    rw [nerve₂Adj.counit.app_eq]
    simp only [ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, NatTrans.comp_app,
      comp_obj, id_obj, whiskerRight_app]
    rw [ReflQuiv.forget.map_comp]
    rw [← Functor.comp_map, ← assoc, ← assoc]
    have := ReflQuiv.adj.unit.naturality (nerve₂Adj.NatIso.hom.app C)
    simp only [Functor.comp_obj] at this
    conv => lhs; lhs; lhs; apply this.symm
    simp only [Cat.freeRefl_obj_α, id_obj, Functor.id_map]
    slice_lhs 2 3 =>
      rw [ReflQuiv.adj.right_triangle_components C]
    simp

/-- ER: The underlying refl Quiver of this functor is essentially the unit of ReflQuiver.adj composed with the quotient functor. Then we just have to check that this preserves composition. Note universe error. -/
def nerve₂Adj.counit.app.inv.reflPrefunctor (C : Cat.{0}) : C ⥤rq TruncSSet.hoFunctor₂.obj (nerveFunctor₂.obj C) :=
  ReflQuiv.adj.unit.app (ReflQuiv.of C) ⋙rq
    (Cat.freeRefl.map (nerve₂Adj.NatIso.inv.app C)).toReflPrefunctor ⋙rq
    (TruncSSet.hoFunctor₂Obj.quotientFunctor (nerveFunctor₂.obj C)).toReflPrefunctor

/-- ER: Use f and g to build a 2-simplex in the nerve of C and use the corresponding HoRel₂. -/
def nerve₂Adj.counit.app.inv (C : Cat) : C ⥤ TruncSSet.hoFunctor₂.obj (nerveFunctor₂.obj C) where
  __ := nerve₂Adj.counit.app.inv.reflPrefunctor C
  map_comp := by
    intros X Y Z f g
    dsimp
    unfold inv.reflPrefunctor
    apply Quotient.sound
    sorry

theorem nerve₂Adj.counit.app.inv_reflPrefunctor (C : Cat) : ReflQuiv.forget.map (nerve₂Adj.counit.app.inv C) =
  ReflQuiv.adj.unit.app (ReflQuiv.of C) ⋙rq (Cat.freeRefl.map (nerve₂Adj.NatIso.inv.app C)).toReflPrefunctor ⋙rq (TruncSSet.hoFunctor₂Obj.quotientFunctor (nerveFunctor₂.obj C)).toReflPrefunctor := rfl

/-- ER: Killed universes to avoid universe error. -/
def nerve₂Adj.counit.app.iso (C : Cat.{0,0}) : TruncSSet.hoFunctor₂.obj (nerveFunctor₂.obj C) ≅ C where
  hom := nerve₂Adj.counit.app _
  inv := nerve₂Adj.counit.app.inv _
  hom_inv_id := sorry
  inv_hom_id := by
    apply ReflQuiv.forget_faithful
    rw [Functor.map_comp]
    rw [nerve₂Adj.counit.app.inv_reflPrefunctor C]
    rw [ReflQuiv.comp_eq_comp, ReflPrefunctor.comp_assoc]
    rw [← ReflQuiv.forget_map]
    show _ ⋙rq _ ⋙rq (ReflQuiv.forget.map _ ≫ ReflQuiv.forget.map (app C)) = _
    rw [← Functor.map_comp]
    have eq := nerve₂Adj.counit.app_eq C
    rw [← Functor.comp_eq_comp _ (app C)] at eq
    unfold nerve₂ at eq
    sorry -- ER: Should be able to rewrite at the eq.

-- ER: Can't infer argument is a morphism in a category.
-- instance nerve₂Adj.counit.app_isIso (C : Cat) : IsIso (nerve₂Adj.counit.app C : TruncSSet.hoFunctor₂.obj (nerveFunctor₂.obj C) ⟶ C) :=
--   Iso.isIso_hom (nerve₂Adj.counit.app.iso C)

-- ER: Should work using the above
instance nerve₂Adj.counit_isIso : IsIso (nerve₂Adj.counit) := by sorry
--  apply NatIso.isIso_of_isIso_app

def nerve₂Adj.counit.iso : nerveFunctor₂ ⋙ TruncSSet.hoFunctor₂ ≅ (𝟭 Cat) := asIso nerve₂Adj.counit

-- ER: Should work.
instance nerveFunctor₂.fullyfaithful : nerveFunctor₂.FullyFaithful := by sorry
--  apply Adjunction.fullyFaithfulROfIsIsoCounit nerve₂Adj

instance : nerveFunctor₂.Full := FullyFaithful.full nerveFunctor₂.fullyfaithful

instance : nerveFunctor₂.Faithful := FullyFaithful.faithful nerveFunctor₂.fullyfaithful

instance nerve₂Adj.reflective : Reflective nerveFunctor₂ := Reflective.mk TruncSSet.hoFunctor₂ nerve₂Adj

end

def SSet.hoFunctor : SSet.{u} ⥤ Cat.{u,u} := truncation 2 ⋙ TruncSSet.hoFunctor₂

def nerveAdjunction : SSet.hoFunctor ⊣ nerveFunctor :=
  Adjunction.ofNatIsoRight
    ((coskeletonAdj 2).comp nerve₂Adj) Nerve.nerve2coskIso.symm

-- ER: Repleteness exists for full and faithful functors but not fully faithful functors, which is why we do this inefficiently.
instance nerveFunctor.faithful : nerveFunctor.Faithful := by
  have := coskeleton.faithful 2
  have : (nerveFunctor₂ ⋙ ran (Δ.ι 2).op).Faithful := by
    refine Faithful.comp nerveFunctor₂ (ran (Δ.ι 2).op)
  refine Functor.Faithful.of_iso Nerve.nerve2coskIso.symm

instance nerveFunctor.full : nerveFunctor.Full := by
  have := coskeleton.full 2
  have : (nerveFunctor₂ ⋙ ran (Δ.ι 2).op).Full := by
    refine Full.comp nerveFunctor₂ (ran (Δ.ι 2).op)
  refine Functor.Full.of_iso Nerve.nerve2coskIso.symm

instance nerveFunctor.fullyfaithful : nerveFunctor.FullyFaithful :=
  FullyFaithful.ofFullyFaithful nerveFunctor

instance nerveCounit_isIso : IsIso (nerveAdjunction.counit) :=
  Adjunction.counit_isIso_of_R_fully_faithful _

def nerveCounitNatIso : nerveFunctor ⋙ SSet.hoFunctor ≅ 𝟭 Cat := asIso (nerveAdjunction.counit)

instance : Reflective nerveFunctor where
  L := SSet.hoFunctor
  adj := nerveAdjunction

instance : HasColimits Cat :=
  hasColimits_of_reflective nerveFunctor

section preservesProducts

open Limits

/-- ER: This should be an instance of a theorem in mathlib about evaluation in functor categories preserving limits that exist. Statement has a universe level error.-/
-- def simplexBinaryProducts (X Y : SSet) (n : ℕ) : (X × Y) _[n] ≅ X _[n] × Y _[n] := by sorry

def hoFunctorPreservesExplicitBinaryProduct {X Y : SSet.{u}}
    (s : BinaryFan X Y) (hyp : IsLimit s) :
    IsLimit (BinaryFan.mk (SSet.hoFunctor.map (BinaryFan.fst s)) (SSet.hoFunctor.map (BinaryFan.snd s))) := by
  have := limitObjIsoLimitCompEvaluation (pair X Y) (op [0])
  simp at this
  refine BinaryFan.isLimitMk ?lift ?fac_left ?fac_right ?uniq
  · sorry
  · sorry
  · sorry
  · sorry



def hoFunctorPreservesBinaryProduct {X Y : SSet.{u}} : PreservesLimit (pair X Y) SSet.hoFunctor where
  preserves := by
    intro c clim
    sorry

def hoFunctorPreservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) SSet.hoFunctor where
      preservesLimit := by
        rintro K
        have := diagramIsoPair K
        sorry


end preservesProducts
