import Mathlib.AlgebraicTopology.Nerve
import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Monad.Limits

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
def adj.unit.app (V : ReflQuiv.{u, u}) : V ⥤rq forget.obj (Cat.freeRefl.obj V) where
  toPrefunctor := Quiv.adj.unit.app (V.toQuiv) ⋙q
    Quiv.forget.map (Cat.FreeReflObj.quotientFunctor V)
  map_id := fun X => by
    apply Quotient.sound
    simp [ReflPrefunctor.map_id]
    constructor

/-- ER: This is used in the proof of both triangle equalities. Should we simp?-/
theorem adj.unit.app_eq (V : ReflQuiv.{u, u}) :
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
nonrec def adj : Cat.freeRefl ⊣ ReflQuiv.forget := by
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
    simp only [id_obj, Cat.free_obj, Cat.of_α, comp_obj, NatTrans.comp_app,
      forget_obj, of_val, whiskerRight_app, adj.unit.app_toPrefunctor, associator_hom_app,
      whiskerLeft_app, id_comp, NatTrans.id_app']
    rw [Functor.id_eq_id, Functor.comp_eq_comp]
    simp only [Cat.freeRefl_obj_α, Functor.comp_id]
    conv => enter [1, 1]; simp only [Cat.freeRefl]
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
    conv => enter [1, 1]; apply  Quiv.adj.left_triangle_components V.toQuiv
    simp [Functor.id_eq_id]
    exact Functor.id_comp _
  · ext C
    simp only [comp_obj, forget_obj, id_obj, NatTrans.comp_app, Cat.freeRefl_obj_α, of_val,
      whiskerLeft_app, associator_inv_app, whiskerRight_app, forget_map, id_comp,
      NatTrans.id_app']
    apply forgetToQuiv_faithful
    rw [forgetToQuiv.map_comp, adj.unit.app_eq, assoc]
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
def truncSSet (k : ℕ)  : Type (u + 1) := (Δ k)ᵒᵖ ⥤ Type u

namespace truncSSet

instance largeCategory {k : ℕ} : LargeCategory (truncSSet k) := by
  dsimp only [truncSSet]
  infer_instance

instance hasLimits {k : ℕ} : HasLimits (truncSSet k) := by
  dsimp only [truncSSet]
  infer_instance

instance hasColimits {k : ℕ} : HasColimits (truncSSet k) := by
  dsimp only [truncSSet]
  infer_instance

@[ext]
lemma hom_ext {k : ℕ} {X Y : truncSSet k} {f g : X ⟶ Y} (hyp : ∀ (n : (Δ k)ᵒᵖ), f.app n = g.app n) : f = g := NatTrans.ext f g (funext hyp)

/-- The ulift functor `truncSSet.{u} ⥤ truncSSet.{max u v}` on truncated simplicial sets. -/
def uliftFunctor (k : ℕ) : truncSSet.{u} k ⥤ truncSSet.{max u v} k :=
  (whiskeringRight _ _ _).obj CategoryTheory.uliftFunctor.{v, u}

end truncSSet

namespace SimplexCategory

def Δ.ι (k) : Δ k ⥤ SimplexCategory := fullSubcategoryInclusion _

def Δ.ι_fullyFaithful (k) : (Δ.ι k).FullyFaithful := fullyFaithfulFullSubcategoryInclusion _

def truncation (k) : SSet ⥤ truncSSet k := (whiskeringLeft _ _ _).obj (Δ.ι k).op

def skeletonAdj (k) : lan (Δ.ι k).op ⊣ truncation k := Lan.adjunction _ _
def coskeletonAdj (k) : truncation k ⊣ ran (Δ.ι k).op := Ran.adjunction _ _

end SimplexCategory

/- ER: Should these generalize to arbitrary k?-/
def cosk₂ : SSet ⥤ SSet :=
  SimplexCategory.truncation 2 ⋙ ran (SimplexCategory.Δ.ι 2).op

def nerveFunctor₂ : Cat ⥤ truncSSet 2 := nerveFunctor ⋙ SimplexCategory.truncation 2

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
    IsIso (nerve2coskNatTrans.component C n) := by sorry

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




def OneTruncation (S : SSet) := S _[0]

def OneTruncation.Hom {S : SSet} (X Y : OneTruncation S) :=
  {p : S _[1] //
    S.map (op (SimplexCategory.δ (n := 0) 1)) p = X ∧
    S.map (op (SimplexCategory.δ (n := 0) 0)) p = Y}

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
variable {C : Type u} [Category.{u} C]
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
    ReflQuiv.of (OneTruncation (nerve C)) ≅ ReflQuiv.of C where
  hom := ofNerve.hom
  inv := ofNerve.inv (C := C)
  hom_inv_id := by
    fapply ReflPrefunctor.ext <;> simp
    · intro X
      apply ComposableArrows.ext₀
      simp [ReflQuiv.comp_eq_comp]; rfl
    · intro X Y f
      obtain ⟨f, rfl, rfl⟩ := f
      apply Subtype.ext
      simp [ReflQuiv.comp_eq_comp]
      fapply ComposableArrows.ext₁ <;> simp [ReflQuiv.comp_eq_comp, ReflQuiv.id_eq_id]
      · change f.left = _
        congr!
        sorry
      · sorry
      · sorry
  inv_hom_id := sorry

/-- ER: For use later. -/
def OneTruncation.ofNerveNatIso : nerveFunctor ⋙ SSet.oneTruncation ≅ ReflQuiv.forget := by
  refine NatIso.ofComponents (fun C => OneTruncation.ofNerve C) ?nat
  · intro C D F
    fapply ReflPrefunctor.ext <;> simp
    · intro X
      unfold SSet.oneTruncation nerveFunctor mapComposableArrows toReflPrefunctor
      exact rfl
    · intro X Y f
      obtain ⟨f, rfl, rfl⟩ := f
      unfold SSet.oneTruncation nerveFunctor mapComposableArrows toReflPrefunctor
      simp [ReflQuiv.comp_eq_comp]
      sorry

/-- ER: Commenting out because of universe failure but otherwise I think this should work.-/
-- def helperAdj : Cat.freeRefl.{u, u} ⊣ nerveFunctor.{u, u} ⋙ SSet.oneTruncation.{u} :=
--   (ReflQuiv.adj).ofNatIsoRight (OneTruncation.ofNerveNatIso.symm)

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

def SSet.hoFunctor : SSet.{u} ⥤ Cat.{u,u} where
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

def reflectiveOfCounitIso {C D} [Category C] [Category D] (R : D ⥤ C) (L : C ⥤ D) (adj : L ⊣ R)
  (h : IsIso adj.counit) : Reflective R where
  L := L
  adj := adj
  map_injective := sorry
  map_surjective := sorry

def nerveCounitApp (C : Type u) [Category.{u} C] : SSet.hoFunctorObj (nerve C) ⥤ C := by
  stop
  refine Quotient.lift _ ((ReflQuiv.adj.homEquiv _ (Cat.of C)).symm OneTruncation.ofNerve.hom) ?_
  rintro _ _ _ _ ⟨φ⟩
  simp
  sorry

def nerveCounitIso (C : Type u) [Category.{u} C] :
    Cat.of (SSet.hoFunctorObj (nerve C)) ≅ Cat.of C where
  hom := nerveCounitApp C
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

theorem nerveCounit.naturality {C D : Type u} [Category C] [Category D] (F : C ⥤ D) :
  SSet.hoFunctorMap (nerveFunctor.map (X := Cat.of C) (Y := Cat.of D) F) ⋙ nerveCounitApp D =
  nerveCounitApp C ⋙ F := sorry

def nerveCounit : nerveFunctor ⋙ SSet.hoFunctor ⟶ 𝟭 Cat where
  app C := nerveCounitApp C
  naturality X Y f := by
    simp [Functor.comp_eq_comp, SSet.hoFunctor]
    convert nerveCounit.naturality f

def nerveCounitNatIso : nerveFunctor ⋙ SSet.hoFunctor ≅ 𝟭 Cat :=
  NatIso.ofComponents (fun C => nerveCounitIso C) (fun f => by
    simp [nerveCounitIso, Functor.comp_eq_comp, SSet.hoFunctor]
    convert nerveCounit.naturality f)

def nerveAdjunction : SSet.hoFunctor ⊣ nerveFunctor where
  homEquiv V C := {
    toFun := fun F => by
      stop
      have : _ ⟶ (_ : Cat) := Quotient.functor _ ⋙ F
      have : OneTruncation V ⥤rq C := ReflQuiv.adj.homEquiv (ReflQuiv.of (OneTruncation V)) C this
      have : ReflQuiv.of (OneTruncation (nerveFunctor.obj C)) ≅ ReflQuiv.of C := OneTruncation.ofNerve _
      sorry
    invFun := sorry
    left_inv := sorry
    right_inv := sorry
  }
  unit.app X := by simp; sorry
  counit := nerveCounitNatIso.hom

instance : Reflective nerveFunctor.{u} :=
  reflectiveOfCounitIso _ _ nerveAdjunction.{u} (Iso.isIso_hom nerveCounitNatIso.{u})

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

-- def hoFunctor : SSet ⥤ Cat :=
--   ColimitAdj.extendAlongYoneda SimplexCategory.toCat
