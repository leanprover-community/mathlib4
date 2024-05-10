
import Lean.Elab.Term
universe w v v₁ v₂ v₃ u u₁ u₂ u₃

open Lean

elab "Sort*" : term => do
  let u ← Lean.Meta.mkFreshLevelMVar
  Elab.Term.levelMVarToParam (.sort u)

/-- The syntax `variable (X Y ... Z : Type*)` creates a new distinct implicit universe variable
`> 0` for each variable in the sequence. -/
elab "Type*" : term => do
  let u ← Lean.Meta.mkFreshLevelMVar
  Elab.Term.levelMVarToParam (.sort (.succ u))
section FunctionStuff

def Function.Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

end FunctionStuff

section FunLikeStuff

class DFunLike (F : Sort*) (α : outParam (Sort*)) (β : outParam <| α → Sort*) where
  /-- The coercion from `F` to a function. -/
  coe : F → ∀ a : α, β a
  /-- The coercion to functions must be injective. -/
  coe_injective' : Function.Injective coe

abbrev FunLike F α β := DFunLike F α fun _ => β

variable (F α : Sort*) (β : α → Sort*)

variable {F α β} [i : DFunLike F α β]

instance (priority := 100) hasCoeToFun : CoeFun F (fun _ ↦ ∀ a : α, β a) where
  coe := @DFunLike.coe _ _ β _ -- need to make explicit to beta reduce for non-dependent functions

end FunLikeStuff

section OrderStuff

class Preorder (α : Type u) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

end OrderStuff

section CategoryStuff

class Quiver (V : Type u) where
  /-- The type of edges/arrows/morphisms between a given source and target. -/
  Hom : V → V → Sort v

infixr:10 " ⟶ " => Quiver.Hom

namespace CategoryTheory

class CategoryStruct (obj : Type u) extends Quiver.{v + 1} obj : Type max u (v + 1) where
  /-- The identity morphism on an object. -/
  id : ∀ X : obj, Hom X X
  /-- Composition of morphisms in a category, written `f ≫ g`. -/
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

-- macro (name := aesop_cat) "aesop_cat" c:Aesop.tactic_clause* : tactic =>
-- `(tactic|
--   aesop $c* (config := { introsTransparency? := some .default, terminal := true })
--             (simp_config := { decide := true, zetaDelta := true })
--             (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident]))

/-- Notation for the identity morphism in a category. -/
scoped notation "𝟙" => CategoryStruct.id  -- type as \b1

/-- Notation for composition of morphisms in a category. -/
scoped infixr:80 " ≫ " => CategoryStruct.comp -- type as \gg

class Category (obj : Type u) extends CategoryStruct.{v} obj : Type max u (v + 1) where
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f -- := by aesop_cat
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f -- := by aesop_cat
  /-- Composition in a category is associative. -/
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h -- := by aesop_cat

end CategoryTheory

end CategoryStuff

section OppositeStuff

structure Opposite (α : Sort u) :=
  op ::
  /-- The canonical map `αᵒᵖ → α`. -/
  unop : α

notation:max -- Use a high right binding power (like that of postfix ⁻¹) so that, for example,
-- `Presheaf Cᵒᵖ` parses as `Presheaf (Cᵒᵖ)` and not `(Presheaf C)ᵒᵖ`.
α "ᵒᵖ" => Opposite α

open Opposite

section Quiver

variable {C : Type u₁}

variable [Quiver.{v₁} C]

/-- `Vᵒᵖ` reverses the direction of all arrows of `V`. -/
instance Quiver.opposite {V} [Quiver V] : Quiver Vᵒᵖ :=
  ⟨fun a b => (unop b ⟶ unop a)ᵒᵖ⟩

def Quiver.Hom.op {V : Type u} [Quiver V] {X Y : V} (f : X ⟶ Y) : op Y ⟶ op X := ⟨f⟩

def Quiver.Hom.unop {V : Type u} [Quiver V] {X Y : Vᵒᵖ} (f : X ⟶ Y) : unop Y ⟶ unop X := Opposite.unop f

theorem Quiver.Hom.op_inj {X Y : C} :
    Function.Injective (Quiver.Hom.op : (X ⟶ Y) → (Opposite.op Y ⟶ Opposite.op X)) := fun _ _ H =>
  congrArg Quiver.Hom.unop H

end Quiver

namespace CategoryTheory

variable [Category.{v₁} C]

instance Category.opposite : Category.{v₁} Cᵒᵖ where
  comp f g := (g.unop ≫ f.unop).op
  id X := (𝟙 (unop X)).op
  id_comp := by sorry
  comp_id := by sorry
  assoc := by sorry

end CategoryTheory

end OppositeStuff

open CategoryTheory

section IsoStuff

variable {C : Type u} [Category.{v} C] {X Y Z : C}

/-- `IsIso` typeclass expressing that a morphism is invertible. -/
class IsIso (f : X ⟶ Y) : Prop where
  /-- The existence of an inverse morphism. -/
  out : ∃ inv : Y ⟶ X, f ≫ inv = 𝟙 X ∧ inv ≫ f = 𝟙 Y

structure Iso {C : Type u} [Category.{v} C] (X Y : C) where
  /-- The forward direction of an isomorphism. -/
  hom : X ⟶ Y
  /-- The backwards direction of an isomorphism. -/
  inv : Y ⟶ X
  /-- Composition of the two directions of an isomorphism is the identity on the source. -/
  hom_inv_id : hom ≫ inv = 𝟙 X -- := by aesop_cat
  /-- Composition of the two directions of an isomorphism in reverse order
  is the identity on the target. -/
  inv_hom_id : inv ≫ hom = 𝟙 Y -- := by aesop_cat

infixr:10 " ≅ " => Iso -- type as \cong or \iso

noncomputable def inv (f : X ⟶ Y) [I : IsIso f] : Y ⟶ X :=
  Classical.choose I.1

theorem hom_inv_id (f : X ⟶ Y) [I : IsIso f] : f ≫ inv f = 𝟙 X :=
  (Classical.choose_spec I.1).left

theorem inv_hom_id (f : X ⟶ Y) [I : IsIso f] : inv f ≫ f = 𝟙 Y :=
  (Classical.choose_spec I.1).right

open Iso in
noncomputable def asIso (f : X ⟶ Y) [IsIso f] : X ≅ Y :=
  ⟨f, inv f, hom_inv_id f, inv_hom_id f⟩

def Iso.symm (I : X ≅ Y) : Y ≅ X where
  hom := I.inv
  inv := I.hom
  hom_inv_id := I.inv_hom_id
  inv_hom_id := I.hom_inv_id

instance IsIso.of_iso (f : X ≅ Y) : IsIso f.hom := ⟨⟨f.inv, by sorry⟩⟩
-- instance IsIso.of_iso (f : X ≅ Y) : IsIso f.hom := ⟨⟨f.inv, by simp⟩⟩

instance IsIso.of_iso_inv (f : X ≅ Y) : IsIso f.inv := IsIso.of_iso f.symm

end IsoStuff

section FunctorStuff

structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  /-- The action of a (pre)functor on vertices/objects. -/
  obj : V → W
  /-- The action of a (pre)functor on edges/arrows/morphisms. -/
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)

namespace CategoryTheory

structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
    extends Prefunctor C D : Type max v₁ v₂ u₁ u₂ where
  /-- A functor preserves identity morphisms. -/
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X) -- := by aesop_cat
  /-- A functor preserves composition. -/
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g -- := by aesop_cat

infixr:26 " ⥤ " => Functor -- type as \func
-- scoped [CategoryTheory] infixr:26 " ⥤ " => Functor -- type as \func

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

protected def Functor.id : C ⥤ C where
  obj X := X
  map f := f
  map_id := by sorry
  map_comp := by sorry

/-- Notation for the identity functor on a category. -/
notation "𝟭" => Functor.id -- Type this as `\sb1`
-- scoped [CategoryTheory] notation "𝟭" => Functor.id -- Type this as `\sb1`

def comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)
  map_comp := sorry -- by intros; dsimp; rw [F.map_comp, G.map_comp]
  map_id := sorry

infixr:80 " ⋙ " => Functor.comp
-- scoped [CategoryTheory] infixr:80 " ⋙ " => Functor.comp

abbrev LargeCategory (C : Type (u + 1)) : Type (u + 1) := Category.{u} C

instance types : LargeCategory (Type u)
    where
  Hom a b := a → b
  id a := id
  comp f g := g ∘ f
  comp_id := by sorry
  id_comp := by sorry
  assoc := by sorry

abbrev SmallCategory (C : Type u) : Type (u + 1) := Category.{u} C

open Preorder in
instance (priority := 100) smallCategory (α : Type u) [Preorder α] : SmallCategory α where
  Hom U V := ULift (PLift (U ≤ V))
  id X := ⟨⟨le_refl X⟩⟩
  comp f g := ⟨⟨le_trans _ _ _ f.down.down g.down.down⟩⟩
  id_comp := by sorry
  comp_id := by sorry
  assoc := by sorry

end CategoryTheory

namespace CategoryTheory.Functor

open Opposite

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

protected def op (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ where
  obj X := op (F.obj (unop X))
  map f := (F.map f.unop).op
  map_id := by sorry
  map_comp := by sorry

protected def rightOp (F : Cᵒᵖ ⥤ D) : C ⥤ Dᵒᵖ where
  obj X := op (F.obj (op X))
  map f := (F.map f.op).op
  map_id := by sorry
  map_comp := by sorry

end CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

class CategoryTheory.Functor.Faithful (F : C ⥤ D) : Prop where
  /-- `F.map` is injective for each `X Y : C`. -/
  map_injective : ∀ {X Y : C}, Function.Injective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) -- := by aesop_cat

end FunctorStuff

section NatTransStuff

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory

structure NatTrans (F G : C ⥤ D) : Type max u₁ v₂ where
  /-- The component of a natural transformation. -/
  app : ∀ X : C, F.obj X ⟶ G.obj X
  /-- The naturality square for a given morphism. -/
  naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f -- := by aesop_cat

end CategoryTheory

namespace NatTrans

protected def id (F : C ⥤ D) : NatTrans F F where
  app X := 𝟙 (F.obj X)
  naturality := by sorry

end NatTrans

namespace CategoryTheory.Functor

variable {F G H I : C ⥤ D}

/-- `vcomp α β` is the vertical compositions of natural transformations. -/
def vcomp (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app X := α.app X ≫ β.app X
  naturality := sorry

end CategoryTheory.Functor

open NatTrans Category CategoryTheory.Functor

instance Functor.category : Category.{max u₁ v₂} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := vcomp α β
  id_comp := by sorry
  comp_id := by sorry
  assoc := by sorry

namespace NatTrans

open Opposite

variable {F G H : C ⥤ D}

protected def op (α : F ⟶ G) : G.op ⟶ F.op where
  app X := (α.app (unop X)).op
  naturality X Y f := sorry -- Quiver.Hom.unop_inj (by simp)


end NatTrans

namespace CategoryTheory.NatIso

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable {F G : C ⥤ D}

protected def op (α : F ≅ G) : G.op ≅ F.op where
  hom := NatTrans.op α.hom
  inv := NatTrans.op α.inv
  hom_inv_id := sorry -- by ext; dsimp; rw [← op_comp]; rw [α.inv_hom_id_app]; rfl
  inv_hom_id := sorry -- by ext; dsimp; rw [← op_comp]; rw [α.hom_inv_id_app]; rfl

def ofComponents (app : ∀ X : C, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y),
      F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f) : -- := by aesop_cat) :
    F ≅ G where
  hom :=
    { app := fun X => (app X).hom
      naturality := sorry}
  inv :=
    { app := fun X => (app X).inv,
      naturality := fun X Y f => by sorry }
        -- have h := congrArg (fun f => (app X).inv ≫ f ≫ (app Y).inv) (naturality f).symm
        -- simp only [Iso.inv_hom_id_assoc, Iso.hom_inv_id, assoc, comp_id, cancel_mono] at h
        -- exact h }
  hom_inv_id := sorry
  inv_hom_id := sorry

end CategoryTheory.NatIso

end NatTransStuff

section SetStuff

def Set (α : Type u) := α → Prop

def setOf {α : Type u} (p : α → Prop) : Set α := p

namespace Set

protected def Mem (a : α) (s : Set α) : Prop :=
  s a

open Lean in
syntax extBinder := binderIdent ((" : " term) <|> binderPred)?
syntax "{" extBinder " | " term "}" : term

macro_rules
  | `({ $x:ident | $p }) => `(setOf fun $x:ident ↦ $p)
  | `({ $x:ident : $t | $p }) => `(setOf fun $x:ident : $t ↦ $p)
  | `({ $x:ident $b:binderPred | $p }) =>
    `(setOf fun $x:ident ↦ satisfies_binder_pred% $x $b ∧ $p)

instance : Membership α (Set α) :=
  ⟨Set.Mem⟩

def univ : Set α := {_a | True}

protected def inter (s₁ s₂ : Set α) : Set α := {a | a ∈ s₁ ∧ a ∈ s₂}

instance : Inter (Set α) := ⟨Set.inter⟩

class SupSet (α : Type u) where
  sSup : Set α → α

instance : SupSet (Set α) :=
  ⟨fun s => { a | ∃ t ∈ s, a ∈ t }⟩

open SupSet in
def sUnion (S : Set (Set α)) : Set α :=
  sSup S

/-- Notation for `Set.sUnion`. Union of a set of sets. -/
prefix:110 "⋃₀ " => sUnion

def preimage (f : α → β) (s : Set β) : Set α := {x | f x ∈ s}

/-- `f ⁻¹' t` denotes the preimage of `t : Set β` under the function `f : α → β`. -/
infixl:80 " ⁻¹' " => preimage

end Set

section OrderStuff

class PartialOrder (α : Type u) extends Preorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

variable {α : Type u} [Preorder α]

theorem le_refl : ∀ a : α, a ≤ a :=
  Preorder.le_refl

theorem le_rfl {a : α} : a ≤ a :=
  le_refl a

theorem le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c :=
  Preorder.le_trans _ _ _

theorem lt_iff_le_not_le : ∀ {a b : α}, a < b ↔ a ≤ b ∧ ¬b ≤ a :=
  Preorder.lt_iff_le_not_le _ _

variable {α : Type u} [PartialOrder α] in
theorem le_antisymm : ∀ {a b : α}, a ≤ b → b ≤ a → a = b :=
  PartialOrder.le_antisymm _ _

abbrev Preorder.lift {α β} [Preorder β] (f : α → β) : Preorder α where
  le x y := f x ≤ f y
  le_refl _ := le_rfl
  le_trans _ _ _ := _root_.le_trans
  lt x y := f x < f y
  lt_iff_le_not_le _ _ := _root_.lt_iff_le_not_le

abbrev PartialOrder.lift {α β} [PartialOrder β] (f : α → β) (inj : Function.Injective f) : PartialOrder α :=
  { Preorder.lift f with le_antisymm := fun _ _ h₁ h₂ ↦ inj sorry }
  -- { Preorder.lift f with le_antisymm := fun _ _ h₁ h₂ ↦ inj (le_antisymm h₁ h₂) }

end OrderStuff

end SetStuff

section SetLikeStuff

class SetLike (A : Type*) (B : outParam <| Type*) where
  /-- The coercion from a term of a `SetLike` to its corresponding `Set`. -/
  protected coe : A → Set B
  /-- The coercion from a term of a `SetLike` to its corresponding `Set` is injective. -/
  protected coe_injective' : Function.Injective coe

attribute [coe] SetLike.coe

namespace SetLike

variable {A : Type*} {B : Type*} [i : SetLike A B]

instance : CoeTC A (Set B) where coe := SetLike.coe

instance (priority := 100) instMembership : Membership B A :=
  ⟨fun x p => x ∈ (p : Set B)⟩

instance (priority := 100) : CoeSort A (Type _) :=
  ⟨fun p => { x : B // x ∈ p }⟩

theorem coe_injective : Function.Injective (SetLike.coe : A → Set B) := fun _ _ h =>
  SetLike.coe_injective' h

instance (priority := 100) instPartialOrder : PartialOrder A :=
  { PartialOrder.lift (SetLike.coe : A → Set B) coe_injective with
    le := fun H K => ∀ ⦃x⦄, x ∈ H → x ∈ K }

end SetLike

end SetLikeStuff

section ConcreteCategoryStuff

class ConcreteCategory (C : Type u) [Category.{v} C] where
  /-- We have a functor to Type -/
  protected forget : C ⥤ Type w
  /-- That functor is faithful -/
  [forget_faithful : forget.Faithful]

attribute [reducible] ConcreteCategory.forget
attribute [instance] ConcreteCategory.forget_faithful

/-- The forgetful functor from a concrete category to `Type u`. -/
abbrev forget (C : Type u) [Category.{v} C] [ConcreteCategory.{w} C] : C ⥤ Type w :=
  ConcreteCategory.forget

-- this is reducible because we want `forget (Type u)` to unfold to `𝟭 _`
@[instance] abbrev ConcreteCategory.types : ConcreteCategory.{u, u, u+1} (Type u) where
  forget := 𝟭 _

def ConcreteCategory.hasCoeToSort (C : Type u) [Category.{v} C] [ConcreteCategory.{w} C] :
    CoeSort C (Type w) where
  coe := fun X => (forget C).obj X

attribute [local instance] ConcreteCategory.hasCoeToSort

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{w} C]

abbrev ConcreteCategory.instFunLike {X Y : C} : FunLike (X ⟶ Y) X Y where
  coe f := (forget C).map f
  coe_injective' _ _ h := (forget C).map_injective h

attribute [local instance] ConcreteCategory.instFunLike

end ConcreteCategoryStuff

section TopologicalSpaceStuff

open Set

/-- A topology on `X`. -/
class TopologicalSpace (X : Type u) where
  /-- A predicate saying that a set is an open set. Use `IsOpen` in the root namespace instead. -/
  protected IsOpen : Set X → Prop
  /-- The set representing the whole space is an open set.
  Use `isOpen_univ` in the root namespace instead. -/
  protected isOpen_univ : IsOpen univ
  /-- The intersection of two open sets is an open set. Use `IsOpen.inter` instead. -/
  protected isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  /-- The union of a family of open sets is an open set.
  Use `isOpen_sUnion` in the root namespace instead. -/
  protected isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)

variable [TopologicalSpace X]

def IsOpen : Set X → Prop := TopologicalSpace.IsOpen

variable (α : Type u) [TopologicalSpace α]

structure Opens where
  /-- The underlying set of a bundled `TopologicalSpace.Opens` object. -/
  carrier : Set α
  /-- The `TopologicalSpace.Opens.carrier _` is an open set. -/
  is_open' : IsOpen carrier

variable {X : Type u} {Y : Type v}

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

instance : SetLike (Opens X) X where
  coe := Opens.carrier
  coe_injective' := fun ⟨_, _⟩ ⟨_, _⟩ _ => by congr

structure Continuous (f : X → Y) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)

structure ContinuousMap (α : Type u₁) (β : Type u₂) [TopologicalSpace α] [TopologicalSpace β] where
  /-- The function `α → β` -/
  protected toFun : α → β
  /-- Proposition that `toFun` is continuous -/
  protected continuous_toFun : Continuous toFun -- := by continuity

notation "C(" α ", " β ")" => ContinuousMap α β

variable {α β γ : Type u} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

instance funLike : FunLike C(α, β) α β where
  coe := ContinuousMap.toFun
  coe_injective' f g h := by cases f; cases g; congr

namespace ContinuousMap

protected def id : C(α, α) where
  toFun := id
  continuous_toFun := sorry

def comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) where
  toFun := f ∘ g
  continuous_toFun := sorry

theorem coe_injective : @Function.Injective C(α, β) (α → β) DFunLike.coe := fun f g h => by
  cases f; cases g; congr

end ContinuousMap

end TopologicalSpaceStuff

section BundledStuff

structure Bundled (c : Type u → Type v) : Type max (u + 1) v where
  /-- The underlying type of the bundled type -/
  α : Type u
  /-- The corresponding instance of the bundled type class -/
  str : c α := by infer_instance

variable {c : Type u → Type u} (hom : ∀ ⦃α β : Type u⦄ (_ : c α) (_ : c β), Type u)

instance Bundled.coeSort : CoeSort (Bundled c) (Type u) :=
  ⟨Bundled.α⟩

structure BundledHom where
  /-- the underlying map of a bundled morphism -/
  toFun : ∀ {α β : Type u} (Iα : c α) (Iβ : c β), hom Iα Iβ → α → β
  /-- the identity as a bundled morphism -/
  id : ∀ {α : Type u} (I : c α), hom I I
  /-- composition of bundled morphisms -/
  comp : ∀ {α β γ : Type u} (Iα : c α) (Iβ : c β) (Iγ : c γ), hom Iβ Iγ → hom Iα Iβ → hom Iα Iγ
  /-- a bundled morphism is determined by the underlying map -/
  hom_ext : ∀ {α β : Type u} (Iα : c α) (Iβ : c β), Function.Injective (toFun Iα Iβ) -- := by aesop_cat
  /-- compatibility with identities -/
  id_toFun : ∀ {α : Type u} (I : c α), toFun I I (id I) = _root_.id -- := by aesop_cat
  /-- compatibility with the composition -/
  comp_toFun :
    ∀ {α β γ : Type u} (Iα : c α) (Iβ : c β) (Iγ : c γ) (f : hom Iα Iβ) (g : hom Iβ Iγ),
      toFun Iα Iγ (comp Iα Iβ Iγ g f) = toFun Iβ Iγ g ∘ toFun Iα Iβ f -- := by aesop_cat

attribute [class] BundledHom

variable [𝒞 : BundledHom hom]

set_option synthInstance.checkSynthOrder false in
instance CategoryTheory.BundledHom.category : Category (Bundled c) where
  Hom := fun X Y => hom X.str Y.str
  id := fun X => BundledHom.id 𝒞 (α := X) X.str
  comp := fun {X Y Z} f g => BundledHom.comp 𝒞 (α := X) (β := Y) (γ := Z) X.str Y.str Z.str g f
  comp_id _ := sorry --by apply 𝒞.hom_ext; simp
  assoc _ _ _ := sorry -- by apply 𝒞.hom_ext; aesop_cat
  id_comp _ := sorry -- by apply 𝒞.hom_ext; simp

instance CategoryTheory.BundledHom.concreteCategory : ConcreteCategory.{u} (Bundled c) where
  forget :=
    { obj := fun X => X
      map := @fun X Y f => 𝒞.toFun X.str Y.str f
      map_id := fun X => 𝒞.id_toFun X.str
      map_comp := fun f g => by dsimp; erw [𝒞.comp_toFun];rfl }
  forget_faithful := { map_injective := by (intros; apply 𝒞.hom_ext) }

def TopCat : Type (u + 1) :=
  Bundled TopologicalSpace

instance bundledHom : BundledHom @ContinuousMap :=
  ⟨@ContinuousMap.toFun, @ContinuousMap.id, @ContinuousMap.comp, @ContinuousMap.coe_injective,
    fun _ => rfl, fun _ _ _ _ _ => rfl⟩

deriving instance LargeCategory for TopCat

instance concreteCategory : ConcreteCategory TopCat := by
  dsimp [TopCat]
  infer_instance

instance instCoeSortTopCatType : CoeSort TopCat (Type*) :=
  Bundled.coeSort

instance topologicalSpaceUnbundled (x : TopCat) : TopologicalSpace x :=
  x.str

end BundledStuff

section LocallyRingedSpaceStuff

variable (C : Type u) [Category.{v} C]

def TopCat.Presheaf (X : TopCat.{w}) : Type max u v w :=
  (Opens X)ᵒᵖ ⥤ C

structure PresheafedSpace where
  carrier : TopCat
  protected presheaf : carrier.Presheaf C

structure SheafedSpace extends PresheafedSpace C where
  /-- A sheafed space is presheafed space which happens to be sheaf. -/
  IsSheaf : presheaf.IsSheaf

structure LocallyRingedSpace extends SheafedSpace CommRingCat.{u} where
  /-- Stalks of a locally ringed space are local rings. -/
  localRing : ∀ x, LocalRing (presheaf.stalk x)

def Γ : LocallyRingedSpace.{u}ᵒᵖ ⥤ CommRingCat.{u} :=
  forgetToSheafedSpace.op ⋙ SheafedSpace.Γ

def SpecΓIdentity : Spec.toLocallyRingedSpace.rightOp ⋙ Γ ≅ 𝟭 _ :=
  Iso.symm <| NatIso.ofComponents.{u,u,u+1,u+1} (fun R =>
    -- Porting note: In Lean3, this `IsIso` is synthesized automatically
    letI : IsIso (toSpecΓ R) := sorry -- StructureSheaf.isIso_to_global _
    asIso (toSpecΓ R)) fun {X Y} f => sorry -- by convert Spec_Γ_naturality (R := X) (S := Y) f

def locallyRingedSpaceAdjunction : Γ.rightOp ⊣ Spec.toLocallyRingedSpace.{u} :=
  Adjunction.mkOfUnitCounit
    { unit := identityToΓSpec
      counit := (NatIso.op SpecΓIdentity).inv
      left_triangle := by
        ext X; erw [Category.id_comp]
        exact congr_arg Quiver.Hom.op (left_triangle X)
      right_triangle := by
        ext R : 2
        -- Porting note: a little bit hand holding
        change identityToΓSpec.app _ ≫ 𝟙 _ ≫ Spec.toLocallyRingedSpace.map _ =
          𝟙 _
        simp_rw [Category.id_comp, show (NatIso.op SpecΓIdentity).inv.app R =
          (SpecΓIdentity.inv.app R.unop).op from rfl]
        exact right_triangle R.unop
        }


end LocallyRingedSpaceStuff

section BadStuff

instance isIso_locallyRingedSpaceAdjunction_counit :
      IsIso locallyRingedSpaceAdjunction.counit :=
  IsIso.of_iso_inv (NatIso.op SpecΓIdentity)

end BadStuff

