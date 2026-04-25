/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Order.Disjoint
public import Mathlib.Order.RelIso.Basic
public import Mathlib.Tactic.Monotonicity.Attr
public import Mathlib.Tactic.PPWithUniv

/-!
# Order homomorphisms

This file defines order homomorphisms, which are bundled monotone functions. A preorder
homomorphism `f : α →o β` is a function `α → β` along with a proof that `∀ x y, x ≤ y → f x ≤ f y`.

## Main definitions

In this file we define the following bundled monotone maps:
* `OrderHom α β` a.k.a. `α →o β`: Preorder homomorphism.
  An `OrderHom α β` is a function `f : α → β` such that `a₁ ≤ a₂ → f a₁ ≤ f a₂`
* `OrderEmbedding α β` a.k.a. `α ↪o β`: Relation embedding.
  An `OrderEmbedding α β` is an embedding `f : α ↪ β` such that `a ≤ b ↔ f a ≤ f b`.
  Defined as an abbreviation of `@RelEmbedding α β (≤) (≤)`.
* `OrderIso`: Relation isomorphism.
  An `OrderIso α β` is an equivalence `f : α ≃ β` such that `a ≤ b ↔ f a ≤ f b`.
  Defined as an abbreviation of `@RelIso α β (≤) (≤)`.

We also define many `OrderHom`s. In some cases we define two versions, one with `ₘ` suffix and
one without it (e.g., `OrderHom.compₘ` and `OrderHom.comp`). This means that the former
function is a "more bundled" version of the latter. We can't just drop the "less bundled" version
because the more bundled version usually does not work with dot notation.

* `OrderHom.id`: identity map as `α →o α`;
* `OrderHom.curry`: an order isomorphism between `α × β →o γ` and `α →o β →o γ`;
* `OrderHom.comp`: composition of two bundled monotone maps;
* `OrderHom.compₘ`: composition of bundled monotone maps as a bundled monotone map;
* `OrderHom.const`: constant function as a bundled monotone map;
* `OrderHom.prod`: combine `α →o β` and `α →o γ` into `α →o β × γ`;
* `OrderHom.prodₘ`: a more bundled version of `OrderHom.prod`;
* `OrderHom.prodIso`: order isomorphism between `α →o β × γ` and `(α →o β) × (α →o γ)`;
* `OrderHom.diag`: diagonal embedding of `α` into `α × α` as a bundled monotone map;
* `OrderHom.onDiag`: restrict a monotone map `α →o α →o β` to the diagonal;
* `OrderHom.fst`: projection `Prod.fst : α × β → α` as a bundled monotone map;
* `OrderHom.snd`: projection `Prod.snd : α × β → β` as a bundled monotone map;
* `OrderHom.prodMap`: `Prod.map f g` as a bundled monotone map;
* `Pi.evalOrderHom`: evaluation of a function at a point `Function.eval i` as a bundled
  monotone map;
* `OrderHom.coeFnHom`: coercion to function as a bundled monotone map;
* `OrderHom.apply`: application of an `OrderHom` at a point as a bundled monotone map;
* `OrderHom.pi`: combine a family of monotone maps `f i : α →o π i` into a monotone map
  `α →o Π i, π i`;
* `OrderHom.piIso`: order isomorphism between `α →o Π i, π i` and `Π i, α →o π i`;
* `OrderHom.subtype.val`: embedding `Subtype.val : Subtype p → α` as a bundled monotone map;
* `OrderHom.dual`: reinterpret a monotone map `α →o β` as a monotone map `αᵒᵈ →o βᵒᵈ`;
* `OrderHom.dualIso`: order isomorphism between `α →o β` and `(αᵒᵈ →o βᵒᵈ)ᵒᵈ`;
* `OrderHom.compl`: order isomorphism `α ≃o αᵒᵈ` given by taking complements in a
  Boolean algebra;

We also define two functions to convert other bundled maps to `α →o β`:

* `OrderEmbedding.toOrderHom`: convert `α ↪o β` to `α →o β`;
* `RelHom.toOrderHom`: convert a `RelHom` between strict orders to an `OrderHom`.

## Tags

monotone map, bundled morphism
-/

@[expose] public section

-- Developments relating order homs and sets belong in `Order.Hom.Set` or later.
assert_not_imported Mathlib.Data.Set.Basic

open OrderDual

variable {F α β γ δ : Type*}

/-- Bundled monotone (aka, increasing) function -/
structure OrderHom (α β : Type*) [Preorder α] [Preorder β] where
  /-- The underlying function of an `OrderHom`. -/
  toFun : α → β
  /-- The underlying function of an `OrderHom` is monotone. -/
  monotone' : Monotone toFun

/-- Notation for an `OrderHom`. -/
infixr:25 " →o " => OrderHom

/-- An order embedding is an embedding `f : α ↪ β` such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `RelEmbedding (≤) (≤)`. -/
abbrev OrderEmbedding (α β : Type*) [LE α] [LE β] :=
  @RelEmbedding α β (· ≤ ·) (· ≤ ·)

to_dual_insert_cast_fun OrderEmbedding :=
  fun ⟨iso, h⟩ ↦ ⟨iso, by rwa [forall_comm]⟩,
  fun ⟨iso, h⟩ ↦ ⟨iso, by rwa [forall_comm]⟩

/-- Notation for an `OrderEmbedding`. -/
infixl:25 " ↪o " => OrderEmbedding

/-- An order isomorphism is an equivalence such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `RelIso (≤) (≤)`. -/
abbrev OrderIso (α β : Type*) [LE α] [LE β] :=
  @RelIso α β (· ≤ ·) (· ≤ ·)

to_dual_insert_cast_fun OrderIso :=
  fun ⟨iso, h⟩ ↦ ⟨iso, by rwa [forall_comm]⟩,
  fun ⟨iso, h⟩ ↦ ⟨iso, by rwa [forall_comm]⟩

/-- Notation for an `OrderIso`. -/
infixl:25 " ≃o " => OrderIso

-- These instances are here just to make `to_dual` work correctly
instance (α β : Type*) [LE α] [LE β] : FunLike (α ↪o β) α β := RelEmbedding.instFunLike
instance (α β : Type*) [LE α] [LE β] : FunLike (α ≃o β) α β := RelIso.instFunLike

section

/-- `OrderHomClass F α b` asserts that `F` is a type of `≤`-preserving morphisms. -/
abbrev OrderHomClass (F : Type*) (α β : outParam Type*) [LE α] [LE β] [FunLike F α β] :=
  RelHomClass F ((· ≤ ·) : α → α → Prop) ((· ≤ ·) : β → β → Prop)

to_dual_insert_cast OrderHomClass := by grind only [RelHomClass]

/-- `OrderIsoClass F α β` states that `F` is a type of order isomorphisms.

You should extend this class when you extend `OrderIso`. -/
class OrderIsoClass (F : Type*) (α β : outParam Type*) [LE α] [LE β] [EquivLike F α β] :
    Prop where
  /-- An order isomorphism respects `≤`. -/
  map_le_map_iff (f : F) {a b : α} : f a ≤ f b ↔ a ≤ b

attribute [to_dual self] OrderIsoClass.map_le_map_iff

end

export OrderIsoClass (map_le_map_iff)

attribute [simp] map_le_map_iff

/-- Turn an element of a type `F` satisfying `OrderIsoClass F α β` into an actual
`OrderIso`. This is declared as the default coercion from `F` to `α ≃o β`. -/
@[coe]
def OrderIsoClass.toOrderIso [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F α β] (f : F) :
    α ≃o β :=
  { EquivLike.toEquiv f with map_rel_iff' := map_le_map_iff f }

/-- Any type satisfying `OrderIsoClass` can be cast into `OrderIso` via
`OrderIsoClass.toOrderIso`. -/
instance [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F α β] : CoeTC F (α ≃o β) :=
  ⟨OrderIsoClass.toOrderIso⟩

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toOrderHomClass [LE α] [LE β]
    [EquivLike F α β] [OrderIsoClass F α β] : OrderHomClass F α β :=
  { EquivLike.toEmbeddingLike (E := F) with
    map_rel := fun f _ _ => (map_le_map_iff f).2 }

namespace OrderHomClass

variable [Preorder α] [Preorder β] [FunLike F α β] [OrderHomClass F α β]

protected theorem monotone (f : F) : Monotone f := fun _ _ => map_rel f

@[gcongr]
protected theorem mono (f : F) : Monotone f := fun _ _ => map_rel f

/-- Turn an element of a type `F` satisfying `OrderHomClass F α β` into an actual
`OrderHom`. This is declared as the default coercion from `F` to `α →o β`. -/
@[coe]
def toOrderHom (f : F) : α →o β where
  toFun := f
  monotone' := OrderHomClass.monotone f

/-- Any type satisfying `OrderHomClass` can be cast into `OrderHom` via
`OrderHomClass.toOrderHom`. -/
instance : CoeTC F (α →o β) :=
  ⟨toOrderHom⟩

end OrderHomClass

section OrderIsoClass

section LE

variable [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F α β]

@[to_dual (attr := simp) le_map_inv_iff]
theorem map_inv_le_iff (f : F) {a : α} {b : β} : EquivLike.inv f b ≤ a ↔ b ≤ f a := by
  convert (map_le_map_iff f).symm
  exact (EquivLike.right_inv f _).symm

@[to_dual self]
theorem map_inv_le_map_inv_iff (f : F) {a b : β} :
    EquivLike.inv f b ≤ EquivLike.inv f a ↔ b ≤ a := by
  simp

end LE

variable [Preorder α] [Preorder β] [EquivLike F α β] [OrderIsoClass F α β]

@[to_dual self]
theorem map_lt_map_iff (f : F) {a b : α} : f a < f b ↔ a < b :=
  lt_iff_lt_of_le_iff_le' (map_le_map_iff f) (map_le_map_iff f)

@[to_dual (attr := simp) lt_map_inv_iff]
theorem map_inv_lt_iff (f : F) {a : α} {b : β} : EquivLike.inv f b < a ↔ b < f a := by
  rw [← map_lt_map_iff f]
  simp only [EquivLike.apply_inv_apply]

@[to_dual self]
theorem map_inv_lt_map_inv_iff (f : F) {a b : β} :
    EquivLike.inv f b < EquivLike.inv f a ↔ b < a := by
  simp

end OrderIsoClass

namespace OrderHom

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]

instance : FunLike (α →o β) α β where
  coe := toFun
  coe_injective' f g h := by cases f; cases g; congr

instance : OrderHomClass (α →o β) α β where
  map_rel f _ _ h := f.monotone' h

@[simp] theorem coe_mk (f : α → β) (hf : Monotone f) : ⇑(mk f hf) = f := rfl

protected theorem monotone (f : α →o β) : Monotone f :=
  f.monotone'

protected theorem mono (f : α →o β) : Monotone f :=
  f.monotone

/-- See Note [custom simps projection]. We give this manually so that we use `toFun` as the
projection directly instead. -/
def Simps.coe (f : α →o β) : α → β := f

/- TODO: all other DFunLike classes use `apply` instead of `coe`
for the projection names. Maybe we should change this. -/
initialize_simps_projections OrderHom (toFun → coe)

@[simp] theorem toFun_eq_coe (f : α →o β) : f.toFun = f := rfl

-- See library note [partially-applied ext lemmas]
@[ext]
theorem ext (f g : α →o β) (h : (f : α → β) = g) : f = g :=
  DFunLike.coe_injective h

@[simp] theorem coe_eq (f : α →o β) : OrderHomClass.toOrderHom f = f := rfl

@[simp] theorem _root_.OrderHomClass.coe_coe {F} [FunLike F α β] [OrderHomClass F α β] (f : F) :
    ⇑(f : α →o β) = f :=
  rfl

/-- One can lift an unbundled monotone function to a bundled one. -/
protected instance canLift : CanLift (α → β) (α →o β) (↑) Monotone where
  prf f h := ⟨⟨f, h⟩, rfl⟩

/-- Copy of an `OrderHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : α →o β) (f' : α → β) (h : f' = f) : α →o β :=
  ⟨f', h.symm.subst f.monotone'⟩

@[simp]
theorem coe_copy (f : α →o β) (f' : α → β) (h : f' = f) : (f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : α →o β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

instance {α : Type*} (β : Type*) [PartialOrder α] [PartialOrder β] [DecidableEq (α → β)] :
    DecidableEq (α →o β) := fun a b =>
  decidable_of_iff (a.toFun = b.toFun) OrderHom.ext_iff.symm

/-- The identity function as bundled monotone function. -/
@[simps -fullyApplied]
def id : α →o α :=
  ⟨_root_.id, monotone_id⟩

instance : Inhabited (α →o α) :=
  ⟨id⟩

/-- The preorder structure of `α →o β` is pointwise inequality: `f ≤ g ↔ ∀ a, f a ≤ g a`. -/
instance : Preorder (α →o β) :=
  @Preorder.lift (α →o β) (α → β) _ DFunLike.coe

instance {β : Type*} [PartialOrder β] : PartialOrder (α →o β) :=
  @PartialOrder.lift (α →o β) (α → β) _ toFun ext

@[to_dual self]
theorem le_def {f g : α →o β} : f ≤ g ↔ ∀ x, f x ≤ g x :=
  Iff.rfl

@[simp, norm_cast, to_dual self]
theorem coe_le_coe {f g : α →o β} : (f : α → β) ≤ g ↔ f ≤ g :=
  Iff.rfl

@[simp, to_dual self]
theorem mk_le_mk {f g : α → β} {hf hg} : mk f hf ≤ mk g hg ↔ f ≤ g :=
  Iff.rfl

@[mono, to_dual self]
theorem apply_mono {f g : α →o β} {x y : α} (h₁ : f ≤ g) (h₂ : x ≤ y) : f x ≤ g y :=
  (h₁ x).trans <| g.mono h₂

/-- Curry/uncurry as an order isomorphism between `α × β →o γ` and `α →o β →o γ`. -/
def curry : (α × β →o γ) ≃o (α →o β →o γ) where
  toFun f := ⟨fun x ↦ ⟨Function.curry f x, fun _ _ h ↦ f.mono ⟨le_rfl, h⟩⟩, fun _ _ h _ =>
    f.mono ⟨h, le_rfl⟩⟩
  invFun f := ⟨Function.uncurry fun x ↦ f x, fun x y h ↦ (f.mono h.1 x.2).trans ((f y.1).mono h.2)⟩
  map_rel_iff' := by simp [le_def]

@[simp]
theorem curry_apply (f : α × β →o γ) (x : α) (y : β) : curry f x y = f (x, y) :=
  rfl

@[simp]
theorem curry_symm_apply (f : α →o β →o γ) (x : α × β) : curry.symm f x = f x.1 x.2 :=
  rfl

/-- The composition of two bundled monotone functions. -/
@[simps -fullyApplied]
def comp (g : β →o γ) (f : α →o β) : α →o γ :=
  ⟨g ∘ f, g.mono.comp f.mono⟩

@[mono, to_dual self]
theorem comp_mono ⦃g₁ g₂ : β →o γ⦄ (hg : g₁ ≤ g₂) ⦃f₁ f₂ : α →o β⦄ (hf : f₁ ≤ f₂) :
    g₁.comp f₁ ≤ g₂.comp f₂ := fun _ => (hg _).trans (g₂.mono <| hf _)

@[simp] lemma mk_comp_mk (g : β → γ) (f : α → β) (hg hf) :
    comp ⟨g, hg⟩ ⟨f, hf⟩ = ⟨g ∘ f, hg.comp hf⟩ := rfl

/-- The composition of two bundled monotone functions, a fully bundled version. -/
@[simps! -fullyApplied]
def compₘ : (β →o γ) →o (α →o β) →o α →o γ :=
  curry ⟨fun f : (β →o γ) × (α →o β) => f.1.comp f.2, fun _ _ h => comp_mono h.1 h.2⟩

@[simp]
theorem comp_id (f : α →o β) : comp f id = f := by
  ext
  rfl

@[simp]
theorem id_comp (f : α →o β) : comp id f = f := by
  ext
  rfl

/-- Constant function bundled as an `OrderHom`. -/
@[simps -fullyApplied]
def const (α : Type*) [Preorder α] {β : Type*} [Preorder β] : β →o α →o β where
  toFun b := ⟨Function.const α b, fun _ _ _ => le_rfl⟩
  monotone' _ _ h _ := h

@[simp]
theorem const_comp (f : α →o β) (c : γ) : (const β c).comp f = const α c :=
  rfl

@[simp]
theorem comp_const (γ : Type*) [Preorder γ] (f : α →o β) (c : α) :
    f.comp (const γ c) = const γ (f c) :=
  rfl

/-- Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)` bundled as a
`OrderHom`. -/
@[simps]
protected def prod (f : α →o β) (g : α →o γ) : α →o β × γ :=
  ⟨fun x => (f x, g x), fun _ _ h => ⟨f.mono h, g.mono h⟩⟩

@[mono, to_dual self]
theorem prod_mono {f₁ f₂ : α →o β} (hf : f₁ ≤ f₂) {g₁ g₂ : α →o γ} (hg : g₁ ≤ g₂) :
    f₁.prod g₁ ≤ f₂.prod g₂ := fun _ => Prod.le_def.2 ⟨hf _, hg _⟩

theorem comp_prod_comp_same (f₁ f₂ : β →o γ) (g : α →o β) :
    (f₁.comp g).prod (f₂.comp g) = (f₁.prod f₂).comp g :=
  rfl

/-- Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)` bundled as a
`OrderHom`. This is a fully bundled version. -/
@[simps!]
def prodₘ : (α →o β) →o (α →o γ) →o α →o β × γ :=
  curry ⟨fun f : (α →o β) × (α →o γ) => f.1.prod f.2, fun _ _ h => prod_mono h.1 h.2⟩

/-- Diagonal embedding of `α` into `α × α` as an `OrderHom`. -/
@[simps!]
def diag : α →o α × α :=
  id.prod id

/-- Restriction of `f : α →o α →o β` to the diagonal. -/
@[simps! +simpRhs]
def onDiag (f : α →o α →o β) : α →o β :=
  (curry.symm f).comp diag

/-- `Prod.fst` as an `OrderHom`. -/
@[simps]
def fst : α × β →o α :=
  ⟨Prod.fst, fun _ _ h => h.1⟩

/-- `Prod.snd` as an `OrderHom`. -/
@[simps]
def snd : α × β →o β :=
  ⟨Prod.snd, fun _ _ h => h.2⟩

@[simp]
theorem fst_prod_snd : (fst : α × β →o α).prod snd = id := by
  ext ⟨x, y⟩ : 2
  rfl

@[simp]
theorem fst_comp_prod (f : α →o β) (g : α →o γ) : fst.comp (f.prod g) = f :=
  ext _ _ rfl

@[simp]
theorem snd_comp_prod (f : α →o β) (g : α →o γ) : snd.comp (f.prod g) = g :=
  ext _ _ rfl

/-- Order isomorphism between the space of monotone maps to `β × γ` and the product of the spaces
of monotone maps to `β` and `γ`. -/
@[simps]
def prodIso : (α →o β × γ) ≃o (α →o β) × (α →o γ) where
  toFun f := (fst.comp f, snd.comp f)
  invFun f := f.1.prod f.2
  map_rel_iff' := forall_and.symm

/-- `Prod.map` of two `OrderHom`s as an `OrderHom` -/
@[simps]
def prodMap (f : α →o β) (g : γ →o δ) : α × γ →o β × δ :=
  ⟨Prod.map f g, fun _ _ h => ⟨f.mono h.1, g.mono h.2⟩⟩

variable {ι : Type*} {π : ι → Type*} [∀ i, Preorder (π i)]

/-- Evaluation of an unbundled function at a point (`Function.eval`) as an `OrderHom`. -/
@[simps -fullyApplied]
def _root_.Pi.evalOrderHom (i : ι) : (∀ j, π j) →o π i :=
  ⟨Function.eval i, Function.monotone_eval i⟩

/-- The "forgetful functor" from `α →o β` to `α → β` that takes the underlying function,
is monotone. -/
@[simps -fullyApplied]
def coeFnHom : (α →o β) →o α → β where
  toFun f := f
  monotone' _ _ h := h

/-- Function application `fun f => f a` (for fixed `a`) is a monotone function from the
monotone function space `α →o β` to `β`. See also `Pi.evalOrderHom`. -/
@[simps! -fullyApplied]
def apply (x : α) : (α →o β) →o β :=
  (Pi.evalOrderHom x).comp coeFnHom

/-- Construct a bundled monotone map `α →o Π i, π i` from a family of monotone maps
`f i : α →o π i`. -/
@[simps]
def pi (f : ∀ i, α →o π i) : α →o ∀ i, π i :=
  ⟨fun x i => f i x, fun _ _ h i => (f i).mono h⟩

/-- Order isomorphism between bundled monotone maps `α →o Π i, π i` and families of bundled monotone
maps `Π i, α →o π i`. -/
@[simps]
def piIso : (α →o ∀ i, π i) ≃o ∀ i, α →o π i where
  toFun f i := (Pi.evalOrderHom i).comp f
  invFun := pi
  map_rel_iff' := forall_comm

/-- `Subtype.val` as a bundled monotone function. -/
@[simps -fullyApplied]
def Subtype.val (p : α → Prop) : Subtype p →o α :=
  ⟨_root_.Subtype.val, fun _ _ h => h⟩

/-- `Subtype.impEmbedding` as an order embedding. -/
@[simps!]
def _root_.Subtype.orderEmbedding {p q : α → Prop} (h : ∀ a, p a → q a) :
    {x // p x} ↪o {x // q x} :=
  { Subtype.impEmbedding _ _ h with
    map_rel_iff' := by aesop }

/-- There is a unique monotone map from a subsingleton to itself. -/
instance unique [Subsingleton α] : Unique (α →o α) where
  default := OrderHom.id
  uniq _ := ext _ _ (Subsingleton.elim _ _)

theorem orderHom_eq_id [Subsingleton α] (g : α →o α) : g = OrderHom.id :=
  Subsingleton.elim _ _

/-- Reinterpret a bundled monotone function as a monotone function between dual orders. -/
@[simps]
protected def dual : (α →o β) ≃ (αᵒᵈ →o βᵒᵈ) where
  toFun f := ⟨(OrderDual.toDual : β → βᵒᵈ) ∘ (f : α → β) ∘
    (OrderDual.ofDual : αᵒᵈ → α), f.mono.dual⟩
  invFun f := ⟨OrderDual.ofDual ∘ f ∘ OrderDual.toDual, f.mono.dual⟩

@[simp]
theorem dual_id : (OrderHom.id : α →o α).dual = OrderHom.id :=
  rfl

@[simp]
theorem dual_comp (g : β →o γ) (f : α →o β) :
    (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
theorem symm_dual_id : OrderHom.dual.symm OrderHom.id = (OrderHom.id : α →o α) :=
  rfl

@[simp]
theorem symm_dual_comp (g : βᵒᵈ →o γᵒᵈ) (f : αᵒᵈ →o βᵒᵈ) :
    OrderHom.dual.symm (g.comp f) = (OrderHom.dual.symm g).comp (OrderHom.dual.symm f) :=
  rfl

/-- `OrderHom.dual` as an order isomorphism. -/
def dualIso (α β : Type*) [Preorder α] [Preorder β] : (α →o β) ≃o (αᵒᵈ →o βᵒᵈ)ᵒᵈ where
  toEquiv := OrderHom.dual.trans OrderDual.toDual
  map_rel_iff' := Iff.rfl

/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `ULift α →o ULift β` in a
higher universe. -/
@[simps!]
def uliftMap (f : α →o β) : ULift α →o ULift β :=
  ⟨fun i => ⟨f i.down⟩, fun _ _ h ↦ f.monotone h⟩

/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `α →o ULift β` in a
higher universe. -/
@[simps!]
def uliftRightMap (f : α →o β) : α →o ULift β :=
  ⟨fun i => ⟨f i⟩, fun _ _ h ↦ f.monotone h⟩

/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `ULift α →o β` in a
higher universe. -/
@[simps!]
def uliftLeftMap (f : α →o β) : ULift α →o β :=
  ⟨fun i => f i.down, fun _ _ h ↦ f.monotone h⟩

@[simp]
theorem uliftLeftMap_uliftRightMap_eq (f : α →o β) : f.uliftLeftMap.uliftRightMap = f.uliftMap :=
  rfl

@[simp]
theorem uliftRightMap_uliftLeftMap_eq (f : α →o β) : f.uliftRightMap.uliftLeftMap = f.uliftMap :=
  rfl

end OrderHom

/-- Embeddings of partial orders that preserve `<` also preserve `≤`. -/
def RelEmbedding.orderEmbeddingOfLTEmbedding [PartialOrder α] [PartialOrder β]
    (f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)) : α ↪o β :=
  { f with
    map_rel_iff' := by
      simp [le_iff_lt_or_eq, f.map_rel_iff, f.injective.eq_iff] }

@[simp]
theorem RelEmbedding.orderEmbeddingOfLTEmbedding_apply [PartialOrder α] [PartialOrder β]
    {f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)} {x : α} :
    RelEmbedding.orderEmbeddingOfLTEmbedding f x = f x :=
  rfl

namespace OrderEmbedding

variable [Preorder α] [Preorder β] (f : α ↪o β)

/-- `<` is preserved by order embeddings of preorders. -/
@[to_dual gtEmbedding /-- `>` is preserved by order embeddings of preorders. -/]
def ltEmbedding : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop) :=
  { f with map_rel_iff' := by simp [lt_iff_le_not_ge, f.map_rel_iff] }

@[to_dual (attr := simp) gtEmbedding_apply]
theorem ltEmbedding_apply (x : α) : f.ltEmbedding x = f x :=
  rfl

@[simp, to_dual self]
theorem le_iff_le {a b} : f a ≤ f b ↔ a ≤ b :=
  f.map_rel_iff

@[simp, to_dual self]
theorem lt_iff_lt {a b} : f a < f b ↔ a < b :=
  f.ltEmbedding.map_rel_iff

theorem eq_iff_eq {a b} : f a = f b ↔ a = b :=
  f.injective.eq_iff

protected theorem monotone : Monotone f :=
  OrderHomClass.monotone f

protected theorem strictMono : StrictMono f := fun _ _ => f.lt_iff_lt.2

protected theorem acc (a : α) : Acc (· < ·) (f a) → Acc (· < ·) a :=
  f.ltEmbedding.acc a

@[to_dual none]
protected theorem wellFounded (f : α ↪o β) :
    WellFounded ((· < ·) : β → β → Prop) → WellFounded ((· < ·) : α → α → Prop) :=
  f.ltEmbedding.wellFounded

protected theorem isWellOrder [IsWellOrder β (· < ·)] (f : α ↪o β) : IsWellOrder α (· < ·) :=
  f.ltEmbedding.isWellOrder

/-- An order embedding is also an order embedding between dual orders. -/
protected def dual : αᵒᵈ ↪o βᵒᵈ :=
  ⟨f.toEmbedding, f.map_rel_iff⟩

/-- A preorder which embeds into a well-founded preorder is itself well-founded. -/
@[to_dual /-- A preorder which embeds into a preorder in which `(· > ·)` is well-founded
also has `(· > ·)` well-founded. -/]
protected theorem wellFoundedLT [WellFoundedLT β] (f : α ↪o β) : WellFoundedLT α where
  wf := f.wellFounded IsWellFounded.wf

/-- To define an order embedding from a partial order to a preorder it suffices to give a function
together with a proof that it satisfies `f a ≤ f b ↔ a ≤ b`.
-/
@[to_dual self]
def ofMapLEIff {α β} [PartialOrder α] [Preorder β] (f : α → β) (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) :
    α ↪o β :=
  RelEmbedding.ofMapRelIff f hf

@[simp, to_dual self]
theorem coe_ofMapLEIff {α β} [PartialOrder α] [Preorder β] {f : α → β} (h) :
    ⇑(ofMapLEIff f h) = f :=
  rfl

/-- A strictly monotone map from a linear order is an order embedding. -/
def ofStrictMono {α β} [LinearOrder α] [Preorder β] (f : α → β) (h : StrictMono f) : α ↪o β :=
  ofMapLEIff f fun _ _ => h.le_iff_le

@[simp, grind =]
theorem coe_ofStrictMono {α β} [LinearOrder α] [Preorder β] {f : α → β} (h : StrictMono f) :
    ⇑(ofStrictMono f h) = f :=
  rfl

/-- Embedding of a subtype into the ambient type as an `OrderEmbedding`. -/
def subtype (p : α → Prop) : Subtype p ↪o α :=
  ⟨Function.Embedding.subtype p, Iff.rfl⟩

@[simp]
theorem subtype_apply {p : α → Prop} (x : Subtype p) : subtype p x = x :=
  rfl

theorem subtype_injective (p : α → Prop) : Function.Injective (subtype p) :=
  Subtype.coe_injective

@[simp]
theorem coe_subtype (p : α → Prop) : ⇑(subtype p) = Subtype.val :=
  rfl

/-- Convert an `OrderEmbedding` to an `OrderHom`. -/
@[simps -fullyApplied]
def toOrderHom {X Y : Type*} [Preorder X] [Preorder Y] (f : X ↪o Y) : X →o Y where
  toFun := f
  monotone' := f.monotone

/-- The trivial embedding from an empty preorder to another preorder -/
@[simps] def ofIsEmpty [IsEmpty α] : α ↪o β where
  toFun := isEmptyElim
  inj' := isEmptyElim
  map_rel_iff' {a} := isEmptyElim a

@[simp, norm_cast]
lemma coe_ofIsEmpty [IsEmpty α] : (ofIsEmpty : α ↪o β) = (isEmptyElim : α → β) := rfl

end OrderEmbedding

section Disjoint

variable [PartialOrder α] [PartialOrder β] (f : OrderEmbedding α β)

/-- If the images by an order embedding of two elements are disjoint,
then they are themselves disjoint. -/
lemma Disjoint.of_orderEmbedding [OrderBot α] [OrderBot β] {a₁ a₂ : α} :
    Disjoint (f a₁) (f a₂) → Disjoint a₁ a₂ := by
  intro h x h₁ h₂
  rw [← f.le_iff_le] at h₁ h₂ ⊢
  calc
    f x ≤ ⊥ := h h₁ h₂
    _ ≤ f ⊥ := bot_le

/-- If the images by an order embedding of two elements are codisjoint,
then they are themselves codisjoint. -/
lemma Codisjoint.of_orderEmbedding [OrderTop α] [OrderTop β] {a₁ a₂ : α} :
    Codisjoint (f a₁) (f a₂) → Codisjoint a₁ a₂ :=
  Disjoint.of_orderEmbedding (α := αᵒᵈ) (β := βᵒᵈ) f.dual

/-- If the images by an order embedding of two elements are complements,
then they are themselves complements. -/
lemma IsCompl.of_orderEmbedding [BoundedOrder α] [BoundedOrder β] {a₁ a₂ : α} :
    IsCompl (f a₁) (f a₂) → IsCompl a₁ a₂ := fun ⟨hd, hcd⟩ ↦
  ⟨Disjoint.of_orderEmbedding f hd, Codisjoint.of_orderEmbedding f hcd⟩

end Disjoint

section RelHom

variable [PartialOrder α] [Preorder β]

namespace RelHom

variable (f : ((· < ·) : α → α → Prop) →r ((· < ·) : β → β → Prop))

/-- A bundled expression of the fact that a map between partial orders that is strictly monotone
is weakly monotone. -/
@[simps -fullyApplied]
def toOrderHom : α →o β where
  toFun := f
  monotone' := StrictMono.monotone fun _ _ => f.map_rel

end RelHom

theorem RelEmbedding.toOrderHom_injective
    (f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)) :
    Function.Injective (f : ((· < ·) : α → α → Prop) →r ((· < ·) : β → β → Prop)).toOrderHom :=
  fun _ _ h => f.injective h

end RelHom

namespace OrderIso

section LE

variable [LE α] [LE β] [LE γ]

instance : EquivLike (α ≃o β) α β where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

instance : OrderIsoClass (α ≃o β) α β where
  map_le_map_iff f _ _ := f.map_rel_iff'

@[simp]
theorem toFun_eq_coe {f : α ≃o β} : f.toFun = f :=
  rfl

-- See note [partially-applied ext lemmas]
@[ext]
theorem ext {f g : α ≃o β} (h : (f : α → β) = g) : f = g :=
  DFunLike.coe_injective h

/-- Reinterpret an order isomorphism as an order embedding. -/
def toOrderEmbedding (e : α ≃o β) : α ↪o β :=
  e.toRelEmbedding

@[simp]
theorem coe_toOrderEmbedding (e : α ≃o β) : ⇑e.toOrderEmbedding = e :=
  rfl

protected theorem bijective (e : α ≃o β) : Function.Bijective e :=
  e.toEquiv.bijective

protected theorem injective (e : α ≃o β) : Function.Injective e :=
  e.toEquiv.injective

protected theorem surjective (e : α ≃o β) : Function.Surjective e :=
  e.toEquiv.surjective

theorem apply_eq_iff_eq (e : α ≃o β) {x y : α} : e x = e y ↔ x = y :=
  e.toEquiv.apply_eq_iff_eq

/-- Identity order isomorphism. -/
def refl (α : Type*) [LE α] : α ≃o α :=
  RelIso.refl (· ≤ ·)

@[simp]
theorem coe_refl : ⇑(refl α) = id :=
  rfl

@[simp]
theorem refl_apply (x : α) : refl α x = x :=
  rfl

@[simp]
theorem refl_toEquiv : (refl α).toEquiv = Equiv.refl α :=
  rfl

/-- Inverse of an order isomorphism. -/
def symm (e : α ≃o β) : β ≃o α := RelIso.symm e

@[simp] lemma symm_mk (e : α ≃ β) (map_rel_iff') :
    symm (.mk e map_rel_iff') = .mk e.symm (by simp [← map_rel_iff']) := rfl

@[simp]
theorem apply_symm_apply (e : α ≃o β) (x : β) : e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply x

@[simp]
theorem symm_apply_apply (e : α ≃o β) (x : α) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x

@[simp]
theorem symm_refl (α : Type*) [LE α] : (refl α).symm = refl α :=
  rfl

theorem apply_eq_iff_eq_symm_apply (e : α ≃o β) (x : α) (y : β) : e x = y ↔ x = e.symm y :=
  e.toEquiv.apply_eq_iff_eq_symm_apply

theorem symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.symm y = x ↔ y = e x :=
  e.toEquiv.symm_apply_eq

@[simp]
theorem symm_symm (e : α ≃o β) : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective (OrderIso.symm : (α ≃o β) → β ≃o α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

theorem symm_injective : Function.Injective (symm : α ≃o β → β ≃o α) :=
  symm_bijective.injective

@[simp]
theorem toEquiv_symm (e : α ≃o β) : e.symm.toEquiv = e.toEquiv.symm :=
  rfl

@[simp]
theorem coe_toEquiv (e : α ≃o β) : ⇑e.toEquiv = e := rfl

@[simp]
theorem coe_symm_toEquiv (e : α ≃o β) : ⇑e.toEquiv.symm = e.symm := rfl

/-- Composition of two order isomorphisms is an order isomorphism. -/
@[trans]
def trans (e : α ≃o β) (e' : β ≃o γ) : α ≃o γ :=
  RelIso.trans e e'

@[simp]
theorem coe_trans (e : α ≃o β) (e' : β ≃o γ) : ⇑(e.trans e') = e' ∘ e :=
  rfl

@[simp]
theorem trans_apply (e : α ≃o β) (e' : β ≃o γ) (x : α) : e.trans e' x = e' (e x) :=
  rfl

@[simp]
theorem refl_trans (e : α ≃o β) : (refl α).trans e = e := by
  ext x
  rfl

@[simp]
theorem trans_refl (e : α ≃o β) : e.trans (refl β) = e := by
  ext x
  rfl

@[simp]
theorem symm_trans_apply (e₁ : α ≃o β) (e₂ : β ≃o γ) (c : γ) :
    (e₁.trans e₂).symm c = e₁.symm (e₂.symm c) :=
  rfl

theorem symm_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) : (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl

@[simp]
theorem self_trans_symm (e : α ≃o β) : e.trans e.symm = OrderIso.refl α :=
  RelIso.self_trans_symm e

@[simp]
theorem symm_trans_self (e : α ≃o β) : e.symm.trans e = OrderIso.refl β :=
  RelIso.symm_trans_self e

/-- An order isomorphism between the domains and codomains of two prosets of
order homomorphisms gives an order isomorphism between the two function prosets. -/
@[simps apply symm_apply]
def arrowCongr {α β γ δ} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]
    (f : α ≃o γ) (g : β ≃o δ) : (α →o β) ≃o (γ →o δ) where
  toFun p := .comp g <| .comp p f.symm
  invFun p := .comp g.symm <| .comp p f
  left_inv p := DFunLike.coe_injective <| by
    change (g.symm ∘ g) ∘ p ∘ (f.symm ∘ f) = p
    simp only [← OrderIso.coe_trans, Function.id_comp,
               OrderIso.self_trans_symm, OrderIso.coe_refl, Function.comp_id]
  right_inv p := DFunLike.coe_injective <| by
    change (g ∘ g.symm) ∘ p ∘ (f ∘ f.symm) = p
    simp only [← OrderIso.coe_trans, Function.id_comp,
               OrderIso.symm_trans_self, OrderIso.coe_refl, Function.comp_id]
  map_rel_iff' {p q} := by
    simp only [Equiv.coe_fn_mk, OrderHom.le_def, OrderHom.comp_coe,
               OrderHomClass.coe_coe, Function.comp_apply, map_le_map_iff]
    exact Iff.symm f.forall_congr_left

/-- If `α` and `β` are order-isomorphic then the two orders of order-homomorphisms
from `α` and `β` to themselves are order-isomorphic. -/
@[simps! apply symm_apply]
def conj {α β} [Preorder α] [Preorder β] (f : α ≃o β) : (α →o α) ≃ (β →o β) :=
  arrowCongr f f

/-- `Prod.swap` as an `OrderIso`. -/
def prodComm : α × β ≃o β × α where
  toEquiv := Equiv.prodComm α β
  map_rel_iff' := Prod.swap_le_swap

/-- `Equiv.prodAssoc` promoted to an order isomorphism. -/
@[simps! (attr := grind =)]
def prodAssoc (α β γ : Type*) [LE α] [LE β] [LE γ] :
    (α × β) × γ ≃o α × (β × γ) where
  toEquiv := .prodAssoc α β γ
  map_rel_iff' := @fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ ↦ by simp [Equiv.prodAssoc, and_assoc]

@[simp]
theorem coe_prodComm : ⇑(prodComm : α × β ≃o β × α) = Prod.swap :=
  rfl

@[simp]
theorem prodComm_symm : (prodComm : α × β ≃o β × α).symm = prodComm :=
  rfl

variable (α)

/-- The order isomorphism between a type and its double dual. -/
def dualDual : α ≃o αᵒᵈᵒᵈ :=
  refl α

@[simp]
theorem coe_dualDual : ⇑(dualDual α) = toDual ∘ toDual :=
  rfl

@[simp]
theorem coe_dualDual_symm : ⇑(dualDual α).symm = ofDual ∘ ofDual :=
  rfl

variable {α}

@[simp]
theorem dualDual_apply (a : α) : dualDual α a = toDual (toDual a) :=
  rfl

@[simp]
theorem dualDual_symm_apply (a : αᵒᵈᵒᵈ) : (dualDual α).symm a = ofDual (ofDual a) :=
  rfl

end LE

open Set

section LE

variable [LE α] [LE β]

@[gcongr, to_dual self]
theorem le_iff_le (e : α ≃o β) {x y : α} : e x ≤ e y ↔ x ≤ y :=
  e.map_rel_iff

@[to_dual symm_apply_le]
theorem le_symm_apply (e : α ≃o β) {x : α} {y : β} : x ≤ e.symm y ↔ e x ≤ y :=
  e.rel_symm_apply

end LE

variable [Preorder α] [Preorder β]

protected theorem monotone (e : α ≃o β) : Monotone e :=
  e.toOrderEmbedding.monotone

protected theorem strictMono (e : α ≃o β) : StrictMono e :=
  e.toOrderEmbedding.strictMono

@[simp, gcongr, to_dual self]
theorem lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y :=
  e.toOrderEmbedding.lt_iff_lt

@[to_dual symm_apply_lt]
theorem lt_symm_apply (e : α ≃o β) {x : α} {y : β} : x < e.symm y ↔ e x < y := by
  rw [← e.lt_iff_lt, e.apply_symm_apply]

/-- Converts an `OrderIso` into a `RelIso (<) (<)`. -/
@[to_dual /-- Converts an `OrderIso` into a `RelIso (>) (>)`. -/]
def toRelIsoLT (e : α ≃o β) : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop) :=
  ⟨e.toEquiv, lt_iff_lt e⟩

@[to_dual (attr := simp)]
theorem toRelIsoLT_apply (e : α ≃o β) (x : α) : e.toRelIsoLT x = e x :=
  rfl

@[to_dual]
theorem toRelIsoLT_symm (e : α ≃o β) : e.symm.toRelIsoLT = e.toRelIsoLT.symm :=
  rfl

@[to_dual (attr := simp)]
theorem coe_toRelIsoLT (e : α ≃o β) : ⇑e.toRelIsoLT = e := rfl

@[to_dual (attr := simp)]
theorem coe_symm_toRelIsoLT (e : α ≃o β) : ⇑e.toRelIsoLT.symm = e.symm := rfl

/-- Converts a `RelIso (<) (<)` into an `OrderIso`. -/
def ofRelIsoLT {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) : α ≃o β :=
  ⟨e.toEquiv, by simp [le_iff_eq_or_lt, e.map_rel_iff, e.injective.eq_iff]⟩

@[simp]
theorem ofRelIsoLT_apply {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) (x : α) : ofRelIsoLT e x = e x :=
  rfl

@[simp]
theorem ofRelIsoLT_symm {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) :
    (ofRelIsoLT e).symm = ofRelIsoLT e.symm :=
  rfl

@[simp]
theorem ofRelIsoLT_toRelIsoLT {α β} [PartialOrder α] [PartialOrder β] (e : α ≃o β) :
    ofRelIsoLT (toRelIsoLT e) = e := by
  ext
  simp

@[simp]
theorem toRelIsoLT_ofRelIsoLT {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) : toRelIsoLT (ofRelIsoLT e) = e := by
  ext
  simp

/-- To show that `f : α → β`, `g : β → α` make up an order isomorphism of linear orders,
it suffices to prove `cmp a (g b) = cmp (f a) b`. -/
def ofCmpEqCmp {α β} [LinearOrder α] [LinearOrder β] (f : α → β) (g : β → α)
    (h : ∀ (a : α) (b : β), cmp a (g b) = cmp (f a) b) : α ≃o β :=
  have gf : ∀ a : α, a = g (f a) := by
    intro
    rw [← cmp_eq_eq_iff, h, cmp_self_eq_eq]
  { toFun := f, invFun := g, left_inv := fun a => (gf a).symm,
    right_inv := by
      intro
      rw [← cmp_eq_eq_iff, ← h, cmp_self_eq_eq],
    map_rel_iff' := by
      intro a b
      apply le_iff_le_of_cmp_eq_cmp
      convert (h a (f b)).symm
      apply gf }

/-- To show that `f : α →o β` and `g : β →o α` make up an order isomorphism it is enough to show
that `g` is the inverse of `f`. -/
@[simps apply]
def ofHomInv (f : α →o β) (g : β →o α) (h₁ : f.comp g = .id) (h₂ : g.comp f = .id) :
    α ≃o β where
  toFun := f
  invFun := g
  left_inv := DFunLike.congr_fun h₂
  right_inv := DFunLike.congr_fun h₁
  map_rel_iff' :=
    { mp h := by simpa [h₂] using show g.comp f _ ≤ g.comp f _ from map_rel g h
      mpr h := f.monotone h }

@[simp]
theorem ofHomInv_symm_apply (f : α →o β) (g : β →o α) (h₁ : f.comp g = .id) (h₂ : g.comp f = .id)
    (a : β) : (ofHomInv f g h₁ h₂).symm a = g a := rfl

/-- Order isomorphism between `α → β` and `β`, where `α` has a unique element. -/
@[simps! toEquiv apply]
def funUnique (α β : Type*) [Unique α] [Preorder β] : (α → β) ≃o β where
  toEquiv := Equiv.funUnique α β
  map_rel_iff' := by simp [Pi.le_def, Unique.forall_iff]

@[simp]
theorem funUnique_symm_apply {α β : Type*} [Unique α] [Preorder β] :
    ((funUnique α β).symm : β → α → β) = Function.const α :=
  rfl

/-- The order isomorphism `α ≃o β` when `α` and `β` are preordered types
containing unique elements. -/
@[simps!]
noncomputable def ofUnique
    (α β : Type*) [Unique α] [Unique β] [Preorder α] [Preorder β] :
    α ≃o β where
  toEquiv := Equiv.ofUnique α β
  map_rel_iff' := by simp

/-- `Equiv.equivOfIsEmpty` promoted to an `OrderIso`. -/
def ofIsEmpty (α β : Type*) [Preorder α] [Preorder β] [IsEmpty α] [IsEmpty β] : α ≃o β :=
  ⟨Equiv.equivOfIsEmpty α β, @isEmptyElim _ _ _⟩

end OrderIso

namespace Equiv

variable [Preorder α] [Preorder β]

/-- If `e` is an equivalence with monotone forward and inverse maps, then `e` is an
order isomorphism. -/
def toOrderIso (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) : α ≃o β :=
  ⟨e, ⟨fun h => by simpa only [e.symm_apply_apply] using h₂ h, fun h => h₁ h⟩⟩

@[simp]
theorem coe_toOrderIso (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) :
    ⇑(e.toOrderIso h₁ h₂) = e :=
  rfl

@[simp]
theorem toOrderIso_toEquiv (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) :
    (e.toOrderIso h₁ h₂).toEquiv = e :=
  rfl

end Equiv

namespace StrictMono

variable [LinearOrder α] [Preorder β]
variable (f : α → β) (h_mono : StrictMono f)

/-- A strictly monotone function with a right inverse is an order isomorphism. -/
@[simps -fullyApplied]
def orderIsoOfRightInverse (g : β → α) (hg : Function.RightInverse g f) : α ≃o β :=
  { OrderEmbedding.ofStrictMono f h_mono with
    toFun := f,
    invFun := g,
    left_inv := fun _ => h_mono.injective <| hg _,
    right_inv := hg }

end StrictMono

/-- An order isomorphism is also an order isomorphism between dual orders. -/
protected def OrderIso.dual [LE α] [LE β] (f : α ≃o β) : αᵒᵈ ≃o βᵒᵈ :=
  ⟨f.toEquiv, f.le_iff_le⟩

section
variable [LE α] [LE β] (f : α ≃o β)

@[simp] lemma OrderIso.dual_apply (x) : f.dual x = .toDual (f x.ofDual) := rfl

@[simp] lemma OrderIso.dual_symm_apply (x) : f.dual.symm x = .toDual (f.symm x.ofDual) := rfl

@[simp] lemma OrderIso.symm_dual : f.symm.dual = f.dual.symm := rfl

end

section LatticeIsos

@[to_dual]
theorem OrderIso.map_bot' [LE α] [PartialOrder β] (f : α ≃o β) {x : α} {y : β} (hx : ∀ x', x ≤ x')
    (hy : ∀ y', y ≤ y') : f x = y := by
  refine le_antisymm ?_ (hy _)
  rw [← f.apply_symm_apply y, f.le_iff_le]
  apply hx

@[to_dual]
theorem OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] [OrderBot β] (f : α ≃o β) : f ⊥ = ⊥ :=
  f.map_bot' (fun _ => bot_le) fun _ => bot_le

@[to_dual le_map_sup]
theorem OrderEmbedding.map_inf_le [SemilatticeInf α] [SemilatticeInf β] (f : α ↪o β) (x y : α) :
    f (x ⊓ y) ≤ f x ⊓ f y :=
  f.monotone.map_inf_le x y

@[to_dual]
theorem OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β] (f : α ≃o β) (x y : α) :
    f (x ⊓ y) = f x ⊓ f y := by
  refine (f.toOrderEmbedding.map_inf_le x y).antisymm ?_
  apply f.symm.le_iff_le.1
  simpa using f.symm.toOrderEmbedding.map_inf_le (f x) (f y)

@[to_dual]
theorem OrderIso.isMax_apply {α β : Type*} [Preorder α] [Preorder β] (f : α ≃o β) {x : α} :
    IsMax (f x) ↔ IsMax x := by
  refine ⟨f.strictMono.isMax_of_apply, ?_⟩
  conv_lhs => rw [← f.symm_apply_apply x]
  exact f.symm.strictMono.isMax_of_apply

/-- Note that this goal could also be stated `(Disjoint on f) a b` -/
theorem Disjoint.map_orderIso [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β]
    {a b : α} (f : α ≃o β) (ha : Disjoint a b) : Disjoint (f a) (f b) := by
  rw [disjoint_iff_inf_le, ← f.map_inf, ← f.map_bot]
  exact f.monotone ha.le_bot

/-- Note that this goal could also be stated `(Codisjoint on f) a b` -/
@[to_dual existing] -- We can remove this use of `existing` once we get https://github.com/leanprover-community/mathlib4/pull/32438
theorem Codisjoint.map_orderIso [SemilatticeSup α] [OrderTop α] [SemilatticeSup β] [OrderTop β]
    {a b : α} (f : α ≃o β) (ha : Codisjoint a b) : Codisjoint (f a) (f b) := by
  rw [codisjoint_iff_le_sup, ← f.map_sup, ← f.map_top]
  exact f.monotone ha.top_le

@[to_dual (attr := simp)]
theorem disjoint_map_orderIso_iff [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β]
    {a b : α} (f : α ≃o β) : Disjoint (f a) (f b) ↔ Disjoint a b :=
  ⟨fun h => f.symm_apply_apply a ▸ f.symm_apply_apply b ▸ h.map_orderIso f.symm,
   fun h => h.map_orderIso f⟩

section BoundedOrder

variable [Lattice α] [Lattice β] [BoundedOrder α] [BoundedOrder β] (f : α ≃o β)

theorem OrderIso.isCompl {x y : α} (h : IsCompl x y) : IsCompl (f x) (f y) :=
  ⟨h.1.map_orderIso _, h.2.map_orderIso _⟩

theorem OrderIso.isCompl_iff {x y : α} : IsCompl x y ↔ IsCompl (f x) (f y) :=
  ⟨f.isCompl, fun h => f.symm_apply_apply x ▸ f.symm_apply_apply y ▸ f.symm.isCompl h⟩

theorem OrderIso.complementedLattice [ComplementedLattice α] (f : α ≃o β) : ComplementedLattice β :=
  ⟨fun x => by
    obtain ⟨y, hy⟩ := exists_isCompl (f.symm x)
    rw [← f.symm_apply_apply y] at hy
    exact ⟨f y, f.symm.isCompl_iff.2 hy⟩⟩

theorem OrderIso.complementedLattice_iff (f : α ≃o β) :
    ComplementedLattice α ↔ ComplementedLattice β :=
  ⟨by intro; exact f.complementedLattice,
   by intro; exact f.symm.complementedLattice⟩

end BoundedOrder

end LatticeIsos

section DenselyOrdered

-- could live in a more upstream file, but hard to find a good place
lemma StrictMono.denselyOrdered_range {X Y : Type*} [LinearOrder X] [DenselyOrdered X] [Preorder Y]
    {f : X → Y} (hf : StrictMono f) :
    DenselyOrdered (Set.range f) := by
  constructor
  simpa [← exists_and_left, ← exists_and_right, exists_comm, hf.lt_iff_lt]
    using fun _ _ ↦ exists_between

lemma denselyOrdered_iff_of_orderIsoClass {X Y F : Type*} [Preorder X] [Preorder Y]
    [EquivLike F X Y] [OrderIsoClass F X Y] (f : F) :
    DenselyOrdered X ↔ DenselyOrdered Y := by
  constructor
  · intro H
    refine ⟨fun a b h ↦ ?_⟩
    obtain ⟨c, hc⟩ := exists_between ((map_inv_lt_map_inv_iff f).mpr h)
    exact ⟨f c, by simpa using hc⟩
  · intro H
    refine ⟨fun a b h ↦ ?_⟩
    obtain ⟨c, hc⟩ := exists_between ((map_lt_map_iff f).mpr h)
    exact ⟨EquivLike.inv f c, by simpa using hc⟩

lemma denselyOrdered_iff_of_strictAnti {X Y F : Type*} [LinearOrder X] [Preorder Y]
    [EquivLike F X Y] (f : F) (hf : StrictAnti f) :
    DenselyOrdered X ↔ DenselyOrdered Y := by
  rw [← denselyOrdered_orderDual]
  let e : Xᵒᵈ ≃o Y := ⟨OrderDual.ofDual.trans (f : X ≃ Y), ?_⟩
  · exact denselyOrdered_iff_of_orderIsoClass e
  · simp only [Equiv.trans_apply, EquivLike.coe_coe, OrderDual.forall, OrderDual.ofDual_toDual,
      OrderDual.toDual_le_toDual]
    intro a b
    rw [hf.le_iff_ge]

end DenselyOrdered

universe v u in
/-- The bijection `ULift.{v} α ≃ α` as an isomorphism of orders. -/
@[pp_with_univ, simps!]
def ULift.orderIso {α : Type u} [Preorder α] :
    ULift.{v} α ≃o α :=
  Equiv.ulift.toOrderIso (fun _ _ ↦ id) (fun _ _ ↦ id)

namespace Relation

/-- For an injective function `f : α → β`, `Relation.Map · f f` is an order embedding from
`α`-relations into `β`-relations. -/
@[simps]
def mapOrderEmbedding {f : α → β} (hf : f.Injective) : (α → α → Prop) ↪o (β → β → Prop) where
  toFun r := Relation.Map r f f
  inj' r s h := by
    dsimp at h
    rw [← Relation.onFun_map_eq_of_injective (r := r) hf,
      ← Relation.onFun_map_eq_of_injective (r := s) hf, h]
  map_rel_iff' {r s} := by
    refine ⟨fun hle a b hr ↦ ?_, Relation.map_mono⟩
    have ⟨a', b', hs, ha, hb⟩ := hle _ _ ⟨a, b, hr, rfl, rfl⟩
    rwa [← hf ha, ← hf hb]

/-- For a surjective function `f : α → β`, `Function.onFun · f` is an order embedding from
`β`-relations into `α`-relations. -/
@[simps]
def onFunOrderEmbedding {f : α → β} (hf : f.Surjective) : (β → β → Prop) ↪o (α → α → Prop) where
  toFun r := r.onFun f
  inj' r s h := by
    dsimp at h
    rw [← Relation.map_onFun_eq_of_surjective (r := r) hf,
      ← Relation.map_onFun_eq_of_surjective (r := s) hf, h]
  map_rel_iff' {r s} := by
    refine ⟨fun hle a b hr ↦ ?_, fun hle a b hr ↦ hle _ _ hr⟩
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    exact hle a b hr

/-- For a bijective function `f : α → β`, `Relation.Map · f f` and `Function.onFun · f` form an
order isomorphism between `α`-relations and `β`-relations. -/
@[simps]
def mapOnFunOrderIso {f : α → β} (hf : f.Bijective) : (α → α → Prop) ≃o (β → β → Prop) where
  __ := Relation.mapOrderEmbedding hf.injective
  invFun r := r.onFun f
  left_inv _ := Relation.onFun_map_eq_of_injective hf.injective
  right_inv _ := Relation.map_onFun_eq_of_surjective hf.surjective

end Relation
