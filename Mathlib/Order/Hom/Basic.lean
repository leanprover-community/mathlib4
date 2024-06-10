/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Logic.Equiv.Option
import Mathlib.Order.RelIso.Basic
import Mathlib.Order.Disjoint
import Mathlib.Order.WithBot
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Util.AssertExists

#align_import order.hom.basic from "leanprover-community/mathlib"@"62a5626868683c104774de8d85b9855234ac807c"

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
* `OrderHom.prodMap`: `prod.map f g` as a bundled monotone map;
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
  boolean algebra;

We also define two functions to convert other bundled maps to `α →o β`:

* `OrderEmbedding.toOrderHom`: convert `α ↪o β` to `α →o β`;
* `RelHom.toOrderHom`: convert a `RelHom` between strict orders to an `OrderHom`.

## Tags

monotone map, bundled morphism
-/


open OrderDual

variable {F α β γ δ : Type*}

/-- Bundled monotone (aka, increasing) function -/
structure OrderHom (α β : Type*) [Preorder α] [Preorder β] where
  /-- The underlying function of an `OrderHom`. -/
  toFun : α → β
  /-- The underlying function of an `OrderHom` is monotone. -/
  monotone' : Monotone toFun
#align order_hom OrderHom

/-- Notation for an `OrderHom`. -/
infixr:25 " →o " => OrderHom

/-- An order embedding is an embedding `f : α ↪ β` such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `RelEmbedding (≤) (≤)`. -/
abbrev OrderEmbedding (α β : Type*) [LE α] [LE β] :=
  @RelEmbedding α β (· ≤ ·) (· ≤ ·)
#align order_embedding OrderEmbedding

/-- Notation for an `OrderEmbedding`. -/
infixl:25 " ↪o " => OrderEmbedding

/-- An order isomorphism is an equivalence such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `RelIso (≤) (≤)`. -/
abbrev OrderIso (α β : Type*) [LE α] [LE β] :=
  @RelIso α β (· ≤ ·) (· ≤ ·)
#align order_iso OrderIso

/-- Notation for an `OrderIso`. -/
infixl:25 " ≃o " => OrderIso

section

/-- `OrderHomClass F α b` asserts that `F` is a type of `≤`-preserving morphisms. -/
abbrev OrderHomClass (F : Type*) (α β : outParam Type*) [LE α] [LE β] [FunLike F α β] :=
  RelHomClass F ((· ≤ ·) : α → α → Prop) ((· ≤ ·) : β → β → Prop)
#align order_hom_class OrderHomClass

/-- `OrderIsoClass F α β` states that `F` is a type of order isomorphisms.

You should extend this class when you extend `OrderIso`. -/
class OrderIsoClass (F α β : Type*) [LE α] [LE β] [EquivLike F α β] : Prop where
  /-- An order isomorphism respects `≤`. -/
  map_le_map_iff (f : F) {a b : α} : f a ≤ f b ↔ a ≤ b
#align order_iso_class OrderIsoClass

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
#align order_iso_class.to_order_hom_class OrderIsoClass.toOrderHomClass

namespace OrderHomClass

variable [Preorder α] [Preorder β] [FunLike F α β] [OrderHomClass F α β]

protected theorem monotone (f : F) : Monotone f := fun _ _ => map_rel f
#align order_hom_class.monotone OrderHomClass.monotone

protected theorem mono (f : F) : Monotone f := fun _ _ => map_rel f
#align order_hom_class.mono OrderHomClass.mono

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

-- Porting note: needed to add explicit arguments to map_le_map_iff
@[simp]
theorem map_inv_le_iff (f : F) {a : α} {b : β} : EquivLike.inv f b ≤ a ↔ b ≤ f a := by
  convert (map_le_map_iff f (a := EquivLike.inv f b) (b := a)).symm
  exact (EquivLike.right_inv f _).symm
#align map_inv_le_iff map_inv_le_iff

-- Porting note: needed to add explicit arguments to map_le_map_iff
@[simp]
theorem le_map_inv_iff (f : F) {a : α} {b : β} : a ≤ EquivLike.inv f b ↔ f a ≤ b := by
  convert (map_le_map_iff f (a := a) (b := EquivLike.inv f b)).symm
  exact (EquivLike.right_inv _ _).symm
#align le_map_inv_iff le_map_inv_iff

end LE

variable [Preorder α] [Preorder β] [EquivLike F α β] [OrderIsoClass F α β]

theorem map_lt_map_iff (f : F) {a b : α} : f a < f b ↔ a < b :=
  lt_iff_lt_of_le_iff_le' (map_le_map_iff f) (map_le_map_iff f)
#align map_lt_map_iff map_lt_map_iff

@[simp]
theorem map_inv_lt_iff (f : F) {a : α} {b : β} : EquivLike.inv f b < a ↔ b < f a := by
  rw [← map_lt_map_iff f]
  simp only [EquivLike.apply_inv_apply]
#align map_inv_lt_iff map_inv_lt_iff

@[simp]
theorem lt_map_inv_iff (f : F) {a : α} {b : β} : a < EquivLike.inv f b ↔ f a < b := by
  rw [← map_lt_map_iff f]
  simp only [EquivLike.apply_inv_apply]
#align lt_map_inv_iff lt_map_inv_iff

end OrderIsoClass

namespace OrderHom

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]

instance : FunLike (α →o β) α β where
  coe := toFun
  coe_injective' f g h := by cases f; cases g; congr

instance : OrderHomClass (α →o β) α β where
  map_rel f _ _ h := f.monotone' h

@[simp] theorem coe_mk (f : α → β) (hf : Monotone f) : ⇑(mk f hf) = f := rfl
#align order_hom.coe_fun_mk OrderHom.coe_mk

protected theorem monotone (f : α →o β) : Monotone f :=
  f.monotone'
#align order_hom.monotone OrderHom.monotone

protected theorem mono (f : α →o β) : Monotone f :=
  f.monotone
#align order_hom.mono OrderHom.mono

/-- See Note [custom simps projection]. We give this manually so that we use `toFun` as the
projection directly instead. -/
def Simps.coe (f : α →o β) : α → β := f

/- Porting note (#11215): TODO: all other DFunLike classes use `apply` instead of `coe`
for the projection names. Maybe we should change this. -/
initialize_simps_projections OrderHom (toFun → coe)

@[simp] theorem toFun_eq_coe (f : α →o β) : f.toFun = f := rfl
#align order_hom.to_fun_eq_coe OrderHom.toFun_eq_coe

-- See library note [partially-applied ext lemmas]
@[ext]
theorem ext (f g : α →o β) (h : (f : α → β) = g) : f = g :=
  DFunLike.coe_injective h
#align order_hom.ext OrderHom.ext

@[simp] theorem coe_eq (f : α →o β) : OrderHomClass.toOrderHom f = f := rfl

@[simp] theorem _root_.OrderHomClass.coe_coe {F} [FunLike F α β] [OrderHomClass F α β] (f : F) :
    ⇑(f : α →o β) = f :=
  rfl

/-- One can lift an unbundled monotone function to a bundled one. -/
protected instance canLift : CanLift (α → β) (α →o β) (↑) Monotone where
  prf f h := ⟨⟨f, h⟩, rfl⟩
#align order_hom.monotone.can_lift OrderHom.canLift

/-- Copy of an `OrderHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : α →o β) (f' : α → β) (h : f' = f) : α →o β :=
  ⟨f', h.symm.subst f.monotone'⟩
#align order_hom.copy OrderHom.copy

@[simp]
theorem coe_copy (f : α →o β) (f' : α → β) (h : f' = f) : (f.copy f' h) = f' :=
  rfl
#align order_hom.coe_copy OrderHom.coe_copy

theorem copy_eq (f : α →o β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
#align order_hom.copy_eq OrderHom.copy_eq

/-- The identity function as bundled monotone function. -/
@[simps (config := .asFn)]
def id : α →o α :=
  ⟨_root_.id, monotone_id⟩
#align order_hom.id OrderHom.id
#align order_hom.id_coe OrderHom.id_coe

instance : Inhabited (α →o α) :=
  ⟨id⟩

/-- The preorder structure of `α →o β` is pointwise inequality: `f ≤ g ↔ ∀ a, f a ≤ g a`. -/
instance : Preorder (α →o β) :=
  @Preorder.lift (α →o β) (α → β) _ toFun

instance {β : Type*} [PartialOrder β] : PartialOrder (α →o β) :=
  @PartialOrder.lift (α →o β) (α → β) _ toFun ext

theorem le_def {f g : α →o β} : f ≤ g ↔ ∀ x, f x ≤ g x :=
  Iff.rfl
#align order_hom.le_def OrderHom.le_def

@[simp, norm_cast]
theorem coe_le_coe {f g : α →o β} : (f : α → β) ≤ g ↔ f ≤ g :=
  Iff.rfl
#align order_hom.coe_le_coe OrderHom.coe_le_coe

@[simp]
theorem mk_le_mk {f g : α → β} {hf hg} : mk f hf ≤ mk g hg ↔ f ≤ g :=
  Iff.rfl
#align order_hom.mk_le_mk OrderHom.mk_le_mk

@[mono]
theorem apply_mono {f g : α →o β} {x y : α} (h₁ : f ≤ g) (h₂ : x ≤ y) : f x ≤ g y :=
  (h₁ x).trans <| g.mono h₂
#align order_hom.apply_mono OrderHom.apply_mono

/-- Curry/uncurry as an order isomorphism between `α × β →o γ` and `α →o β →o γ`. -/
def curry : (α × β →o γ) ≃o (α →o β →o γ) where
  toFun f := ⟨fun x ↦ ⟨Function.curry f x, fun _ _ h ↦ f.mono ⟨le_rfl, h⟩⟩, fun _ _ h _ =>
    f.mono ⟨h, le_rfl⟩⟩
  invFun f := ⟨Function.uncurry fun x ↦ f x, fun x y h ↦ (f.mono h.1 x.2).trans ((f y.1).mono h.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by simp [le_def]
#align order_hom.curry OrderHom.curry

@[simp]
theorem curry_apply (f : α × β →o γ) (x : α) (y : β) : curry f x y = f (x, y) :=
  rfl
#align order_hom.curry_apply OrderHom.curry_apply

@[simp]
theorem curry_symm_apply (f : α →o β →o γ) (x : α × β) : curry.symm f x = f x.1 x.2 :=
  rfl
#align order_hom.curry_symm_apply OrderHom.curry_symm_apply

/-- The composition of two bundled monotone functions. -/
@[simps (config := .asFn)]
def comp (g : β →o γ) (f : α →o β) : α →o γ :=
  ⟨g ∘ f, g.mono.comp f.mono⟩
#align order_hom.comp OrderHom.comp
#align order_hom.comp_coe OrderHom.comp_coe

@[mono]
theorem comp_mono ⦃g₁ g₂ : β →o γ⦄ (hg : g₁ ≤ g₂) ⦃f₁ f₂ : α →o β⦄ (hf : f₁ ≤ f₂) :
    g₁.comp f₁ ≤ g₂.comp f₂ := fun _ => (hg _).trans (g₂.mono <| hf _)
#align order_hom.comp_mono OrderHom.comp_mono

/-- The composition of two bundled monotone functions, a fully bundled version. -/
@[simps! (config := .asFn)]
def compₘ : (β →o γ) →o (α →o β) →o α →o γ :=
  curry ⟨fun f : (β →o γ) × (α →o β) => f.1.comp f.2, fun _ _ h => comp_mono h.1 h.2⟩
#align order_hom.compₘ OrderHom.compₘ
#align order_hom.compₘ_coe_coe_coe OrderHom.compₘ_coe_coe_coe

@[simp]
theorem comp_id (f : α →o β) : comp f id = f := by
  ext
  rfl
#align order_hom.comp_id OrderHom.comp_id

@[simp]
theorem id_comp (f : α →o β) : comp id f = f := by
  ext
  rfl
#align order_hom.id_comp OrderHom.id_comp

/-- Constant function bundled as an `OrderHom`. -/
@[simps (config := .asFn)]
def const (α : Type*) [Preorder α] {β : Type*} [Preorder β] : β →o α →o β where
  toFun b := ⟨Function.const α b, fun _ _ _ => le_rfl⟩
  monotone' _ _ h _ := h
#align order_hom.const OrderHom.const
#align order_hom.const_coe_coe OrderHom.const_coe_coe

@[simp]
theorem const_comp (f : α →o β) (c : γ) : (const β c).comp f = const α c :=
  rfl
#align order_hom.const_comp OrderHom.const_comp

@[simp]
theorem comp_const (γ : Type*) [Preorder γ] (f : α →o β) (c : α) :
    f.comp (const γ c) = const γ (f c) :=
  rfl
#align order_hom.comp_const OrderHom.comp_const

/-- Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)` bundled as a
`OrderHom`. -/
@[simps]
protected def prod (f : α →o β) (g : α →o γ) : α →o β × γ :=
  ⟨fun x => (f x, g x), fun _ _ h => ⟨f.mono h, g.mono h⟩⟩
#align order_hom.prod OrderHom.prod
#align order_hom.prod_coe OrderHom.prod_coe

@[mono]
theorem prod_mono {f₁ f₂ : α →o β} (hf : f₁ ≤ f₂) {g₁ g₂ : α →o γ} (hg : g₁ ≤ g₂) :
    f₁.prod g₁ ≤ f₂.prod g₂ := fun _ => Prod.le_def.2 ⟨hf _, hg _⟩
#align order_hom.prod_mono OrderHom.prod_mono

theorem comp_prod_comp_same (f₁ f₂ : β →o γ) (g : α →o β) :
    (f₁.comp g).prod (f₂.comp g) = (f₁.prod f₂).comp g :=
  rfl
#align order_hom.comp_prod_comp_same OrderHom.comp_prod_comp_same

/-- Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)` bundled as a
`OrderHom`. This is a fully bundled version. -/
@[simps!]
def prodₘ : (α →o β) →o (α →o γ) →o α →o β × γ :=
  curry ⟨fun f : (α →o β) × (α →o γ) => f.1.prod f.2, fun _ _ h => prod_mono h.1 h.2⟩
#align order_hom.prodₘ OrderHom.prodₘ
#align order_hom.prodₘ_coe_coe_coe OrderHom.prodₘ_coe_coe_coe

/-- Diagonal embedding of `α` into `α × α` as an `OrderHom`. -/
@[simps!]
def diag : α →o α × α :=
  id.prod id
#align order_hom.diag OrderHom.diag
#align order_hom.diag_coe OrderHom.diag_coe

/-- Restriction of `f : α →o α →o β` to the diagonal. -/
@[simps! (config := { simpRhs := true })]
def onDiag (f : α →o α →o β) : α →o β :=
  (curry.symm f).comp diag
#align order_hom.on_diag OrderHom.onDiag
#align order_hom.on_diag_coe OrderHom.onDiag_coe

/-- `Prod.fst` as an `OrderHom`. -/
@[simps]
def fst : α × β →o α :=
  ⟨Prod.fst, fun _ _ h => h.1⟩
#align order_hom.fst OrderHom.fst
#align order_hom.fst_coe OrderHom.fst_coe

/-- `Prod.snd` as an `OrderHom`. -/
@[simps]
def snd : α × β →o β :=
  ⟨Prod.snd, fun _ _ h => h.2⟩
#align order_hom.snd OrderHom.snd
#align order_hom.snd_coe OrderHom.snd_coe

@[simp]
theorem fst_prod_snd : (fst : α × β →o α).prod snd = id := by
  ext ⟨x, y⟩ : 2
  rfl
#align order_hom.fst_prod_snd OrderHom.fst_prod_snd

@[simp]
theorem fst_comp_prod (f : α →o β) (g : α →o γ) : fst.comp (f.prod g) = f :=
  ext _ _ rfl
#align order_hom.fst_comp_prod OrderHom.fst_comp_prod

@[simp]
theorem snd_comp_prod (f : α →o β) (g : α →o γ) : snd.comp (f.prod g) = g :=
  ext _ _ rfl
#align order_hom.snd_comp_prod OrderHom.snd_comp_prod

/-- Order isomorphism between the space of monotone maps to `β × γ` and the product of the spaces
of monotone maps to `β` and `γ`. -/
@[simps]
def prodIso : (α →o β × γ) ≃o (α →o β) × (α →o γ) where
  toFun f := (fst.comp f, snd.comp f)
  invFun f := f.1.prod f.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := forall_and.symm
#align order_hom.prod_iso OrderHom.prodIso
#align order_hom.prod_iso_apply OrderHom.prodIso_apply
#align order_hom.prod_iso_symm_apply OrderHom.prodIso_symm_apply

/-- `Prod.map` of two `OrderHom`s as an `OrderHom`. -/
@[simps]
def prodMap (f : α →o β) (g : γ →o δ) : α × γ →o β × δ :=
  ⟨Prod.map f g, fun _ _ h => ⟨f.mono h.1, g.mono h.2⟩⟩
#align order_hom.prod_map OrderHom.prodMap
#align order_hom.prod_map_coe OrderHom.prodMap_coe

variable {ι : Type*} {π : ι → Type*} [∀ i, Preorder (π i)]

/-- Evaluation of an unbundled function at a point (`Function.eval`) as an `OrderHom`. -/
@[simps (config := .asFn)]
def _root_.Pi.evalOrderHom (i : ι) : (∀ j, π j) →o π i :=
  ⟨Function.eval i, Function.monotone_eval i⟩
#align pi.eval_order_hom Pi.evalOrderHom
#align pi.eval_order_hom_coe Pi.evalOrderHom_coe

/-- The "forgetful functor" from `α →o β` to `α → β` that takes the underlying function,
is monotone. -/
@[simps (config := .asFn)]
def coeFnHom : (α →o β) →o α → β where
  toFun f := f
  monotone' _ _ h := h
#align order_hom.coe_fn_hom OrderHom.coeFnHom
#align order_hom.coe_fn_hom_coe OrderHom.coeFnHom_coe

/-- Function application `fun f => f a` (for fixed `a`) is a monotone function from the
monotone function space `α →o β` to `β`. See also `Pi.evalOrderHom`.  -/
@[simps! (config := .asFn)]
def apply (x : α) : (α →o β) →o β :=
  (Pi.evalOrderHom x).comp coeFnHom
#align order_hom.apply OrderHom.apply
#align order_hom.apply_coe OrderHom.apply_coe

/-- Construct a bundled monotone map `α →o Π i, π i` from a family of monotone maps
`f i : α →o π i`. -/
@[simps]
def pi (f : ∀ i, α →o π i) : α →o ∀ i, π i :=
  ⟨fun x i => f i x, fun _ _ h i => (f i).mono h⟩
#align order_hom.pi OrderHom.pi
#align order_hom.pi_coe OrderHom.pi_coe

/-- Order isomorphism between bundled monotone maps `α →o Π i, π i` and families of bundled monotone
maps `Π i, α →o π i`. -/
@[simps]
def piIso : (α →o ∀ i, π i) ≃o ∀ i, α →o π i where
  toFun f i := (Pi.evalOrderHom i).comp f
  invFun := pi
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := forall_swap
#align order_hom.pi_iso OrderHom.piIso
#align order_hom.pi_iso_apply OrderHom.piIso_apply
#align order_hom.pi_iso_symm_apply OrderHom.piIso_symm_apply

/-- `Subtype.val` as a bundled monotone function.  -/
@[simps (config := .asFn)]
def Subtype.val (p : α → Prop) : Subtype p →o α :=
  ⟨_root_.Subtype.val, fun _ _ h => h⟩
#align order_hom.subtype.val OrderHom.Subtype.val
#align order_hom.subtype.val_coe OrderHom.Subtype.val_coe

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
#align order_hom.unique OrderHom.unique

theorem orderHom_eq_id [Subsingleton α] (g : α →o α) : g = OrderHom.id :=
  Subsingleton.elim _ _
#align order_hom.order_hom_eq_id OrderHom.orderHom_eq_id

/-- Reinterpret a bundled monotone function as a monotone function between dual orders. -/
@[simps]
protected def dual : (α →o β) ≃ (αᵒᵈ →o βᵒᵈ) where
  toFun f := ⟨(OrderDual.toDual : β → βᵒᵈ) ∘ (f : α → β) ∘
    (OrderDual.ofDual : αᵒᵈ → α), f.mono.dual⟩
  invFun f := ⟨OrderDual.ofDual ∘ f ∘ OrderDual.toDual, f.mono.dual⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align order_hom.dual OrderHom.dual
#align order_hom.dual_apply_coe OrderHom.dual_apply_coe
#align order_hom.dual_symm_apply_coe OrderHom.dual_symm_apply_coe

-- Porting note: We used to be able to write `(OrderHom.id : α →o α).dual` here rather than
-- `OrderHom.dual (OrderHom.id : α →o α)`.
-- See https://github.com/leanprover/lean4/issues/1910
@[simp]
theorem dual_id : OrderHom.dual (OrderHom.id : α →o α) = OrderHom.id :=
  rfl
#align order_hom.dual_id OrderHom.dual_id

@[simp]
theorem dual_comp (g : β →o γ) (f : α →o β) :
    OrderHom.dual (g.comp f) = (OrderHom.dual g).comp (OrderHom.dual f) :=
  rfl
#align order_hom.dual_comp OrderHom.dual_comp

@[simp]
theorem symm_dual_id : OrderHom.dual.symm OrderHom.id = (OrderHom.id : α →o α) :=
  rfl
#align order_hom.symm_dual_id OrderHom.symm_dual_id

@[simp]
theorem symm_dual_comp (g : βᵒᵈ →o γᵒᵈ) (f : αᵒᵈ →o βᵒᵈ) :
    OrderHom.dual.symm (g.comp f) = (OrderHom.dual.symm g).comp (OrderHom.dual.symm f) :=
  rfl
#align order_hom.symm_dual_comp OrderHom.symm_dual_comp

/-- `OrderHom.dual` as an order isomorphism. -/
def dualIso (α β : Type*) [Preorder α] [Preorder β] : (α →o β) ≃o (αᵒᵈ →o βᵒᵈ)ᵒᵈ where
  toEquiv := OrderHom.dual.trans OrderDual.toDual
  map_rel_iff' := Iff.rfl
#align order_hom.dual_iso OrderHom.dualIso

/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `WithBot α →o WithBot β`. -/
@[simps (config := .asFn)]
protected def withBotMap (f : α →o β) : WithBot α →o WithBot β :=
  ⟨WithBot.map f, f.mono.withBot_map⟩
#align order_hom.with_bot_map OrderHom.withBotMap
#align order_hom.with_bot_map_coe OrderHom.withBotMap_coe

/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `WithTop α →o WithTop β`. -/
@[simps (config := .asFn)]
protected def withTopMap (f : α →o β) : WithTop α →o WithTop β :=
  ⟨WithTop.map f, f.mono.withTop_map⟩
#align order_hom.with_top_map OrderHom.withTopMap
#align order_hom.with_top_map_coe OrderHom.withTopMap_coe

end OrderHom

/-- Embeddings of partial orders that preserve `<` also preserve `≤`. -/
def RelEmbedding.orderEmbeddingOfLTEmbedding [PartialOrder α] [PartialOrder β]
    (f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)) : α ↪o β :=
  { f with
    map_rel_iff' := by
      intros
      simp [le_iff_lt_or_eq, f.map_rel_iff, f.injective.eq_iff] }
#align rel_embedding.order_embedding_of_lt_embedding RelEmbedding.orderEmbeddingOfLTEmbedding

@[simp]
theorem RelEmbedding.orderEmbeddingOfLTEmbedding_apply [PartialOrder α] [PartialOrder β]
    {f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)} {x : α} :
    RelEmbedding.orderEmbeddingOfLTEmbedding f x = f x :=
  rfl
#align rel_embedding.order_embedding_of_lt_embedding_apply RelEmbedding.orderEmbeddingOfLTEmbedding_apply

namespace OrderEmbedding

variable [Preorder α] [Preorder β] (f : α ↪o β)

/-- `<` is preserved by order embeddings of preorders. -/
def ltEmbedding : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop) :=
  { f with map_rel_iff' := by intros; simp [lt_iff_le_not_le, f.map_rel_iff] }
#align order_embedding.lt_embedding OrderEmbedding.ltEmbedding

@[simp]
theorem ltEmbedding_apply (x : α) : f.ltEmbedding x = f x :=
  rfl
#align order_embedding.lt_embedding_apply OrderEmbedding.ltEmbedding_apply

@[simp]
theorem le_iff_le {a b} : f a ≤ f b ↔ a ≤ b :=
  f.map_rel_iff
#align order_embedding.le_iff_le OrderEmbedding.le_iff_le

@[simp]
theorem lt_iff_lt {a b} : f a < f b ↔ a < b :=
  f.ltEmbedding.map_rel_iff
#align order_embedding.lt_iff_lt OrderEmbedding.lt_iff_lt

theorem eq_iff_eq {a b} : f a = f b ↔ a = b :=
  f.injective.eq_iff
#align order_embedding.eq_iff_eq OrderEmbedding.eq_iff_eq

protected theorem monotone : Monotone f :=
  OrderHomClass.monotone f
#align order_embedding.monotone OrderEmbedding.monotone

protected theorem strictMono : StrictMono f := fun _ _ => f.lt_iff_lt.2
#align order_embedding.strict_mono OrderEmbedding.strictMono

protected theorem acc (a : α) : Acc (· < ·) (f a) → Acc (· < ·) a :=
  f.ltEmbedding.acc a
#align order_embedding.acc OrderEmbedding.acc

protected theorem wellFounded :
    WellFounded ((· < ·) : β → β → Prop) → WellFounded ((· < ·) : α → α → Prop) :=
  f.ltEmbedding.wellFounded
#align order_embedding.well_founded OrderEmbedding.wellFounded

protected theorem isWellOrder [IsWellOrder β (· < ·)] : IsWellOrder α (· < ·) :=
  f.ltEmbedding.isWellOrder
#align order_embedding.is_well_order OrderEmbedding.isWellOrder

/-- An order embedding is also an order embedding between dual orders. -/
protected def dual : αᵒᵈ ↪o βᵒᵈ :=
  ⟨f.toEmbedding, f.map_rel_iff⟩
#align order_embedding.dual OrderEmbedding.dual

/-- A preorder which embeds into a well-founded preorder is itself well-founded. -/
protected theorem wellFoundedLT [WellFoundedLT β] : WellFoundedLT α where
  wf := f.wellFounded IsWellFounded.wf

/-- A preorder which embeds into a preorder in which `(· > ·)` is well-founded
also has `(· > ·)` well-founded. -/
protected theorem wellFoundedGT [WellFoundedGT β] : WellFoundedGT α :=
  @OrderEmbedding.wellFoundedLT αᵒᵈ _ _ _ f.dual _

/-- A version of `WithBot.map` for order embeddings. -/
@[simps (config := .asFn)]
protected def withBotMap (f : α ↪o β) : WithBot α ↪o WithBot β :=
  { f.toEmbedding.optionMap with
    toFun := WithBot.map f,
    map_rel_iff' := @fun a b => WithBot.map_le_iff f f.map_rel_iff a b }
#align order_embedding.with_bot_map OrderEmbedding.withBotMap
#align order_embedding.with_bot_map_apply OrderEmbedding.withBotMap_apply

/-- A version of `WithTop.map` for order embeddings. -/
@[simps (config := .asFn)]
protected def withTopMap (f : α ↪o β) : WithTop α ↪o WithTop β :=
  { f.dual.withBotMap.dual with toFun := WithTop.map f }
#align order_embedding.with_top_map OrderEmbedding.withTopMap
#align order_embedding.with_top_map_apply OrderEmbedding.withTopMap_apply

/-- To define an order embedding from a partial order to a preorder it suffices to give a function
together with a proof that it satisfies `f a ≤ f b ↔ a ≤ b`.
-/
def ofMapLEIff {α β} [PartialOrder α] [Preorder β] (f : α → β) (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) :
    α ↪o β :=
  RelEmbedding.ofMapRelIff f hf
#align order_embedding.of_map_le_iff OrderEmbedding.ofMapLEIff

@[simp]
theorem coe_ofMapLEIff {α β} [PartialOrder α] [Preorder β] {f : α → β} (h) :
    ⇑(ofMapLEIff f h) = f :=
  rfl
#align order_embedding.coe_of_map_le_iff OrderEmbedding.coe_ofMapLEIff

/-- A strictly monotone map from a linear order is an order embedding. -/
def ofStrictMono {α β} [LinearOrder α] [Preorder β] (f : α → β) (h : StrictMono f) : α ↪o β :=
  ofMapLEIff f fun _ _ => h.le_iff_le
#align order_embedding.of_strict_mono OrderEmbedding.ofStrictMono

@[simp]
theorem coe_ofStrictMono {α β} [LinearOrder α] [Preorder β] {f : α → β} (h : StrictMono f) :
    ⇑(ofStrictMono f h) = f :=
  rfl
#align order_embedding.coe_of_strict_mono OrderEmbedding.coe_ofStrictMono

/-- Embedding of a subtype into the ambient type as an `OrderEmbedding`. -/
@[simps! (config := .asFn)]
def subtype (p : α → Prop) : Subtype p ↪o α :=
  ⟨Function.Embedding.subtype p, Iff.rfl⟩
#align order_embedding.subtype OrderEmbedding.subtype
#align order_embedding.subtype_apply OrderEmbedding.subtype_apply

/-- Convert an `OrderEmbedding` to an `OrderHom`. -/
@[simps (config := .asFn)]
def toOrderHom {X Y : Type*} [Preorder X] [Preorder Y] (f : X ↪o Y) : X →o Y where
  toFun := f
  monotone' := f.monotone
#align order_embedding.to_order_hom OrderEmbedding.toOrderHom
#align order_embedding.to_order_hom_coe OrderEmbedding.toOrderHom_coe

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
@[simps (config := .asFn)]
def toOrderHom : α →o β where
  toFun := f
  monotone' := StrictMono.monotone fun _ _ => f.map_rel
#align rel_hom.to_order_hom RelHom.toOrderHom
#align rel_hom.to_order_hom_coe RelHom.toOrderHom_coe

end RelHom

theorem RelEmbedding.toOrderHom_injective
    (f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)) :
    Function.Injective (f : ((· < ·) : α → α → Prop) →r ((· < ·) : β → β → Prop)).toOrderHom :=
  fun _ _ h => f.injective h
#align rel_embedding.to_order_hom_injective RelEmbedding.toOrderHom_injective

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
#align order_iso.to_fun_eq_coe OrderIso.toFun_eq_coe

-- See note [partially-applied ext lemmas]
@[ext]
theorem ext {f g : α ≃o β} (h : (f : α → β) = g) : f = g :=
  DFunLike.coe_injective h
#align order_iso.ext OrderIso.ext

/-- Reinterpret an order isomorphism as an order embedding. -/
def toOrderEmbedding (e : α ≃o β) : α ↪o β :=
  e.toRelEmbedding
#align order_iso.to_order_embedding OrderIso.toOrderEmbedding

@[simp]
theorem coe_toOrderEmbedding (e : α ≃o β) : ⇑e.toOrderEmbedding = e :=
  rfl
#align order_iso.coe_to_order_embedding OrderIso.coe_toOrderEmbedding

protected theorem bijective (e : α ≃o β) : Function.Bijective e :=
  e.toEquiv.bijective
#align order_iso.bijective OrderIso.bijective

protected theorem injective (e : α ≃o β) : Function.Injective e :=
  e.toEquiv.injective
#align order_iso.injective OrderIso.injective

protected theorem surjective (e : α ≃o β) : Function.Surjective e :=
  e.toEquiv.surjective
#align order_iso.surjective OrderIso.surjective

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem apply_eq_iff_eq (e : α ≃o β) {x y : α} : e x = e y ↔ x = y :=
  e.toEquiv.apply_eq_iff_eq
#align order_iso.apply_eq_iff_eq OrderIso.apply_eq_iff_eq

/-- Identity order isomorphism. -/
def refl (α : Type*) [LE α] : α ≃o α :=
  RelIso.refl (· ≤ ·)
#align order_iso.refl OrderIso.refl

@[simp]
theorem coe_refl : ⇑(refl α) = id :=
  rfl
#align order_iso.coe_refl OrderIso.coe_refl

@[simp]
theorem refl_apply (x : α) : refl α x = x :=
  rfl
#align order_iso.refl_apply OrderIso.refl_apply

@[simp]
theorem refl_toEquiv : (refl α).toEquiv = Equiv.refl α :=
  rfl
#align order_iso.refl_to_equiv OrderIso.refl_toEquiv

/-- Inverse of an order isomorphism. -/
def symm (e : α ≃o β) : β ≃o α := RelIso.symm e
#align order_iso.symm OrderIso.symm

@[simp]
theorem apply_symm_apply (e : α ≃o β) (x : β) : e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply x
#align order_iso.apply_symm_apply OrderIso.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : α ≃o β) (x : α) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x
#align order_iso.symm_apply_apply OrderIso.symm_apply_apply

@[simp]
theorem symm_refl (α : Type*) [LE α] : (refl α).symm = refl α :=
  rfl
#align order_iso.symm_refl OrderIso.symm_refl

theorem apply_eq_iff_eq_symm_apply (e : α ≃o β) (x : α) (y : β) : e x = y ↔ x = e.symm y :=
  e.toEquiv.apply_eq_iff_eq_symm_apply
#align order_iso.apply_eq_iff_eq_symm_apply OrderIso.apply_eq_iff_eq_symm_apply

theorem symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.symm y = x ↔ y = e x :=
  e.toEquiv.symm_apply_eq
#align order_iso.symm_apply_eq OrderIso.symm_apply_eq

@[simp]
theorem symm_symm (e : α ≃o β) : e.symm.symm = e := by
  ext
  rfl
#align order_iso.symm_symm OrderIso.symm_symm

theorem symm_bijective : Function.Bijective (OrderIso.symm : (α ≃o β) → β ≃o α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

theorem symm_injective : Function.Injective (symm : α ≃o β → β ≃o α) :=
  symm_bijective.injective
#align order_iso.symm_injective OrderIso.symm_injective

@[simp]
theorem toEquiv_symm (e : α ≃o β) : e.toEquiv.symm = e.symm.toEquiv :=
  rfl
#align order_iso.to_equiv_symm OrderIso.toEquiv_symm

/-- Composition of two order isomorphisms is an order isomorphism. -/
@[trans]
def trans (e : α ≃o β) (e' : β ≃o γ) : α ≃o γ :=
  RelIso.trans e e'
#align order_iso.trans OrderIso.trans

@[simp]
theorem coe_trans (e : α ≃o β) (e' : β ≃o γ) : ⇑(e.trans e') = e' ∘ e :=
  rfl
#align order_iso.coe_trans OrderIso.coe_trans

@[simp]
theorem trans_apply (e : α ≃o β) (e' : β ≃o γ) (x : α) : e.trans e' x = e' (e x) :=
  rfl
#align order_iso.trans_apply OrderIso.trans_apply

@[simp]
theorem refl_trans (e : α ≃o β) : (refl α).trans e = e := by
  ext x
  rfl
#align order_iso.refl_trans OrderIso.refl_trans

@[simp]
theorem trans_refl (e : α ≃o β) : e.trans (refl β) = e := by
  ext x
  rfl
#align order_iso.trans_refl OrderIso.trans_refl

@[simp]
theorem symm_trans_apply (e₁ : α ≃o β) (e₂ : β ≃o γ) (c : γ) :
    (e₁.trans e₂).symm c = e₁.symm (e₂.symm c) :=
  rfl
#align order_iso.symm_trans_apply OrderIso.symm_trans_apply

theorem symm_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) : (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl
#align order_iso.symm_trans OrderIso.symm_trans

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
  toFun  p := .comp g <| .comp p f.symm
  invFun p := .comp g.symm <| .comp p f
  left_inv p := DFunLike.coe_injective <| by
    change (g.symm ∘ g) ∘ p ∘ (f.symm ∘ f) = p
    simp only [← DFunLike.coe_eq_coe_fn, ← OrderIso.coe_trans, Function.id_comp,
               OrderIso.self_trans_symm, OrderIso.coe_refl, Function.comp_id]
  right_inv p := DFunLike.coe_injective <| by
    change (g ∘ g.symm) ∘ p ∘ (f ∘ f.symm) = p
    simp only [← DFunLike.coe_eq_coe_fn, ← OrderIso.coe_trans, Function.id_comp,
               OrderIso.symm_trans_self, OrderIso.coe_refl, Function.comp_id]
  map_rel_iff' {p q} := by
    simp only [Equiv.coe_fn_mk, OrderHom.le_def, OrderHom.comp_coe,
               OrderHomClass.coe_coe, Function.comp_apply, map_le_map_iff]
    exact Iff.symm f.forall_congr_left'

/-- If `α` and `β` are order-isomorphic then the two orders of order-homomorphisms
from `α` and `β` to themselves are order-isomorphic. -/
@[simps! apply symm_apply]
def conj {α β} [Preorder α] [Preorder β] (f : α ≃o β) : (α →o α) ≃ (β →o β) :=
  arrowCongr f f

/-- `Prod.swap` as an `OrderIso`. -/
def prodComm : α × β ≃o β × α where
  toEquiv := Equiv.prodComm α β
  map_rel_iff' := Prod.swap_le_swap
#align order_iso.prod_comm OrderIso.prodComm

@[simp]
theorem coe_prodComm : ⇑(prodComm : α × β ≃o β × α) = Prod.swap :=
  rfl
#align order_iso.coe_prod_comm OrderIso.coe_prodComm

@[simp]
theorem prodComm_symm : (prodComm : α × β ≃o β × α).symm = prodComm :=
  rfl
#align order_iso.prod_comm_symm OrderIso.prodComm_symm

variable (α)

/-- The order isomorphism between a type and its double dual. -/
def dualDual : α ≃o αᵒᵈᵒᵈ :=
  refl α
#align order_iso.dual_dual OrderIso.dualDual

@[simp]
theorem coe_dualDual : ⇑(dualDual α) = toDual ∘ toDual :=
  rfl
#align order_iso.coe_dual_dual OrderIso.coe_dualDual

@[simp]
theorem coe_dualDual_symm : ⇑(dualDual α).symm = ofDual ∘ ofDual :=
  rfl
#align order_iso.coe_dual_dual_symm OrderIso.coe_dualDual_symm

variable {α}

@[simp]
theorem dualDual_apply (a : α) : dualDual α a = toDual (toDual a) :=
  rfl
#align order_iso.dual_dual_apply OrderIso.dualDual_apply

@[simp]
theorem dualDual_symm_apply (a : αᵒᵈᵒᵈ) : (dualDual α).symm a = ofDual (ofDual a) :=
  rfl
#align order_iso.dual_dual_symm_apply OrderIso.dualDual_symm_apply

end LE

open Set

section LE

variable [LE α] [LE β] [LE γ]

--@[simp] Porting note (#10618): simp can prove it
theorem le_iff_le (e : α ≃o β) {x y : α} : e x ≤ e y ↔ x ≤ y :=
  e.map_rel_iff
#align order_iso.le_iff_le OrderIso.le_iff_le

theorem le_symm_apply (e : α ≃o β) {x : α} {y : β} : x ≤ e.symm y ↔ e x ≤ y :=
  e.rel_symm_apply
#align order_iso.le_symm_apply OrderIso.le_symm_apply

theorem symm_apply_le (e : α ≃o β) {x : α} {y : β} : e.symm y ≤ x ↔ y ≤ e x :=
  e.symm_apply_rel
#align order_iso.symm_apply_le OrderIso.symm_apply_le

end LE

variable [Preorder α] [Preorder β] [Preorder γ]

protected theorem monotone (e : α ≃o β) : Monotone e :=
  e.toOrderEmbedding.monotone
#align order_iso.monotone OrderIso.monotone

protected theorem strictMono (e : α ≃o β) : StrictMono e :=
  e.toOrderEmbedding.strictMono
#align order_iso.strict_mono OrderIso.strictMono

@[simp]
theorem lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y :=
  e.toOrderEmbedding.lt_iff_lt
#align order_iso.lt_iff_lt OrderIso.lt_iff_lt

/-- Converts an `OrderIso` into a `RelIso (<) (<)`. -/
def toRelIsoLT (e : α ≃o β) : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop) :=
  ⟨e.toEquiv, lt_iff_lt e⟩
#align order_iso.to_rel_iso_lt OrderIso.toRelIsoLT

@[simp]
theorem toRelIsoLT_apply (e : α ≃o β) (x : α) : e.toRelIsoLT x = e x :=
  rfl
#align order_iso.to_rel_iso_lt_apply OrderIso.toRelIsoLT_apply

@[simp]
theorem toRelIsoLT_symm (e : α ≃o β) : e.toRelIsoLT.symm = e.symm.toRelIsoLT :=
  rfl
#align order_iso.to_rel_iso_lt_symm OrderIso.toRelIsoLT_symm

/-- Converts a `RelIso (<) (<)` into an `OrderIso`. -/
def ofRelIsoLT {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) : α ≃o β :=
  ⟨e.toEquiv, by simp [le_iff_eq_or_lt, e.map_rel_iff, e.injective.eq_iff]⟩
#align order_iso.of_rel_iso_lt OrderIso.ofRelIsoLT

@[simp]
theorem ofRelIsoLT_apply {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) (x : α) : ofRelIsoLT e x = e x :=
  rfl
#align order_iso.of_rel_iso_lt_apply OrderIso.ofRelIsoLT_apply

@[simp]
theorem ofRelIsoLT_symm {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) :
    (ofRelIsoLT e).symm = ofRelIsoLT e.symm :=
  rfl
#align order_iso.of_rel_iso_lt_symm OrderIso.ofRelIsoLT_symm

@[simp]
theorem ofRelIsoLT_toRelIsoLT {α β} [PartialOrder α] [PartialOrder β] (e : α ≃o β) :
    ofRelIsoLT (toRelIsoLT e) = e := by
  ext
  simp
#align order_iso.of_rel_iso_lt_to_rel_iso_lt OrderIso.ofRelIsoLT_toRelIsoLT

@[simp]
theorem toRelIsoLT_ofRelIsoLT {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) : toRelIsoLT (ofRelIsoLT e) = e := by
  ext
  simp
#align order_iso.to_rel_iso_lt_of_rel_iso_lt OrderIso.toRelIsoLT_ofRelIsoLT

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
      intros a b
      apply le_iff_le_of_cmp_eq_cmp
      convert (h a (f b)).symm
      apply gf }
#align order_iso.of_cmp_eq_cmp OrderIso.ofCmpEqCmp

/-- To show that `f : α →o β` and `g : β →o α` make up an order isomorphism it is enough to show
    that `g` is the inverse of `f`-/
def ofHomInv {F G : Type*} [FunLike F α β] [OrderHomClass F α β] [FunLike G β α]
    [OrderHomClass G β α] (f : F) (g : G)
    (h₁ : (f : α →o β).comp (g : β →o α) = OrderHom.id)
    (h₂ : (g : β →o α).comp (f : α →o β) = OrderHom.id) :
    α ≃o β where
  toFun := f
  invFun := g
  left_inv := DFunLike.congr_fun h₂
  right_inv := DFunLike.congr_fun h₁
  map_rel_iff' := @fun a b =>
    ⟨fun h => by
      replace h := map_rel g h
      rwa [Equiv.coe_fn_mk, show g (f a) = (g : β →o α).comp (f : α →o β) a from rfl,
        show g (f b) = (g : β →o α).comp (f : α →o β) b from rfl, h₂] at h,
      fun h => (f : α →o β).monotone h⟩
#align order_iso.of_hom_inv OrderIso.ofHomInv

/-- Order isomorphism between `α → β` and `β`, where `α` has a unique element. -/
@[simps! toEquiv apply]
def funUnique (α β : Type*) [Unique α] [Preorder β] : (α → β) ≃o β where
  toEquiv := Equiv.funUnique α β
  map_rel_iff' := by simp [Pi.le_def, Unique.forall_iff]
#align order_iso.fun_unique OrderIso.funUnique
#align order_iso.fun_unique_apply OrderIso.funUnique_apply
#align order_iso.fun_unique_to_equiv OrderIso.funUnique_toEquiv

@[simp]
theorem funUnique_symm_apply {α β : Type*} [Unique α] [Preorder β] :
    ((funUnique α β).symm : β → α → β) = Function.const α :=
  rfl
#align order_iso.fun_unique_symm_apply OrderIso.funUnique_symm_apply

end OrderIso

namespace Equiv

variable [Preorder α] [Preorder β]

/-- If `e` is an equivalence with monotone forward and inverse maps, then `e` is an
order isomorphism. -/
def toOrderIso (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) : α ≃o β :=
  ⟨e, ⟨fun h => by simpa only [e.symm_apply_apply] using h₂ h, fun h => h₁ h⟩⟩
#align equiv.to_order_iso Equiv.toOrderIso

@[simp]
theorem coe_toOrderIso (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) :
    ⇑(e.toOrderIso h₁ h₂) = e :=
  rfl
#align equiv.coe_to_order_iso Equiv.coe_toOrderIso

@[simp]
theorem toOrderIso_toEquiv (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) :
    (e.toOrderIso h₁ h₂).toEquiv = e :=
  rfl
#align equiv.to_order_iso_to_equiv Equiv.toOrderIso_toEquiv

end Equiv

namespace StrictMono

variable [LinearOrder α] [Preorder β]
variable (f : α → β) (h_mono : StrictMono f) (h_surj : Function.Surjective f)

/-- A strictly monotone function with a right inverse is an order isomorphism. -/
@[simps (config := .asFn)]
def orderIsoOfRightInverse (g : β → α) (hg : Function.RightInverse g f) : α ≃o β :=
  { OrderEmbedding.ofStrictMono f h_mono with
    toFun := f,
    invFun := g,
    left_inv := fun _ => h_mono.injective <| hg _,
    right_inv := hg }
#align strict_mono.order_iso_of_right_inverse StrictMono.orderIsoOfRightInverse
#align strict_mono.order_iso_of_right_inverse_apply StrictMono.orderIsoOfRightInverse_apply
#align strict_mono.order_iso_of_right_inverse_symm_apply StrictMono.orderIsoOfRightInverse_symm_apply

end StrictMono

/-- An order isomorphism is also an order isomorphism between dual orders. -/
protected def OrderIso.dual [LE α] [LE β] (f : α ≃o β) : αᵒᵈ ≃o βᵒᵈ :=
  ⟨f.toEquiv, f.map_rel_iff⟩
#align order_iso.dual OrderIso.dual

section LatticeIsos

theorem OrderIso.map_bot' [LE α] [PartialOrder β] (f : α ≃o β) {x : α} {y : β} (hx : ∀ x', x ≤ x')
    (hy : ∀ y', y ≤ y') : f x = y := by
  refine le_antisymm ?_ (hy _)
  rw [← f.apply_symm_apply y, f.map_rel_iff]
  apply hx
#align order_iso.map_bot' OrderIso.map_bot'

theorem OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] [OrderBot β] (f : α ≃o β) : f ⊥ = ⊥ :=
  f.map_bot' (fun _ => bot_le) fun _ => bot_le
#align order_iso.map_bot OrderIso.map_bot

theorem OrderIso.map_top' [LE α] [PartialOrder β] (f : α ≃o β) {x : α} {y : β} (hx : ∀ x', x' ≤ x)
    (hy : ∀ y', y' ≤ y) : f x = y :=
  f.dual.map_bot' hx hy
#align order_iso.map_top' OrderIso.map_top'

theorem OrderIso.map_top [LE α] [PartialOrder β] [OrderTop α] [OrderTop β] (f : α ≃o β) : f ⊤ = ⊤ :=
  f.dual.map_bot
#align order_iso.map_top OrderIso.map_top

theorem OrderEmbedding.map_inf_le [SemilatticeInf α] [SemilatticeInf β] (f : α ↪o β) (x y : α) :
    f (x ⊓ y) ≤ f x ⊓ f y :=
  f.monotone.map_inf_le x y
#align order_embedding.map_inf_le OrderEmbedding.map_inf_le

theorem OrderEmbedding.le_map_sup [SemilatticeSup α] [SemilatticeSup β] (f : α ↪o β) (x y : α) :
    f x ⊔ f y ≤ f (x ⊔ y) :=
  f.monotone.le_map_sup x y
#align order_embedding.le_map_sup OrderEmbedding.le_map_sup

theorem OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β] (f : α ≃o β) (x y : α) :
    f (x ⊓ y) = f x ⊓ f y := by
  refine (f.toOrderEmbedding.map_inf_le x y).antisymm ?_
  apply f.symm.le_iff_le.1
  simpa using f.symm.toOrderEmbedding.map_inf_le (f x) (f y)
#align order_iso.map_inf OrderIso.map_inf

theorem OrderIso.map_sup [SemilatticeSup α] [SemilatticeSup β] (f : α ≃o β) (x y : α) :
    f (x ⊔ y) = f x ⊔ f y :=
  f.dual.map_inf x y
#align order_iso.map_sup OrderIso.map_sup

/-- Note that this goal could also be stated `(Disjoint on f) a b` -/
theorem Disjoint.map_orderIso [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β]
    {a b : α} (f : α ≃o β) (ha : Disjoint a b) : Disjoint (f a) (f b) := by
  rw [disjoint_iff_inf_le, ← f.map_inf, ← f.map_bot]
  exact f.monotone ha.le_bot
#align disjoint.map_order_iso Disjoint.map_orderIso

/-- Note that this goal could also be stated `(Codisjoint on f) a b` -/
theorem Codisjoint.map_orderIso [SemilatticeSup α] [OrderTop α] [SemilatticeSup β] [OrderTop β]
    {a b : α} (f : α ≃o β) (ha : Codisjoint a b) : Codisjoint (f a) (f b) := by
  rw [codisjoint_iff_le_sup, ← f.map_sup, ← f.map_top]
  exact f.monotone ha.top_le
#align codisjoint.map_order_iso Codisjoint.map_orderIso

@[simp]
theorem disjoint_map_orderIso_iff [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β]
    {a b : α} (f : α ≃o β) : Disjoint (f a) (f b) ↔ Disjoint a b :=
  ⟨fun h => f.symm_apply_apply a ▸ f.symm_apply_apply b ▸ h.map_orderIso f.symm,
   fun h => h.map_orderIso f⟩
#align disjoint_map_order_iso_iff disjoint_map_orderIso_iff

@[simp]
theorem codisjoint_map_orderIso_iff [SemilatticeSup α] [OrderTop α] [SemilatticeSup β] [OrderTop β]
    {a b : α} (f : α ≃o β) : Codisjoint (f a) (f b) ↔ Codisjoint a b :=
  ⟨fun h => f.symm_apply_apply a ▸ f.symm_apply_apply b ▸ h.map_orderIso f.symm,
   fun h => h.map_orderIso f⟩
#align codisjoint_map_order_iso_iff codisjoint_map_orderIso_iff

namespace WithBot

/-- Taking the dual then adding `⊥` is the same as adding `⊤` then taking the dual.
This is the order iso form of `WithBot.ofDual`, as proven by `coe_toDualTopEquiv_eq`.
-/
protected def toDualTopEquiv [LE α] : WithBot αᵒᵈ ≃o (WithTop α)ᵒᵈ :=
  OrderIso.refl _
#align with_bot.to_dual_top_equiv WithBot.toDualTopEquiv

@[simp]
theorem toDualTopEquiv_coe [LE α] (a : α) :
    WithBot.toDualTopEquiv ↑(toDual a) = toDual (a : WithTop α) :=
  rfl
#align with_bot.to_dual_top_equiv_coe WithBot.toDualTopEquiv_coe

@[simp]
theorem toDualTopEquiv_symm_coe [LE α] (a : α) :
    WithBot.toDualTopEquiv.symm (toDual (a : WithTop α)) = ↑(toDual a) :=
  rfl
#align with_bot.to_dual_top_equiv_symm_coe WithBot.toDualTopEquiv_symm_coe

@[simp]
theorem toDualTopEquiv_bot [LE α] : WithBot.toDualTopEquiv (⊥ : WithBot αᵒᵈ) = ⊥ :=
  rfl
#align with_bot.to_dual_top_equiv_bot WithBot.toDualTopEquiv_bot

@[simp]
theorem toDualTopEquiv_symm_bot [LE α] : WithBot.toDualTopEquiv.symm (⊥ : (WithTop α)ᵒᵈ) = ⊥ :=
  rfl
#align with_bot.to_dual_top_equiv_symm_bot WithBot.toDualTopEquiv_symm_bot

theorem coe_toDualTopEquiv_eq [LE α] :
    (WithBot.toDualTopEquiv : WithBot αᵒᵈ → (WithTop α)ᵒᵈ) = toDual ∘ WithBot.ofDual :=
  funext fun _ => rfl
#align with_bot.coe_to_dual_top_equiv_eq WithBot.coe_toDualTopEquiv_eq

end WithBot

namespace WithTop

/-- Taking the dual then adding `⊤` is the same as adding `⊥` then taking the dual.
This is the order iso form of `WithTop.ofDual`, as proven by `coe_toDualBotEquiv_eq`. -/
protected def toDualBotEquiv [LE α] : WithTop αᵒᵈ ≃o (WithBot α)ᵒᵈ :=
  OrderIso.refl _
#align with_top.to_dual_bot_equiv WithTop.toDualBotEquiv

@[simp]
theorem toDualBotEquiv_coe [LE α] (a : α) :
    WithTop.toDualBotEquiv ↑(toDual a) = toDual (a : WithBot α) :=
  rfl
#align with_top.to_dual_bot_equiv_coe WithTop.toDualBotEquiv_coe

@[simp]
theorem toDualBotEquiv_symm_coe [LE α] (a : α) :
    WithTop.toDualBotEquiv.symm (toDual (a : WithBot α)) = ↑(toDual a) :=
  rfl
#align with_top.to_dual_bot_equiv_symm_coe WithTop.toDualBotEquiv_symm_coe

@[simp]
theorem toDualBotEquiv_top [LE α] : WithTop.toDualBotEquiv (⊤ : WithTop αᵒᵈ) = ⊤ :=
  rfl
#align with_top.to_dual_bot_equiv_top WithTop.toDualBotEquiv_top

@[simp]
theorem toDualBotEquiv_symm_top [LE α] : WithTop.toDualBotEquiv.symm (⊤ : (WithBot α)ᵒᵈ) = ⊤ :=
  rfl
#align with_top.to_dual_bot_equiv_symm_top WithTop.toDualBotEquiv_symm_top

theorem coe_toDualBotEquiv [LE α] :
    (WithTop.toDualBotEquiv : WithTop αᵒᵈ → (WithBot α)ᵒᵈ) = toDual ∘ WithTop.ofDual :=
  funext fun _ => rfl
#align with_top.coe_to_dual_bot_equiv_eq WithTop.coe_toDualBotEquiv

end WithTop

namespace OrderIso

variable [PartialOrder α] [PartialOrder β] [PartialOrder γ]

/-- A version of `Equiv.optionCongr` for `WithTop`. -/
@[simps! apply]
def withTopCongr (e : α ≃o β) : WithTop α ≃o WithTop β :=
  { e.toOrderEmbedding.withTopMap with
    toEquiv := e.toEquiv.optionCongr }
#align order_iso.with_top_congr OrderIso.withTopCongr
#align order_iso.with_top_congr_apply OrderIso.withTopCongr_apply

@[simp]
theorem withTopCongr_refl : (OrderIso.refl α).withTopCongr = OrderIso.refl _ :=
  RelIso.toEquiv_injective Equiv.optionCongr_refl
#align order_iso.with_top_congr_refl OrderIso.withTopCongr_refl

@[simp]
theorem withTopCongr_symm (e : α ≃o β) : e.withTopCongr.symm = e.symm.withTopCongr :=
  RelIso.toEquiv_injective e.toEquiv.optionCongr_symm
#align order_iso.with_top_congr_symm OrderIso.withTopCongr_symm

@[simp]
theorem withTopCongr_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) :
    e₁.withTopCongr.trans e₂.withTopCongr = (e₁.trans e₂).withTopCongr :=
  RelIso.toEquiv_injective <| e₁.toEquiv.optionCongr_trans e₂.toEquiv
#align order_iso.with_top_congr_trans OrderIso.withTopCongr_trans

/-- A version of `Equiv.optionCongr` for `WithBot`. -/
@[simps! apply]
def withBotCongr (e : α ≃o β) : WithBot α ≃o WithBot β :=
  { e.toOrderEmbedding.withBotMap with toEquiv := e.toEquiv.optionCongr }
#align order_iso.with_bot_congr OrderIso.withBotCongr
#align order_iso.with_bot_congr_apply OrderIso.withBotCongr_apply

@[simp]
theorem withBotCongr_refl : (OrderIso.refl α).withBotCongr = OrderIso.refl _ :=
  RelIso.toEquiv_injective Equiv.optionCongr_refl
#align order_iso.with_bot_congr_refl OrderIso.withBotCongr_refl

@[simp]
theorem withBotCongr_symm (e : α ≃o β) : e.withBotCongr.symm = e.symm.withBotCongr :=
  RelIso.toEquiv_injective e.toEquiv.optionCongr_symm
#align order_iso.with_bot_congr_symm OrderIso.withBotCongr_symm

@[simp]
theorem withBotCongr_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) :
    e₁.withBotCongr.trans e₂.withBotCongr = (e₁.trans e₂).withBotCongr :=
  RelIso.toEquiv_injective <| e₁.toEquiv.optionCongr_trans e₂.toEquiv
#align order_iso.with_bot_congr_trans OrderIso.withBotCongr_trans

end OrderIso

section BoundedOrder

variable [Lattice α] [Lattice β] [BoundedOrder α] [BoundedOrder β] (f : α ≃o β)

theorem OrderIso.isCompl {x y : α} (h : IsCompl x y) : IsCompl (f x) (f y) :=
  ⟨h.1.map_orderIso _, h.2.map_orderIso _⟩
#align order_iso.is_compl OrderIso.isCompl

theorem OrderIso.isCompl_iff {x y : α} : IsCompl x y ↔ IsCompl (f x) (f y) :=
  ⟨f.isCompl, fun h => f.symm_apply_apply x ▸ f.symm_apply_apply y ▸ f.symm.isCompl h⟩
#align order_iso.is_compl_iff OrderIso.isCompl_iff

theorem OrderIso.complementedLattice [ComplementedLattice α] : ComplementedLattice β :=
  ⟨fun x => by
    obtain ⟨y, hy⟩ := exists_isCompl (f.symm x)
    rw [← f.symm_apply_apply y] at hy
    exact ⟨f y, f.symm.isCompl_iff.2 hy⟩⟩
#align order_iso.complemented_lattice OrderIso.complementedLattice

theorem OrderIso.complementedLattice_iff : ComplementedLattice α ↔ ComplementedLattice β :=
  ⟨by intro; exact f.complementedLattice,
   by intro; exact f.symm.complementedLattice⟩
#align order_iso.complemented_lattice_iff OrderIso.complementedLattice_iff

end BoundedOrder

end LatticeIsos

-- Developments relating order homs and sets belong in `Order.Hom.Set` or later.
assert_not_exists Set.range
