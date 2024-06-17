/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Hom.Bounded
import Mathlib.Topology.Order.Hom.Basic

#align_import topology.order.hom.esakia from "leanprover-community/mathlib"@"9822b65bfc4ac74537d77ae318d27df1df662471"

/-!
# Esakia morphisms

This file defines pseudo-epimorphisms and Esakia morphisms.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `PseudoEpimorphism`: Pseudo-epimorphisms. Maps `f` such that `f a ≤ b` implies the existence of
  `a'` such that `a ≤ a'` and `f a' = b`.
* `EsakiaHom`: Esakia morphisms. Continuous pseudo-epimorphisms.

## Typeclasses

* `PseudoEpimorphismClass`
* `EsakiaHomClass`

## References

* [Wikipedia, *Esakia space*](https://en.wikipedia.org/wiki/Esakia_space)
-/


open Function

variable {F α β γ δ : Type*}

/-- The type of pseudo-epimorphisms, aka p-morphisms, aka bounded maps, from `α` to `β`. -/
structure PseudoEpimorphism (α β : Type*) [Preorder α] [Preorder β] extends α →o β where
  exists_map_eq_of_map_le' ⦃a : α⦄ ⦃b : β⦄ : toFun a ≤ b → ∃ c, a ≤ c ∧ toFun c = b
#align pseudo_epimorphism PseudoEpimorphism

/-- The type of Esakia morphisms, aka continuous pseudo-epimorphisms, from `α` to `β`. -/
structure EsakiaHom (α β : Type*) [TopologicalSpace α] [Preorder α] [TopologicalSpace β]
  [Preorder β] extends α →Co β where
  exists_map_eq_of_map_le' ⦃a : α⦄ ⦃b : β⦄ : toFun a ≤ b → ∃ c, a ≤ c ∧ toFun c = b
#align esakia_hom EsakiaHom

section

/-- `PseudoEpimorphismClass F α β` states that `F` is a type of `⊔`-preserving morphisms.

You should extend this class when you extend `PseudoEpimorphism`. -/
class PseudoEpimorphismClass (F : Type*) (α β : outParam Type*)
    [Preorder α] [Preorder β] [FunLike F α β]
    extends RelHomClass F ((· ≤ ·) : α → α → Prop) ((· ≤ ·) : β → β → Prop) : Prop where
  exists_map_eq_of_map_le (f : F) ⦃a : α⦄ ⦃b : β⦄ : f a ≤ b → ∃ c, a ≤ c ∧ f c = b
#align pseudo_epimorphism_class PseudoEpimorphismClass

/-- `EsakiaHomClass F α β` states that `F` is a type of lattice morphisms.

You should extend this class when you extend `EsakiaHom`. -/
class EsakiaHomClass (F : Type*) (α β : outParam Type*) [TopologicalSpace α] [Preorder α]
    [TopologicalSpace β] [Preorder β] [FunLike F α β]
    extends ContinuousOrderHomClass F α β : Prop where
  exists_map_eq_of_map_le (f : F) ⦃a : α⦄ ⦃b : β⦄ : f a ≤ b → ∃ c, a ≤ c ∧ f c = b
#align esakia_hom_class EsakiaHomClass

end

export PseudoEpimorphismClass (exists_map_eq_of_map_le)

section Hom

variable [FunLike F α β]

-- See note [lower instance priority]
instance (priority := 100) PseudoEpimorphismClass.toTopHomClass [PartialOrder α] [OrderTop α]
    [Preorder β] [OrderTop β] [PseudoEpimorphismClass F α β] : TopHomClass F α β where
  map_top f := by
    let ⟨b, h⟩ := exists_map_eq_of_map_le f (@le_top _ _ _ <| f ⊤)
    rw [← top_le_iff.1 h.1, h.2]
#align pseudo_epimorphism_class.to_top_hom_class PseudoEpimorphismClass.toTopHomClass

-- See note [lower instance priority]
instance (priority := 100) EsakiaHomClass.toPseudoEpimorphismClass [TopologicalSpace α] [Preorder α]
    [TopologicalSpace β] [Preorder β] [EsakiaHomClass F α β] : PseudoEpimorphismClass F α β :=
  { ‹EsakiaHomClass F α β› with
    map_rel := ContinuousOrderHomClass.map_monotone }
#align esakia_hom_class.to_pseudo_epimorphism_class EsakiaHomClass.toPseudoEpimorphismClass

instance [Preorder α] [Preorder β] [PseudoEpimorphismClass F α β] :
    CoeTC F (PseudoEpimorphism α β) :=
  ⟨fun f => ⟨f, exists_map_eq_of_map_le f⟩⟩

instance [TopologicalSpace α] [Preorder α] [TopologicalSpace β] [Preorder β]
    [EsakiaHomClass F α β] : CoeTC F (EsakiaHom α β) :=
  ⟨fun f => ⟨f, exists_map_eq_of_map_le f⟩⟩

end Hom

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toPseudoEpimorphismClass [Preorder α] [Preorder β]
    [EquivLike F α β] [OrderIsoClass F α β] : PseudoEpimorphismClass F α β where
  exists_map_eq_of_map_le f _a b h :=
    ⟨EquivLike.inv f b, (le_map_inv_iff f).2 h, EquivLike.right_inv _ _⟩
#align order_iso_class.to_pseudo_epimorphism_class OrderIsoClass.toPseudoEpimorphismClass

/-! ### Pseudo-epimorphisms -/


namespace PseudoEpimorphism

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]

instance instFunLike : FunLike (PseudoEpimorphism α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

instance : PseudoEpimorphismClass (PseudoEpimorphism α β) α β where
  map_rel f _ _ h := f.monotone' h
  exists_map_eq_of_map_le := PseudoEpimorphism.exists_map_eq_of_map_le'

@[simp]
theorem toOrderHom_eq_coe (f : PseudoEpimorphism α β) : ⇑f.toOrderHom = f := rfl

theorem toFun_eq_coe {f : PseudoEpimorphism α β} : f.toFun = (f : α → β) := rfl
#align pseudo_epimorphism.to_fun_eq_coe PseudoEpimorphism.toFun_eq_coe

@[ext]
theorem ext {f g : PseudoEpimorphism α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
#align pseudo_epimorphism.ext PseudoEpimorphism.ext

/-- Copy of a `PseudoEpimorphism` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : PseudoEpimorphism α β) (f' : α → β) (h : f' = f) : PseudoEpimorphism α β :=
  ⟨f.toOrderHom.copy f' h, by simpa only [h.symm, toFun_eq_coe] using f.exists_map_eq_of_map_le'⟩
#align pseudo_epimorphism.copy PseudoEpimorphism.copy

@[simp]
theorem coe_copy (f : PseudoEpimorphism α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl
#align pseudo_epimorphism.coe_copy PseudoEpimorphism.coe_copy

theorem copy_eq (f : PseudoEpimorphism α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
#align pseudo_epimorphism.copy_eq PseudoEpimorphism.copy_eq

variable (α)

/-- `id` as a `PseudoEpimorphism`. -/
protected def id : PseudoEpimorphism α α :=
  ⟨OrderHom.id, fun _ b h => ⟨b, h, rfl⟩⟩
#align pseudo_epimorphism.id PseudoEpimorphism.id

instance : Inhabited (PseudoEpimorphism α α) :=
  ⟨PseudoEpimorphism.id α⟩

@[simp]
theorem coe_id : ⇑(PseudoEpimorphism.id α) = id := rfl
#align pseudo_epimorphism.coe_id PseudoEpimorphism.coe_id

@[simp]
theorem coe_id_orderHom : (PseudoEpimorphism.id α : α →o α) = OrderHom.id := rfl
#align pseudo_epimorphism.coe_id_order_hom PseudoEpimorphism.coe_id_orderHom

variable {α}

@[simp]
theorem id_apply (a : α) : PseudoEpimorphism.id α a = a := rfl
#align pseudo_epimorphism.id_apply PseudoEpimorphism.id_apply

/-- Composition of `PseudoEpimorphism`s as a `PseudoEpimorphism`. -/
def comp (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) : PseudoEpimorphism α γ :=
  ⟨g.toOrderHom.comp f.toOrderHom, fun a b h₀ => by
    obtain ⟨b, h₁, rfl⟩ := g.exists_map_eq_of_map_le' h₀
    obtain ⟨b, h₂, rfl⟩ := f.exists_map_eq_of_map_le' h₁
    exact ⟨b, h₂, rfl⟩⟩
#align pseudo_epimorphism.comp PseudoEpimorphism.comp

@[simp]
theorem coe_comp (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) :
    (g.comp f : α → γ) = g ∘ f := rfl
#align pseudo_epimorphism.coe_comp PseudoEpimorphism.coe_comp

@[simp]
theorem coe_comp_orderHom (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) :
    (g.comp f : α →o γ) = (g : β →o γ).comp f := rfl
#align pseudo_epimorphism.coe_comp_order_hom PseudoEpimorphism.coe_comp_orderHom

@[simp]
theorem comp_apply (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) (a : α) :
    (g.comp f) a = g (f a) := rfl
#align pseudo_epimorphism.comp_apply PseudoEpimorphism.comp_apply

@[simp]
theorem comp_assoc (h : PseudoEpimorphism γ δ) (g : PseudoEpimorphism β γ)
    (f : PseudoEpimorphism α β) : (h.comp g).comp f = h.comp (g.comp f) := rfl
#align pseudo_epimorphism.comp_assoc PseudoEpimorphism.comp_assoc

@[simp]
theorem comp_id (f : PseudoEpimorphism α β) : f.comp (PseudoEpimorphism.id α) = f :=
  ext fun _ => rfl
#align pseudo_epimorphism.comp_id PseudoEpimorphism.comp_id

@[simp]
theorem id_comp (f : PseudoEpimorphism α β) : (PseudoEpimorphism.id β).comp f = f :=
  ext fun _ => rfl
#align pseudo_epimorphism.id_comp PseudoEpimorphism.id_comp

@[simp]
theorem cancel_right {g₁ g₂ : PseudoEpimorphism β γ} {f : PseudoEpimorphism α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (comp · f)⟩
#align pseudo_epimorphism.cancel_right PseudoEpimorphism.cancel_right

@[simp]
theorem cancel_left {g : PseudoEpimorphism β γ} {f₁ f₂ : PseudoEpimorphism α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align pseudo_epimorphism.cancel_left PseudoEpimorphism.cancel_left

end PseudoEpimorphism

/-! ### Esakia morphisms -/


namespace EsakiaHom

variable [TopologicalSpace α] [Preorder α] [TopologicalSpace β] [Preorder β] [TopologicalSpace γ]
  [Preorder γ] [TopologicalSpace δ] [Preorder δ]

def toPseudoEpimorphism (f : EsakiaHom α β) : PseudoEpimorphism α β :=
  { f with }
#align esakia_hom.to_pseudo_epimorphism EsakiaHom.toPseudoEpimorphism

instance instFunLike : FunLike (EsakiaHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr

instance : EsakiaHomClass (EsakiaHom α β) α β where
  map_monotone f := f.monotone'
  map_continuous f := f.continuous_toFun
  exists_map_eq_of_map_le f := f.exists_map_eq_of_map_le'

-- Porting note: introduced this to appease simpNF linter with `toFun_eq_coe`
@[simp]
theorem toContinuousOrderHom_coe {f : EsakiaHom α β} :
    f.toContinuousOrderHom = (f : α → β) := rfl

-- Porting note: removed simp attribute as simp now solves this
theorem toFun_eq_coe {f : EsakiaHom α β} : f.toFun = (f : α → β) := rfl
#align esakia_hom.to_fun_eq_coe EsakiaHom.toFun_eq_coe

@[ext]
theorem ext {f g : EsakiaHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
#align esakia_hom.ext EsakiaHom.ext

/-- Copy of an `EsakiaHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : EsakiaHom α β) (f' : α → β) (h : f' = f) : EsakiaHom α β :=
  ⟨f.toContinuousOrderHom.copy f' h, by
    simpa only [h.symm, toFun_eq_coe] using f.exists_map_eq_of_map_le'⟩
#align esakia_hom.copy EsakiaHom.copy

@[simp]
theorem coe_copy (f : EsakiaHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl
#align esakia_hom.coe_copy EsakiaHom.coe_copy

theorem copy_eq (f : EsakiaHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
#align esakia_hom.copy_eq EsakiaHom.copy_eq

variable (α)

/-- `id` as an `EsakiaHom`. -/
protected def id : EsakiaHom α α :=
  ⟨ContinuousOrderHom.id α, fun _ b h => ⟨b, h, rfl⟩⟩
#align esakia_hom.id EsakiaHom.id

instance : Inhabited (EsakiaHom α α) :=
  ⟨EsakiaHom.id α⟩

@[simp]
theorem coe_id : ⇑(EsakiaHom.id α) = id := rfl
#align esakia_hom.coe_id EsakiaHom.coe_id

@[simp]
theorem coe_id_pseudoEpimorphism :
    (EsakiaHom.id α : PseudoEpimorphism α α) = PseudoEpimorphism.id α := rfl
#align esakia_hom.coe_id_pseudo_epimorphism EsakiaHom.coe_id_pseudoEpimorphism

variable {α}

@[simp]
theorem id_apply (a : α) : EsakiaHom.id α a = a := rfl
#align esakia_hom.id_apply EsakiaHom.id_apply

@[simp]
theorem coe_id_continuousOrderHom : (EsakiaHom.id α : α →Co α) = ContinuousOrderHom.id α := rfl
#align esakia_hom.coe_id_continuous_order_hom EsakiaHom.coe_id_continuousOrderHom

/-- Composition of `EsakiaHom`s as an `EsakiaHom`. -/
def comp (g : EsakiaHom β γ) (f : EsakiaHom α β) : EsakiaHom α γ :=
  ⟨g.toContinuousOrderHom.comp f.toContinuousOrderHom, fun a b h₀ => by
    obtain ⟨b, h₁, rfl⟩ := g.exists_map_eq_of_map_le' h₀
    obtain ⟨b, h₂, rfl⟩ := f.exists_map_eq_of_map_le' h₁
    exact ⟨b, h₂, rfl⟩⟩
#align esakia_hom.comp EsakiaHom.comp

@[simp]
theorem coe_comp_continuousOrderHom (g : EsakiaHom β γ) (f : EsakiaHom α β) :
    (g.comp f : α →Co γ) = (g: β →Co γ).comp f := rfl
#align esakia_hom.coe_comp_continuous_order_hom EsakiaHom.coe_comp_continuousOrderHom

@[simp]
theorem coe_comp_pseudoEpimorphism (g : EsakiaHom β γ) (f : EsakiaHom α β) :
    (g.comp f : PseudoEpimorphism α γ) = (g : PseudoEpimorphism β γ).comp f := rfl
#align esakia_hom.coe_comp_pseudo_epimorphism EsakiaHom.coe_comp_pseudoEpimorphism

@[simp]
theorem coe_comp (g : EsakiaHom β γ) (f : EsakiaHom α β) : (g.comp f : α → γ) = g ∘ f := rfl
#align esakia_hom.coe_comp EsakiaHom.coe_comp

@[simp]
theorem comp_apply (g : EsakiaHom β γ) (f : EsakiaHom α β) (a : α) : (g.comp f) a = g (f a) := rfl
#align esakia_hom.comp_apply EsakiaHom.comp_apply

@[simp]
theorem comp_assoc (h : EsakiaHom γ δ) (g : EsakiaHom β γ) (f : EsakiaHom α β) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl
#align esakia_hom.comp_assoc EsakiaHom.comp_assoc

@[simp]
theorem comp_id (f : EsakiaHom α β) : f.comp (EsakiaHom.id α) = f :=
  ext fun _ => rfl
#align esakia_hom.comp_id EsakiaHom.comp_id

@[simp]
theorem id_comp (f : EsakiaHom α β) : (EsakiaHom.id β).comp f = f :=
  ext fun _ => rfl
#align esakia_hom.id_comp EsakiaHom.id_comp

@[simp]
theorem cancel_right {g₁ g₂ : EsakiaHom β γ} {f : EsakiaHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (comp · f)⟩
#align esakia_hom.cancel_right EsakiaHom.cancel_right

@[simp]
theorem cancel_left {g : EsakiaHom β γ} {f₁ f₂ : EsakiaHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align esakia_hom.cancel_left EsakiaHom.cancel_left

end EsakiaHom
