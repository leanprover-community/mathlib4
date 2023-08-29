/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Hom.Bounded
import Mathlib.Order.SymmDiff

#align_import order.hom.lattice from "leanprover-community/mathlib"@"7581030920af3dcb241d1df0e36f6ec8289dd6be"

/-!
# Lattice homomorphisms

This file defines (bounded) lattice homomorphisms.

We use the `FunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `SupHom`: Maps which preserve `⊔`.
* `InfHom`: Maps which preserve `⊓`.
* `SupBotHom`: Finitary supremum homomorphisms. Maps which preserve `⊔` and `⊥`.
* `InfTopHom`: Finitary infimum homomorphisms. Maps which preserve `⊓` and `⊤`.
* `LatticeHom`: Lattice homomorphisms. Maps which preserve `⊔` and `⊓`.
* `BoundedLatticeHom`: Bounded lattice homomorphisms. Maps which preserve `⊤`, `⊥`, `⊔` and `⊓`.

## Typeclasses

* `SupHomClass`
* `InfHomClass`
* `SupBotHomClass`
* `InfTopHomClass`
* `LatticeHomClass`
* `BoundedLatticeHomClass`

## TODO

Do we need more intersections between `BotHom`, `TopHom` and lattice homomorphisms?
-/


open Function OrderDual

variable {F ι α β γ δ : Type*}

/-- The type of `⊔`-preserving functions from `α` to `β`. -/
structure SupHom (α β : Type*) [Sup α] [Sup β] where
  /-- The underlying function of a `SupHom` -/
  toFun : α → β
  /-- A `SupHom` preserves suprema. -/
  map_sup' (a b : α) : toFun (a ⊔ b) = toFun a ⊔ toFun b
#align sup_hom SupHom

/-- The type of `⊓`-preserving functions from `α` to `β`. -/
structure InfHom (α β : Type*) [Inf α] [Inf β] where
  /-- The underlying function of an `InfHom` -/
  toFun : α → β
  /-- An `InfHom` preserves infima. -/
  map_inf' (a b : α) : toFun (a ⊓ b) = toFun a ⊓ toFun b
#align inf_hom InfHom

/-- The type of finitary supremum-preserving homomorphisms from `α` to `β`. -/
structure SupBotHom (α β : Type*) [Sup α] [Sup β] [Bot α] [Bot β] extends SupHom α β where
  /-- A `SupBotHom` preserves the bottom element. -/
  map_bot' : toFun ⊥ = ⊥
#align sup_bot_hom SupBotHom

/-- The type of finitary infimum-preserving homomorphisms from `α` to `β`. -/
structure InfTopHom (α β : Type*) [Inf α] [Inf β] [Top α] [Top β] extends InfHom α β where
  /-- An `InfTopHom` preserves the top element. -/
  map_top' : toFun ⊤ = ⊤
#align inf_top_hom InfTopHom

/-- The type of lattice homomorphisms from `α` to `β`. -/
structure LatticeHom (α β : Type*) [Lattice α] [Lattice β] extends SupHom α β where
  /-- A `LatticeHom` preserves infima. -/
  map_inf' (a b : α) : toFun (a ⊓ b) = toFun a ⊓ toFun b
#align lattice_hom LatticeHom

/-- The type of bounded lattice homomorphisms from `α` to `β`. -/
structure BoundedLatticeHom (α β : Type*) [Lattice α] [Lattice β] [BoundedOrder α]
  [BoundedOrder β] extends LatticeHom α β where
  /-- A `BoundedLatticeHom` preserves the top element. -/
  map_top' : toFun ⊤ = ⊤
  /-- A `BoundedLatticeHom` preserves the bottom element. -/
  map_bot' : toFun ⊥ = ⊥
#align bounded_lattice_hom BoundedLatticeHom

-- Porting note: todo: remove this configuration and use the default configuration.
-- We keep this to be consistent with Lean 3.
initialize_simps_projections SupBotHom (+toSupHom, -toFun)
initialize_simps_projections InfTopHom (+toInfHom, -toFun)
initialize_simps_projections LatticeHom (+toSupHom, -toFun)
initialize_simps_projections BoundedLatticeHom (+toLatticeHom, -toFun)

section

/-- `SupHomClass F α β` states that `F` is a type of `⊔`-preserving morphisms.

You should extend this class when you extend `SupHom`. -/
class SupHomClass (F : Type*) (α β : outParam <| Type*) [Sup α] [Sup β] extends
  FunLike F α fun _ => β where
  /-- A `SupHomClass` morphism preserves suprema. -/
  map_sup (f : F) (a b : α) : f (a ⊔ b) = f a ⊔ f b
#align sup_hom_class SupHomClass

/-- `InfHomClass F α β` states that `F` is a type of `⊓`-preserving morphisms.

You should extend this class when you extend `InfHom`. -/
class InfHomClass (F : Type*) (α β : outParam <| Type*) [Inf α] [Inf β] extends
  FunLike F α fun _ => β where
  /-- An `InfHomClass` morphism preserves infima. -/
  map_inf (f : F) (a b : α) : f (a ⊓ b) = f a ⊓ f b
#align inf_hom_class InfHomClass

/-- `SupBotHomClass F α β` states that `F` is a type of finitary supremum-preserving morphisms.

You should extend this class when you extend `SupBotHom`. -/
class SupBotHomClass (F : Type*) (α β : outParam <| Type*) [Sup α] [Sup β] [Bot α]
  [Bot β] extends SupHomClass F α β where
  /-- A `SupBotHomClass` morphism preserves the bottom element. -/
  map_bot (f : F) : f ⊥ = ⊥
#align sup_bot_hom_class SupBotHomClass

/-- `InfTopHomClass F α β` states that `F` is a type of finitary infimum-preserving morphisms.

You should extend this class when you extend `SupBotHom`. -/
class InfTopHomClass (F : Type*) (α β : outParam <| Type*) [Inf α] [Inf β] [Top α]
  [Top β] extends InfHomClass F α β where
  /-- An `InfTopHomClass` morphism preserves the top element. -/
  map_top (f : F) : f ⊤ = ⊤
#align inf_top_hom_class InfTopHomClass

/-- `LatticeHomClass F α β` states that `F` is a type of lattice morphisms.

You should extend this class when you extend `LatticeHom`. -/
class LatticeHomClass (F : Type*) (α β : outParam <| Type*) [Lattice α] [Lattice β] extends
  SupHomClass F α β where
  /-- A `LatticeHomClass` morphism preserves infima. -/
  map_inf (f : F) (a b : α) : f (a ⊓ b) = f a ⊓ f b
#align lattice_hom_class LatticeHomClass

/-- `BoundedLatticeHomClass F α β` states that `F` is a type of bounded lattice morphisms.

You should extend this class when you extend `BoundedLatticeHom`. -/
class BoundedLatticeHomClass (F : Type*) (α β : outParam <| Type*) [Lattice α] [Lattice β]
  [BoundedOrder α] [BoundedOrder β] extends LatticeHomClass F α β where
  /-- A `BoundedLatticeHomClass` morphism preserves the top element. -/
  map_top (f : F) : f ⊤ = ⊤
  /-- A `BoundedLatticeHomClass` morphism preserves the bottom element. -/
  map_bot (f : F) : f ⊥ = ⊥
#align bounded_lattice_hom_class BoundedLatticeHomClass

end

export SupHomClass (map_sup)

export InfHomClass (map_inf)

attribute [simp] map_top map_bot map_sup map_inf

-- porting note: changes to the typeclass inference system mean that we need to
-- make a lot of changes here, adding `outParams`, changing `[]`s into `{}` and
-- so on.
-- See note [lower instance priority]
instance (priority := 100) SupHomClass.toOrderHomClass [SemilatticeSup α] [SemilatticeSup β]
    [SupHomClass F α β] : OrderHomClass F α β :=
  { ‹SupHomClass F α β› with
    map_rel := fun f a b h => by rw [← sup_eq_right, ← map_sup, sup_eq_right.2 h] }
                                 -- 🎉 no goals
#align sup_hom_class.to_order_hom_class SupHomClass.toOrderHomClass

-- See note [lower instance priority]
instance (priority := 100) InfHomClass.toOrderHomClass [SemilatticeInf α] [SemilatticeInf β]
    [InfHomClass F α β] : OrderHomClass F α β :=
  { ‹InfHomClass F α β› with
    map_rel := fun f a b h => by rw [← inf_eq_left, ← map_inf, inf_eq_left.2 h] }
                                 -- 🎉 no goals
#align inf_hom_class.to_order_hom_class InfHomClass.toOrderHomClass

-- See note [lower instance priority]
instance (priority := 100) SupBotHomClass.toBotHomClass [Sup α] [Sup β] [Bot α]
    [Bot β] [SupBotHomClass F α β] : BotHomClass F α β :=
  { ‹SupBotHomClass F α β› with }
#align sup_bot_hom_class.to_bot_hom_class SupBotHomClass.toBotHomClass

-- See note [lower instance priority]
instance (priority := 100) InfTopHomClass.toTopHomClass [Inf α] [Inf β] [Top α]
    [Top β] [InfTopHomClass F α β] : TopHomClass F α β :=
  { ‹InfTopHomClass F α β› with }
#align inf_top_hom_class.to_top_hom_class InfTopHomClass.toTopHomClass

-- See note [lower instance priority]
instance (priority := 100) LatticeHomClass.toInfHomClass [Lattice α] [Lattice β]
    [LatticeHomClass F α β] : InfHomClass F α β :=
  { ‹LatticeHomClass F α β› with }
#align lattice_hom_class.to_inf_hom_class LatticeHomClass.toInfHomClass

-- See note [lower instance priority]
instance (priority := 100) BoundedLatticeHomClass.toSupBotHomClass [Lattice α] [Lattice β]
    [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
    SupBotHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with }
#align bounded_lattice_hom_class.to_sup_bot_hom_class BoundedLatticeHomClass.toSupBotHomClass

-- See note [lower instance priority]
instance (priority := 100) BoundedLatticeHomClass.toInfTopHomClass [Lattice α] [Lattice β]
    [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
    InfTopHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with }
#align bounded_lattice_hom_class.to_inf_top_hom_class BoundedLatticeHomClass.toInfTopHomClass

-- See note [lower instance priority]
instance (priority := 100) BoundedLatticeHomClass.toBoundedOrderHomClass [Lattice α]
    [Lattice β] [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
    BoundedOrderHomClass F α β :=
{ show OrderHomClass F α β from inferInstance, ‹BoundedLatticeHomClass F α β› with }
#align bounded_lattice_hom_class.to_bounded_order_hom_class BoundedLatticeHomClass.toBoundedOrderHomClass

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toSupHomClass [SemilatticeSup α] [SemilatticeSup β]
    [OrderIsoClass F α β] : SupHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_sup := fun f a b =>
      eq_of_forall_ge_iff fun c => by simp only [← le_map_inv_iff, sup_le_iff] }
                                      -- 🎉 no goals
#align order_iso_class.to_sup_hom_class OrderIsoClass.toSupHomClass


-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toInfHomClass [SemilatticeInf α] [SemilatticeInf β]
    [OrderIsoClass F α β] : InfHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_inf := fun f a b =>
      eq_of_forall_le_iff fun c => by simp only [← map_inv_le_iff, le_inf_iff] }
                                      -- 🎉 no goals
#align order_iso_class.to_inf_hom_class OrderIsoClass.toInfHomClass

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toSupBotHomClass [SemilatticeSup α] [OrderBot α]
    [SemilatticeSup β] [OrderBot β] [OrderIsoClass F α β] : SupBotHomClass F α β :=
  { OrderIsoClass.toSupHomClass, OrderIsoClass.toBotHomClass with }
#align order_iso_class.to_sup_bot_hom_class OrderIsoClass.toSupBotHomClass

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toInfTopHomClass [SemilatticeInf α] [OrderTop α]
    [SemilatticeInf β] [OrderTop β] [OrderIsoClass F α β] : InfTopHomClass F α β :=
  { OrderIsoClass.toInfHomClass, OrderIsoClass.toTopHomClass with }
#align order_iso_class.to_inf_top_hom_class OrderIsoClass.toInfTopHomClass

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toLatticeHomClass [Lattice α] [Lattice β]
    [OrderIsoClass F α β] : LatticeHomClass F α β :=
  { OrderIsoClass.toSupHomClass, OrderIsoClass.toInfHomClass with }
#align order_iso_class.to_lattice_hom_class OrderIsoClass.toLatticeHomClass

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toBoundedLatticeHomClass [Lattice α] [Lattice β]
    [BoundedOrder α] [BoundedOrder β] [OrderIsoClass F α β] :
    BoundedLatticeHomClass F α β :=
  { OrderIsoClass.toLatticeHomClass, OrderIsoClass.toBoundedOrderHomClass with }
#align order_iso_class.to_bounded_lattice_hom_class OrderIsoClass.toBoundedLatticeHomClass

section BoundedLattice

variable [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β] [BoundedLatticeHomClass F α β]
  (f : F) {a b : α}

theorem Disjoint.map (h : Disjoint a b) : Disjoint (f a) (f b) := by
  rw [disjoint_iff, ← map_inf, h.eq_bot, map_bot]
  -- 🎉 no goals
#align disjoint.map Disjoint.map

theorem Codisjoint.map (h : Codisjoint a b) : Codisjoint (f a) (f b) := by
  rw [codisjoint_iff, ← map_sup, h.eq_top, map_top]
  -- 🎉 no goals
#align codisjoint.map Codisjoint.map

theorem IsCompl.map (h : IsCompl a b) : IsCompl (f a) (f b) :=
  ⟨h.1.map _, h.2.map _⟩
#align is_compl.map IsCompl.map

end BoundedLattice

section BooleanAlgebra

variable [BooleanAlgebra α] [BooleanAlgebra β] [BoundedLatticeHomClass F α β] (f : F)

/-- Special case of `map_compl` for boolean algebras. -/
theorem map_compl' (a : α) : f aᶜ = (f a)ᶜ :=
  (isCompl_compl.map _).compl_eq.symm
#align map_compl' map_compl'

/-- Special case of `map_sdiff` for boolean algebras. -/
theorem map_sdiff' (a b : α) : f (a \ b) = f a \ f b := by
  rw [sdiff_eq, sdiff_eq, map_inf, map_compl']
  -- 🎉 no goals
#align map_sdiff' map_sdiff'

/-- Special case of `map_symmDiff` for boolean algebras. -/
theorem map_symmDiff' (a b : α) : f (a ∆ b) = f a ∆ f b := by
  rw [symmDiff, symmDiff, map_sup, map_sdiff', map_sdiff']
  -- 🎉 no goals
#align map_symm_diff' map_symmDiff'

end BooleanAlgebra

instance [Sup α] [Sup β] [SupHomClass F α β] : CoeTC F (SupHom α β) :=
  ⟨fun f => ⟨f, map_sup f⟩⟩

instance [Inf α] [Inf β] [InfHomClass F α β] : CoeTC F (InfHom α β) :=
  ⟨fun f => ⟨f, map_inf f⟩⟩

instance [Sup α] [Sup β] [Bot α] [Bot β] [SupBotHomClass F α β] : CoeTC F (SupBotHom α β) :=
  ⟨fun f => ⟨f, map_bot f⟩⟩

instance [Inf α] [Inf β] [Top α] [Top β] [InfTopHomClass F α β] : CoeTC F (InfTopHom α β) :=
  ⟨fun f => ⟨f, map_top f⟩⟩

instance [Lattice α] [Lattice β] [LatticeHomClass F α β] : CoeTC F (LatticeHom α β) :=
  ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f }⟩

instance [Lattice α] [Lattice β] [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
    CoeTC F (BoundedLatticeHom α β) :=
  ⟨fun f =>
    { (f : LatticeHom α β) with
      toFun := f
      map_top' := map_top f
      map_bot' := map_bot f }⟩

/-! ### Supremum homomorphisms -/

namespace SupHom

variable [Sup α]

section Sup

variable [Sup β] [Sup γ] [Sup δ]

instance : SupHomClass (SupHom α β) α β where
  coe := SupHom.toFun
  coe_injective' f g h := by cases f; cases g; congr
                             -- ⊢ { toFun := toFun✝, map_sup' := map_sup'✝ } = g
                                      -- ⊢ { toFun := toFun✝¹, map_sup' := map_sup'✝¹ } = { toFun := toFun✝, map_sup' : …
                                               -- 🎉 no goals
  map_sup := SupHom.map_sup'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
-- porting note: replaced `CoeFun` with `FunLike` so that we use `FunLike.coe` instead of `toFun`
instance : FunLike (SupHom α β) α fun _ => β :=
  SupHomClass.toFunLike

@[simp]
theorem toFun_eq_coe {f : SupHom α β} : f.toFun = (f : α → β) :=
  rfl
#align sup_hom.to_fun_eq_coe SupHom.toFun_eq_coe

@[ext]
theorem ext {f g : SupHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align sup_hom.ext SupHom.ext

/-- Copy of a `SupHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : SupHom α β) (f' : α → β) (h : f' = f) : SupHom α β where
  toFun := f'
  map_sup' := h.symm ▸ f.map_sup'
#align sup_hom.copy SupHom.copy

@[simp]
theorem coe_copy (f : SupHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align sup_hom.coe_copy SupHom.coe_copy

theorem copy_eq (f : SupHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align sup_hom.copy_eq SupHom.copy_eq

variable (α)

/-- `id` as a `SupHom`. -/
protected def id : SupHom α α :=
  ⟨id, fun _ _ => rfl⟩
#align sup_hom.id SupHom.id

instance : Inhabited (SupHom α α) :=
  ⟨SupHom.id α⟩

@[simp]
theorem coe_id : ⇑(SupHom.id α) = id :=
  rfl
#align sup_hom.coe_id SupHom.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : SupHom.id α a = a :=
  rfl
#align sup_hom.id_apply SupHom.id_apply

/-- Composition of `SupHom`s as a `SupHom`. -/
def comp (f : SupHom β γ) (g : SupHom α β) : SupHom α γ where
  toFun := f ∘ g
  map_sup' a b := by rw [comp_apply, map_sup, map_sup]; rfl
                     -- ⊢ ↑f (↑g a) ⊔ ↑f (↑g b) = (↑f ∘ ↑g) a ⊔ (↑f ∘ ↑g) b
                                                        -- 🎉 no goals
#align sup_hom.comp SupHom.comp

@[simp]
theorem coe_comp (f : SupHom β γ) (g : SupHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
#align sup_hom.coe_comp SupHom.coe_comp

@[simp]
theorem comp_apply (f : SupHom β γ) (g : SupHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align sup_hom.comp_apply SupHom.comp_apply

@[simp]
theorem comp_assoc (f : SupHom γ δ) (g : SupHom β γ) (h : SupHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align sup_hom.comp_assoc SupHom.comp_assoc

@[simp] theorem comp_id (f : SupHom α β) : f.comp (SupHom.id α) = f := rfl
#align sup_hom.comp_id SupHom.comp_id

@[simp] theorem id_comp (f : SupHom α β) : (SupHom.id β).comp f = f := rfl
#align sup_hom.id_comp SupHom.id_comp

theorem cancel_right {g₁ g₂ : SupHom β γ} {f : SupHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => SupHom.ext <| hf.forall.2 <| FunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩
#align sup_hom.cancel_right SupHom.cancel_right

theorem cancel_left {g : SupHom β γ} {f₁ f₂ : SupHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => SupHom.ext fun a => hg <| by rw [← SupHom.comp_apply, h, SupHom.comp_apply],
                                         -- 🎉 no goals
    congr_arg _⟩
#align sup_hom.cancel_left SupHom.cancel_left

end Sup

variable (α) [SemilatticeSup β]

/-- The constant function as a `SupHom`. -/
def const (b : β) : SupHom α β :=
  ⟨fun _ => b, fun _ _ => sup_idem.symm⟩
#align sup_hom.const SupHom.const

@[simp]
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl
#align sup_hom.coe_const SupHom.coe_const

@[simp]
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl
#align sup_hom.const_apply SupHom.const_apply

variable {α}

instance : Sup (SupHom α β) :=
  ⟨fun f g =>
    ⟨f ⊔ g, fun a b => by
      rw [Pi.sup_apply, map_sup, map_sup]
      -- ⊢ ↑f a ⊔ ↑f b ⊔ (↑g a ⊔ ↑g b) = (↑f ⊔ ↑g) a ⊔ (↑f ⊔ ↑g) b
      exact sup_sup_sup_comm _ _ _ _⟩⟩
      -- 🎉 no goals

instance : SemilatticeSup (SupHom α β) :=
  (FunLike.coe_injective.semilatticeSup _) fun _ _ => rfl

instance [Bot β] : Bot (SupHom α β) :=
  ⟨SupHom.const α ⊥⟩

instance [Top β] : Top (SupHom α β) :=
  ⟨SupHom.const α ⊤⟩

instance [OrderBot β] : OrderBot (SupHom α β) :=
  OrderBot.lift ((↑) : _ → α → β) (fun _ _ => id) rfl

instance [OrderTop β] : OrderTop (SupHom α β) :=
  OrderTop.lift ((↑) : _ → α → β) (fun _ _ => id) rfl

instance [BoundedOrder β] : BoundedOrder (SupHom α β) :=
  BoundedOrder.lift ((↑) : _ → α → β) (fun _ _ => id) rfl rfl

@[simp]
theorem coe_sup (f g : SupHom α β) : FunLike.coe (f ⊔ g) = f ⊔ g :=
  rfl
#align sup_hom.coe_sup SupHom.coe_sup

@[simp]
theorem coe_bot [Bot β] : ⇑(⊥ : SupHom α β) = ⊥ :=
  rfl
#align sup_hom.coe_bot SupHom.coe_bot

@[simp]
theorem coe_top [Top β] : ⇑(⊤ : SupHom α β) = ⊤ :=
  rfl
#align sup_hom.coe_top SupHom.coe_top

@[simp]
theorem sup_apply (f g : SupHom α β) (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl
#align sup_hom.sup_apply SupHom.sup_apply

@[simp]
theorem bot_apply [Bot β] (a : α) : (⊥ : SupHom α β) a = ⊥ :=
  rfl
#align sup_hom.bot_apply SupHom.bot_apply

@[simp]
theorem top_apply [Top β] (a : α) : (⊤ : SupHom α β) a = ⊤ :=
  rfl
#align sup_hom.top_apply SupHom.top_apply

end SupHom

/-! ### Infimum homomorphisms -/


namespace InfHom

variable [Inf α]

section Inf

variable [Inf β] [Inf γ] [Inf δ]

instance : InfHomClass (InfHom α β) α β where
  coe := InfHom.toFun
  coe_injective' f g h := by cases f; cases g; congr
                             -- ⊢ { toFun := toFun✝, map_inf' := map_inf'✝ } = g
                                      -- ⊢ { toFun := toFun✝¹, map_inf' := map_inf'✝¹ } = { toFun := toFun✝, map_inf' : …
                                               -- 🎉 no goals
  map_inf := InfHom.map_inf'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : FunLike (InfHom α β) α fun _ => β :=
  InfHomClass.toFunLike

@[simp]
theorem toFun_eq_coe {f : InfHom α β} : f.toFun = (f : α → β) :=
  rfl
#align inf_hom.to_fun_eq_coe InfHom.toFun_eq_coe

@[ext]
theorem ext {f g : InfHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align inf_hom.ext InfHom.ext

/-- Copy of an `InfHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : InfHom α β) (f' : α → β) (h : f' = f) : InfHom α β
    where
  toFun := f'
  map_inf' := h.symm ▸ f.map_inf'
#align inf_hom.copy InfHom.copy

@[simp]
theorem coe_copy (f : InfHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align inf_hom.coe_copy InfHom.coe_copy

theorem copy_eq (f : InfHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align inf_hom.copy_eq InfHom.copy_eq

variable (α)

/-- `id` as an `InfHom`. -/
protected def id : InfHom α α :=
  ⟨id, fun _ _ => rfl⟩
#align inf_hom.id InfHom.id

instance : Inhabited (InfHom α α) :=
  ⟨InfHom.id α⟩

@[simp]
theorem coe_id : ⇑(InfHom.id α) = id :=
  rfl
#align inf_hom.coe_id InfHom.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : InfHom.id α a = a :=
  rfl
#align inf_hom.id_apply InfHom.id_apply

/-- Composition of `InfHom`s as an `InfHom`. -/
def comp (f : InfHom β γ) (g : InfHom α β) : InfHom α γ where
  toFun := f ∘ g
  map_inf' a b := by rw [comp_apply, map_inf, map_inf]; rfl
                     -- ⊢ ↑f (↑g a) ⊓ ↑f (↑g b) = (↑f ∘ ↑g) a ⊓ (↑f ∘ ↑g) b
                                                        -- 🎉 no goals
#align inf_hom.comp InfHom.comp

@[simp]
theorem coe_comp (f : InfHom β γ) (g : InfHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
#align inf_hom.coe_comp InfHom.coe_comp

@[simp]
theorem comp_apply (f : InfHom β γ) (g : InfHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align inf_hom.comp_apply InfHom.comp_apply

@[simp]
theorem comp_assoc (f : InfHom γ δ) (g : InfHom β γ) (h : InfHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align inf_hom.comp_assoc InfHom.comp_assoc

@[simp] theorem comp_id (f : InfHom α β) : f.comp (InfHom.id α) = f := rfl
#align inf_hom.comp_id InfHom.comp_id

@[simp] theorem id_comp (f : InfHom α β) : (InfHom.id β).comp f = f := rfl
#align inf_hom.id_comp InfHom.id_comp

theorem cancel_right {g₁ g₂ : InfHom β γ} {f : InfHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => InfHom.ext <| hf.forall.2 <| FunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩
#align inf_hom.cancel_right InfHom.cancel_right

theorem cancel_left {g : InfHom β γ} {f₁ f₂ : InfHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => InfHom.ext fun a => hg <| by rw [← InfHom.comp_apply, h, InfHom.comp_apply],
                                         -- 🎉 no goals
    congr_arg _⟩
#align inf_hom.cancel_left InfHom.cancel_left

end Inf

variable (α) [SemilatticeInf β]

/-- The constant function as an `InfHom`. -/
def const (b : β) : InfHom α β :=
  ⟨fun _ => b, fun _ _ => inf_idem.symm⟩
#align inf_hom.const InfHom.const

@[simp]
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl
#align inf_hom.coe_const InfHom.coe_const

@[simp]
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl
#align inf_hom.const_apply InfHom.const_apply

variable {α}

instance : Inf (InfHom α β) :=
  ⟨fun f g =>
    ⟨f ⊓ g, fun a b => by
      rw [Pi.inf_apply, map_inf, map_inf]
      -- ⊢ ↑f a ⊓ ↑f b ⊓ (↑g a ⊓ ↑g b) = (↑f ⊓ ↑g) a ⊓ (↑f ⊓ ↑g) b
      exact inf_inf_inf_comm _ _ _ _⟩⟩
      -- 🎉 no goals

instance : SemilatticeInf (InfHom α β) :=
  (FunLike.coe_injective.semilatticeInf _) fun _ _ => rfl

instance [Bot β] : Bot (InfHom α β) :=
  ⟨InfHom.const α ⊥⟩

instance [Top β] : Top (InfHom α β) :=
  ⟨InfHom.const α ⊤⟩

instance [OrderBot β] : OrderBot (InfHom α β) :=
  OrderBot.lift ((↑) : _ → α → β) (fun _ _ => id) rfl

instance [OrderTop β] : OrderTop (InfHom α β) :=
  OrderTop.lift ((↑) : _ → α → β) (fun _ _ => id) rfl

instance [BoundedOrder β] : BoundedOrder (InfHom α β) :=
  BoundedOrder.lift ((↑) : _ → α → β) (fun _ _ => id) rfl rfl

@[simp]
theorem coe_inf (f g : InfHom α β) : FunLike.coe (f ⊓ g) = f ⊓ g :=
  rfl
#align inf_hom.coe_inf InfHom.coe_inf

@[simp]
theorem coe_bot [Bot β] : ⇑(⊥ : InfHom α β) = ⊥ :=
  rfl
#align inf_hom.coe_bot InfHom.coe_bot

@[simp]
theorem coe_top [Top β] : ⇑(⊤ : InfHom α β) = ⊤ :=
  rfl
#align inf_hom.coe_top InfHom.coe_top

@[simp]
theorem inf_apply (f g : InfHom α β) (a : α) : (f ⊓ g) a = f a ⊓ g a :=
  rfl
#align inf_hom.inf_apply InfHom.inf_apply

@[simp]
theorem bot_apply [Bot β] (a : α) : (⊥ : InfHom α β) a = ⊥ :=
  rfl
#align inf_hom.bot_apply InfHom.bot_apply

@[simp]
theorem top_apply [Top β] (a : α) : (⊤ : InfHom α β) a = ⊤ :=
  rfl
#align inf_hom.top_apply InfHom.top_apply

end InfHom

/-! ### Finitary supremum homomorphisms -/

namespace SupBotHom

variable [Sup α] [Bot α]

section Sup

variable [Sup β] [Bot β] [Sup γ] [Bot γ] [Sup δ] [Bot δ]

/-- Reinterpret a `SupBotHom` as a `BotHom`. -/
def toBotHom (f : SupBotHom α β) : BotHom α β :=
  { f with }
#align sup_bot_hom.to_bot_hom SupBotHom.toBotHom

instance : SupBotHomClass (SupBotHom α β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    -- ⊢ { toSupHom := { toFun := toFun✝, map_sup' := map_sup'✝ }, map_bot' := map_bo …
    obtain ⟨⟨_, _⟩, _⟩ := g
    -- ⊢ { toSupHom := { toFun := toFun✝¹, map_sup' := map_sup'✝¹ }, map_bot' := map_ …
    congr
    -- 🎉 no goals
  map_sup f := f.map_sup'
  map_bot f := f.map_bot'

-- porting note: replaced `CoeFun` instance with `FunLike` instance
instance : FunLike (SupBotHom α β) α fun _ => β :=
  SupHomClass.toFunLike

-- porting note: this is the `simp`-normal version of `toFun_eq_coe`
@[simp]
theorem coe_toSupHom {f : SupBotHom α β} : (f.toSupHom : α → β) = (f : α → β) :=
  rfl

-- porting note: adding this since we also added `coe_toSupHom`
@[simp]
theorem coe_toBotHom {f : SupBotHom α β} : (f.toBotHom : α → β) = (f : α → β) :=
  rfl

theorem toFun_eq_coe {f : SupBotHom α β} : f.toFun = (f : α → β) :=
  rfl
#align sup_bot_hom.to_fun_eq_coe SupBotHom.toFun_eq_coe

@[ext]
theorem ext {f g : SupBotHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align sup_bot_hom.ext SupBotHom.ext

/-- Copy of a `SupBotHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : SupBotHom α β) (f' : α → β) (h : f' = f) : SupBotHom α β :=
  { f.toBotHom.copy f' h with toSupHom := f.toSupHom.copy f' h }
#align sup_bot_hom.copy SupBotHom.copy

@[simp]
theorem coe_copy (f : SupBotHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align sup_bot_hom.coe_copy SupBotHom.coe_copy

theorem copy_eq (f : SupBotHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align sup_bot_hom.copy_eq SupBotHom.copy_eq

variable (α)

/-- `id` as a `SupBotHom`. -/
@[simps]
protected def id : SupBotHom α α :=
  ⟨SupHom.id α, rfl⟩
#align sup_bot_hom.id SupBotHom.id

instance : Inhabited (SupBotHom α α) :=
  ⟨SupBotHom.id α⟩

@[simp]
theorem coe_id : ⇑(SupBotHom.id α) = id :=
  rfl
#align sup_bot_hom.coe_id SupBotHom.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : SupBotHom.id α a = a :=
  rfl
#align sup_bot_hom.id_apply SupBotHom.id_apply

/-- Composition of `SupBotHom`s as a `SupBotHom`. -/
def comp (f : SupBotHom β γ) (g : SupBotHom α β) : SupBotHom α γ :=
  { f.toSupHom.comp g.toSupHom, f.toBotHom.comp g.toBotHom with }
#align sup_bot_hom.comp SupBotHom.comp

@[simp]
theorem coe_comp (f : SupBotHom β γ) (g : SupBotHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
#align sup_bot_hom.coe_comp SupBotHom.coe_comp

@[simp]
theorem comp_apply (f : SupBotHom β γ) (g : SupBotHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align sup_bot_hom.comp_apply SupBotHom.comp_apply

@[simp]
theorem comp_assoc (f : SupBotHom γ δ) (g : SupBotHom β γ) (h : SupBotHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align sup_bot_hom.comp_assoc SupBotHom.comp_assoc

@[simp] theorem comp_id (f : SupBotHom α β) : f.comp (SupBotHom.id α) = f := rfl
#align sup_bot_hom.comp_id SupBotHom.comp_id

@[simp] theorem id_comp (f : SupBotHom α β) : (SupBotHom.id β).comp f = f := rfl
#align sup_bot_hom.id_comp SupBotHom.id_comp

theorem cancel_right {g₁ g₂ : SupBotHom β γ} {f : SupBotHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩
#align sup_bot_hom.cancel_right SupBotHom.cancel_right

theorem cancel_left {g : SupBotHom β γ} {f₁ f₂ : SupBotHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => SupBotHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
                                            -- 🎉 no goals
#align sup_bot_hom.cancel_left SupBotHom.cancel_left

end Sup

variable [SemilatticeSup β] [OrderBot β]

instance : Sup (SupBotHom α β) :=
  ⟨fun f g => { f.toBotHom ⊔ g.toBotHom with toSupHom := f.toSupHom ⊔ g.toSupHom }⟩

instance : SemilatticeSup (SupBotHom α β) :=
  (FunLike.coe_injective.semilatticeSup _) fun _ _ => rfl

instance : OrderBot (SupBotHom α β) where
  bot := ⟨⊥, rfl⟩
  bot_le _ _ := bot_le

@[simp]
theorem coe_sup (f g : SupBotHom α β) : FunLike.coe (f ⊔ g) = f ⊔ g :=
  rfl
#align sup_bot_hom.coe_sup SupBotHom.coe_sup

@[simp]
theorem coe_bot : ⇑(⊥ : SupBotHom α β) = ⊥ :=
  rfl
#align sup_bot_hom.coe_bot SupBotHom.coe_bot

@[simp]
theorem sup_apply (f g : SupBotHom α β) (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl
#align sup_bot_hom.sup_apply SupBotHom.sup_apply

@[simp]
theorem bot_apply (a : α) : (⊥ : SupBotHom α β) a = ⊥ :=
  rfl
#align sup_bot_hom.bot_apply SupBotHom.bot_apply

end SupBotHom

/-! ### Finitary infimum homomorphisms -/


namespace InfTopHom

variable [Inf α] [Top α]

section Inf

variable [Inf β] [Top β] [Inf γ] [Top γ] [Inf δ] [Top δ]

/-- Reinterpret an `InfTopHom` as a `TopHom`. -/
def toTopHom (f : InfTopHom α β) : TopHom α β :=
  { f with }
#align inf_top_hom.to_top_hom InfTopHom.toTopHom

instance : InfTopHomClass (InfTopHom α β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    -- ⊢ { toInfHom := { toFun := toFun✝, map_inf' := map_inf'✝ }, map_top' := map_to …
    obtain ⟨⟨_, _⟩, _⟩ := g
    -- ⊢ { toInfHom := { toFun := toFun✝¹, map_inf' := map_inf'✝¹ }, map_top' := map_ …
    congr
    -- 🎉 no goals
  map_inf f := f.map_inf'
  map_top f := f.map_top'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : FunLike (InfTopHom α β) α fun _ => β :=
  InfHomClass.toFunLike

-- porting note: this is the `simp`-normal version of `toFun_eq_coe`
@[simp]
theorem coe_toInfHom {f : InfTopHom α β} : (f.toInfHom : α → β) = (f : α → β) :=
  rfl

-- porting note: adding this since we also added `coe_toInfHom`
@[simp]
theorem coe_toTopHom {f : InfTopHom α β} : (f.toTopHom : α → β) = (f : α → β) :=
  rfl

theorem toFun_eq_coe {f : InfTopHom α β} : f.toFun = (f : α → β) := rfl
#align inf_top_hom.to_fun_eq_coe InfTopHom.toFun_eq_coe

@[ext]
theorem ext {f g : InfTopHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align inf_top_hom.ext InfTopHom.ext

/-- Copy of an `InfTopHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : InfTopHom α β) (f' : α → β) (h : f' = f) : InfTopHom α β :=
  { f.toTopHom.copy f' h with toInfHom := f.toInfHom.copy f' h }
#align inf_top_hom.copy InfTopHom.copy

@[simp]
theorem coe_copy (f : InfTopHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align inf_top_hom.coe_copy InfTopHom.coe_copy

theorem copy_eq (f : InfTopHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align inf_top_hom.copy_eq InfTopHom.copy_eq

variable (α)

/-- `id` as an `InfTopHom`. -/
@[simps]
protected def id : InfTopHom α α :=
  ⟨InfHom.id α, rfl⟩
#align inf_top_hom.id InfTopHom.id

instance : Inhabited (InfTopHom α α) :=
  ⟨InfTopHom.id α⟩

@[simp]
theorem coe_id : ⇑(InfTopHom.id α) = id :=
  rfl
#align inf_top_hom.coe_id InfTopHom.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : InfTopHom.id α a = a :=
  rfl
#align inf_top_hom.id_apply InfTopHom.id_apply

/-- Composition of `InfTopHom`s as an `InfTopHom`. -/
def comp (f : InfTopHom β γ) (g : InfTopHom α β) : InfTopHom α γ :=
  { f.toInfHom.comp g.toInfHom, f.toTopHom.comp g.toTopHom with }
#align inf_top_hom.comp InfTopHom.comp

@[simp]
theorem coe_comp (f : InfTopHom β γ) (g : InfTopHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
#align inf_top_hom.coe_comp InfTopHom.coe_comp

@[simp]
theorem comp_apply (f : InfTopHom β γ) (g : InfTopHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align inf_top_hom.comp_apply InfTopHom.comp_apply

@[simp]
theorem comp_assoc (f : InfTopHom γ δ) (g : InfTopHom β γ) (h : InfTopHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align inf_top_hom.comp_assoc InfTopHom.comp_assoc

@[simp] theorem comp_id (f : InfTopHom α β) : f.comp (InfTopHom.id α) = f := rfl
#align inf_top_hom.comp_id InfTopHom.comp_id

@[simp] theorem id_comp (f : InfTopHom α β) : (InfTopHom.id β).comp f = f := rfl
#align inf_top_hom.id_comp InfTopHom.id_comp

theorem cancel_right {g₁ g₂ : InfTopHom β γ} {f : InfTopHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩
#align inf_top_hom.cancel_right InfTopHom.cancel_right

theorem cancel_left {g : InfTopHom β γ} {f₁ f₂ : InfTopHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => InfTopHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
                                            -- 🎉 no goals
#align inf_top_hom.cancel_left InfTopHom.cancel_left

end Inf

variable [SemilatticeInf β] [OrderTop β]

instance : Inf (InfTopHom α β) :=
  ⟨fun f g => { f.toTopHom ⊓ g.toTopHom with toInfHom := f.toInfHom ⊓ g.toInfHom }⟩

instance : SemilatticeInf (InfTopHom α β) :=
  (FunLike.coe_injective.semilatticeInf _) fun _ _ => rfl

instance : OrderTop (InfTopHom α β) where
  top := ⟨⊤, rfl⟩
  le_top _ _ := le_top

@[simp]
theorem coe_inf (f g : InfTopHom α β) : FunLike.coe (f ⊓ g) = f ⊓ g :=
  rfl
#align inf_top_hom.coe_inf InfTopHom.coe_inf

@[simp]
theorem coe_top : ⇑(⊤ : InfTopHom α β) = ⊤ :=
  rfl
#align inf_top_hom.coe_top InfTopHom.coe_top

@[simp]
theorem inf_apply (f g : InfTopHom α β) (a : α) : (f ⊓ g) a = f a ⊓ g a :=
  rfl
#align inf_top_hom.inf_apply InfTopHom.inf_apply

@[simp]
theorem top_apply (a : α) : (⊤ : InfTopHom α β) a = ⊤ :=
  rfl
#align inf_top_hom.top_apply InfTopHom.top_apply

end InfTopHom

/-! ### Lattice homomorphisms -/


namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ] [Lattice δ]

/-- Reinterpret a `LatticeHom` as an `InfHom`. -/
def toInfHom (f : LatticeHom α β) : InfHom α β :=
  { f with }
#align lattice_hom.to_inf_hom LatticeHom.toInfHom

instance : LatticeHomClass (LatticeHom α β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr
                             -- ⊢ { toSupHom := { toFun := toFun✝, map_sup' := map_sup'✝ }, map_inf' := map_in …
                                                      -- ⊢ { toSupHom := { toFun := toFun✝¹, map_sup' := map_sup'✝¹ }, map_inf' := map_ …
                                                                               -- 🎉 no goals
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : FunLike (LatticeHom α β) α fun _ => β :=
  SupHomClass.toFunLike

-- porting note: this is the `simp`-normal version of `toFun_eq_coe`
@[simp]
theorem coe_toSupHom {f : LatticeHom α β} : (f.toSupHom : α → β) = (f : α → β) :=
  rfl

-- porting note: adding this since we also added `coe_toSupHom`
@[simp]
theorem coe_toInfHom {f : LatticeHom α β} : (f.toInfHom : α → β) = (f : α → β) :=
  rfl

theorem toFun_eq_coe {f : LatticeHom α β} : f.toFun = (f : α → β) := rfl
#align lattice_hom.to_fun_eq_coe LatticeHom.toFun_eq_coe

@[ext]
theorem ext {f g : LatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align lattice_hom.ext LatticeHom.ext

/-- Copy of a `LatticeHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : LatticeHom α β) (f' : α → β) (h : f' = f) : LatticeHom α β :=
  { f.toSupHom.copy f' h, f.toInfHom.copy f' h with }
#align lattice_hom.copy LatticeHom.copy

@[simp]
theorem coe_copy (f : LatticeHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align lattice_hom.coe_copy LatticeHom.coe_copy

theorem copy_eq (f : LatticeHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align lattice_hom.copy_eq LatticeHom.copy_eq

variable (α)

/-- `id` as a `LatticeHom`. -/
protected def id : LatticeHom α α where
  toFun := id
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
#align lattice_hom.id LatticeHom.id

instance : Inhabited (LatticeHom α α) :=
  ⟨LatticeHom.id α⟩

@[simp]
theorem coe_id : ⇑(LatticeHom.id α) = id :=
  rfl
#align lattice_hom.coe_id LatticeHom.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : LatticeHom.id α a = a :=
  rfl
#align lattice_hom.id_apply LatticeHom.id_apply

/-- Composition of `LatticeHom`s as a `LatticeHom`. -/
def comp (f : LatticeHom β γ) (g : LatticeHom α β) : LatticeHom α γ :=
  { f.toSupHom.comp g.toSupHom, f.toInfHom.comp g.toInfHom with }
#align lattice_hom.comp LatticeHom.comp

@[simp]
theorem coe_comp (f : LatticeHom β γ) (g : LatticeHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
#align lattice_hom.coe_comp LatticeHom.coe_comp

@[simp]
theorem comp_apply (f : LatticeHom β γ) (g : LatticeHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align lattice_hom.comp_apply LatticeHom.comp_apply

@[simp]
-- porting note: `simp`-normal form of `coe_comp_sup_hom`
theorem coe_comp_sup_hom' (f : LatticeHom β γ) (g : LatticeHom α β) :
    ⟨f ∘ g, map_sup (f.comp g)⟩ = (f : SupHom β γ).comp g :=
  rfl

theorem coe_comp_sup_hom (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g : SupHom α γ) = (f : SupHom β γ).comp g :=
  rfl
#align lattice_hom.coe_comp_sup_hom LatticeHom.coe_comp_sup_hom

@[simp]
-- porting note: `simp`-normal form of `coe_comp_inf_hom`
theorem coe_comp_inf_hom' (f : LatticeHom β γ) (g : LatticeHom α β) :
    ⟨f ∘ g, map_inf (f.comp g)⟩ = (f : InfHom β γ).comp g :=
  rfl

theorem coe_comp_inf_hom (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g : InfHom α γ) = (f : InfHom β γ).comp g :=
  rfl
#align lattice_hom.coe_comp_inf_hom LatticeHom.coe_comp_inf_hom

@[simp]
theorem comp_assoc (f : LatticeHom γ δ) (g : LatticeHom β γ) (h : LatticeHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align lattice_hom.comp_assoc LatticeHom.comp_assoc

@[simp]
theorem comp_id (f : LatticeHom α β) : f.comp (LatticeHom.id α) = f :=
  LatticeHom.ext fun _ => rfl
#align lattice_hom.comp_id LatticeHom.comp_id

@[simp]
theorem id_comp (f : LatticeHom α β) : (LatticeHom.id β).comp f = f :=
  LatticeHom.ext fun _ => rfl
#align lattice_hom.id_comp LatticeHom.id_comp

theorem cancel_right {g₁ g₂ : LatticeHom β γ} {f : LatticeHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => LatticeHom.ext <| hf.forall.2 <| FunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩
#align lattice_hom.cancel_right LatticeHom.cancel_right

theorem cancel_left {g : LatticeHom β γ} {f₁ f₂ : LatticeHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => LatticeHom.ext fun a => hg <| by rw [← LatticeHom.comp_apply, h, LatticeHom.comp_apply],
                                             -- 🎉 no goals
    congr_arg _⟩
#align lattice_hom.cancel_left LatticeHom.cancel_left

end LatticeHom

namespace OrderHomClass

variable (α β) [LinearOrder α] [Lattice β] [OrderHomClass F α β]

/-- An order homomorphism from a linear order is a lattice homomorphism. -/
-- porting note: made it an `instance` because we're no longer afraid of loops
instance (priority := 100) toLatticeHomClass : LatticeHomClass F α β :=
  { ‹OrderHomClass F α β› with
    map_sup := fun f a b => by
      obtain h | h := le_total a b
      -- ⊢ ↑f (a ⊔ b) = ↑f a ⊔ ↑f b
      · rw [sup_eq_right.2 h, sup_eq_right.2 (OrderHomClass.mono f h : f a ≤ f b)]
        -- 🎉 no goals
      · rw [sup_eq_left.2 h, sup_eq_left.2 (OrderHomClass.mono f h : f b ≤ f a)]
        -- 🎉 no goals
    map_inf := fun f a b => by
      obtain h | h := le_total a b
      -- ⊢ ↑f (a ⊓ b) = ↑f a ⊓ ↑f b
      · rw [inf_eq_left.2 h, inf_eq_left.2 (OrderHomClass.mono f h : f a ≤ f b)]
        -- 🎉 no goals
      · rw [inf_eq_right.2 h, inf_eq_right.2 (OrderHomClass.mono f h : f b ≤ f a)] }
        -- 🎉 no goals
#align order_hom_class.to_lattice_hom_class OrderHomClass.toLatticeHomClass

/-- Reinterpret an order homomorphism to a linear order as a `LatticeHom`. -/
def toLatticeHom (f : F) : LatticeHom α β := f
#align order_hom_class.to_lattice_hom OrderHomClass.toLatticeHom

@[simp]
theorem coe_to_lattice_hom (f : F) : ⇑(toLatticeHom α β f) = f :=
  rfl
#align order_hom_class.coe_to_lattice_hom OrderHomClass.coe_to_lattice_hom

@[simp]
theorem to_lattice_hom_apply (f : F) (a : α) : toLatticeHom α β f a = f a :=
  rfl
#align order_hom_class.to_lattice_hom_apply OrderHomClass.to_lattice_hom_apply

end OrderHomClass

/-! ### Bounded lattice homomorphisms -/


namespace BoundedLatticeHom

variable [Lattice α] [Lattice β] [Lattice γ] [Lattice δ] [BoundedOrder α] [BoundedOrder β]
  [BoundedOrder γ] [BoundedOrder δ]

/-- Reinterpret a `BoundedLatticeHom` as a `SupBotHom`. -/
def toSupBotHom (f : BoundedLatticeHom α β) : SupBotHom α β :=
  { f with }
#align bounded_lattice_hom.to_sup_bot_hom BoundedLatticeHom.toSupBotHom

/-- Reinterpret a `BoundedLatticeHom` as an `InfTopHom`. -/
def toInfTopHom (f : BoundedLatticeHom α β) : InfTopHom α β :=
  { f with }
#align bounded_lattice_hom.to_inf_top_hom BoundedLatticeHom.toInfTopHom

/-- Reinterpret a `BoundedLatticeHom` as a `BoundedOrderHom`. -/
def toBoundedOrderHom (f : BoundedLatticeHom α β) : BoundedOrderHom α β :=
  { f, (f.toLatticeHom : α →o β) with }
#align bounded_lattice_hom.to_bounded_order_hom BoundedLatticeHom.toBoundedOrderHom

instance instBoundedLatticeHomClass : BoundedLatticeHomClass (BoundedLatticeHom α β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr
                             -- ⊢ { toLatticeHom := { toSupHom := { toFun := toFun✝, map_sup' := map_sup'✝ },  …
                                                           -- ⊢ { toLatticeHom := { toSupHom := { toFun := toFun✝¹, map_sup' := map_sup'✝¹ } …
                                                                                         -- 🎉 no goals
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
  map_bot f := f.map_bot'

-- porting note: this is the `simp`-normal version of `toFun_eq_coe`
@[simp]
theorem coe_toLatticeHom {f : BoundedLatticeHom α β} : (f.toLatticeHom : α → β) = (f : α → β) :=
  rfl

@[simp]
theorem toFun_eq_coe {f : BoundedLatticeHom α β} : f.toFun = (f : α → β) :=
  rfl
#align bounded_lattice_hom.to_fun_eq_coe BoundedLatticeHom.toFun_eq_coe

@[ext]
theorem ext {f g : BoundedLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align bounded_lattice_hom.ext BoundedLatticeHom.ext

/-- Copy of a `BoundedLatticeHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : BoundedLatticeHom α β) (f' : α → β) (h : f' = f) : BoundedLatticeHom α β :=
  { f.toLatticeHom.copy f' h, f.toBoundedOrderHom.copy f' h with }
#align bounded_lattice_hom.copy BoundedLatticeHom.copy

@[simp]
theorem coe_copy (f : BoundedLatticeHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align bounded_lattice_hom.coe_copy BoundedLatticeHom.coe_copy

theorem copy_eq (f : BoundedLatticeHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align bounded_lattice_hom.copy_eq BoundedLatticeHom.copy_eq

variable (α)

/-- `id` as a `BoundedLatticeHom`. -/
protected def id : BoundedLatticeHom α α :=
  { LatticeHom.id α, BoundedOrderHom.id α with }
#align bounded_lattice_hom.id BoundedLatticeHom.id

instance : Inhabited (BoundedLatticeHom α α) :=
  ⟨BoundedLatticeHom.id α⟩

@[simp]
theorem coe_id : ⇑(BoundedLatticeHom.id α) = id :=
  rfl
#align bounded_lattice_hom.coe_id BoundedLatticeHom.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : BoundedLatticeHom.id α a = a :=
  rfl
#align bounded_lattice_hom.id_apply BoundedLatticeHom.id_apply

/-- Composition of `BoundedLatticeHom`s as a `BoundedLatticeHom`. -/
def comp (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) : BoundedLatticeHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom, f.toBoundedOrderHom.comp g.toBoundedOrderHom with }
#align bounded_lattice_hom.comp BoundedLatticeHom.comp

@[simp]
theorem coe_comp (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : α → γ) = f ∘ g :=
  rfl
#align bounded_lattice_hom.coe_comp BoundedLatticeHom.coe_comp

@[simp]
theorem comp_apply (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) (a : α) :
    (f.comp g) a = f (g a) :=
  rfl
#align bounded_lattice_hom.comp_apply BoundedLatticeHom.comp_apply

@[simp]
-- porting note: `simp`-normal form of `coe_comp_lattice_hom`
theorem coe_comp_lattice_hom' (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (⟨(f : SupHom β γ).comp g, map_inf (f.comp g)⟩ : LatticeHom α γ) =
      (f : LatticeHom β γ).comp g :=
  rfl

theorem coe_comp_lattice_hom (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : LatticeHom α γ) = (f : LatticeHom β γ).comp g :=
  rfl
#align bounded_lattice_hom.coe_comp_lattice_hom BoundedLatticeHom.coe_comp_lattice_hom

@[simp]
-- porting note: `simp`-normal form of `coe_comp_sup_hom`
theorem coe_comp_sup_hom' (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    ⟨f ∘ g, map_sup (f.comp g)⟩ = (f : SupHom β γ).comp g :=
  rfl

theorem coe_comp_sup_hom (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : SupHom α γ) = (f : SupHom β γ).comp g :=
  rfl
#align bounded_lattice_hom.coe_comp_sup_hom BoundedLatticeHom.coe_comp_sup_hom

@[simp]
-- porting note: `simp`-normal form of `coe_comp_inf_hom`
theorem coe_comp_inf_hom' (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    ⟨f ∘ g, map_inf (f.comp g)⟩ = (f : InfHom β γ).comp g :=
  rfl

theorem coe_comp_inf_hom (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : InfHom α γ) = (f : InfHom β γ).comp g :=
  rfl
#align bounded_lattice_hom.coe_comp_inf_hom BoundedLatticeHom.coe_comp_inf_hom

@[simp]
theorem comp_assoc (f : BoundedLatticeHom γ δ) (g : BoundedLatticeHom β γ)
    (h : BoundedLatticeHom α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align bounded_lattice_hom.comp_assoc BoundedLatticeHom.comp_assoc

@[simp] theorem comp_id (f : BoundedLatticeHom α β) : f.comp (BoundedLatticeHom.id α) = f := rfl
#align bounded_lattice_hom.comp_id BoundedLatticeHom.comp_id

@[simp] theorem id_comp (f : BoundedLatticeHom α β) : (BoundedLatticeHom.id β).comp f = f := rfl
#align bounded_lattice_hom.id_comp BoundedLatticeHom.id_comp

theorem cancel_right {g₁ g₂ : BoundedLatticeHom β γ} {f : BoundedLatticeHom α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => BoundedLatticeHom.ext <| hf.forall.2 <| FunLike.ext_iff.1 h,
    fun h => congr_arg₂ _ h rfl⟩
#align bounded_lattice_hom.cancel_right BoundedLatticeHom.cancel_right

theorem cancel_left {g : BoundedLatticeHom β γ} {f₁ f₂ : BoundedLatticeHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
                                  -- 🎉 no goals
#align bounded_lattice_hom.cancel_left BoundedLatticeHom.cancel_left

end BoundedLatticeHom

/-! ### Dual homs -/

namespace SupHom

variable [Sup α] [Sup β] [Sup γ]

/-- Reinterpret a supremum homomorphism as an infimum homomorphism between the dual lattices. -/
@[simps]
protected def dual : SupHom α β ≃ InfHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨f, f.map_sup'⟩
  invFun f := ⟨f, f.map_inf'⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align sup_hom.dual SupHom.dual

@[simp]
theorem dual_id : SupHom.dual (SupHom.id α) = InfHom.id _ :=
  rfl
#align sup_hom.dual_id SupHom.dual_id

@[simp]
theorem dual_comp (g : SupHom β γ) (f : SupHom α β) :
    SupHom.dual (g.comp f) = (SupHom.dual g).comp (SupHom.dual f) :=
  rfl
#align sup_hom.dual_comp SupHom.dual_comp

@[simp]
theorem symm_dual_id : SupHom.dual.symm (InfHom.id _) = SupHom.id α :=
  rfl
#align sup_hom.symm_dual_id SupHom.symm_dual_id

@[simp]
theorem symm_dual_comp (g : InfHom βᵒᵈ γᵒᵈ) (f : InfHom αᵒᵈ βᵒᵈ) :
    SupHom.dual.symm (g.comp f) =
      (SupHom.dual.symm g).comp (SupHom.dual.symm f) :=
  rfl
#align sup_hom.symm_dual_comp SupHom.symm_dual_comp

end SupHom

namespace InfHom

variable [Inf α] [Inf β] [Inf γ]

/-- Reinterpret an infimum homomorphism as a supremum homomorphism between the dual lattices. -/
@[simps]
protected def dual : InfHom α β ≃ SupHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨f, f.map_inf'⟩
  invFun f := ⟨f, f.map_sup'⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align inf_hom.dual InfHom.dual

@[simp]
theorem dual_id : InfHom.dual (InfHom.id α) = SupHom.id _ :=
  rfl
#align inf_hom.dual_id InfHom.dual_id

@[simp]
theorem dual_comp (g : InfHom β γ) (f : InfHom α β) :
    InfHom.dual (g.comp f) = (InfHom.dual g).comp (InfHom.dual f) :=
  rfl
#align inf_hom.dual_comp InfHom.dual_comp

@[simp]
theorem symm_dual_id : InfHom.dual.symm (SupHom.id _) = InfHom.id α :=
  rfl
#align inf_hom.symm_dual_id InfHom.symm_dual_id

@[simp]
theorem symm_dual_comp (g : SupHom βᵒᵈ γᵒᵈ) (f : SupHom αᵒᵈ βᵒᵈ) :
    InfHom.dual.symm (g.comp f) =
      (InfHom.dual.symm g).comp (InfHom.dual.symm f) :=
  rfl
#align inf_hom.symm_dual_comp InfHom.symm_dual_comp

end InfHom

namespace SupBotHom

variable [Sup α] [Bot α] [Sup β] [Bot β] [Sup γ] [Bot γ]

/-- Reinterpret a finitary supremum homomorphism as a finitary infimum homomorphism between the dual
lattices. -/
def dual : SupBotHom α β ≃ InfTopHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨SupHom.dual f.toSupHom, f.map_bot'⟩
  invFun f := ⟨SupHom.dual.symm f.toInfHom, f.map_top'⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align sup_bot_hom.dual SupBotHom.dual

@[simp] theorem dual_id : SupBotHom.dual (SupBotHom.id α) = InfTopHom.id _ := rfl
#align sup_bot_hom.dual_id SupBotHom.dual_id

@[simp]
theorem dual_comp (g : SupBotHom β γ) (f : SupBotHom α β) :
    SupBotHom.dual (g.comp f) = (SupBotHom.dual g).comp (SupBotHom.dual f) :=
  rfl
#align sup_bot_hom.dual_comp SupBotHom.dual_comp

@[simp]
theorem symm_dual_id : SupBotHom.dual.symm (InfTopHom.id _) = SupBotHom.id α :=
  rfl
#align sup_bot_hom.symm_dual_id SupBotHom.symm_dual_id

@[simp]
theorem symm_dual_comp (g : InfTopHom βᵒᵈ γᵒᵈ) (f : InfTopHom αᵒᵈ βᵒᵈ) :
    SupBotHom.dual.symm (g.comp f) =
      (SupBotHom.dual.symm g).comp (SupBotHom.dual.symm f) :=
  rfl
#align sup_bot_hom.symm_dual_comp SupBotHom.symm_dual_comp

end SupBotHom

namespace InfTopHom

variable [Inf α] [Top α] [Inf β] [Top β] [Inf γ] [Top γ]

/-- Reinterpret a finitary infimum homomorphism as a finitary supremum homomorphism between the dual
lattices. -/
@[simps]
protected def dual : InfTopHom α β ≃ SupBotHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨InfHom.dual f.toInfHom, f.map_top'⟩
  invFun f := ⟨InfHom.dual.symm f.toSupHom, f.map_bot'⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align inf_top_hom.dual InfTopHom.dual

@[simp]
theorem dual_id : InfTopHom.dual (InfTopHom.id α) = SupBotHom.id _ :=
  rfl
#align inf_top_hom.dual_id InfTopHom.dual_id

@[simp]
theorem dual_comp (g : InfTopHom β γ) (f : InfTopHom α β) :
    InfTopHom.dual (g.comp f) = (InfTopHom.dual g).comp (InfTopHom.dual f) :=
  rfl
#align inf_top_hom.dual_comp InfTopHom.dual_comp

@[simp]
theorem symm_dual_id : InfTopHom.dual.symm (SupBotHom.id _) = InfTopHom.id α :=
  rfl
#align inf_top_hom.symm_dual_id InfTopHom.symm_dual_id

@[simp]
theorem symm_dual_comp (g : SupBotHom βᵒᵈ γᵒᵈ) (f : SupBotHom αᵒᵈ βᵒᵈ) :
    InfTopHom.dual.symm (g.comp f) =
      (InfTopHom.dual.symm g).comp (InfTopHom.dual.symm f) :=
  rfl
#align inf_top_hom.symm_dual_comp InfTopHom.symm_dual_comp

end InfTopHom

namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ]

/-- Reinterpret a lattice homomorphism as a lattice homomorphism between the dual lattices. -/
@[simps]
protected def dual : LatticeHom α β ≃ LatticeHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨InfHom.dual f.toInfHom, f.map_sup'⟩
  invFun f := ⟨SupHom.dual.symm f.toInfHom, f.map_sup'⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align lattice_hom.dual LatticeHom.dual

@[simp] theorem dual_id : LatticeHom.dual (LatticeHom.id α) = LatticeHom.id _ := rfl
#align lattice_hom.dual_id LatticeHom.dual_id

@[simp]
theorem dual_comp (g : LatticeHom β γ) (f : LatticeHom α β) :
    LatticeHom.dual (g.comp f) = (LatticeHom.dual g).comp (LatticeHom.dual f) :=
  rfl
#align lattice_hom.dual_comp LatticeHom.dual_comp

@[simp]
theorem symm_dual_id : LatticeHom.dual.symm (LatticeHom.id _) = LatticeHom.id α :=
  rfl
#align lattice_hom.symm_dual_id LatticeHom.symm_dual_id

@[simp]
theorem symm_dual_comp (g : LatticeHom βᵒᵈ γᵒᵈ) (f : LatticeHom αᵒᵈ βᵒᵈ) :
    LatticeHom.dual.symm (g.comp f) =
      (LatticeHom.dual.symm g).comp (LatticeHom.dual.symm f) :=
  rfl
#align lattice_hom.symm_dual_comp LatticeHom.symm_dual_comp

end LatticeHom

namespace BoundedLatticeHom

variable [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β] [Lattice γ] [BoundedOrder γ]

/-- Reinterpret a bounded lattice homomorphism as a bounded lattice homomorphism between the dual
bounded lattices. -/
@[simps]
protected def dual : BoundedLatticeHom α β ≃ BoundedLatticeHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨LatticeHom.dual f.toLatticeHom, f.map_bot', f.map_top'⟩
  invFun f := ⟨LatticeHom.dual.symm f.toLatticeHom, f.map_bot', f.map_top'⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align bounded_lattice_hom.dual BoundedLatticeHom.dual

@[simp]
theorem dual_id : BoundedLatticeHom.dual (BoundedLatticeHom.id α) = BoundedLatticeHom.id _ :=
  rfl
#align bounded_lattice_hom.dual_id BoundedLatticeHom.dual_id

@[simp]
theorem dual_comp (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β) :
    BoundedLatticeHom.dual (g.comp f) =
      (BoundedLatticeHom.dual g).comp (BoundedLatticeHom.dual f) :=
  rfl
#align bounded_lattice_hom.dual_comp BoundedLatticeHom.dual_comp

@[simp]
theorem symm_dual_id :
    BoundedLatticeHom.dual.symm (BoundedLatticeHom.id _) = BoundedLatticeHom.id α :=
  rfl
#align bounded_lattice_hom.symm_dual_id BoundedLatticeHom.symm_dual_id

@[simp]
theorem symm_dual_comp (g : BoundedLatticeHom βᵒᵈ γᵒᵈ) (f : BoundedLatticeHom αᵒᵈ βᵒᵈ) :
    BoundedLatticeHom.dual.symm (g.comp f) =
      (BoundedLatticeHom.dual.symm g).comp (BoundedLatticeHom.dual.symm f) :=
  rfl
#align bounded_lattice_hom.symm_dual_comp BoundedLatticeHom.symm_dual_comp

end BoundedLatticeHom

/-! ### `WithTop`, `WithBot` -/

namespace SupHom
variable [SemilatticeSup α] [SemilatticeSup β] [SemilatticeSup γ]

/-- Adjoins a `⊤` to the domain and codomain of a `SupHom`. -/
@[simps]
protected def withTop (f : SupHom α β) : SupHom (WithTop α) (WithTop β) where
  -- porting note: this was `Option.map f`
  toFun := WithTop.map f
  map_sup' a b :=
    match a, b with
    | ⊤, ⊤ => rfl
    | ⊤, (b : α) => rfl
    | (a : α), ⊤ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_sup' _ _)
#align sup_hom.with_top SupHom.withTop

@[simp]
theorem withTop_id : (SupHom.id α).withTop = SupHom.id _ := FunLike.coe_injective Option.map_id
#align sup_hom.with_top_id SupHom.withTop_id

@[simp]
theorem withTop_comp (f : SupHom β γ) (g : SupHom α β) :
    (f.comp g).withTop = f.withTop.comp g.withTop :=
-- porting note: Proof was `FunLike.coe_injective (Option.map_comp_map _ _).symm`
  FunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _
#align sup_hom.with_top_comp SupHom.withTop_comp

/-- Adjoins a `⊥` to the domain and codomain of a `SupHom`. -/
@[simps]
protected def withBot (f : SupHom α β) : SupBotHom (WithBot α) (WithBot β) where
  toFun := Option.map f
  map_sup' a b :=
    match a, b with
    | ⊥, ⊥ => rfl
    | ⊥, (b : α) => rfl
    | (a : α), ⊥ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_sup' _ _)
  map_bot' := rfl
#align sup_hom.with_bot SupHom.withBot

@[simp]
theorem withBot_id : (SupHom.id α).withBot = SupBotHom.id _ := FunLike.coe_injective Option.map_id
#align sup_hom.with_bot_id SupHom.withBot_id

@[simp]
theorem withBot_comp (f : SupHom β γ) (g : SupHom α β) :
    (f.comp g).withBot = f.withBot.comp g.withBot :=
-- porting note: Proof was `FunLike.coe_injective (Option.map_comp_map _ _).symm`
  FunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _
#align sup_hom.with_bot_comp SupHom.withBot_comp

/-- Adjoins a `⊤` to the codomain of a `SupHom`. -/
@[simps]
def withTop' [OrderTop β] (f : SupHom α β) : SupHom (WithTop α) β where
  toFun a := a.elim ⊤ f
  map_sup' a b :=
    match a, b with
    | ⊤, ⊤ => top_sup_eq.symm
    | ⊤, (b : α) => top_sup_eq.symm
    | (a : α), ⊤ => sup_top_eq.symm
    | (a : α), (b : α) => f.map_sup' _ _
#align sup_hom.with_top' SupHom.withTop'

/-- Adjoins a `⊥` to the domain of a `SupHom`. -/
@[simps]
def withBot' [OrderBot β] (f : SupHom α β) : SupBotHom (WithBot α) β where
  toFun a := a.elim ⊥ f
  map_sup' a b :=
    match a, b with
    | ⊥, ⊥ => bot_sup_eq.symm
    | ⊥, (b : α) => bot_sup_eq.symm
    | (a : α), ⊥ => sup_bot_eq.symm
    | (a : α), (b : α) => f.map_sup' _ _
  map_bot' := rfl
#align sup_hom.with_bot' SupHom.withBot'

end SupHom

namespace InfHom

variable [SemilatticeInf α] [SemilatticeInf β] [SemilatticeInf γ]

/-- Adjoins a `⊤` to the domain and codomain of an `InfHom`. -/
@[simps]
protected def withTop (f : InfHom α β) : InfTopHom (WithTop α) (WithTop β) where
  toFun := Option.map f
  map_inf' a b :=
    match a, b with
    | ⊤, ⊤ => rfl
    | ⊤, (b : α) => rfl
    | (a : α), ⊤ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_inf' _ _)
  map_top' := rfl
#align inf_hom.with_top InfHom.withTop

@[simp]
theorem withTop_id : (InfHom.id α).withTop = InfTopHom.id _ := FunLike.coe_injective Option.map_id
#align inf_hom.with_top_id InfHom.withTop_id

@[simp]
theorem withTop_comp (f : InfHom β γ) (g : InfHom α β) :
    (f.comp g).withTop = f.withTop.comp g.withTop :=
-- porting note: Proof was `FunLike.coe_injective (Option.map_comp_map _ _).symm`
  FunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _
#align inf_hom.with_top_comp InfHom.withTop_comp

/-- Adjoins a `⊥` to the domain and codomain of an `InfHom`. -/
@[simps]
protected def withBot (f : InfHom α β) : InfHom (WithBot α) (WithBot β) where
  toFun := Option.map f
  map_inf' a b :=
    match a, b with
    | ⊥, ⊥ => rfl
    | ⊥, (b : α) => rfl
    | (a : α), ⊥ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_inf' _ _)
#align inf_hom.with_bot InfHom.withBot

@[simp]
theorem withBot_id : (InfHom.id α).withBot = InfHom.id _ := FunLike.coe_injective Option.map_id
#align inf_hom.with_bot_id InfHom.withBot_id

@[simp]
theorem withBot_comp (f : InfHom β γ) (g : InfHom α β) :
    (f.comp g).withBot = f.withBot.comp g.withBot :=
-- porting note: Proof was `FunLike.coe_injective (Option.map_comp_map _ _).symm`
  FunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _
#align inf_hom.with_bot_comp InfHom.withBot_comp

/-- Adjoins a `⊤` to the codomain of an `InfHom`. -/
@[simps]
def withTop' [OrderTop β] (f : InfHom α β) : InfTopHom (WithTop α) β where
  toFun a := a.elim ⊤ f
  map_inf' a b :=
    match a, b with
    | ⊤, ⊤ => top_inf_eq.symm
    | ⊤, (b : α) => top_inf_eq.symm
    | (a : α), ⊤ => inf_top_eq.symm
    | (a : α), (b : α) => f.map_inf' _ _
  map_top' := rfl
#align inf_hom.with_top' InfHom.withTop'

/-- Adjoins a `⊥` to the codomain of an `InfHom`. -/
@[simps]
def withBot' [OrderBot β] (f : InfHom α β) : InfHom (WithBot α) β where
  toFun a := a.elim ⊥ f
  map_inf' a b :=
    match a, b with
    | ⊥, ⊥ => bot_inf_eq.symm
    | ⊥, (b : α) => bot_inf_eq.symm
    | (a : α), ⊥ => inf_bot_eq.symm
    | (a : α), (b : α) => f.map_inf' _ _
#align inf_hom.with_bot' InfHom.withBot'

end InfHom

namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ]

/-- Adjoins a `⊤` to the domain and codomain of a `LatticeHom`. -/
@[simps]
protected def withTop (f : LatticeHom α β) : LatticeHom (WithTop α) (WithTop β) :=
  { f.toInfHom.withTop with toSupHom := f.toSupHom.withTop }
#align lattice_hom.with_top LatticeHom.withTop

-- porting note: `simps` doesn't generate those
@[simp, norm_cast]
lemma coe_withTop (f : LatticeHom α β) : ⇑f.withTop = WithTop.map f := rfl

lemma withTop_apply (f : LatticeHom α β) (a : WithTop α) : f.withTop a = a.map f := rfl

@[simp]
theorem withTop_id : (LatticeHom.id α).withTop = LatticeHom.id _ :=
  FunLike.coe_injective Option.map_id
#align lattice_hom.with_top_id LatticeHom.withTop_id

@[simp]
theorem withTop_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withTop = f.withTop.comp g.withTop :=
-- porting note: Proof was `FunLike.coe_injective (Option.map_comp_map _ _).symm`
  FunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _
#align lattice_hom.with_top_comp LatticeHom.withTop_comp

/-- Adjoins a `⊥` to the domain and codomain of a `LatticeHom`. -/
@[simps]
protected def withBot (f : LatticeHom α β) : LatticeHom (WithBot α) (WithBot β) :=
  { f.toInfHom.withBot with toSupHom := f.toSupHom.withBot }
#align lattice_hom.with_bot LatticeHom.withBot

-- porting note: `simps` doesn't generate those
@[simp, norm_cast]
lemma coe_withBot (f : LatticeHom α β) : ⇑f.withBot = Option.map f := rfl

lemma withBot_apply (f : LatticeHom α β) (a : WithBot α) : f.withBot a = a.map f := rfl

@[simp]
theorem withBot_id : (LatticeHom.id α).withBot = LatticeHom.id _ :=
  FunLike.coe_injective Option.map_id
#align lattice_hom.with_bot_id LatticeHom.withBot_id

@[simp]
theorem withBot_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withBot = f.withBot.comp g.withBot :=
-- porting note: Proof was `FunLike.coe_injective (Option.map_comp_map _ _).symm`
  FunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _
#align lattice_hom.with_bot_comp LatticeHom.withBot_comp

/-- Adjoins a `⊤` and `⊥` to the domain and codomain of a `LatticeHom`. -/
@[simps]
def withTopWithBot (f : LatticeHom α β) :
    BoundedLatticeHom (WithTop <| WithBot α) (WithTop <| WithBot β) :=
  ⟨f.withBot.withTop, rfl, rfl⟩
#align lattice_hom.with_top_with_bot LatticeHom.withTopWithBot

-- porting note: `simps` doesn't generate those
@[simp, norm_cast]
lemma coe_withTopWithBot (f : LatticeHom α β) : ⇑f.withTopWithBot = Option.map (Option.map f) := rfl

lemma withTopWithBot_apply (f : LatticeHom α β) (a : WithTop <| WithBot α) :
    f.withTopWithBot a = a.map (Option.map f) := rfl

@[simp]
theorem withTopWithBot_id : (LatticeHom.id α).withTopWithBot = BoundedLatticeHom.id _ :=
  FunLike.coe_injective $ by
    refine' (congr_arg Option.map _).trans Option.map_id
    -- ⊢ (fun x => ↑(LatticeHom.withBot (LatticeHom.id α)).toSupHom x) = id
    rw [withBot_id]
    -- ⊢ (fun x => ↑(LatticeHom.id (WithBot α)).toSupHom x) = id
    rfl
    -- 🎉 no goals
#align lattice_hom.with_top_with_bot_id LatticeHom.withTopWithBot_id

@[simp]
theorem withTopWithBot_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withTopWithBot = f.withTopWithBot.comp g.withTopWithBot := by
  ext; simp
  -- ⊢ ↑(withTopWithBot (comp f g)) a✝ = ↑(BoundedLatticeHom.comp (withTopWithBot f …
       -- 🎉 no goals
#align lattice_hom.with_top_with_bot_comp LatticeHom.withTopWithBot_comp

/-- Adjoins a `⊥` to the codomain of a `LatticeHom`. -/
@[simps]
def withTop' [OrderTop β] (f : LatticeHom α β) : LatticeHom (WithTop α) β :=
  { f.toSupHom.withTop', f.toInfHom.withTop' with }
#align lattice_hom.with_top' LatticeHom.withTop'

/-- Adjoins a `⊥` to the domain and codomain of a `LatticeHom`. -/
@[simps]
def withBot' [OrderBot β] (f : LatticeHom α β) : LatticeHom (WithBot α) β :=
  { f.toSupHom.withBot', f.toInfHom.withBot' with }
#align lattice_hom.with_bot' LatticeHom.withBot'

/-- Adjoins a `⊤` and `⊥` to the codomain of a `LatticeHom`. -/
@[simps]
def withTopWithBot' [BoundedOrder β] (f : LatticeHom α β) :
    BoundedLatticeHom (WithTop $ WithBot α) β where
  toLatticeHom := f.withBot'.withTop'
  map_top' := rfl
  map_bot' := rfl
#align lattice_hom.with_top_with_bot' LatticeHom.withTopWithBot'

end LatticeHom
