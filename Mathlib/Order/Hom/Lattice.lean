/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Hom.Basic

/-!
# Unbounded lattice homomorphisms

This file defines unbounded lattice homomorphisms. _Bounded_ lattice homomorphisms are defined in
`Mathlib/Order/Hom/BoundedLattice.lean`.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `SupHom`: Maps which preserve `⊔`.
* `InfHom`: Maps which preserve `⊓`.
* `LatticeHom`: Lattice homomorphisms. Maps which preserve `⊔` and `⊓`.

## Typeclasses

* `SupHomClass`
* `InfHomClass`
* `LatticeHomClass`
-/


open Function

variable {F α β γ δ : Type*}

/-- The type of `⊔`-preserving functions from `α` to `β`. -/
structure SupHom (α β : Type*) [Max α] [Max β] where
  /-- The underlying function of a `SupHom`.

  Do not use this function directly. Instead use the coercion coming from the `FunLike`
  instance. -/
  toFun : α → β
  /-- A `SupHom` preserves suprema.

  Do not use this directly. Use `map_sup` instead. -/
  map_sup' (a b : α) : toFun (a ⊔ b) = toFun a ⊔ toFun b

/-- The type of `⊓`-preserving functions from `α` to `β`. -/
structure InfHom (α β : Type*) [Min α] [Min β] where
  /-- The underlying function of an `InfHom`.

  Do not use this function directly. Instead use the coercion coming from the `FunLike`
  instance. -/
  toFun : α → β
  /-- An `InfHom` preserves infima.

  Do not use this directly. Use `map_inf` instead. -/
  map_inf' (a b : α) : toFun (a ⊓ b) = toFun a ⊓ toFun b

/-- The type of lattice homomorphisms from `α` to `β`. -/
structure LatticeHom (α β : Type*) [Lattice α] [Lattice β] extends SupHom α β where
  /-- A `LatticeHom` preserves infima.

  Do not use this directly. Use `map_inf` instead. -/
  map_inf' (a b : α) : toFun (a ⊓ b) = toFun a ⊓ toFun b

-- TODO: remove this configuration and use the default configuration.
initialize_simps_projections LatticeHom (+toSupHom, -toFun)

section

/-- `SupHomClass F α β` states that `F` is a type of `⊔`-preserving morphisms.

You should extend this class when you extend `SupHom`. -/
class SupHomClass (F α β : Type*) [Max α] [Max β] [FunLike F α β] : Prop where
  /-- A `SupHomClass` morphism preserves suprema. -/
  map_sup (f : F) (a b : α) : f (a ⊔ b) = f a ⊔ f b

/-- `InfHomClass F α β` states that `F` is a type of `⊓`-preserving morphisms.

You should extend this class when you extend `InfHom`. -/
class InfHomClass (F α β : Type*) [Min α] [Min β] [FunLike F α β] : Prop where
  /-- An `InfHomClass` morphism preserves infima. -/
  map_inf (f : F) (a b : α) : f (a ⊓ b) = f a ⊓ f b

/-- `LatticeHomClass F α β` states that `F` is a type of lattice morphisms.

You should extend this class when you extend `LatticeHom`. -/
class LatticeHomClass (F α β : Type*) [Lattice α] [Lattice β] [FunLike F α β] : Prop
  extends SupHomClass F α β where
  /-- A `LatticeHomClass` morphism preserves infima. -/
  map_inf (f : F) (a b : α) : f (a ⊓ b) = f a ⊓ f b

end

export SupHomClass (map_sup)

export InfHomClass (map_inf)

attribute [simp] map_sup map_inf

section Hom

variable [FunLike F α β]

-- See note [lower instance priority]
instance (priority := 100) SupHomClass.toOrderHomClass [SemilatticeSup α] [SemilatticeSup β]
    [SupHomClass F α β] : OrderHomClass F α β :=
  { ‹SupHomClass F α β› with
    map_rel := fun f a b h => by rw [← sup_eq_right, ← map_sup, sup_eq_right.2 h] }

-- See note [lower instance priority]
instance (priority := 100) InfHomClass.toOrderHomClass [SemilatticeInf α] [SemilatticeInf β]
    [InfHomClass F α β] : OrderHomClass F α β :=
  { ‹InfHomClass F α β› with
    map_rel := fun f a b h => by rw [← inf_eq_left, ← map_inf, inf_eq_left.2 h] }

-- See note [lower instance priority]
instance (priority := 100) LatticeHomClass.toInfHomClass [Lattice α] [Lattice β]
    [LatticeHomClass F α β] : InfHomClass F α β :=
  { ‹LatticeHomClass F α β› with }

end Hom

section Equiv

variable [EquivLike F α β]

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toSupHomClass [SemilatticeSup α] [SemilatticeSup β]
    [OrderIsoClass F α β] : SupHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_sup := fun f a b =>
      eq_of_forall_ge_iff fun c => by simp only [← le_map_inv_iff, sup_le_iff] }


-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toInfHomClass [SemilatticeInf α] [SemilatticeInf β]
    [OrderIsoClass F α β] : InfHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_inf := fun f a b =>
      eq_of_forall_le_iff fun c => by simp only [← map_inv_le_iff, le_inf_iff] }

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toLatticeHomClass [Lattice α] [Lattice β]
    [OrderIsoClass F α β] : LatticeHomClass F α β :=
  { OrderIsoClass.toSupHomClass, OrderIsoClass.toInfHomClass with }

end Equiv

section OrderEmbedding

variable [FunLike F α β]

/-- We can regard an injective map preserving binary infima as an order embedding. -/
@[simps! apply]
def orderEmbeddingOfInjective [SemilatticeInf α] [SemilatticeInf β] (f : F) [InfHomClass F α β]
    (hf : Injective f) : α ↪o β :=
  OrderEmbedding.ofMapLEIff f (fun x y ↦ by
    refine ⟨fun h ↦ ?_, fun h ↦ OrderHomClass.mono f h⟩
    rwa [← inf_eq_left, ← hf.eq_iff, map_inf, inf_eq_left])

end OrderEmbedding

variable [FunLike F α β]

instance [Max α] [Max β] [SupHomClass F α β] : CoeTC F (SupHom α β) :=
  ⟨fun f => ⟨f, map_sup f⟩⟩

instance [Min α] [Min β] [InfHomClass F α β] : CoeTC F (InfHom α β) :=
  ⟨fun f => ⟨f, map_inf f⟩⟩

instance [Lattice α] [Lattice β] [LatticeHomClass F α β] : CoeTC F (LatticeHom α β) :=
  ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f }⟩

/-! ### Supremum homomorphisms -/

namespace SupHom

variable [Max α]

section Sup

variable [Max β] [Max γ] [Max δ]

instance : FunLike (SupHom α β) α β where
  coe := SupHom.toFun
  coe_injective' f g h := by cases f; cases g; congr

instance : SupHomClass (SupHom α β) α β where
  map_sup := SupHom.map_sup'

@[simp] lemma toFun_eq_coe (f : SupHom α β) : f.toFun = f := rfl

@[simp, norm_cast] lemma coe_mk (f : α → β) (hf) : ⇑(mk f hf) = f := rfl

@[ext]
theorem ext {f g : SupHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `SupHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : SupHom α β) (f' : α → β) (h : f' = f) : SupHom α β where
  toFun := f'
  map_sup' := h.symm ▸ f.map_sup'

@[simp]
theorem coe_copy (f : SupHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : SupHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `SupHom`. -/
protected def id : SupHom α α :=
  ⟨id, fun _ _ => rfl⟩

instance : Inhabited (SupHom α α) :=
  ⟨SupHom.id α⟩

@[simp, norm_cast]
theorem coe_id : ⇑(SupHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : SupHom.id α a = a :=
  rfl

/-- Composition of `SupHom`s as a `SupHom`. -/
def comp (f : SupHom β γ) (g : SupHom α β) : SupHom α γ where
  toFun := f ∘ g
  map_sup' a b := by rw [comp_apply, map_sup, map_sup]; rfl

@[simp]
theorem coe_comp (f : SupHom β γ) (g : SupHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : SupHom β γ) (g : SupHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : SupHom γ δ) (g : SupHom β γ) (h : SupHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp] theorem comp_id (f : SupHom α β) : f.comp (SupHom.id α) = f := rfl

@[simp] theorem id_comp (f : SupHom α β) : (SupHom.id β).comp f = f := rfl

@[simp]
theorem cancel_right {g₁ g₂ : SupHom β γ} {f : SupHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => SupHom.ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]
theorem cancel_left {g : SupHom β γ} {f₁ f₂ : SupHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => SupHom.ext fun a => hg <| by rw [← SupHom.comp_apply, h, SupHom.comp_apply],
    congr_arg _⟩

end Sup

variable (α) [SemilatticeSup β]

/-- The constant function as a `SupHom`. -/
def const (b : β) : SupHom α β := ⟨fun _ ↦ b, fun _ _ ↦ (sup_idem _).symm⟩

@[simp]
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl

@[simp]
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl

variable {α}

instance : Max (SupHom α β) :=
  ⟨fun f g =>
    ⟨f ⊔ g, fun a b => by
      rw [Pi.sup_apply, map_sup, map_sup]
      exact sup_sup_sup_comm _ _ _ _⟩⟩

instance : SemilatticeSup (SupHom α β) :=
  (DFunLike.coe_injective.semilatticeSup _) fun _ _ => rfl

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
theorem coe_sup (f g : SupHom α β) : DFunLike.coe (f ⊔ g) = f ⊔ g :=
  rfl

@[simp]
theorem coe_bot [Bot β] : ⇑(⊥ : SupHom α β) = ⊥ :=
  rfl

@[simp]
theorem coe_top [Top β] : ⇑(⊤ : SupHom α β) = ⊤ :=
  rfl

@[simp]
theorem sup_apply (f g : SupHom α β) (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl

@[simp]
theorem bot_apply [Bot β] (a : α) : (⊥ : SupHom α β) a = ⊥ :=
  rfl

@[simp]
theorem top_apply [Top β] (a : α) : (⊤ : SupHom α β) a = ⊤ :=
  rfl

/-- `Subtype.val` as a `SupHom`. -/
def subtypeVal {P : β → Prop}
    (Psup : ∀ ⦃x y : β⦄, P x → P y → P (x ⊔ y)) :
    letI := Subtype.semilatticeSup Psup
    SupHom {x : β // P x} β :=
  letI := Subtype.semilatticeSup Psup
  .mk Subtype.val (by simp)

@[simp]
lemma subtypeVal_apply {P : β → Prop}
    (Psup : ∀ ⦃x y : β⦄, P x → P y → P (x ⊔ y)) (x : {x : β // P x}) :
    subtypeVal Psup x = x := rfl

@[simp]
lemma subtypeVal_coe {P : β → Prop}
    (Psup : ∀ ⦃x y : β⦄, P x → P y → P (x ⊔ y)) :
    ⇑(subtypeVal Psup) = Subtype.val := rfl

end SupHom

/-! ### Infimum homomorphisms -/


namespace InfHom

variable [Min α]

section Inf

variable [Min β] [Min γ] [Min δ]

instance : FunLike (InfHom α β) α β where
  coe := InfHom.toFun
  coe_injective' f g h := by cases f; cases g; congr

instance : InfHomClass (InfHom α β) α β where
  map_inf := InfHom.map_inf'

@[simp] lemma toFun_eq_coe (f : InfHom α β) : f.toFun = (f : α → β) := rfl

@[simp, norm_cast] lemma coe_mk (f : α → β) (hf) : ⇑(mk f hf) = f := rfl

@[ext]
theorem ext {f g : InfHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of an `InfHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : InfHom α β) (f' : α → β) (h : f' = f) : InfHom α β where
  toFun := f'
  map_inf' := h.symm ▸ f.map_inf'

@[simp]
theorem coe_copy (f : InfHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : InfHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as an `InfHom`. -/
protected def id : InfHom α α :=
  ⟨id, fun _ _ => rfl⟩

instance : Inhabited (InfHom α α) :=
  ⟨InfHom.id α⟩

@[simp, norm_cast]
theorem coe_id : ⇑(InfHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : InfHom.id α a = a :=
  rfl

/-- Composition of `InfHom`s as an `InfHom`. -/
def comp (f : InfHom β γ) (g : InfHom α β) : InfHom α γ where
  toFun := f ∘ g
  map_inf' a b := by rw [comp_apply, map_inf, map_inf]; rfl

@[simp]
theorem coe_comp (f : InfHom β γ) (g : InfHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : InfHom β γ) (g : InfHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : InfHom γ δ) (g : InfHom β γ) (h : InfHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp] theorem comp_id (f : InfHom α β) : f.comp (InfHom.id α) = f := rfl

@[simp] theorem id_comp (f : InfHom α β) : (InfHom.id β).comp f = f := rfl

@[simp]
theorem cancel_right {g₁ g₂ : InfHom β γ} {f : InfHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => InfHom.ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]
theorem cancel_left {g : InfHom β γ} {f₁ f₂ : InfHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => InfHom.ext fun a => hg <| by rw [← InfHom.comp_apply, h, InfHom.comp_apply],
    congr_arg _⟩

end Inf

variable (α) [SemilatticeInf β]

/-- The constant function as an `InfHom`. -/
def const (b : β) : InfHom α β := ⟨fun _ ↦ b, fun _ _ ↦ (inf_idem _).symm⟩

@[simp]
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl

@[simp]
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl

variable {α}

instance : Min (InfHom α β) :=
  ⟨fun f g =>
    ⟨f ⊓ g, fun a b => by
      rw [Pi.inf_apply, map_inf, map_inf]
      exact inf_inf_inf_comm _ _ _ _⟩⟩

instance : SemilatticeInf (InfHom α β) :=
  (DFunLike.coe_injective.semilatticeInf _) fun _ _ => rfl

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
theorem coe_inf (f g : InfHom α β) : DFunLike.coe (f ⊓ g) = f ⊓ g :=
  rfl

@[simp]
theorem coe_bot [Bot β] : ⇑(⊥ : InfHom α β) = ⊥ :=
  rfl

@[simp]
theorem coe_top [Top β] : ⇑(⊤ : InfHom α β) = ⊤ :=
  rfl

@[simp]
theorem inf_apply (f g : InfHom α β) (a : α) : (f ⊓ g) a = f a ⊓ g a :=
  rfl

@[simp]
theorem bot_apply [Bot β] (a : α) : (⊥ : InfHom α β) a = ⊥ :=
  rfl

@[simp]
theorem top_apply [Top β] (a : α) : (⊤ : InfHom α β) a = ⊤ :=
  rfl

/-- `Subtype.val` as an `InfHom`. -/
def subtypeVal {P : β → Prop}
    (Pinf : ∀ ⦃x y : β⦄, P x → P y → P (x ⊓ y)) :
    letI := Subtype.semilatticeInf Pinf
    InfHom {x : β // P x} β :=
  letI := Subtype.semilatticeInf Pinf
  .mk Subtype.val (by simp)

@[simp]
lemma subtypeVal_apply {P : β → Prop}
    (Pinf : ∀ ⦃x y : β⦄, P x → P y → P (x ⊓ y)) (x : {x : β // P x}) :
    subtypeVal Pinf x = x := rfl

@[simp]
lemma subtypeVal_coe {P : β → Prop}
    (Pinf : ∀ ⦃x y : β⦄, P x → P y → P (x ⊓ y)) :
    ⇑(subtypeVal Pinf) = Subtype.val := rfl

end InfHom

/-! ### Lattice homomorphisms -/


namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ] [Lattice δ]

/-- Reinterpret a `LatticeHom` as an `InfHom`. -/
def toInfHom (f : LatticeHom α β) : InfHom α β :=
  { f with }

instance : FunLike (LatticeHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

instance : LatticeHomClass (LatticeHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'

lemma toFun_eq_coe (f : LatticeHom α β) : f.toFun = f := rfl

@[simp] lemma coe_toSupHom (f : LatticeHom α β) : ⇑f.toSupHom = f := rfl
@[simp] lemma coe_toInfHom (f : LatticeHom α β) : ⇑f.toInfHom = f := rfl
@[simp] lemma coe_mk (f : SupHom α β) (hf) : ⇑(mk f hf) = f := rfl

@[ext]
theorem ext {f g : LatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `LatticeHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : LatticeHom α β) (f' : α → β) (h : f' = f) : LatticeHom α β :=
  { f.toSupHom.copy f' h, f.toInfHom.copy f' h with }

@[simp]
theorem coe_copy (f : LatticeHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : LatticeHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `LatticeHom`. -/
protected def id : LatticeHom α α where
  toFun := id
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

instance : Inhabited (LatticeHom α α) :=
  ⟨LatticeHom.id α⟩

@[simp, norm_cast]
theorem coe_id : ⇑(LatticeHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : LatticeHom.id α a = a :=
  rfl

/-- Composition of `LatticeHom`s as a `LatticeHom`. -/
def comp (f : LatticeHom β γ) (g : LatticeHom α β) : LatticeHom α γ :=
  { f.toSupHom.comp g.toSupHom, f.toInfHom.comp g.toInfHom with }

@[simp]
theorem coe_comp (f : LatticeHom β γ) (g : LatticeHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : LatticeHom β γ) (g : LatticeHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
-- `simp`-normal form of `coe_comp_sup_hom`
theorem coe_comp_sup_hom' (f : LatticeHom β γ) (g : LatticeHom α β) :
    ⟨f ∘ g, map_sup (f.comp g)⟩ = (f : SupHom β γ).comp g :=
  rfl

theorem coe_comp_sup_hom (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g : SupHom α γ) = (f : SupHom β γ).comp g :=
  rfl

@[simp]
-- `simp`-normal form of `coe_comp_inf_hom`
theorem coe_comp_inf_hom' (f : LatticeHom β γ) (g : LatticeHom α β) :
    ⟨f ∘ g, map_inf (f.comp g)⟩ = (f : InfHom β γ).comp g :=
  rfl

theorem coe_comp_inf_hom (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g : InfHom α γ) = (f : InfHom β γ).comp g :=
  rfl

@[simp]
theorem comp_assoc (f : LatticeHom γ δ) (g : LatticeHom β γ) (h : LatticeHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : LatticeHom α β) : f.comp (LatticeHom.id α) = f :=
  LatticeHom.ext fun _ => rfl

@[simp]
theorem id_comp (f : LatticeHom α β) : (LatticeHom.id β).comp f = f :=
  LatticeHom.ext fun _ => rfl

@[simp]
theorem cancel_right {g₁ g₂ : LatticeHom β γ} {f : LatticeHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => LatticeHom.ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]
theorem cancel_left {g : LatticeHom β γ} {f₁ f₂ : LatticeHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => LatticeHom.ext fun a => hg <| by rw [← LatticeHom.comp_apply, h, LatticeHom.comp_apply],
    congr_arg _⟩

/-- `Subtype.val` as a `LatticeHom`. -/
def subtypeVal {P : β → Prop}
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) :
    letI := Subtype.lattice Psup Pinf
    LatticeHom {x : β // P x} β :=
  letI := Subtype.lattice Psup Pinf
  .mk (SupHom.subtypeVal Psup) (by simp [Subtype.coe_inf Pinf])

@[simp]
lemma subtypeVal_apply {P : β → Prop}
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y))
    (x : {x : β // P x}) :
    subtypeVal Psup Pinf x = x := rfl

@[simp]
lemma subtypeVal_coe {P : β → Prop}
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) :
    ⇑(subtypeVal Psup Pinf) = Subtype.val := rfl

end LatticeHom

namespace OrderHomClass

variable (α β)
variable [LinearOrder α] [Lattice β] [OrderHomClass F α β]

/-- An order homomorphism from a linear order is a lattice homomorphism. -/
instance (priority := 100) toLatticeHomClass : LatticeHomClass F α β :=
  { ‹OrderHomClass F α β› with
    map_sup := fun f a b => by
      obtain h | h := le_total a b
      · rw [sup_eq_right.2 h, sup_eq_right.2 (OrderHomClass.mono f h : f a ≤ f b)]
      · rw [sup_eq_left.2 h, sup_eq_left.2 (OrderHomClass.mono f h : f b ≤ f a)]
    map_inf := fun f a b => by
      obtain h | h := le_total a b
      · rw [inf_eq_left.2 h, inf_eq_left.2 (OrderHomClass.mono f h : f a ≤ f b)]
      · rw [inf_eq_right.2 h, inf_eq_right.2 (OrderHomClass.mono f h : f b ≤ f a)] }

/-- Reinterpret an order homomorphism to a linear order as a `LatticeHom`. -/
def toLatticeHom (f : F) : LatticeHom α β := f

@[simp]
theorem coe_to_lattice_hom (f : F) : ⇑(toLatticeHom α β f) = f :=
  rfl

@[simp]
theorem to_lattice_hom_apply (f : F) (a : α) : toLatticeHom α β f a = f a :=
  rfl

end OrderHomClass

/-! ### Dual homs -/

namespace SupHom

variable [Max α] [Max β] [Max γ]

/-- Reinterpret a supremum homomorphism as an infimum homomorphism between the dual lattices. -/
@[simps]
protected def dual : SupHom α β ≃ InfHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨f, f.map_sup'⟩
  invFun f := ⟨f, f.map_inf'⟩

@[simp]
theorem dual_id : SupHom.dual (SupHom.id α) = InfHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : SupHom β γ) (f : SupHom α β) :
    SupHom.dual (g.comp f) = (SupHom.dual g).comp (SupHom.dual f) :=
  rfl

@[simp]
theorem symm_dual_id : SupHom.dual.symm (InfHom.id _) = SupHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : InfHom βᵒᵈ γᵒᵈ) (f : InfHom αᵒᵈ βᵒᵈ) :
    SupHom.dual.symm (g.comp f) =
      (SupHom.dual.symm g).comp (SupHom.dual.symm f) :=
  rfl

end SupHom

namespace InfHom

variable [Min α] [Min β] [Min γ]

/-- Reinterpret an infimum homomorphism as a supremum homomorphism between the dual lattices. -/
@[simps]
protected def dual : InfHom α β ≃ SupHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨f, f.map_inf'⟩
  invFun f := ⟨f, f.map_sup'⟩

@[simp]
theorem dual_id : InfHom.dual (InfHom.id α) = SupHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : InfHom β γ) (f : InfHom α β) :
    InfHom.dual (g.comp f) = (InfHom.dual g).comp (InfHom.dual f) :=
  rfl

@[simp]
theorem symm_dual_id : InfHom.dual.symm (SupHom.id _) = InfHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : SupHom βᵒᵈ γᵒᵈ) (f : SupHom αᵒᵈ βᵒᵈ) :
    InfHom.dual.symm (g.comp f) =
      (InfHom.dual.symm g).comp (InfHom.dual.symm f) :=
  rfl

end InfHom

namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ]

/-- Reinterpret a lattice homomorphism as a lattice homomorphism between the dual lattices. -/
@[simps]
protected def dual : LatticeHom α β ≃ LatticeHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨InfHom.dual f.toInfHom, f.map_sup'⟩
  invFun f := ⟨SupHom.dual.symm f.toInfHom, f.map_sup'⟩

@[simp] theorem dual_id : LatticeHom.dual (LatticeHom.id α) = LatticeHom.id _ := rfl

@[simp]
theorem dual_comp (g : LatticeHom β γ) (f : LatticeHom α β) :
    LatticeHom.dual (g.comp f) = (LatticeHom.dual g).comp (LatticeHom.dual f) :=
  rfl

@[simp]
theorem symm_dual_id : LatticeHom.dual.symm (LatticeHom.id _) = LatticeHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : LatticeHom βᵒᵈ γᵒᵈ) (f : LatticeHom αᵒᵈ βᵒᵈ) :
    LatticeHom.dual.symm (g.comp f) =
      (LatticeHom.dual.symm g).comp (LatticeHom.dual.symm f) :=
  rfl

end LatticeHom

/-! ### Prod -/

namespace LatticeHom
variable [Lattice α] [Lattice β]

/-- Natural projection homomorphism from `α × β` to `α`. -/
def fst : LatticeHom (α × β) α where
  toFun := Prod.fst
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

/-- Natural projection homomorphism from `α × β` to `β`. -/
def snd : LatticeHom (α × β) β where
  toFun := Prod.snd
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

@[simp, norm_cast] lemma coe_fst : ⇑(fst (α := α) (β := β)) = Prod.fst := rfl
@[simp, norm_cast] lemma coe_snd : ⇑(snd (α := α) (β := β)) = Prod.snd := rfl
lemma fst_apply (x : α × β) : fst x = x.fst := rfl
lemma snd_apply (x : α × β) : snd x = x.snd := rfl

end LatticeHom

/-! ### Pi -/

namespace Pi
variable {ι : Type*} {α : ι → Type*} [∀ i, Lattice (α i)]

/-- Evaluation as a lattice homomorphism. -/
def evalLatticeHom (i : ι) : LatticeHom (∀ i, α i) (α i) where
  toFun := Function.eval i
  map_sup' _a _b := rfl
  map_inf' _a _b := rfl

@[simp, norm_cast]
lemma coe_evalLatticeHom (i : ι) : ⇑(evalLatticeHom (α := α) i) = Function.eval i := rfl

lemma evalLatticeHom_apply (i : ι) (f : ∀ i, α i) : evalLatticeHom i f = f i := rfl

end Pi
