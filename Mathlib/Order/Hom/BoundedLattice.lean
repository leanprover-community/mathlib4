/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Hom.Bounded
public import Mathlib.Order.Hom.Lattice
public import Mathlib.Order.SymmDiff

/-!
# Bounded lattice homomorphisms

This file defines bounded lattice homomorphisms.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `SupBotHom`: Finitary supremum homomorphisms. Maps which preserve `⊔` and `⊥`.
* `InfTopHom`: Finitary infimum homomorphisms. Maps which preserve `⊓` and `⊤`.
* `BoundedLatticeHom`: Bounded lattice homomorphisms. Maps which preserve `⊤`, `⊥`, `⊔` and `⊓`.

## Typeclasses

* `SupBotHomClass`
* `InfTopHomClass`
* `BoundedLatticeHomClass`

## TODO

Do we need more intersections between `BotHom`, `TopHom` and lattice homomorphisms?
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


open Function

variable {F α β γ δ : Type*}

/-- The type of finitary supremum-preserving homomorphisms from `α` to `β`. -/
structure SupBotHom (α β : Type*) [Max α] [Max β] [Bot α] [Bot β]
  extends SupHom α β, BotHom α β where

/-- The type of finitary infimum-preserving homomorphisms from `α` to `β`. -/
@[to_dual]
structure InfTopHom (α β : Type*) [Min α] [Min β] [Top α] [Top β]
  extends InfHom α β, TopHom α β where

attribute [nolint docBlame] SupBotHom.toBotHom InfTopHom.toTopHom

/-- The type of bounded lattice homomorphisms from `α` to `β`. -/
structure BoundedLatticeHom (α β : Type*) [Lattice α] [Lattice β] [BoundedOrder α]
  [BoundedOrder β] extends LatticeHom α β, InfTopHom α β, SupBotHom α β where

attribute [nolint docBlame] BoundedLatticeHom.toInfTopHom BoundedLatticeHom.toSupBotHom

attribute [to_dual self (reorder := map_top' map_bot')] BoundedLatticeHom.mk
attribute [to_dual existing] BoundedLatticeHom.toInfTopHom BoundedLatticeHom.map_top'

section

/-- `SupBotHomClass F α β` states that `F` is a type of finitary supremum-preserving morphisms.

You should extend this class when you extend `SupBotHom`. -/
class SupBotHomClass (F α β : Type*) [Max α] [Max β] [Bot α] [Bot β] [FunLike F α β] : Prop
  extends SupHomClass F α β where
  /-- A `SupBotHomClass` morphism preserves the bottom element. -/
  map_bot (f : F) : f ⊥ = ⊥

/-- `InfTopHomClass F α β` states that `F` is a type of finitary infimum-preserving morphisms.

You should extend this class when you extend `SupBotHom`. -/
@[to_dual]
class InfTopHomClass (F α β : Type*) [Min α] [Min β] [Top α] [Top β] [FunLike F α β] : Prop
  extends InfHomClass F α β where
  /-- An `InfTopHomClass` morphism preserves the top element. -/
  map_top (f : F) : f ⊤ = ⊤

/-- `BoundedLatticeHomClass F α β` states that `F` is a type of bounded lattice morphisms.

You should extend this class when you extend `BoundedLatticeHom`. -/
class BoundedLatticeHomClass (F α β : Type*) [Lattice α] [Lattice β] [BoundedOrder α]
    [BoundedOrder β] [FunLike F α β] : Prop
  extends LatticeHomClass F α β where
  /-- A `BoundedLatticeHomClass` morphism preserves the top element. -/
  map_top (f : F) : f ⊤ = ⊤
  /-- A `BoundedLatticeHomClass` morphism preserves the bottom element. -/
  map_bot (f : F) : f ⊥ = ⊥

attribute [to_dual self (reorder := map_top map_bot)] BoundedLatticeHomClass.mk
attribute [to_dual existing] BoundedLatticeHomClass.map_bot

end

section Hom

variable [FunLike F α β]

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) SupBotHomClass.toBotHomClass [Max α] [Max β] [Bot α]
    [Bot β] [SupBotHomClass F α β] : BotHomClass F α β :=
  { ‹SupBotHomClass F α β› with }

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) BoundedLatticeHomClass.toSupBotHomClass [Lattice α] [Lattice β]
    [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
    SupBotHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with }

-- See note [lower instance priority]
instance (priority := 100) BoundedLatticeHomClass.toBoundedOrderHomClass [Lattice α]
    [Lattice β] [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
    BoundedOrderHomClass F α β :=
{ show OrderHomClass F α β from inferInstance, ‹BoundedLatticeHomClass F α β› with }

end Hom

section Equiv

variable [EquivLike F α β]

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) OrderIsoClass.toSupBotHomClass [SemilatticeSup α] [OrderBot α]
    [SemilatticeSup β] [OrderBot β] [OrderIsoClass F α β] : SupBotHomClass F α β :=
  { OrderIsoClass.toSupHomClass, OrderIsoClass.toBotHomClass with }

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toBoundedLatticeHomClass [Lattice α] [Lattice β]
    [BoundedOrder α] [BoundedOrder β] [OrderIsoClass F α β] :
    BoundedLatticeHomClass F α β :=
  { OrderIsoClass.toLatticeHomClass, OrderIsoClass.toBoundedOrderHomClass with }

end Equiv

section BoundedLattice

variable [Lattice α] [Lattice β] [FunLike F α β]

@[to_dual]
theorem Disjoint.map [OrderBot α] [OrderBot β] [BotHomClass F α β] [InfHomClass F α β] {a b : α}
    (f : F) (h : Disjoint a b) : Disjoint (f a) (f b) := by
  rw [disjoint_iff, ← map_inf, h.eq_bot, map_bot]

theorem IsCompl.map [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] {a b : α}
    (f : F) (h : IsCompl a b) : IsCompl (f a) (f b) :=
  ⟨h.1.map _, h.2.map _⟩

end BoundedLattice

section BooleanAlgebra

variable [BooleanAlgebra α] [BooleanAlgebra β] [FunLike F α β] [BoundedLatticeHomClass F α β]
variable (f : F)

/-- Special case of `map_compl` for Boolean algebras. -/
theorem map_compl' (a : α) : f aᶜ = (f a)ᶜ :=
  (isCompl_compl.map _).compl_eq.symm

/-- Special case of `map_sdiff` for Boolean algebras. -/
theorem map_sdiff' (a b : α) : f (a \ b) = f a \ f b := by
  rw [sdiff_eq, sdiff_eq, map_inf, map_compl']

open scoped symmDiff in
/-- Special case of `map_symmDiff` for Boolean algebras. -/
theorem map_symmDiff' (a b : α) : f (a ∆ b) = f a ∆ f b := by
  rw [symmDiff, symmDiff, map_sup, map_sdiff', map_sdiff']

end BooleanAlgebra

variable [FunLike F α β]

@[to_dual]
instance [Max α] [Max β] [Bot α] [Bot β] [SupBotHomClass F α β] : CoeTC F (SupBotHom α β) :=
  ⟨fun f => ⟨f, map_bot f⟩⟩

instance [Lattice α] [Lattice β] [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
    CoeTC F (BoundedLatticeHom α β) :=
  ⟨fun f =>
    { (f : LatticeHom α β) with
      toFun := f
      map_top' := map_top f
      map_bot' := map_bot f }⟩

/-! ### Finitary supremum homomorphisms -/

namespace SupBotHom

variable [Max α] [Bot α]

section Sup

variable [Max β] [Bot β] [Max γ] [Bot γ] [Max δ] [Bot δ]

@[to_dual]
instance : FunLike (SupBotHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

@[to_dual]
instance : SupBotHomClass (SupBotHom α β) α β where
  map_sup f := f.map_sup'
  map_bot f := f.map_bot'

@[to_dual]
lemma toFun_eq_coe (f : SupBotHom α β) : f.toFun = f := rfl

@[to_dual (attr := simp)] lemma coe_toSupHom (f : SupBotHom α β) : ⇑f.toSupHom = f := rfl
@[to_dual (attr := simp)] lemma coe_toBotHom (f : SupBotHom α β) : ⇑f.toBotHom = f := rfl
@[to_dual (attr := simp)] lemma coe_mk (f : SupHom α β) (hf) : ⇑(mk f hf) = f := rfl

@[to_dual (attr := ext)]
theorem ext {f g : SupBotHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `SupBotHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_dual /--
Copy of an `InfTopHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/]
protected def copy (f : SupBotHom α β) (f' : α → β) (h : f' = f) : SupBotHom α β :=
  { f.toBotHom.copy f' h with toSupHom := f.toSupHom.copy f' h }

@[to_dual (attr := simp)]
theorem coe_copy (f : SupBotHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

@[to_dual]
theorem copy_eq (f : SupBotHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `SupBotHom`. -/
@[to_dual (attr := simps!) /-- `id` as an `InfTopHom`. -/]
protected def id : SupBotHom α α :=
  ⟨SupHom.id α, rfl⟩

@[to_dual]
instance : Inhabited (SupBotHom α α) :=
  ⟨SupBotHom.id α⟩

@[to_dual (attr := simp, norm_cast)]
theorem coe_id : ⇑(SupBotHom.id α) = id :=
  rfl

variable {α}

@[to_dual (attr := simp)]
theorem id_apply (a : α) : SupBotHom.id α a = a :=
  rfl

/-- Composition of `SupBotHom`s as a `SupBotHom`. -/
@[to_dual /-- Composition of `InfTopHom`s as an `InfTopHom`. -/]
def comp (f : SupBotHom β γ) (g : SupBotHom α β) : SupBotHom α γ :=
  { f.toSupHom.comp g.toSupHom, f.toBotHom.comp g.toBotHom with }

@[to_dual (attr := simp)]
theorem coe_comp (f : SupBotHom β γ) (g : SupBotHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[to_dual (attr := simp)]
theorem comp_apply (f : SupBotHom β γ) (g : SupBotHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[to_dual (attr := simp)]
theorem comp_assoc (f : SupBotHom γ δ) (g : SupBotHom β γ) (h : SupBotHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[to_dual (attr := simp)] theorem comp_id (f : SupBotHom α β) : f.comp (SupBotHom.id α) = f := rfl

@[to_dual (attr := simp)] theorem id_comp (f : SupBotHom α β) : (SupBotHom.id β).comp f = f := rfl

@[to_dual (attr := simp)]
theorem cancel_right {g₁ g₂ : SupBotHom β γ} {f : SupBotHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[to_dual (attr := simp)]
theorem cancel_left {g : SupBotHom β γ} {f₁ f₂ : SupBotHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => SupBotHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end Sup

variable [SemilatticeSup β] [OrderBot β]

@[to_dual]
instance : Max (SupBotHom α β) :=
  ⟨fun f g => { f.toBotHom ⊔ g.toBotHom with toSupHom := f.toSupHom ⊔ g.toSupHom }⟩

@[to_dual]
instance : PartialOrder (SupBotHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

@[to_dual]
instance : SemilatticeSup (SupBotHom α β) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ ↦ rfl

@[to_dual]
instance : OrderBot (SupBotHom α β) where
  bot := ⟨⊥, rfl⟩
  bot_le _ _ := bot_le

@[to_dual (attr := simp)]
theorem coe_sup (f g : SupBotHom α β) : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g :=
  rfl

@[to_dual (attr := simp)]
theorem coe_bot : ⇑(⊥ : SupBotHom α β) = ⊥ :=
  rfl

@[to_dual (attr := simp)]
theorem sup_apply (f g : SupBotHom α β) (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl

@[to_dual (attr := simp)]
theorem bot_apply (a : α) : (⊥ : SupBotHom α β) a = ⊥ :=
  rfl

/-- `Subtype.val` as a `SupBotHom`. -/
@[to_dual (rename := Pbot → Ptop, Psup → Pinf) /-- `Subtype.val` as an `InfTopHom`. -/]
def subtypeVal {P : β → Prop}
    (Pbot : P ⊥) (Psup : ∀ ⦃x y : β⦄, P x → P y → P (x ⊔ y)) :
    letI := Subtype.orderBot Pbot
    letI := Subtype.semilatticeSup Psup
    SupBotHom {x : β // P x} β :=
  letI := Subtype.orderBot Pbot
  letI := Subtype.semilatticeSup Psup
  .mk (SupHom.subtypeVal Psup) (by simp [Subtype.coe_bot Pbot])

@[to_dual (attr := simp) (rename := Pbot → Ptop, Psup → Pinf)]
lemma subtypeVal_apply {P : β → Prop}
    (Pbot : P ⊥) (Psup : ∀ ⦃x y : β⦄, P x → P y → P (x ⊔ y)) (x : {x : β // P x}) :
    subtypeVal Pbot Psup x = x := rfl

@[to_dual (attr := simp) (rename := Pbot → Ptop, Psup → Pinf)]
lemma subtypeVal_coe {P : β → Prop}
    (Pbot : P ⊥) (Psup : ∀ ⦃x y : β⦄, P x → P y → P (x ⊔ y)) :
    ⇑(subtypeVal Pbot Psup) = Subtype.val := rfl

end SupBotHom

/-! ### Bounded lattice homomorphisms -/

namespace BoundedLatticeHom

variable [Lattice α] [Lattice β] [Lattice γ] [Lattice δ] [BoundedOrder α] [BoundedOrder β]
  [BoundedOrder γ] [BoundedOrder δ]

/-- Reinterpret a `BoundedLatticeHom` as a `BoundedOrderHom`. -/
def toBoundedOrderHom (f : BoundedLatticeHom α β) : BoundedOrderHom α β :=
  { f, (f.toLatticeHom : α →o β) with }

instance instFunLike : FunLike (BoundedLatticeHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr

instance instBoundedLatticeHomClass : BoundedLatticeHomClass (BoundedLatticeHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
  map_bot f := f.map_bot'

@[simp] lemma toFun_eq_coe (f : BoundedLatticeHom α β) : f.toFun = f := rfl

@[simp] lemma coe_toLatticeHom (f : BoundedLatticeHom α β) : ⇑f.toLatticeHom = f := rfl
@[to_dual (attr := simp)]
lemma coe_toSupBotHom (f : BoundedLatticeHom α β) : ⇑f.toSupBotHom = f := rfl
@[simp] lemma coe_toBoundedOrderHom (f : BoundedLatticeHom α β) : ⇑f.toBoundedOrderHom = f := rfl
@[simp] lemma coe_mk (f : LatticeHom α β) (hf hf') : ⇑(mk f hf hf') = f := rfl

@[ext]
theorem ext {f g : BoundedLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `BoundedLatticeHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : BoundedLatticeHom α β) (f' : α → β) (h : f' = f) : BoundedLatticeHom α β :=
  { f.toLatticeHom.copy f' h, f.toBoundedOrderHom.copy f' h with }

@[simp]
theorem coe_copy (f : BoundedLatticeHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : BoundedLatticeHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `BoundedLatticeHom`. -/
protected def id : BoundedLatticeHom α α :=
  { LatticeHom.id α, BoundedOrderHom.id α with }

instance : Inhabited (BoundedLatticeHom α α) :=
  ⟨BoundedLatticeHom.id α⟩

@[simp, norm_cast]
theorem coe_id : ⇑(BoundedLatticeHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : BoundedLatticeHom.id α a = a :=
  rfl

/-- Composition of `BoundedLatticeHom`s as a `BoundedLatticeHom`. -/
def comp (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) : BoundedLatticeHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom, f.toBoundedOrderHom.comp g.toBoundedOrderHom with }

@[simp]
theorem coe_comp (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) (a : α) :
    (f.comp g) a = f (g a) :=
  rfl

@[simp]
-- `simp`-normal form of `coe_comp_lattice_hom`
theorem coe_comp_lattice_hom' (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (⟨(f : SupHom β γ).comp g, map_inf (f.comp g)⟩ : LatticeHom α γ) =
      (f : LatticeHom β γ).comp g :=
  rfl

theorem coe_comp_lattice_hom (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : LatticeHom α γ) = (f : LatticeHom β γ).comp g :=
  rfl

@[to_dual (attr := simp)]
-- `simp`-normal form of `coe_comp_sup_hom`
theorem coe_comp_sup_hom' (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    ⟨f ∘ g, map_sup (f.comp g)⟩ = (f : SupHom β γ).comp g :=
  rfl

@[to_dual]
theorem coe_comp_sup_hom (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : SupHom α γ) = (f : SupHom β γ).comp g :=
  rfl

@[simp]
theorem comp_assoc (f : BoundedLatticeHom γ δ) (g : BoundedLatticeHom β γ)
    (h : BoundedLatticeHom α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp] theorem comp_id (f : BoundedLatticeHom α β) : f.comp (BoundedLatticeHom.id α) = f := rfl

@[simp] theorem id_comp (f : BoundedLatticeHom α β) : (BoundedLatticeHom.id β).comp f = f := rfl

@[simp]
theorem cancel_right {g₁ g₂ : BoundedLatticeHom β γ} {f : BoundedLatticeHom α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => BoundedLatticeHom.ext <| hf.forall.2 <| DFunLike.ext_iff.1 h,
    fun h => congr_arg₂ _ h rfl⟩

@[simp]
theorem cancel_left {g : BoundedLatticeHom β γ} {f₁ f₂ : BoundedLatticeHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

/-- `Subtype.val` as a `BoundedLatticeHom`. -/
@[to_dual self (reorder := Pbot Ptop, Psup Pinf)]
def subtypeVal {P : β → Prop} (Pbot : P ⊥) (Ptop : P ⊤)
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) :
    letI := Subtype.lattice Psup Pinf
    letI := Subtype.boundedOrder Pbot Ptop
    BoundedLatticeHom {x : β // P x} β :=
  letI := Subtype.lattice Psup Pinf
  letI := Subtype.boundedOrder Pbot Ptop
  .mk (.subtypeVal Psup Pinf) (by simp [Subtype.coe_top Ptop]) (by simp [Subtype.coe_bot Pbot])

@[simp]
lemma subtypeVal_apply {P : β → Prop}
    (Pbot : P ⊥) (Ptop : P ⊤) (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y))
    (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) (x : {x : β // P x}) :
    subtypeVal Pbot Ptop Psup Pinf x = x := rfl

@[simp]
lemma subtypeVal_coe {P : β → Prop} (Pbot : P ⊥) (Ptop : P ⊤)
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) :
    ⇑(subtypeVal Pbot Ptop Psup Pinf) = Subtype.val := rfl

end BoundedLatticeHom

/-! ### Dual homs -/

namespace SupBotHom

variable [Max α] [Bot α] [Max β] [Bot β] [Max γ] [Bot γ]

/-- Reinterpret a finitary supremum homomorphism as a finitary infimum homomorphism between the dual
lattices. -/
@[to_dual /--
Reinterpret a finitary infimum homomorphism as a finitary supremum homomorphism between the dual
lattices. -/]
def dual : SupBotHom α β ≃ InfTopHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨SupHom.dual f.toSupHom, f.map_bot'⟩
  invFun f := ⟨SupHom.dual.symm f.toInfHom, f.map_top'⟩

@[to_dual (attr := simp)] theorem dual_id : SupBotHom.dual (SupBotHom.id α) = InfTopHom.id _ := rfl

@[to_dual (attr := simp)]
theorem dual_comp (g : SupBotHom β γ) (f : SupBotHom α β) :
    SupBotHom.dual (g.comp f) = (SupBotHom.dual g).comp (SupBotHom.dual f) :=
  rfl

@[to_dual (attr := simp)]
theorem symm_dual_id : SupBotHom.dual.symm (InfTopHom.id _) = SupBotHom.id α :=
  rfl

@[to_dual (attr := simp)]
theorem symm_dual_comp (g : InfTopHom βᵒᵈ γᵒᵈ) (f : InfTopHom αᵒᵈ βᵒᵈ) :
    SupBotHom.dual.symm (g.comp f) =
      (SupBotHom.dual.symm g).comp (SupBotHom.dual.symm f) :=
  rfl

end SupBotHom

namespace BoundedLatticeHom

variable [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β] [Lattice γ] [BoundedOrder γ]

/-- Reinterpret a bounded lattice homomorphism as a bounded lattice homomorphism between the dual
bounded lattices. -/
@[simps!]
protected def dual : BoundedLatticeHom α β ≃ BoundedLatticeHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨LatticeHom.dual f.toLatticeHom, f.map_bot', f.map_top'⟩
  invFun f := ⟨LatticeHom.dual.symm f.toLatticeHom, f.map_bot', f.map_top'⟩

@[simp]
theorem dual_id : BoundedLatticeHom.dual (BoundedLatticeHom.id α) = BoundedLatticeHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β) :
    BoundedLatticeHom.dual (g.comp f) =
      (BoundedLatticeHom.dual g).comp (BoundedLatticeHom.dual f) :=
  rfl

@[simp]
theorem symm_dual_id :
    BoundedLatticeHom.dual.symm (BoundedLatticeHom.id _) = BoundedLatticeHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : BoundedLatticeHom βᵒᵈ γᵒᵈ) (f : BoundedLatticeHom αᵒᵈ βᵒᵈ) :
    BoundedLatticeHom.dual.symm (g.comp f) =
      (BoundedLatticeHom.dual.symm g).comp (BoundedLatticeHom.dual.symm f) :=
  rfl

end BoundedLatticeHom
