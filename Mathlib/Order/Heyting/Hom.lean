/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Hom.Lattice

#align_import order.heyting.hom from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# Heyting algebra morphisms

A Heyting homomorphism between two Heyting algebras is a bounded lattice homomorphism that preserves
Heyting implication.

We use the `FunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `HeytingHom`: Heyting homomorphisms.
* `CoheytingHom`: Co-Heyting homomorphisms.
* `BiheytingHom`: Bi-Heyting homomorphisms.

## Typeclasses

* `HeytingHomClass`
* `CoheytingHomClass`
* `BiheytingHomClass`
-/


open Function

variable {F α β γ δ : Type*}

/-- The type of Heyting homomorphisms from `α` to `β`. Bounded lattice homomorphisms that preserve
Heyting implication. -/
structure HeytingHom (α β : Type*) [HeytingAlgebra α] [HeytingAlgebra β] extends
  LatticeHom α β where
  /-- The proposition that a Heyting homomorphism preserves the bottom element.-/
  protected map_bot' : toFun ⊥ = ⊥
  /-- The proposition that a Heyting homomorphism preserves the Heyting implication.-/
  protected map_himp' : ∀ a b, toFun (a ⇨ b) = toFun a ⇨ toFun b
#align heyting_hom HeytingHom

/-- The type of co-Heyting homomorphisms from `α` to `β`. Bounded lattice homomorphisms that
preserve difference. -/
structure CoheytingHom (α β : Type*) [CoheytingAlgebra α] [CoheytingAlgebra β] extends
  LatticeHom α β where
  /-- The proposition that a co-Heyting homomorphism preserves the top element.-/
  protected map_top' : toFun ⊤ = ⊤
  /-- The proposition that a co-Heyting homomorphism preserves the difference operation.-/
  protected map_sdiff' : ∀ a b, toFun (a \ b) = toFun a \ toFun b
#align coheyting_hom CoheytingHom

/-- The type of bi-Heyting homomorphisms from `α` to `β`. Bounded lattice homomorphisms that
preserve Heyting implication and difference. -/
structure BiheytingHom (α β : Type*) [BiheytingAlgebra α] [BiheytingAlgebra β] extends
  LatticeHom α β where
  /-- The proposition that a bi-Heyting homomorphism preserves the Heyting implication.-/
  protected map_himp' : ∀ a b, toFun (a ⇨ b) = toFun a ⇨ toFun b
  /-- The proposition that a bi-Heyting homomorphism preserves the difference operation.-/
  protected map_sdiff' : ∀ a b, toFun (a \ b) = toFun a \ toFun b
#align biheyting_hom BiheytingHom

/-- `HeytingHomClass F α β` states that `F` is a type of Heyting homomorphisms.

You should extend this class when you extend `HeytingHom`. -/
class HeytingHomClass (F : Type*) (α β : outParam <| Type*) [HeytingAlgebra α]
  [HeytingAlgebra β] extends LatticeHomClass F α β where
  /-- The proposition that a Heyting homomorphism preserves the bottom element.-/
  map_bot (f : F) : f ⊥ = ⊥
  /-- The proposition that a Heyting homomorphism preserves the Heyting implication.-/
  map_himp (f : F) : ∀ a b, f (a ⇨ b) = f a ⇨ f b
#align heyting_hom_class HeytingHomClass

/-- `CoheytingHomClass F α β` states that `F` is a type of co-Heyting homomorphisms.

You should extend this class when you extend `CoheytingHom`. -/
class CoheytingHomClass (F : Type*) (α β : outParam <| Type*) [CoheytingAlgebra α]
  [CoheytingAlgebra β] extends LatticeHomClass F α β where
  /-- The proposition that a co-Heyting homomorphism preserves the top element.-/
  map_top (f : F) : f ⊤ = ⊤
  /-- The proposition that a co-Heyting homomorphism preserves the difference operation.-/
  map_sdiff (f : F) : ∀ a b, f (a \ b) = f a \ f b
#align coheyting_hom_class CoheytingHomClass

/-- `BiheytingHomClass F α β` states that `F` is a type of bi-Heyting homomorphisms.

You should extend this class when you extend `BiheytingHom`. -/
class BiheytingHomClass (F : Type*) (α β : outParam <| Type*) [BiheytingAlgebra α]
  [BiheytingAlgebra β] extends LatticeHomClass F α β where
  /-- The proposition that a bi-Heyting homomorphism preserves the Heyting implication.-/
  map_himp (f : F) : ∀ a b, f (a ⇨ b) = f a ⇨ f b
  /-- The proposition that a bi-Heyting homomorphism preserves the difference operation.-/
  map_sdiff (f : F) : ∀ a b, f (a \ b) = f a \ f b
#align biheyting_hom_class BiheytingHomClass

export HeytingHomClass (map_himp)

export CoheytingHomClass (map_sdiff)

attribute [simp] map_himp map_sdiff

/- Porting note: `[HeytingAlgebra α, β]` -> `{ _ : HeytingAlgebra α, β}` as a dangerous instance fix
similar for Coheyting & Biheyting instances -/
-- See note [lower instance priority]
instance (priority := 100) HeytingHomClass.toBoundedLatticeHomClass [HeytingAlgebra α]
    { _ : HeytingAlgebra β} [HeytingHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹HeytingHomClass F α β› with
    map_top := fun f => by rw [← @himp_self α _ ⊥, ← himp_self, map_himp] }
                           -- 🎉 no goals
#align heyting_hom_class.to_bounded_lattice_hom_class HeytingHomClass.toBoundedLatticeHomClass

-- See note [lower instance priority]
instance (priority := 100) CoheytingHomClass.toBoundedLatticeHomClass [CoheytingAlgebra α]
    { _ : CoheytingAlgebra β} [CoheytingHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹CoheytingHomClass F α β› with
    map_bot := fun f => by rw [← @sdiff_self α _ ⊤, ← sdiff_self, map_sdiff] }
                           -- 🎉 no goals
#align coheyting_hom_class.to_bounded_lattice_hom_class CoheytingHomClass.toBoundedLatticeHomClass

-- See note [lower instance priority]
instance (priority := 100) BiheytingHomClass.toHeytingHomClass [BiheytingAlgebra α]
    { _ : BiheytingAlgebra β} [BiheytingHomClass F α β] : HeytingHomClass F α β :=
  { ‹BiheytingHomClass F α β› with
    map_bot := fun f => by rw [← @sdiff_self α _ ⊤, ← sdiff_self, BiheytingHomClass.map_sdiff] }
                           -- 🎉 no goals
#align biheyting_hom_class.to_heyting_hom_class BiheytingHomClass.toHeytingHomClass

-- See note [lower instance priority]
instance (priority := 100) BiheytingHomClass.toCoheytingHomClass [BiheytingAlgebra α]
    { _ : BiheytingAlgebra β} [BiheytingHomClass F α β] : CoheytingHomClass F α β :=
  { ‹BiheytingHomClass F α β› with
    map_top := fun f => by rw [← @himp_self α _ ⊥, ← himp_self, map_himp] }
                           -- 🎉 no goals
#align biheyting_hom_class.to_coheyting_hom_class BiheytingHomClass.toCoheytingHomClass

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toHeytingHomClass [HeytingAlgebra α]
    { _ : HeytingAlgebra β} [OrderIsoClass F α β] : HeytingHomClass F α β :=
  { OrderIsoClass.toBoundedLatticeHomClass with
    map_himp := fun f a b =>
      eq_of_forall_le_iff fun c => by
        simp only [← map_inv_le_iff, le_himp_iff]
        -- ⊢ EquivLike.inv f c ⊓ a ≤ b ↔ EquivLike.inv f (c ⊓ ↑f a) ≤ b
        rw [← OrderIsoClass.map_le_map_iff f]
        -- ⊢ ↑f (EquivLike.inv f c ⊓ a) ≤ ↑f b ↔ EquivLike.inv f (c ⊓ ↑f a) ≤ b
        simp }
        -- 🎉 no goals
#align order_iso_class.to_heyting_hom_class OrderIsoClass.toHeytingHomClass

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toCoheytingHomClass [CoheytingAlgebra α]
    { _ : CoheytingAlgebra β} [OrderIsoClass F α β] : CoheytingHomClass F α β :=
  { OrderIsoClass.toBoundedLatticeHomClass with
    map_sdiff := fun f a b =>
      eq_of_forall_ge_iff fun c => by
        simp only [← le_map_inv_iff, sdiff_le_iff]
        -- ⊢ a ≤ b ⊔ EquivLike.inv f c ↔ a ≤ EquivLike.inv f (↑f b ⊔ c)
        rw [← OrderIsoClass.map_le_map_iff f]
        -- ⊢ ↑f a ≤ ↑f (b ⊔ EquivLike.inv f c) ↔ a ≤ EquivLike.inv f (↑f b ⊔ c)
        simp }
        -- 🎉 no goals
#align order_iso_class.to_coheyting_hom_class OrderIsoClass.toCoheytingHomClass

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toBiheytingHomClass [BiheytingAlgebra α]
    { _ : BiheytingAlgebra β} [OrderIsoClass F α β] : BiheytingHomClass F α β :=
  { OrderIsoClass.toLatticeHomClass with
    map_himp := fun f a b =>
      eq_of_forall_le_iff fun c => by
        simp only [← map_inv_le_iff, le_himp_iff]
        -- ⊢ EquivLike.inv f c ⊓ a ≤ b ↔ EquivLike.inv f (c ⊓ ↑f a) ≤ b
        rw [← OrderIsoClass.map_le_map_iff f]
        -- ⊢ ↑f (EquivLike.inv f c ⊓ a) ≤ ↑f b ↔ EquivLike.inv f (c ⊓ ↑f a) ≤ b
        simp
        -- 🎉 no goals
    map_sdiff := fun f a b =>
      eq_of_forall_ge_iff fun c => by
        simp only [← le_map_inv_iff, sdiff_le_iff]
        -- ⊢ a ≤ b ⊔ EquivLike.inv f c ↔ a ≤ EquivLike.inv f (↑f b ⊔ c)
        rw [← OrderIsoClass.map_le_map_iff f]
        -- ⊢ ↑f a ≤ ↑f (b ⊔ EquivLike.inv f c) ↔ a ≤ EquivLike.inv f (↑f b ⊔ c)
        simp }
        -- 🎉 no goals
#align order_iso_class.to_biheyting_hom_class OrderIsoClass.toBiheytingHomClass

-- Porting note: Revisit this issue to see if it works in Lean 4. -/
-- See note [reducible non instances]
/-- This can't be an instance because of typeclass loops. -/
@[reducible]
def BoundedLatticeHomClass.toBiheytingHomClass [BooleanAlgebra α] [BooleanAlgebra β]
    [BoundedLatticeHomClass F α β] : BiheytingHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with
    map_himp := fun f a b => by rw [himp_eq, himp_eq, map_sup, (isCompl_compl.map _).compl_eq]
                                -- 🎉 no goals
    map_sdiff := fun f a b => by rw [sdiff_eq, sdiff_eq, map_inf, (isCompl_compl.map _).compl_eq] }
                                 -- 🎉 no goals
#align bounded_lattice_hom_class.to_biheyting_hom_class BoundedLatticeHomClass.toBiheytingHomClass

section HeytingAlgebra

variable [HeytingAlgebra α] [HeytingAlgebra β] [HeytingHomClass F α β] (f : F)

@[simp]
theorem map_compl (a : α) : f aᶜ = (f a)ᶜ := by rw [← himp_bot, ← himp_bot, map_himp, map_bot]
                                                -- 🎉 no goals
#align map_compl map_compl

@[simp]
theorem map_bihimp (a b : α) : f (a ⇔ b) = f a ⇔ f b := by simp_rw [bihimp, map_inf, map_himp]
                                                           -- 🎉 no goals
#align map_bihimp map_bihimp

-- TODO: `map_bihimp`
end HeytingAlgebra

section CoheytingAlgebra

variable [CoheytingAlgebra α] [CoheytingAlgebra β] [CoheytingHomClass F α β] (f : F)

@[simp]
theorem map_hnot (a : α) : f (￢a) = ￢f a := by rw [← top_sdiff', ← top_sdiff', map_sdiff, map_top]
                                               -- 🎉 no goals
#align map_hnot map_hnot

@[simp]
theorem map_symmDiff (a b : α) : f (a ∆ b) = f a ∆ f b := by simp_rw [symmDiff, map_sup, map_sdiff]
                                                             -- 🎉 no goals
#align map_symm_diff map_symmDiff

end CoheytingAlgebra

instance [HeytingAlgebra α] [HeytingAlgebra β] [HeytingHomClass F α β] : CoeTC F (HeytingHom α β) :=
  ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f
      map_bot' := map_bot f
      map_himp' := map_himp f }⟩

instance [CoheytingAlgebra α] [CoheytingAlgebra β] [CoheytingHomClass F α β] :
    CoeTC F (CoheytingHom α β) :=
  ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f
      map_top' := map_top f
      map_sdiff' := map_sdiff f }⟩

instance [BiheytingAlgebra α] [BiheytingAlgebra β] [BiheytingHomClass F α β] :
    CoeTC F (BiheytingHom α β) :=
  ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f
      map_himp' := map_himp f
      map_sdiff' := map_sdiff f }⟩

namespace HeytingHom

variable [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra γ] [HeytingAlgebra δ]

instance instHeytingHomClass : HeytingHomClass (HeytingHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr
                             -- ⊢ { toLatticeHom := { toSupHom := { toFun := toFun✝, map_sup' := map_sup'✝ },  …
                                                           -- ⊢ { toLatticeHom := { toSupHom := { toFun := toFun✝¹, map_sup' := map_sup'✝¹ } …
                                                                                         -- 🎉 no goals
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_bot f := f.map_bot'
  map_himp := HeytingHom.map_himp'


-- Porting note: CoeFun undesired here in lean 4
-- /-- Helper instance for when there's too many metavariables to apply `FunLike.CoeFun`
-- directly. -/
-- instance : CoeFun (HeytingHom α β) fun _ => α → β :=
--   FunLike.hasCoeToFun

-- @[simp] -- Porting note: not in simp-nf, simp can simplify lhs. Added aux simp lemma
theorem toFun_eq_coe {f : HeytingHom α β} : f.toFun = ⇑f :=
  rfl
#align heyting_hom.to_fun_eq_coe HeytingHom.toFun_eq_coe

@[simp]
theorem toFun_eq_coe_aux {f : HeytingHom α β} : (↑f.toLatticeHom) = ⇑f :=
  rfl

@[ext]
theorem ext {f g : HeytingHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align heyting_hom.ext HeytingHom.ext

/-- Copy of a `HeytingHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : HeytingHom α β) (f' : α → β) (h : f' = f) : HeytingHom α β where
  toFun := f'
  map_sup' := by simpa only [h] using map_sup f
                 -- 🎉 no goals
  map_inf' := by simpa only [h] using map_inf f
                 -- 🎉 no goals
  map_bot' := by simpa only [h] using map_bot f
                 -- 🎉 no goals
  map_himp' := by simpa only [h] using map_himp f
                  -- 🎉 no goals
#align heyting_hom.copy HeytingHom.copy

@[simp]
theorem coe_copy (f : HeytingHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align heyting_hom.coe_copy HeytingHom.coe_copy

theorem copy_eq (f : HeytingHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align heyting_hom.copy_eq HeytingHom.copy_eq

variable (α)

/-- `id` as a `HeytingHom`. -/
protected def id : HeytingHom α α :=
  { BotHom.id _ with
    toLatticeHom := LatticeHom.id _
    map_himp' := fun _ _ => rfl }
#align heyting_hom.id HeytingHom.id

@[simp]
theorem coe_id : ⇑(HeytingHom.id α) = id :=
  rfl
#align heyting_hom.coe_id HeytingHom.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : HeytingHom.id α a = a :=
  rfl
#align heyting_hom.id_apply HeytingHom.id_apply

instance : Inhabited (HeytingHom α α) :=
  ⟨HeytingHom.id _⟩

instance : PartialOrder (HeytingHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

/-- Composition of `HeytingHom`s as a `HeytingHom`. -/
def comp (f : HeytingHom β γ) (g : HeytingHom α β) : HeytingHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_bot' := by simp
                   -- 🎉 no goals
    map_himp' := fun a b => by simp }
                               -- 🎉 no goals
#align heyting_hom.comp HeytingHom.comp

variable {f f₁ f₂ : HeytingHom α β} {g g₁ g₂ : HeytingHom β γ}

@[simp]
theorem coe_comp (f : HeytingHom β γ) (g : HeytingHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align heyting_hom.coe_comp HeytingHom.coe_comp

@[simp]
theorem comp_apply (f : HeytingHom β γ) (g : HeytingHom α β) (a : α) : f.comp g a = f (g a) :=
  rfl
#align heyting_hom.comp_apply HeytingHom.comp_apply

@[simp]
theorem comp_assoc (f : HeytingHom γ δ) (g : HeytingHom β γ) (h : HeytingHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align heyting_hom.comp_assoc HeytingHom.comp_assoc

@[simp]
theorem comp_id (f : HeytingHom α β) : f.comp (HeytingHom.id α) = f :=
  ext fun _ => rfl
#align heyting_hom.comp_id HeytingHom.comp_id

@[simp]
theorem id_comp (f : HeytingHom α β) : (HeytingHom.id β).comp f = f :=
  ext fun _ => rfl
#align heyting_hom.id_comp HeytingHom.id_comp

theorem cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩
#align heyting_hom.cancel_right HeytingHom.cancel_right

theorem cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => HeytingHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
                                             -- 🎉 no goals
#align heyting_hom.cancel_left HeytingHom.cancel_left

end HeytingHom

namespace CoheytingHom

variable [CoheytingAlgebra α] [CoheytingAlgebra β] [CoheytingAlgebra γ] [CoheytingAlgebra δ]

instance : CoheytingHomClass (CoheytingHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr
                             -- ⊢ { toLatticeHom := { toSupHom := { toFun := toFun✝, map_sup' := map_sup'✝ },  …
                                                           -- ⊢ { toLatticeHom := { toSupHom := { toFun := toFun✝¹, map_sup' := map_sup'✝¹ } …
                                                                                         -- 🎉 no goals
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
  map_sdiff := CoheytingHom.map_sdiff'

-- Porting note: CoeFun undesired here in lean 4
-- /-- Helper instance for when there's too many metavariables to apply `FunLike.CoeFun`
-- directly. -/
-- instance : CoeFun (CoheytingHom α β) fun _ => α → β :=
--   FunLike.hasCoeToFun


-- @[simp] -- Porting note: not in simp-nf, simp can simplify lhs. Added aux simp lemma
theorem toFun_eq_coe {f : CoheytingHom α β} : f.toFun = (f : α → β) :=
  rfl
#align coheyting_hom.to_fun_eq_coe CoheytingHom.toFun_eq_coe

@[simp]
theorem toFun_eq_coe_aux {f : CoheytingHom α β} : (↑f.toLatticeHom) = ⇑f :=
  rfl

@[ext]
theorem ext {f g : CoheytingHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align coheyting_hom.ext CoheytingHom.ext

/-- Copy of a `CoheytingHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : CoheytingHom α β) (f' : α → β) (h : f' = f) : CoheytingHom α β where
  toFun := f'
  map_sup' := by simpa only [h] using map_sup f
                 -- 🎉 no goals
  map_inf' := by simpa only [h] using map_inf f
                 -- 🎉 no goals
  map_top' := by simpa only [h] using map_top f
                 -- 🎉 no goals
  map_sdiff' := by simpa only [h] using map_sdiff f
                   -- 🎉 no goals
#align coheyting_hom.copy CoheytingHom.copy

@[simp]
theorem coe_copy (f : CoheytingHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align coheyting_hom.coe_copy CoheytingHom.coe_copy

theorem copy_eq (f : CoheytingHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align coheyting_hom.copy_eq CoheytingHom.copy_eq

variable (α)

/-- `id` as a `CoheytingHom`. -/
protected def id : CoheytingHom α α :=
  { TopHom.id _ with
    toLatticeHom := LatticeHom.id _
    map_sdiff' := fun _ _ => rfl }
#align coheyting_hom.id CoheytingHom.id

@[simp]
theorem coe_id : ⇑(CoheytingHom.id α) = id :=
  rfl
#align coheyting_hom.coe_id CoheytingHom.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : CoheytingHom.id α a = a :=
  rfl
#align coheyting_hom.id_apply CoheytingHom.id_apply

instance : Inhabited (CoheytingHom α α) :=
  ⟨CoheytingHom.id _⟩

instance : PartialOrder (CoheytingHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

/-- Composition of `CoheytingHom`s as a `CoheytingHom`. -/
def comp (f : CoheytingHom β γ) (g : CoheytingHom α β) : CoheytingHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_top' := by simp
                   -- 🎉 no goals
    map_sdiff' := fun a b => by simp }
                                -- 🎉 no goals
#align coheyting_hom.comp CoheytingHom.comp

variable {f f₁ f₂ : CoheytingHom α β} {g g₁ g₂ : CoheytingHom β γ}

@[simp]
theorem coe_comp (f : CoheytingHom β γ) (g : CoheytingHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align coheyting_hom.coe_comp CoheytingHom.coe_comp

@[simp]
theorem comp_apply (f : CoheytingHom β γ) (g : CoheytingHom α β) (a : α) : f.comp g a = f (g a) :=
  rfl
#align coheyting_hom.comp_apply CoheytingHom.comp_apply

@[simp]
theorem comp_assoc (f : CoheytingHom γ δ) (g : CoheytingHom β γ) (h : CoheytingHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align coheyting_hom.comp_assoc CoheytingHom.comp_assoc

@[simp]
theorem comp_id (f : CoheytingHom α β) : f.comp (CoheytingHom.id α) = f :=
  ext fun _ => rfl
#align coheyting_hom.comp_id CoheytingHom.comp_id

@[simp]
theorem id_comp (f : CoheytingHom α β) : (CoheytingHom.id β).comp f = f :=
  ext fun _ => rfl
#align coheyting_hom.id_comp CoheytingHom.id_comp

theorem cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩
#align coheyting_hom.cancel_right CoheytingHom.cancel_right

theorem cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => CoheytingHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
                                               -- 🎉 no goals
#align coheyting_hom.cancel_left CoheytingHom.cancel_left

end CoheytingHom

namespace BiheytingHom

variable [BiheytingAlgebra α] [BiheytingAlgebra β] [BiheytingAlgebra γ] [BiheytingAlgebra δ]

instance : BiheytingHomClass (BiheytingHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr
                             -- ⊢ { toLatticeHom := { toSupHom := { toFun := toFun✝, map_sup' := map_sup'✝ },  …
                                                           -- ⊢ { toLatticeHom := { toSupHom := { toFun := toFun✝¹, map_sup' := map_sup'✝¹ } …
                                                                                         -- 🎉 no goals
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_himp f := f.map_himp'
  map_sdiff f := f.map_sdiff'

-- Porting note: CoeFun undesired here in lean 4
-- /-- Helper instance for when there's too many metavariables to apply `FunLike.CoeFun`
-- directly. -/
-- instance : CoeFun (BiheytingHom α β) fun _ => α → β :=
--   FunLike.hasCoeToFun

-- @[simp] -- Porting note: not in simp-nf, simp can simplify lhs. Added aux simp lemma
theorem toFun_eq_coe {f : BiheytingHom α β} : f.toFun = (f : α → β) :=
  rfl
#align biheyting_hom.to_fun_eq_coe BiheytingHom.toFun_eq_coe

@[simp]
theorem toFun_eq_coe_aux {f : BiheytingHom α β} : (↑f.toLatticeHom) = ⇑f :=
  rfl

@[ext]
theorem ext {f g : BiheytingHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align biheyting_hom.ext BiheytingHom.ext

/-- Copy of a `BiheytingHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : BiheytingHom α β) (f' : α → β) (h : f' = f) : BiheytingHom α β where
  toFun := f'
  map_sup' := by simpa only [h] using map_sup f
                 -- 🎉 no goals
  map_inf' := by simpa only [h] using map_inf f
                 -- 🎉 no goals
  map_himp' := by simpa only [h] using map_himp f
                  -- 🎉 no goals
  map_sdiff' := by simpa only [h] using map_sdiff f
                   -- 🎉 no goals
#align biheyting_hom.copy BiheytingHom.copy

@[simp]
theorem coe_copy (f : BiheytingHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align biheyting_hom.coe_copy BiheytingHom.coe_copy

theorem copy_eq (f : BiheytingHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align biheyting_hom.copy_eq BiheytingHom.copy_eq

variable (α)

/-- `id` as a `BiheytingHom`. -/
protected def id : BiheytingHom α α :=
  { HeytingHom.id _, CoheytingHom.id _ with toLatticeHom := LatticeHom.id _ }
#align biheyting_hom.id BiheytingHom.id

@[simp]
theorem coe_id : ⇑(BiheytingHom.id α) = id :=
  rfl
#align biheyting_hom.coe_id BiheytingHom.coe_id

variable {α}

@[simp]
theorem id_apply (a : α) : BiheytingHom.id α a = a :=
  rfl
#align biheyting_hom.id_apply BiheytingHom.id_apply

instance : Inhabited (BiheytingHom α α) :=
  ⟨BiheytingHom.id _⟩

instance : PartialOrder (BiheytingHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

/-- Composition of `BiheytingHom`s as a `BiheytingHom`. -/
def comp (f : BiheytingHom β γ) (g : BiheytingHom α β) : BiheytingHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_himp' := fun a b => by simp
                               -- 🎉 no goals
    map_sdiff' := fun a b => by simp }
                                -- 🎉 no goals
#align biheyting_hom.comp BiheytingHom.comp

variable {f f₁ f₂ : BiheytingHom α β} {g g₁ g₂ : BiheytingHom β γ}

@[simp]
theorem coe_comp (f : BiheytingHom β γ) (g : BiheytingHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align biheyting_hom.coe_comp BiheytingHom.coe_comp

@[simp]
theorem comp_apply (f : BiheytingHom β γ) (g : BiheytingHom α β) (a : α) : f.comp g a = f (g a) :=
  rfl
#align biheyting_hom.comp_apply BiheytingHom.comp_apply

@[simp]
theorem comp_assoc (f : BiheytingHom γ δ) (g : BiheytingHom β γ) (h : BiheytingHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align biheyting_hom.comp_assoc BiheytingHom.comp_assoc

@[simp]
theorem comp_id (f : BiheytingHom α β) : f.comp (BiheytingHom.id α) = f :=
  ext fun _ => rfl
#align biheyting_hom.comp_id BiheytingHom.comp_id

@[simp]
theorem id_comp (f : BiheytingHom α β) : (BiheytingHom.id β).comp f = f :=
  ext fun _ => rfl
#align biheyting_hom.id_comp BiheytingHom.id_comp

theorem cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩
#align biheyting_hom.cancel_right BiheytingHom.cancel_right

theorem cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => BiheytingHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
                                               -- 🎉 no goals
#align biheyting_hom.cancel_left BiheytingHom.cancel_left

end BiheytingHom
