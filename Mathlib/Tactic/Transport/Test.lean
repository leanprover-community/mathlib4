/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.Transport.Core
public import Mathlib.Topology.Continuous

/-!
## haha
-/

public section

/-
How to transfer from `Set` to `Finset`?
- In a `∀ s : Finset α`, we set `s' := (↑s : Set α)`, so `s'` relates to `s`
- In `_ = _`, `_ ⊆ _`, `_ ⊂ _`, `_.Nonempty`, `_.card`, `x ∈ _`, rewrite with the relevant theorem,
  to generate a goal `_ ~ ?_`
- Fill in `{a} ~ {a}`, `∅ ~ ∅`, `s.insert a ~ s.insert a`, `s.image f ~ s.image f`,
  union, intersection, set difference

-/

attribute [transport] mt Or.imp -- exists_imp forall_imp
  Mathlib.Tactic.GCongr.imp_mono Mathlib.Tactic.GCongr.and_mono

namespace TransportTest

section MapClass

variable {α β : Type*}

/-
-- Injecion: `Finset` to `Set`, `Nat` to `Int`
-- Surjection: `Nat` to `ZMod`, quotients.

-/

class Transport {α β : Type*} (r : outParam <| α → β → Prop)

-- instance (α β : Type*) {r : α → β → Prop} [Transport (fun x y ↦ r y x)] : Transport r where

section

class SurjClass (α β : Type*) {r : α → β → Prop} [Transport r] where
  surj (β) (a : α) : ∃ b : β, r a b

class SurjClass' (α β : Type*) {r : α → β → Prop} [Transport r] where
  surj (α) (b : β) : ∃ a : α, r a b

variable {α β : Type*} {r : α → β → Prop} [Transport r]

variable (β) in
lemma surj [SurjClass α β] (a : α) : ∃ b : β, r a b := SurjClass.surj β a
variable (α) in
lemma surj' [SurjClass' α β] (b : β) : ∃ a : α, r a b := SurjClass'.surj α b

variable {p : α → Prop} {q : β → Prop}

@[transport intro]
theorem forall_transport [SurjClass α β]
    (h : ∀ a b, r a b → q b → p a) :
    (∀ b, q b) → (∀ a, p a) :=
  fun h' a ↦ (surj β a).rec fun b hb ↦ h a b hb (h' b)

-- @[transport intro]
theorem forall_transport' [SurjClass' α β]
    (h : ∀ a b, r a b → p a → q b) :
    (∀ a, p a) → (∀ b, q b) :=
  fun h' b ↦ (surj' α b).rec fun a ha ↦ h a b ha (h' a)

@[transport intro]
theorem forall_transport_eq [SurjClass α β] [SurjClass' α β]
    (h : ∀ a b, r a b → p a = q b) :
    (∀ a, p a) = (∀ b, q b) :=
  propext ⟨forall_transport' (h · · · |>.mp), forall_transport (h · · · |>.mpr)⟩

@[transport intro]
theorem exists_transport [SurjClass α β]
    (h : ∀ a b, r a b → p a → q b) :
    (∃ a, p a) → (∃ b, q b) :=
  fun ⟨a, ha⟩ ↦ (surj β a).rec fun b hb ↦ ⟨b, h a b hb ha⟩

-- @[transport intro]
theorem exists_transport' [SurjClass' α β]
    (h : ∀ a b, r a b → q b → p a) :
    (∃ b, q b) → (∃ a, p a) :=
  fun ⟨b, hb⟩ ↦ (surj' α b).rec fun a ha ↦ ⟨a, h a b ha hb⟩

@[transport intro]
theorem exists_transport_eq [SurjClass α β] [SurjClass' α β]
    (h : ∀ a b, r a b → p a = q b) :
    (∃ a, p a) = (∃ b, q b) :=
  propext ⟨exists_transport (h · · · |>.mp), exists_transport' (h · · · |>.mpr)⟩

end

section

class InjClass (α β : Type*) {r : α → β → Prop} [Transport r] where
  inj {a b b'} : r a b → r a b' → b = b'

class InjClass' (α β : Type*) {r : α → β → Prop} [Transport r] where
  inj {a a' b} : r a b → r a' b → a = a'

variable {α β : Type*} {r : α → β → Prop} [Transport r]

lemma inj [InjClass α β] {a : α} {b b' : β} (h : r a b) (h' : r a b') : b = b' :=
  InjClass.inj h h'

lemma inj' [InjClass' α β] {a a' : α} {b : β} (h : r a b) (h' : r a' b) : a = a' :=
  InjClass'.inj h h'

variable {p : α → Sort*} {q : β → Sort*}

variable {α β : Type*} {r : α → β → Prop} [Transport r]

@[transport intro]
theorem eq_transport [InjClass α β]
    {a a' : α} {b b' : β}
    (h : r a b) (h' : r a' b') : a = a' → b = b' := by
  rintro rfl
  exact inj h h'

@[transport intro]
theorem eq_transport' [InjClass' α β]
    {a a' : α} {b b' : β}
    (h : r a b) (h' : r a' b') : b = b' → a = a' := by
  rintro rfl
  exact inj' h h'

@[transport intro]
theorem eq_transport_eq [InjClass α β] [InjClass' α β]
    {a a' : α} {b b' : β}
    (h : r a b) (h' : r a' b') : (a = a') = (b = b') :=
  propext ⟨eq_transport h h', eq_transport' h h'⟩

@[transport intro]
theorem ne_transport [InjClass α β]
    {a a' : α} {b b' : β}
    (h : r a b) (h' : r a' b') : b ≠ b' → a ≠ a' := by
  contrapose
  exact eq_transport h h'

@[transport intro]
theorem ne_transport' [InjClass' α β]
    {a a' : α} {b b' : β}
    (h : r a b) (h' : r a' b') : a ≠ a' → b ≠ b' := by
  contrapose
  exact eq_transport' h h'

@[transport intro]
theorem ne_transport_eq [InjClass α β] [InjClass' α β]
    {a a' : α} {b b' : β}
    (h : r a b) (h' : r a' b') : (a ≠ a') = (b ≠ b') :=
  (eq_transport_eq h h').to_iff.ne.eq

end

class MapTransport {α β : Type*} (r : outParam <| α → β → Prop) (map : outParam <| α → β)

variable (α β : Type*) {r : α → β → Prop} {map : α → β}

instance [MapTransport r map] : Transport r where

class SemiMapClass [MapTransport r map] where
  rel_map (a) : r a (map a)

variable [MapTransport r map]

class MapClass extends SemiMapClass α β where
  map_eq_of_rel {a b} : r a b → map a = b

class InjMapClass extends MapClass α β where
  map_injective : Function.Injective map

class SurjMapClass extends MapClass α β where
  map_surjective : Function.Surjective map

class EquivMapClass extends InjMapClass α β, SurjMapClass α β

variable {α β}

lemma rel_map [SemiMapClass α β] (a) : r a (map a) := SemiMapClass.rel_map a
lemma map_eq_of_rel [MapClass α β] {a b} : r a b → map a = b := MapClass.map_eq_of_rel
lemma map_injective [InjMapClass α β] : Function.Injective map := InjMapClass.map_injective r
variable (α) in
lemma map_surjective [SurjMapClass α β] : Function.Surjective map := SurjMapClass.map_surjective r
lemma map_bijective [EquivMapClass α β] : Function.Bijective map :=
  ⟨map_injective, map_surjective α⟩

instance [SemiMapClass α β] : SurjClass α β where
  surj a := ⟨map a, rel_map a⟩

instance [SurjMapClass α β] : SurjClass' α β where
  surj b := by rcases map_surjective α b with ⟨b, rfl⟩; use b, rel_map b

instance [MapClass α β] : InjClass α β where
  inj h h' := by rw [← map_eq_of_rel h, ← map_eq_of_rel h']

instance [InjMapClass α β] : InjClass' α β where
  inj h h' := map_injective <| (map_eq_of_rel h).trans (map_eq_of_rel h').symm

instance [MapClass α β] [SurjClass' α β] : SurjMapClass α β where
  map_surjective b := by
    rcases surj' α b with ⟨a, ha⟩
    use a, map_eq_of_rel ha

instance [MapClass α β] [InjClass' α β] : InjMapClass α β where
  map_injective a a' h :=
    inj' (b := map a) (rel_map a) (h ▸ rel_map a')


instance : MapTransport (@Eq α) (·) where

instance : EquivMapClass α α where
  rel_map _ := rfl
  map_eq_of_rel := id
  map_injective := Function.injective_id
  map_surjective := Function.surjective_id


end MapClass

def MapRel {α β : Type*} (map : α → β) (a : α) (b : β) : Prop := map a = b

namespace MapRel

variable {α β : Type*} {map : α → β} [MapTransport (MapRel map) map]

instance : MapClass α β where
  rel_map _ := by rfl
  map_eq_of_rel := by exact id

theorem instInjMapClass (h : Function.Injective map) : InjMapClass α β :=
  ⟨by exact h⟩

theorem instSurjMapClass (h : Function.Surjective map) : SurjMapClass α β :=
  ⟨by exact h⟩

end MapRel

section Option

variable {α β α' β' : Type*}

inductive OptionRel (r : α → β → Prop) : Option α → Option β → Prop where
  | none : OptionRel r none none
  | some {a b} : r a b → OptionRel r (some a) (some b)

variable (r : α → β → Prop)

instance [Transport r] : Transport (OptionRel r) where

instance [Transport r] [SurjClass α β] : SurjClass (Option α) (Option β) where
  surj
    | none => ⟨none, .none⟩
    | some a => (surj β a).rec fun b hb ↦ ⟨some b, .some hb⟩

instance [Transport r] [SurjClass' α β] : SurjClass' (Option α) (Option β) where
  surj
    | none => ⟨none, .none⟩
    | some b => (surj' α b).rec fun a ha ↦ ⟨some a, .some ha⟩

instance [Transport r] [InjClass α β] : InjClass (Option α) (Option β) where
  inj
    | .none, .none => congr(none)
    | .some h₁, .some h₂ => congr(some $(inj h₁ h₂))

instance [Transport r] [InjClass' α β] : InjClass' (Option α) (Option β) where
  inj
    | .none, .none => congr(none)
    | .some h₁, .some h₂ => congr(some $(inj' h₁ h₂))

-- variable {map : α → β}

-- instance [MapTransport r map] : MapTransport (OptionRel r) (.map map) where

-- instance [MapTransport r map] [SemiMapClass α β] : SemiMapClass (Option α) (Option β) where
--   rel_map
--     | none => .none
--     | some a => .some (rel_map a)

-- instance [MapTransport r map] [MapClass α β] : MapClass (Option α) (Option β) where
--   map_eq_of_rel
--     | .none => congr(none)
--     | .some h => congr(some $(map_eq_of_rel h))

@[transport] -- TODO: variable name of `x`/`y` is not preserved
theorem Option.elim_transport {r : α → β → Prop} {r' : α' → β' → Prop}
    {o : Option α} {o' : Option β} (ho : OptionRel r o o')
    {x : α'} {x' : β'} (hx : r' x x')
    {f : α → α'} {f' : β → β'} (hf : ∀ (x y), r x y → r' (f x) (f' y)) :
    r' (o.elim x f) (o'.elim x' f') :=
  ho.casesOn hx (hf _ _)


end Option

section Prod

variable {α α' β β' : Type*}

structure ProdRel (r : α → β → Prop) (r' : α' → β' → Prop) (a : α × α') (b : β × β') : Prop where
  left : r a.1 b.1
  right : r' a.2 b.2

variable (r : α → β → Prop) (r' : α' → β' → Prop)

instance [Transport r] [Transport r'] : Transport (ProdRel r r') where

instance [Transport r] [Transport r'] [SurjClass α β] [SurjClass α' β'] :
    SurjClass (α × α') (β × β') where
  surj | (a, a') => (surj β a).rec fun b hb ↦ (surj β' a').rec fun b' hb' ↦ ⟨(b, b'), ⟨hb, hb'⟩⟩

instance [Transport r] [Transport r'] [SurjClass' α β] [SurjClass' α' β'] :
    SurjClass' (α × α') (β × β') where
  surj | (b, b') => (surj' α b).rec fun a ha ↦ (surj' α' b').rec fun a' ha' ↦ ⟨(a, a'), ⟨ha, ha'⟩⟩

instance [Transport r] [Transport r'] [InjClass α β] [InjClass α' β'] :
    InjClass (α × α') (β × β') where
  inj | ⟨h₁, h₁'⟩, ⟨h₂, h₂'⟩ => congr(($(inj h₁ h₂), $(inj h₁' h₂')))

instance [Transport r] [Transport r'] [InjClass' α β] [InjClass' α' β'] :
    InjClass' (α × α') (β × β') where
  inj | ⟨h₁, h₁'⟩, ⟨h₂, h₂'⟩ => congr(($(inj' h₁ h₂), $(inj' h₁' h₂')))

-- variable {map : α → β} {map' : α' → β'}

-- instance [MapTransport r map] [MapTransport r' map'] :
--     MapTransport (ProdRel r r') (.map map map') where

-- variable [MapTransport r map] [MapTransport r' map']

-- instance [SemiMapClass α β] [SemiMapClass α' β'] : SemiMapClass (α × α') (β × β') where
--   rel_map | (a, b) => ⟨rel_map a, rel_map b⟩

-- instance [MapClass α β] [MapClass α' β'] : MapClass (α × α') (β × β') where
--   map_eq_of_rel | ⟨h, h'⟩ => congr(⟨$(map_eq_of_rel h), $(map_eq_of_rel h')⟩)

end Prod

section Function

variable {α β : Type*} {γ : β → Type*} {δ : α → Type*}
variable (r : α → β → Prop) (r' : ∀ {a b}, γ b → δ a → Prop)

instance [Transport r] [∀ a b, Transport (@r' a b)] : Transport (FunctionRel r @r') where

instance [Transport r] [∀ a b, Transport (@r' a b)]
    [InjClass α β] [SurjClass α β] [∀ a b, SurjClass (γ b) (δ a)] :
    SurjClass (Π b, γ b) (Π a, δ a) where
  surj g := by
    choose x hx using fun a : α ↦ surj β a
    choose y hy using fun {a b} ↦ fun c : γ b ↦ surj (δ a) c
    use (y <| g <| x ·)
    intro a b h
    dsimp
    rw [inj (hx a) h]
    exact hy (g b)

instance [Transport r] [∀ a b, Transport (@r' a b)]
    [InjClass' α β] [SurjClass' α β] [∀ a b, SurjClass' (γ b) (δ a)] :
    SurjClass' (Π b, γ b) (Π a, δ a) where
  surj g := by
    choose x hx using fun b : β ↦ surj' α b
    choose y hy using fun {a b} ↦ fun d : δ a ↦ surj' (γ b) d
    use (y <| g <| x ·)
    intro a b h
    dsimp
    rw [inj' (hx b) h]
    exact hy (g a)

instance [Transport r] [∀ a b, Transport (@r' a b)] [SurjClass α β] [∀ a b, InjClass (γ b) (δ a)] :
    InjClass (Π b, γ b) (Π a, δ a) where
  inj h h' := by
    ext a
    rcases surj β a with ⟨b, hb⟩
    apply inj (h hb) (h' hb)

instance [Transport r] [∀ a b, Transport (@r' a b)] [SurjClass' α β] [∀ a b, InjClass' (γ b) (δ a)] :
    InjClass' (Π b, γ b) (Π a, δ a) where
  inj h h' := by
    ext b
    rcases surj' α b with ⟨a, ha⟩
    exact inj' (h ha) (h' ha)

variable {map : α → β} {map' : ∀ {a b}, γ b → δ a}

instance [MapTransport r map] [∀ a b, MapTransport (@r' a b) map'] :
    MapTransport (FunctionRel r @r') (fun f a ↦ map' (f (map a))) where

variable [MapTransport r map] [∀ a b, MapTransport (@r' a b) map']

instance [MapClass α β] [∀ a b, SemiMapClass (γ b) (δ a)] : SemiMapClass (Π b, γ b) (Π a, δ a) where
  rel_map g := by
    intro a b h
    dsimp
    rw [map_eq_of_rel h]
    apply rel_map

instance [MapClass α β] [∀ a b, MapClass (γ b) (δ a)] : MapClass (Π b, γ b) (Π a, δ a) where
  map_eq_of_rel {g f} h := by
    ext a
    exact map_eq_of_rel (h (rel_map a))

end Function

section Set

variable {α β : Type*}

def SetRel (r : α → β → Prop) (t : Set β) (s : Set α) : Prop :=
  ∀ {a b}, r a b → (a ∈ s) = (b ∈ t)

variable (r : α → β → Prop)

instance [Transport r] : Transport (SetRel r) where

instance [Transport r] [InjClass α β] [SurjClass α β] : SurjClass (Set β) (Set α) where
  surj s := by
    choose f hf using fun a : α ↦ surj β a
    use {x | f x ∈ s}
    intro a b h
    exact congr($(inj (hf a) h) ∈ s)

instance [Transport r] [InjClass' α β] [SurjClass' α β] : SurjClass' (Set β) (Set α) where
  surj s := by
    choose f hf using fun b : β ↦ surj' α b
    use {x | f x ∈ s}
    intro a b h
    symm
    exact congr($(inj' (hf b) h) ∈ s)

instance [Transport r] [SurjClass α β] : InjClass (Set β) (Set α) where
  inj h h' := by
    ext a
    rcases surj β a with ⟨b, hb⟩
    rw [h hb, h' hb]

-- variable {map : α → β}

-- instance [MapTransport r map] : MapTransport (SetRel r) ({x | map x ∈ ·}) where

-- variable [MapTransport r map]

-- instance [MapClass α β] : MapClass (Set β) (Set α) where
--   rel_map s := by
--     intro a b h
--     exact congr($(map_eq_of_rel h) ∈ s)
--   map_eq_of_rel {g f} h := by
--     ext a
--     exact (h (rel_map a)).symm.to_iff

-- instance [SurjMapClass α β] : InjMapClass (Set β) (Set α) where
--   map_injective g g' h := by
--     ext b
--     obtain ⟨a, rfl⟩ := map_surjective α b
--     exact congr(a ∈ $h)

-- instance [EquivMapClass α β] : EquivMapClass (Set β) (Set α) where
--   map_surjective s := by
--     use {x | (Equiv.ofBijective map map_bijective).symm x ∈ s}
--     ext a
--     exact congr($(Equiv.ofBijective_symm_apply_apply _ _ _) ∈ s)

variable {r} {s t : Set α} {s' t' : Set β}

-- TODO: should be able to remove `[Transport r]`?
@[transport intro]
theorem Set.transport_mem [Transport r] (hs : SetRel r s' s) {a a'} (ha : r a a') :
    (a ∈ s) = (a' ∈ s') :=
  hs ha

-- TODO: remove this lemma
@[transport intro]
theorem Set.transport_mem' [Transport r] (hs : SetRel r s' s) {a a'} (ha : r a a') :
    (a' ∈ s') = (a ∈ s) :=
  hs ha |>.symm

@[transport] theorem Set.transport_univ : SetRel r .univ .univ := by simp [SetRel]
@[transport] theorem Set.transport_empty : SetRel r ∅ ∅ := by simp [SetRel]

@[transport intro]
theorem Set.transport_subset [Transport r] [SurjClass α β] [SurjClass' α β]
    (hs : SetRel r s' s) (ht : SetRel r t' t) :
    (s ⊆ t) = (s' ⊆ t') := by
  simp_rw [Set.subset_def]
  transport [hs, ht] α to β
  rfl

@[transport intro]
theorem Set.transport_ssubset [Transport r] [SurjClass α β] [SurjClass' α β]
    (hs : SetRel r s' s) (ht : SetRel r t' t) :
    (s ⊂ t) = (s' ⊂ t') := by
  simp_rw [Set.ssubset_def]
  transport [hs, ht] β to α
  rfl

variable {ι ι' : Type*} {r' : ι → ι' → Prop} [Transport r'] (s : ι → Set α) (t : ι' → Set β)

@[transport]
theorem Set.transport_iUnion [Transport r] [SurjClass ι ι'] [SurjClass' ι ι']
    (h : ∀ i i', r' i i' → SetRel r (t i') (s i)) :
    SetRel r (Set.iUnion t) (Set.iUnion s) := by
  intro a b hr
  push _ ∈ _
  transport [h, hr] α to β, ι to ι'
  rfl

@[transport]
theorem Set.transport_iInter [SurjClass ι ι'] [SurjClass' ι ι']
    (h : ∀ i i', r' i i' → SetRel r (t i') (s i)) :
    SetRel r (Set.iInter t) (Set.iInter s) := by
  intro a b hr
  push _ ∈ _
  apply forall_transport_eq
  intro i i' hi
  exact h i i' hi hr

end Set

section Finset

variable {α : Type*}

abbrev FinsetToSetRel : Finset α → Set α → Prop := MapRel (↑)

-- variable {α β : Type*} (r : α → β → Prop)

-- abbrev FinsetToSetRel : Finset β → Set α → Prop := (SetRel r ↑· ·)

variable {s t : Finset α} {s' t' : Set α}

@[transport]
theorem Finset.transport_subset (hs : FinsetToSetRel s s') (ht : FinsetToSetRel t t') :
    (s ⊆ t) = (s' ⊆ t') := by
  subst hs ht; simp

@[transport]
theorem Finset.transport_ssubset (hs : FinsetToSetRel s s') (ht : FinsetToSetRel t t') :
    (s ⊂ t) = (s' ⊂ t') := by
  subst hs ht; simp

@[transport]
theorem Finset.transport_empty : FinsetToSetRel (∅ : Finset α) ∅ := by simp [FinsetToSetRel, MapRel]

@[transport]
theorem Finset.transport_singleton {a a' : α} (h : a = a') :
    FinsetToSetRel ({a} : Finset α) {a'} := by
  simp [h, FinsetToSetRel, MapRel]

variable [DecidableEq α]

@[transport]
theorem Finset.transport_insert {a a' : α} (ha : a = a') (hs : FinsetToSetRel s s') :
    FinsetToSetRel (insert a s) (insert a' s') := by
  simp_all [FinsetToSetRel, MapRel]

@[transport]
theorem Finset.transport_erase {a a' : α} (ha : a = a') (hs : FinsetToSetRel s s') :
    FinsetToSetRel (s.erase a) (s' \ {a'}) := by
  simp_all [FinsetToSetRel, MapRel]

@[transport]
theorem Finset.transport_union (hs : FinsetToSetRel s s') (ht : FinsetToSetRel t t') :
    FinsetToSetRel (s ∪ t) (s' ∪ t') := by
  simp_all [FinsetToSetRel, MapRel]

@[transport]
theorem Finset.transport_inter (hs : FinsetToSetRel s s') (ht : FinsetToSetRel t t') :
    FinsetToSetRel (s ∩ t) (s' ∩ t') := by
  simp_all [FinsetToSetRel, MapRel]

-- TODO: Nonempty, membership, cardinality.

instance : MapTransport (@FinsetToSetRel α) (↑) where

instance : InjMapClass (Finset α) (Set α) := MapRel.instInjMapClass Finset.coe_injective

end Finset





variable {α : Type*} (s t : Finset α) (s' t' : Set α)

example [DecidableEq α] (a : α) : insert a (∅ : Finset α) = {a} := by
  transport Finset α to Set α
  guard_target = insert a (∅ : Set α) = {a}
  rw [← Set.singleton_def]

example [DecidableEq α] (a : α) : ∀ s : Finset α, s ∪ {a} = insert a s := by
  transport Finset α to Set α
  intro s
  exact Set.union_singleton

example [DecidableEq α] (a : α) : ¬ ∀ s : Set α, insert a ∅ = s := by
  transport Set α to Finset α
  guard_target = ¬ ∀ s : Finset α, insert a ∅ = s
  sorry

-- Yay, this now works
example [DecidableEq α] (a : α) (s : Option (Finset α)) : s.elim {a} (·.erase a) = ∅ := by
  transport Finset α to Set α generalizing s
  guard_hyp s : Option (Set α)
  guard_target = s.elim {a} (· \ {a}) = ∅
  sorry

-- In this example, transport cannot eliminate all occurrences of `s`, so it should fail.
/--
error: unsolved goals
α : Type u_1
s t : Finset α
s' t' : Set α
p : Finset α → Prop
⊢ ∀ (s : Set α), p _fvar.21683 ∧ s = s
-/
#guard_msgs in
example (p : Finset α → Prop) : ∀ s, p s ∧ s = s := by
  transport Finset α to Set α



def MyCompact (X : Type) [TopologicalSpace X] :=
  ∀ {ι : Type} {U : ι → Set X} (_ : ∀ i, IsOpen (U i)) (_ : Set.univ ⊆ ⋃ i, U i),
  ∃ t : Finset ι, Set.univ ⊆ ⋃ i ∈ t, U i

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

@[transport intro]
theorem transport_IsOpen {r : X → Y → Prop} {map : X → Y} [MapTransport r map] [SemiMapClass X Y]
    (hf : Continuous map) {s : Set X} {t : Set Y} (h : SetRel r t s) : IsOpen t → IsOpen s := by
  convert IsOpen.preimage hf
  ext x
  exact (h (rel_map x)).to_iff

-- Yay, this now works!!!
set_option trace.Meta.synthInstance true in
set_option trace.Meta.grewrite true in
example (f : X → Y) (hf : f.Surjective) (hf_cont : Continuous f)
    (hX : MyCompact X) : MyCompact Y := by
  unfold MyCompact
  have : MapTransport (MapRel f) f := ⟨⟩; have := MapRel.instSurjMapClass hf
  transport Y to X
  exact hX

end TransportTest

/-
Let's say a commutative ring is local if it has exactly one maximal ideal.
I claim that a ring isomorphic to a local ring is local, and here's a funny proof.
Say a ring is nontrivial if it has more than one element.
If R -> S is an injection and R is nontrivial then S is nontrivial, by transport.
Say a ring is prelocal if it has at most one maximal ideal.
If R -> S is a surjection and R is prelocal then S is prelocal, by transport.
Furthermore a nontrivial prelocal ring is local.
Hence if R -> S is an isomorphism and R is local then S is local.
-/
-- TODO: cleaner separation of local contexts before/after
