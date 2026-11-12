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
  Mathlib.Tactic.GCongr.imp_mono
  Mathlib.Tactic.GCongr.and_mono

namespace TransportTest

section Class

/-
-- Injecion: `Finset` to `Set`, `Nat` to `Int`
-- Surjection: `Nat` to `ZMod`, quotients.

-/

class Transport {α β : Type*} (r : outParam <| α → β → Prop)

instance (priority := high) (α : Type*) : Transport (@Eq α) where

variable {α β : Type*}

class BiTransport (r : outParam <| α → β → Prop) where

instance (priority := high) {r : α → β → Prop} [Transport r] : BiTransport r where

instance {r : α → β → Prop} [BiTransport r] : BiTransport fun x y ↦ r y x where

section

class Total (α β : Type*) {r : α → β → Prop} [BiTransport r] where
  total (β) (a : α) : ∃ b : β, r a b

variable {r : α → β → Prop}

variable (β) in
lemma total [BiTransport r] [Total α β] (a : α) : ∃ b : β, r a b := Total.total β a

instance : Total α α where total a := ⟨a, rfl⟩

variable {p : α → Prop} {q : β → Prop}

@[transport]
theorem forall_transport [BiTransport r] [Total α β]
    (h : ∀ {a b}, r a b → q b → p a) :
    (∀ b, q b) → (∀ a, p a) :=
  fun h' a ↦ (total β a).rec fun b hb ↦ h hb (h' b)

@[transport]
theorem forall_transport_eq [Transport r] [Total α β] [Total β α]
    (h : ∀ {a b}, r a b → p a = q b) :
    (∀ a, p a) = (∀ b, q b) :=
  propext ⟨forall_transport (h · |>.mp), forall_transport (h · |>.mpr)⟩

@[transport]
theorem exists_transport [BiTransport r] [Total α β]
    (h : ∀ {a b}, r a b → p a → q b) :
    (∃ a, p a) → (∃ b, q b) :=
  fun ⟨a, ha⟩ ↦ (total β a).rec fun b hb ↦ ⟨b, h hb ha⟩

@[transport]
theorem exists_transport_eq [Transport r] [Total α β] [Total β α]
    (h : ∀ {a b}, r a b → p a = q b) :
    (∃ a, p a) = (∃ b, q b) :=
  propext ⟨exists_transport (h · |>.mp), exists_transport (h · |>.mpr)⟩

end

section

class Unique (α β : Type*) {r : α → β → Prop} [BiTransport r] where
  unique {a b b'} : r a b → r a b' → b = b'

variable {r : α → β → Prop} {a a' : α} {b b' : β}

lemma rightUnique [BiTransport r] [Unique α β] (h : r a b) (h' : r a b') : b = b' :=
  Unique.unique h h'

lemma leftUnique [BiTransport r] [Unique β α] (h : r a b) (h' : r a' b) : a = a' :=
  Unique.unique (r := fun x y ↦ r y x) h h'

instance : Unique α α where unique h h' := h.symm.trans h'

@[transport]
theorem eq_transport [BiTransport r] [Unique α β]
    (h : r a b) (h' : r a' b') : a = a' → b = b' := by
  rintro rfl
  exact rightUnique h h'

@[transport]
theorem eq_transport_eq [Transport r] [Unique α β] [Unique β α]
    (h : r a b) (h' : r a' b') : (a = a') = (b = b') :=
  propext ⟨eq_transport h h', eq_transport h h'⟩

@[transport]
theorem ne_transport [BiTransport r] [Unique α β]
    (h : r a b) (h' : r a' b') : b ≠ b' → a ≠ a' := by
  contrapose
  exact eq_transport h h'

@[transport]
theorem ne_transport_eq [Transport r] [Unique α β] [Unique β α]
    (h : r a b) (h' : r a' b') : (a ≠ a') = (b ≠ b') :=
  (eq_transport_eq h h').to_iff.ne.eq

end

class MapTransport (r : outParam <| α → β → Prop) (map : outParam <| α → β)

variable (α β : Type*) {r : α → β → Prop} {map : α → β}

instance (priority := high) : MapTransport (@Eq α) (·) where

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

instance [SemiMapClass α β] : Total α β where
  total a := ⟨map a, rel_map a⟩

instance [SurjMapClass α β] : Total β α where
  total b := by rcases map_surjective α b with ⟨b, rfl⟩; use b, rel_map b

instance [MapClass α β] : Unique α β where
  unique h h' := by rw [← map_eq_of_rel h, ← map_eq_of_rel h']

instance [InjMapClass α β] : Unique β α where
  unique h h' := map_injective <| (map_eq_of_rel h).trans (map_eq_of_rel h').symm

instance [MapClass α β] [Total β α] : SurjMapClass α β where
  map_surjective b := by
    rcases total α b with ⟨a, ha⟩
    use a, map_eq_of_rel ha

instance [MapClass α β] [Unique β α] : InjMapClass α β where
  map_injective a a' h :=
    leftUnique (b := map a) (rel_map a) (h ▸ rel_map a')

instance : EquivMapClass α α where
  rel_map _ := rfl
  map_eq_of_rel := id
  map_injective := Function.injective_id
  map_surjective := Function.surjective_id


end Class

@[expose]
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

instance [Transport r] [Total α β] : Total (Option α) (Option β) where
  total
    | none => ⟨none, .none⟩
    | some a => (total β a).rec fun b hb ↦ ⟨some b, .some hb⟩

instance (r : β → α → Prop) [Transport r] [Total α β] : Total (Option α) (Option β) where
  total
    | none => ⟨none, .none⟩
    | some a => (total β a).rec fun b hb ↦ ⟨some b, .some hb⟩

instance [Transport r] [Unique α β] : Unique (Option α) (Option β) where
  unique
    | .none, .none => congr(none)
    | .some h₁, .some h₂ => congr(some $(rightUnique h₁ h₂))

instance (r : β → α → Prop) [Transport r] [Unique α β] : Unique (Option α) (Option β) where
  unique
    | .none, .none => congr(none)
    | .some h₁, .some h₂ => congr(some $(leftUnique h₁ h₂))

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

@[transport]
theorem Option.elim_transport {r : α → β → Prop} {r' : α' → β' → Prop}
    {o : Option α} {o' : Option β} (ho : OptionRel r o o')
    {x : α'} {x' : β'} (hx : r' x x')
    {f : α → α'} {f' : β → β'} (hf : ∀ x y, r x y → r' (f x) (f' y)) :
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

instance [Transport r] [Transport r']
    [Total α β] [Total α' β'] : Total (α × α') (β × β') where
  total := fun (a, a') => by
    rcases total β a with ⟨b, hb⟩
    rcases total β' a' with ⟨b', hb'⟩
    exact ⟨(b, b'), ⟨hb, hb'⟩⟩

instance (r : β → α → Prop) (r' : β' → α' → Prop) [Transport r] [Transport r']
    [Total α β] [Total α' β'] : Total (α × α') (β × β') where
  total := fun (a, a') => by
    rcases total β a with ⟨b, hb⟩
    rcases total β' a' with ⟨b', hb'⟩
    exact ⟨(b, b'), ⟨hb, hb'⟩⟩

instance [Transport r] [Transport r']
    [Unique α β] [Unique α' β'] : Unique (α × α') (β × β') where
  unique := fun ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩ => congr(($(rightUnique h₁ h₂), $(rightUnique h₁' h₂')))

instance (r : β → α → Prop) (r' : β' → α' → Prop) [Transport r] [Transport r']
    [Unique α β] [Unique α' β'] : Unique (α × α') (β × β') where
  unique := fun ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩ => congr(($(leftUnique h₁ h₂), $(leftUnique h₁' h₂')))

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
    [Unique α β] [Total α β] [∀ a b, Total (γ b) (δ a)] :
    Total (Π b, γ b) (Π a, δ a) where
  total g := by
    choose x hx using fun a : α ↦ total β a
    choose y hy using fun {a b} ↦ fun c : γ b ↦ total (δ a) c
    use (y <| g <| x ·)
    intro a b h
    dsimp
    rw [rightUnique (hx a) h]
    exact hy (g b)

instance (r : β → α → Prop) (r' : ∀ {a b}, δ a → γ b → Prop)
    [Transport r] [∀ a b, Transport (@r' a b)]
    [Unique α β] [Total α β] [∀ a b, Total (γ b) (δ a)] :
    Total (Π b, γ b) (Π a, δ a) where
  total g := by
    choose x hx using fun a : α ↦ total β a
    choose y hy using fun {a b} ↦ fun c : γ b ↦ total (δ a) c
    use (y <| g <| x ·)
    intro b a h
    dsimp
    rw [leftUnique (hx a) h]
    exact hy (g b)

instance [Transport r] [∀ a b, Transport (@r' a b)]
    [Total α β] [∀ a b, Unique (γ b) (δ a)] :
    Unique (Π b, γ b) (Π a, δ a) where
  unique h h' := by
    ext a
    rcases total β a with ⟨b, hb⟩
    apply rightUnique (h hb) (h' hb)

instance (r : β → α → Prop) (r' : ∀ {a b}, δ a → γ b → Prop)
    [Transport r] [∀ a b, Transport (@r' a b)]
    [Total α β] [∀ a b, Unique (γ b) (δ a)] :
    Unique (Π b, γ b) (Π a, δ a) where
  unique h h' := by
    ext a
    rcases total β a with ⟨b, hb⟩
    apply leftUnique (h hb) (h' hb)

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

instance [Transport r] [Unique α β] [Total α β] : Total (Set β) (Set α) where
  total s := by
    choose f hf using fun a : α ↦ total β a
    use {x | f x ∈ s}
    intro a b h
    exact congr($(rightUnique (hf a) h) ∈ s)

instance (r : β → α → Prop) [Transport r] [Unique α β] [Total α β] : Total (Set β) (Set α) where
  total s := by
    choose f hf using fun a : α ↦ total β a
    use {x | f x ∈ s}
    intro b a h
    symm
    exact congr($(leftUnique (hf a) h) ∈ s)

instance [Transport r] [Total α β] : Unique (Set β) (Set α) where
  unique h h' := by
    ext a
    rcases total β a with ⟨b, hb⟩
    rw [h hb, h' hb]

instance (r : β → α → Prop) [Transport r] [Total α β] : Unique (Set β) (Set α) where
  unique h h' := by
    ext a
    rcases total β a with ⟨b, hb⟩
    rw [← h hb, h' hb]

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

@[transport]
theorem Set.transport_mem (hs : SetRel r s' s) {a a'} (ha : r a a') :
    (a ∈ s) = (a' ∈ s') :=
  hs ha

-- TODO: remove this lemma
@[transport]
theorem Set.transport_mem' (hs : SetRel r s' s) {a a'} (ha : r a a') :
    (a' ∈ s') = (a ∈ s) :=
  hs ha |>.symm

@[transport] theorem Set.transport_univ : SetRel r .univ .univ := by simp [SetRel]
@[transport] theorem Set.transport_empty : SetRel r ∅ ∅ := by simp [SetRel]

@[transport] theorem Set.transport_singleton [Transport r] [Unique α β] [Unique β α]
    {a : α} {b : β} (h : r a b) : SetRel r {b} {a} := by
  intro _ _ h'
  simp only [Set.mem_singleton_iff]
  transport [h, h'] α to β
  rfl

@[transport]
theorem Set.transport_subset [Transport r] [Total α β] [Total β α]
    (hs : SetRel r s' s) (ht : SetRel r t' t) :
    (s ⊆ t) = (s' ⊆ t') := by
  simp_rw [Set.subset_def]
  transport [hs, ht] α to β
  rfl

@[transport]
theorem Set.transport_ssubset [Transport r] [Total α β] [Total β α]
    (hs : SetRel r s' s) (ht : SetRel r t' t) :
    (s ⊂ t) = (s' ⊂ t') := by
  simp_rw [Set.ssubset_def]
  transport [hs, ht] β to α
  rfl

section
variable {ι ι' : Type*} {r' : ι → ι' → Prop} [Transport r'] (s : ι → Set α) (t : ι' → Set β)

@[transport]
theorem Set.transport_iUnion [Total ι ι'] [Total ι' ι]
    (h : ∀ i i', r' i i' → SetRel r (t i') (s i)) :
    SetRel r (Set.iUnion t) (Set.iUnion s) := by
  intro a b hr
  push _ ∈ _
  have : Transport r := ⟨⟩
  transport [h, hr] α to β, ι to ι'
  rfl

@[transport]
theorem Set.transport_iInter [Total ι ι'] [Total ι' ι]
    (h : ∀ i i', r' i i' → SetRel r (t i') (s i)) :
    SetRel r (Set.iInter t) (Set.iInter s) := by
  intro a b hr
  push _ ∈ _
  apply forall_transport_eq
  intro i i' hi
  exact h i i' hi hr

end

variable {ι : Sort*} (s : ι → Set α) (t : ι → Set β)

@[transport low]
theorem Set.transport_iUnion'
    (h : ∀ i, SetRel r (t i) (s i)) :
    SetRel r (Set.iUnion t) (Set.iUnion s) := by
  intro a b hr
  push _ ∈ _
  have : Transport r := ⟨⟩
  transport [h, hr] α to β
  rfl

@[transport low]
theorem Set.transport_iInter'
    (h : ∀ i, SetRel r (t i) (s i)) :
    SetRel r (Set.iInter t) (Set.iInter s) := by
  intro a b hr
  push _ ∈ _
  have : Transport r := ⟨⟩
  transport [h, hr] α to β
  rfl

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

/--
trace: α : Type u_1
s t : Finset α
s' t' : Set α
inst✝ : DecidableEq α
a : α
⊢ ¬∀ (s : Finset α), insert a ∅ = s
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example [DecidableEq α] (a : α) : ¬ ∀ s : Set α, insert a ∅ = s := by
  transport Set α to Finset α
  trace_state
  sorry

-- Yay, this now works
/--
trace: α : Type u_1
s✝ t : Finset α
s' t' : Set α
inst✝ : DecidableEq α
a : α
s : Option (Set α)
⊢ (s.elim {a} fun s ↦ s \ {a}) = ∅
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example [DecidableEq α] (a : α) (s : Option (Finset α)) : s.elim {a} (fun s ↦ s.erase a) = ∅ := by
  transport Finset α to Set α generalizing s
  trace_state
  sorry

-- In this example, transport cannot eliminate all occurrences of `s`, so it should fail.
/-- error: transport made no progress on `p s✝` -/
#guard_msgs in
example (p : Finset α → Prop) : ∀ s, p s ∧ s = s := by
  transport Finset α to Set α



def MyCompact (X : Type) [TopologicalSpace X] :=
  ∀ {ι : Type} {U : ι → Set X} (_ : ∀ i, IsOpen (U i)) (_ : Set.univ ⊆ ⋃ i, U i),
  ∃ t : Finset ι, Set.univ ⊆ ⋃ i ∈ t, U i

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

@[transport]
theorem transport_IsOpen {r : X → Y → Prop} {map : X → Y} [MapTransport r map] [SemiMapClass X Y]
    (hf : Continuous map) {s : Set X} {t : Set Y} (h : SetRel r t s) : IsOpen t → IsOpen s := by
  convert IsOpen.preimage hf
  ext x
  exact (h (rel_map x)).to_iff

-- Yay, this now works!!!
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
