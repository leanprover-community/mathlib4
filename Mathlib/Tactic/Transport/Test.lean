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

attribute [transport] mt Or.imp Exists.imp forall_imp
  Mathlib.Tactic.GCongr.imp_mono
  Mathlib.Tactic.GCongr.and_mono

namespace Transport

section Class

/-
-- Injecion: `Finset` to `Set`, `Nat` to `Int`
-- Surjection: `Nat` to `ZMod`, quotients.

-/

section

variable {α β : Sort*}

class LeftTotal (r : α → β → Prop) where
  total (a : α) : ∃ b : β, r a b

class RightTotal (r : α → β → Prop) where
  total (b : β) : ∃ a : α, r a b

variable (r : α → β → Prop)

local instance [i : LeftTotal r] : RightTotal (flip r) := ⟨i.total⟩
local instance [i : RightTotal r] : LeftTotal (flip r) := ⟨i.total⟩

lemma leftTotal [LeftTotal r] (a : α) : ∃ b : β, r a b := LeftTotal.total a
lemma rightTotal [RightTotal r] (b : β) : ∃ a : α, r a b := RightTotal.total b

variable {p : α → Prop} {q : β → Prop}

@[transport]
theorem forall_transport [LeftTotal r]
    (h : ∀ {a b}, r a b → q b → p a) :
    (∀ b, q b) → (∀ a, p a) :=
  fun h' a ↦ (leftTotal r a).rec fun b hb ↦ h hb (h' b)

@[transport]
theorem forall_transport' [RightTotal r] (h : ∀ {a b}, r a b → p a → q b) :
    (∀ a, p a) → (∀ b, q b) :=
  forall_transport (flip r) h

@[transport]
theorem forall_transport_eq [LeftTotal r] [RightTotal r] (h : ∀ {a b}, r a b → p a = q b) :
    (∀ a, p a) ↔ (∀ b, q b) :=
  ⟨forall_transport' r (h · |>.mp), forall_transport r (h · |>.mpr)⟩

@[transport]
theorem exists_transport [LeftTotal r] (h : ∀ {a b}, r a b → p a → q b) :
    (∃ a, p a) → (∃ b, q b) :=
  fun ⟨a, ha⟩ ↦ (leftTotal r a).rec fun b hb ↦ ⟨b, h hb ha⟩

@[transport]
theorem exists_transport' [RightTotal r] (h : ∀ {a b}, r a b → q b → p a) :
    (∃ b, q b) → (∃ a, p a) :=
  exists_transport (flip r) h

@[transport]
theorem exists_transport_eq [LeftTotal r] [RightTotal r] (h : ∀ {a b}, r a b → p a = q b) :
    (∃ a, p a) ↔ (∃ b, q b) :=
  ⟨exists_transport r (h · |>.mp), exists_transport' r (h · |>.mpr)⟩

end

section

variable {α β : Sort*}

class RightUnique (r : α → β → Prop) where
  unique {a b b'} : r a b → r a b' → b = b'

class LeftUnique (r : α → β → Prop) where
  unique {a a' b} : r a b → r a' b → a = a'

variable {r : α → β → Prop} {a a' : α} {b b' : β}

local instance [i : LeftUnique r] : RightUnique (flip r) := ⟨i.unique⟩
local instance [i : RightUnique r] : LeftUnique (flip r) := ⟨i.unique⟩

lemma rightUnique [RightUnique r] (h : r a b) (h' : r a b') : b = b' :=
  RightUnique.unique h h'

lemma leftUnique [LeftUnique r] (h : r a b) (h' : r a' b) : a = a' :=
  RightUnique.unique (r := flip r) h h'

@[transport]
theorem eq_transport [RightUnique r]
    (h : r a b) (h' : r a' b') : a = a' → b = b' := by
  rintro rfl
  exact rightUnique h h'

@[transport]
theorem eq_transport' [LeftUnique r]
    (h : r a b) (h' : r a' b') : b = b' → a = a' :=
  eq_transport (r := flip r) h h'

@[transport]
theorem eq_transport_eq [RightUnique r] [LeftUnique r]
    (h : r a b) (h' : r a' b') : a = a' ↔ b = b' :=
  ⟨eq_transport h h', eq_transport' h h'⟩

@[transport]
theorem ne_transport [RightUnique r]
    (h : r a b) (h' : r a' b') : b ≠ b' → a ≠ a' := by
  contrapose
  exact eq_transport h h'

@[transport]
theorem ne_transport' [LeftUnique r]
    (h : r a b) (h' : r a' b') : a ≠ a' → b ≠ b' :=
  ne_transport (r := flip r) h h'

@[transport]
theorem ne_transport_eq [RightUnique r] [LeftUnique r]
    (h : r a b) (h' : r a' b') : a ≠ a' ↔ b ≠ b' :=
  (eq_transport_eq h h').ne

end

variable {α β : Type*}

class MapTransport (r : α → β → Prop) (map : outParam <| α → β)

variable (r : α → β → Prop) {map : α → β}

class SemiMapClass [MapTransport r map] where
  rel_map (a) : r a (map a)

variable [MapTransport r map]

class MapClass extends SemiMapClass r where
  map_eq_of_rel {a b} : r a b → map a = b

class InjMapClass extends MapClass r where
  map_injective : Function.Injective map

class SurjMapClass extends MapClass r where
  map_surjective : Function.Surjective map

class EquivMapClass extends InjMapClass r, SurjMapClass r

lemma rel_map [SemiMapClass r] (a) : r a (map a) := SemiMapClass.rel_map a
lemma map_eq_of_rel [MapClass r] {a b} : r a b → map a = b := MapClass.map_eq_of_rel
lemma map_injective [InjMapClass r] : Function.Injective map := InjMapClass.map_injective r
lemma map_surjective [SurjMapClass r] : Function.Surjective map := SurjMapClass.map_surjective r
lemma map_bijective [EquivMapClass r] : Function.Bijective map :=
  ⟨map_injective r, map_surjective r⟩

instance [SemiMapClass r] : LeftTotal r where
  total a := ⟨map a, rel_map r a⟩

instance [SurjMapClass r] : RightTotal r where
  total b := by rcases map_surjective r b with ⟨b, rfl⟩; use b, rel_map r b

instance [MapClass r] : RightUnique r where
  unique h h' := by rw [← map_eq_of_rel r h, ← map_eq_of_rel r h']

instance [InjMapClass r] : LeftUnique r where
  unique h h' := map_injective r <| (map_eq_of_rel r h).trans (map_eq_of_rel r h').symm

instance [MapClass r] [RightTotal r] : SurjMapClass r where
  map_surjective b := by
    rcases rightTotal r b with ⟨a, ha⟩
    use a, map_eq_of_rel r ha

instance [MapClass r] [LeftUnique r] : InjMapClass r where
  map_injective a a' h :=
    leftUnique (b := map a) (rel_map r a) (h ▸ rel_map r a')

end Class

section Eq

variable (α : Sort*)

instance : LeftTotal (@Eq α) where total a := ⟨a, rfl⟩
instance : RightTotal (@Eq α) where total a := ⟨a, rfl⟩
instance : RightUnique (@Eq α) where unique h h' := h.symm.trans h'
instance : LeftUnique (@Eq α) where unique h h' := h.trans h'.symm

variable (α : Type*)

instance : MapTransport (@Eq α) (·) where

instance : EquivMapClass (@Eq α) where
  rel_map _ := rfl
  map_eq_of_rel := id
  map_injective := Function.injective_id
  map_surjective := Function.surjective_id

end Eq

namespace MapRel

variable {α β : Type*} {map : α → β}

instance : MapTransport (MapRel map) map where

instance : MapClass (MapRel map) where
  rel_map _ := by rfl
  map_eq_of_rel := by exact id

theorem instInjMapClass (h : Function.Injective map) : InjMapClass (MapRel map) :=
  ⟨by exact h⟩

theorem instSurjMapClass (h : Function.Surjective map) : SurjMapClass (MapRel map) :=
  ⟨by exact h⟩

end MapRel

section Option

variable {α β α' β' : Type*}

@[transport]
inductive OptionRel (r : α → β → Prop) : Option α → Option β → Prop where
  | none : OptionRel r none none
  | some {a b} : r a b → OptionRel r (some a) (some b)

variable (r : α → β → Prop)

instance [LeftTotal r] : LeftTotal (OptionRel r) where
  total
    | none => ⟨none, .none⟩
    | some a => (leftTotal r a).rec fun b hb ↦ ⟨some b, .some hb⟩

instance [RightTotal r] : RightTotal (OptionRel r) where
  total
    | none => ⟨none, .none⟩
    | some a => (rightTotal r a).rec fun b hb ↦ ⟨some b, .some hb⟩

instance [RightUnique r] : RightUnique (OptionRel r) where
  unique
    | .none, .none => congr(none)
    | .some h₁, .some h₂ => congr(some $(rightUnique h₁ h₂))

instance [LeftUnique r] : LeftUnique (OptionRel r) where
  unique
    | .none, .none => congr(none)
    | .some h₁, .some h₂ => congr(some $(leftUnique h₁ h₂))

-- variable {map : α → β}

-- instance [MapTransport r map] : MapTransport (OptionRel r) (.map map) where

-- instance [MapTransport r map] [SemiMapClass r] : SemiMapClass (Option α) (Option β) where
--   rel_map
--     | none => .none
--     | some a => .some (rel_map a)

-- instance [MapTransport r map] [MapClass r] : MapClass (Option α) (Option β) where
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

@[transport]
structure ProdRel (r : α → β → Prop) (r' : α' → β' → Prop) (a : α × α') (b : β × β') : Prop where
  left : r a.1 b.1
  right : r' a.2 b.2

variable (r : α → β → Prop) (r' : α' → β' → Prop)

instance [LeftTotal r] [LeftTotal r'] : LeftTotal (ProdRel r r') where
  total := fun (a, a') => by
    rcases leftTotal r a with ⟨b, hb⟩
    rcases leftTotal r' a' with ⟨b', hb'⟩
    exact ⟨(b, b'), ⟨hb, hb'⟩⟩

instance [RightTotal r] [RightTotal r'] : RightTotal (ProdRel r r') where
  total := fun (a, a') => by
    rcases rightTotal r a with ⟨b, hb⟩
    rcases rightTotal r' a' with ⟨b', hb'⟩
    exact ⟨(b, b'), ⟨hb, hb'⟩⟩

instance [RightUnique r] [RightUnique r'] : RightUnique (ProdRel r r') where
  unique := fun ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩ => congr(($(rightUnique h₁ h₂), $(rightUnique h₁' h₂')))

instance [LeftUnique r] [LeftUnique r'] : LeftUnique (ProdRel r r') where
  unique := fun ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩ => congr(($(leftUnique h₁ h₂), $(leftUnique h₁' h₂')))

-- variable {map : α → β} {map' : α' → β'}

-- instance [MapTransport r map] [MapTransport r' map'] :
--     MapTransport (ProdRel r r') (.map map map') where

-- variable [MapTransport r map] [MapTransport r' map']

-- instance [SemiMapClass r] [SemiMapClass α' β'] : SemiMapClass (α × α') (β × β') where
--   rel_map | (a, b) => ⟨rel_map a, rel_map b⟩

-- instance [MapClass r] [MapClass α' β'] : MapClass (α × α') (β × β') where
--   map_eq_of_rel | ⟨h, h'⟩ => congr(⟨$(map_eq_of_rel h), $(map_eq_of_rel h')⟩)

end Prod

section Function

attribute [transport] FunctionRel

variable {α β : Type*} {γ : β → Type*} {δ : α → Type*}
variable (r : α → β → Prop) (r' : ∀ {a b}, r a b → γ b → δ a → Prop)

instance [RightUnique r] [LeftTotal r] [∀ a b (h : r a b), LeftTotal (r' h)] :
    LeftTotal (FunctionRel r r') where
  total g := by
    choose x hx using fun a : α ↦ leftTotal r a
    choose y hy using fun {a} ↦ fun c : γ (x a) ↦ leftTotal (r' (hx a)) c
    use (y <| g <| x ·)
    intro a b h
    dsimp
    obtain rfl := rightUnique (hx a) h
    exact hy (g (x a))

instance [LeftUnique r] [RightTotal r] [∀ a b (h : r a b), RightTotal (r' h)] :
    RightTotal (FunctionRel r r') where
  total g := by
    choose x hx using fun b : β ↦ rightTotal r b
    choose y hy using fun {b} ↦ fun d : δ (x b) ↦ rightTotal (r' (hx b)) d
    use (y <| g <| x ·)
    intro a b h
    dsimp
    obtain rfl := leftUnique (hx b) h
    exact hy (g (x b))

instance [LeftTotal r] [∀ a b (h : r a b), RightUnique (r' h)] :
    RightUnique (FunctionRel r r') where
  unique h h' := by
    ext a
    rcases leftTotal r a with ⟨b, hb⟩
    apply rightUnique (h hb) (h' hb)

instance [RightTotal r] [∀ a b (h : r a b), LeftUnique (r' h)] :
    LeftUnique (FunctionRel r r') where
  unique h h' := by
    ext a
    rcases rightTotal r a with ⟨b, hb⟩
    apply leftUnique (h hb) (h' hb)

variable {map : α → β} {map' : ∀ {a b}, γ b → δ a}

instance [MapTransport r map] [∀ a b (h : r a b), MapTransport (r' h) map'] :
    MapTransport (FunctionRel r @r') (fun f a ↦ map' (f (map a))) where

variable [MapTransport r map] [∀ a b (h : r a b), MapTransport (r' h) map']

instance [MapClass r] [∀ a b (h : r a b), SemiMapClass (r' h)] :
    SemiMapClass (FunctionRel r r') where
  rel_map g := by
    intro a b h
    dsimp
    rw [map_eq_of_rel r h]
    apply rel_map

instance [MapClass r] [∀ a b (h : r a b), MapClass (r' h)] : MapClass (FunctionRel r r') where
  map_eq_of_rel {g f} h := by
    ext a
    exact map_eq_of_rel (r' (rel_map r a)) (h (rel_map r a))

end Function

section Set

variable {α β : Type*}

@[transport]
def SetRel (r : α → β → Prop) (t : Set β) (s : Set α) : Prop :=
  ∀ {a b}, r a b → (a ∈ s ↔ b ∈ t)

variable (r : α → β → Prop)

instance [RightUnique r] [LeftTotal r] : LeftTotal (SetRel r) where
  total s := by
    choose f hf using fun a : α ↦ leftTotal r a
    use {x | f x ∈ s}
    intro a b h
    exact congr($(rightUnique (hf a) h) ∈ s)

instance [LeftUnique r] [RightTotal r] : RightTotal (SetRel r) where
  total s := by
    choose f hf using fun b : β ↦ rightTotal r b
    use {x | f x ∈ s}
    intro b a h
    symm
    exact congr($(leftUnique (hf a) h) ∈ s)

instance [LeftTotal r] : RightUnique (SetRel r) where
  unique h h' := by
    ext a
    rcases leftTotal r a with ⟨b, hb⟩
    rw [h hb, h' hb]

instance [RightTotal r] : LeftUnique (SetRel r) where
  unique h h' := by
    ext b
    rcases rightTotal r b with ⟨a, ha⟩
    rw [← h ha, h' ha]

-- variable {map : α → β}

-- instance [MapTransport r map] : MapTransport (SetRel r) ({x | map x ∈ ·}) where

-- variable [MapTransport r map]

-- instance [MapClass r] : MapClass (Set β) (Set α) where
--   rel_map s := by
--     intro a b h
--     exact congr($(map_eq_of_rel h) ∈ s)
--   map_eq_of_rel {g f} h := by
--     ext a
--     exact (h (rel_map a)).symm

-- instance [SurjMapClass r] : InjMapClass (Set β) (Set α) where
--   map_injective g g' h := by
--     ext b
--     obtain ⟨a, rfl⟩ := map_surjective α b
--     exact congr(a ∈ $h)

-- instance [EquivMapClass r] : EquivMapClass (Set β) (Set α) where
--   map_surjective s := by
--     use {x | (Equiv.ofBijective map map_bijective).symm x ∈ s}
--     ext a
--     exact congr($(Equiv.ofBijective_symm_apply_apply _ _ _) ∈ s)

variable {r} {s t : Set α} {s' t' : Set β}

@[transport]
theorem Set.transport_mem (hs : SetRel r s' s) {a a'} (ha : r a a') :
    a ∈ s ↔ a' ∈ s' :=
  hs ha

-- TODO: remove this lemma
@[transport]
theorem Set.transport_mem' (hs : SetRel r s' s) {a a'} (ha : r a a') :
    a' ∈ s' ↔ a ∈ s :=
  hs ha |>.symm

@[transport] theorem Set.transport_univ : SetRel r .univ .univ := by simp [SetRel]
@[transport] theorem Set.transport_empty : SetRel r ∅ ∅ := by simp [SetRel]

@[transport] theorem Set.transport_singleton [RightUnique r] [LeftUnique r]
    {a : α} {b : β} (h : r a b) : SetRel r {b} {a} := by
  intro _ _ h'
  simp only [Set.mem_singleton_iff]
  transport [h, h', → r]
  rfl

@[transport]
theorem Set.transport_subset [LeftTotal r] [RightTotal r]
    (hs : SetRel r s' s) (ht : SetRel r t' t) :
    s ⊆ t ↔ s' ⊆ t' := by
  simp_rw [Set.subset_def]
  transport [hs, ht, → r]
  rfl

@[transport]
theorem Set.transport_ssubset [LeftTotal r] [RightTotal r]
    (hs : SetRel r s' s) (ht : SetRel r t' t) :
    s ⊂ t ↔ s' ⊂ t' := by
  simp_rw [Set.ssubset_def]
  transport [hs, ht, → r]
  rfl

variable {ι ι' : Sort*} {r' : ι → ι' → Prop} (s : ι → Set α) (t : ι' → Set β)

@[transport]
theorem Set.transport_iUnion [LeftTotal r'] [RightTotal r']
    (h : ∀ i i', r' i i' → SetRel r (t i') (s i)) :
    SetRel r (Set.iUnion t) (Set.iUnion s) := by
  intro a b hr
  push _ ∈ _
  transport [h, hr, → r, → r']
  rfl

@[transport]
theorem Set.transport_iInter [LeftTotal r'] [RightTotal r']
    (h : ∀ i i', r' i i' → SetRel r (t i') (s i)) :
    SetRel r (Set.iInter t) (Set.iInter s) := by
  intro a b hr
  push _ ∈ _
  transport [h, hr, → r, → r']
  rfl

end Set

section Finset

instance {A B : Type*} [SetLike A B] :
  MapTransport (@MapRel A (Set B) SetLike.coe) SetLike.coe where

instance {A B : Type*} [SetLike A B] : InjMapClass (@MapRel A (Set B) SetLike.coe) :=
  MapRel.instInjMapClass SetLike.coe_injective

variable {α : Type*}

attribute [transport SetLike.coe (A := Finset α)] Finset.coe_univ Finset.coe_empty
  Finset.coe_singleton Finset.coe_union Finset.coe_inter Finset.coe_subset Finset.coe_ssubset
  Finset.coe_insert Finset.coe_erase Finset.coe_nonempty Finset.mem_coe

abbrev FinsetToSetRel : Finset α → Set α → Prop := MapRel (↑)

end Finset





variable {α : Type*} (s t : Finset α) (s' t' : Set α)

example [DecidableEq α] (a : α) : insert a (∅ : Finset α) = {a} := by
  transport [FinsetToSetRel]
  guard_target = insert a (∅ : Set α) = {a}
  rw [← Set.singleton_def]

example [DecidableEq α] (a : α) : ∀ s : Finset α, s ∪ {a} = insert a s := by
  transport [FinsetToSetRel]
  intro s
  exact Set.union_singleton

/--
trace: α : Type u_1
s t : Finset α
s' t' : Set α
inst✝ : DecidableEq α
a : α
⊢ ¬∀ (s : Finset α), insert a ∅ = s
-/
#guard_msgs(trace) in
example [DecidableEq α] (a : α) : ¬ ∀ s : Set α, insert a ∅ = s := by
  transport [FinsetToSetRel]
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
-/
#guard_msgs(trace) in
example [DecidableEq α] (a : α) (s : Option (Finset α)) : s.elim {a} (fun s ↦ s.erase a) = ∅ := by
  transport [FinsetToSetRel] generalizing s
  trace_state
  sorry

-- In this example, transport cannot eliminate all occurrences of `s`, so it should fail.
/-- error: transport made no progress on `∀ (s : Finset α), p s ∧ s = s` -/
#guard_msgs(error) in
example (p : Finset α → Prop) : ∀ s, p s ∧ s = s := by
  transport [FinsetToSetRel]



def MyCompact (X : Type) [TopologicalSpace X] :=
  ∀ {ι : Type} {U : ι → Set X} (_ : ∀ i, IsOpen (U i)) (_ : Set.univ ⊆ ⋃ i, U i),
  ∃ t : Finset ι, Set.univ ⊆ ⋃ i ∈ t, U i

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

@[transport]
theorem transport_IsOpen {r : X → Y → Prop} {map : X → Y} [MapTransport r map] [SemiMapClass r]
    (hf : Continuous map) {s : Set X} {t : Set Y} (h : SetRel r t s) : IsOpen t → IsOpen s := by
  convert IsOpen.preimage hf
  ext x
  exact h (rel_map r x)

-- Yay, this now works!!!
example (f : X → Y) (hf : f.Surjective) (hf_cont : Continuous f)
    (hX : MyCompact X) : MyCompact Y := by
  unfold MyCompact
  have := MapRel.instSurjMapClass hf
  transport [MapRel f]
  exact hX

end Transport

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
