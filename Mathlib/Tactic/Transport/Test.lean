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

attribute [transport] mt Or.imp exists_imp forall_imp
  Mathlib.Tactic.GCongr.imp_mono Mathlib.Tactic.GCongr.and_mono

namespace TransportTest

section MapClass

variable {α β : Type*}

/-
-- Injecion: `Finset` to `Set`, `Nat` to `Int`
-- Surjection: `Nat` to `ZMod`, quotients.

-/

class Transport {α β : Type*} (r : outParam <| α → β → Prop) (map : outParam <| α → β)

variable (α β : Type*) {r : α → β → Prop} {map : α → β} [Transport r map]

class SemiMapClass [Transport r map] where
  rel_map (a) : r a (map a)

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

variable {p : α → Sort*} {q : β → Sort*}

@[transport intro]
def forall_transport [SemiMapClass α β]
    (h : ∀ a b, r a b → q b → p a) :
    (∀ b, q b) → (∀ a, p a) :=
  fun h' a ↦ h _ _ (rel_map a) (h' (map a))

variable {p : α → Prop} {q : β → Prop}

@[transport intro]
theorem exists_transport [SemiMapClass α β]
    (h : ∀ a b, r a b → p a → q b) :
    (∃ a, p a) → (∃ b, q b) :=
  fun ⟨a, ha⟩ ↦ ⟨map a, h _ _ (rel_map a) ha⟩

@[transport intro]
theorem forall_transport_eq [SurjMapClass α β]
    (h : ∀ a b, r a b → q b = p a) :
    (∀ b, q b) = (∀ a, p a) := by
  refine propext ⟨forall_transport fun _ _ ↦ (h _ _ · |>.mp), ?_⟩
  intro h' b
  obtain ⟨a, rfl⟩ := map_surjective α b
  exact (h _ _ (rel_map a)).mpr (h' a)

@[transport intro]
theorem exists_transport_eq [SurjMapClass α β]
    (h : ∀ a b, r a b → p a = q b) :
    (∃ a, p a) = (∃ b, q b) := by
  refine propext ⟨exists_transport fun _ _ ↦ (h _ _ · |>.mp), ?_⟩
  intro ⟨b, h'⟩
  obtain ⟨a, rfl⟩ := map_surjective α b
  use a
  exact (h _ _ (rel_map a)).mpr h'

end MapClass

section Eq

variable {α β : Type*} {r : α → β → Prop} {map : α → β} [Transport r map]

@[transport intro]
theorem eq_transport [MapClass α β]
    {a a' : α} {b b' : β}
    (h : r a b) (h' : r a' b') : a = a' → b = b' := by
  rintro rfl
  rw [← map_eq_of_rel h, ← map_eq_of_rel h']

@[transport intro]
theorem eq_transport_eq [InjMapClass α β]
    {a a' : α} {b b' : β}
    (h : r a b) (h' : r a' b') : (a = a') = (b = b') := by
  refine propext ⟨eq_transport h h', ?_⟩
  rintro rfl
  exact map_injective <| (map_eq_of_rel h).trans (map_eq_of_rel h').symm

@[transport intro]
theorem ne_transport [MapClass α β]
    {a a' : α} {b b' : β}
    (h : r a b) (h' : r a' b') : b ≠ b' → a ≠ a' := by
  contrapose
  exact eq_transport h h'

@[transport]
theorem ne_transport_eq [InjMapClass α β]
    {a a' : α} {b b' : β}
    (h : r a b) (h' : r a' b') : (a ≠ a') = (b ≠ b') :=
  (eq_transport_eq h h').to_iff.ne.eq

end Eq

def MapRel {α β : Type*} (map : α → β) (a : α) (b : β) : Prop := map a = b

namespace MapRel

variable {α β : Type*} {map : α → β} [Transport (MapRel map) map]

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

variable (r : α → β → Prop) {map : α → β}

instance [Transport r map] : Transport (OptionRel r) (.map map) where

variable [Transport r map]

instance [SemiMapClass α β] : SemiMapClass (Option α) (Option β) where
  rel_map
    | none => .none
    | some a => .some (rel_map a)

instance [MapClass α β] : MapClass (Option α) (Option β) where
  map_eq_of_rel
    | .none => congr(none)
    | .some h => congr(some $(map_eq_of_rel h))

instance [InjMapClass α β] : InjMapClass (Option α) (Option β) where
  map_injective := Option.map_injective map_injective

-- TODO:
-- instance [SurjMapClass α β] : SurjMapClass (Option α) (Option β) where
--   rel_surj := by sorry


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

variable (r : α → β → Prop) (r' : α' → β' → Prop) {map : α → β} {map' : α' → β'}

instance [Transport r map] [Transport r' map'] : Transport (ProdRel r r') (.map map map') where

variable [Transport r map] [Transport r' map']

instance [SemiMapClass α β] [SemiMapClass α' β'] : SemiMapClass (α × α') (β × β') where
  rel_map | (a, b) => ⟨rel_map a, rel_map b⟩

instance [MapClass α β] [MapClass α' β'] : MapClass (α × α') (β × β') where
  map_eq_of_rel | ⟨h, h'⟩ => congr(⟨$(map_eq_of_rel h), $(map_eq_of_rel h')⟩)

instance [InjMapClass α β] [InjMapClass α' β'] : InjMapClass (α × α') (β × β') where
  map_injective := Function.Injective.prodMap map_injective map_injective

instance [SurjMapClass α β] [SurjMapClass α' β'] : SurjMapClass (α × α') (β × β') where
  map_surjective := Function.Surjective.prodMap (map_surjective α) (map_surjective α')

instance [EquivMapClass α β] [EquivMapClass α' β'] : EquivMapClass (α × α') (β × β') where

end Prod

section Pi

variable {ι : Type*} {α β : ι → Type*} (r : ∀ i, α i → β i → Prop) (map : ∀ {i}, α i → β i)

@[expose, implicit_reducible]
def PiRel (r : ∀ i, α i → β i → Prop) (a : ∀ i, α i) (b : ∀ i, β i) : Prop :=
  ∀ i, r i (a i) (b i)

instance [∀ i, Transport (r i) map] : Transport (PiRel r) (map <| · ·) where

variable [∀ i, Transport (r i) map]

instance [∀ i, SemiMapClass (α i) (β i)] : SemiMapClass (∀ i, α i) (∀ i, β i) where
  rel_map x := (rel_map <| x ·)

instance [∀ i, MapClass (α i) (β i)] : MapClass (∀ i, α i) (∀ i, β i) where
  map_eq_of_rel h := congr(fun i ↦ $(map_eq_of_rel (h i)))

instance [∀ i, InjMapClass (α i) (β i)] : InjMapClass (∀ i, α i) (∀ i, β i) where
  map_injective a b h := by
    ext i
    exact map_injective congr($h i)

instance [∀ i, SurjMapClass (α i) (β i)] : SurjMapClass (∀ i, α i) (∀ i, β i) where
  map_surjective b := by
    choose x hx using fun i (b : β i) ↦ map_surjective (α i) b
    use fun i ↦ x i (b i)
    ext i
    exact hx i (b i)

instance [∀ i, EquivMapClass (α i) (β i)] : EquivMapClass (∀ i, α i) (∀ i, β i) where

end Pi

section Function

variable {α β γ : Type*}

-- TODO: make a relation that generalizes both `PiRel` and `FunctionRel`?
variable (γ) in
@[implicit_reducible]
def FunctionRel (r : α → β → Prop) (g : β → γ) (f : α → γ) : Prop :=
  ∀ {a b}, r a b → f a = g b

variable (r : α → β → Prop) {map : α → β}

instance [Transport r map] : Transport (FunctionRel γ r) (· <| map ·) where

variable [Transport r map]

instance [MapClass α β] : MapClass (β → γ) (α → γ) where
  rel_map g := by
    intro a b h
    exact congr(g $(map_eq_of_rel h))
  map_eq_of_rel {g f} h := by
    ext a
    exact (h (rel_map a)).symm

instance [SurjMapClass α β] : InjMapClass (β → γ) (α → γ) where
  map_injective g g' h := by
    ext b
    obtain ⟨a, rfl⟩ := map_surjective α b
    exact congr($h a)

instance [EquivMapClass α β] : EquivMapClass (β → γ) (α → γ) where
  map_surjective f := by
    use (f <| (Equiv.ofBijective map map_bijective).symm ·)
    ext a
    exact congr(f $(Equiv.ofBijective_symm_apply_apply _ _ _))

end Function

section Set

variable {α β : Type*}

@[implicit_reducible, expose]
def SetRel (r : α → β → Prop) (t : Set β) (s : Set α) : Prop :=
  ∀ {a b}, r a b → (a ∈ s) = (b ∈ t)

variable (r : α → β → Prop) {map : α → β}

instance [Transport r map] : Transport (SetRel r) ({x | map x ∈ ·}) where

variable [Transport r map]

instance [MapClass α β] : MapClass (Set β) (Set α) where
  rel_map s := by
    intro a b h
    exact congr($(map_eq_of_rel h) ∈ s)
  map_eq_of_rel {g f} h := by
    ext a
    exact (h (rel_map a)).symm.to_iff

instance [SurjMapClass α β] : InjMapClass (Set β) (Set α) where
  map_injective g g' h := by
    ext b
    obtain ⟨a, rfl⟩ := map_surjective α b
    exact congr(a ∈ $h)

instance [EquivMapClass α β] : EquivMapClass (Set β) (Set α) where
  map_surjective s := by
    use {x | (Equiv.ofBijective map map_bijective).symm x ∈ s}
    ext a
    exact congr($(Equiv.ofBijective_symm_apply_apply _ _ _) ∈ s)

variable {r} {s t : Set α} {s' t' : Set β}

@[transport intro]
theorem Set.transport_mem [SemiMapClass α β] (hs : SetRel r s' s) {a a'} (ha : r a a') :
    (a ∈ s) = (a' ∈ s') :=
  hs ha

-- TODO: remove this lemma
@[transport intro]
theorem Set.transport_mem' [SemiMapClass α β] (hs : SetRel r s' s) {a a'} (ha : r a a') :
    (a' ∈ s') = (a ∈ s) :=
  hs ha |>.symm

@[transport] theorem Set.transport_univ : SetRel r .univ .univ := by simp [SetRel]
@[transport] theorem Set.transport_empty : SetRel r ∅ ∅ := by simp [SetRel]

@[transport intro]
theorem Set.transport_subset [SurjMapClass α β] (hs : SetRel r s' s) (ht : SetRel r t' t) :
    (s ⊆ t) = (s' ⊆ t') := by
  simp_rw [Set.subset_def]
  transport α to β
  rfl

@[transport intro]
theorem Set.transport_ssubset [SurjMapClass α β] (hs : SetRel r s' s) (ht : SetRel r t' t) :
    (s ⊂ t) = (s' ⊂ t') := by
  simp_rw [Set.ssubset_def]
  transport β to α
  rfl

variable {ι : Sort*} (s : ι → Set α) (t : ι → Set β)

@[transport]
theorem Set.transport_iUnion [SemiMapClass α β] (h : ∀ i, SetRel r (t i) (s i)) :
    SetRel r (Set.iUnion t) (Set.iUnion s) := by
  intro a b hr
  push _ ∈ _
  transport α to β
  rfl

@[transport]
theorem Set.transport_iInter [SemiMapClass α β] (h : ∀ i, SetRel r (t i) (s i)) :
    SetRel r (Set.iInter t) (Set.iInter s) := by
  intro a b hr
  push _ ∈ _
  transport β to α
  rfl

end Set

section Finset

variable {α : Type*}

abbrev FinsetToSetRel : Finset α → Set α → Prop := MapRel (↑)

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

instance : Transport (@FinsetToSetRel α) (↑) where

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

-- In this example, transport cannot eliminate all occurrences of `s`, so it should fails.
/--
error: unsolved goals
α : Type u_1
s t : Finset α
s' t' : Set α
p : Finset α → Prop
⊢ ∀ (s : Set α), p _fvar.19324 ∧ s = s
-/
#guard_msgs in
example (p : Finset α → Prop) : ∀ s, p s ∧ s = s := by
  transport Finset α to Set α



def MyCompact (X : Type) [TopologicalSpace X] :=
  ∀ {ι : Type} {U : ι → Set X} (_ : ∀ i, IsOpen (U i)) (_ : Set.univ ⊆ ⋃ i, U i),
  ∃ t : Finset ι, Set.univ ⊆ ⋃ i ∈ t, U i

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

@[transport intro]
theorem transport_IsOpen {r : X → Y → Prop} {map : X → Y} [Transport r map] [SemiMapClass X Y]
    (hf : Continuous map) {s : Set X} {t : Set Y} (h : SetRel r t s) : IsOpen t → IsOpen s := by
  convert IsOpen.preimage hf
  ext x
  exact (h (rel_map x)).to_iff

-- Yay, this now works!!!
example (f : X → Y) (hf : f.Surjective) (hf_cont : Continuous f)
    (hX : MyCompact X) : MyCompact Y := by
  unfold MyCompact
  have : Transport (MapRel f) f := ⟨⟩; have := MapRel.instSurjMapClass hf
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
