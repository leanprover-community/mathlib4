module

public import Mathlib.Tactic.Transport.Core
public import Mathlib.Tactic
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

namespace Transport

section MapClass

variable {α β : Type*} (r : α → β → Prop)

/-
-- Injecion: `Finset` to `Set`, `Nat` to `Int`
-- Surjection: `Nat` to `ZMod`, quotients.

-/

class SemiMapClass (r : outParam <| α → β → Prop) where
  map : α → β
  rel_map (a) : r a (map a)

class MapClass (r : outParam <| α → β → Prop) extends SemiMapClass r where
  map_eq_of_rel {a b} : r a b → map a = b

class InjMapClass (r : outParam <| α → β → Prop) extends MapClass r where
  map_injective (r) : Function.Injective map

class SurjMapClass (r : outParam <| α → β → Prop) extends MapClass r where
  map_surjective (r) : Function.Surjective map

class EquivMapClass (r : outParam <| α → β → Prop) extends InjMapClass r, SurjMapClass r

export SemiMapClass (map rel_map)
export MapClass (map_eq_of_rel)
export InjMapClass (map_injective)
export SurjMapClass (map_surjective)

lemma map_bijective [EquivMapClass r] : Function.Bijective (map (r := r)) :=
  ⟨map_injective r, map_surjective r⟩

variable (r : α → β → Prop) {p : α → Sort*} {q : β → Sort*}

@[transport intro]
def forall_transport [SemiMapClass r]
    (h : ∀ a b, r a b → q b → p a) :
    (∀ b, q b) → (∀ a, p a) :=
  fun h' a ↦ h _ _ (rel_map a) (h' (map a))

variable {p : α → Prop} {q : β → Prop}

@[transport intro]
theorem exists_transport [SemiMapClass r]
    (h : ∀ a b, r a b → p a → q b) :
    (∃ a, p a) → (∃ b, q b) :=
  fun ⟨a, ha⟩ ↦ ⟨map a, h _ _ (rel_map a) ha⟩

@[transport intro]
theorem forall_transport_eq [SurjMapClass r]
    (h : ∀ a b, r a b → q b = p a) :
    (∀ b, q b) = (∀ a, p a) := by
  refine propext ⟨forall_transport r fun _ _ ↦ (h _ _ · |>.mp), ?_⟩
  intro h' b
  obtain ⟨a, rfl⟩ := map_surjective r b
  exact (h _ _ (rel_map a)).mpr (h' a)


@[transport intro]
theorem exists_transport_eq [SemiMapClass r] [SemiMapClass (flip r)]
    (h : ∀ a b, r a b → p a = q b) :
    (∃ a, p a) = (∃ b, q b) :=
  propext
    ⟨exists_transport r fun _ _ ↦ (h _ _ · |>.mp),
    exists_transport (flip r) fun _ _ ↦ (h _ _ · |>.mpr)⟩

end MapClass

section MapRel

variable {α β : Type*} (map : α → β)

def MapRel (a : α) (b : β) : Prop := map a = b

@[implicit_reducible]
def MapRel.instMapClass : MapClass (MapRel map) where
  map
  rel_map _ := by rfl
  map_eq_of_rel := by exact id

@[implicit_reducible]
def MapRel.instInjMapClass (h : Function.Injective map) : InjMapClass (MapRel map) :=
  let := MapRel.instMapClass map
  ⟨h⟩

@[implicit_reducible]
def MapRel.instSurjMapClass (h : Function.Surjective map) : SurjMapClass (MapRel map) :=
  let := MapRel.instMapClass map
  ⟨h⟩

end MapRel

section Eq

@[transport intro]
theorem eq_transport {α β : Type*} {r : α → β → Prop} [MapClass r]
    {a a' : α} {b b' : β}
    (h : r a b) (h' : r a' b') : a = a' → b = b' := by
  rintro rfl
  rw [← MapClass.map_eq_of_rel h, ← MapClass.map_eq_of_rel h']

@[transport intro]
theorem eq_transport_eq {α β : Type*} {r : α → β → Prop} [InjMapClass r]
    {a a' : α} {b b' : β}
    (h : r a b) (h' : r a' b') : (a = a') = (b = b') := by
  refine propext ⟨eq_transport h h', ?_⟩
  rintro rfl
  exact map_injective r <| (MapClass.map_eq_of_rel h).trans (MapClass.map_eq_of_rel h').symm

@[transport intro]
theorem ne_transport {α β : Type*} {r : α → β → Prop} [MapClass r]
    {a a' : α} {b b' : β}
    (h : r a b) (h' : r a' b') : b ≠ b' → a ≠ a' := by
  contrapose
  exact eq_transport h h'

@[transport intro]
theorem ne_transport_eq {α β : Type*} {r : α → β → Prop} [InjMapClass r]
    {a a' : α} {b b' : β}
    (h : r a b) (h' : r a' b') : (a ≠ a') = (b ≠ b') :=
  (eq_transport_eq h h').to_iff.ne.eq

end Eq

section Option

variable {α β α' β' : Type*}

inductive OptionRel (r : α → β → Prop) : Option α → Option β → Prop where
  | none : OptionRel r none none
  | some {a b} : r a b → OptionRel r (some a) (some b)

instance (r : α → β → Prop) [SemiMapClass r] : SemiMapClass (OptionRel r) where
  map := Option.map map
  rel_map
    | none => .none
    | some a => .some (rel_map a)

instance (r : α → β → Prop) [MapClass r] : MapClass (OptionRel r) where
  map_eq_of_rel
    | .none => congr(none)
    | .some h => congr(some $(map_eq_of_rel h))

instance (r : α → β → Prop) [InjMapClass r] : InjMapClass (OptionRel r) where
  map_injective := Option.map_injective (map_injective r)

-- TODO:
-- instance (r : α → β → Prop) [SurjMapClass r] : SurjMapClass (OptionRel r) where
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

instance (r : α → β → Prop) (r' : α' → β' → Prop) [SemiMapClass r] [SemiMapClass r'] :
    SemiMapClass (ProdRel r r') where
  map := Prod.map map map
  rel_map | (a, b) => ⟨rel_map a, rel_map b⟩

instance (r : α → β → Prop) (r' : α' → β' → Prop) [MapClass r] [MapClass r'] :
    MapClass (ProdRel r r') where
  map_eq_of_rel | ⟨h, h'⟩ => congr(⟨$(map_eq_of_rel h), $(map_eq_of_rel h')⟩)

instance (r : α → β → Prop) (r' : α' → β' → Prop) [InjMapClass r] [InjMapClass r'] :
    InjMapClass (ProdRel r r') where
  map_injective := Function.Injective.prodMap (map_injective r) (map_injective r')

instance (r : α → β → Prop) (r' : α' → β' → Prop) [SurjMapClass r] [SurjMapClass r'] :
    SurjMapClass (ProdRel r r') where
  map_surjective := Function.Surjective.prodMap (map_surjective r) (map_surjective r')

instance (r : α → β → Prop) (r' : α' → β' → Prop) [EquivMapClass r] [EquivMapClass r'] :
    EquivMapClass (ProdRel r r') where

end Prod

section Pi

variable {ι : Type*} {α β : ι → Type*}

@[expose, implicit_reducible]
def PiRel (r : ∀ i, α i → β i → Prop) (a : ∀ i, α i) (b : ∀ i, β i) : Prop :=
  ∀ i, r i (a i) (b i)

instance (r : ∀ i, α i → β i → Prop) [∀ i, SemiMapClass (r i)] : SemiMapClass (PiRel r) where
  map x := (map <| x ·)
  rel_map x := by exact (rel_map <| x ·)

instance (r : ∀ i, α i → β i → Prop) [∀ i, MapClass (r i)] : MapClass (PiRel r) where
  map_eq_of_rel h := by exact congr(fun i ↦ $(map_eq_of_rel (h i)))

instance (r : ∀ i, α i → β i → Prop) [∀ i, InjMapClass (r i)] : InjMapClass (PiRel r) where
  map_injective a b h := by
    ext i
    exact map_injective (r i) congr($h i)

instance (r : ∀ i, α i → β i → Prop) [∀ i, SurjMapClass (r i)] : SurjMapClass (PiRel r) where
  map_surjective b := by
    choose x hx using (map_surjective <| r ·)
    use fun i ↦ x i (b i)
    ext i
    exact hx i (b i)

instance (r : ∀ i, α i → β i → Prop) [∀ i, EquivMapClass (r i)] : EquivMapClass (PiRel r) where

end Pi

section Function

variable {α β γ : Type*}

-- TODO: make a relation that generalizes both `PiRel` and `FunctionRel`?
def FunctionRel (r : α → β → Prop) (g : β → γ) (f : α → γ) : Prop :=
  ∀ {a b}, r a b → f a = g b

instance (r : α → β → Prop) [MapClass r] : MapClass (FunctionRel (γ := γ) r) where
  map g := (g <| map ·)
  rel_map g := by
    intro a b h
    exact congr(g $(map_eq_of_rel h))
  map_eq_of_rel {g f} h := by
    ext a
    exact (h (rel_map a)).symm

instance (r : α → β → Prop) [SurjMapClass r] : InjMapClass (FunctionRel (γ := γ) r) where
  map_injective g g' h := by
    ext b
    obtain ⟨a, rfl⟩ := map_surjective r b
    exact congr($h a)

instance (r : α → β → Prop) [EquivMapClass r] : EquivMapClass (FunctionRel (γ := γ) r) where
  map_surjective f := by
    use (f <| (Equiv.ofBijective map (map_bijective r)).symm ·)
    ext a
    exact congr(f $(Equiv.ofBijective_symm_apply_apply _ _ _))

end Function

section Set

variable {α β : Type*}

@[implicit_reducible, expose]
def SetRel (r : α → β → Prop) (t : Set β) (s : Set α) : Prop :=
  ∀ {a b}, r a b → (a ∈ s) = (b ∈ t)

instance (r : α → β → Prop) [MapClass r] : MapClass (SetRel r) where
  map s := {x | map x ∈ s}
  rel_map s := by
    intro a b h
    exact congr($(map_eq_of_rel h) ∈ s)
  map_eq_of_rel {g f} h := by
    ext a
    exact (h (rel_map a)).symm.to_iff

instance (r : α → β → Prop) [SurjMapClass r] : InjMapClass (SetRel r) where
  map_injective g g' h := by
    ext b
    obtain ⟨a, rfl⟩ := map_surjective r b
    exact congr(a ∈ $h)

instance (r : α → β → Prop) [EquivMapClass r] : EquivMapClass (SetRel r) where
  map_surjective s := by
    use {x | (Equiv.ofBijective map (map_bijective r)).symm x ∈ s}
    ext a
    exact congr($(Equiv.ofBijective_symm_apply_apply _ _ _) ∈ s)

variable (r : α → β → Prop) {s t : Set α} {s' t' : Set β}

@[transport intro]
theorem Set.transport_mem [SemiMapClass r] (hs : SetRel r s' s) {a a'} (ha : r a a') :
    (a ∈ s) = (a' ∈ s') :=
  hs ha

-- TODO: remove this lemma
@[transport intro]
theorem Set.transport_mem' [SemiMapClass r] (hs : SetRel r s' s) {a a'} (ha : r a a') :
    (a' ∈ s') = (a ∈ s) :=
  hs ha |>.symm

@[transport] theorem Set.transport_univ : SetRel r .univ .univ := by simp [SetRel]
@[transport] theorem Set.transport_empty : SetRel r ∅ ∅ := by simp [SetRel]

@[transport intro]
theorem Set.transport_subset [SurjMapClass r] (hs : SetRel r s' s) (ht : SetRel r t' t) :
    (s ⊆ t) = (s' ⊆ t') := by
  refine propext ⟨?_, ?_⟩
  · intro h b
    obtain ⟨a, rfl⟩ := map_surjective r b
    specialize @h a
    rwa [hs (rel_map a), ht (rel_map a)] at h
  · intro h a
    specialize @h (map a)
    rwa [hs (rel_map a), ht (rel_map a)]

variable {ι : Sort*} (s : ι → Set α) (t : ι → Set β)

@[transport]
theorem Set.transport_iUnion [SemiMapClass r] (h : ∀ i, SetRel r (t i) (s i)) :
    SetRel r (Set.iUnion t) (Set.iUnion s) := by
  intro a b hr
  push _ ∈ _
  transport α to β
  rfl

end Set

section Finset

variable {α : Type*}

abbrev FinsetSetRel := MapRel (fun s : Finset α ↦ (s : Set α))

variable (s t : Finset α) (s' t' : Set α)

@[transport]
theorem Finset.transport_subset (hs : FinsetSetRel s s') (ht : FinsetSetRel t t') :
    (s ⊆ t) = (s' ⊆ t') := by
  subst hs ht; simp

@[transport]
theorem Finset.transport_ssubset (hs : FinsetSetRel s s') (ht : FinsetSetRel t t') :
    (s ⊂ t) = (s' ⊂ t') := by
  subst hs ht; simp

@[transport]
theorem Finset.transport_empty : FinsetSetRel (∅ : Finset α) ∅ := by simp [FinsetSetRel, MapRel]

@[transport]
theorem Finset.transport_singleton {a a' : α} (h : a = a') :
    FinsetSetRel ({a} : Finset α) {a'} := by
  simp [h, FinsetSetRel, MapRel]

variable [DecidableEq α]

@[transport]
theorem Finset.transport_insert {a a' : α} (ha : a = a') (hs : FinsetSetRel s s') :
    FinsetSetRel (insert a s) (insert a' s') := by
  simp_all [FinsetSetRel, MapRel]

@[transport]
theorem Finset.transport_erase {a a' : α} (ha : a = a') (hs : FinsetSetRel s s') :
    FinsetSetRel (s.erase a) (s' \ {a'}) := by
  simp_all [FinsetSetRel, MapRel]

@[transport]
theorem Finset.transport_union (hs : FinsetSetRel s s') (ht : FinsetSetRel t t') :
    FinsetSetRel (s ∪ t) (s' ∪ t') := by
  simp_all [FinsetSetRel, MapRel]

@[transport]
theorem Finset.transport_inter (hs : FinsetSetRel s s') (ht : FinsetSetRel t t') :
    FinsetSetRel (s ∩ t) (s' ∩ t') := by
  simp_all [FinsetSetRel, MapRel]

-- TODO: Nonempty, membership, cardinality.

instance : InjMapClass (FinsetSetRel (α := α)) where
  map := (↑)
  rel_map _ := by rfl
  map_eq_of_rel h := by exact h
  map_injective := Finset.coe_injective

end Finset





variable {α : Type*} (s t : Finset α) (s' t' : Set α)


-- set_option trace.Meta.isDefEq true in
-- set_option trace.Meta.synthInstance true in
-- set_option trace.Meta.grewrite true in
example [DecidableEq α] (s : Finset α) (a : α) : insert a (∅ : Finset α) = {a} := by
  transport Finset α to Set α
  guard_target = insert a (∅ : Set α) = {a}
  sorry

example [DecidableEq α] (a : α) : ∀ s : Finset α, insert a ∅ = s := by
  transport Finset α to Set α
  guard_target = ∀ s : Set α, insert a ∅ = s
  sorry

-- set_option trace.Meta.isDefEq true in
-- set_option trace.Meta.synthInstance true in
-- set_option trace.Meta.grewrite true in

example [DecidableEq α] (a : α) : ∀ s : Finset α, Finset.erase ∅ a = s := by
  transport Finset α to Set α
  guard_target = ∀ s : Set α, (∅ : Set α) \ {a} = s
  sorry

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



def MyCompact (X : Type) [TopologicalSpace X] :=
  ∀ {ι : Type} {U : ι → Set X} (_ : ∀ i, IsOpen (U i)) (_ : Set.univ ⊆ ⋃ i, U i),
  ∃ t : Finset ι, Set.univ ⊆ ⋃ i ∈ t, U i

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

@[transport intro]
theorem transport_IsOpen (r : X → Y → Prop) [SurjMapClass r] (hf : Continuous (map (r := r)))
    {s : Set X} {t : Set Y} (h : SetRel r t s) : IsOpen t → IsOpen s := by
  convert IsOpen.preimage hf
  ext x
  exact (h (rel_map x)).to_iff

-- Yay, this now works!!!
example (f : X → Y) (hf : f.Surjective) (hf_cont : Continuous f)
    (hX : MyCompact X) : MyCompact Y := by
  unfold MyCompact
  let := MapRel.instSurjMapClass f hf
  transport Y to X
  · exact hX
  · exact hf_cont

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
-- TODO?: cleaner separation of local contexts of metavariables that are before/after?
