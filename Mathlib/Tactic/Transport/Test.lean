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

variable {α : Type*} (s t : Finset α) (s' t' : Set α)

def Finset.IsSet : Prop := s = s'

-- @[transport]
-- theorem Finset.transport_eq (hs : s.IsSet s') (ht : t.IsSet t') : (s = t) = (s' = t') := by
--   subst hs ht; simp

-- @[transport]
-- theorem Finset.transport_ne (hs : s.IsSet s') (ht : t.IsSet t') : (s ≠ t) = (s' ≠ t') := by
--   subst hs ht; simp

@[transport]
theorem Finset.transport_subset (hs : s.IsSet s') (ht : t.IsSet t') : (s ⊆ t) = (s' ⊆ t') := by
  subst hs ht; simp

@[transport]
theorem Finset.transport_ssubset (hs : s.IsSet s') (ht : t.IsSet t') : (s ⊂ t) = (s' ⊂ t') := by
  subst hs ht; simp

-- TODO: Nonempty, membership, cardinality.

@[transport]
theorem Finset.transport_empty : (∅ : Finset α).IsSet ∅ := by simp [IsSet]

@[transport]
theorem Finset.transport_singleton {a a' : α} (h : a = a') :
    ({a} : Finset α).IsSet {a'} := by
  simp [h, IsSet]

@[transport]
theorem Finset.transport_insert [DecidableEq α] {a a' : α} (ha : a = a') (hs : s.IsSet s') :
    (insert a s).IsSet (insert a' s') := by
  simp_all [IsSet]

@[transport]
theorem Finset.transport_erase [DecidableEq α] {a a' : α} (ha : a = a') (hs : s.IsSet s') :
    (s.erase a).IsSet (s' \ {a'}) := by
  simp_all [IsSet]

@[transport]
theorem Finset.transport_union [DecidableEq α] (hs : s.IsSet s') (ht : t.IsSet t') :
    (s ∪ t).IsSet (s' ∪ t') := by
  simp_all [IsSet]

@[transport]
theorem Finset.transport_inter [DecidableEq α] (hs : s.IsSet s') (ht : t.IsSet t') :
    (s ∩ t).IsSet (s' ∩ t') := by
  simp_all [IsSet]

attribute [transport] mt Or.imp And.imp

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
  rel_inj : Function.Injective map

class SurjMapClass (r : outParam <| α → β → Prop) extends MapClass r where
  rel_surj : Function.Surjective map

class EquivMapClass (r : outParam <| α → β → Prop) extends InjMapClass r, SurjMapClass r

instance : EquivMapClass (@Eq α) where
  map := (·)
  rel_map _ := rfl
  map_eq_of_rel := id
  rel_inj := Function.injective_id
  rel_surj := Function.surjective_id

open SemiMapClass

variable (r : α → β → Prop) {p : α → Sort*} {q : β → Sort*}

@[transport intro]
def forall_transport [SemiMapClass r]
    (h : ∀ (a b), r a b → q b → p a) :
    (∀ b, q b) → (∀ a, p a) :=
  fun h' a ↦ h _ _ (rel_map a) (h' (map a))

variable {p : α → Prop} {q : β → Prop}

@[transport intro]
theorem exists_transport [SemiMapClass r]
    (h : ∀ (a b), r a b → p a → q b) :
    (∃ a, p a) → (∃ b, q b) :=
  fun ⟨a, ha⟩ ↦ ⟨map a, h _ _ (rel_map a) ha⟩

@[transport intro]
theorem forall_transport_eq [SemiMapClass r] [SemiMapClass (flip r)]
    (h : ∀ (a b), r a b → q b = p a) :
    (∀ b, q b) = (∀ a, p a) :=
  propext
    ⟨forall_transport r fun _ _ ↦ (h _ _ · |>.mp),
    forall_transport (flip r) fun _ _ ↦ (h _ _ · |>.mpr)⟩

@[transport intro]
theorem exists_transport_eq [SemiMapClass r] [SemiMapClass (flip r)]
    (h : ∀ (a b), r a b → p a = q b) :
    (∃ a, p a) = (∃ b, q b) :=
  propext
    ⟨exists_transport r fun _ _ ↦ (h _ _ · |>.mp),
    exists_transport (flip r) fun _ _ ↦ (h _ _ · |>.mpr)⟩

end MapClass

instance : InjMapClass (Finset.IsSet (α := α)) where
  map := (↑)
  rel_map _ := by rfl
  map_eq_of_rel h := by exact h
  rel_inj := Finset.coe_injective


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
  exact InjMapClass.rel_inj <|
    (MapClass.map_eq_of_rel h).trans (MapClass.map_eq_of_rel h').symm

@[transport intro]
theorem ne_transport {α β : Type*} {r : α → β → Prop} [MapClass r]
    {a a' : α} {b b' : β}
    (h : r a b) (h' : r a' b') : b ≠ b' → a ≠ a' := by
  contrapose!
  exact eq_transport h h'

@[transport intro]
theorem ne_transport_eq {α β : Type*} {r : α → β → Prop} [InjMapClass r]
    {a a' : α} {b b' : β}
    (h : r a b) (h' : r a' b') : (a ≠ a') = (b ≠ b') :=
  (eq_transport_eq h h').to_iff.ne.eq

end Eq

section Option

open SemiMapClass MapClass

variable {α β α' β' : Type*}

inductive Option.IsOption (r : α → β → Prop) : Option α → Option β → Prop where
  | none : none.IsOption r none
  | some {a b} : r a b → (some a).IsOption r (some b)

instance (r : α → β → Prop) [SemiMapClass r] : SemiMapClass (Option.IsOption r) where
  map := Option.map map
  rel_map
    | none => .none
    | some a => .some (rel_map a)

instance (r : α → β → Prop) [MapClass r] : MapClass (Option.IsOption r) where
  map_eq_of_rel
    | .none => congr(none)
    | .some h => congr(some $(map_eq_of_rel h))

instance (r : α → β → Prop) [InjMapClass r] : InjMapClass (Option.IsOption r) where
  rel_inj := Option.map_injective InjMapClass.rel_inj

-- instance (r : α → β → Prop) [SurjMapClass r] : SurjMapClass (Option.IsOption r) where
--   rel_surj := by sorry


@[transport] -- TODO: variable name of `x`/`y` is not preserved
theorem Option.elim_transport {r : α → β → Prop} {r' : α' → β' → Prop}
    {o : Option α} {o' : Option β} (ho : o.IsOption r o')
    {x : α'} {x' : β'} (hx : r' x x')
    {f : α → α'} {f' : β → β'} (hf : ∀ (x y), r x y → r' (f x) (f' y)) :
    r' (o.elim x f) (o'.elim x' f') :=
  ho.casesOn hx (hf _ _)


end Option

inductive Prod.IsProd {α α' β β' : Type*} (r : α → β → Prop) (r' : α' → β' → Prop) :
    α × α' → β × β' → Prop where
  | mk (a a' b b') : r a b → r' a' b' → (a, a').IsProd r r' (b, b')


def Prod.forall_transport {α α' β β' : Type*}
    {p : α × α' → Sort*} {q : β × β' → Sort*}
    (r : β → α → Prop) (f : β → α) (hf : ∀ b, r b (f b))
    (r' : β' → α' → Prop) (f' : β' → α') (hf' : ∀ b, r' b (f' b))
    (h : ∀ (s : β × β') (s' : α × α'), s.IsProd r r' s' → p s' → q s) :
    (∀ s, p s) → (∀ s, q s) :=
  fun h' b ↦ by
    apply h b (b.map f f') _ (h' _)
    cases b with | mk b₁ b₂ => ?_
    apply IsProd.mk
    · apply hf
    · apply hf'


inductive Forall.IsForall {ι : Type*} {α β : ι → Type*} (r : ∀ {i}, α i → β i → Prop) :
    (∀ i, α i) → (∀ i, β i) → Prop
  | mk {a b} : (∀ i, r (a i) (b i)) → IsForall r a b

def Forall.forall_transport {ι : Type*} {α β : ι → Type*}
    {p : (∀ i, α i) → Sort*} {q : (∀ i, β i) → Sort*}
    (r : ∀ {i}, α i → β i → Prop) (f : ∀ {i}, β i → α i) (hf : ∀ {i}, ∀ b : β i, r (f b) b)
    (h : ∀ a : ∀ i, α i, ∀ b : ∀ i, β i, IsForall r a b → p a → q b) :
    (∀ a, p a) → (∀ b, q b) :=
  fun h' b ↦ h (f <| b ·) b (IsForall.mk fun i ↦ hf (b i)) (h' _)




-- set_option trace.Meta.isDefEq true in
-- set_option trace.Meta.synthInstance true in
-- set_option trace.Meta.grewrite true in
example [DecidableEq α] (s : Finset α) (a : α) : insert a (∅ : Finset α) = {a} := by
  transport
  guard_target = insert a (∅ : Set α) = {a}
  sorry

example [DecidableEq α] (a : α) : ∀ s : Finset α, insert a ∅ = s := by
  show_term transport
  guard_target = ∀ s : Set α, insert a ∅ = s
  sorry

-- set_option trace.Meta.isDefEq true in
-- set_option trace.Meta.synthInstance true in
-- set_option trace.Meta.grewrite true in

example [DecidableEq α] (a : α) : ∀ s : Finset α, Finset.erase ∅ a = s := by
  transport
  guard_target = ∀ s : Set α, (∅ : Set α) \ {a} = s
  sorry

example [DecidableEq α] (a : α) : ¬ ∀ s : Set α, insert a ∅ = s := by
  transport
  guard_target = ¬ ∀ s : Finset α, insert a ∅ = s
  sorry

-- Yay, this now works
example [DecidableEq α] (a : α) (s : Option (Finset α)) : s.elim {a} (·.erase a) = ∅ := by
  revert s a
  transport
  guard_target = ∀ a : α, ∀ s : Option (Set α), s.elim {a} (· \ {a}) = ∅
  sorry

-- TODO?: cleaner separation of local contexts of metavariables that are before/after?
