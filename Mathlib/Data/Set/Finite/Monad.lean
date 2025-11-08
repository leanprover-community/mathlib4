/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Functor

/-!
# Finiteness of the Set monad operations

## Tags

finite sets
-/

assert_not_exists IsOrderedRing MonoidWithZero

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/-! ### Fintype instances

Every instance here should have a corresponding `Set.Finite` constructor in the next section.
-/

section FintypeInstances

section monad
attribute [local instance] Set.monad

/-- If `s : Set α` is a set with `Fintype` instance and `f : α → Set β` is a function such that
each `f a`, `a ∈ s`, has a `Fintype` structure, then `s >>= f` has a `Fintype` structure. -/
def fintypeBind {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α → Set β)
    (H : ∀ a ∈ s, Fintype (f a)) : Fintype (s >>= f) :=
  Set.fintypeBiUnion s f H

instance fintypeBind' {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α → Set β)
    [∀ a, Fintype (f a)] : Fintype (s >>= f) :=
  Set.fintypeBiUnion' s f

end monad

instance fintypePure : ∀ a : α, Fintype (pure a : Set α) :=
  Set.fintypeSingleton

instance fintypeSeq [DecidableEq β] (f : Set (α → β)) (s : Set α) [Fintype f] [Fintype s] :
    Fintype (f.seq s) := by
  rw [seq_def]
  apply Set.fintypeBiUnion'

instance fintypeSeq' {α β : Type u} [DecidableEq β] (f : Set (α → β)) (s : Set α) [Fintype f]
    [Fintype s] : Fintype (f <*> s) :=
  Set.fintypeSeq f s

end FintypeInstances

end Set

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `Fintype` instances
in `Data.Set.Finite`. While every `Fintype` instance gives a `Finite` instance, those
instances that depend on `Fintype` or `Decidable` instances need an additional `Finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`Subtype.Finite` for subsets of a finite type.
-/


namespace Finite.Set

theorem finite_pure (a : α) : (pure a : Set α).Finite :=
  toFinite _

instance finite_seq (f : Set (α → β)) (s : Set α) [Finite f] [Finite s] : Finite (f.seq s) := by
  rw [seq_def]
  infer_instance

end Finite.Set

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the previous section
(or in the `Fintype` module).

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/


section SetFiniteConstructors

section monad
attribute [local instance] Set.monad

theorem Finite.bind {α β} {s : Set α} {f : α → Set β} (h : s.Finite) (hf : ∀ a ∈ s, (f a).Finite) :
    (s >>= f).Finite :=
  h.biUnion hf

end monad

theorem Finite.seq {f : Set (α → β)} {s : Set α} (hf : f.Finite) (hs : s.Finite) :
    (f.seq s).Finite :=
  hf.image2 _ hs

theorem Finite.seq' {α β : Type u} {f : Set (α → β)} {s : Set α} (hf : f.Finite) (hs : s.Finite) :
    (f <*> s).Finite :=
  hf.seq hs

end SetFiniteConstructors

end Set
