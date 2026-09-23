/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Logic.Equiv.Defs

/-!
# A type for VM-erased data

This file defines a type `Erased α` which is classically isomorphic to `α`,
but erased in the VM. That is, at runtime every value of `Erased α` is
represented as `0`, just like types and proofs.
-/

@[expose] public section


universe u

namespace Erased

/-- Extracts the erased value, if it is a type.

Note: `(mk a).OutType` is not definitionally equal to `a`.
-/
abbrev OutType (a : Erased (Sort u)) : Sort u :=
  out a

/-- Extracts the erased value, if it is a proof. -/
theorem out_proof {p : Prop} (a : Erased p) : p :=
  out a

/-- Equivalence between `Erased α` and `α`. -/
noncomputable def equiv (α) : Erased α ≃ α :=
  ⟨out, mk, mk_out, out_mk⟩

instance (α : Type u) : Repr (Erased α) :=
  ⟨fun _ _ => "Erased"⟩

instance (α : Type u) : ToString (Erased α) :=
  ⟨fun _ => "Erased"⟩

/-- Computably produce an erased value from a proof of nonemptiness. -/
def choice {α} (h : Nonempty α) : Erased α :=
  mk (Classical.choice h)

@[simp]
theorem nonempty_iff {α} : Nonempty (Erased α) ↔ Nonempty α :=
  ⟨fun ⟨a⟩ => ⟨a.out⟩, fun ⟨a⟩ => ⟨mk a⟩⟩

instance {α} [h : Nonempty α] : Inhabited (Erased α) :=
  ⟨choice h⟩

/-- `(>>=)` operation on `Erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `Monad`).
-/
def bind {α β} (a : Erased α) (f : α → Erased β) : Erased β :=
  ⟨fun b => (f a.out).1 b, (f a.out).2⟩

@[simp]
theorem bind_eq_out {α β} (a f) : @bind α β a f = f a.out := rfl

/-- Collapses two levels of erasure.
-/
def join {α} (a : Erased (Erased α)) : Erased α :=
  bind a id

@[simp]
theorem join_eq_out {α} (a) : @join α a = a.out :=
  rfl

/-- `(<$>)` operation on `Erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `Functor`).
-/
def map {α β} (f : α → β) (a : Erased α) : Erased β :=
  bind a (mk ∘ f)

@[simp]
theorem map_out {α β} {f : α → β} (a : Erased α) : (a.map f).out = f a.out := by simp [map]

protected instance Monad : Monad Erased where
  pure := @mk
  bind := @bind
  map := @map

@[simp]
theorem pure_def {α} : (pure : α → Erased α) = @mk _ :=
  rfl

@[simp]
theorem bind_def {α β} : ((· >>= ·) : Erased α → (α → Erased β) → Erased β) = @bind _ _ :=
  rfl

@[simp]
theorem map_def {α β} : ((· <$> ·) : (α → β) → Erased α → Erased β) = @map _ _ :=
  rfl

protected instance instLawfulMonad : LawfulMonad Erased :=
  { id_map := by intros; ext; simp
    map_const := by intros; ext; simp [Functor.mapConst]
    pure_bind := by intros; ext; simp
    bind_assoc := by intros; ext; simp
    bind_pure_comp := by intros; ext; simp
    bind_map := by intros; ext; simp [Seq.seq]
    seqLeft_eq := by intros; ext; simp [Seq.seq, SeqLeft.seqLeft]
    seqRight_eq := by intros; ext; simp [Seq.seq, SeqRight.seqRight]
    pure_seq := by intros; ext; simp [Seq.seq] }

end Erased
