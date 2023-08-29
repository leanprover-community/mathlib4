/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Logic.Equiv.Defs

#align_import data.erased from "leanprover-community/mathlib"@"10b4e499f43088dd3bb7b5796184ad5216648ab1"

/-!
# A type for VM-erased data

This file defines a type `Erased α` which is classically isomorphic to `α`,
but erased in the VM. That is, at runtime every value of `Erased α` is
represented as `0`, just like types and proofs.
-/


universe u

/-- `Erased α` is the same as `α`, except that the elements
  of `Erased α` are erased in the VM in the same way as types
  and proofs. This can be used to track data without storing it
  literally. -/
def Erased (α : Sort u) : Sort max 1 u :=
  Σ's : α → Prop, ∃ a, (fun b => a = b) = s
#align erased Erased

namespace Erased

/-- Erase a value. -/
@[inline]
def mk {α} (a : α) : Erased α :=
  ⟨fun b => a = b, a, rfl⟩
#align erased.mk Erased.mk

/-- Extracts the erased value, noncomputably. -/
noncomputable def out {α} : Erased α → α
  | ⟨_, h⟩ => Classical.choose h
#align erased.out Erased.out

/-- Extracts the erased value, if it is a type.

Note: `(mk a).OutType` is not definitionally equal to `a`.
-/
@[reducible]
def OutType (a : Erased (Sort u)) : Sort u :=
  out a
#align erased.out_type Erased.OutType

/-- Extracts the erased value, if it is a proof. -/
theorem out_proof {p : Prop} (a : Erased p) : p :=
  out a
#align erased.out_proof Erased.out_proof

@[simp]
theorem out_mk {α} (a : α) : (mk a).out = a := by
  let h := (mk a).2; show Classical.choose h = a
  -- ⊢ out (mk a) = a
                     -- ⊢ Classical.choose h = a
  have := Classical.choose_spec h
  -- ⊢ Classical.choose h = a
  exact cast (congr_fun this a).symm rfl
  -- 🎉 no goals
#align erased.out_mk Erased.out_mk

@[simp]
theorem mk_out {α} : ∀ a : Erased α, mk (out a) = a
  | ⟨s, h⟩ => by simp [mk]; congr; exact Classical.choose_spec h
                 -- ⊢ { fst := fun b => out { fst := s, snd := h } = b, snd := (_ : ∃ a, (fun b => …
                            -- ⊢ (fun b => out { fst := s, snd := h } = b) = s
                                   -- 🎉 no goals
#align erased.mk_out Erased.mk_out

@[ext]
theorem out_inj {α} (a b : Erased α) (h : a.out = b.out) : a = b := by simpa using congr_arg mk h
                                                                       -- 🎉 no goals
#align erased.out_inj Erased.out_inj

/-- Equivalence between `Erased α` and `α`. -/
noncomputable def equiv (α) : Erased α ≃ α :=
  ⟨out, mk, mk_out, out_mk⟩
#align erased.equiv Erased.equiv

instance (α : Type u) : Repr (Erased α) :=
  ⟨fun _ _ => "Erased"⟩

instance (α : Type u) : ToString (Erased α) :=
  ⟨fun _ => "Erased"⟩

-- Porting note: Deleted `has_to_format`

/-- Computably produce an erased value from a proof of nonemptiness. -/
def choice {α} (h : Nonempty α) : Erased α :=
  mk (Classical.choice h)
#align erased.choice Erased.choice

@[simp]
theorem nonempty_iff {α} : Nonempty (Erased α) ↔ Nonempty α :=
  ⟨fun ⟨a⟩ => ⟨a.out⟩, fun ⟨a⟩ => ⟨mk a⟩⟩
#align erased.nonempty_iff Erased.nonempty_iff

instance {α} [h : Nonempty α] : Inhabited (Erased α) :=
  ⟨choice h⟩

/-- `(>>=)` operation on `Erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `Monad`).
-/
def bind {α β} (a : Erased α) (f : α → Erased β) : Erased β :=
  ⟨fun b => (f a.out).1 b, (f a.out).2⟩
#align erased.bind Erased.bind

@[simp]
theorem bind_eq_out {α β} (a f) : @bind α β a f = f a.out := rfl
#align erased.bind_eq_out Erased.bind_eq_out

/-- Collapses two levels of erasure.
-/
def join {α} (a : Erased (Erased α)) : Erased α :=
  bind a id
#align erased.join Erased.join

@[simp]
theorem join_eq_out {α} (a) : @join α a = a.out :=
  bind_eq_out _ _
#align erased.join_eq_out Erased.join_eq_out

/-- `(<$>)` operation on `Erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `Functor`).
-/
def map {α β} (f : α → β) (a : Erased α) : Erased β :=
  bind a (mk ∘ f)
#align erased.map Erased.map

@[simp]
theorem map_out {α β} {f : α → β} (a : Erased α) : (a.map f).out = f a.out := by simp [map]
                                                                                 -- 🎉 no goals
#align erased.map_out Erased.map_out

protected instance Monad : Monad Erased where
  pure := @mk
  bind := @bind
  map := @map
#align erased.monad Erased.Monad

@[simp]
theorem pure_def {α} : (pure : α → Erased α) = @mk _ :=
  rfl
#align erased.pure_def Erased.pure_def

@[simp]
theorem bind_def {α β} : ((· >>= ·) : Erased α → (α → Erased β) → Erased β) = @bind _ _ :=
  rfl
#align erased.bind_def Erased.bind_def

@[simp]
theorem map_def {α β} : ((· <$> ·) : (α → β) → Erased α → Erased β) = @map _ _ :=
  rfl
#align erased.map_def Erased.map_def

--Porting note: Old proof `by refine' { .. } <;> intros <;> ext <;> simp`
protected instance LawfulMonad : LawfulMonad Erased :=
  { Erased.Monad with
    id_map := by intros; ext; simp
                 -- ⊢ id <$> x✝ = x✝
                    -- ⊢ Functor.mapConst = Functor.map ∘ Function.const β✝
                            -- ⊢ out (Functor.mapConst x✝¹ x✝) = out ((Functor.map ∘ Function.const β✝) x✝¹ x✝)
                                 -- 🎉 no goals
                         -- ⊢ out (id <$> x✝) = out x✝
                              -- 🎉 no goals
    map_const := by intros; ext; simp [Functor.mapConst]
    pure_bind := by intros; ext; simp
                    -- ⊢ pure x✝ >>= f✝ = f✝ x✝
                            -- ⊢ out (pure x✝ >>= f✝) = out (f✝ x✝)
                         -- ⊢ (do
                                 -- ⊢ (out do
                     -- ⊢ (SeqLeft.seqLeft x✝ fun x => y✝) = Seq.seq (Function.const β✝ <$> x✝) fun x  …
                             -- ⊢ out (SeqLeft.seqLeft x✝ fun x => y✝) = out (Seq.seq (Function.const β✝ <$> x …
                                  -- 🎉 no goals
                                      -- 🎉 no goals
                      -- ⊢ (SeqRight.seqRight x✝ fun x => y✝) = Seq.seq (Function.const α✝ id <$> x✝) f …
                              -- ⊢ out (SeqRight.seqRight x✝ fun x => y✝) = out (Seq.seq (Function.const α✝ id  …
                                   -- 🎉 no goals
                                 -- 🎉 no goals
                   -- ⊢ (Seq.seq (pure g✝) fun x => x✝) = g✝ <$> x✝
                           -- ⊢ out (Seq.seq (pure g✝) fun x => x✝) = out (g✝ <$> x✝)
                                -- 🎉 no goals
                   -- ⊢ (do
                           -- ⊢ (out do
                                -- 🎉 no goals
    bind_assoc := by intros; ext; simp
                     -- ⊢ x✝ >>= f✝ >>= g✝ = x✝ >>= fun x => f✝ x >>= g✝
                             -- ⊢ out (x✝ >>= f✝ >>= g✝) = out (x✝ >>= fun x => f✝ x >>= g✝)
                                  -- 🎉 no goals
    bind_pure_comp := by intros; ext; simp
    bind_map := by intros; ext; simp [Seq.seq]
    seqLeft_eq := by intros; ext; simp [Seq.seq, Functor.mapConst, SeqLeft.seqLeft]
    seqRight_eq := by intros; ext; simp [Seq.seq, Functor.mapConst, SeqRight.seqRight]
    pure_seq := by intros; ext; simp [Seq.seq, Functor.mapConst, SeqRight.seqRight] }

end Erased
