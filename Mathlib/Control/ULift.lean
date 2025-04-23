/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Jannis Limperg
-/

import Mathlib.Init
/-!
# Monadic instances for `ULift` and `PLift`

In this file we define `Monad` and `IsLawfulMonad` instances on `PLift` and `ULift`. -/

universe u v u' v'

namespace PLift

variable {α : Sort u} {β : Sort v}

/-- Functorial action. -/
protected def map (f : α → β) (a : PLift α) : PLift β :=
  PLift.up (f a.down)

@[simp]
theorem map_up (f : α → β) (a : α) : (PLift.up a).map f = PLift.up (f a) :=
  rfl

/-- Embedding of pure values. -/
@[simp]
protected def pure : α → PLift α :=
  up

/-- Applicative sequencing. -/
protected def seq (f : PLift (α → β)) (x : Unit → PLift α) : PLift β :=
  PLift.up (f.down (x ()).down)

@[simp]
theorem seq_up (f : α → β) (x : α) : (PLift.up f).seq (fun _ => PLift.up x) = PLift.up (f x) :=
  rfl

/-- Monadic bind. -/
protected def bind (a : PLift α) (f : α → PLift β) : PLift β :=
  f a.down

@[simp]
theorem bind_up (a : α) (f : α → PLift β) : (PLift.up a).bind f = f a :=
  rfl

instance : Monad PLift where
  map := @PLift.map
  pure := @PLift.pure
  seq := @PLift.seq
  bind := @PLift.bind

instance : LawfulFunctor PLift where
  id_map := @fun _ ⟨_⟩ => rfl
  comp_map := @fun _ _ _ _ _ ⟨_⟩ => rfl
  map_const := @fun _ _ => rfl

instance : LawfulApplicative PLift where
  seqLeft_eq := @fun _ _ _ _ => rfl
  seqRight_eq := @fun _ _ _ _ => rfl
  pure_seq := @fun _ _ _ ⟨_⟩ => rfl
  map_pure := @fun _ _ _ _ => rfl
  seq_pure := @fun _ _ ⟨_⟩ _ => rfl
  seq_assoc := @fun _ _ _ ⟨_⟩ ⟨_⟩ ⟨_⟩ => rfl

instance : LawfulMonad PLift where
  bind_pure_comp := @fun _ _ _ ⟨_⟩ => rfl
  bind_map := @fun _ _ ⟨_⟩ ⟨_⟩ => rfl
  pure_bind := @fun _ _ _ _ => rfl
  bind_assoc := @fun _ _ _ ⟨_⟩ _ _ => rfl

@[simp]
theorem rec.constant {α : Sort u} {β : Type v} (b : β) :
    (@PLift.rec α (fun _ => β) fun _ => b) = fun _ => b := rfl

end PLift

namespace ULift

variable {α : Type u} {β : Type v}

/-- Functorial action. -/
protected def map (f : α → β) (a : ULift.{u'} α) : ULift.{v'} β := ULift.up.{v'} (f a.down)

@[simp]
theorem map_up (f : α → β) (a : α) : (ULift.up.{u'} a).map f = ULift.up.{v'} (f a) := rfl

/-- Embedding of pure values. -/
@[simp]
protected def pure : α → ULift α :=
  up

/-- Applicative sequencing. -/
protected def seq {α β} (f : ULift (α → β)) (x : Unit → ULift α) : ULift β :=
  ULift.up.{u} (f.down (x ()).down)

@[simp]
theorem seq_up (f : α → β) (x : α) : (ULift.up f).seq (fun _ => ULift.up x) = ULift.up (f x) :=
  rfl

/-- Monadic bind. -/
protected def bind (a : ULift α) (f : α → ULift β) : ULift β :=
  f a.down

@[simp]
theorem bind_up (a : α) (f : α → ULift β) : (ULift.up a).bind f = f a :=
  rfl

instance : Monad ULift where
  map := @ULift.map
  pure := @ULift.pure
  seq := @ULift.seq
  bind := @ULift.bind

instance : LawfulFunctor ULift where
  id_map := @fun _ ⟨_⟩ => rfl
  comp_map := @fun _ _ _ _ _ ⟨_⟩ => rfl
  map_const := @fun _ _ => rfl

instance : LawfulApplicative ULift where
  seqLeft_eq := @fun _ _ _ _ => rfl
  seqRight_eq := @fun _ _ _ _ => rfl
  pure_seq := @fun _ _ _ ⟨_⟩ => rfl
  map_pure := @fun _ _ _ _ => rfl
  seq_pure := @fun _ _ ⟨_⟩ _ => rfl
  seq_assoc := @fun _ _ _ ⟨_⟩ ⟨_⟩ ⟨_⟩ => rfl

instance : LawfulMonad ULift where
  bind_pure_comp := @fun _ _ _ ⟨_⟩ => rfl
  bind_map := @fun _ _ ⟨_⟩ ⟨_⟩ => rfl
  pure_bind := @fun _ _ _ _ => rfl
  bind_assoc := @fun _ _ _ ⟨_⟩ _ _ => rfl

@[simp]
theorem rec.constant {α : Type u} {β : Sort v} (b : β) :
    (@ULift.rec α (fun _ => β) fun _ => b) = fun _ => b := rfl

end ULift
