/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Logic.Equiv.Defs

/-!
# Extra lemmas about `Ulift` and `Plift`

In this file we provide `Subsingleton`, `Unique`, `DecidableEq`, and `isEmpty` instances for
`Ulift α` and `Plift α`. We also prove `Ulift.forall`, `Ulift.exists`, `Plift.forall`, and
`Plift.exists`.
-/


universe u v

open Function

namespace PLift

variable {α : Sort u} {β : Sort v}

instance [Subsingleton α] : Subsingleton (PLift α) :=
  Equiv.plift.Subsingleton

instance [Nonempty α] : Nonempty (PLift α) :=
  Equiv.plift.Nonempty

instance [Unique α] : Unique (PLift α) :=
  Equiv.plift.unique

instance [DecidableEq α] : DecidableEq (PLift α) :=
  Equiv.plift.DecidableEq

instance [IsEmpty α] : IsEmpty (PLift α) :=
  Equiv.plift.isEmpty

theorem up_injective : Injective (@up α) :=
  Equiv.plift.symm.Injective
#align plift.up_injective PLift.up_injective

theorem up_surjective : Surjective (@up α) :=
  Equiv.plift.symm.Surjective
#align plift.up_surjective PLift.up_surjective

theorem up_bijective : Bijective (@up α) :=
  Equiv.plift.symm.Bijective
#align plift.up_bijective PLift.up_bijective

@[simp]
theorem up_inj {x y : α} : up x = up y ↔ x = y :=
  up_injective.eq_iff
#align plift.up_inj PLift.up_inj

theorem down_surjective : Surjective (@down α) :=
  Equiv.plift.Surjective
#align plift.down_surjective PLift.down_surjective

theorem down_bijective : Bijective (@down α) :=
  Equiv.plift.Bijective
#align plift.down_bijective PLift.down_bijective

@[simp]
theorem forall {p : PLift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (PLift.up x) :=
  up_surjective.forall
#align plift.forall PLift.forall

@[simp]
theorem exists {p : PLift α → Prop} : (∃ x, p x) ↔ ∃ x : α, p (PLift.up x) :=
  up_surjective.exists
#align plift.exists PLift.exists

end PLift

namespace ULift

variable {α : Type u} {β : Type v}

instance [Subsingleton α] : Subsingleton (ULift α) :=
  Equiv.ulift.Subsingleton

instance [Nonempty α] : Nonempty (ULift α) :=
  Equiv.ulift.Nonempty

instance [Unique α] : Unique (ULift α) :=
  Equiv.ulift.unique

instance [DecidableEq α] : DecidableEq (ULift α) :=
  Equiv.ulift.DecidableEq

instance [IsEmpty α] : IsEmpty (ULift α) :=
  Equiv.ulift.isEmpty

theorem up_injective : Injective (@up α) :=
  Equiv.ulift.symm.Injective
#align ulift.up_injective ULift.up_injective

theorem up_surjective : Surjective (@up α) :=
  Equiv.ulift.symm.Surjective
#align ulift.up_surjective ULift.up_surjective

theorem up_bijective : Bijective (@up α) :=
  Equiv.ulift.symm.Bijective
#align ulift.up_bijective ULift.up_bijective

@[simp]
theorem up_inj {x y : α} : up x = up y ↔ x = y :=
  up_injective.eq_iff
#align ulift.up_inj ULift.up_inj

theorem down_surjective : Surjective (@down α) :=
  Equiv.ulift.Surjective
#align ulift.down_surjective ULift.down_surjective

theorem down_bijective : Bijective (@down α) :=
  Equiv.ulift.Bijective
#align ulift.down_bijective ULift.down_bijective

@[simp]
theorem forall {p : ULift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (ULift.up x) :=
  up_surjective.forall
#align ulift.forall ULift.forall

@[simp]
theorem exists {p : ULift α → Prop} : (∃ x, p x) ↔ ∃ x : α, p (ULift.up x) :=
  up_surjective.exists
#align ulift.exists ULift.exists

end ULift

