/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Logic.Equiv.Basic

/-!
# Extra lemmas about `ULift` and `PLift`

In this file we provide `Subsingleton`, `Unique`, `DecidableEq`, and `IsEmpty` instances for
`ULift α` and `PLift α`. We also prove `ULift.forall`, `ULift.exists`, `PLift.Forall`, and
`PLift.Exists`.
-/


universe u v

open Function

namespace PLift

variable {α : Sort u} {β : Sort v}

instance [Subsingleton α] : Subsingleton (PLift α) :=
  Equiv.plift.subsingleton

instance [Nonempty α] : Nonempty (PLift α) :=
  Equiv.plift.nonempty

instance [Unique α] : Unique (PLift α) :=
  Equiv.plift.unique

instance [DecidableEq α] : DecidableEq (PLift α) :=
  Equiv.plift.decidableEq

instance [IsEmpty α] : IsEmpty (PLift α) :=
  Equiv.plift.isEmpty

theorem upInjective : Injective (@up α) :=
  Equiv.plift.symm.injective
#align plift.up_injective PLift.upInjective

theorem upSurjective : Surjective (@up α) :=
  Equiv.plift.symm.surjective
#align plift.up_surjective PLift.upSurjective

theorem upBijective : Bijective (@up α) :=
  Equiv.plift.symm.bijective
#align plift.up_bijective PLift.upBijective

@[simp]
theorem up_inj {x y : α} : up x = up y ↔ x = y :=
  upInjective.eq_iff
#align plift.up_inj PLift.up_inj

theorem downSurjective : Surjective (@down α) :=
  Equiv.plift.surjective
#align plift.down_surjective PLift.downSurjective

theorem downBijective : Bijective (@down α) :=
  Equiv.plift.bijective
#align plift.down_bijective PLift.downBijective

@[simp]
theorem forall₃ {p : PLift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (PLift.up x) :=
  upSurjective.forall
#align plift.forall PLift.forall₃

@[simp]
theorem exists₃ {p : PLift α → Prop} : (∃ x, p x) ↔ ∃ x : α, p (PLift.up x) :=
  upSurjective.exists
#align plift.exists PLift.exists₃

end PLift

namespace ULift

variable {α : Type u} {β : Type v}

instance [Subsingleton α] : Subsingleton (ULift α) :=
  Equiv.ulift.subsingleton

instance [Nonempty α] : Nonempty (ULift α) :=
  Equiv.ulift.nonempty

instance [Unique α] : Unique (ULift α) :=
  Equiv.ulift.unique

instance [DecidableEq α] : DecidableEq (ULift α) :=
  Equiv.ulift.decidableEq

instance [IsEmpty α] : IsEmpty (ULift α) :=
  Equiv.ulift.isEmpty

theorem upInjective : Injective (@up α) :=
  Equiv.ulift.symm.injective
#align ulift.up_injective ULift.upInjective

theorem upSurjective : Surjective (@up α) :=
  Equiv.ulift.symm.surjective
#align ulift.up_surjective ULift.upSurjective

theorem upBijective : Bijective (@up α) :=
  Equiv.ulift.symm.bijective
#align ulift.up_bijective ULift.upBijective

@[simp]
theorem up_inj {x y : α} : up x = up y ↔ x = y :=
  upInjective.eq_iff
#align ulift.up_inj ULift.up_inj

theorem downSurjective : Surjective (@down α) :=
  Equiv.ulift.surjective
#align ulift.down_surjective ULift.downSurjective

theorem downBijective : Bijective (@down α) :=
  Equiv.ulift.bijective
#align ulift.down_bijective ULift.downBijective

@[simp]
theorem forall₃ {p : ULift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (ULift.up x) :=
  upSurjective.forall
#align ulift.forall ULift.forall₃

@[simp]
theorem exists₃ {p : ULift α → Prop} : (∃ x, p x) ↔ ∃ x : α, p (ULift.up x) :=
  upSurjective.exists
#align ulift.exists ULift.exists₃

end ULift
