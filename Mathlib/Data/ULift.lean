/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Control.ULift
import Mathlib.Logic.Equiv.Basic

#align_import data.ulift from "leanprover-community/mathlib"@"41cf0cc2f528dd40a8f2db167ea4fb37b8fde7f3"

/-!
# Extra lemmas about `ULift` and `PLift`

In this file we provide `Subsingleton`, `Unique`, `DecidableEq`, and `isEmpty` instances for
`ULift α` and `PLift α`. We also prove `ULift.forall`, `ULift.exists`, `PLift.forall`, and
`PLift.exists`.
-/

universe u v u' v'

open Function

namespace PLift

variable {α : Sort u} {β : Sort v} {f : α → β}

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

theorem up_injective : Injective (@up α) :=
  Equiv.plift.symm.injective
#align plift.up_injective PLift.up_injective

theorem up_surjective : Surjective (@up α) :=
  Equiv.plift.symm.surjective
#align plift.up_surjective PLift.up_surjective

theorem up_bijective : Bijective (@up α) :=
  Equiv.plift.symm.bijective
#align plift.up_bijective PLift.up_bijective

@[simp]
theorem up_inj {x y : α} : up x = up y ↔ x = y :=
  up_injective.eq_iff
#align plift.up_inj PLift.up_inj

theorem down_surjective : Surjective (@down α) :=
  Equiv.plift.surjective
#align plift.down_surjective PLift.down_surjective

theorem down_bijective : Bijective (@down α) :=
  Equiv.plift.bijective
#align plift.down_bijective PLift.down_bijective

@[simp]
theorem «forall» {p : PLift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (PLift.up x) :=
  up_surjective.forall
#align plift.forall PLift.forall

@[simp]
theorem «exists» {p : PLift α → Prop} : (∃ x, p x) ↔ ∃ x : α, p (PLift.up x) :=
  up_surjective.exists
#align plift.exists PLift.exists

@[simp] lemma map_injective : Injective (PLift.map f) ↔ Injective f :=
  (Injective.of_comp_iff' _ down_bijective).trans <| up_injective.of_comp_iff _

@[simp] lemma map_surjective : Surjective (PLift.map f) ↔ Surjective f :=
  (down_surjective.of_comp_iff _).trans <| Surjective.of_comp_iff' up_bijective _

@[simp] lemma map_bijective : Bijective (PLift.map f) ↔ Bijective f :=
  (down_bijective.of_comp_iff _).trans <| Bijective.of_comp_iff' up_bijective _

end PLift

namespace ULift

variable {α : Type u} {β : Type v} {f : α → β}

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

theorem up_injective : Injective (@up α) :=
  Equiv.ulift.symm.injective
#align ulift.up_injective ULift.up_injective

theorem up_surjective : Surjective (@up α) :=
  Equiv.ulift.symm.surjective
#align ulift.up_surjective ULift.up_surjective

theorem up_bijective : Bijective (@up α) :=
  Equiv.ulift.symm.bijective
#align ulift.up_bijective ULift.up_bijective

@[simp]
theorem up_inj {x y : α} : up x = up y ↔ x = y :=
  up_injective.eq_iff
#align ulift.up_inj ULift.up_inj

theorem down_surjective : Surjective (@down α) :=
  Equiv.ulift.surjective
#align ulift.down_surjective ULift.down_surjective

theorem down_bijective : Bijective (@down α) :=
  Equiv.ulift.bijective
#align ulift.down_bijective ULift.down_bijective

@[simp]
theorem «forall» {p : ULift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (ULift.up x) :=
  up_surjective.forall
#align ulift.forall ULift.forall

@[simp]
theorem «exists» {p : ULift α → Prop} : (∃ x, p x) ↔ ∃ x : α, p (ULift.up x) :=
  up_surjective.exists
#align ulift.exists ULift.exists

@[simp] lemma map_injective : Injective (ULift.map f : ULift.{u'} α → ULift.{v'} β) ↔ Injective f :=
  (Injective.of_comp_iff' _ down_bijective).trans <| up_injective.of_comp_iff _

@[simp] lemma map_surjective :
    Surjective (ULift.map f : ULift.{u'} α → ULift.{v'} β) ↔ Surjective f :=
  (down_surjective.of_comp_iff _).trans <| Surjective.of_comp_iff' up_bijective _

@[simp] lemma map_bijective : Bijective (ULift.map f : ULift.{u'} α → ULift.{v'} β) ↔ Bijective f :=
  (down_bijective.of_comp_iff _).trans <| Bijective.of_comp_iff' up_bijective _

@[ext]
theorem ext (x y : ULift α) (h : x.down = y.down) : x = y :=
  congrArg up h
#align ulift.ext ULift.ext

theorem ext_iff {α : Type*} (x y : ULift α) : x = y ↔ x.down = y.down :=
  ⟨congrArg _, ULift.ext _ _⟩
#align ulift.ext_iff ULift.ext_iff

end ULift
