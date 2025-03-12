/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Data.Set.Basic

/-!
# Order structures and monotonicity lemmas for `Set`
-/

open Function

universe u v

namespace Set

variable {α : Type u} {β : Type v} {a b : α} {s s₁ s₂ t t₁ t₂ u : Set α}

section Preorder

variable [Preorder α] [Preorder β] {f : α → β}

theorem monotoneOn_iff_monotone : MonotoneOn f s ↔
    Monotone fun a : s => f a := by
  simp [Monotone, MonotoneOn]

theorem antitoneOn_iff_antitone : AntitoneOn f s ↔
    Antitone fun a : s => f a := by
  simp [Antitone, AntitoneOn]

theorem strictMonoOn_iff_strictMono : StrictMonoOn f s ↔
    StrictMono fun a : s => f a := by
  simp [StrictMono, StrictMonoOn]

theorem strictAntiOn_iff_strictAnti : StrictAntiOn f s ↔
    StrictAnti fun a : s => f a := by
  simp [StrictAnti, StrictAntiOn]

end Preorder

section LinearOrder

variable [LinearOrder α] [LinearOrder β] {f : α → β}

/-- A function between linear orders which is neither monotone nor antitone makes a dent upright or
downright. -/
theorem not_monotoneOn_not_antitoneOn_iff_exists_le_le :
    ¬MonotoneOn f s ∧ ¬AntitoneOn f s ↔
      ∃ᵉ (a ∈ s) (b ∈ s) (c ∈ s), a ≤ b ∧ b ≤ c ∧
        (f a < f b ∧ f c < f b ∨ f b < f a ∧ f b < f c) := by
  simp [monotoneOn_iff_monotone, antitoneOn_iff_antitone, and_assoc, exists_and_left,
    not_monotone_not_antitone_iff_exists_le_le, @and_left_comm (_ ∈ s)]

/-- A function between linear orders which is neither monotone nor antitone makes a dent upright or
downright. -/
theorem not_monotoneOn_not_antitoneOn_iff_exists_lt_lt :
    ¬MonotoneOn f s ∧ ¬AntitoneOn f s ↔
      ∃ᵉ (a ∈ s) (b ∈ s) (c ∈ s), a < b ∧ b < c ∧
        (f a < f b ∧ f c < f b ∨ f b < f a ∧ f b < f c) := by
  simp [monotoneOn_iff_monotone, antitoneOn_iff_antitone, and_assoc, exists_and_left,
    not_monotone_not_antitone_iff_exists_lt_lt, @and_left_comm (_ ∈ s)]

end LinearOrder

end Set

/-! ### Monotone lemmas for sets -/

section Monotone
variable {α β : Type*}

theorem Monotone.inter [Preorder β] {f g : β → Set α} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ∩ g x :=
  hf.inf hg

theorem MonotoneOn.inter [Preorder β] {f g : β → Set α} {s : Set β} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (fun x => f x ∩ g x) s :=
  hf.inf hg

theorem Antitone.inter [Preorder β] {f g : β → Set α} (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x ∩ g x :=
  hf.inf hg

theorem AntitoneOn.inter [Preorder β] {f g : β → Set α} {s : Set β} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => f x ∩ g x) s :=
  hf.inf hg

theorem Monotone.union [Preorder β] {f g : β → Set α} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ∪ g x :=
  hf.sup hg

theorem MonotoneOn.union [Preorder β] {f g : β → Set α} {s : Set β} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (fun x => f x ∪ g x) s :=
  hf.sup hg

theorem Antitone.union [Preorder β] {f g : β → Set α} (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x ∪ g x :=
  hf.sup hg

theorem AntitoneOn.union [Preorder β] {f g : β → Set α} {s : Set β} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => f x ∪ g x) s :=
  hf.sup hg

namespace Set

theorem monotone_setOf [Preorder α] {p : α → β → Prop} (hp : ∀ b, Monotone fun a => p a b) :
    Monotone fun a => { b | p a b } := fun _ _ h b => hp b h

theorem antitone_setOf [Preorder α] {p : α → β → Prop} (hp : ∀ b, Antitone fun a => p a b) :
    Antitone fun a => { b | p a b } := fun _ _ h b => hp b h

/-- Quantifying over a set is antitone in the set -/
theorem antitone_bforall {P : α → Prop} : Antitone fun s : Set α => ∀ x ∈ s, P x :=
  fun _ _ hst h x hx => h x <| hst hx

end Set

end Monotone
