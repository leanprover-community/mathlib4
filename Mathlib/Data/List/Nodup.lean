/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
import Mathlib.Data.List.Pairwise

/-!
# Lists with no duplicates

`List.Nodup` is defined in `Std.Data.List.Basic`. In this file we prove various properties of this
predicate.
-/

open Function

namespace List

theorem Nodup.map_on {f : α → β} (H : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (d : Nodup l) :
    (map f l).Nodup :=
  Pairwise.map _ (fun a b ⟨ma, mb, n⟩ e => n (H a ma b mb e)) (Pairwise.and_mem.1 d)

protected theorem Nodup.map {f : α → β} (hf : Function.Injective f) : Nodup l → Nodup (map f l) :=
  Nodup.map_on fun _ _ _ _ h => hf h

theorem Nodup.of_map (f : α → β) {l : List α} : Nodup (map f l) → Nodup l :=
  (Pairwise.of_map f) fun _ _ => mt <| congr_arg f

@[simp]
theorem nodup_attach {l : List α} : Nodup (attach l) ↔ Nodup l :=
  ⟨fun h => attach_map_val l ▸ h.map fun _ _ => Subtype.eq,
   fun h => Nodup.of_map Subtype.val ((attach_map_val l).symm ▸ h)⟩

alias nodup_attach ↔ Nodup.of_attach Nodup.attach

-- TODO in mathlib3 we had:
-- attribute [protected] nodup.attach

theorem Nodup.pmap {p : α → Prop} {f : ∀ a, p a → β} {l : List α} {H}
    (hf : ∀ a ha b hb, f a ha = f b hb → a = b) (h : Nodup l) : Nodup (pmap f l H) := by
  rw [pmap_eq_map_attach]
  exact h.attach.map fun ⟨a, ha⟩ ⟨b, hb⟩ h => by
    congr
    exact hf a (H _ ha) b (H _ hb) h
