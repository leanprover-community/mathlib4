import Mathlib.Data.List.Pairwise

open Function

namespace List

theorem Nodup.map_on {f : α → β} (H : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (d : Nodup l) : (map f l).Nodup :=
  Pairwise.map _ (fun a b ⟨ma, mb, n⟩ e => n (H a ma b mb e)) (Pairwise.and_mem.1 d)

protected theorem Nodup.map {f : α → β} (hf : Function.injective f) : Nodup l → Nodup (map f l) :=
  Nodup.map_on fun _ _ _ _ h => hf h

theorem Nodup.of_map (f : α → β) {l : List α} : Nodup (map f l) → Nodup l :=
  (Pairwise.of_map f) fun a b => mt <| congr_arg f

@[simp]
theorem nodup_attach {l : List α} : Nodup (attach l) ↔ Nodup l :=
  ⟨fun h => attach_map_val l ▸ h.map fun a b => Subtype.eq, fun h =>
    Nodup.of_map Subtype.val ((attach_map_val l).symm ▸ h)⟩

alias nodup_attach ↔ nodup.of_attach nodup.attach

attribute [protected] nodup.attach

theorem Nodupₓ.pmap {p : α → Prop} {f : ∀ a, p a → β} {l : List α} {H} (hf : ∀ a ha b hb, f a ha = f b hb → a = b)
    (h : Nodupₓ l) : Nodupₓ (pmap f l H) := by
  rw [pmap_eq_map_attach] <;>
    exact
      h.attach.map fun ⟨a, ha⟩ ⟨b, hb⟩ h => by
        congr <;> exact hf a (H _ ha) b (H _ hb) h
