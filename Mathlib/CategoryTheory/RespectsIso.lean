import Mathlib.CategoryTheory.Iso

namespace Set

open CategoryTheory

variable {C : Type _} [Category C]

class RespectsIso (S : Set C) : Prop where
  condition : ∀ ⦃X Y : C⦄ (_ : X ≅ Y), X ∈ S → Y ∈ S

lemma mem_of_iso (S : Set C) [S.RespectsIso] {X Y : C} (e : X ≅ Y) (hX : X ∈ S) : Y ∈ S :=
  RespectsIso.condition e hX

lemma mem_iff_of_iso (S : Set C) [S.RespectsIso] {X Y : C} (e : X ≅ Y) : X ∈ S ↔ Y ∈ S :=
  ⟨S.mem_of_iso e, S.mem_of_iso e.symm⟩

end Set
