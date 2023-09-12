import Mathlib.CategoryTheory.Iso
import Mathlib.Data.Set.Basic

namespace Set

open CategoryTheory

variable {C : Type _} [Category C]

class RespectsIso (S : Set C) : Prop where
  condition : ∀ ⦃X Y : C⦄ (_ : X ≅ Y), X ∈ S → Y ∈ S

lemma mem_of_iso (S : Set C) [S.RespectsIso] {X Y : C} (e : X ≅ Y) (hX : X ∈ S) : Y ∈ S :=
  RespectsIso.condition e hX

lemma mem_iff_of_iso (S : Set C) [S.RespectsIso] {X Y : C} (e : X ≅ Y) : X ∈ S ↔ Y ∈ S :=
  ⟨S.mem_of_iso e, S.mem_of_iso e.symm⟩

def isoClosure (S : Set C) : Set C := fun X => ∃ (Y : C) (_ : Y ∈ S), Nonempty (X ≅ Y)

lemma subset_isoClosure (S : Set C) : S ⊆ S.isoClosure := fun X hX => ⟨X, hX, ⟨Iso.refl X⟩⟩

lemma isoClosure_eq_self (S : Set C) [S.RespectsIso] : S.isoClosure = S := by
  apply subset_antisymm
  · intro X ⟨Y, hY, ⟨e⟩⟩
    exact S.mem_of_iso e.symm hY
  · exact S.subset_isoClosure

instance (S : Set C) : S.isoClosure.RespectsIso where
  condition := by
    rintro X Y e ⟨Z, hZ, ⟨f⟩⟩
    exact ⟨Z, hZ, ⟨e.symm.trans f⟩⟩

end Set
