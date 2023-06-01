import Mathlib.CategoryTheory.Triangulated.TStructure.Trunc
import Mathlib.Algebra.Homology.SpectralSequence.Construction

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

namespace Triangulated

variable {C : Type _} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)

namespace TStructure

namespace TruncLTt

noncomputable def obj : ℤt → C ⥤ C
  | some none => 0
  | some (some a) => t.truncLT a
  | none => 𝟭 C

noncomputable def map : ∀ {x y : ℤt}, (x ⟶ y) → (obj t x ⟶ obj t y)
  | some none, some none => fun _ => 𝟙 _
  | some none, some (some b) => fun _ => 0
  | some none, none => fun _ => 0
  | some (some a), some none  => fun _ => 0
  | some (some a), some (some b) =>
      fun hab => t.natTransTruncLTOfLE a b (by simpa using (leOfHom hab))
  | some (some a), none => fun _ => t.truncLTι  a
  | none, some none  => fun _ => 0
  | none, some (some b) => fun _ => 0
  | none, none => fun _ => 𝟙 _

end TruncLTt

noncomputable def truncLTt : ℤt ⥤ C ⥤ C where
  obj := TruncLTt.obj t
  map φ := TruncLTt.map t φ
  map_id := by
    rintro (_|a|_)
    . rfl
    . rfl
    . dsimp [TruncLTt.map]
      rw [natTransTruncLTOfLE_eq_id]
      rfl
  map_comp {a b c} hab hbc := by
    replace hab := leOfHom hab
    replace hbc := leOfHom hbc
    obtain (_|a|_) := a <;> obtain (_|b|_) := b <;> obtain (_|c|_) := c
    all_goals try dsimp [TruncLTt.map] ; simp
    . simpa using WithTop.not_top_le_coe _ hab
    . simpa using WithTop.not_top_le_coe _ hab
    . simp at hbc
    . simp at hbc
      simpa using WithBot.not_coe_le_bot _ hbc
    . simpa using WithTop.not_top_le_coe _ hbc
    . simp at hab
      simpa using WithBot.not_coe_le_bot _ hab
    . simp at hab
      simpa using WithBot.not_coe_le_bot _ hab

end TStructure

end Triangulated

end CategoryTheory
