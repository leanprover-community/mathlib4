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
    obtain (_|_|_) := a <;> obtain (_|_|_) := b <;> obtain (_|_|_) := c
    all_goals simp at hbc hab <;> dsimp [TruncLTt.map] <;> simp

namespace TruncGEt

noncomputable def obj : ℤt → C ⥤ C
  | some none => 𝟭 C
  | some (some a) => t.truncGE a
  | none => 0

noncomputable def map : ∀ {x y : ℤt}, (x ⟶ y) → (obj t x ⟶ obj t y)
  | some none, some none => fun _ => 𝟙 _
  | some none, some (some b) => fun _ => t.truncGEπ b
  | some none, none => fun _ => 0
  | some (some a), some none  => fun _ => 0
  | some (some a), some (some b) =>
      fun hab => t.natTransTruncGEOfGE a b (by simpa using (leOfHom hab))
  | some (some a), none => fun _ => 0
  | none, some none  => fun _ => 0
  | none, some (some b) => fun _ => 0
  | none, none => fun _ => 𝟙 _

end TruncGEt

noncomputable def truncGEt : ℤt ⥤ C ⥤ C where
  obj := TruncGEt.obj t
  map φ := TruncGEt.map t φ
  map_id := by
    rintro (_|a|_)
    . rfl
    . rfl
    . dsimp [TruncGEt.map]
      rw [natTransTruncGEOfGE_eq_id]
      rfl
  map_comp {a b c} hab hbc := by
    replace hab := leOfHom hab
    replace hbc := leOfHom hbc
    obtain (_|_|_) := a <;> obtain (_|_|_) := b <;> obtain (_|_|_) := c
    all_goals simp at hbc hab <;> dsimp [TruncGEt.map] <;> simp

namespace TruncGEtδLTt

noncomputable def app : ∀ (a : ℤt), t.truncGEt.obj a ⟶ t.truncLTt.obj a ⋙ shiftFunctor C (1 : ℤ)
  | some none => 0
  | some (some a) => t.truncGEδLT a
  | none => 0

end TruncGEtδLTt

/-@[simp]
lemma natTransTruncGEOfGE_comp_truncGEδLT (a b : ℤ) (h : a ≤ b) :
    t.natTransTruncGEOfGE a b h ≫ t.truncGEδLT b =
      t.truncGEδLT a ≫ whiskerRight (t.natTransTruncLTOfLE a b h) (shiftFunctor C (1 : ℤ)) := by
  ext X
  dsimp
  simp
  sorry

noncomputable def truncGEtδLTt :
    t.truncGEt ⟶ t.truncLTt ⋙ ((whiskeringRight C C C).obj (shiftFunctor C (1 : ℤ))) where
  app a := TruncGEtδLTt.app t a
  naturality {a b} hab := by
    have hab' := leOfHom hab
    obtain (_|_|a) := a
    . apply IsZero.eq_of_src
      exact isZero_zero _
    . obtain (_|_|_) := b
      . dsimp [truncGEt, TruncGEt.map, TruncGEtδLTt.app]
        simp
      . obtain rfl : hab = 𝟙 _ := Subsingleton.elim _ _
        simp
      . dsimp [truncGEt, TruncGEt.map, TruncGEtδLTt.app]
        simp
    . obtain (_|_|b) := b
      . dsimp [truncGEt, TruncGEt.map, TruncGEtδLTt.app, truncLTt, TruncLTt.map]
        simp
      . dsimp [truncGEt, TruncGEt.map, TruncGEtδLTt.app, truncLTt, TruncLTt.map]
        ext
        simp
      . dsimp [truncGEt, TruncGEt.map, TruncGEtδLTt.app]
        simp at hab'
        exact t.natTransTruncGEOfGE_comp_truncGEδLT _ _ hab'-/

end TStructure

end Triangulated

end CategoryTheory
