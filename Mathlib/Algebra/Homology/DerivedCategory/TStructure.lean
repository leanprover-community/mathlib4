import Mathlib.Algebra.Homology.DerivedCategory.TruncLE
import Mathlib.CategoryTheory.Triangulated.TStructure

open CategoryTheory Category Pretriangulated Triangulated Limits Preadditive

namespace DerivedCategory

variable {C : Type _} [Category C] [Abelian C]

namespace TStructure

def t : TStructure (DerivedCategory C) where
  setLE n := fun K => K.IsLE n
  setGE n := fun K => K.IsGE n
  setLE_respectsIso n := ⟨fun K L e (hK : K.IsLE n) => isLE_of_iso e n⟩
  setGE_respectsIso n := ⟨fun K L e (hK : K.IsGE n) => isGE_of_iso e n⟩
  shift_mem_setLE n a n' h K (hK : K.IsLE n) := K.isLE_shift n a n' h
  shift_mem_setGE n a n' h K (hK : K.IsGE n) := K.isGE_shift n a n' h
  zero' K L f (hK : K.IsLE 0) (hY : L.IsGE 1):= by
    have hL' : L.truncLEι 0 = 0 := by
      apply IsZero.eq_of_src
      rw [L.isZero_truncLE_iff 0 1 (by simp)]
      infer_instance
    rw [← cancel_epi (K.truncLEι 0), comp_zero, ← truncLEι_naturality, hL', comp_zero]
  setLE_zero_subset {K} (hK : K.IsLE 0) := K.isLE_of_LE 0 1 (by linarith)
  setGE_one_subset {K} (hK : K.IsGE 1) := K.isGE_of_GE 0 1 (by linarith)
  exists_triangle_zero_one X := by
    obtain ⟨Z, g, h, mem⟩ := distinguished_cocone_triangle (X.truncLEι 0)
    refine' ⟨_, _, _, _, _, _, _, mem⟩
    . change (X.truncLE 0).IsLE 0
      infer_instance
    . apply (distTriang₃_isGE_iff _ mem 0 1 (by simp)).2
      dsimp
      constructor
      . exact X.isIso_homologyMap_truncLEι 0
      . rw [mono_iff_cancel_zero]
        intros
        apply IsZero.eq_of_tgt
        exact X.isZero_homology_truncLE 0 1 (by linarith)


end TStructure

end DerivedCategory
