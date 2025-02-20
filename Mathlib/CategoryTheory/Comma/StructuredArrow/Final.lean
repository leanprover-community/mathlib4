/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Comma.Final
import Mathlib.CategoryTheory.Filtered.OfColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Preserves.Grothendieck
import Mathlib.CategoryTheory.Limits.Final

/-!
# Finality on Costructured Arrow categories

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Proposition 3.1.8
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Functor

section Small

variable {A : Type u₁} [SmallCategory A] {B : Type u₁} [SmallCategory B]
variable {T : Type u₁} [SmallCategory T]

attribute [local instance] Grothendieck.final_map

open CostructuredArrow in
private lemma final_of_final_toOver (L : A ⥤ T) (R : B ⥤ T) [Final R]
    [∀ b : B, Final (toOver L (R.obj b))] : Final L := by
  rw [final_iff_isIso_colimit_pre]
  intro G
  have : ∀ (b : B), Final ((whiskerLeft R (functorPre L (𝟭 T))).app b) := fun b =>
    inferInstanceAs (Final (toOver L (R.obj b)))
  let i : colimit (L ⋙ G) ≅ colimit G :=
  calc colimit (L ⋙ G) ≅ colimit <| grothendieckProj L ⋙ L ⋙ G :=
          colimitIsoColimitGrothendieck L (L ⋙ G)
    _ ≅ colimit <| Grothendieck.pre (functor L) R ⋙ grothendieckProj L ⋙ L ⋙ G :=
          (Final.colimitIso (Grothendieck.pre (functor L) R) (grothendieckProj L ⋙ L ⋙ G)).symm
    _ ≅ colimit <| Grothendieck.map (whiskerLeft _ (functorPre L (𝟭 T))) ⋙
          grothendieckPrecompFunctorToComma (𝟭 T) R ⋙ Comma.fst (𝟭 T) R ⋙ G :=
            HasColimit.isoOfNatIso (NatIso.ofComponents (fun _ => Iso.refl _))
    _ ≅ colimit <| grothendieckPrecompFunctorToComma (𝟭 T) R ⋙ Comma.fst (𝟭 T) R ⋙ G :=
          Final.colimitIso _ _  -- hyp used here
    _ ≅ colimit <| Grothendieck.pre (functor (𝟭 T)) R ⋙ grothendieckProj (𝟭 T) ⋙ G :=
          HasColimit.isoOfNatIso (Iso.refl _)
    _ ≅ colimit <| grothendieckProj (𝟭 T) ⋙ G :=
          Final.colimitIso _ _
    _ ≅ colimit G := (colimitIsoColimitGrothendieck (𝟭 T) G).symm
  convert (Iso.isIso_hom i)
  apply colimit.hom_ext
  intro a
  simp [i]
  simp only [← Category.assoc]
  rw [Iso.eq_comp_inv]
  simp
  sorry

end Small

end CategoryTheory
