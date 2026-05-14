/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Justus Springer
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.SetLike

/-!
# The opposite of a triangulated category is triangulated

The pretriangulated structure on `Cᵒᵖ` was constructed in the file
`CategoryTheory.Triangulated.Opposite.Pretriangulated`. Here, we show
that `Cᵒᵖ` is triangulated if `C` is triangulated.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

public section

namespace CategoryTheory

open Preadditive Limits

namespace Pretriangulated

variable (C : Type*) [Category* C] [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Opposite

set_option backward.isDefEq.respectTransparency false in
scoped instance [IsTriangulated C] : IsTriangulated Cᵒᵖ where
  octahedron_axiom := by
    intro X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ u₁₃ comm v₁₂ w₁₂ h₁₂ v₂₃ w₂₃ h₂₃ v₁₃ w₁₃ h₁₃
    let o := Triangulated.someOctahedron' (by aesop) ((mem_distTriang_op_iff _).mp h₂₃)
      ((mem_distTriang_op_iff _).mp h₁₂) ((mem_distTriang_op_iff _).mp h₁₃)
    refine ⟨o.m₃.op, o.m₁.op, congr($(o.comm₄).op), ?_, congr($(o.comm₁).op), ?_, ?_⟩
    · have eq₃ := congr($(o.comm₃).op)
      dsimp at eq₃
      rw [← Category.assoc, ← op_comp, ← Functor.map_comp,
        NatIso.cancel_natIso_inv_right (opShiftFunctorEquivalence C _).unitIso] at eq₃
      exact congr($(Functor.map_injective _ congr($(eq₃).unop)).op)
    · have eq₂ := congr($(o.comm₂).op)
      dsimp at eq₂
      rw [← Category.assoc, ← op_comp, ← Functor.map_comp, Category.assoc,
        ← opShiftFunctorEquivalence_unitIso_inv_naturality, ← Category.assoc,
        NatIso.cancel_natIso_inv_right (opShiftFunctorEquivalence C _).unitIso, ← op_comp,
        ← Functor.map_comp] at eq₂
      exact congr($(Functor.map_injective _ congr($(eq₂).unop)).op).symm
    · have := op_distinguished _ o.mem
      dsimp at this
      convert this using 2
      rw [Category.assoc, Functor.map_comp, Functor.map_comp,
        ← opShiftFunctorEquivalence_counitIso_hom_app_shift,
        ← opShiftFunctorEquivalence_counitIso_inv_naturality_assoc, Iso.inv_hom_id_app_assoc]

end Opposite

end Pretriangulated

end CategoryTheory
