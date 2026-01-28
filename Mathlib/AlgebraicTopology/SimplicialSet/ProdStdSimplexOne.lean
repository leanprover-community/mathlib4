/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne

/-!
# Binary products `Δ[n] ⊗ Δ[1]`

-/

@[expose] public section

universe u

open CategoryTheory Simplicial MonoidalCategory Opposite

namespace SSet

namespace prodStdSimplex

variable {p : ℕ}

namespace nonDegenerateEquiv₁

open stdSimplex in
def toFun (i : Fin (p + 1)) : (Δ[p] ⊗ Δ[1]).nonDegenerate (p + 1) :=
    ⟨⟨stdSimplex.objEquiv.{u}.symm (SimplexCategory.σ i),
      objMk₁ i.succ.castSucc⟩, by
  rw [nonDegenerate_max_dim_iff _ rfl]
  ext j
  dsimp
  by_cases hj : j ≤ i.castSucc
  · rw [objMk₁_of_castSucc_lt _ _ (by simpa),
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero]
    change (i.predAbove j : ℕ) = _
    simp [Fin.predAbove_of_le_castSucc _ _ hj]
  · simp only [not_le] at hj
    rw [objMk₁_of_le_castSucc _ _ (by simpa), objEquiv_symm_apply]
    change (i.predAbove j : ℕ) + 1 = _
    rw [Fin.predAbove_of_castSucc_lt _ _ hj, Fin.val_pred]
    lia⟩

end nonDegenerateEquiv₁

noncomputable def nonDegenerateEquiv₁ :
    Fin (p + 1) ≃ (Δ[p] ⊗ Δ[1] : SSet.{u}).nonDegenerate (p + 1) :=
  Equiv.ofBijective nonDegenerateEquiv₁.toFun (by
    refine ⟨fun _ _ h ↦ ?_, fun ⟨⟨s₁, s₂⟩, hs⟩ ↦ ?_⟩
    · simpa using stdSimplex.objMk₁_injective (congr_arg (Prod.snd ∘ Subtype.val) h)
    · rw [nonDegenerate_max_dim_iff _ rfl] at hs
      obtain ⟨i, rfl⟩ := stdSimplex.objMk₁_surjective s₂
      obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (i := i) (by
        rintro rfl
        have := DFunLike.congr_fun hs 0
        dsimp at this
        simp only [Fin.ext_iff,
          stdSimplex.objMk₁_of_le_castSucc (0 : Fin (p + 3)) 0 (by simp)] at this
        lia)
      obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
      · exact ⟨i, nonDegenerate_ext₂ rfl rfl⟩
      · have := DFunLike.congr_fun hs (Fin.last _)
        dsimp at this
        simp only [Fin.ext_iff, Fin.val_last,
          stdSimplex.objMk₁_of_castSucc_lt (Fin.last (p + 2))
            (Fin.last (p + 1)) (by simp)] at this
        lia)

@[simp]
lemma nonDegenerateEquiv₁_fst (i : Fin (p + 1)) :
    (nonDegenerateEquiv₁ i).1.1 =
      (stdSimplex.objEquiv (m := (op ⦋p + 1⦌))).symm (SimplexCategory.σ i) := rfl

@[simp]
lemma nonDegenerateEquiv₁_snd (i : Fin (p + 1)) :
    (nonDegenerateEquiv₁ i).1.2 =
      stdSimplex.objMk₁ i.succ.castSucc := rfl

end prodStdSimplex

end SSet
