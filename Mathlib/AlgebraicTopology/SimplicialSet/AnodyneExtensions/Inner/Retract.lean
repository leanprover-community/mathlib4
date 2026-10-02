/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct
public import Mathlib.CategoryTheory.Subfunctor.Retract

/-!
# Inner horn inclusions as retracts of pushout-products

Any inner horn inclusion `Λ[n, i].ι` is a retract of the pushout-product `Λ[2, 1].ι □ Λ[n, i].ι`.

## References

* [Charles Rezk, *Introduction to Quasicategories*, proof of Lemma 78.4][Rezk2022]

-/

@[expose] public section

universe u

namespace SSet

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory Functor

private def innerHornRetract.s₀ {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) →o Fin 3 where
  toFun j := if j < i then 0 else if j = i then 1 else 2
  monotone' _ _ _ := by grind

private def innerHornRetract.r₀ {n : ℕ} (i : Fin (n + 1)) :
    Fin 3 × Fin (n + 1) →o Fin (n + 1) where
  toFun := fun ⟨k, j⟩ ↦ if (j < i ∧ k = 0) ∨ (i < j ∧ k = 2) then j else i
  monotone' := by
    rintro ⟨k, j⟩ ⟨k', j'⟩ ⟨hk, hj⟩
    grind

open innerHornRetract in
set_option backward.isDefEq.respectTransparency false in
/-- An inner horn inclusion `Λ[n, i].ι` is a retract of `(Λ[2, 1] ⊔ Λ[n, i]).ι`
its pushout-product with `Λ[2, 1].ι`. -/
@[no_expose]
noncomputable def innerHornRetract {n : ℕ} (i : Fin (n + 1))
    (h0 : 0 < i) (hn : i < Fin.last n) :
    RetractArrow Λ[n, i].ι (Λ[2, 1].unionProd Λ[n, i]).ι := by
  let s : Δ[n] ⟶ Δ[2] ⊗ Δ[n] := lift (stdSimplex.map (SimplexCategory.Hom.mk (s₀ i))) (𝟙 _)
  let r : Δ[2] ⊗ Δ[n] ⟶ Δ[n] :=
    (prodStdSimplex.isoNerve 2 n).hom ≫ nerveMap (r₀ i).uliftMap.monotone.functor ≫
      (stdSimplex.isoNerve n).inv
  refine (Subfunctor.retractArrow Λ[n, i] (Λ[2, 1].unionProd Λ[n, i])
    ⟨s, r, ?_⟩ ?_ ?_).trans (Retract.refl _)
  · ext ⟨⟨k⟩⟩ x j
    apply Fin.val_eq_of_eq
    change r₀ _ ((s₀ i) (x j), x j) = x j
    dsimp [r₀, s₀]
    grind
  · intro k x hx
    exact Or.inl ⟨Set.mem_univ _, hx⟩
  · rintro ⟨⟨k⟩⟩ ⟨x, y⟩ h
    change r.app _ (x, y) ∈ Λ[n, i].obj _
    rw [Subcomplex.mem_unionProd_iff] at h
    rw [mem_horn_iff_notMem_range]
    rcases h with hy | hx
    · obtain ⟨a, ha, hy⟩ := (mem_horn_iff_notMem_range y i).1 hy
      refine ⟨a, ha, fun ⟨j, hj⟩ ↦ ?_⟩
      change (if y j < i ∧ x j = 0 ∨ i < y j ∧ x j = 2 then y j else i) = a at hj
      grind
    · obtain ⟨a, ha, hx⟩ := (mem_horn_iff_notMem_range x 1).1 hx
      fin_cases a
      · refine ⟨0, ne_of_lt h0, fun ⟨j, hj⟩ ↦ ?_⟩
        change (if y j < i ∧ x j = 0 ∨ i < y j ∧ x j = 2 then y j else i) = 0 at hj
        grind
      · exact (ha rfl).elim
      · refine ⟨Fin.last n, ne_of_gt hn, fun ⟨j, hj⟩ ↦ ?_⟩
        change (if y j < i ∧ x j = 0 ∨ i < y j ∧ x j = 2 then y j else i) = Fin.last n at hj
        grind

end SSet
