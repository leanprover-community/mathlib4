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

An inner horn inclusion `Λ[n, i].ι` is a retract of `(Λ[2, 1].unionProd Λ[n, i]).ι`.

## References

* [Charles Rezk, *Introduction to Quasicategories*, proof of Lemma 78.4][Rezk2022]

-/

@[expose] public section

universe u

namespace SSet

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory Functor

namespace innerHornRetract

/-- The first coordinate of the underlying section on vertices. -/
def s₀ {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) →o Fin 3 where
  toFun j := if j < i then 0 else if j = i then 1 else 2
  monotone' _ _ _ := by grind

lemma stdSimplex_map_s₀_app_apply {n : ℕ} (i : Fin (n + 1)) {d : ℕ}
    (x : Δ[n] _⦋d⦌) (j : Fin (d + 1)) :
    (stdSimplex.{u}.map (SimplexCategory.Hom.mk (s₀ i))).app (Opposite.op ⦋d⦌) x j =
      if x j < i then 0 else if x j = i then 1 else 2 := rfl

/-- The underlying retraction on vertices. -/
def r₀ {n : ℕ} (i : Fin (n + 1)) : Fin 3 × Fin (n + 1) →o Fin (n + 1) where
  toFun p := if (p.2 < i ∧ p.1 = 0) ∨ (i < p.2 ∧ p.1 = 2) then p.2 else i
  monotone' := by
    rintro ⟨k, j⟩ ⟨k', j'⟩ ⟨hk, hj⟩
    grind

/-- The retract of standard simplices underlying the retract of the horn inclusions. -/
def retract {n : ℕ} (i : Fin (n + 1)) : Retract (Δ[n] : SSet.{u}) (Δ[2] ⊗ Δ[n]) where
  i := lift (stdSimplex.map (SimplexCategory.Hom.mk (s₀ i))) (𝟙 _)
  r := prodStdSimplex.toStdSimplex (r₀ i)
  retract := by
    ext ⟨⟨d⟩⟩ x j : 5
    simp [r₀, stdSimplex_map_s₀_app_apply]
    grind

end innerHornRetract

open innerHornRetract in
/-- An inner horn inclusion `Λ[n, i].ι` is a retract of `(Λ[2, 1].unionProd Λ[n, i]).ι`. -/
noncomputable def innerHornRetract {n : ℕ} (i : Fin (n + 1))
    (h0 : 0 < i) (hn : i < Fin.last n) :
    RetractArrow Λ[n, i].ι (Λ[2, 1].unionProd Λ[n, i]).ι := by
  refine Λ[n, i].retractArrow (Λ[2, 1].unionProd Λ[n, i]) (retract i) ?_ ?_
  · intro d x hx
    rw [Subfunctor.preimage_obj, Set.mem_preimage, Subcomplex.mem_unionProd_iff]
    exact Or.inl hx
  · rintro ⟨⟨d⟩⟩ z hz
    simp only [Subfunctor.preimage_obj, Set.mem_preimage, mem_horn_iff_notMem_range]
    rcases (Subcomplex.mem_unionProd_iff _ _ z).1 hz with hy | hx
    · obtain ⟨a, ha, hy⟩ := (mem_horn_iff_notMem_range z.2 i).1 hy
      refine ⟨a, ha, fun ⟨j, hj⟩ ↦ ?_⟩
      simp [retract, r₀] at hj
      grind
    · obtain ⟨a, ha, hx⟩ := (mem_horn_iff_notMem_range z.1 1).1 hx
      fin_cases a
      · refine ⟨0, ne_of_lt h0, fun ⟨j, hj⟩ ↦ ?_⟩
        simp [retract, r₀] at hj
        grind
      · grind
      · refine ⟨Fin.last n, ne_of_gt hn, fun ⟨j, hj⟩ ↦ ?_⟩
        simp [retract, r₀] at hj
        grind

end SSet
