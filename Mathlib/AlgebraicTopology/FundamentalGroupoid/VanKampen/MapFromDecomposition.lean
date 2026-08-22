module

public import Mathlib
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CanonicalCocone
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.UniversalProperty
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.PathHelpers
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.SingleCovered
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.ComposeMorphisms

@[expose] public section

open TopologicalSpace CategoryTheory Limits

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

/-- Given an explicit decomposition of a path into segments, compute the resulting morphism. -/
def map_from_decomposition {x y : X} {n : ℕ}
    (pts : Fin (n + 1) → X)
    (covers : Fin n → Opens X)
    (hcover_mem : ∀ i, covers i ∈ 𝒰)
    (h_start : pts 0 = x)
    (h_end : pts (Fin.last n) = y)
    (h_segments : ∀ i : Fin n,
      ∃ (γi : Path (pts (Fin.castSucc i)) (pts (Fin.succ i))),
        Set.range γi ⊆ (covers i : Set X)) :
    (desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x)) ⟶
    (desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y)) := by
  let objs : Fin (n + 1) → s.pt :=
    fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))

  let homs : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i) := by
    intro i
    let h_i : ∃ (γi : Path (pts (Fin.castSucc i)) (pts (Fin.succ i))),
        Set.range γi ⊆ (covers i : Set X) := h_segments i
    let γi := Classical.choose h_i
    let hγi := Classical.choose_spec h_i
    exact single_covered_map X 𝒰 hcover hfinite_intersections s γi (covers i) (hcover_mem i) hγi

  let comp : objs 0 ⟶ objs (Fin.last n) := comp_list n objs homs

  have h0 : objs 0 = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x) := by
    dsimp only [objs]
    have h_eq : FundamentalGroupoid.mk (pts 0) = FundamentalGroupoid.mk x := by
      congr
      <;> exact h_start
    rw [h_eq]

  have hn : objs (Fin.last n) = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y) := by
    dsimp only [objs]
    have h_eq : FundamentalGroupoid.mk (pts (Fin.last n)) = FundamentalGroupoid.mk y := by
      congr
      <;> exact h_end
    rw [h_eq]

  exact eqToHom h0.symm ≫ comp ≫ eqToHom hn

end

end
