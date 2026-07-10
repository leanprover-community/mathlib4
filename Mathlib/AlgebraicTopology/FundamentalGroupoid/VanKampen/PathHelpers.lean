module

public import Mathlib

@[expose] public section

open TopologicalSpace Path.Homotopic unitInterval CategoryTheory

noncomputable section

variable {X : Type*} [TopologicalSpace X]

namespace Path

/-- Restrict a path to a subinterval [a, b] ⊆ [0,1].

This is a wrapper around `Path.truncateOfLE` for the case where we explicitly
have `0 ≤ a` and `b ≤ 1`. The resulting path follows γ on [a, b]. -/
def restrict {x y : X} (γ : Path x y) (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    Path (γ.extend a) (γ.extend b) :=
  γ.truncateOfLE hab

/-- The range of a restricted path is a subset of the range of the original path. -/
theorem range_restrict_subset {x y : X} (γ : Path x y)
    (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    Set.range (γ.restrict a b ha hb hab) ⊆ Set.range γ := by
  have h : Set.range (γ.truncateOfLE hab) ⊆ Set.range γ := truncate_range γ
  exact h

/-- If the range of a path is contained in a set U, then the path factors
    through the subtype U. -/
theorem lift_to_subtype {x y : X} (γ : Path x y) {U : Set X}
    (hx : x ∈ U) (hy : y ∈ U) (h : Set.range γ ⊆ U) :
    ∃ (γ' : Path (⟨x, hx⟩ : U) (⟨y, hy⟩)),
      (∀ (t : I), (γ' t : X) = γ t) := by
  let γ' : Path (⟨x, hx⟩ : U) (⟨y, hy⟩) :=
    { toFun := fun t : I => ⟨γ t, h (Set.mem_range_self t)⟩
      continuous_toFun := by
        exact Continuous.subtype_mk γ.continuous _
      source' := by
        simp
      target' := by
        simp }
  refine ⟨γ', fun t => rfl⟩

/-- Applying the inclusion map to a lifted path gives back the original path. -/
theorem map_lift_to_subtype {x y : X} (γ : Path x y) {U : Set X}
    (hx : x ∈ U) (hy : y ∈ U) (h : Set.range γ ⊆ U)
    (γ' : Path (⟨x, hx⟩ : U) (⟨y, hy⟩))
    (hγ' : ∀ (t : I), (γ' t : X) = γ t) :
    γ'.map continuous_subtype_val = γ := by
  ext t
  simpa [map_coe] using hγ' t

/-- The homotopy class of a concatenation of paths equals the composition
    of the homotopy classes. -/
theorem homotopic_quotient_trans_eq_comp {x y z : X} (γ₁ : Path x y) (γ₂ : Path y z) :
    Path.Homotopic.Quotient.mk (γ₁.trans γ₂) =
      (Path.Homotopic.Quotient.mk γ₁).trans (Path.Homotopic.Quotient.mk γ₂) :=
  Path.Homotopic.Quotient.mk_trans γ₁ γ₂

/-- In the fundamental groupoid, composition of morphisms corresponds to
    concatenation of paths. This is a direct consequence of `comp_eq` and `mk_trans`. -/
theorem fundamentalGroupoid_comp_eq_trans
    (x' y' z' : FundamentalGroupoid X)
    (p : x' ⟶ y') (q : y' ⟶ z') :
    p ≫ q = p.trans q :=
  FundamentalGroupoid.comp_eq x' y' z' p q

end Path

end

end
