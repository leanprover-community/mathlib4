module

public import Mathlib
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CanonicalCocone
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.UniversalProperty
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.PathHelpers
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.SingleCovered
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.SingleCoveredSimple
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.EqToHomHelpers
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.ComposeMorphisms
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.MapFromDecomposition

@[expose] public section

open TopologicalSpace CategoryTheory Limits

open scoped unitInterval

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

/-- Helper: the range of a concatenated path is the union of the ranges. -/
lemma range_trans_subset {X : Type*} [TopologicalSpace X] {x y z : X}
    (γ₁ : Path x y) (γ₂ : Path y z) {U : Set X}
    (h₁ : Set.range γ₁ ⊆ U) (h₂ : Set.range γ₂ ⊆ U) :
    Set.range (γ₁.trans γ₂) ⊆ U := by
  have h : Set.range (γ₁.trans γ₂) = Set.range γ₁ ∪ Set.range γ₂ :=
    Path.trans_range γ₁ γ₂
  rw [h]
  exact Set.union_subset h₁ h₂

/-- Refining a decomposition by splitting one segment into two gives the same result.

    This follows from the simple version plus eqToHom transport bookkeeping. -/
theorem single_covered_split_eq {x y z : X}
    (U : Opens X) (hU : U ∈ 𝒰)
    (γ₁ : Path x y) (h₁ : Set.range γ₁ ⊆ (U : Set X))
    (γ₂ : Path y z) (h₂ : Set.range γ₂ ⊆ (U : Set X)) :
    let f₁ := single_covered_map X 𝒰 hcover hfinite_intersections s γ₁ U hU h₁
    let f₂ := single_covered_map X 𝒰 hcover hfinite_intersections s γ₂ U hU h₂
    let f_both := single_covered_map X 𝒰 hcover hfinite_intersections s (γ₁.trans γ₂) U hU
      (range_trans_subset γ₁ γ₂ h₁ h₂)
    f₁ ≫ f₂ = f_both := by
  dsimp only

  -- Get that x, y, z are all in U
  have hx : x ∈ U := by
    have h1 : γ₁ 0 ∈ Set.range γ₁ := Set.mem_range_self 0
    have h2 : γ₁ 0 = x := γ₁.source
    rw [h2] at h1
    exact h₁ h1
  have hy : y ∈ U := by
    have h1 : γ₁ 1 ∈ Set.range γ₁ := Set.mem_range_self 1
    have h2 : γ₁ 1 = y := γ₁.target
    rw [h2] at h1
    exact h₁ h1
  have hz : z ∈ U := by
    have h1 : γ₂ 1 ∈ Set.range γ₂ := Set.mem_range_self 1
    have h2 : γ₂ 1 = z := γ₂.target
    rw [h2] at h1
    exact h₂ h1

  let x_obj := FundamentalGroupoid.mk x
  let y_obj := FundamentalGroupoid.mk y
  let z_obj := FundamentalGroupoid.mk z

  -- The obj_at objects
  let obj_at_x := obj_at X 𝒰 s x U hU hx
  let obj_at_y := obj_at X 𝒰 s y U hU hy
  let obj_at_z := obj_at X 𝒰 s z U hU hz

  -- The desc_functor_obj objects
  let dfo_x := desc_functor_obj X 𝒰 hcover s x_obj
  let dfo_y := desc_functor_obj X 𝒰 hcover s y_obj
  let dfo_z := desc_functor_obj X 𝒰 hcover s z_obj

  -- The equalities from obj_at to desc_functor_obj
  have h_dom_x : obj_at_x = dfo_x := by
    dsimp only [obj_at_x, dfo_x, desc_functor_obj]
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ x ∈ U' := hcover x
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ x ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s x U' hU'.1 hU'.2 = obj_at X 𝒰 s x U hU hx :=
      obj_at_eq X 𝒰 s hfinite_intersections x U' U hU'.1 hU hU'.2 hx
    exact this.symm
  have h_dom_y : obj_at_y = dfo_y := by
    dsimp only [obj_at_y, dfo_y, desc_functor_obj]
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ y ∈ U' := hcover y
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ y ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s y U' hU'.1 hU'.2 = obj_at X 𝒰 s y U hU hy :=
      obj_at_eq X 𝒰 s hfinite_intersections y U' U hU'.1 hU hU'.2 hy
    exact this.symm
  have h_dom_z : obj_at_z = dfo_z := by
    dsimp only [obj_at_z, dfo_z, desc_functor_obj]
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ z ∈ U' := hcover z
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ z ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s z U' hU'.1 hU'.2 = obj_at X 𝒰 s z U hU hz :=
      obj_at_eq X 𝒰 s hfinite_intersections z U' U hU'.1 hU hU'.2 hz
    exact this.symm

  -- The simple versions of the maps
  let f₁_simple := single_covered_map_simple X 𝒰 s γ₁ U hU hx hy h₁
  let f₂_simple := single_covered_map_simple X 𝒰 s γ₂ U hU hy hz h₂
  let f_both_simple := single_covered_map_simple X 𝒰 s (γ₁.trans γ₂) U hU hx hz
    (range_trans_subset_simple γ₁ γ₂ h₁ h₂)

  -- The split property for the simple version (already proved!)
  have h_simple : f₁_simple ≫ f₂_simple = f_both_simple :=
    single_covered_split_eq_simple X 𝒰 s U hU hx hy hz γ₁ h₁ γ₂ h₂

  -- The full versions are the simple versions composed with eqToHom transports
  have h_f₁ : single_covered_map X 𝒰 hcover hfinite_intersections s γ₁ U hU h₁ =
      eqToHom h_dom_x.symm ≫ f₁_simple ≫ eqToHom h_dom_y := by
    rfl
  have h_f₂ : single_covered_map X 𝒰 hcover hfinite_intersections s γ₂ U hU h₂ =
      eqToHom h_dom_y.symm ≫ f₂_simple ≫ eqToHom h_dom_z := by
    rfl
  have h_f_both : single_covered_map X 𝒰 hcover hfinite_intersections s (γ₁.trans γ₂) U hU
      (range_trans_subset γ₁ γ₂ h₁ h₂) =
      eqToHom h_dom_x.symm ≫ f_both_simple ≫ eqToHom h_dom_z := by
    rfl

  -- Now we can use the eqToHom_comp_cancel lemma
  have h_main : (eqToHom h_dom_x.symm ≫ f₁_simple ≫ eqToHom h_dom_y) ≫
      (eqToHom h_dom_y.symm ≫ f₂_simple ≫ eqToHom h_dom_z) =
      eqToHom h_dom_x.symm ≫ (f₁_simple ≫ f₂_simple) ≫ eqToHom h_dom_z :=
    eqToHom_comp_cancel h_dom_x h_dom_y h_dom_z f₁_simple f₂_simple

  rw [h_f₁, h_f₂, h_f_both]
  rw [h_main, h_simple]

end

end
