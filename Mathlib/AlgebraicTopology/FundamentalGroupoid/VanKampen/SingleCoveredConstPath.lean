module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.SingleCovered

@[expose] public section

set_option maxHeartbeats 200000

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

include hcover hfinite_intersections

/-- single_covered_map of a constant path equals eqToHom. -/
lemma single_covered_map_const_path {x y : X} (γ : Path x y) (hxy : x = y)
    (U : Opens X) (hU : U ∈ 𝒰) (h_range : Set.range γ ⊆ (U : Set X))
    (h_const : ∀ t, γ t = x) :
    single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h_range =
    eqToHom (by
      apply congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk)
      exact hxy) := by
  classical
  let U_set : Set X := (U : Set X)
  have hx : x ∈ U := by
    have h1 : γ 0 ∈ Set.range γ := Set.mem_range_self 0
    have h2 : γ 0 = x := γ.source
    rw [h2] at h1
    exact h_range h1
  have hy : y ∈ U := by
    have h1 : γ 1 ∈ Set.range γ := Set.mem_range_self 1
    have h2 : γ 1 = y := γ.target
    rw [h2] at h1
    exact h_range h1
  let γ_lift : Path (⟨x, hx⟩ : U_set) (⟨y, hy⟩ : U_set) :=
    (Path.lift_to_subtype γ hx hy h_range).choose
  let hγ_lift : ∀ (t : I), (γ_lift t : X) = γ t :=
    (Path.lift_to_subtype γ hx hy h_range).choose_spec
  have h_pointwise : ∀ (t : I), (γ_lift t : X) = x := by
    intro t
    have h1 : (γ_lift t : X) = γ t := hγ_lift t
    rw [h1, h_const t]
  have h_lift_const : ∀ (t : I), γ_lift t = γ_lift 0 := by
    intro t
    apply Subtype.ext
    have h1 : (γ_lift t : X) = x := h_pointwise t
    have h2 : (γ_lift 0 : X) = x := h_pointwise 0
    rw [h1, h2]
  let γ_class : (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
                (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) :=
    Path.Homotopic.Quotient.mk γ_lift
  have h_sub_eq : (⟨x, hx⟩ : U_set) = (⟨y, hy⟩ : U_set) := by
    apply Subtype.ext
    exact hxy
  have h_path_eq : γ_lift = (Path.refl (⟨x, hx⟩ : U_set)).cast rfl h_sub_eq.symm := by
    apply Path.ext
    funext t
    have h1 : γ_lift t = γ_lift 0 := h_lift_const t
    have h2 : γ_lift 0 = (⟨x, hx⟩ : U_set) := by
      exact γ_lift.source
    have h3 : ((Path.refl (⟨x, hx⟩ : U_set)).cast rfl h_sub_eq.symm) t = (⟨x, hx⟩ : U_set) := by
      simp [Path.cast]
      <;> rfl
    rw [h1, h2, h3]
  have h_class_eq : γ_class = eqToHom (congr_arg FundamentalGroupoid.mk h_sub_eq) := by
    have h_main : Path.Homotopic.Quotient.mk ((Path.refl (⟨x, hx⟩ : U_set)).cast rfl h_sub_eq.symm) =
        eqToHom (congr_arg FundamentalGroupoid.mk h_sub_eq) := by
      have h_conj := FundamentalGroupoid.conj_eqToHom (hx := rfl) (hy := h_sub_eq.symm) (p := Path.Homotopic.Quotient.mk (Path.refl (⟨x, hx⟩ : U_set)))
      have h_id : Path.Homotopic.Quotient.mk (Path.refl (⟨x, hx⟩ : U_set)) = 𝟙 (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) :=
        FundamentalGroupoid.id_eq_path_refl (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set))
      simpa [h_id] using h_conj.symm
    have h1 : γ_class = Path.Homotopic.Quotient.mk ((Path.refl (⟨x, hx⟩ : U_set)).cast rfl h_sub_eq.symm) := by
      dsimp only [γ_class]
      exact congr_arg (Path.Homotopic.Quotient.mk) h_path_eq
    rw [h1]
    exact h_main
  let f : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
          (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) :=
    (s.ι.app ⟨U, hU⟩).map γ_class
  have h_f_eq : f = eqToHom (congr_arg ((s.ι.app ⟨U, hU⟩).obj) (congr_arg FundamentalGroupoid.mk h_sub_eq)) := by
    dsimp only [f]
    rw [h_class_eq]
    <;> exact CategoryTheory.eqToHom_map (s.ι.app ⟨U, hU⟩) (congr_arg FundamentalGroupoid.mk h_sub_eq)
  have h_eq1 : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) =
      obj_at X 𝒰 s x U hU hx := by rfl
  have h_eq2 : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) =
      obj_at X 𝒰 s y U hU hy := by rfl
  let x_obj : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) :=
    FundamentalGroupoid.mk x
  let y_obj : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) :=
    FundamentalGroupoid.mk y
  have h_dom : obj_at X 𝒰 s x U hU hx = desc_functor_obj X 𝒰 hcover s x_obj := by
    dsimp only [desc_functor_obj]
    let x_pt : X := x_obj.as
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ x_pt ∈ U' := hcover x_pt
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ x_pt ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s x U' hU'.1 hU'.2 = obj_at X 𝒰 s x U hU hx :=
      obj_at_eq X 𝒰 s hfinite_intersections x U' U hU'.1 hU hU'.2 hx
    exact this.symm
  have h_cod : obj_at X 𝒰 s y U hU hy = desc_functor_obj X 𝒰 hcover s y_obj := by
    dsimp only [desc_functor_obj]
    let y_pt : X := y_obj.as
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ y_pt ∈ U' := hcover y_pt
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ y_pt ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s y U' hU'.1 hU'.2 = obj_at X 𝒰 s y U hU hy :=
      obj_at_eq X 𝒰 s hfinite_intersections y U' U hU'.1 hU hU'.2 hy
    exact this.symm
  let f' : obj_at X 𝒰 s x U hU hx ⟶ obj_at X 𝒰 s y U hU hy :=
    eqToHom h_eq1.symm ≫ f ≫ eqToHom h_eq2
  have h_obj_eq : obj_at X 𝒰 s x U hU hx = obj_at X 𝒰 s y U hU hy := by
    dsimp only [obj_at]
    apply congr_arg ((s.ι.app ⟨U, hU⟩).obj)
    apply congr_arg FundamentalGroupoid.mk
    apply Subtype.ext
    exact hxy
  have h_f'_eq : f' = eqToHom h_obj_eq := by
    dsimp only [f']
    rw [h_f_eq]
    calc
      eqToHom h_eq1.symm ≫ eqToHom (congr_arg ((s.ι.app ⟨U, hU⟩).obj) (congr_arg FundamentalGroupoid.mk h_sub_eq)) ≫ eqToHom h_eq2
        = (eqToHom h_eq1.symm ≫ eqToHom (congr_arg ((s.ι.app ⟨U, hU⟩).obj) (congr_arg FundamentalGroupoid.mk h_sub_eq))) ≫ eqToHom h_eq2 := by
          rw [Category.assoc]
      _ = eqToHom (h_eq1.symm.trans (congr_arg ((s.ι.app ⟨U, hU⟩).obj) (congr_arg FundamentalGroupoid.mk h_sub_eq))) ≫ eqToHom h_eq2 := by
          rw [eqToHom_trans]
      _ = eqToHom ((h_eq1.symm.trans (congr_arg ((s.ι.app ⟨U, hU⟩).obj) (congr_arg FundamentalGroupoid.mk h_sub_eq))).trans h_eq2) := by
          rw [eqToHom_trans]
      _ = eqToHom h_obj_eq := by
          apply congr_arg eqToHom
          apply Subsingleton.elim
  have h_main : eqToHom h_dom.symm ≫ f' ≫ eqToHom h_cod =
      eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hxy) := by
    rw [h_f'_eq]
    <;> simp [eqToHom_trans, Category.assoc]
    <;> exact?
  exact h_main

end

end
