module

public import Mathlib
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CanonicalCocone
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.UniversalProperty
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.PathHelpers
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.SingleCoveredSimple

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

/-- Given a path γ whose range is contained in some U ∈ 𝒰, we can map its homotopy class
    to a morphism in s.pt using the cocone leg for U. -/
def single_covered_map {x y : X} (γ : Path x y)
    (U : Opens X) (hU : U ∈ 𝒰) (h : Set.range γ ⊆ (U : Set X)) :
    (desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x)) ⟶
    (desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y)) := by
  -- Get that x and y are in U (since their range is in U)
  have hx : x ∈ U := by
    have h1 : γ 0 ∈ Set.range γ := Set.mem_range_self 0
    have h2 : γ 0 = x := γ.source
    rw [h2] at h1
    exact h h1
  have hy : y ∈ U := by
    have h1 : γ 1 ∈ Set.range γ := Set.mem_range_self 1
    have h2 : γ 1 = y := γ.target
    rw [h2] at h1
    exact h h1

  let U_set : Set X := (U : Set X)

  -- Lift the path to the subtype U
  let γ_lift : Path (⟨x, hx⟩ : U_set) (⟨y, hy⟩ : U_set) :=
    (Path.lift_to_subtype γ hx hy h).choose
  let hγ_lift : ∀ (t : I), (γ_lift t : X) = γ t :=
    (Path.lift_to_subtype γ hx hy h).choose_spec

  -- Get the homotopy class in π₁(U)
  let γ_class : (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
                (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) :=
    Path.Homotopic.Quotient.mk γ_lift

  -- Apply the cocone functor
  let f : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
          (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) :=
    (s.ι.app ⟨U, hU⟩).map γ_class

  let x_obj : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) :=
    FundamentalGroupoid.mk x
  let y_obj : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) :=
    FundamentalGroupoid.mk y

  -- By definition, obj_at X 𝒰 s x U hU hx = (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk ⟨x, hx⟩)
  have h_eq1 : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) =
      obj_at X 𝒰 s x U hU hx := by rfl
  have h_eq2 : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) =
      obj_at X 𝒰 s y U hU hy := by rfl

  -- And by obj_at_eq, obj_at for our U equals desc_functor_obj
  -- desc_functor_obj picks some U' via Classical.choose; we show obj_at U = obj_at U'
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

  -- Now we have:
  -- f : A → B
  -- h_eq1 : A = obj_at x
  -- h_eq2 : B = obj_at y
  -- h_dom : obj_at x = desc_functor_obj x
  -- h_cod : obj_at y = desc_functor_obj y
  -- We want: desc_functor_obj x → desc_functor_obj y

  -- Transport f to go from obj_at x to obj_at y
  let f' : obj_at X 𝒰 s x U hU hx ⟶ obj_at X 𝒰 s y U hU hy :=
    eqToHom h_eq1.symm ≫ f ≫ eqToHom h_eq2

  -- Then transport to go from desc_functor_obj x to desc_functor_obj y
  exact eqToHom h_dom.symm ≫ f' ≫ eqToHom h_cod

/-- single_covered_map of the constant path is the identity morphism. -/
lemma single_covered_map_refl {x : X}
    (U : Opens X) (hU : U ∈ 𝒰) (hx : x ∈ U) :
    single_covered_map X 𝒰 hcover hfinite_intersections s (Path.refl x) U hU
      (by simp [hx] <;> tauto) =
    𝟙 (desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x)) := by
  dsimp only [single_covered_map]
  let U_set : Set X := (U : Set X)
  let h_range : Set.range (Path.refl x) ⊆ (U : Set X) := by simp [hx] <;> tauto
  let hx' : x ∈ U := hx
  let hy' : x ∈ U := hx
  let γ_lift : Path (⟨x, hx'⟩ : U_set) (⟨x, hy'⟩ : U_set) :=
    (Path.lift_to_subtype (Path.refl x) hx' hy' h_range).choose
  let hγ_lift : ∀ (t : I), (γ_lift t : X) = (Path.refl x) t :=
    (Path.lift_to_subtype (Path.refl x) hx' hy' h_range).choose_spec

  -- Step 1: γ_lift is pointwise equal to the constant path
  have h_pointwise : ∀ (t : I), γ_lift t = (⟨x, hx'⟩ : U_set) := by
    intro t
    apply Subtype.ext
    have h1 : (γ_lift t : X) = (Path.refl x) t := hγ_lift t
    have h2 : (Path.refl x) t = x := by simp [Path.refl_apply]
    rw [h1, h2] <;> rfl

  -- Step 2: Therefore γ_lift = Path.refl (⟨x, hx'⟩)
  have h_path_eq : γ_lift = Path.refl (⟨x, hx'⟩ : U_set) := by
    apply Path.ext
    funext t
    exact h_pointwise t

  -- Step 3: The homotopy class is the identity
  let γ_class : (FundamentalGroupoid.mk (⟨x, hx'⟩ : U_set)) ⟶
                (FundamentalGroupoid.mk (⟨x, hy'⟩ : U_set)) :=
    Path.Homotopic.Quotient.mk γ_lift
  have h_class_eq : γ_class = 𝟙 (FundamentalGroupoid.mk (⟨x, hx'⟩ : U_set)) := by
    have h1 : Path.Homotopic.Quotient.mk γ_lift = Path.Homotopic.Quotient.mk (Path.refl (⟨x, hx'⟩ : U_set)) := by
      rw [h_path_eq]
    have h2 : Path.Homotopic.Quotient.mk (Path.refl (⟨x, hx'⟩ : U_set)) = 𝟙 (FundamentalGroupoid.mk (⟨x, hx'⟩ : U_set)) :=
      (FundamentalGroupoid.id_eq_path_refl (FundamentalGroupoid.mk (⟨x, hx'⟩ : U_set))).symm
    exact Eq.trans h1 h2

  -- Step 4: The functor preserves identities
  let f : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx'⟩ : U_set)) ⟶
          (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hy'⟩ : U_set)) :=
    (s.ι.app ⟨U, hU⟩).map γ_class
  have h_f_eq : f = 𝟙 ((s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx'⟩ : U_set))) := by
    dsimp only [f]
    rw [h_class_eq]
    <;> exact?

  -- Step 5: Simplify the transports
  let x_obj : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) :=
    FundamentalGroupoid.mk x
  have h_eq1 : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx'⟩ : U_set)) =
      obj_at X 𝒰 s x U hU hx' := by rfl
  have h_eq2 : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hy'⟩ : U_set)) =
      obj_at X 𝒰 s x U hU hy' := by rfl
  have h_dom : obj_at X 𝒰 s x U hU hx' = desc_functor_obj X 𝒰 hcover s x_obj := by
    dsimp only [desc_functor_obj]
    let x_pt : X := x_obj.as
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ x_pt ∈ U' := hcover x_pt
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ x_pt ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s x U' hU'.1 hU'.2 = obj_at X 𝒰 s x U hU hx' :=
      obj_at_eq X 𝒰 s hfinite_intersections x U' U hU'.1 hU hU'.2 hx'
    exact this.symm
  have h_cod : obj_at X 𝒰 s x U hU hy' = desc_functor_obj X 𝒰 hcover s x_obj := by
    dsimp only [desc_functor_obj]
    let x_pt : X := x_obj.as
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ x_pt ∈ U' := hcover x_pt
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ x_pt ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s x U' hU'.1 hU'.2 = obj_at X 𝒰 s x U hU hy' :=
      obj_at_eq X 𝒰 s hfinite_intersections x U' U hU'.1 hU hU'.2 hy'
    exact this.symm

  let f' : obj_at X 𝒰 s x U hU hx' ⟶ obj_at X 𝒰 s x U hU hy' :=
    eqToHom h_eq1.symm ≫ f ≫ eqToHom h_eq2

  -- Since hx' = hy', h_eq1 = h_eq2
  have h_eq1_eq_h_eq2 : h_eq1 = h_eq2 := by rfl
  have h_f'_eq : f' = 𝟙 (obj_at X 𝒰 s x U hU hx') := by
    dsimp only [f']
    rw [h_f_eq, h_eq1_eq_h_eq2]
    <;> simp [eqToHom_trans, Category.assoc]
    <;> exact?

  -- Final step
  have h_main : eqToHom h_dom.symm ≫ f' ≫ eqToHom h_cod =
      𝟙 (desc_functor_obj X 𝒰 hcover s x_obj) := by
    rw [h_f'_eq]
    have h_dom_eq_h_cod : h_dom = h_cod := by rfl
    rw [h_dom_eq_h_cod]
    <;> simp [eqToHom_trans, Category.assoc]
    <;> exact?
  exact h_main

/-- Helper lemma: if W ≤ U are opens in 𝒰, and γ's range is in W,
    then single_covered_map using U equals single_covered_map using W. -/
lemma single_covered_map_indep_of_le {x y : X} (γ : Path x y)
    (W U : Opens X) (hW : W ∈ 𝒰) (hU : U ∈ 𝒰) (hWU : W ≤ U)
    (hW_range : Set.range γ ⊆ (W : Set X)) :
    @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ U hU (subset_trans hW_range hWU) =
    @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ W hW hW_range := by
  classical
  let W_set : Set X := (W : Set X)
  let U_set : Set X := (U : Set X)

  -- Get that x and y are in W (hence also in U)
  have hxW : x ∈ W := by
    have h1 : γ 0 ∈ Set.range γ := Set.mem_range_self 0
    have h2 : γ 0 = x := γ.source
    rw [h2] at h1
    exact hW_range h1
  have hyW : y ∈ W := by
    have h1 : γ 1 ∈ Set.range γ := Set.mem_range_self 1
    have h2 : γ 1 = y := γ.target
    rw [h2] at h1
    exact hW_range h1
  have hxU : x ∈ U := hWU hxW
  have hyU : y ∈ U := hWU hyW

  -- Lift γ to both W and U
  let γ_W_lift : Path (⟨x, hxW⟩ : W_set) (⟨y, hyW⟩ : W_set) :=
    (Path.lift_to_subtype γ hxW hyW hW_range).choose
  let hγ_W_lift : ∀ (t : I), (γ_W_lift t : X) = γ t :=
    (Path.lift_to_subtype γ hxW hyW hW_range).choose_spec

  let γ_U_lift : Path (⟨x, hxU⟩ : U_set) (⟨y, hyU⟩ : U_set) :=
    (Path.lift_to_subtype γ hxU hyU (subset_trans hW_range hWU)).choose
  let hγ_U_lift : ∀ (t : I), (γ_U_lift t : X) = γ t :=
    (Path.lift_to_subtype γ hxU hyU (subset_trans hW_range hWU)).choose_spec

  -- The inclusion map from W to U
  let i_WU_set : W_set → U_set := fun z => ⟨z, hWU z.2⟩
  have hi_cont : Continuous i_WU_set := by
    exact continuous_inclusion hWU

  -- Map the W-lifted path along the inclusion
  let γ_W_mapped : Path (⟨x, hxU⟩ : U_set) (⟨y, hyU⟩ : U_set) :=
    γ_W_lift.map hi_cont

  -- The mapped path equals the U-lifted path
  have h_eq_fun : ⇑γ_W_mapped = ⇑γ_U_lift := by
    funext t
    apply Subtype.ext
    have h1 : (γ_W_mapped t : X) = γ t := by
      have h1a : (γ_W_mapped t : X) = (i_WU_set (γ_W_lift t) : X) := by
        rw [Path.map_coe] <;> rfl
      rw [h1a]
      have h1b : (i_WU_set (γ_W_lift t) : X) = (γ_W_lift t : X) := by rfl
      rw [h1b]
      exact hγ_W_lift t
    have h2 : (γ_U_lift t : X) = γ t := hγ_U_lift t
    have h3 : (γ_W_mapped t : X) = (γ_U_lift t : X) := by
      rw [h1, h2]
    exact h3
  have h_eq_paths : γ_W_mapped = γ_U_lift := Path.ext h_eq_fun

  -- The inclusion W → U as a morphism in the subtype category
  let i_WU_subtype : (⟨W, hW⟩ : {U : Opens X // U ∈ 𝒰}) ⟶ (⟨U, hU⟩ : {U : Opens X // U ∈ 𝒰}) :=
    homOfLE hWU

  let D := ((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
    Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor

  -- Naturality of the cocone
  have h_nat : D.map i_WU_subtype ≫ s.ι.app ⟨U, hU⟩ = s.ι.app ⟨W, hW⟩ :=
    s.ι.naturality i_WU_subtype

  -- Get the homotopy classes
  let γ_W_class : (FundamentalGroupoid.mk (⟨x, hxW⟩ : W_set)) ⟶
                  (FundamentalGroupoid.mk (⟨y, hyW⟩ : W_set)) :=
    Path.Homotopic.Quotient.mk γ_W_lift
  let γ_U_class : (FundamentalGroupoid.mk (⟨x, hxU⟩ : U_set)) ⟶
                  (FundamentalGroupoid.mk (⟨y, hyU⟩ : U_set)) :=
    Path.Homotopic.Quotient.mk γ_U_lift

  -- The functor D.map i_WU_subtype maps γ_W_class to γ_U_class
  have h_map_class : (D.map i_WU_subtype).map γ_W_class = γ_U_class := by
    have h1 : (D.map i_WU_subtype).map γ_W_class = Path.Homotopic.Quotient.mk (γ_W_lift.map hi_cont) := by
      rfl
    have h2 : γ_W_lift.map hi_cont = γ_W_mapped := by rfl
    rw [h1, h2, h_eq_paths]
    <;> rfl

  -- We'll prove this using the simple version and obj_at_eq
  -- First, get the equalities between obj_at W and obj_at U
  have h_eq_x : obj_at X 𝒰 s x W hW hxW = obj_at X 𝒰 s x U hU hxU :=
    obj_at_eq X 𝒰 s hfinite_intersections x W U hW hU hxW hxU
  have h_eq_y : obj_at X 𝒰 s y W hW hyW = obj_at X 𝒰 s y U hU hyU :=
    obj_at_eq X 𝒰 s hfinite_intersections y W U hW hU hyW hyU

  -- Now we need to relate the full single_covered_map to the simple version
  -- The full version is: eqToHom h_dom.symm ≫ simple ≫ eqToHom h_cod
  -- where h_dom : obj_at ... = desc_functor_obj ...
  have h_dom_W : obj_at X 𝒰 s x W hW hxW = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x) := by
    dsimp only [desc_functor_obj]
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ x ∈ U' := hcover x
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ x ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s x U' hU'.1 hU'.2 = obj_at X 𝒰 s x W hW hxW :=
      obj_at_eq X 𝒰 s hfinite_intersections x U' W hU'.1 hW hU'.2 hxW
    exact this.symm
  have h_cod_W : obj_at X 𝒰 s y W hW hyW = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y) := by
    dsimp only [desc_functor_obj]
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ y ∈ U' := hcover y
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ y ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s y U' hU'.1 hU'.2 = obj_at X 𝒰 s y W hW hyW :=
      obj_at_eq X 𝒰 s hfinite_intersections y U' W hU'.1 hW hU'.2 hyW
    exact this.symm
  have h_dom_U : obj_at X 𝒰 s x U hU hxU = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x) := by
    dsimp only [desc_functor_obj]
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ x ∈ U' := hcover x
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ x ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s x U' hU'.1 hU'.2 = obj_at X 𝒰 s x U hU hxU :=
      obj_at_eq X 𝒰 s hfinite_intersections x U' U hU'.1 hU hU'.2 hxU
    exact this.symm
  have h_cod_U : obj_at X 𝒰 s y U hU hyU = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y) := by
    dsimp only [desc_functor_obj]
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ y ∈ U' := hcover y
    let U' : Opens X := Classical.choose h
    let hU' : U' ∈ 𝒰 ∧ y ∈ U' := Classical.choose_spec h
    have : obj_at X 𝒰 s y U' hU'.1 hU'.2 = obj_at X 𝒰 s y U hU hyU :=
      obj_at_eq X 𝒰 s hfinite_intersections y U' U hU'.1 hU hU'.2 hyU
    exact this.symm

  -- The transports are compatible: both equalities go between the same objects
  have h_dom_compat : h_eq_x.trans h_dom_U = h_dom_W := by
    apply Subsingleton.elim
  have h_cod_compat : h_eq_y.trans h_cod_U = h_cod_W := by
    apply Subsingleton.elim

  -- Let f_W and f_U be the simple versions
  let f_W := single_covered_map_simple X 𝒰 s γ W hW hxW hyW hW_range
  let f_U := single_covered_map_simple X 𝒰 s γ U hU hxU hyU (subset_trans hW_range hWU)

  -- By the simple version lemma:
  -- eqToHom h_eq_x.symm ≫ f_W ≫ eqToHom h_eq_y = f_U
  have h_simple : eqToHom h_eq_x.symm ≫ f_W ≫ eqToHom h_eq_y = f_U :=
    single_covered_map_simple_indep_of_le X 𝒰 s W U hW hU hWU γ hxW hyW hxU hyU hW_range
      (subset_trans hW_range hWU) h_eq_x h_eq_y

  -- Now unfold both sides of the goal in terms of the simple versions
  have h_goal_W : @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ W hW hW_range =
      eqToHom h_dom_W.symm ≫ f_W ≫ eqToHom h_cod_W := by
    rfl
  have h_goal_U : @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ U hU (subset_trans hW_range hWU) =
      eqToHom h_dom_U.symm ≫ f_U ≫ eqToHom h_cod_U := by
    rfl

  -- Rewrite the goal using these
  rw [h_goal_U, h_goal_W]

  -- Use the compatibility equations to rewrite h_dom_W and h_cod_W
  have h_dom_W' : h_dom_W = h_eq_x.trans h_dom_U := h_dom_compat.symm
  have h_cod_W' : h_cod_W = h_eq_y.trans h_cod_U := h_cod_compat.symm
  rw [h_dom_W', h_cod_W']

  -- Now we have:
  -- eqToDom (h_eq_x.trans h_dom_U).symm ≫ f_W ≫ eqToHom (h_eq_y.trans h_cod_U)
  -- = eqToHom h_dom_U.symm ≫ f_U ≫ eqToHom h_cod_U
  -- And we know: eqToHom h_eq_x.symm ≫ f_W ≫ eqToHom h_eq_y = f_U

  -- Use eqToHom_trans to break down the transports
  have h1 : eqToHom (h_eq_x.trans h_dom_U).symm = eqToHom h_dom_U.symm ≫ eqToHom h_eq_x.symm := by
    -- Both sides are isomorphisms between the same objects
    -- We can prove this by showing the equality of the underlying equalities
    have h_eq : (h_eq_x.trans h_dom_U).symm = h_dom_U.symm.trans h_eq_x.symm := by
      rfl
    rw [h_eq]
    rw [eqToHom_trans]
    <;> rfl
  have h2 : eqToHom (h_eq_y.trans h_cod_U) = eqToHom h_eq_y ≫ eqToHom h_cod_U := by
    rw [eqToHom_trans]
    <;> rfl

  -- Rewrite the right side of the goal using h1 and h2
  have h_goal : eqToHom (h_eq_x.trans h_dom_U).symm ≫ f_W ≫ eqToHom (h_eq_y.trans h_cod_U) =
      eqToHom h_dom_U.symm ≫ f_U ≫ eqToHom h_cod_U := by
    have h3 : eqToHom (h_eq_x.trans h_dom_U).symm ≫ f_W ≫ eqToHom (h_eq_y.trans h_cod_U) =
        (eqToHom h_dom_U.symm ≫ eqToHom h_eq_x.symm) ≫ f_W ≫ (eqToHom h_eq_y ≫ eqToHom h_cod_U) := by
      rw [h1, h2]
      <;> rfl
    rw [h3]
    have h4 : (eqToHom h_dom_U.symm ≫ eqToHom h_eq_x.symm) ≫ f_W ≫ (eqToHom h_eq_y ≫ eqToHom h_cod_U) =
        eqToHom h_dom_U.symm ≫ (eqToHom h_eq_x.symm ≫ f_W ≫ eqToHom h_eq_y) ≫ eqToHom h_cod_U := by
      simp [Category.assoc]
      <;> rfl
    rw [h4]
    rw [h_simple]
    <;> rfl

  exact h_goal.symm
/-- The result is independent of which U we choose (as long as γ's range is in U). -/
theorem single_covered_map_indep {x y : X} (γ : Path x y)
    (U V : Opens X) (hU : U ∈ 𝒰) (hV : V ∈ 𝒰)
    (hU' : Set.range γ ⊆ (U : Set X)) (hV' : Set.range γ ⊆ (V : Set X)) :
    @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ U hU hU' =
    @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ V hV hV' := by
  classical
  -- Let W = U ∩ V
  let s_finset : Finset (Opens X) := {U, V}
  have h_nonempty : s_finset.Nonempty := by
    exact Finset.nonempty_iff_ne_empty.mpr (by simp [s_finset])
  have h_all_in : ∀ W ∈ s_finset, W ∈ 𝒰 := by
    intro W hW
    have : W = U ∨ W = V := by simpa [s_finset] using hW
    rcases this with (rfl | rfl) <;> tauto
  let W : Opens X := s_finset.inf (fun U : Opens X => U)
  have hW_in : W ∈ 𝒰 := hfinite_intersections s_finset h_nonempty h_all_in
  have hW_eq : W = U ⊓ V := by
    have h : W = s_finset.inf id := by rfl
    rw [h]
    have h2 : ({U, V} : Finset (Opens X)).inf id = U ⊓ V := by
      classical
      simp [Finset.inf_insert]
      <;> rfl
    exact h2
  have hW_le_U : W ≤ U := Finset.inf_le (Finset.mem_insert_self U {V})
  have hW_le_V : W ≤ V := Finset.inf_le (by simp [s_finset])
  have hW_range : Set.range γ ⊆ (W : Set X) := by
    rw [hW_eq]
    intro z hz
    exact ⟨hU' hz, hV' hz⟩

  -- Now both U and V versions equal the W version
  have h1 : @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ U hU hU' =
      @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ W hW_in hW_range :=
    single_covered_map_indep_of_le X 𝒰 hcover hfinite_intersections s γ W U hW_in hU hW_le_U hW_range
  have h2 : @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ V hV hV' =
      @single_covered_map X _ 𝒰 hcover hfinite_intersections s x y γ W hW_in hW_range :=
    single_covered_map_indep_of_le X 𝒰 hcover hfinite_intersections s γ W V hW_in hV hW_le_V hW_range

  exact h1.trans h2.symm

/-- single_covered_map is independent of the choice of proof that the range is in U. -/
lemma single_covered_map_indep_of_h_range {x y : X} (γ : Path x y)
    (U : Opens X) (hU : U ∈ 𝒰)
    (h1 h2 : Set.range γ ⊆ (U : Set X)) :
    single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h1 =
    single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h2 := by
  congr
  <;> exact Subsingleton.elim _ _

/-- Congruence lemma for single_covered_map: if two paths have the same underlying
    function and their endpoints are equal, then their single_covered_map images
    are equal (after transporting along the endpoint equalities). -/
lemma single_covered_map_congr {x₁ y₁ x₂ y₂ : X}
    (γ₁ : Path x₁ y₁) (γ₂ : Path x₂ y₂)
    (hx : x₁ = x₂) (hy : y₁ = y₂)
    (hfun : ∀ t, γ₁ t = γ₂ t)
    (U : Opens X) (hU : U ∈ 𝒰)
    (h_range1 : Set.range γ₁ ⊆ (U : Set X))
    (h_range2 : Set.range γ₂ ⊆ (U : Set X)) :
    eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx).symm ≫
    single_covered_map X 𝒰 hcover hfinite_intersections s γ₁ U hU h_range1 ≫
    eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy) =
    single_covered_map X 𝒰 hcover hfinite_intersections s γ₂ U hU h_range2 := by
  subst hx
  subst hy
  -- Now x₁ = x₂ and y₁ = y₂ definitionally, so eqToHom terms become identities
  simp [eqToHom_refl, Category.id_comp, Category.comp_id]
  -- Now goal is: single_covered_map ... γ₁ ... = single_covered_map ... γ₂ ...
  have h_eq : γ₁ = γ₂ := by
    apply Path.ext
    funext t
    exact hfun t
  -- Substitute γ₁ = γ₂ everywhere
  cases h_eq
  -- Now both sides are single_covered_map ... γ₁ ... with different h_range proofs
  exact single_covered_map_indep_of_h_range X 𝒰 hcover hfinite_intersections s γ₁ U hU h_range1 h_range2

/-- If two paths are homotopic via a homotopy that stays entirely within U,
    then their single_covered_map images are equal. -/
lemma single_covered_map_homotopic {x y : X}
    (γ₁ γ₂ : Path x y)
    (U : Opens X) (hU : U ∈ 𝒰)
    (h_range1 : Set.range γ₁ ⊆ (U : Set X))
    (h_range2 : Set.range γ₂ ⊆ (U : Set X))
    (H : Path.Homotopy γ₁ γ₂)
    (hH : ∀ (p : I × I), H p ∈ (U : Set X)) :
    single_covered_map X 𝒰 hcover hfinite_intersections s γ₁ U hU h_range1 =
    single_covered_map X 𝒰 hcover hfinite_intersections s γ₂ U hU h_range2 := by
  classical
  let U_set : Set X := (U : Set X)

  -- Get that x and y are in U
  have hx : x ∈ U := by
    have h1' : γ₁ 0 ∈ Set.range γ₁ := Set.mem_range_self 0
    have h2' : γ₁ 0 = x := γ₁.source
    rw [h2'] at h1'
    exact h_range1 h1'
  have hy : y ∈ U := by
    have h1' : γ₁ 1 ∈ Set.range γ₁ := Set.mem_range_self 1
    have h2' : γ₁ 1 = y := γ₁.target
    rw [h2'] at h1'
    exact h_range1 h1'

  -- Define the lifted homotopy H' : I × I → U_set
  let H'_fun : I × I → U_set := fun p => ⟨H p, hH p⟩
  have H'_cont : Continuous H'_fun := by
    have h : Continuous (fun p : I × I => (H'_fun p : X)) := H.continuous
    exact Continuous.subtype_mk h hH

  -- Build the continuous map
  let H'_cm : C(I × I, U_set) := ⟨H'_fun, H'_cont⟩

  -- Get the lifted paths used in single_covered_map
  let γ₁_lift : Path (⟨x, hx⟩ : U_set) (⟨y, hy⟩ : U_set) :=
    (Path.lift_to_subtype γ₁ hx hy h_range1).choose
  let hγ₁_lift : ∀ (t : I), (γ₁_lift t : X) = γ₁ t :=
    (Path.lift_to_subtype γ₁ hx hy h_range1).choose_spec

  let γ₂_lift : Path (⟨x, hx⟩ : U_set) (⟨y, hy⟩ : U_set) :=
    (Path.lift_to_subtype γ₂ hx hy h_range2).choose
  let hγ₂_lift : ∀ (t : I), (γ₂_lift t : X) = γ₂ t :=
    (Path.lift_to_subtype γ₂ hx hy h_range2).choose_spec

  -- Now we build a Homotopy between the two lifted paths (as continuous maps)
  let H'_homotopy : ContinuousMap.Homotopy γ₁_lift.toContinuousMap γ₂_lift.toContinuousMap :=
    {
      toContinuousMap := H'_cm,
      map_zero_left := by
        intro s
        apply Subtype.ext
        simpa [H'_cm, H'_fun, hγ₁_lift] using H.map_zero_left s
      map_one_left := by
        intro s
        apply Subtype.ext
        simpa [H'_cm, H'_fun, hγ₂_lift] using H.map_one_left s
    }

  -- Now we build the HomotopyWith (HomotopyRel) with the prop' field
  let H'_rel : ContinuousMap.HomotopyRel γ₁_lift.toContinuousMap γ₂_lift.toContinuousMap {0, 1} :=
    {
      H'_homotopy with
      prop' := by
        intro t
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with (rfl | rfl)
        · -- x = 0
          apply Subtype.ext
          simpa [H'_homotopy, H'_cm, H'_fun, Path.Homotopy.source] using rfl
        · -- x = 1
          apply Subtype.ext
          simpa [H'_homotopy, H'_cm, H'_fun, Path.Homotopy.target] using rfl
    }

  -- This is exactly a Path.Homotopy
  let H' : Path.Homotopy γ₁_lift γ₂_lift := H'_rel

  -- Therefore the homotopy classes are equal
  have h_homotopic : Path.Homotopic γ₁_lift γ₂_lift := ⟨H'⟩
  have h_classes : Path.Homotopic.Quotient.mk γ₁_lift = Path.Homotopic.Quotient.mk γ₂_lift :=
    Path.Homotopic.Quotient.eq.mpr h_homotopic

  -- Now we just need to unwrap the definition of single_covered_map
  dsimp only [single_covered_map]

  -- The structure is:
  -- eqToHom h_dom.symm ≫ (eqToHom h_eq1.symm ≫ (s.ι.app ⟨U, hU⟩).map γ_class ≫ eqToHom h_eq2) ≫ eqToHom h_cod
  -- We need to rewrite using h_classes in the middle
  simp only [Category.assoc]
  exact congr_arg (fun c => eqToHom _ ≫ eqToHom _ ≫ (s.ι.app ⟨U, hU⟩).map c ≫ eqToHom _ ≫ eqToHom _) h_classes

end

end
