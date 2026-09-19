module

public import Mathlib
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CanonicalCocone
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.UniversalProperty
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.PathHelpers
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.TransLift
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.EqToHomHelpers

@[expose] public section

open TopologicalSpace CategoryTheory Limits

open scoped unitInterval

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

/-- Helper: the range of a concatenated path is the union of the ranges. -/
lemma range_trans_subset_simple {X : Type*} [TopologicalSpace X] {x y z : X}
    (γ₁ : Path x y) (γ₂ : Path y z) {U : Set X}
    (h₁ : Set.range γ₁ ⊆ U) (h₂ : Set.range γ₂ ⊆ U) :
    Set.range (γ₁.trans γ₂) ⊆ U := by
  have h : Set.range (γ₁.trans γ₂) = Set.range γ₁ ∪ Set.range γ₂ :=
    Path.trans_range γ₁ γ₂
  rw [h]
  exact Set.union_subset h₁ h₂

/-- Simpler version of single_covered_map that doesn't transport to desc_functor_obj.
    The domain and codomain are objects obtained from specific opens. -/
def single_covered_map_simple {x y : X} (γ : Path x y)
    (U : Opens X) (hU : U ∈ 𝒰) (hx : x ∈ U) (hy : y ∈ U)
    (h : Set.range γ ⊆ (U : Set X)) :
    obj_at X 𝒰 s x U hU hx ⟶ obj_at X 𝒰 s y U hU hy := by
  let U_set : Set X := (U : Set X)
  let γ_lift : Path (⟨x, hx⟩ : U_set) (⟨y, hy⟩ : U_set) :=
    (Path.lift_to_subtype γ hx hy h).choose
  let γ_class : (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
                (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) :=
    Path.Homotopic.Quotient.mk γ_lift
  let f : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
          (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) :=
    (s.ι.app ⟨U, hU⟩).map γ_class
  have h_eq1 : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) =
      obj_at X 𝒰 s x U hU hx := by rfl
  have h_eq2 : (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) =
      obj_at X 𝒰 s y U hU hy := by rfl
  exact eqToHom h_eq1.symm ≫ f ≫ eqToHom h_eq2

/-- Helper: any two lifts of the same path to a subtype are equal. -/
lemma lift_unique_simple {X : Type*} [TopologicalSpace X] {U : Set X} {x y : X}
    (γ : Path x y) (hx : x ∈ U) (hy : y ∈ U) (h : Set.range γ ⊆ U)
    (γ₁ γ₂ : Path (⟨x, hx⟩ : U) (⟨y, hy⟩ : U))
    (h₁ : ∀ (t : unitInterval), (γ₁ t : X) = γ t)
    (h₂ : ∀ (t : unitInterval), (γ₂ t : X) = γ t) :
    γ₁ = γ₂ := by
  apply Path.ext
  funext t
  apply Subtype.ext
  exact (h₁ t).trans (h₂ t).symm

/-- The split property for the simple version: composing the maps for two segments
    equals the map for the concatenated path. -/
theorem single_covered_split_eq_simple {x y z : X}
    (U : Opens X) (hU : U ∈ 𝒰)
    (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U)
    (γ₁ : Path x y) (h₁ : Set.range γ₁ ⊆ (U : Set X))
    (γ₂ : Path y z) (h₂ : Set.range γ₂ ⊆ (U : Set X)) :
    single_covered_map_simple X 𝒰 s γ₁ U hU hx hy h₁ ≫
    single_covered_map_simple X 𝒰 s γ₂ U hU hy hz h₂ =
    single_covered_map_simple X 𝒰 s (γ₁.trans γ₂) U hU hx hz
      (range_trans_subset_simple γ₁ γ₂ h₁ h₂) := by
  dsimp only [single_covered_map_simple]
  let U_set : Set X := (U : Set X)

  -- Get the lifts
  let γ₁_lift : Path (⟨x, hx⟩ : U_set) (⟨y, hy⟩ : U_set) :=
    (Path.lift_to_subtype γ₁ hx hy h₁).choose
  let hγ₁_lift : ∀ (t : unitInterval), (γ₁_lift t : X) = γ₁ t :=
    (Path.lift_to_subtype γ₁ hx hy h₁).choose_spec

  let γ₂_lift : Path (⟨y, hy⟩ : U_set) (⟨z, hz⟩ : U_set) :=
    (Path.lift_to_subtype γ₂ hy hz h₂).choose
  let hγ₂_lift : ∀ (t : unitInterval), (γ₂_lift t : X) = γ₂ t :=
    (Path.lift_to_subtype γ₂ hy hz h₂).choose_spec

  let h_both_range : Set.range (γ₁.trans γ₂) ⊆ (U : Set X) :=
    range_trans_subset_simple γ₁ γ₂ h₁ h₂

  let γ_both_lift : Path (⟨x, hx⟩ : U_set) (⟨z, hz⟩ : U_set) :=
    (Path.lift_to_subtype (γ₁.trans γ₂) hx hz h_both_range).choose
  let hγ_both_lift : ∀ (t : unitInterval), (γ_both_lift t : X) = (γ₁.trans γ₂) t :=
    (Path.lift_to_subtype (γ₁.trans γ₂) hx hz h_both_range).choose_spec

  -- The concatenation of the lifts is also a lift of the concatenated path
  -- This is a key fact we need: map of trans equals trans of maps
  let γ_concat_lift : Path (⟨x, hx⟩ : U_set) (⟨z, hz⟩ : U_set) :=
    γ₁_lift.trans γ₂_lift

  -- Prove that γ_concat_lift is a lift of γ₁.trans γ₂
  have hγ_concat_lift : ∀ (t : unitInterval), (γ_concat_lift t : X) = (γ₁.trans γ₂) t :=
    trans_lift_commutes hx hy hz γ₁ γ₂ γ₁_lift γ₂_lift hγ₁_lift hγ₂_lift

  -- Therefore the two lifts are equal
  have h_lifts_eq : γ_both_lift = γ_concat_lift :=
    lift_unique_simple (γ₁.trans γ₂) hx hz h_both_range γ_both_lift γ_concat_lift hγ_both_lift hγ_concat_lift

  -- Get the homotopy classes
  let γ₁_class : (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
                (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) :=
    Path.Homotopic.Quotient.mk γ₁_lift
  let γ₂_class : (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) ⟶
                (FundamentalGroupoid.mk (⟨z, hz⟩ : U_set)) :=
    Path.Homotopic.Quotient.mk γ₂_lift
  let γ_both_class : (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
                    (FundamentalGroupoid.mk (⟨z, hz⟩ : U_set)) :=
    Path.Homotopic.Quotient.mk γ_both_lift

  -- The class of the concatenation is the composition of the classes
  have h_class_comp : γ₁_class ≫ γ₂_class = γ_both_class := by
    have h : γ₁_class ≫ γ₂_class = Path.Homotopic.Quotient.mk (γ₁_lift.trans γ₂_lift) := by
      exact FundamentalGroupoid.comp_eq _ _ _ _ _
    have h' : Path.Homotopic.Quotient.mk (γ₁_lift.trans γ₂_lift) = Path.Homotopic.Quotient.mk γ_both_lift := by
      rw [show γ₁_lift.trans γ₂_lift = γ_both_lift from h_lifts_eq.symm]
    rw [h, h']
    <;> rfl

  -- Apply the cocone functor
  let F := s.ι.app ⟨U, hU⟩
  let f₁_core : F.obj (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
              F.obj (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) :=
    F.map γ₁_class
  let f₂_core : F.obj (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)) ⟶
              F.obj (FundamentalGroupoid.mk (⟨z, hz⟩ : U_set)) :=
    F.map γ₂_class
  let f_both_core : F.obj (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)) ⟶
                  F.obj (FundamentalGroupoid.mk (⟨z, hz⟩ : U_set)) :=
    F.map γ_both_class

  have h_map_comp : f₁_core ≫ f₂_core = f_both_core := by
    have h : F.map (γ₁_class ≫ γ₂_class) = F.map γ₁_class ≫ F.map γ₂_class := by
      exact F.map_comp γ₁_class γ₂_class
    have h' : F.map (γ₁_class ≫ γ₂_class) = F.map γ_both_class :=
      congr_arg (fun f : _ ⟶ _ => F.map f) h_class_comp
    have h'' : F.map γ₁_class ≫ F.map γ₂_class = F.map γ_both_class := by
      rw [←h, h']
    exact h''

  -- Now the eqToHom transports cancel out nicely
  let obj_x := (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨x, hx⟩ : U_set))
  let obj_y := (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨y, hy⟩ : U_set))
  let obj_z := (s.ι.app ⟨U, hU⟩).obj (FundamentalGroupoid.mk (⟨z, hz⟩ : U_set))
  let h_eq_x : obj_x = obj_at X 𝒰 s x U hU hx := by rfl
  let h_eq_y : obj_y = obj_at X 𝒰 s y U hU hy := by rfl
  let h_eq_z : obj_z = obj_at X 𝒰 s z U hU hz := by rfl
  let e_x : obj_at X 𝒰 s x U hU hx ⟶ obj_x := eqToHom h_eq_x.symm
  let e_y : obj_y ⟶ obj_at X 𝒰 s y U hU hy := eqToHom h_eq_y
  let e_y' : obj_at X 𝒰 s y U hU hy ⟶ obj_y := eqToHom h_eq_y.symm
  let e_z : obj_z ⟶ obj_at X 𝒰 s z U hU hz := eqToHom h_eq_z

  -- Apply the general eqToHom cancellation lemma
  have h_main1 : (eqToHom h_eq_x.symm ≫ f₁_core ≫ eqToHom h_eq_y) ≫
      (eqToHom h_eq_y.symm ≫ f₂_core ≫ eqToHom h_eq_z) =
      eqToHom h_eq_x.symm ≫ (f₁_core ≫ f₂_core) ≫ eqToHom h_eq_z :=
    eqToHom_comp_cancel h_eq_x h_eq_y h_eq_z f₁_core f₂_core

  -- Now use h_map_comp to replace f₁_core ≫ f₂_core with f_both_core
  have h_main2 : eqToHom h_eq_x.symm ≫ (f₁_core ≫ f₂_core) ≫ eqToHom h_eq_z =
      eqToHom h_eq_x.symm ≫ f_both_core ≫ eqToHom h_eq_z := by
    have h : eqToHom h_eq_x.symm ≫ (f₁_core ≫ f₂_core) ≫ eqToHom h_eq_z =
        eqToHom h_eq_x.symm ≫ (f₁_core ≫ f₂_core) ≫ eqToHom h_eq_z := rfl
    rw [h_map_comp]
    <;> rfl

  exact h_main1.trans h_main2

/-- Helper: if two functors are equal, then their map of a morphism is equal
    when transported along the appropriate eqToHom's. -/
lemma functor_eq_map_eq {C D : Type u} [Category C] [Category D]
    {F G : C ⥤ D} (h : F = G) {X Y : C} (f : X ⟶ Y) :
    F.map f = eqToHom (congr_arg (fun (K : C ⥤ D) => K.obj X) h) ≫
      G.map f ≫ eqToHom (congr_arg (fun (K : C ⥤ D) => K.obj Y) h).symm := by
  cases h
  <;> simp [eqToHom_refl, Category.comp_id, Category.id_comp]
  <;> rfl

/-- Independence of the simple version with respect to inclusion of opens.
    If W ≤ U, the map through W (transported to U's obj_at type) equals the map through U. -/
theorem single_covered_map_simple_indep_of_le {x y : X}
    (W U : Opens X) (hW : W ∈ 𝒰) (hU : U ∈ 𝒰) (hWU : W ≤ U)
    (γ : Path x y) (hxW : x ∈ W) (hyW : y ∈ W)
    (hxU : x ∈ U) (hyU : y ∈ U)
    (hW_range : Set.range γ ⊆ (W : Set X))
    (hU_range : Set.range γ ⊆ (U : Set X))
    (h_eq_x : obj_at X 𝒰 s x W hW hxW = obj_at X 𝒰 s x U hU hxU)
    (h_eq_y : obj_at X 𝒰 s y W hW hyW = obj_at X 𝒰 s y U hU hyU) :
    eqToHom h_eq_x.symm ≫ single_covered_map_simple X 𝒰 s γ W hW hxW hyW hW_range ≫ eqToHom h_eq_y =
    single_covered_map_simple X 𝒰 s γ U hU hxU hyU hU_range := by
  dsimp only [single_covered_map_simple]

  let W_set : Set X := (W : Set X)
  let U_set : Set X := (U : Set X)

  -- Get the lifts
  let γ_W_lift : Path (⟨x, hxW⟩ : W_set) (⟨y, hyW⟩ : W_set) :=
    (Path.lift_to_subtype γ hxW hyW hW_range).choose
  let hγ_W_lift : ∀ (t : unitInterval), (γ_W_lift t : X) = γ t :=
    (Path.lift_to_subtype γ hxW hyW hW_range).choose_spec

  let γ_U_lift : Path (⟨x, hxU⟩ : U_set) (⟨y, hyU⟩ : U_set) :=
    (Path.lift_to_subtype γ hxU hyU hU_range).choose
  let hγ_U_lift : ∀ (t : unitInterval), (γ_U_lift t : X) = γ t :=
    (Path.lift_to_subtype γ hxU hyU hU_range).choose_spec

  -- The inclusion map from W to U induces a map on paths
  let incl_WU : W_set → U_set := fun z => ⟨(z : X), hWU z.property⟩
  have hi_cont : Continuous incl_WU := by apply continuous_inclusion hWU

  -- incl_WU ∘ γ_W_lift is a lift of γ to U
  let γ_U_from_W : Path (⟨x, hxU⟩ : U_set) (⟨y, hyU⟩ : U_set) :=
    γ_W_lift.map hi_cont

  have hγ_U_from_W : ∀ (t : unitInterval), (γ_U_from_W t : X) = γ t := by
    intro t
    have h1 : (γ_U_from_W t : X) = (incl_WU (γ_W_lift t) : X) := by rfl
    rw [h1]
    have h2 : (incl_WU (γ_W_lift t) : X) = (γ_W_lift t : X) := by rfl
    rw [h2]
    exact hγ_W_lift t

  -- Therefore γ_U_from_W = γ_U_lift (by uniqueness of lifts)
  have h_lifts_eq : γ_U_from_W = γ_U_lift :=
    lift_unique_simple γ hxU hyU hU_range γ_U_from_W γ_U_lift hγ_U_from_W hγ_U_lift

  -- Get the homotopy classes
  let γ_W_class : (FundamentalGroupoid.mk (⟨x, hxW⟩ : W_set)) ⟶
                (FundamentalGroupoid.mk (⟨y, hyW⟩ : W_set)) :=
    Path.Homotopic.Quotient.mk γ_W_lift
  let γ_U_class : (FundamentalGroupoid.mk (⟨x, hxU⟩ : U_set)) ⟶
                (FundamentalGroupoid.mk (⟨y, hyU⟩ : U_set)) :=
    Path.Homotopic.Quotient.mk γ_U_lift

  -- Cocone naturality
  let D := ((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
    Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor
  let i : (⟨W, hW⟩ : {U // U ∈ 𝒰}) ⟶ ⟨U, hU⟩ := homOfLE hWU
  have h_nat : D.map i ≫ s.ι.app ⟨U, hU⟩ = s.ι.app ⟨W, hW⟩ := s.ι.naturality i

  -- The induced functor maps γ_W_class to γ_U_class
  have h_map_class : (D.map i).map γ_W_class = γ_U_class := by
    have h1 : (D.map i).map γ_W_class = Path.Homotopic.Quotient.mk γ_U_from_W := by rfl
    rw [h1, h_lifts_eq] <;> rfl

  let F_W := s.ι.app ⟨W, hW⟩
  let F_U := s.ι.app ⟨U, hU⟩

  let f_W_core : F_W.obj (FundamentalGroupoid.mk (⟨x, hxW⟩ : W_set)) ⟶
              F_W.obj (FundamentalGroupoid.mk (⟨y, hyW⟩ : W_set)) :=
    F_W.map γ_W_class
  let f_U_core : F_U.obj (FundamentalGroupoid.mk (⟨x, hxU⟩ : U_set)) ⟶
              F_U.obj (FundamentalGroupoid.mk (⟨y, hyU⟩ : U_set)) :=
    F_U.map γ_U_class

  let h_eq1_W : F_W.obj (FundamentalGroupoid.mk (⟨x, hxW⟩ : W_set)) =
      obj_at X 𝒰 s x W hW hxW := by rfl
  let h_eq2_W : F_W.obj (FundamentalGroupoid.mk (⟨y, hyW⟩ : W_set)) =
      obj_at X 𝒰 s y W hW hyW := by rfl
  let h_eq1_U : F_U.obj (FundamentalGroupoid.mk (⟨x, hxU⟩ : U_set)) =
      obj_at X 𝒰 s x U hU hxU := by rfl
  let h_eq2_U : F_U.obj (FundamentalGroupoid.mk (⟨y, hyU⟩ : U_set)) =
      obj_at X 𝒰 s y U hU hyU := by rfl

  -- Key step: use naturality to relate f_W_core and f_U_core
  have h_core : f_W_core =
      eqToHom (congr_arg (fun (K : _ ⥤ _) => K.obj (FundamentalGroupoid.mk (⟨x, hxW⟩ : W_set))) h_nat.symm) ≫
      F_U.map ((D.map i).map γ_W_class) ≫
      eqToHom (congr_arg (fun (K : _ ⥤ _) => K.obj (FundamentalGroupoid.mk (⟨y, hyW⟩ : W_set))) h_nat.symm).symm :=
    functor_eq_map_eq h_nat.symm γ_W_class

  -- Substitute h_core and h_map_class into the goal
  have h_main_goal : eqToHom h_eq_x.symm ≫ (eqToHom h_eq1_W.symm ≫ f_W_core ≫ eqToHom h_eq2_W) ≫ eqToHom h_eq_y =
      eqToHom h_eq1_U.symm ≫ f_U_core ≫ eqToHom h_eq2_U := by
    -- First, rewrite f_W_core
    have h1 : eqToHom h_eq_x.symm ≫ (eqToHom h_eq1_W.symm ≫ f_W_core ≫ eqToHom h_eq2_W) ≫ eqToHom h_eq_y =
        eqToHom h_eq_x.symm ≫ (eqToHom h_eq1_W.symm ≫
          (eqToHom (congr_arg (fun (K : _ ⥤ _) => K.obj (FundamentalGroupoid.mk (⟨x, hxW⟩ : W_set))) h_nat.symm) ≫
           F_U.map ((D.map i).map γ_W_class) ≫
           eqToHom (congr_arg (fun (K : _ ⥤ _) => K.obj (FundamentalGroupoid.mk (⟨y, hyW⟩ : W_set))) h_nat.symm).symm) ≫
          eqToHom h_eq2_W) ≫ eqToHom h_eq_y := by
      rw [h_core]
      <;> rfl
    rw [h1]

    -- Then rewrite h_map_class
    have h2 : eqToHom h_eq_x.symm ≫ (eqToHom h_eq1_W.symm ≫
          (eqToHom (congr_arg (fun (K : _ ⥤ _) => K.obj (FundamentalGroupoid.mk (⟨x, hxW⟩ : W_set))) h_nat.symm) ≫
           F_U.map ((D.map i).map γ_W_class) ≫
           eqToHom (congr_arg (fun (K : _ ⥤ _) => K.obj (FundamentalGroupoid.mk (⟨y, hyW⟩ : W_set))) h_nat.symm).symm) ≫
          eqToHom h_eq2_W) ≫ eqToHom h_eq_y =
        eqToHom h_eq_x.symm ≫ (eqToHom h_eq1_W.symm ≫
          (eqToHom (congr_arg (fun (K : _ ⥤ _) => K.obj (FundamentalGroupoid.mk (⟨x, hxW⟩ : W_set))) h_nat.symm) ≫
           F_U.map γ_U_class ≫
           eqToHom (congr_arg (fun (K : _ ⥤ _) => K.obj (FundamentalGroupoid.mk (⟨y, hyW⟩ : W_set))) h_nat.symm).symm) ≫
          eqToHom h_eq2_W) ≫ eqToHom h_eq_y := by
      rw [h_map_class]
      <;> rfl
    rw [h2]

    -- All equality proofs between the same objects are equal
    have h_irrel : ∀ {A B : s.pt} (h1 h2 : A = B), eqToHom h1 = eqToHom h2 := by
      intro A B h1 h2
      congr <;> exact Subsingleton.elim _ _

    -- Now simplify using associativity and proof irrelevance
    simp [Category.assoc, eqToHom_trans]
    <;>
    (try { congr <;> exact Subsingleton.elim _ _ })
    <;>
    aesop

  exact h_main_goal

/-- single_covered_map_simple is independent of the choice of proof that the range is in U. -/
lemma single_covered_map_simple_indep_of_h_range {x y : X} (γ : Path x y)
    (U : Opens X) (hU : U ∈ 𝒰) (hx : x ∈ U) (hy : y ∈ U)
    (h1 h2 : Set.range γ ⊆ (U : Set X)) :
    single_covered_map_simple X 𝒰 s γ U hU hx hy h1 =
    single_covered_map_simple X 𝒰 s γ U hU hx hy h2 := by
  congr
  <;> exact Subsingleton.elim _ _

end

end
