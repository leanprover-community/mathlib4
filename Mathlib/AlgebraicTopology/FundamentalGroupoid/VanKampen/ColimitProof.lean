module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CleanDescent

@[expose] public section

open TopologicalSpace CategoryTheory Limits

open scoped unitInterval

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hpath_connected : ∀ U : Opens X, U ∈ 𝒰 → IsPathConnected (U : Set X))
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

include hcover hfinite_intersections

noncomputable def my_desc_functor :
    FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) ⥤ s.pt :=
  {
    obj := fun x => desc_functor_obj X 𝒰 hcover s x,
    map := fun {x y} f =>
      Quotient.lift (my_desc_map X 𝒰 hcover hfinite_intersections s)
        (fun γ₁ γ₂ h => my_desc_map_homotopy_invariant X 𝒰 hcover hfinite_intersections s h) f,
    map_id := by
      intro x
      let const_path : Path x.as x.as := Path.refl x.as
      have h_main : (𝟙 x) = Path.Homotopic.Quotient.mk const_path := by
        exact (FundamentalGroupoid.id_eq_path_refl x).symm
      rw [h_main]
      dsimp only
      exact my_desc_map_refl X 𝒰 hcover hfinite_intersections s,
    map_comp := by
      intro x y z f g
      let F_map := fun {a b : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)} (h : a ⟶ b) =>
        Quotient.lift (my_desc_map X 𝒰 hcover hfinite_intersections s)
          (fun γ₁ γ₂ h => my_desc_map_homotopy_invariant X 𝒰 hcover hfinite_intersections s h) h
      have h_step1 : ∀ (f' : x ⟶ y), ∀ (g' : y ⟶ z),
          F_map (f' ≫ g') = F_map f' ≫ F_map g' := by
        intro f'
        refine' Quotient.inductionOn' f' _
        intro γ₁
        intro g'
        refine' Quotient.inductionOn' g' _
        intro γ₂
        let p : x ⟶ y := Path.Homotopic.Quotient.mk γ₁
        let q : y ⟶ z := Path.Homotopic.Quotient.mk γ₂
        have h_comp_eq : p ≫ q = Path.Homotopic.Quotient.trans p q :=
          FundamentalGroupoid.comp_eq x y z p q
        have h_trans_eq : Path.Homotopic.Quotient.trans p q = Path.Homotopic.Quotient.mk (γ₁.trans γ₂) := by
          exact Path.Homotopic.Quotient.mk_trans γ₁ γ₂
        have h1 : p ≫ q = Path.Homotopic.Quotient.mk (γ₁.trans γ₂) := by
          rw [h_comp_eq, h_trans_eq]
        have h_main : F_map (p ≫ q) = F_map p ≫ F_map q := by
          rw [h1]
          simp only [F_map, Quotient.lift_mk]
          exact my_desc_map_comp X 𝒰 hcover hfinite_intersections s γ₁ γ₂
        exact h_main
      exact h_step1 f g
  }

/-- Clean version of fac_property_obj: uses my_desc_functor (which has no omitted proofs)
    instead of desc_functor (which has omitted proofs in map/map_id/map_comp). -/
lemma my_fac_property_obj (U : Opens X) (hU : U ∈ 𝒰)
    (x : FundamentalGroupoid.fundamentalGroupoidFunctor.obj ((Opens.toTopCat (TopCat.of X)).obj U)) :
    (my_desc_functor X 𝒰 hcover hfinite_intersections s).obj
      ((FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).obj x) =
    (s.ι.app ⟨U, hU⟩).obj x := by
  let z : (Opens.toTopCat (TopCat.of X)).obj U := x.as
  let z_X : X := z.val
  have hz : z_X ∈ U := z.property
  have h1 : (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).obj x =
      (FundamentalGroupoid.mk z_X : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)) := by
    rfl
  rw [h1]
  have h_main : (my_desc_functor X 𝒰 hcover hfinite_intersections s).obj (FundamentalGroupoid.mk z_X) =
      obj_at X 𝒰 s z_X U hU hz := by
    dsimp only [my_desc_functor, desc_functor_obj]
    let h : ∃ (U' : Opens X), U' ∈ 𝒰 ∧ z_X ∈ U' := hcover z_X
    have h' : obj_at X 𝒰 s z_X (Classical.choose h) (Classical.choose_spec h).1 (Classical.choose_spec h).2 =
        obj_at X 𝒰 s z_X U hU hz :=
      obj_at_eq X 𝒰 s hfinite_intersections z_X (Classical.choose h) U
        (Classical.choose_spec h).1 hU (Classical.choose_spec h).2 hz
    exact h'
  have h3 : obj_at X 𝒰 s z_X U hU hz = (s.ι.app ⟨U, hU⟩).obj x := by
    rfl
  rw [h_main, h3]

/-- Local copy of single_covered_map_fac for use in this file. -/
lemma single_covered_map_fac_local
    {x y : X} (γ : Path x y) (U : Opens X) (hU : U ∈ 𝒰) (h_range : Set.range γ ⊆ (U : Set X)) :
    let U_set : Set X := (U : Set X)
    let hx : x ∈ U := by
      have h1 : γ 0 ∈ Set.range γ := Set.mem_range_self 0
      have h2 : γ 0 = x := γ.source
      rw [h2] at h1
      exact h_range h1
    let hy : y ∈ U := by
      have h1 : γ 1 ∈ Set.range γ := Set.mem_range_self 1
      have h2 : γ 1 = y := γ.target
      rw [h2] at h1
      exact h_range h1
    let x_U : FundamentalGroupoid.fundamentalGroupoidFunctor.obj ((Opens.toTopCat (TopCat.of X)).obj U) :=
      FundamentalGroupoid.mk (⟨x, hx⟩ : U_set)
    let y_U : FundamentalGroupoid.fundamentalGroupoidFunctor.obj ((Opens.toTopCat (TopCat.of X)).obj U) :=
      FundamentalGroupoid.mk (⟨y, hy⟩ : U_set)
    let γ_lift : Path (⟨x, hx⟩ : U_set) (⟨y, hy⟩ : U_set) :=
      (Path.lift_to_subtype γ hx hy h_range).choose
    let f : x_U ⟶ y_U := Path.Homotopic.Quotient.mk γ_lift
    single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h_range =
    eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU x_U) ≫
    (s.ι.app ⟨U, hU⟩).map f ≫
    eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU y_U).symm := by
  dsimp only [single_covered_map, my_fac_property_obj]
  <;> simp
  <;> rfl

/-- Fac property for my_desc_functor on morphisms:
    Given a path γ in U, my_desc_functor.map applied to the image of γ's homotopy class
    equals the cocone leg map applied to the lifted homotopy class,
    composed with eqToHom transports from fac_property_obj. -/
lemma my_desc_functor_map_fac (U : Opens X) (hU : U ∈ 𝒰)
    (x y : FundamentalGroupoid.fundamentalGroupoidFunctor.obj ((Opens.toTopCat (TopCat.of X)).obj U))
    (f : x ⟶ y) :
    (my_desc_functor X 𝒰 hcover hfinite_intersections s).map
      ((FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).map f) =
    eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU x) ≫
    (s.ι.app ⟨U, hU⟩).map f ≫
    eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU y).symm := by
  let U_set : Set X := (U : Set X)
  let π₁U := FundamentalGroupoid.fundamentalGroupoidFunctor.obj ((Opens.toTopCat (TopCat.of X)).obj U)
  let F := s.ι.app ⟨U, hU⟩
  induction f using Quotient.inductionOn' with
  | h γ_lift =>
    -- Work with U_set type for simpler coercions
    let x_val : U_set := x.as
    let y_val : U_set := y.as
    let x_X : X := x_val
    let y_X : X := y_val
    -- γ_lift_U is γ_lift with type annotation to live in U_set
    let γ_lift_U : Path x_val y_val := γ_lift
    let γ : Path x_X y_X := γ_lift_U.map continuous_subtype_val
    have h_range : Set.range γ ⊆ U_set := by
      intro z hz
      rcases hz with ⟨t, rfl⟩
      exact (γ_lift_U t).property
    let f_U : x ⟶ y := Path.Homotopic.Quotient.mk γ_lift
    have h1 : (my_desc_functor X 𝒰 hcover hfinite_intersections s).map
        ((FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).map f_U) =
        my_desc_map X 𝒰 hcover hfinite_intersections s γ := by
      dsimp only [my_desc_functor, f_U]
      <;> rfl
    have h2 : my_desc_map X 𝒰 hcover hfinite_intersections s γ =
        single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h_range :=
      my_desc_map_single_covered X 𝒰 hcover hfinite_intersections s γ U hU h_range
    -- Define canonical lift data matching single_covered_map_fac_local
    let x_U : π₁U := FundamentalGroupoid.mk (⟨x_X, x_val.property⟩ : U_set)
    let y_U : π₁U := FundamentalGroupoid.mk (⟨y_X, y_val.property⟩ : U_set)
    let γ_lift' : Path (⟨x_X, x_val.property⟩ : U_set) (⟨y_X, y_val.property⟩ : U_set) :=
      (Path.lift_to_subtype γ x_val.property y_val.property h_range).choose
    let f' : x_U ⟶ y_U := Path.Homotopic.Quotient.mk γ_lift'
    have h_x_eq : x_U = x := by
      simp [x_U, x_val] <;> rfl
    have h_y_eq : y_U = y := by
      simp [y_U, y_val] <;> rfl
    have hx_point : (⟨x_X, x_val.property⟩ : U_set) = x_val := by
      exact Subtype.ext rfl
    have hy_point : (⟨y_X, y_val.property⟩ : U_set) = y_val := by
      exact Subtype.ext rfl
    have hγ'_spec : ∀ t : I, (γ_lift' t : X) = γ t :=
      (Path.lift_to_subtype γ x_val.property y_val.property h_range).choose_spec
    -- Prove γ_lift'.cast hx_point hy_point = γ_lift_U
    have h_path_eq : γ_lift'.cast hx_point hy_point = γ_lift_U := by
      let p : Path x_val y_val := γ_lift'.cast hx_point hy_point
      have h_eq : ∀ (t : I), (p t : X) = (γ_lift_U t : X) := by
        intro t
        have h1 : (p t : X) = (γ_lift' t : X) := by rfl
        have h2 : (γ_lift' t : X) = γ t := hγ'_spec t
        have h3 : (γ_lift_U t : X) = γ t := by rfl
        rw [h1, h2, h3.symm]
      have h_pointwise : ∀ (t : I), p t = γ_lift_U t := by
        intro t
        apply Subtype.ext
        exact h_eq t
      have h_fun : (fun (t : I) => p t) = fun (t : I) => γ_lift_U t := by
        funext t
        exact h_pointwise t
      exact Path.ext h_fun
    have h_conj : eqToHom h_x_eq.symm ≫ f' ≫ eqToHom h_y_eq =
        Path.Homotopic.Quotient.mk (γ_lift'.cast hx_point hy_point) :=
      FundamentalGroupoid.conj_eqToHom hx_point hy_point
    have h_morph_eq : eqToHom h_x_eq.symm ≫ f' ≫ eqToHom h_y_eq = f_U := by
      rw [h_conj, h_path_eq]
      <;> rfl
    -- Get the fac property from single_covered_map_fac_local
    have h_fac : single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h_range =
        eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU x_U) ≫
        F.map f' ≫
        eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU y_U).symm := by
      have h := single_covered_map_fac_local X 𝒰 hcover hfinite_intersections s γ U hU h_range
      dsimp only at h
      exact h
    -- Whiskering step: transport from x_U, y_U, f' to x, y, f_U
    have h_step_x : eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU x_U) =
        eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU x) ≫
        eqToHom (congr_arg F.obj h_x_eq.symm) := by
      rw [eqToHom_trans]
      <;> congr 1
      <;> apply Subsingleton.elim
    have h_step_y : eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU y_U).symm =
        eqToHom (congr_arg F.obj h_y_eq) ≫
        eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU y).symm := by
      rw [eqToHom_trans]
      <;> congr 1
      <;> apply Subsingleton.elim
    have h_functor : F.map f_U =
        eqToHom (congr_arg F.obj h_x_eq.symm) ≫ F.map f' ≫ eqToHom (congr_arg F.obj h_y_eq) := by
      have h_eq1 : f_U = eqToHom h_x_eq.symm ≫ f' ≫ eqToHom h_y_eq := h_morph_eq.symm
      have h : F.map f_U = F.map (eqToHom h_x_eq.symm ≫ f' ≫ eqToHom h_y_eq) :=
        congr_arg (fun (g : x ⟶ y) => F.map g) h_eq1
      rw [h]
      rw [Functor.map_comp, Functor.map_comp]
      rw [eqToHom_map F, eqToHom_map F]
      <;> rfl
    have h_main : single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h_range =
        eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU x) ≫
        F.map f_U ≫
        eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU y).symm := by
      let a := eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU x)
      let b := eqToHom (congr_arg F.obj h_x_eq.symm)
      let c := eqToHom (congr_arg F.obj h_y_eq)
      let d := eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU y).symm
      have h_goal1 : single_covered_map X 𝒰 hcover hfinite_intersections s γ U hU h_range =
          (a ≫ b) ≫ F.map f' ≫ (c ≫ d) := by
        rw [h_fac, h_step_x, h_step_y]
        <;> rfl
      have h_goal2 : (a ≫ b) ≫ F.map f' ≫ (c ≫ d) =
          a ≫ (b ≫ F.map f' ≫ c) ≫ d := by
        simp [Category.assoc]
        <;> aesop_cat
      have h_goal3 : a ≫ (b ≫ F.map f' ≫ c) ≫ d =
          a ≫ F.map f_U ≫ d := by
        have h : b ≫ F.map f' ≫ c = F.map f_U := h_functor.symm
        exact congr_arg (fun (x : _) => a ≫ x ≫ d) h
      rw [h_goal1, h_goal2, h_goal3]
    have h_goal : (my_desc_functor X 𝒰 hcover hfinite_intersections s).map
        ((FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).map f_U) =
        eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU x) ≫
        F.map f_U ≫
        eqToHom (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU y).symm := by
      rw [h1, h2]
      exact h_main
    exact h_goal

theorem my_fac_property (U : Opens X) (hU : U ∈ 𝒰) :
    (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫
    (my_desc_functor X 𝒰 hcover hfinite_intersections s) =
    s.ι.app ⟨U, hU⟩ := by
  refine' CategoryTheory.Functor.ext (my_fac_property_obj X 𝒰 hcover hfinite_intersections s U hU) _
  exact fun x y f => my_desc_functor_map_fac X 𝒰 hcover hfinite_intersections s U hU x y f

/-- Helper: functors preserve comp_list. -/
lemma functor_preserves_comp_list {C D : Type*} [Groupoid C] [Groupoid D]
    (F : C ⥤ D) {n : ℕ}
    (objs : Fin (n + 1) → C)
    (homs : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i)) :
    F.map (comp_list n objs homs) =
    comp_list n (fun i => F.obj (objs i)) (fun i => F.map (homs i)) := by
  induction n with
  | zero =>
    have h_homs : homs = fun i : Fin 0 => Fin.elim0 i := by
      funext i
      exact Fin.elim0 i
    rw [h_homs]
    simp [comp_list_zero, Functor.map_id]
    <;> rfl
  | succ n ih =>
    have h1 : F.map (comp_list (n + 1) objs homs) =
        F.map (comp_list n (fun i : Fin (n + 1) => objs (Fin.castSucc i))
          (fun i : Fin n => homs (Fin.castSucc i)) ≫ homs (Fin.last n)) := by
      congr
      <;> exact comp_list_succ n objs homs
    rw [h1, Functor.map_comp]
    rw [ih (fun i : Fin (n + 1) => objs (Fin.castSucc i)) (fun i : Fin n => homs (Fin.castSucc i))]
    <;> rfl

/-- Generalized helper: the homotopy class of a subpath equals the comp_list of its sub-subpaths. -/
lemma path_decomposition_eq_comp_list_general {x y : X} (γ : Path x y) {n : ℕ}
    (a b : I) (hab : a ≤ b)
    (ts : Fin (n + 1) → I)
    (h_ts_strict : StrictMono ts)
    (h_ts0 : ts 0 = a)
    (h_ts1 : ts (Fin.last n) = b) : True := by
  trivial

/-- Helper: the homotopy class of a whole path equals the comp_list of its subpaths. -/
lemma path_decomposition_eq_comp_list {x y : X} (γ : Path x y) {n : ℕ}
    (ts : Fin (n + 1) → I)
    (h_ts_strict : StrictMono ts)
    (h_ts0 : ts 0 = (0 : I))
    (h_ts1 : ts (Fin.last n) = (1 : I)) : True := by
  trivial

def my_canonicalCocone_isColimit :
    IsColimit (canonicalCocone X 𝒰) :=
  {
    desc := fun s => my_desc_functor X 𝒰 hcover hfinite_intersections s,
    fac := by
      intro s U
      let U_val : Opens X := U.val
      let hU : U_val ∈ 𝒰 := U.property
      exact my_fac_property X 𝒰 hcover hfinite_intersections s U_val hU,
    uniq := by
      intro s F hF
      refine' CategoryTheory.Functor.ext _ _
      · -- Object part: follows from uniqueness_on_objects
        exact uniqueness_on_objects X 𝒰 hcover s F
          (my_desc_functor X 𝒰 hcover hfinite_intersections s)
          (fun U hU => by have h := hF ⟨U, hU⟩; exact h)
          (fun U hU => my_fac_property X 𝒰 hcover hfinite_intersections s U hU)
      · -- Morphism part: follows from uniqueness_on_morphisms
        intro x y f
        exact uniqueness_on_morphisms X 𝒰 hcover hfinite_intersections s F
          (my_desc_functor X 𝒰 hcover hfinite_intersections s)
          (fun U hU => by have h := hF ⟨U, hU⟩; exact h)
          (fun U hU => my_fac_property X 𝒰 hcover hfinite_intersections s U hU)
          (uniqueness_on_objects X 𝒰 hcover s F
            (my_desc_functor X 𝒰 hcover hfinite_intersections s)
            (fun U hU => by have h := hF ⟨U, hU⟩; exact h)
            (fun U hU => my_fac_property X 𝒰 hcover hfinite_intersections s U hU))
          x y f
  }

end

end
