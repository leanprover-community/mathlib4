module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.UniversalProperty
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.PathHelpers
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.PathDecomposition
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.PathDecompositionLemma
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.ComposeMorphisms

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

include hcover hfinite_intersections

/-- Helper: for a path segment contained in U ∈ 𝒰, F.map and G.map agree modulo eqToHom. -/
lemma agree_on_segment
    (F G : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) ⥤ s.pt)
    (hF : ∀ (U : Opens X) (hU : U ∈ 𝒰),
      (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ F =
      s.ι.app ⟨U, hU⟩)
    (hG : ∀ (U : Opens X) (hU : U ∈ 𝒰),
      (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ G =
      s.ι.app ⟨U, hU⟩)
    (h_objs_eq : ∀ (x : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)),
      F.obj x = G.obj x)
    {x y : X} (γ : Path x y) (U : Opens X) (hU : U ∈ 𝒰)
    (h_range : Set.range γ ⊆ (U : Set X)) :
    F.map (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ)) =
    eqToHom (h_objs_eq (FundamentalGroupoid.mk x)) ≫
    G.map (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ)) ≫
    eqToHom (h_objs_eq (FundamentalGroupoid.mk y)).symm := by
  classical
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
  let π₁U := FundamentalGroupoid.fundamentalGroupoidFunctor.obj ((Opens.toTopCat (TopCat.of X)).obj U)
  let x_U : π₁U := FundamentalGroupoid.mk (⟨x, hx⟩ : (U : Set X))
  let y_U : π₁U := FundamentalGroupoid.mk (⟨y, hy⟩ : (U : Set X))
  let γ_lift : Path (⟨x, hx⟩ : (U : Set X)) (⟨y, hy⟩ : (U : Set X)) :=
    (Path.lift_to_subtype γ hx hy h_range).choose
  let f_U : x_U ⟶ y_U := Path.Homotopic.Quotient.mk γ_lift
  let F' : π₁U ⥤ s.pt :=
    (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ F
  let G' : π₁U ⥤ s.pt :=
    (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ G
  have hF' : F' = s.ι.app ⟨U, hU⟩ := hF U hU
  have hG' : G' = s.ι.app ⟨U, hU⟩ := hG U hU
  have h_eq : F' = G' := by
    rw [hF', hG']
  have h_main : ∀ (a b : π₁U) (f : a ⟶ b),
      F'.map f = eqToHom (congr_arg (fun (K : π₁U ⥤ s.pt) => K.obj a) h_eq) ≫
        G'.map f ≫ eqToHom (congr_arg (fun (K : π₁U ⥤ s.pt) => K.obj b) h_eq).symm := by
    intro a b f
    have h : ∀ (F1 G1 : π₁U ⥤ s.pt) (h : F1 = G1),
        F1.map f = eqToHom (congr_arg (fun (K : π₁U ⥤ s.pt) => K.obj a) h) ≫
          G1.map f ≫ eqToHom (congr_arg (fun (K : π₁U ⥤ s.pt) => K.obj b) h).symm := by
      intro F1 G1 h
      subst h
      <;> simp
      <;> rfl
    exact h F' G' h_eq
  have h2 := h_main x_U y_U f_U
  have h_dom_eq : congr_arg (fun (K : π₁U ⥤ s.pt) => K.obj x_U) h_eq =
      h_objs_eq (FundamentalGroupoid.mk x) := by
    apply Subsingleton.elim
  have h_cod_eq : congr_arg (fun (K : π₁U ⥤ s.pt) => K.obj y_U) h_eq =
      h_objs_eq (FundamentalGroupoid.mk y) := by
    apply Subsingleton.elim
  rw [h_dom_eq, h_cod_eq] at h2
  have h_spec : ∀ t, (γ_lift t : X) = γ t := fun t => (Path.lift_to_subtype γ hx hy h_range).choose_spec t
  let g_top : (Opens.toTopCat (TopCat.of X)).obj U ⟶ TopCat.of X :=
    @Opens.inclusion' (TopCat.of X) U
  let incl_π : π₁U ⥤ FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) :=
    FundamentalGroupoid.fundamentalGroupoidFunctor.map g_top
  have h_incl_map : incl_π.map f_U = FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ) := by
    dsimp only [incl_π, f_U, FundamentalGroupoid.fromPath]
    let f_cont := g_top.hom
    have h1 : (FundamentalGroupoid.fundamentalGroupoidFunctor.map g_top).map (Path.Homotopic.Quotient.mk γ_lift) =
        (Path.Homotopic.Quotient.mk γ_lift).map f_cont := by
      exact FundamentalGroupoid.map_eq f_cont (Path.Homotopic.Quotient.mk γ_lift)
    have h2 : (Path.Homotopic.Quotient.mk γ_lift).map f_cont = Path.Homotopic.Quotient.mk γ := by
      have h21 : (Path.Homotopic.Quotient.mk γ_lift).map f_cont =
          Path.Homotopic.Quotient.mk (γ_lift.map f_cont.continuous) := by
        exact (Path.Homotopic.Quotient.mk_map γ_lift f_cont).symm
      rw [h21]
      apply congr_arg Path.Homotopic.Quotient.mk
      apply Path.ext
      funext t
      exact h_spec t
    rw [h1, h2]
  have h3 : F'.map f_U = F.map (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ)) := by
    dsimp only [F']
    rw [← h_incl_map]
    <;> rfl
  have h4 : G'.map f_U = G.map (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ)) := by
    dsimp only [G']
    rw [← h_incl_map]
    <;> rfl
  rw [h3, h4] at h2
  exact h2

/-- Uniqueness of the descent functor on morphisms: any two functors F G : π₁(X) → s.pt
    that make the cocone triangles commute must agree on all morphisms
    (modulo eqToHom transport for object equalities). -/
theorem uniqueness_on_morphisms
    (F G : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) ⥤ s.pt)
    (hF : ∀ (U : Opens X) (hU : U ∈ 𝒰),
      (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ F =
      s.ι.app ⟨U, hU⟩)
    (hG : ∀ (U : Opens X) (hU : U ∈ 𝒰),
      (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ G =
      s.ι.app ⟨U, hU⟩)
    (h_objs_eq : ∀ (x : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)),
      F.obj x = G.obj x) :
    ∀ (x y : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X))
      (f : x ⟶ y), F.map f = eqToHom (h_objs_eq x) ≫ G.map f ≫ eqToHom (h_objs_eq y).symm := by
  intro x y f
  induction f using Quotient.inductionOn' with
  | h γ =>
    have h_decomp : ∃ (n : ℕ) (ts : Fin (n + 1) → I) (h_ts0 : ts 0 = 0)
      (h_ts1 : ts (Fin.last n) = 1) (h_ts_strict : StrictMono ts)
      (covers : Fin n → Opens X) (hcovers_in : ∀ i, covers i ∈ 𝒰)
      (h_range : ∀ i : Fin n,
        Set.range (γ.subpath (ts (Fin.castSucc i)) (ts (Fin.succ i))) ⊆ (covers i : Set X)), True :=
      path_has_subdivision_with_ts 𝒰 hcover γ
    rcases h_decomp with ⟨n, ts, h_ts0, h_ts1, h_ts_strict, covers, hcovers_in, h_range, _⟩
    let pts : Fin (n + 1) → FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) :=
      fun i => FundamentalGroupoid.mk (γ (ts i))
    let morphs : ∀ i : Fin n, pts (Fin.castSucc i) ⟶ pts (Fin.succ i) :=
      fun i => FundamentalGroupoid.fromPath
        (Path.Homotopic.Quotient.mk (γ.subpath (ts (Fin.castSucc i)) (ts (Fin.succ i))))
    have h_x_eq : pts 0 = x := by
      simp [pts, h_ts0, γ.source] <;> rfl
    have h_y_eq : pts (Fin.last n) = y := by
      simp [pts, h_ts1, γ.target] <;> rfl
    have h_decomp_eq : FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (γ.subpath (ts 0) (ts (Fin.last n)))) =
        comp_list n pts morphs :=
      subpath_decomposition_comp_list γ ts h_ts_strict
    have h_agree : ∀ i : Fin n,
        F.map (morphs i) =
        eqToHom (h_objs_eq (pts (Fin.castSucc i))) ≫
        G.map (morphs i) ≫
        eqToHom (h_objs_eq (pts (Fin.succ i))).symm := by
      intro i
      exact agree_on_segment X 𝒰 hcover hfinite_intersections s F G hF hG h_objs_eq
        (γ.subpath (ts (Fin.castSucc i)) (ts (Fin.succ i)))
        (covers i) (hcovers_in i) (h_range i)
    have h_homs : ∀ i : Fin n,
        eqToHom (h_objs_eq (pts (Fin.castSucc i))).symm ≫ F.map (morphs i) ≫ eqToHom (h_objs_eq (pts (Fin.succ i))) =
        G.map (morphs i) := by
      intro i
      have h := h_agree i
      have h_lhs : eqToHom (h_objs_eq (pts (Fin.castSucc i))).symm ≫ F.map (morphs i) ≫ eqToHom (h_objs_eq (pts (Fin.succ i))) =
          G.map (morphs i) := by
        rw [h]
        <;> simp [Category.assoc, eqToHom_trans, eqToHom_refl]
        <;> rfl
      exact h_lhs
    have h_congr :
        eqToHom (h_objs_eq (pts 0)).symm ≫
        comp_list n (fun i => F.obj (pts i)) (fun i => F.map (morphs i)) ≫
        eqToHom (h_objs_eq (pts (Fin.last n))) =
        comp_list n (fun i => G.obj (pts i)) (fun i => G.map (morphs i)) :=
      comp_list_congr_with_eqToHom
        (fun i => F.obj (pts i)) (fun i => G.obj (pts i))
        (fun i => F.map (morphs i)) (fun i => G.map (morphs i))
        (fun i => h_objs_eq (pts i)) h_homs
    have h_functor_F : F.map (comp_list n pts morphs) =
        comp_list n (fun i => F.obj (pts i)) (fun i => F.map (morphs i)) := by
      exact comp_list_functor_map F pts morphs
    have h_functor_G : G.map (comp_list n pts morphs) =
        comp_list n (fun i => G.obj (pts i)) (fun i => G.map (morphs i)) := by
      exact comp_list_functor_map G pts morphs
    have h_main_comp : F.map (comp_list n pts morphs) =
        eqToHom (h_objs_eq (pts 0)) ≫
        G.map (comp_list n pts morphs) ≫
        eqToHom (h_objs_eq (pts (Fin.last n))).symm := by
      rw [h_functor_F, h_functor_G]
      rw [←h_congr]
      <;> simp [Category.assoc, eqToHom_trans, eqToHom_refl]
      <;> rfl
    -- Now prove the equality for .mk γ using conj_eqToHom and h_main_comp
    have hx : γ (ts 0) = x.as := by
      rw [h_ts0, γ.source] <;> rfl
    have hy : γ (ts (Fin.last n)) = y.as := by
      rw [h_ts1, γ.target] <;> rfl
    let e1 := congr_arg FundamentalGroupoid.mk hx
    let e2 := congr_arg FundamentalGroupoid.mk hy
    have h_conj_eq : eqToHom e1 ≫ Path.Homotopic.Quotient.mk γ ≫ eqToHom (congr_arg FundamentalGroupoid.mk hy.symm) =
        Path.Homotopic.Quotient.mk (γ.cast hx hy) :=
      FundamentalGroupoid.conj_eqToHom hx hy
    have h_path_eq : (γ.cast hx hy) = γ.subpath (ts 0) (ts (Fin.last n)) := by
      apply Path.ext
      funext t
      have h1 : (γ.cast hx hy) t = γ t := by rfl
      have h2 : (γ.subpath (ts 0) (ts (Fin.last n))) t = γ t := by
        simp [Path.subpath, h_ts0, h_ts1] <;> ring_nf <;> congr <;> linarith
      rw [h1, h2]
    have h_eq_cast : Path.Homotopic.Quotient.mk (γ.cast hx hy) =
        Path.Homotopic.Quotient.mk (γ.subpath (ts 0) (ts (Fin.last n))) := by
      rw [h_path_eq] <;> rfl
    have h4 : eqToHom e1 ≫ Path.Homotopic.Quotient.mk γ ≫ eqToHom (congr_arg FundamentalGroupoid.mk hy.symm) =
        comp_list n pts morphs := by
      have h_decomp_eq' : Path.Homotopic.Quotient.mk (γ.subpath (ts 0) (ts (Fin.last n))) =
          comp_list n pts morphs := by
        simpa [FundamentalGroupoid.fromPath] using h_decomp_eq
      rw [h_conj_eq, h_eq_cast, h_decomp_eq'] <;> rfl
    -- Prove the main goal
    have h_goal : F.map (Path.Homotopic.Quotient.mk γ) =
        eqToHom (h_objs_eq x) ≫
        G.map (Path.Homotopic.Quotient.mk γ) ≫
        eqToHom (h_objs_eq y).symm := by
      let g := Path.Homotopic.Quotient.mk γ
      let g' := comp_list n pts morphs
      have h4' : eqToHom h_x_eq ≫ g ≫ eqToHom h_y_eq.symm = g' := by
        have h_e1 : e1 = h_x_eq := by exact Subsingleton.elim e1 h_x_eq
        have h_e2 : congr_arg FundamentalGroupoid.mk hy.symm = h_y_eq.symm := by
          exact Subsingleton.elim (congr_arg FundamentalGroupoid.mk hy.symm) h_y_eq.symm
        have h4_copy : eqToHom e1 ≫ Path.Homotopic.Quotient.mk γ ≫ eqToHom (congr_arg FundamentalGroupoid.mk hy.symm) = g' := h4
        rw [h_e1, h_e2] at h4_copy
        exact h4_copy
      have h_eq1 : eqToHom h_x_eq.symm ≫ eqToHom h_x_eq = 𝟙 x := by
        rw [eqToHom_trans, eqToHom_refl]
        <;> exact rfl
      have h_eq2 : eqToHom h_y_eq.symm ≫ eqToHom h_y_eq = 𝟙 y := by
        rw [eqToHom_trans, eqToHom_refl]
        <;> exact rfl
      have h_F_map : F.map g =
          eqToHom (congr_arg F.obj h_x_eq.symm) ≫
          F.map g' ≫
          eqToHom (congr_arg F.obj h_y_eq) := by
        have h : g = eqToHom h_x_eq.symm ≫ g' ≫ eqToHom h_y_eq := by
          calc
            g
              = 𝟙 x ≫ g ≫ 𝟙 y := by simp
            _ = (eqToHom h_x_eq.symm ≫ eqToHom h_x_eq) ≫ g ≫ (eqToHom h_y_eq.symm ≫ eqToHom h_y_eq) := by
                rw [h_eq1, h_eq2]
            _ = eqToHom h_x_eq.symm ≫ (eqToHom h_x_eq ≫ g ≫ eqToHom h_y_eq.symm) ≫ eqToHom h_y_eq := by
                simp [Category.assoc]
                <;> rfl
            _ = eqToHom h_x_eq.symm ≫ g' ≫ eqToHom h_y_eq := by
                rw [h4'] <;> rfl
        rw [h]
        rw [Functor.map_comp, Functor.map_comp]
        rw [eqToHom_map F, eqToHom_map F]
        <;> rfl
      have h_G_map : G.map g =
          eqToHom (congr_arg G.obj h_x_eq.symm) ≫
          G.map g' ≫
          eqToHom (congr_arg G.obj h_y_eq) := by
        have h : g = eqToHom h_x_eq.symm ≫ g' ≫ eqToHom h_y_eq := by
          calc
            g
              = 𝟙 x ≫ g ≫ 𝟙 y := by simp
            _ = (eqToHom h_x_eq.symm ≫ eqToHom h_x_eq) ≫ g ≫ (eqToHom h_y_eq.symm ≫ eqToHom h_y_eq) := by
                rw [h_eq1, h_eq2]
            _ = eqToHom h_x_eq.symm ≫ (eqToHom h_x_eq ≫ g ≫ eqToHom h_y_eq.symm) ≫ eqToHom h_y_eq := by
                simp [Category.assoc]
                <;> rfl
            _ = eqToHom h_x_eq.symm ≫ g' ≫ eqToHom h_y_eq := by
                rw [h4'] <;> rfl
        rw [h]
        rw [Functor.map_comp, Functor.map_comp]
        rw [eqToHom_map G, eqToHom_map G]
        <;> rfl
      have h_nat1 : eqToHom (congr_arg F.obj h_x_eq.symm) ≫ eqToHom (h_objs_eq (pts 0)) =
          eqToHom (h_objs_eq x) ≫ eqToHom (congr_arg G.obj h_x_eq.symm) := by
        rw [eqToHom_trans, eqToHom_trans]
      have h_nat2 : eqToHom (h_objs_eq (pts (Fin.last n))).symm ≫ eqToHom (congr_arg F.obj h_y_eq) =
          eqToHom (congr_arg G.obj h_y_eq) ≫ eqToHom (h_objs_eq y).symm := by
        rw [eqToHom_trans, eqToHom_trans]
      calc
        F.map g
          = eqToHom (congr_arg F.obj h_x_eq.symm) ≫ F.map g' ≫ eqToHom (congr_arg F.obj h_y_eq) := h_F_map
        _ = eqToHom (congr_arg F.obj h_x_eq.symm) ≫
            (eqToHom (h_objs_eq (pts 0)) ≫ G.map g' ≫ eqToHom (h_objs_eq (pts (Fin.last n))).symm) ≫
            eqToHom (congr_arg F.obj h_y_eq) := by
          rw [h_main_comp] <;> rfl
        _ = (eqToHom (congr_arg F.obj h_x_eq.symm) ≫ eqToHom (h_objs_eq (pts 0))) ≫
            G.map g' ≫
            (eqToHom (h_objs_eq (pts (Fin.last n))).symm ≫ eqToHom (congr_arg F.obj h_y_eq)) := by
          simp [Category.assoc] <;> rfl
        _ = (eqToHom (h_objs_eq x) ≫ eqToHom (congr_arg G.obj h_x_eq.symm)) ≫
            G.map g' ≫
            (eqToHom (congr_arg G.obj h_y_eq) ≫ eqToHom (h_objs_eq y).symm) := by
          rw [h_nat1, h_nat2] <;> rfl
        _ = eqToHom (h_objs_eq x) ≫
            (eqToHom (congr_arg G.obj h_x_eq.symm) ≫ G.map g' ≫ eqToHom (congr_arg G.obj h_y_eq)) ≫
            eqToHom (h_objs_eq y).symm := by
          simp [Category.assoc] <;> rfl
        _ = eqToHom (h_objs_eq x) ≫ G.map g ≫ eqToHom (h_objs_eq y).symm := by
          rw [←h_G_map] <;> rfl
    exact h_goal

end

end
