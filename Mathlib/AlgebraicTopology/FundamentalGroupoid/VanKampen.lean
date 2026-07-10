module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.IsColimit

/-!
# Van Kampen theorem

# References
- May
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open scoped FundamentalGroupoid

universe u

variable {X : TopCat.{u}}

noncomputable section

namespace FundamentalGroupoid

def opensToGrpd (X : TopCat.{u}) : Opens X ⥤ Grpd :=
  Opens.toTopCat X ⋙ π

scoped notation "πₒ" => FundamentalGroupoid.opensToGrpd

end FundamentalGroupoid

namespace VanKampenTransport

open FundamentalGroupoid

variable (X)

/-- The canonical cocone on a subtype family 𝒰 with apex V. -/
def mkSubtypeCocone (V : Opens X) (𝒰 : Set (Opens X))
    (h_le : ∀ U ∈ 𝒰, U ≤ V) :
    Cocone ((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor ⋙ πₒ X) :=
  { pt := (πₒ X).obj V
    ι := {
      app := fun (U : {U // U ∈ 𝒰}) =>
        (πₒ X).map (homOfLE (h_le U.val U.property))
      naturality := fun {U W} f => by
        have h2 : (Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor.map f ≫
            homOfLE (h_le W.val W.property) = homOfLE (h_le U.val U.property) := by
          apply Subsingleton.elim
        convert congr_arg (πₒ X).map h2 using 1
        <;> simp [opensToGrpd, Functor.comp_map]
        <;> rfl
    }
  }

variable {X}
variable {ι : Type u} (U : ι → Opens X)

abbrev coverSet : Set (Opens X) := {W | ∃ i : ι, W ≤ U i}
abbrev coverProp : ObjectProperty (Opens X) := fun V => ∃ i : ι, V ≤ U i

-- Subsingleton hom-sets for FullSubcategory
instance subsingleton_hom_fullsubcat {V W : (coverProp U).FullSubcategory} :
    Subsingleton (V ⟶ W) := by
  refine' ⟨fun f g => _⟩
  have h : (coverProp U).ι.map f = (coverProp U).ι.map g := Subsingleton.elim _ _
  exact ObjectProperty.hom_ext (coverProp U) h

-- Subsingleton hom-sets for subtype
instance subsingleton_hom_subtype {V W : {W : Opens X // W ∈ coverSet U}} :
    Subsingleton (V ⟶ W) :=
  Preorder.subsingleton_hom V W

-- Forward functor
def fwdFunctor :
    {W : Opens X // W ∈ coverSet U} ⥤ (coverProp U).FullSubcategory where
  obj := fun W => ⟨W.val, W.property⟩
  map := fun {W V} (f : W ⟶ V) =>
    ObjectProperty.homMk ((Subtype.mono_coe (fun W : Opens X => W ∈ coverSet U)).functor.map f)
  map_id := by
    intro W
    exact Subsingleton.elim _ _
  map_comp := by
    intro W V Z f g
    exact Subsingleton.elim _ _

-- Backward functor
def bwdFunctor :
    (coverProp U).FullSubcategory ⥤ {W : Opens X // W ∈ coverSet U} where
  obj := fun V => ⟨V.obj, V.property⟩
  map := fun {V W} (f : V ⟶ W) =>
    homOfLE (show (⟨V.obj, V.property⟩ : {W : Opens X // W ∈ coverSet U}) ≤
      (⟨W.obj, W.property⟩) from leOfHom f.hom)
  map_id := by
    intro V
    exact Subsingleton.elim _ _
  map_comp := by
    intro V W Z f g
    exact Subsingleton.elim _ _

-- Index equivalence
def indexEquiv :
    {W : Opens X // W ∈ coverSet U} ≌ (coverProp U).FullSubcategory := by
  refine' {
    functor := fwdFunctor U,
    inverse := bwdFunctor U,
    unitIso := NatIso.ofComponents (fun x => eqToIso (by simp [fwdFunctor, bwdFunctor])) (by
      intro x y f
      exact Subsingleton.elim _ _),
    counitIso := NatIso.ofComponents (fun x => eqToIso (by simp [fwdFunctor, bwdFunctor])) (by
      intro x y f
      exact Subsingleton.elim _ _)
  }

/-- The opensLeCover family is closed under finite intersections. -/
lemma opensLeCover_closedUnderFiniteIntersections
    (s : Finset (Opens X)) (hs_nonempty : s.Nonempty)
    (hs : ∀ V ∈ s, ∃ i : ι, V ≤ U i) :
    ∃ i : ι, s.inf (fun V => V) ≤ U i := by
  classical
  obtain ⟨V, hV_in⟩ := hs_nonempty
  rcases hs V hV_in with ⟨i, hi⟩
  refine' ⟨i, _⟩
  have h : s.inf (fun V => V) ≤ V := Finset.inf_le hV_in
  exact le_trans h hi

/-- Relative Van Kampen theorem (subtype form).
    Proof: apply absolute Van Kampen to the subspace V and transport back. -/
theorem relative_vanKampen_subtype (V : Opens X) (𝒰 : Set (Opens X))
    (h_le : ∀ U ∈ 𝒰, U ≤ V)
    (hcover : ∀ x ∈ V, ∃ U ∈ 𝒰, x ∈ U)
    (hfinite_intersections :
      ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U => U) ∈ 𝒰) :
    Nonempty (IsColimit (mkSubtypeCocone X V 𝒰 h_le)) := by
  -- Step 0: Setup
  let Y : TopCat := (Opens.toTopCat X).obj V
  let i_top : Y ⟶ X := Opens.inclusion' V
  let h_emb : Topology.IsOpenEmbedding i_top := Opens.isOpenEmbedding' V
  let F_map : Opens X ⥤ Opens Y := Opens.map i_top
  let 𝒰_Y : Set (Opens Y) := F_map.obj '' 𝒰
  let π₁ := FundamentalGroupoid.fundamentalGroupoidFunctor

  -- Step 1: hcover_Y
  have hcover_Y : ∀ y : Y, ∃ U_Y : Opens Y, U_Y ∈ 𝒰_Y ∧ y ∈ U_Y := by
    intro y
    have hx : (i_top y) ∈ V := y.property
    rcases hcover (i_top y) hx with ⟨U, hU_in, hU_mem⟩
    refine' ⟨F_map.obj U, ⟨U, hU_in, rfl⟩, _⟩
    have h : y ∈ F_map.obj U ↔ i_top y ∈ U := Iff.rfl
    exact h.mpr hU_mem

  -- Step 2: hfi_Y
  have hfi_Y : ∀ s : Finset (Opens Y), s.Nonempty →
      (∀ U_Y ∈ s, U_Y ∈ 𝒰_Y) → s.inf (fun U_Y => U_Y) ∈ 𝒰_Y := by
    intro s hs_nonempty hs
    classical
    have h1 : ∀ U_Y ∈ s, ∃ U : Opens X, U ∈ 𝒰 ∧ F_map.obj U = U_Y := by
      intro U_Y hU_Y
      have h2 : U_Y ∈ 𝒰_Y := hs U_Y hU_Y
      rcases h2 with ⟨U, hU_in, rfl⟩
      exact ⟨U, hU_in, rfl⟩
    choose f hf using fun (U_Y : Opens Y) (hU_Y : U_Y ∈ s) => h1 U_Y hU_Y
    let f' : Opens Y → Opens X := fun U_Y => if h : U_Y ∈ s then f U_Y h else ⊥
    let s_X : Finset (Opens X) := Finset.image f' s
    have hs_X_nonempty : s_X.Nonempty := by
      rcases hs_nonempty with ⟨U_Y, hU_Y⟩
      exact ⟨f' U_Y, Finset.mem_image.mpr ⟨U_Y, hU_Y, rfl⟩⟩
    have hs_X_in : ∀ U ∈ s_X, U ∈ 𝒰 := by
      intro U hU
      rcases Finset.mem_image.mp hU with ⟨U_Y, hU_Y, rfl⟩
      have h2 : f' U_Y = f U_Y hU_Y := by
        dsimp only [f']
        rw [dif_pos hU_Y]
      rw [h2]
      exact (hf U_Y hU_Y).1
    have h_inf_in : s_X.inf (fun U => U) ∈ 𝒰 := hfinite_intersections s_X hs_X_nonempty hs_X_in
    have h_inf_eq : F_map.obj (s_X.inf (fun U => U)) = s.inf (fun U_Y => U_Y) := by
      apply SetLike.ext
      intro y
      have h_left : y ∈ F_map.obj (s_X.inf (fun U => U)) ↔ ∀ U ∈ s_X, i_top y ∈ U := by
        have h_mem : y ∈ F_map.obj (s_X.inf (fun U => U)) ↔ i_top y ∈ s_X.inf (fun U => U) := Iff.rfl
        rw [h_mem]
        have h_coe : (↑(s_X.inf (fun U : Opens X => U)) : Set X) = s_X.inf (fun U : Opens X => (↑U : Set X)) :=
          Opens.coe_finset_inf (fun U : Opens X => U) s_X
        have h1 : i_top y ∈ s_X.inf (fun U : Opens X => U) ↔ i_top y ∈ (↑(s_X.inf (fun U : Opens X => U)) : Set X) := Iff.rfl
        rw [h1, h_coe]
        have h2 : i_top y ∈ s_X.inf (fun U : Opens X => (↑U : Set X)) ↔
            ∀ U ∈ s_X, i_top y ∈ (↑U : Set X) := by
          simp [Set.ext_iff, Finset.le_inf_iff]
          <;> tauto
        exact h2
      have h_right : y ∈ s.inf (fun U_Y => U_Y) ↔ ∀ U_Y ∈ s, y ∈ U_Y := by
        have h_coe : (↑(s.inf (fun U_Y : Opens Y => U_Y)) : Set Y) = s.inf (fun U_Y : Opens Y => (↑U_Y : Set Y)) :=
          Opens.coe_finset_inf (fun U_Y : Opens Y => U_Y) s
        have h1 : y ∈ s.inf (fun U_Y : Opens Y => U_Y) ↔ y ∈ (↑(s.inf (fun U_Y : Opens Y => U_Y)) : Set Y) := Iff.rfl
        rw [h1, h_coe]
        simp [Set.ext_iff, Finset.le_inf_iff]
        <;> tauto
      rw [h_left, h_right]
      constructor
      · intro h
        intro U_Y hU_Y
        have h4 : f' U_Y ∈ s_X := Finset.mem_image.mpr ⟨U_Y, hU_Y, rfl⟩
        have h5 : i_top y ∈ f' U_Y := h (f' U_Y) h4
        have h6 : F_map.obj (f' U_Y) = U_Y := by
          have h7 : f' U_Y = f U_Y hU_Y := by
            dsimp only [f']
            rw [dif_pos hU_Y]
          rw [h7]
          exact (hf U_Y hU_Y).2
        have h8 : y ∈ F_map.obj (f' U_Y) ↔ i_top y ∈ f' U_Y := Iff.rfl
        rw [←h6]
        exact h8.mpr h5
      · intro h
        intro U hU
        rcases Finset.mem_image.mp hU with ⟨U_Y, hU_Y, rfl⟩
        have h7 : f' U_Y = f U_Y hU_Y := by
          dsimp only [f']
          rw [dif_pos hU_Y]
        have h9 : y ∈ F_map.obj (f' U_Y) := by
          have h10 : F_map.obj (f' U_Y) = U_Y := by
            rw [h7]
            exact (hf U_Y hU_Y).2
          rw [h10]
          exact h U_Y hU_Y
        have h11 : y ∈ F_map.obj (f' U_Y) ↔ i_top y ∈ f' U_Y := Iff.rfl
        exact h11.mp h9
    exact ⟨s_X.inf (fun U => U), h_inf_in, h_inf_eq⟩

  -- Step 3: Index categories
  let J := {U : Opens X // U ∈ 𝒰}
  let K := {U_Y : Opens Y // U_Y ∈ 𝒰_Y}
  let F_J : J ⥤ Opens X := (Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor
  let F_K : K ⥤ Opens Y := (Subtype.mono_coe (fun U_Y : Opens Y => U_Y ∈ 𝒰_Y)).functor
  let F_diag : J ⥤ Grpd := F_J ⋙ opensToGrpd X

  classical

  -- Step 5: Equivalence e : J ≌ K
  have hF_map_reflects_le : ∀ (U W : Opens X), U ≤ V → W ≤ V → F_map.obj U ≤ F_map.obj W → U ≤ W := by
    intro U W hU hW h
    intro x hx
    have hxV : x ∈ V := hU hx
    let y : Y := ⟨x, hxV⟩
    have hyU : y ∈ F_map.obj U := hx
    have hyW : y ∈ F_map.obj W := h hyU
    exact hyW
  have hF_map_reflects_eq : ∀ (U W : Opens X), U ≤ V → W ≤ V → F_map.obj U = F_map.obj W → U = W := by
    intro U W hU hW h
    have h1 : F_map.obj U ≤ F_map.obj W := by exact Eq.le h
    have h2 : F_map.obj W ≤ F_map.obj U := by exact Eq.le h.symm
    have h3 : U ≤ W := hF_map_reflects_le U W hU hW h1
    have h4 : W ≤ U := hF_map_reflects_le W U hW hU h2
    exact le_antisymm h3 h4

  let e_fun_obj (U : J) : K := ⟨F_map.obj U.val, ⟨U.val, U.property, rfl⟩⟩
  let e_fun : J ⥤ K :=
    { obj := e_fun_obj
      map := fun {U W} (_ : U ⟶ W) =>
        homOfLE (show (e_fun_obj U).val ≤ (e_fun_obj W).val from by
          exact leOfHom (F_map.map (homOfLE (leOfHom ‹U ⟶ W›))))
      map_id := by intro U; apply Subsingleton.elim
      map_comp := by intro U W Z f g; apply Subsingleton.elim }

  have h_exists : ∀ (U_Y : K), ∃ (U : Opens X), U ∈ 𝒰 ∧ F_map.obj U = U_Y.val := by
    intro U_Y
    have h : U_Y.val ∈ 𝒰_Y := U_Y.property
    rcases h with ⟨U, hU_in, h_eq⟩
    exact ⟨U, hU_in, h_eq⟩
  choose g_fun_obj_val hg using h_exists
  let g_fun_obj (U_Y : K) : J := ⟨g_fun_obj_val U_Y, (hg U_Y).1⟩
  let g_fun : K ⥤ J :=
    { obj := g_fun_obj
      map := fun {U_Y W_Y} (f : U_Y ⟶ W_Y) =>
        homOfLE (hF_map_reflects_le (g_fun_obj U_Y).val (g_fun_obj W_Y).val
          (h_le (g_fun_obj U_Y).val (g_fun_obj U_Y).property)
          (h_le (g_fun_obj W_Y).val (g_fun_obj W_Y).property)
          (by rw [(hg U_Y).2, (hg W_Y).2]; exact leOfHom f))
      map_id := by intro U_Y; apply Subsingleton.elim
      map_comp := by intro U_Y W_Y Z_Y f g; apply Subsingleton.elim }

  have h_unit : ∀ (U : J), g_fun.obj (e_fun.obj U) = U := by
    intro U
    apply Subtype.ext
    have h1 : F_map.obj (g_fun.obj (e_fun.obj U)).val = (e_fun.obj U).val := (hg (e_fun.obj U)).2
    have h2 : (e_fun.obj U).val = F_map.obj U.val := by rfl
    have h3 : F_map.obj (g_fun.obj (e_fun.obj U)).val = F_map.obj U.val := by rw [h1, h2]
    have h4 : (g_fun.obj (e_fun.obj U)).val ≤ V := h_le (g_fun.obj (e_fun.obj U)).val (g_fun.obj (e_fun.obj U)).property
    have h5 : U.val ≤ V := h_le U.val U.property
    exact hF_map_reflects_eq (g_fun.obj (e_fun.obj U)).val U.val h4 h5 h3

  have h_counit : ∀ (U_Y : K), e_fun.obj (g_fun.obj U_Y) = U_Y := by
    intro U_Y
    apply Subtype.ext
    have h1 : F_map.obj (g_fun.obj U_Y).val = U_Y.val := (hg U_Y).2
    simpa [e_fun, e_fun_obj] using h1

  let e : J ≌ K :=
    { functor := e_fun
      inverse := g_fun
      unitIso := NatIso.ofComponents (fun U =>
        eqToIso (show (𝟭 J).obj U = (e_fun ⋙ g_fun).obj U from by
          simpa [Functor.comp_obj] using (h_unit U).symm)) (by
        intro U W f; apply Subsingleton.elim)
      counitIso := NatIso.ofComponents (fun U_Y =>
        eqToIso (show (g_fun ⋙ e_fun).obj U_Y = (𝟭 K).obj U_Y from by
          simpa [Functor.comp_obj] using h_counit U_Y)) (by
        intro U_Y W_Y f; apply Subsingleton.elim) }

  -- Step 6: Define G_diag and s_Y with explicit type
  let G_diag : K ⥤ Grpd := F_K ⋙ opensToGrpd Y
  let s_Y : Cocone G_diag := canonicalCocone Y 𝒰_Y
  have h_colim_Y : IsColimit s_Y :=
    my_canonicalCocone_isColimit Y 𝒰_Y hcover_Y hfi_Y

  -- Step 7: Whisker colimit along e
  let s1 : Cocone (e_fun ⋙ G_diag) := s_Y.whisker e_fun
  have h1 : IsColimit s1 := h_colim_Y.whiskerEquivalence e

  -- Step 8: Natural isomorphism e.functor ⋙ G_diag ≅ F_diag
  have h_range_i_top : Set.range (i_top : Y → X) = (V : Set X) := by
    ext x
    simp only [Set.mem_range, SetLike.mem_coe]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      refine' ⟨⟨x, hx⟩, _⟩
      rfl
  have h_range : ∀ (U : J), (U.val : Set X) ⊆ Set.range (i_top : Y → X) := by
    intro U
    have hU : U.val ≤ V := h_le U.val U.property
    rw [h_range_i_top]
    exact hU

  -- Homeomorphism between U_Y (subspace of Y) and U (subspace of X)
  let homeo_iso (U : J) :
      (Opens.toTopCat Y).obj (F_map.obj U.val) ≅ (Opens.toTopCat X).obj U.val :=
    TopCat.isoOfHomeo (Topology.IsEmbedding.homeomorphOfSubsetRange h_emb.isEmbedding (h_range U))

  -- Key fact: s_Y.ι.app U_Y = π₁.map (Opens.inclusion' U_Y.val)
  have h_s_Y_app : ∀ (U_Y : K), s_Y.ι.app U_Y = π₁.map (Opens.inclusion' U_Y.val) := by
    intro U_Y
    rfl

  -- Component-wise isomorphism
  let component_iso (U : J) : (e_fun ⋙ G_diag).obj U ≅ F_diag.obj U :=
    π₁.mapIso (homeo_iso U)

  -- Naturality of the component isomorphisms
  let F1 : J ⥤ TopCat := e_fun ⋙ F_K ⋙ Opens.toTopCat Y
  let F2 : J ⥤ TopCat := F_J ⋙ Opens.toTopCat X
  let nat_iso_top_components (U : J) : F1.obj U ≅ F2.obj U := homeo_iso U
  have h_nat_top : ∀ {U W : J} (f : U ⟶ W),
      F1.map f ≫ (nat_iso_top_components W).hom =
      (nat_iso_top_components U).hom ≫ F2.map f := by
    intro U W f
    dsimp only [F1, F2, nat_iso_top_components, Functor.comp_map]
    let f_Y : (e_fun.obj U).val ⟶ (e_fun.obj W).val := F_K.map (e_fun.map f)
    let f_X : U.val ⟶ W.val := F_J.map f
    have h_comm : (Opens.toTopCat Y).map f_Y ≫ (homeo_iso W).hom =
        (homeo_iso U).hom ≫ (Opens.toTopCat X).map f_X := by
      apply TopCat.hom_ext
      ext ⟨y, hy⟩
      simp [homeo_iso, f_Y, f_X, Subtype.ext_iff]
      <;> rfl
    exact h_comm
  let nat_iso_top : F1 ≅ F2 :=
    NatIso.ofComponents nat_iso_top_components fun {X Y} f => h_nat_top f
  let h_nat_iso : e_fun ⋙ G_diag ≅ F_diag := by
    dsimp only [G_diag, F_diag, opensToGrpd]
    exact Functor.isoWhiskerRight nat_iso_top π₁

  -- Step 9: Transport colimit along natural isomorphism
  let α : e_fun ⋙ G_diag ≅ F_diag := h_nat_iso
  let β : F_diag ≅ e_fun ⋙ G_diag := α.symm
  let s2 : Cocone F_diag := (Cocone.precompose β.hom).obj s1
  have h2 : IsColimit s2 :=
    (IsColimit.precomposeHomEquiv β s1).symm h1

  -- Step 10: Triangle identity
  have h_triangle_id : ∀ (j : J),
      (component_iso j).hom ≫ (mkSubtypeCocone X V 𝒰 h_le).ι.app j = s1.ι.app j := by
    intro j
    have h3 : s1.ι.app j = s_Y.ι.app (e_fun.obj j) := by rfl
    have h4 : s_Y.ι.app (e_fun.obj j) = π₁.map (Opens.inclusion' (e_fun.obj j).val) := h_s_Y_app (e_fun.obj j)
    have h5 : (mkSubtypeCocone X V 𝒰 h_le).ι.app j = (opensToGrpd X).map (homOfLE (h_le j.val j.property)) := by rfl
    let a : (Opens.toTopCat Y).obj (F_map.obj j.val) ⟶ (Opens.toTopCat X).obj j.val := (homeo_iso j).hom
    let b : (Opens.toTopCat X).obj j.val ⟶ (Opens.toTopCat X).obj V := (Opens.toTopCat X).map (homOfLE (h_le j.val j.property))
    let c : (Opens.toTopCat Y).obj (F_map.obj j.val) ⟶ Y := Opens.inclusion' (e_fun.obj j).val
    have h_eq_top : a ≫ b = c := by
      apply TopCat.hom_ext
      ext ⟨y, hy⟩
      simp [homeo_iso, a, b, c, Subtype.ext_iff]
      <;> rfl
    have h_comp_ab : π₁.map (a ≫ b) = π₁.map a ≫ π₁.map b := π₁.map_comp a b
    have h_goal : π₁.map a ≫ π₁.map b = π₁.map c := by
      calc
        π₁.map a ≫ π₁.map b
          = π₁.map (a ≫ b) := h_comp_ab.symm
        _ = π₁.map c := by rw [h_eq_top]
    have h1 : (component_iso j).hom = π₁.map a := by exact?
    have h_main : (component_iso j).hom ≫ (mkSubtypeCocone X V 𝒰 h_le).ι.app j = s1.ι.app j := by
      rw [h1, h5, h3, h4]
      dsimp only [opensToGrpd, Functor.comp_map]
      exact h_goal
    exact h_main

  -- Step 11: s2 ≅ mkSubtypeCocone X V 𝒰 h_le
  have h_iso : s2 ≅ mkSubtypeCocone X V 𝒰 h_le := by
    let apex_iso : s2.pt ≅ (mkSubtypeCocone X V 𝒰 h_le).pt := eqToIso (by
      dsimp only [s2, s1, s_Y, β, mkSubtypeCocone, opensToGrpd,
        Cocone.precompose_obj_pt, Cocone.whisker]
      <;> rfl)
    have h_s2_ι_eq : ∀ (j : J), s2.ι.app j = (mkSubtypeCocone X V 𝒰 h_le).ι.app j := by
      intro j
      have h_s2_def : s2.ι.app j = β.hom.app j ≫ s1.ι.app j := by rfl
      have hβ : β.hom.app j = (component_iso j).inv := by
        have hβ1 : β.hom.app j = α.inv.app j := by rfl
        rw [hβ1]
        dsimp only [α, h_nat_iso]
        <;> rfl
      rw [h_s2_def, hβ]
      have h_tri : (component_iso j).hom ≫ (mkSubtypeCocone X V 𝒰 h_le).ι.app j = s1.ι.app j :=
        h_triangle_id j
      calc
        (component_iso j).inv ≫ s1.ι.app j
          = (component_iso j).inv ≫ ((component_iso j).hom ≫ (mkSubtypeCocone X V 𝒰 h_le).ι.app j) := by
            congr 1
            exact h_tri.symm
        _ = ((component_iso j).inv ≫ (component_iso j).hom) ≫ (mkSubtypeCocone X V 𝒰 h_le).ι.app j := by
          rw [Category.assoc]
        _ = 𝟙 _ ≫ (mkSubtypeCocone X V 𝒰 h_le).ι.app j := by
          rw [Iso.inv_hom_id]
          <;> rfl
        _ = (mkSubtypeCocone X V 𝒰 h_le).ι.app j := by
          rw [Category.id_comp]
    fconstructor
    · -- hom : s2 ⟶ mkSubtypeCocone
      exact { hom := apex_iso.hom
              w := by
                intro j
                have h_main : s2.ι.app j ≫ apex_iso.hom = (mkSubtypeCocone X V 𝒰 h_le).ι.app j := by
                  rw [h_s2_ι_eq j]
                  simp [apex_iso] <;> rfl
                exact h_main }
    · -- inv : mkSubtypeCocone ⟶ s2
      exact { hom := apex_iso.inv
              w := by
                intro j
                have h_main : (mkSubtypeCocone X V 𝒰 h_le).ι.app j ≫ apex_iso.inv = s2.ι.app j := by
                  rw [h_s2_ι_eq j]
                  simp [apex_iso] <;> rfl
                exact h_main }
    · -- hom_inv_id
      ext <;> simp [apex_iso] <;> rfl
    · -- inv_hom_id
      ext <;> simp [apex_iso] <;> rfl

  have h_main : IsColimit (mkSubtypeCocone X V 𝒰 h_le) :=
    IsColimit.ofIsoColimit h2 h_iso
  exact ⟨h_main⟩

variable (X)

/-- Transport colimit from subtype-indexed to opensLeCover-indexed.

    Proof: uses index equivalence + cocone isomorphisms to transport
    the colimit from the subtype-indexed diagram to the opensLeCover diagram. -/
theorem transport_index_equiv (V : Opens X)
    (h_le : ∀ W ∈ coverSet U, W ≤ V)
    (hV : V = iSup U)
    (h_colim : Nonempty (IsColimit (mkSubtypeCocone X V (coverSet U) h_le))) :
    Nonempty (IsColimit ((πₒ X).mapCocone
      (TopCat.Presheaf.SheafCondition.opensLeCoverCocone U))) := by
  subst hV
  rcases h_colim with ⟨h_colim⟩
  let e := indexEquiv U
  let J := {W : Opens X // W ∈ coverSet U}
  let K := (coverProp U).FullSubcategory
  let F_S := (Subtype.mono_coe (fun W : Opens X => W ∈ coverSet U)).functor ⋙ πₒ X
  let F_D := (coverProp U).ι ⋙ πₒ X
  let c_S := mkSubtypeCocone X (iSup U) (coverSet U) h_le
  let c_D := (πₒ X).mapCocone (TopCat.Presheaf.SheafCondition.opensLeCoverCocone U)

  have hF : fwdFunctor U ⋙ F_D = F_S := by
    dsimp only [F_D, F_S]
    have h : fwdFunctor U ⋙ (coverProp U).ι =
        (Subtype.mono_coe (fun W : Opens X => W ∈ coverSet U)).functor := by
      refine' CategoryTheory.Functor.ext (fun x => by rfl) _
      intro x y f
      exact Subsingleton.elim _ _
    exact congr_arg (fun (F : J ⥤ Opens X) => F ⋙ πₒ X) h

  let α : (fwdFunctor U ⋙ F_D) ≅ F_S := eqToIso hF

  -- Step 1: c1 is c_S precomposed with α.hom (colimit on fwdFunctor U ⋙ F_D)
  let c1 : Cocone (fwdFunctor U ⋙ F_D) := (Cocone.precompose α.hom).obj c_S
  have h1 : IsColimit c1 := (IsColimit.precomposeHomEquiv α c_S).symm h_colim

  -- Step 2: Build c'_D directly on F_D, then c_whisker = whisker e.functor c'_D
  let c'_D : Cocone F_D :=
    { pt := c_S.pt
      ι := {
        app := fun (k : K) => (πₒ X).map (homOfLE (h_le k.obj k.property))
        naturality := fun {k₁ k₂ : K} (f : k₁ ⟶ k₂) => by
          have h : (πₒ X).map ((coverProp U).ι.map f) ≫
              (πₒ X).map (homOfLE (h_le k₂.obj k₂.property)) =
              (πₒ X).map (homOfLE (h_le k₁.obj k₁.property)) := by
            rw [← Functor.map_comp]
            congr 1
            <;> exact Subsingleton.elim _ _
          convert h using 1
          <;> simp [opensToGrpd, Functor.comp_map] <;> rfl
      }
    }

  let c_whisker : Cocone (fwdFunctor U ⋙ F_D) := Cocone.whisker (fwdFunctor U) c'_D

  -- Step 3: Build isomorphism c1 ≅ c_whisker
  let e_mor : c1 ⟶ c_whisker :=
    { hom := 𝟙 c_S.pt
      w := fun j => by
        dsimp only [c1, c_whisker, c'_D, α, eqToIso, Cocone.whisker,
          Cocone.precompose, Functor.whiskerLeft]
        <;> simp [Category.id_comp, Category.comp_id]
        <;> aesop_cat }

  let e_inv : c_whisker ⟶ c1 :=
    { hom := 𝟙 c_S.pt
      w := fun j => by
        dsimp only [c1, c_whisker, c'_D, α, eqToIso, Cocone.whisker,
          Cocone.precompose, Functor.whiskerLeft]
        <;> simp [Category.id_comp, Category.comp_id]
        <;> aesop_cat }

  have h_e1 : e_mor ≫ e_inv = 𝟙 c1 := by
    apply CoconeMorphism.ext
    simp [e_mor, e_inv]
    <;> rfl

  have h_e2 : e_inv ≫ e_mor = 𝟙 c_whisker := by
    apply CoconeMorphism.ext
    simp [e_mor, e_inv]
    <;> rfl

  let e_iso : c1 ≅ c_whisker :=
    { hom := e_mor
      inv := e_inv
      hom_inv_id := h_e1
      inv_hom_id := h_e2 }

  have h2 : IsColimit c_whisker := IsColimit.ofIsoColimit h1 e_iso

  -- Step 4: By whisker equivalence, c'_D is a colimit
  have h3 : IsColimit c'_D :=
    (IsColimit.whiskerEquivalenceEquiv e).symm h2

  -- Step 5: Build isomorphism c'_D ≅ c_D
  let e2_mor : c'_D ⟶ c_D :=
    { hom := 𝟙 c_S.pt
      w := fun k => by
        dsimp only [c'_D, c_D, Functor.mapCocone]
        <;> simp [Category.id_comp, Category.comp_id]
        <;> rfl }

  let e2_inv : c_D ⟶ c'_D :=
    { hom := 𝟙 c_S.pt
      w := fun k => by
        dsimp only [c'_D, c_D, Functor.mapCocone]
        <;> simp [Category.id_comp, Category.comp_id]
        <;> rfl }

  have h_e21 : e2_mor ≫ e2_inv = 𝟙 c'_D := by
    apply CoconeMorphism.ext
    simp [e2_mor, e2_inv]
    <;> rfl

  have h_e22 : e2_inv ≫ e2_mor = 𝟙 c_D := by
    apply CoconeMorphism.ext
    simp [e2_mor, e2_inv]
    <;> rfl

  let e2_iso : c'_D ≅ c_D :=
    { hom := e2_mor
      inv := e2_inv
      hom_inv_id := h_e21
      inv_hom_id := h_e22 }

  have h_final : IsColimit c_D := IsColimit.ofIsoColimit h3 e2_iso

  exact ⟨h_final⟩

/-- Van Kampen in opensLeCover form. -/
theorem vanKampen_opensLeCover :
    Nonempty (IsColimit ((πₒ X).mapCocone
      (TopCat.Presheaf.SheafCondition.opensLeCoverCocone U))) := by
  let V : Opens X := iSup U
  let 𝒰 : Set (Opens X) := coverSet U
  have h_le : ∀ W ∈ 𝒰, W ≤ V := by
    intro W hW
    rcases hW with ⟨i, hi⟩
    exact le_trans hi (le_iSup U i)
  have hcover : ∀ x ∈ V, ∃ W ∈ 𝒰, x ∈ W := by
    intro x hx
    have h1 : x ∈ iSup U := hx
    rw [Opens.mem_iSup] at h1
    rcases h1 with ⟨i, hi⟩
    refine' ⟨U i, ⟨i, le_refl (U i)⟩, hi⟩
  have hfi : ∀ s : Finset (Opens X), s.Nonempty → (∀ W ∈ s, W ∈ 𝒰) → s.inf (fun W => W) ∈ 𝒰 := by
    intro s hs_nonempty hs
    exact opensLeCover_closedUnderFiniteIntersections U s hs_nonempty hs
  have h1 : Nonempty (IsColimit (mkSubtypeCocone X V 𝒰 h_le)) :=
    relative_vanKampen_subtype V 𝒰 h_le hcover hfi
  have hV : V = iSup U := by rfl
  exact transport_index_equiv X U V h_le hV h1

end VanKampenTransport

namespace IsSheafBridge

open FundamentalGroupoid

variable (X : TopCat.{u})

/-- Bridge: Van Kampen colimit ⇒ IsSheafOpensLeCover for (πₒ X).op. -/
theorem isSheafOpensLeCover_of_vanKampen
    (h_vk : ∀ {ι : Type u} (U : ι → Opens X),
      Nonempty (IsColimit ((πₒ X).mapCocone
        (TopCat.Presheaf.SheafCondition.opensLeCoverCocone U)))) :
    TopCat.Presheaf.IsSheafOpensLeCover ((πₒ X).op) := by
  intro ι U
  have h1 : Nonempty (IsColimit ((πₒ X).mapCocone
      (TopCat.Presheaf.SheafCondition.opensLeCoverCocone U))) := h_vk U
  rcases h1 with ⟨h_colim⟩
  have h2 : IsLimit (((πₒ X).op).mapCone
      (TopCat.Presheaf.SheafCondition.opensLeCoverCocone U).op) :=
    h_colim.op
  exact ⟨h2⟩

/-- Main bridge: Van Kampen ⇒ IsSheaf. -/
theorem isSheaf_of_vanKampen
    (h_vk : ∀ {ι : Type u} (U : ι → Opens X),
      Nonempty (IsColimit ((πₒ X).mapCocone
        (TopCat.Presheaf.SheafCondition.opensLeCoverCocone U)))) :
    TopCat.Presheaf.IsSheaf ((πₒ X).op) := by
  have h1 : TopCat.Presheaf.IsSheafOpensLeCover ((πₒ X).op) :=
    isSheafOpensLeCover_of_vanKampen X h_vk
  have h2 : TopCat.Presheaf.IsSheaf ((πₒ X).op) :=
    (TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover ((πₒ X).op)).mpr h1
  exact h2

end IsSheafBridge

namespace FundamentalGroupoid

variable {X : TopCat.{u}}
variable {ι : Type u} (U : ι → Opens X)

/-- The **van Kampen theorem**: the fundamental groupoid functor is a cosheaf. -/
theorem isSheaf_op_opensToGrpd : TopCat.Presheaf.IsSheaf (πₒ X).op := by
  have h_vk : ∀ {ι : Type u} (U : ι → Opens X),
      Nonempty (IsColimit ((πₒ X).mapCocone
        (TopCat.Presheaf.SheafCondition.opensLeCoverCocone U))) := by
    intro ι U
    exact VanKampenTransport.vanKampen_opensLeCover X U
  exact IsSheafBridge.isSheaf_of_vanKampen X h_vk

end FundamentalGroupoid

end

end
