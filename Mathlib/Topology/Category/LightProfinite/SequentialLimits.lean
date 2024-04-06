import Mathlib.Topology.Category.LightProfinite.Subcategory
import Mathlib.Topology.Category.LightProfinite.EffectiveEpi

open CategoryTheory Limits

namespace LightProfinite

variable (M : ℕᵒᵖ ⥤ LightProfinite)

noncomputable
def component_map {X Y : LightProfinite} (f : X ⟶ Y) (n : ℕ) :
    (toSurj.obj X).diagram.obj ⟨n⟩ ⟶ (toSurj.obj Y).diagram.obj ⟨n⟩ :=
  let g := locallyConstant_of_hom (toSurj.map f) n
  have := Profinite.exists_locallyConstant (toSurj.obj X).cone (toSurj.obj X).isLimit g
  let m := this.choose.unop
  let g' : LocallyConstant ((toSurj.obj X).component m) ((toSurj.obj Y).component n) :=
    this.choose_spec.choose
  -- have h : g = g'.comap (X.obj.proj m) := this.choose_spec.choose_spec
  if hh : m ≤ n then
    (toSurj.obj X).transitionMapLE hh ≫ g'.1 else
    (section_ ((toSurj.obj X).transitionMapLE
      (le_of_lt (by simpa using hh)))) ≫ g'.1

instance (X : LightProfinite) (n : ℕ) : Epi <| (toSurj.obj X).proj n := by
  rw [LightProfinite.epi_iff_surjective]
  exact X.proj_surjective' _

lemma hom_ext_ish (X : LightProfinite) (n : ℕ) (Y : FintypeCat)
    (f g : (toSurj.obj X).diagram.obj ⟨n⟩ ⟶ Y)
    (h : (toSurj.obj X).proj n ≫ fintypeCatToLightProfinite.map f =
      (toSurj.obj X).proj n ≫ fintypeCatToLightProfinite.map g) : f = g := by
  apply fintypeCatToLightProfinite.map_injective
  rwa [cancel_epi] at h

lemma comp_eq_of_comap_eq {X Y : LightProfinite} {Z : FintypeCat} (f : X ⟶ Y)
    (g₁ : LocallyConstant X Z.toLightProfinite) (g₂ : LocallyConstant Y Z.toLightProfinite)
    (h : g₂.comap f = g₁) :
    f ≫ (⟨g₂.1, g₂.2.continuous⟩ : Y ⟶ Z.toLightProfinite) = ⟨g₁.1, g₁.2.continuous⟩ := by
  ext x
  change g₂.1 (f x) = g₁.1 x
  rw [← LocallyConstant.coe_inj] at h
  simp only [concreteCategory_forget_obj, LocallyConstant.toFun_eq_coe]
  erw [← congrFun h x]
  exact (LocallyConstant.coe_comap_apply _ _ f.continuous _).symm

lemma component_map_eq_of_bla {X Y : LightProfinite} {n : ℕ}
    (f : X ⟶ Y)
    (g : (toSurj.obj X).diagram.obj ⟨n⟩ ⟶ (toSurj.obj Y).diagram.obj ⟨n⟩)
    (h : (toSurj.obj X).proj n ≫ fintypeCatToLightProfinite.map g = f ≫ (toSurj.obj Y).proj n) :
    component_map f n = g := by
  let g'' := locallyConstant_of_hom (toSurj.map f) n
  have := Profinite.exists_locallyConstant (toSurj.obj X).cone (toSurj.obj X).isLimit g''
  let m := this.choose.unop
  let g' : LocallyConstant ((toSurj.obj X).component m) ((toSurj.obj Y).component n) :=
    this.choose_spec.choose
  have hhh : g'' = g'.comap ((toSurj.obj X).proj m) := this.choose_spec.choose_spec
  simp only [component_map]
  split_ifs with hh
  · apply hom_ext_ish
    suffices proj (toSurj.obj X) n ≫ transitionMapLE' (toSurj.obj X) hh ≫ ⟨g'.1, g'.2.continuous⟩ =
        proj (toSurj.obj X) n ≫ fintypeCatToLightProfinite.map g by exact this
    rw [reassoc_of% proj_comp_transitionMapLE', comp_eq_of_comap_eq _ _ _ hhh.symm, h]
    rfl
  · have hh' : n ≤ m := le_of_lt (by simpa using hh)
    rw [← Category.id_comp g, ← IsSplitEpi.id (transitionMapLE (toSurj.obj X) hh'), Category.assoc]
    congr
    apply hom_ext_ish
    simp [-toSurj_obj]
    suffices proj (toSurj.obj X) m ≫ transitionMapLE' (toSurj.obj X) hh' ≫
        fintypeCatToLightProfinite.map g =
        proj (toSurj.obj X) m  ≫ ⟨g'.1, g'.2.continuous⟩ by exact this.symm
    rw [← Category.assoc, proj_comp_transitionMapLE', comp_eq_of_comap_eq _ _ _ hhh.symm, h]
    rfl

@[simp]
lemma component_map_id (X : LightProfinite) (n : ℕ) : component_map (𝟙 X) n = 𝟙 _ := by
  apply component_map_eq_of_bla
  rfl

lemma component_map_w {X Y : LightProfinite} (f : X ⟶ Y) {n m : ℕ} (h : n ≤ m) :
    component_map f m ≫ (toSurj.obj Y).diagram.map ⟨(homOfLE h)⟩ =
    (toSurj.obj X).diagram.map ⟨(homOfLE h)⟩ ≫ component_map f n := sorry

lemma proj_comp_section_transitionMapLE' (S : LightProfinite) {n m : ℕ} (h : n ≤ m) :
    (toSurj.obj S).proj n ≫ fintypeCatToLightProfinite.map
      (section_ ((toSurj.obj S).transitionMapLE h)) =
        (toSurj.obj S).proj m := by
  -- have : Epi (transitionMapLE' (toSurj.obj S) h) := sorry
  -- have : (toSurj.obj S).proj n ≫ fintypeCatToLightProfinite.map
  --     (section_ ((toSurj.obj S).transitionMapLE h)) ≫ transitionMapLE' (toSurj.obj S) h =
  --     (toSurj.obj S).proj m ≫ transitionMapLE' (toSurj.obj S) h := sorry
  rw [← Category.comp_id (proj (toSurj.obj S) m)]
  change _ = _ ≫ 𝟙 (fintypeCatToLightProfinite.obj _)
  sorry
  -- rw [← fintypeCatToLightProfinite.map_id, ← IsSplitEpi.id (transitionMapLE (toSurj.obj S) h)]
  -- rw [← Category.assoc, cancel_epi (transitionMapLE' (toSurj.obj S) h)] at this
  -- erw [← cancel_epi (transitionMapLE' S h)]

lemma component_map_w' {X Y : LightProfinite} (f : X ⟶ Y) (n : ℕ)  :
    (toSurj.obj X).proj n ≫ fintypeCatToLightProfinite.map (component_map f n) =
    f ≫ (toSurj.obj Y).proj n := by
  let g'' := locallyConstant_of_hom (toSurj.map f) n
  have := Profinite.exists_locallyConstant (toSurj.obj X).cone (toSurj.obj X).isLimit g''
  let m := this.choose.unop
  let g' : LocallyConstant ((toSurj.obj X).component m) ((toSurj.obj Y).component n) :=
    this.choose_spec.choose
  have hhh : g'' = g'.comap ((toSurj.obj X).proj m) := this.choose_spec.choose_spec
  have := comp_eq_of_comap_eq _ _ _ hhh.symm
  simp only [component_map]
  split_ifs with hh
  · suffices proj (toSurj.obj X) n ≫ transitionMapLE' (toSurj.obj X) hh ≫ ⟨g'.1, g'.2.continuous⟩ =
        f ≫ proj (toSurj.obj Y) n by exact this
    rw [reassoc_of% proj_comp_transitionMapLE', comp_eq_of_comap_eq _ _ _ hhh.symm]
    rfl
  · have hh' : n ≤ m := le_of_lt (by simpa using hh)
    simp only [Functor.map_comp]
    rw [reassoc_of% proj_comp_section_transitionMapLE']
    change proj _ _ ≫ ⟨g'.1, g'.2.continuous⟩ = _
    rw [comp_eq_of_comap_eq _ _ _ hhh.symm]
    rfl

@[simp]
lemma component_map_comp {X Y Z : LightProfinite} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    component_map (f ≫ g) n = component_map f n ≫ component_map g n := by
  apply component_map_eq_of_bla
  simp only [Functor.map_comp, ← Category.assoc]
  rw [component_map_w' f n]
  erw [Category.assoc, Category.assoc (f := f), component_map_w' g n]

noncomputable def functor : ℕᵒᵖ × ℕᵒᵖ ⥤ FintypeCat where
  obj n := ((M ⋙ toSurj).obj n.1).diagram.obj n.2
  map f := ((M ⋙ toSurj).obj _).diagram.map f.2 ≫ (component_map (M.map f.1) _)
  map_comp f g := by
    have : (component_map (M.map f.1) _) ≫ ((M ⋙ toSurj).obj _).diagram.map g.2 =
        ((M ⋙ toSurj).obj _).diagram.map g.2 ≫ (component_map (M.map f.1) _) := component_map_w _ _
    simp only [Functor.comp_obj, prod_Hom, prod_comp, Functor.map_comp, component_map_comp,
      Category.assoc]
    rw [reassoc_of% this]



#exit

def limitCone : Cone M where
  pt := {
    diagram := {
      obj := fun n ↦ (M.obj n).diagram.obj n
      map := @fun n m f ↦ (by
        --fun f n ↦ (M.obj _).diagram.map f
        simp
        refine (M.obj n).diagram.map f ≫ ?_
        let g := M.map f
        sorry
        )
      map_id := sorry
      map_comp := sorry
    }
    cone := sorry
    isLimit := sorry
  }
  π := sorry
