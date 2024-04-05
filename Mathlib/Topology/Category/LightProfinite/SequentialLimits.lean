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

@[simp]
lemma component_map_id (X : LightProfinite) (n : ℕ) : component_map (𝟙 X) n = 𝟙 _ := by
  let g := locallyConstant_of_hom (toSurj.map (𝟙 X)) n
  have := Profinite.exists_locallyConstant (toSurj.obj X).cone (toSurj.obj X).isLimit g
  let m := this.choose.unop
  let g' : LocallyConstant ((toSurj.obj X).component m) ((toSurj.obj X).component n) :=
    this.choose_spec.choose
  have h : g = g'.comap ((toSurj.obj X).proj m) := this.choose_spec.choose_spec
  rw [← LocallyConstant.coe_inj] at h
  simp only [component_map]
  split_ifs with hh
  · apply hom_ext_ish
    suffices proj (toSurj.obj X) n ≫ transitionMapLE' (toSurj.obj X) hh ≫ ⟨g'.1, g'.2.continuous⟩ =
        proj (toSurj.obj X) n ≫ 𝟙 _ by exact this
    rw [reassoc_of% proj_comp_transitionMapLE']
    ext x
    replace h := congrFun h x
    -- erw [LocallyConstance.coe_comap_apply _ _ _] at h
    sorry
  · sorry

  -- let g := locallyConstant_of_hom (toSurj.map (𝟙 X)) n
  -- have := Profinite.exists_locallyConstant (toSurj.obj X).cone (toSurj.obj X).isLimit g
  -- let m := this.choose.unop
  -- let g' : LocallyConstant ((toSurj.obj X).component m) ((toSurj.obj X).component n) :=
  --   this.choose_spec.choose
  -- have h : g = g'.comap ((toSurj.obj X).proj m) := this.choose_spec.choose_spec
  -- ext x
  -- simp only [component_map, Functor.comp_obj, FintypeCat.toProfinite_obj_toCompHaus_toTop_α,
  --   Functor.const_obj_obj, LocallyConstant.toFun_eq_coe, id_eq, FintypeCat.id_apply]
  -- split_ifs with hh
  -- · obtain ⟨y, hy⟩ := X.proj_surjective' n x
  --   rw [← LocallyConstant.coe_inj] at h
  --   have hhh := congrFun h y
  --   erw [LocallyConstant.coe_comap_apply _ _ (_ : (_ : LightProfinite) ⟶ _).continuous,
  --     ← (toSurj.obj X).proj_comp_transitionMapLE'' hh] at hhh
  --   rw [← hy]
  --   exact hhh.symm
  -- · change g' _ = x
  --   have hh' : n ≤ m := le_of_lt (by simpa using hh)
  --   apply ConcreteCategory.injective_of_mono_of_preservesPullback
  --       (section_ ((toSurj.obj X).transitionMapLE hh'))
  --   obtain ⟨y, hy⟩ := X.proj_surjective' m (section_ (transitionMapLE _ hh') x)
  --   rw [← LocallyConstant.coe_inj] at h
  --   have hhh := congrFun h y
  --   erw [LocallyConstant.coe_comap_apply _ _ (_ : (_ : LightProfinite) ⟶ _).continuous,
  --     ← (toSurj.obj X).proj_comp_transitionMapLE'' (le_of_lt (by simpa using hh))] at hhh
  --   simp at hhh hy
  --   erw [hy] at hhh
  --   simp
  --   rw [← hhh]
  --   have := congrFun (IsSplitEpi.id ((toSurj.obj X).transitionMapLE hh')) x
  --   simp at this
  --   rw [this]

  -- apply hom_ext_ish
  -- ext x
  -- rw [← LocallyConstant.coe_inj] at h
  -- exact congrFun h x


@[simp]
lemma component_map_comp {X Y Z : LightProfinite} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    component_map (f ≫ g) n = component_map f n ≫ component_map g n := by
  ext x
  simp only [component_map]
  split_ifs
  all_goals sorry

lemma component_map_w {X Y : LightProfinite} (f : X ⟶ Y) {n m : ℕ} (h : n ≤ m) :
    component_map f m ≫ (toSurj.obj Y).diagram.map ⟨(homOfLE h)⟩ =
    (toSurj.obj X).diagram.map ⟨(homOfLE h)⟩ ≫ component_map f n := sorry

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
