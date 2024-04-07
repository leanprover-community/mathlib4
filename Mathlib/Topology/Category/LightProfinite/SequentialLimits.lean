import Mathlib.Topology.Category.LightProfinite.Subcategory
import Mathlib.Topology.Category.LightProfinite.EffectiveEpi

open CategoryTheory Limits

namespace LightProfinite

variable (M : ℕᵒᵖ ⥤ LightProfinite)

noncomputable def index {X Y : LightProfinite} (f : X ⟶ Y) (n : ℕ) : ℕ :=
  let g := locallyConstant_of_hom f n
  have := Profinite.exists_locallyConstant X.cone X.isLimit g
  max n this.choose.unop

noncomputable def component_map {X Y : LightProfinite} (f : X ⟶ Y) (n : ℕ) :
    X.diagram.obj ⟨index f n⟩ ⟶ Y.diagram.obj ⟨n⟩ :=
  let g := locallyConstant_of_hom f n
  have := Profinite.exists_locallyConstant X.cone X.isLimit g
  X.transitionMapLE (le_max_right _ _) ≫ this.choose_spec.choose.toFun

noncomputable def index_seq : ℕ → ℕ := by
  intro n
  induction n with
  | zero => exact index (M.map (homOfLE (Nat.le_succ 0)).op) 0
  | succ n ih => exact index (M.map (homOfLE (Nat.le_succ n)).op) ih

lemma index_seq_monotone : Monotone (index_seq M) := sorry

section

variable {C : Type*} [Category C]

def compose_n (f : ℕ → C) (h : (n : ℕ) → f (n + 1) ⟶ f n) {n m : ℕ}
    (hh : n ≤ m) : f m ⟶ f n :=
  Nat.leRecOn hh (fun g ↦ h _ ≫ g) (𝟙 _)

lemma compose_n_id (f : ℕ → C) (h : (n : ℕ) → f (n + 1) ⟶ f n) (n : ℕ) :
    compose_n f h (le_refl n) = 𝟙 _ :=
  Nat.leRecOn_self _

lemma compose_n_trans (f : ℕ → C) (h : (n : ℕ) → f (n + 1) ⟶ f n) {n m k : ℕ} (h₁ : n ≤ m)
    (h₂ : m ≤ k) :
    compose_n f h (h₁.trans h₂) = compose_n f h h₂ ≫ compose_n f h h₁ := by
  induction h₂ with
  | refl =>
    simp [compose_n, Nat.leRecOn_self _]
  | @step p h₂ ih =>
    rw [compose_n, Nat.leRecOn_succ (h₁.trans h₂)]
    simp only [compose_n] at ih
    rw [ih, compose_n, compose_n, ← Category.assoc]
    congr
    exact (Nat.leRecOn_succ _ _).symm

@[simps!]
def Nat.functor_mk (f : ℕ → C) (h : (n : ℕ) → f (n + 1) ⟶ f n) :
    ℕᵒᵖ ⥤ C where
  obj n := f n.unop
  map := @fun ⟨_⟩ ⟨_⟩ ⟨⟨⟨hh⟩⟩⟩ ↦ compose_n f h hh
  map_id _ := compose_n_id _ _ _
  map_comp _ _ := compose_n_trans _ _ _ _

def compose_n' (f : ℕ → C) (h : (n : ℕ) → f n ⟶ f (n + 1)) {n m : ℕ}
    (hh : n ≤ m) : f n ⟶ f m :=
  Nat.leRecOn hh (fun g ↦ g ≫ h _) (𝟙 _)

lemma compose_n_id' (f : ℕ → C) (h : (n : ℕ) → f n ⟶ f (n + 1)) (n : ℕ) :
    compose_n' f h (le_refl n) = 𝟙 _ :=
  Nat.leRecOn_self _

lemma compose_n_trans' (f : ℕ → C) (h : (n : ℕ) → f n ⟶ f (n + 1)) {n m k : ℕ} (h₁ : n ≤ m)
    (h₂ : m ≤ k) :
    compose_n' f h (h₁.trans h₂) = compose_n' f h h₁ ≫ compose_n' f h h₂ := by
  sorry
  -- induction h₁ with
  -- | refl =>
  --   simp [compose_n', Nat.leRecOn_self _]
  -- | @step p h₁ ih =>
  --   rw [compose_n', Nat.leRecOn_succ (h₁.trans h₂)]
  --   simp only [compose_n'] at ih
  --   rw [ih, compose_n', compose_n', Category.assoc]
  --   congr
  --   convert (Nat.leRecOn_succ h₂ _).symm

@[simps!]
def Nat.functor_mk' (f : ℕ → C) (h : (n : ℕ) → f n ⟶ f (n + 1)) :
    ℕ ⥤ C where
  obj n := f n
  map := @fun _ _ ⟨⟨hh⟩⟩ ↦ compose_n' f h hh
  map_id _ := compose_n_id' _ _ _
  map_comp _ _ := compose_n_trans' _ _ _ _

end

noncomputable def stepMap (n : ℕ) : (M.obj ⟨n+1⟩).diagram.obj ⟨index_seq M (n+1)⟩ ⟶
    (M.obj ⟨n⟩).diagram.obj ⟨index_seq M n⟩ :=
  component_map (M.map (homOfLE _).op) _

noncomputable def cofinal_M : ℕᵒᵖ ⥤ LightProfinite :=
  (Nat.functor_mk' (index_seq M) fun n ↦ homOfLE (index_seq_monotone _ (Nat.le_succ n))).op ⋙ M

noncomputable def stepMap' (n m : ℕ) : (M.obj ⟨n+1⟩).diagram.obj ⟨index_seq M (m+1)⟩ ⟶
    (M.obj ⟨n⟩).diagram.obj ⟨index_seq M m⟩ := by
  let f := component_map (M.map (homOfLE (Nat.le_succ n)).op) m
  simp [index_seq]
  sorry

noncomputable def limitCone : Cone M where
  pt := of (Nat.functor_mk (fun n ↦ (M.obj ⟨n⟩).diagram.obj ⟨(index_seq M n)⟩) (stepMap M))
  -- pt := {
  --   diagram := Nat.functor_mk (fun n ↦ (M.obj ⟨n⟩).diagram.obj ⟨(index_seq M n)⟩) (stepMap M)
  --   cone := sorry
  --   isLimit := sorry
  -- }
  π := {
    app := fun ⟨n⟩ ↦ (by
      simp [of]
      sorry
      )
    naturality := sorry
  }
    -- let α := (limit.cone ((Nat.functor_mk (fun n ↦ (M.obj ⟨n⟩).diagram.obj ⟨(index_seq M n)⟩)
    --   (stepMap M)) ⋙ FintypeCat.toProfinite)).π



#exit

noncomputable def functor : ℕᵒᵖ × ℕᵒᵖ ⥤ FintypeCat where
  obj n := (M.obj n.1).diagram.obj ⟨(index (M.map (homOfLE (Nat.le_succ n.1.unop)).op) n.2.unop)⟩
  map := sorry
  map_id := sorry
  map_comp := sorry
  -- obj n := ((M ⋙ toSurj).obj n.1).diagram.obj n.2
  -- map f := ((M ⋙ toSurj).obj _).diagram.map f.2 ≫ (component_map (M.map f.1) _)

noncomputable
def component_map {X Y : LightProfinite} (f : X ⟶ Y) (n : ℕ) :
    (toSurj.obj X).diagram.obj ⟨n⟩ ⟶ (toSurj.obj Y).diagram.obj ⟨n⟩ :=
  let g := locallyConstant_of_hom (toSurj.map f) n
  have := Profinite.exists_locallyConstant (toSurj.obj X).cone (toSurj.obj X).isLimit g
  let m := this.choose.unop
  let g' : LocallyConstant ((toSurj.obj X).component m) ((toSurj.obj Y).component n) :=
    this.choose_spec.choose
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
  sorry -- not true

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
  · simp only [Functor.map_comp]
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

-- This definition won't work...
noncomputable def functor : ℕᵒᵖ × ℕᵒᵖ ⥤ FintypeCat where
  obj n := ((M ⋙ toSurj).obj n.1).diagram.obj n.2
  map f := ((M ⋙ toSurj).obj _).diagram.map f.2 ≫ (component_map (M.map f.1) _)
  map_comp f g := by
    have : (component_map (M.map f.1) _) ≫ ((M ⋙ toSurj).obj _).diagram.map g.2 =
        ((M ⋙ toSurj).obj _).diagram.map g.2 ≫ (component_map (M.map f.1) _) := component_map_w _ _
    simp only [Functor.comp_obj, prod_Hom, prod_comp, Functor.map_comp, component_map_comp,
      Category.assoc]
    rw [reassoc_of% this]

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
