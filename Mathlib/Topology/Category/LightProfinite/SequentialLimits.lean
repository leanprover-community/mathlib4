import Mathlib.Topology.Category.LightProfinite.EffectiveEpi
import Mathlib.Topology.Category.LightProfinite.Reindex
import Mathlib.Topology.Category.LightProfinite.Subcategory

open CategoryTheory Limits

namespace LightProfinite

universe u

variable {X Y : LightProfinite.{u}} (f : X ⟶ Y)

abbrev levelMap
    (f : (n : ℕ) → X.diagram.obj ⟨n⟩ ⟶ Y.diagram.obj ⟨n⟩)
    (w : ∀ n, f (n + 1) ≫ Y.transitionMap n = X.transitionMap n ≫ f n) : X ⟶ Y := by
  apply homMk fun n ↦ X.proj n ≫ fintypeCatToLightProfinite.map (f n)
  intro n
  ext x
  replace w := congrFun (w n) (X.proj (n + 1) x)
  simp at w
  simp
  erw [w, CategoryTheory.comp_apply, ← proj_comp_transitionMap _ n]
  rfl

lemma levelMap_w (f : (n : ℕ) → X.diagram.obj ⟨n⟩ ⟶ Y.diagram.obj ⟨n⟩)
    (w : ∀ n, f (n + 1) ≫ Y.transitionMap n = X.transitionMap n ≫ f n) (n : ℕ) :
    levelMap f w ≫ Y.proj n = X.proj n ≫ fintypeCatToLightProfinite.map (f n) := by
  erw [Y.isLimit.fac]
  rfl

structure levelRepresentation : Type (u + 1) where
  left : LightProfinite
  right : LightProfinite
  leftIso : left ≅ X
  rightIso : right ≅ Y
  map (n : ℕ) : left.diagram.obj ⟨n⟩ ⟶ right.diagram.obj ⟨n⟩
  w (n : ℕ) : map (n+1) ≫ right.transitionMap n = left.transitionMap n ≫ map n
  w' : levelMap map w ≫ rightIso.hom = leftIso.hom ≫ f

class IsLevelRepresentation {Z W : LightProfinite} (g : Z ⟶ W) (i₁ : Z ≅ X) (i₂ : W ≅ Y)
    (map : (n : ℕ) → Z.diagram.obj ⟨n⟩ ⟶ W.diagram.obj ⟨n⟩) : Prop where
  w : ∀ n, map (n+1) ≫ W.transitionMap n = Z.transitionMap n ≫ map n
  w' : levelMap map w ≫ i₂.hom = i₁.hom ≫ f

lemma isLevelRepresentation_w {Z W : LightProfinite} (g : Z ⟶ W) (i₁ : Z ≅ X) (i₂ : W ≅ Y)
    (map : (n : ℕ) → Z.diagram.obj ⟨n⟩ ⟶ W.diagram.obj ⟨n⟩)
    [h : IsLevelRepresentation f g i₁ i₂ map]
    (n : ℕ) : map (n + 1) ≫ transitionMap W n = transitionMap Z n ≫ map n :=
  h.w n

lemma isLevelRepresentation_w' {Z W : LightProfinite} (g : Z ⟶ W) (i₁ : Z ≅ X) (i₂ : W ≅ Y)
    (map : (n : ℕ) → Z.diagram.obj ⟨n⟩ ⟶ W.diagram.obj ⟨n⟩)
    [h : IsLevelRepresentation f g i₁ i₂ map] :
    levelMap map (isLevelRepresentation_w f g i₁ i₂ map) ≫ i₂.hom = i₁.hom ≫ f :=
  h.w'

@[simps]
def levelRepresentation.mk' {Z W : LightProfinite} (g : Z ⟶ W) (i₁ : Z ≅ X) (i₂ : W ≅ Y)
    (map : (n : ℕ) → Z.diagram.obj ⟨n⟩ ⟶ W.diagram.obj ⟨n⟩) [IsLevelRepresentation f g i₁ i₂ map] :
    levelRepresentation f where
  w := isLevelRepresentation_w f g i₁ i₂ map
  w' := isLevelRepresentation_w' f g i₁ i₂ map

variable (M : ℕᵒᵖ ⥤ LightProfinite.{u})

structure levelRepresentationDiagram : Type (u + 1) where
  left : ℕᵒᵖ ⥤ LightProfinite.{u}
  iso (n : ℕ) : left.obj ⟨n⟩ ≅ M.obj ⟨n⟩
  map (n m : ℕ) : (left.obj ⟨n+1⟩).diagram.obj ⟨m⟩ → (left.obj ⟨n⟩).diagram.obj ⟨m⟩
  w (n m : ℕ) : (left.obj ⟨n+1⟩).proj m ≫ fintypeCatToLightProfinite.map (map n m) =
      left.map (homOfLE (Nat.le_succ n)).op ≫ (left.obj ⟨n⟩).proj m
  rep (n : ℕ): IsLevelRepresentation (M.map (homOfLE (Nat.le_succ n)).op)
      (left.map (homOfLE (Nat.le_succ n)).op) (iso (n + 1)) (iso n) (map n)

class IsLevelRepresentationDiagram (L : ℕᵒᵖ ⥤ LightProfinite) (i : (n : ℕ) → L.obj ⟨n⟩ ≅ M.obj ⟨n⟩)
    (map : (n m : ℕ) → (L.obj ⟨n+1⟩).diagram.obj ⟨m⟩ → (L.obj ⟨n⟩).diagram.obj ⟨m⟩) : Prop where
  w (n m : ℕ) : (L.obj ⟨n+1⟩).proj m ≫ fintypeCatToLightProfinite.map (map n m) =
      L.map (homOfLE (Nat.le_succ n)).op ≫ (L.obj ⟨n⟩).proj m
  rep (n : ℕ) : IsLevelRepresentation (M.map (homOfLE (Nat.le_succ n)).op)
      (L.map (homOfLE (Nat.le_succ n)).op) (i (n + 1)) (i n) (map n)

attribute [instance] IsLevelRepresentationDiagram.rep

variable (L : ℕᵒᵖ ⥤ LightProfinite) (i : (n : ℕ) → L.obj ⟨n⟩ ≅ M.obj ⟨n⟩)
    (map : (n m : ℕ) → (L.obj ⟨n+1⟩).diagram.obj ⟨m⟩ ⟶ (L.obj ⟨n⟩).diagram.obj ⟨m⟩)
    [h : IsLevelRepresentationDiagram M L i map]

lemma isLevelRepresentationDiagram_w (n m : ℕ) :
    (L.obj ⟨n+1⟩).proj m ≫ fintypeCatToLightProfinite.map (map n m) =
    L.map (homOfLE (Nat.le_succ n)).op ≫ (L.obj ⟨n⟩).proj m :=
  h.w n m

lemma isLevelRepresentationDiagram_w_w (n m : ℕ) :
    map n (m + 1) ≫ (L.obj ⟨n⟩).transitionMap m = (L.obj ⟨n+1⟩).transitionMap m ≫ map n m :=
  (isLevelRepresentation_w (M.map (homOfLE (Nat.le_succ n)).op)
    (L.map (homOfLE (Nat.le_succ n)).op) (i (n + 1)) (i n) (map n) m)

@[simps]
def levelRepresentationDiagram.mk' : levelRepresentationDiagram M where
  left := L
  iso := i
  map := map
  w := isLevelRepresentationDiagram_w M L i map
  rep := inferInstance

def iso_of_isLevelRepresentation : L ≅ M where
  hom := natTrans_nat_op_mk (fun n ↦ (i n).hom) (by
    intro n
    have : IsLevelRepresentation (M.map (homOfLE (Nat.le_succ n)).op)
      (L.map (homOfLE (Nat.le_succ n)).op) (i (n + 1)) (i n) (map n) := inferInstance
    have w' := this.w'
    have h : IsLevelRepresentationDiagram M L i map := inferInstance
    erw [← w']
    congr
    apply (_ : LightProfinite).isLimit.hom_ext
    intro ⟨m⟩
    erw [levelMap_w, h.w]
    rfl)
  inv := natTrans_nat_op_mk (fun n ↦ (i n).inv) (by
    intro n
    have : IsLevelRepresentation (M.map (homOfLE (Nat.le_succ n)).op)
      (L.map (homOfLE (Nat.le_succ n)).op) (i (n + 1)) (i n) (map n) := inferInstance
    have w' := this.w'
    rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv] at w'
    have h : IsLevelRepresentationDiagram M L i map := inferInstance
    erw [← w']
    congr
    apply (_ : LightProfinite).isLimit.hom_ext
    intro ⟨m⟩
    erw [levelMap_w, h.w]
    rfl)

def functor : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ FintypeCat :=
  Nat.functor_mk (fun n ↦ (L.obj ⟨n⟩).diagram)
    fun n ↦ natTrans_nat_op_mk (map n ·)
      fun m ↦ (isLevelRepresentationDiagram_w_w M L i map n m).symm

def functor' : ℕᵒᵖ × ℕᵒᵖ ⥤ FintypeCat :=
  uncurry.obj (functor M L i map)

def limitFunctor : ℕᵒᵖ ⥤ FintypeCat :=
  Nat.op_diagonal ⋙ functor' M L i map

noncomputable section

lemma hom_ext {X Y : LightProfinite} (f g : X ⟶ Y) (h : ∀ n, f ≫ Y.proj n = g ≫ Y.proj n) :
    f = g := Y.isLimit.hom_ext fun ⟨n⟩ ↦ h n

@[simp]
lemma homMk_comp_proj {X Y : LightProfinite} (f : (n : ℕ) → X ⟶ Y.component n)
    (w : ∀ n, Y.transitionMap n ∘ f (n + 1) = f n) (n : ℕ) : homMk f w ≫ Y.proj n = f n := by
  erw [Y.isLimit.fac]
  rfl

def limitCone : Cone L where
  pt := of <| limitFunctor M L i map
  π := by
    refine natTrans_nat_op_mk ?_ ?_
    · intro n
      refine homMk ?_ ?_
      · intro m
        exact (_ : LightProfinite).proj (max m n) ≫
          fintypeCatToLightProfinite.map
            (compose_n (fun k ↦ (L.obj ⟨k⟩).diagram.obj ⟨max m n⟩) (fun k ↦ map k (max m n))
              (le_max_right _ _) ≫
            transitionMapLE _ (le_max_left m n))
      · sorry
    · intro m
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Nat.op_diagonal_obj,
        Functor.map_comp, Category.id_comp]
      apply LightProfinite.hom_ext
      intro k
      simp only [Functor.const_obj_obj, Nat.op_diagonal_obj, homMk_comp_proj, Category.assoc]
      erw [← isLevelRepresentationDiagram_w M L i map]
      symm
      rw [← Category.assoc]
      simp
      sorry



def index {X Y : LightProfinite.{u}} (f : X ⟶ Y) (n : ℕ) : ℕ :=
  let g := locallyConstant_of_hom f n
  have := Profinite.exists_locallyConstant X.cone X.isLimit g
  max n this.choose.unop

def component_map {X Y : LightProfinite.{u}} (f : X ⟶ Y) (n : ℕ) :
    X.diagram.obj ⟨index f n⟩ ⟶ Y.diagram.obj ⟨n⟩ :=
  let g := locallyConstant_of_hom f n
  have := Profinite.exists_locallyConstant X.cone X.isLimit g
  X.transitionMapLE (le_max_right _ _) ≫ this.choose_spec.choose.toFun

def index_seq : ℕ → ℕ := by
  intro n
  induction n with
  | zero => exact index (M.map (homOfLE (Nat.le_succ 0)).op) 0
  | succ n ih => exact index (M.map (homOfLE (Nat.le_succ n)).op) ih

def index_seq' (n : ℕ) : ℕ → ℕ := by
  induction n with
  | zero => exact index (M.map (homOfLE (Nat.le_succ 0)).op)
  | succ n ih => exact fun m ↦ index (M.map (homOfLE (Nat.le_succ n)).op) <| ih m

lemma index_seq_monotone : Monotone (index_seq M) := sorry

def stepMap (n : ℕ) : (M.obj ⟨n+1⟩).diagram.obj ⟨index_seq M (n+1)⟩ ⟶
    (M.obj ⟨n⟩).diagram.obj ⟨index_seq M n⟩ :=
  component_map (M.map (homOfLE _).op) _

def cofinal_M : ℕᵒᵖ ⥤ LightProfinite.{u} :=
  (Nat.functor_mk' (index_seq M) fun n ↦ homOfLE (index_seq_monotone _ (Nat.le_succ n))).op ⋙ M

def stepMap' (n m : ℕ) : (M.obj ⟨n+1⟩).diagram.obj ⟨index_seq' M (n+1) m⟩ ⟶
    (M.obj ⟨n⟩).diagram.obj ⟨index_seq' M n m⟩ :=
  component_map (M.map (homOfLE _).op) _

def stepMap₂ (n m : ℕ) : (M.obj ⟨n⟩).diagram.obj ⟨index_seq' M n (m+1)⟩ ⟶
    (M.obj ⟨n⟩).diagram.obj ⟨index_seq' M n m⟩ := by
  refine (_ : LightProfinite).transitionMapLE ?_
  induction n with
  | zero => sorry
  | succ n ih => sorry

def stepMap'' (n m : ℕ) : (M.obj ⟨n+1⟩).diagram.obj ⟨index_seq' M (n+1) (m+1)⟩ ⟶
    (M.obj ⟨n⟩).diagram.obj ⟨index_seq' M n m⟩ :=
  (_ : LightProfinite).transitionMapLE sorry ≫ stepMap' M n m

#exit

def limitCone : Cone M where
  pt := of (Nat.functor_mk (fun n ↦ (M.obj ⟨n⟩).diagram.obj ⟨(index_seq' M n n)⟩) (fun n ↦ stepMap'' M n n))
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
