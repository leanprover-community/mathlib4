import Mathlib

open CategoryTheory Limits AlgebraicTopology SimplicialObject
  Simplicial

universe u w

variable {C : Type*} [Category* C] (X : SimplicialObject C) (K : SSet.{w})

namespace CategoryTheory

lemma uliftYonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Cᵒᵖ ⥤ Type (max w _))
    (x : F.obj ⟨X⟩) :
    uliftYoneda.{w}.map f ≫ uliftYonedaEquiv.{w}.symm x =
      uliftYonedaEquiv.{w}.symm ((F.map f.op) x) := by
  apply uliftYonedaEquiv.injective
  simp [uliftYonedaEquiv]

end CategoryTheory

namespace SSet

variable {K} in
noncomputable def N.Hom.hom {x y : K.N} (f : x ⟶ y) : ⦋x.dim⦌ ⟶ ⦋y.dim⦌ :=
  (SSet.N.le_iff_exists_mono.mp <| leOfHom f).choose

variable {K} in
instance {x y : K.N} (f : x ⟶ y) : Mono (N.Hom.hom f) :=
  (SSet.N.le_iff_exists_mono.mp <| leOfHom f).choose_spec.choose

variable {K} in
@[simp]
lemma N.Hom.hom_spec {x y : K.N} (f : x ⟶ y) : K.map (N.Hom.hom f).op y.simplex = x.simplex :=
  (SSet.N.le_iff_exists_mono.mp <| leOfHom f).choose_spec.choose_spec

class Nonsingular (K : SSet.{u}) : Prop where
  mono_of_mem_nonDegenerate {n : ℕ} (x : K _⦋n⦌) (hx : x ∈ K.nonDegenerate n) :
    Mono (yonedaEquiv.symm x)

abbrev nonDegenerateElements : ObjectProperty K.Elements :=
  fun x ↦ x.snd ∈ K.nonDegenerate _

lemma ext_of_nonsingular [K.Nonsingular] {n : ℕ} (x : K _⦋n⦌) (hx : x ∈ K.nonDegenerate n)
    {m : SimplexCategory} {f g : m ⟶ ⦋n⦌} (h : K.map f.op x = K.map g.op x) : f = g := by
  have : Mono (uliftYonedaEquiv.symm x) := Nonsingular.mono_of_mem_nonDegenerate _ hx
  apply uliftYoneda.map_injective
  rw [← cancel_mono (uliftYonedaEquiv.symm x)]
  simp [uliftYonedaEquiv_symm_naturality_left, congr(uliftYonedaEquiv.symm $h)]

instance [K.Nonsingular] : Quiver.IsThin K.nonDegenerateElements.FullSubcategory := by
  intro x ⟨⟨⟨⟨n⟩⟩, val⟩, hy⟩
  refine ⟨fun f g ↦ ?_⟩
  ext : 2
  exact Opposite.unop_injective <| ext_of_nonsingular K _ x.property (f.1.2.trans g.1.2.symm)

@[ext (iff := false)]
lemma N.Hom.ext [K.Nonsingular] {x y : K.N} {f g : ⦋x.dim⦌ ⟶ ⦋y.dim⦌}
    (hf : K.map f.op y.simplex = x.simplex) (hg : K.map g.op y.simplex = x.simplex) :
    f = g := by
  apply ext_of_nonsingular K y.simplex y.2
  rw [hf, hg]

variable {K} in
@[reassoc (attr := simp)]
lemma N.Hom.hom_comp [K.Nonsingular] {x y z : K.N} (f : x ⟶ y) (g : y ⟶ z) :
    N.Hom.hom (f ≫ g) = N.Hom.hom f ≫ N.Hom.hom g := by
  cat_disch

variable {K} in
@[reassoc (attr := simp)]
lemma N.Hom.hom_id [K.Nonsingular] (x : K.N) :
    N.Hom.hom (𝟙 x) = 𝟙 _ := by
  cat_disch

-- Δ_{K}
@[simps]
noncomputable
def ninclusion [K.Nonsingular] : K.Nᵒᵖ ⥤ K.Elements where
  obj Y := .mk (.op <| .mk Y.unop.dim) Y.unop.simplex
  map {Y Z} f := .mk (.op <| N.Hom.hom f.unop) (N.Hom.hom_spec _)

example : K.Elements ⥤ SimplexCategoryᵒᵖ := CategoryOfElements.π _

-- attribute [grind] Nonsingular.mono_of_mem_nonDegenerate

set_option backward.isDefEq.respectTransparency false in
lemma map_mem_nonDegenerate_of_nonsingular [K.Nonsingular] (n m : SimplexCategory) (f : n ⟶ m)
    [Mono f] (x : K.obj (.op m)) (hx : x ∈ K.nonDegenerate m.len) :
    K.map f.op x ∈ K.nonDegenerate _ := by
  have : Mono (yonedaEquiv.symm <| K.map f.op x) := by
    have : yonedaEquiv.symm (K.map f.op x) = uliftYoneda.map f ≫ yonedaEquiv.symm x :=
      (uliftYonedaEquiv_symm_naturality_left _ _ _).symm
    rw [this]
    have : Mono (yonedaEquiv.symm x) := Nonsingular.mono_of_mem_nonDegenerate _ hx
    infer_instance
  have := (nonDegenerate_iff_of_mono (yonedaEquiv.symm <| K.map f.op x)
    (stdSimplex.objEquiv.symm (𝟙 _))).mpr (SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate _)
  simpa using this


@[to_dual self]
theorem _root_.Quiver.Hom.unop_surjective {X Y : Cᵒᵖ} :
    Function.Surjective (Quiver.Hom.unop : (X ⟶ Y) → (Opposite.unop Y ⟶ Opposite.unop X)) :=
  fun f ↦ ⟨f.op, rfl⟩

@[to_dual self]
theorem _root_.Quiver.Hom.op_surjective {X Y : C} :
    Function.Surjective (Quiver.Hom.op : (X ⟶ Y) → (Opposite.op Y ⟶ Opposite.op X)) :=
  fun f ↦ ⟨f.unop, rfl⟩

set_option backward.isDefEq.respectTransparency false in
instance [K.Nonsingular] : K.nonDegenerateElements.ι.Initial := by
  refine ⟨fun ⟨⟨⟨n⟩⟩, x⟩ ↦ ?_⟩
  obtain ⟨m, f, hf, ⟨y, hy⟩, heq⟩ := exists_nonDegenerate K x
  let U : CostructuredArrow K.nonDegenerateElements.ι ⟨⟨⟨n⟩⟩, x⟩ :=
    CostructuredArrow.mk (Y := ⟨⟨_, y⟩, hy⟩) ⟨.op <| by exact f, heq.symm⟩
  have : Nonempty (CostructuredArrow K.nonDegenerateElements.ι ⟨⟨⟨n⟩⟩, x⟩) := ⟨U⟩
  suffices h : ∀ a : CostructuredArrow K.nonDegenerateElements.ι ⟨Opposite.op ⦋n⦌, x⟩,
      Nonempty (a ⟶ U) from
    zigzag_isConnected fun j₁ j₂ ↦ .trans (.of_hom (h _).some) (.of_inv (h _).some)
  rintro ⟨⟨⟨⟨⟨na⟩⟩, pa⟩, ha⟩, _, homa, ha'⟩
  dsimp at homa ha
  obtain ⟨homa, rfl⟩ := Quiver.Hom.op_surjective homa
  simp_rw [heq] at this
  obtain ⟨⟨⟨⟨ma⟩, τa, πa, rfl⟩, h⟩⟩ := HasStrongEpiMonoFactorisations.has_fac homa
  simp only [Functor.const_obj_obj, ObjectProperty.ι_obj, op_comp, Functor.map_comp,
    comp_apply] at ha'
  obtain rfl := unique_nonDegenerate_dim _ x πa
    ⟨_, K.map_mem_nonDegenerate_of_nonsingular _ _ τa pa ha⟩ ha'.symm f ⟨_, hy⟩ heq
  obtain rfl := congr($(unique_nonDegenerate_simplex _ _ πa
    ⟨_, K.map_mem_nonDegenerate_of_nonsingular _ _ τa pa ha⟩ ha'.symm f ⟨_, hy⟩ heq).1)
  obtain rfl := unique_nonDegenerate_map _ _ πa
    ⟨_, K.map_mem_nonDegenerate_of_nonsingular _ _ τa pa ha⟩ ha'.symm f ⟨_, hy⟩ heq
  exact ⟨CostructuredArrow.homMk ⟨.op τa, by simp [U]⟩ (by ext; simp [U])⟩

set_option backward.isDefEq.respectTransparency false in
@[simps]
noncomputable
def nonDegenerateElementsEquiv [K.Nonsingular] :
    K.nonDegenerateElements.FullSubcategory ≌ K.Nᵒᵈ where
  functor.obj x := OrderDual.toDual ⟨⟨x.obj.snd⟩, x.property⟩
  functor.map {x y} f := homOfLE <| by
    rw [OrderDual.toDual_le_toDual, N.le_iff_exists_mono]
    dsimp
    refine ⟨f.hom.1.unop, ?_, f.hom.2⟩
    have : Mono (yonedaEquiv.symm y.obj.snd) := Nonsingular.mono_of_mem_nonDegenerate _ y.property
    have : Mono (yonedaEquiv.symm x.obj.snd) := Nonsingular.mono_of_mem_nonDegenerate _ x.property
    have heq : yonedaEquiv.symm y.1.2 =
        uliftYoneda.map f.hom.1.unop ≫ yonedaEquiv.symm x.1.2 := by
      -- TODO: make `SSet.yonedaEquiv` an `abbrev`?
      erw [uliftYonedaEquiv_symm_naturality_left]
      congr
      exact f.hom.2.symm
    have : Mono (uliftYoneda.map f.hom.1.unop) :=
      mono_of_mono_fac heq.symm
    exact Functor.mono_of_mono_map uliftYoneda this
  inverse.obj x := ⟨⟨_, (OrderDual.ofDual x).simplex⟩, (OrderDual.ofDual x).2⟩
  inverse.map {x y} f := ⟨.op <| N.Hom.hom _, by simp⟩
  unitIso :=
    NatIso.ofComponents
      (fun x ↦ ObjectProperty.isoMk _
        (CategoryOfElements.isoMk _ _ (.op <| Iso.refl _) (by simp)))
        (by dsimp; cat_disch)
  counitIso := Iso.refl _

@[simp]
lemma yonedaEquiv_symm_objEquiv_symm {n m : ℕ} (x : ⦋m⦌ ⟶ ⦋n⦌) :
    yonedaEquiv.symm (stdSimplex.objEquiv.symm x) = uliftYoneda.map x :=
  rfl

-- def asdfasdfasdf (n m : ℕ) :

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma map_objEquiv_objEquiv_symm_id (n m : ℕ) (x : Δ[n] _⦋m⦌) (i) :
    dsimp% Δ[n].map (stdSimplex.objEquiv x).op (stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)) i = x i := by
  rfl

lemma mono_stdSimplex_objEquiv_of_mem_nonDegenerate {n m : ℕ} {x : Δ[n] _⦋m⦌}
    (hx : x ∈ Δ[n].nonDegenerate _) :
    Mono (stdSimplex.objEquiv x) := by
  obtain ⟨x, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  simpa using (SSet.stdSimplex.objEquiv_symm_mem_nonDegenerate_iff_mono x).mp hx

set_option backward.isDefEq.respectTransparency false in
instance (n : ℕ) : (Δ[n] : SSet.{u}).Nonsingular where
  mono_of_mem_nonDegenerate {m} x hx := by
    obtain ⟨x, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
    have : SSet.yonedaEquiv.symm (stdSimplex.objEquiv.symm x) = uliftYoneda.map x := by
      rfl
    rw [this]
    rw [uliftYoneda.{u}.mono_map_iff_mono]
    exact (SSet.stdSimplex.objEquiv_symm_mem_nonDegenerate_iff_mono x).mp hx

set_option backward.isDefEq.respectTransparency false in
instance (n : ℕ) : OrderTop (Δ[n] : SSet.{u}).N where
  top := ⟨.mk (stdSimplex.objEquiv.symm (𝟙 _)), stdSimplex.objEquiv_symm_id_mem_nonDegenerate n⟩
  le_top a := by
    rw [N.le_iff_exists_mono]
    exact ⟨stdSimplex.objEquiv a.simplex, mono_stdSimplex_objEquiv_of_mem_nonDegenerate a.2,
      stdSimplex.ext _ a.simplex (by simp)⟩

@[simp]
lemma dimp_N_stdSimplex_top (n : ℕ) : (⊤ : (Δ[n] : SSet.{u}).N).dim = n :=
  rfl

@[simp]
lemma simplex_N_stdSimplex_top (n : ℕ) :
    (⊤ : (Δ[n] : SSet.{u}).N).simplex = stdSimplex.objEquiv.symm (𝟙 _) :=
  rfl

lemma Nonsingular.of_mono {K L : SSet.{u}} (f : K ⟶ L) [Mono f] [L.Nonsingular] :
    K.Nonsingular where
  mono_of_mem_nonDegenerate {n} x hx := by
    have : (f.app (Opposite.op ⦋n⦌)) x ∈ L.nonDegenerate _ := by
      rwa [nonDegenerate_iff_of_mono]
    have : Mono (yonedaEquiv.symm ((f.app (Opposite.op ⦋n⦌)) x)) :=
      mono_of_mem_nonDegenerate ((ConcreteCategory.hom (f.app (Opposite.op ⦋n⦌))) x) this
    have : yonedaEquiv.symm x ≫ f = yonedaEquiv.symm (f.app _ x) := by simp
    exact mono_of_mono_fac this

instance [K.Nonsingular] (y : K.Subcomplex) : (y : SSet.{w}).Nonsingular :=
  Nonsingular.of_mono y.ι

end SSet

namespace CategoryTheory

variable {C : Type*} [Category* C]

structure Functor.Coelements (F : Cᵒᵖ ⥤ Type*) where
  obj : C
  val : F.obj (.op obj)

variable (F : Cᵒᵖ ⥤ Type*)

--namespace Functor.Coelements
--
--structure Hom (X Y : F.Coelements) where
--  hom : X.obj ⟶ Y.obj
--  map_hom_val : F.map hom.op Y.val = X.val := by cat_disch
--
--instance : Category F.Coelements where
--  Hom := Hom F
--  id X := { hom := 𝟙 _ }
--  comp {X Y Z} f g := { hom := f.hom ≫ g.hom }
--
--end Functor.Coelements

end CategoryTheory

namespace CategoryTheory.SimplicialObject

noncomputable abbrev bracketDiag : K.Elements ⥤ C :=
  CategoryOfElements.π K ⋙ X

abbrev HasBracket : Prop := HasLimit (X.bracketDiag K)

noncomputable abbrev bracket [X.HasBracket K] : C :=
  limit (X.bracketDiag K)

instance [K.Nonsingular] [HasLimitsOfShape K.Nᵒᵈ C] : X.HasBracket K :=
  Functor.Initial.hasLimit_of_comp
    (K.nonDegenerateElementsEquiv.inverse ⋙ K.nonDegenerateElements.ι)

example [K.Nonsingular] [HasFiniteLimits C] [K.Finite] : X.HasBracket K :=
  inferInstance

noncomputable
def bracketIsoOfNonsingular [K.Nonsingular] [X.HasBracket K] :
    X.bracket K ≅
      limit (K.nonDegenerateElementsEquiv.inverse ⋙ K.nonDegenerateElements.ι ⋙ X.bracketDiag K) :=
  (Functor.Initial.limitIso _ _).symm ≪≫ HasLimit.isoOfNatIso (Functor.associator _ _ _)

-- TODO: add `π` lemma for `limitIso`
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma bracketIsoOfNonsingular_hom_π [K.Nonsingular] [X.HasBracket K] (x : K.Nᵒᵈ) :
    (X.bracketIsoOfNonsingular K).hom ≫ limit.π _ x =
      limit.π _ _ := by
  simp [bracketIsoOfNonsingular, CategoryTheory.Functor.Initial.limitIso_inv]

-- TODO: add `π` lemma for `limitIso`
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma bracketIsoOfNonsingular_inv_π [K.Nonsingular] [X.HasBracket K] (x : K.Nᵒᵈ) :
    dsimp% (X.bracketIsoOfNonsingular K).inv ≫ limit.π _ _ =
      limit.π _ x := by
  simp [← cancel_epi (X.bracketIsoOfNonsingular K).hom]

open SSet

noncomputable def bracketStdSimplexIso (n : ℕ) : X.bracket Δ[n] ≅ X _⦋n⦌ :=
  X.bracketIsoOfNonsingular _ ≪≫
    IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitOfDiagramInitial isInitialBot _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma bracketStdSimplexIso_inv_π (n : ℕ) :
    (X.bracketStdSimplexIso n).inv ≫ limit.π _ ⟨_, stdSimplex.objEquiv.symm (𝟙 _)⟩ = 𝟙 _ := by
  have : (X.bracketIsoOfNonsingular Δ[n]).inv ≫
      limit.π (X.bracketDiag (Δ[n] : SSet.{_}))
        ⟨Opposite.op ⦋n⦌, stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)⟩ = limit.π _ ⊥ :=
    X.bracketIsoOfNonsingular_inv_π Δ[n] ⊥
  dsimp
  simp only [bracketStdSimplexIso, Iso.trans_inv, Category.assoc]
  rw [this]
  simp

example (n : ℕ) : (∂Δ[n] : SSet.{u}).Nonsingular :=
  inferInstance

variable {K L M : SSet.{u}}

@[simps!]
def _root_.CategoryTheory.CategoryOfElements.mapπiso
    {C : Type*} [Category* C] {F G : C ⥤ Type u} (f : F ⟶ G) :
    CategoryOfElements.map f ⋙ CategoryOfElements.π G ≅ CategoryOfElements.π F :=
  NatIso.ofComponents fun _ ↦ Iso.refl _

noncomputable
def bracketMap [X.HasBracket K] [X.HasBracket L] (f : K ⟶ L) :
    X.bracket L ⟶ X.bracket K :=
  haveI : HasLimit (CategoryOfElements.map f ⋙ CategoryOfElements.π L ⋙ X) :=
    hasLimit_of_iso (Functor.isoWhiskerRight (CategoryOfElements.mapπiso f) _).symm
  limit.pre (CategoryOfElements.π L ⋙ X) (CategoryOfElements.map f) ≫
    (HasLimit.isoOfNatIso <| (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CategoryOfElements.mapπiso _) _).hom

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma bracketMap_π [X.HasBracket K] [X.HasBracket L] (f : K ⟶ L) (x : K.Elements) :
    X.bracketMap f ≫ limit.π _ x = limit.π _ ((CategoryOfElements.map f).obj x) := by
  simp [bracketMap]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma bracketMap_comp [X.HasBracket K] [X.HasBracket L] [X.HasBracket M]
      (f : K ⟶ L) (g : L ⟶ M) :
    X.bracketMap (f ≫ g) = X.bracketMap g ≫ X.bracketMap f := by
  ext
  simp [CategoryOfElements.map]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma bracketMap_id [X.HasBracket K] : X.bracketMap (𝟙 K) = 𝟙 _ := by
  ext ⟨j⟩
  simp [CategoryOfElements.map]

end SimplicialObject

structure MorphismProperty.IsHypercover [HasFiniteLimits C] (P : MorphismProperty C) : Prop where
  prop_bracketMap (n : ℕ) : P (X.bracketMap <| (∂Δ[n] : (Δ[n] : SSet.{0}).Subcomplex).ι)

end CategoryTheory
