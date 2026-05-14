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
noncomputable
def nonDegenerateElementsEquiv [K.Nonsingular] :
    K.nonDegenerateElements.FullSubcategory ≌ K.Nᵒᵖ where
  functor.obj x := ⟨⟨x.obj.snd⟩, x.property⟩
  functor.map {x y} f := .op <| homOfLE <| by
    rw [N.le_iff_exists_mono]
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
  inverse.obj x := ⟨⟨_, x.unop.simplex⟩, x.unop.2⟩
  inverse.map {x y} f := ⟨.op <| N.Hom.hom f.unop, by simp⟩
  unitIso :=
    NatIso.ofComponents
      (fun x ↦ ObjectProperty.isoMk _
        (CategoryOfElements.isoMk _ _ (.op <| Iso.refl _) (by simp)))
        (by dsimp; cat_disch)
  counitIso := Iso.refl _

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

instance [K.Nonsingular] [HasLimitsOfShape K.Nᵒᵖ C] : X.HasBracket K :=
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
lemma bracketIsoOfNonsingular_π [K.Nonsingular] [X.HasBracket K] (x : K.Nᵒᵖ) :
    (X.bracketIsoOfNonsingular K).hom ≫ limit.π _ x =
      limit.π _ _ := by
  simp [bracketIsoOfNonsingular, CategoryTheory.Functor.Initial.limitIso_inv]

--def asdfasdfas (n : ℕ) : Δ[n].K ≌ _ :=
--  sorry

instance (n : ℕ) : Δ[n].Nonsingular where
  mono_of_mem_nonDegenerate {m} x hx := sorry

variable [HasFiniteLimits C]

def fooobaz (n : ℕ) : X.bracket Δ[n] ≅ X _⦋n⦌ :=
  sorry

end CategoryTheory.SimplicialObject
