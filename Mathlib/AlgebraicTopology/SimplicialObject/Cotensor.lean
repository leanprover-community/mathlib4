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

lemma N.Hom.ext {x y : K.N} (f g : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) [Mono f] [Mono g]
    (hf : K.map f.op y.simplex = x.simplex) (hg : K.map g.op y.simplex = x.simplex) :
    f = g :=
  sorry

variable {K} in
@[reassoc (attr := simp)]
lemma N.Hom.hom_comp {x y z : K.N} (f : x ⟶ y) (g : y ⟶ z) :
    N.Hom.hom (f ≫ g) = N.Hom.hom f ≫ N.Hom.hom g := by
  apply N.Hom.ext
  · simp
  · simp

variable {K} in
@[reassoc (attr := simp)]
lemma N.Hom.hom_id (x : K.N) :
    N.Hom.hom (𝟙 x) = 𝟙 _ := by
  apply N.Hom.ext
  · simp
  · simp

-- Δ_{K}
@[simps]
noncomputable
def ninclusion : K.Nᵒᵖ ⥤ K.Elements where
  obj Y := .mk (.op <| .mk Y.unop.dim) Y.unop.simplex
  map {Y Z} f := .mk (.op <| N.Hom.hom f.unop) (N.Hom.hom_spec _)

example : K.Elements ⥤ SimplexCategoryᵒᵖ := CategoryOfElements.π _

abbrev nonDegenerateElements : ObjectProperty K.Elements :=
  fun x ↦ x.snd ∈ K.nonDegenerate _

class Nonsingular (K : SSet.{u}) : Prop where
  mono_of_mem_nonDegenerate {n : ℕ} (x : K _⦋n⦌) (hx : x ∈ K.nonDegenerate n) :
    Mono (yonedaEquiv.symm x)

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

instance [K.Nonsingular] : K.nonDegenerateElements.ι.Initial := by
  refine ⟨fun ⟨⟨⟨n⟩⟩, x⟩ ↦ ?_⟩
  obtain ⟨m, f, hf, ⟨y, hy⟩, heq⟩ := exists_nonDegenerate K x
  let U : CostructuredArrow K.nonDegenerateElements.ι ⟨⟨⟨n⟩⟩, x⟩ :=
    CostructuredArrow.mk (Y := ⟨⟨_, y⟩, hy⟩) ⟨.op <| by exact f, heq.symm⟩
  have : Nonempty (CostructuredArrow K.nonDegenerateElements.ι ⟨⟨⟨n⟩⟩, x⟩) := ⟨U⟩
  apply zigzag_isConnected
  intro a b
  trans U
  · apply Zigzag.of_hom
    have := a.hom.1.unop
    dsimp at this
    have := a.hom.2
    dsimp at this
    -- have := CostructuredArrow.w _
    simp_rw [heq] at this
    refine CostructuredArrow.homMk ⟨?_, ?_⟩ ?_
    · refine .op ?_
      dsimp [U]
      sorry
    · sorry
    · sorry
  · sorry

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

noncomputable def bracketDiag : K.Elements ⥤ C :=
  CategoryOfElements.π K ⋙ X

abbrev HasBracket : Prop := HasLimit (X.bracketDiag K)

noncomputable def bracket [X.HasBracket K] : C :=
  limit (X.bracketDiag K)

instance [HasFiniteLimits C] [K.Finite] : X.HasBracket K :=
  sorry

end CategoryTheory.SimplicialObject
