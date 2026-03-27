/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
# The monoidal category structure on simplicial sets

This file defines an instance of chosen finite products
for the category `SSet`. It follows from the fact
the `SSet` if a category of functors to the category
of types and that the category of types have chosen
finite products. As a result, we obtain a monoidal
category structure on `SSet`.

-/

@[expose] public section

universe u

open Simplicial CategoryTheory MonoidalCategory CartesianMonoidalCategory
  Limits SimplicialObject.Truncated

namespace SSet

@[simp]
lemma leftUnitor_hom_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : (𝟙_ _ ⊗ K).obj Δ) :
    (λ_ K).hom.app Δ x = x.2 := rfl

@[simp]
lemma leftUnitor_inv_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : K.obj Δ) :
    (λ_ K).inv.app Δ x = ⟨PUnit.unit, x⟩ := rfl

@[simp]
lemma rightUnitor_hom_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ 𝟙_ _).obj Δ) :
    (ρ_ K).hom.app Δ x = x.1 := rfl

@[simp]
lemma rightUnitor_inv_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : K.obj Δ) :
    (ρ_ K).inv.app Δ x = ⟨x, PUnit.unit⟩ := rfl

@[simp]
lemma tensorHom_app_apply {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L')
    {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ L).obj Δ) :
    (f ⊗ₘ g).app Δ x = ⟨f.app Δ x.1, g.app Δ x.2⟩ := rfl

@[simp]
lemma whiskerLeft_app_apply (K : SSet.{u}) {L L' : SSet.{u}} (g : L ⟶ L')
    {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ L).obj Δ) :
    (K ◁ g).app Δ x = ⟨x.1, g.app Δ x.2⟩ := rfl

@[simp]
lemma whiskerRight_app_apply {K K' : SSet.{u}} (f : K ⟶ K') (L : SSet.{u})
    {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ L).obj Δ) :
    (f ▷ L).app Δ x = ⟨f.app Δ x.1, x.2⟩ := rfl

@[simp]
lemma associator_hom_app_apply (K L M : SSet.{u}) {Δ : SimplexCategoryᵒᵖ}
    (x : ((K ⊗ L) ⊗ M).obj Δ) :
    (α_ K L M).hom.app Δ x = ⟨x.1.1, x.1.2, x.2⟩ := rfl

@[simp]
lemma associator_inv_app_apply (K L M : SSet.{u}) {Δ : SimplexCategoryᵒᵖ}
    (x : (K ⊗ L ⊗ M).obj Δ) :
    (α_ K L M).inv.app Δ x = ⟨⟨x.1, x.2.1⟩, x.2.2⟩ := rfl

/-- The bijection `(𝟙_ SSet ⟶ K) ≃ K _⦋0⦌`. -/
def unitHomEquiv (K : SSet.{u}) : (𝟙_ _ ⟶ K) ≃ K _⦋0⦌ where
  toFun φ := φ.app _ PUnit.unit
  invFun x :=
    { app := fun Δ _ => K.map (SimplexCategory.const Δ.unop ⦋0⦌ 0).op x
      naturality := fun Δ Δ' f => by
        ext ⟨⟩
        dsimp
        rw [← FunctorToTypes.map_comp_apply]
        rfl }
  left_inv φ := by
    ext Δ ⟨⟩
    dsimp
    rw [← FunctorToTypes.naturality]
    rfl
  right_inv x := by simp

/-- The object `Δ[0]` is terminal in `SSet`. -/
def stdSimplex.isTerminalObj₀ : IsTerminal (Δ[0] : SSet.{u}) :=
  IsTerminal.ofUniqueHom (fun _ ↦ SSet.const (obj₀Equiv.symm 0))
    (fun _ _ ↦ by
      ext ⟨n⟩
      exact objEquiv.injective (by ext; simp))

@[ext]
lemma stdSimplex.ext₀ {X : SSet.{u}} {f g : X ⟶ Δ[0]} : f = g :=
  isTerminalObj₀.hom_ext _ _

instance (X Y : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    [Finite (X.obj n)] [Finite (Y.obj n)] :
    Finite ((X ⊗ Y).obj n) :=
  inferInstanceAs (Finite (X.obj n × Y.obj n))

instance : (𝟙_ SSet.{u}).Finite :=
  finite_of_iso (stdSimplex.isTerminalObj₀.{u}.uniqueUpToIso
    CartesianMonoidalCategory.isTerminalTensorUnit)

instance : HasDimensionLE (𝟙_ SSet.{u}) 0 :=
  (hasDimensionLT_iff_of_iso (stdSimplex.isTerminalObj₀.{u}.uniqueUpToIso
    CartesianMonoidalCategory.isTerminalTensorUnit) _).1 inferInstance

namespace Subcomplex

/-- The external product of subcomplexes of simplicial sets. -/
@[simps]
def prod {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) : (X ⊗ Y).Subcomplex where
  obj Δ := (A.obj Δ).prod (B.obj Δ)
  map i _ hx := ⟨A.map i hx.1, B.map i hx.2⟩

lemma prod_monotone {X Y : SSet.{u}}
    {A₁ A₂ : X.Subcomplex} (hX : A₁ ≤ A₂) {B₁ B₂ : Y.Subcomplex} (hY : B₁ ≤ B₂) :
    A₁.prod B₁ ≤ A₂.prod B₂ :=
  fun _ _ hx => ⟨hX _ hx.1, hY _ hx.2⟩

lemma prod_le_top_prod {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) :
    A.prod B ≤ (⊤ : X.Subcomplex).prod B :=
  prod_monotone le_top (by rfl)

lemma prod_le_prod_top {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) :
    A.prod B ≤ A.prod ⊤ :=
  prod_monotone (by rfl) le_top

set_option backward.isDefEq.respectTransparency false in
lemma range_tensorHom {X₁ X₂ Y₁ Y₂ : SSet.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    range (f₁ ⊗ₘ f₂) = (range f₁).prod (range f₂) := by
  ext m ⟨y₁, y₂⟩
  constructor
  · rintro ⟨⟨x₁, x₂⟩, h⟩
    rw [Prod.eq_iff_fst_eq_snd_eq] at h
    exact ⟨⟨x₁, h.1⟩, ⟨x₂, h.2⟩⟩
  · rintro ⟨⟨x₁, rfl⟩, ⟨x₂, rfl⟩⟩
    exact ⟨⟨x₁, x₂⟩, rfl⟩

/-- The isomorphism `(A.prod B).toSSet ≅ A.toSSet ⊗ B.toSSet`. -/
@[simps]
def prodIso {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) :
    (A.prod B).toSSet ≅ A ⊗ B where
  hom := CartesianMonoidalCategory.lift
    (lift ((A.prod B).ι ≫ CartesianMonoidalCategory.fst _ _) (by
      intro _ _ ⟨⟨_, ⟨_, _⟩⟩, _⟩
      cat_disch))
    (lift ((A.prod B).ι ≫ CartesianMonoidalCategory.snd _ _) (by
      intro _ _ ⟨⟨_, ⟨_, _⟩⟩, _⟩
      cat_disch))
  inv := lift (A.ι ⊗ₘ B.ι) (by
    rintro m _ ⟨⟨y₁, y₂⟩, ⟨⟩⟩
    exact ⟨Subtype.coe_prop _, Subtype.coe_prop _⟩)

end Subcomplex

/-- The inclusion `X ⟶ X ⊗ Δ[1]` which is `0` on the second factor. -/
noncomputable def ι₀ {X : SSet.{u}} : X ⟶ X ⊗ Δ[1] :=
  lift (𝟙 X) (const (stdSimplex.obj₀Equiv.{u}.symm 0))

@[reassoc (attr := simp)]
lemma ι₀_comp {X Y : SSet.{u}} (f : X ⟶ Y) :
    ι₀ ≫ f ▷ _ = f ≫ ι₀ := rfl

@[reassoc (attr := simp)]
lemma ι₀_fst (X : SSet.{u}) : ι₀ ≫ fst X _ = 𝟙 X := rfl

@[reassoc (attr := simp)]
lemma ι₀_snd (X : SSet.{u}) : ι₀ ≫ snd X _ = const (stdSimplex.obj₀Equiv.{u}.symm 0) := rfl

@[simp]
lemma ι₀_app_fst {X : SSet.{u}} {m} (x : X.obj m) : (ι₀.app _ x).1 = x := rfl

@[simp]
lemma ι₀_app_snd_apply {X : SSet.{u}} {m : ℕ} (x : X _⦋m⦌) (k : Fin (m + 1)) :
    (ι₀.app _ x).2 k = 0 := rfl

/-- The inclusion `X ⟶ X ⊗ Δ[1]` which is `1` on the second factor. -/
noncomputable def ι₁ {X : SSet.{u}} : X ⟶ X ⊗ Δ[1] :=
  lift (𝟙 X) (const (stdSimplex.obj₀Equiv.{u}.symm 1))

@[reassoc (attr := simp)]
lemma ι₁_fst (X : SSet.{u}) : ι₁ ≫ fst X _ = 𝟙 X := rfl

@[reassoc (attr := simp)]
lemma ι₁_snd (X : SSet.{u}) : ι₁ ≫ snd X _ = (const (stdSimplex.obj₀Equiv.{u}.symm 1)) := rfl

@[reassoc (attr := simp)]
lemma ι₁_comp {X Y : SSet.{u}} (f : X ⟶ Y) :
    ι₁ ≫ f ▷ _ = f ≫ ι₁ := rfl

@[simp]
lemma ι₁_app_fst {X : SSet.{u}} {m} (x : X.obj m) : (ι₁.app _ x).1 = x := rfl

@[simp]
lemma ι₁_app_snd_apply {X : SSet.{u}} {m : ℕ} (x : X _⦋m⦌) (k : Fin (m + 1)) :
    (ι₁.app _ x).2 k = 1 := rfl

section

variable (X Y : SSet.{u})

section

variable {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) (z : (X ⊗ Y).obj m)
@[simp high, grind =] lemma prod_map_fst : ((X ⊗ Y).map f z).1 = X.map f z.1 := rfl
@[simp high, grind =] lemma prod_map_snd : ((X ⊗ Y).map f z).2 = Y.map f z.2 := rfl

end

@[simp, grind =] lemma prod_δ_fst {n : ℕ} (i : Fin (n + 2)) (z : (X ⊗ Y : SSet.{u}) _⦋n + 1⦌) :
    ((X ⊗ Y).δ i z).1 = X.δ i z.1 := rfl

@[simp, grind =] lemma prod_δ_snd {n : ℕ} (i : Fin (n + 2)) (z : (X ⊗ Y : SSet.{u}) _⦋n + 1⦌) :
    ((X ⊗ Y).δ i z).2 = Y.δ i z.2 := rfl

@[simp, grind =] lemma prod_σ_fst {n : ℕ} (i : Fin (n + 1)) (z : (X ⊗ Y : SSet.{u}) _⦋n⦌) :
    ((X ⊗ Y).σ i z).1 = X.σ i z.1 := rfl

@[simp, grind =] lemma prod_σ_snd {n : ℕ} (i : Fin (n + 1)) (z : (X ⊗ Y : SSet.{u}) _⦋n⦌) :
    ((X ⊗ Y).σ i z).2 = Y.σ i z.2 := rfl

end

section

namespace Subcomplex

variable {X Y : SSet.{u}} (S : X.Subcomplex) (T : Y.Subcomplex)

/-- Given `S ≤ X` and `T ≤ Y`, this is the subcomplex of `X ⊗ Y` given by `(X ⊗ T) ⊔ (S ⊗ Y)`. -/
def unionProd : (X ⊗ Y).Subcomplex := ((⊤ : X.Subcomplex).prod T) ⊔ (S.prod ⊤)

lemma mem_unionProd_iff {n : SimplexCategoryᵒᵖ} (x : (X ⊗ Y).obj n) :
    x ∈ (unionProd S T).obj _ ↔ x.2 ∈ T.obj _ ∨ x.1 ∈ S.obj _ := by
  dsimp [unionProd, Set.prod]
  cat_disch

lemma top_prod_le_unionProd : (⊤ : X.Subcomplex).prod T ≤ S.unionProd T := le_sup_left

lemma prod_top_le_unionProd : (S.prod ⊤) ≤ S.unionProd T := le_sup_right

lemma prod_le_unionProd : S.prod T ≤ S.unionProd T :=
  (prod_le_prod_top S T).trans (prod_top_le_unionProd S T)

namespace unionProd

/-- The inclusion `X ⊗ T ⟶ S.unionProd T` as simplicial sets. -/
noncomputable def ι₁ : X ⊗ T ⟶ S.unionProd T :=
  lift (X ◁ T.ι) (by
    rintro m _ ⟨⟨y₁, y₂⟩, ⟨⟩⟩
    exact Or.inl ⟨Set.mem_univ _, Subtype.coe_prop _⟩)

/-- The inclusion `S ⊗ Y ⟶ S.unionProd T` as simplicial sets -/
noncomputable def ι₂ : (S : SSet.{u}) ⊗ Y ⟶ (unionProd S T : SSet.{u}) :=
  lift (S.ι ▷ Y) (by
    rintro m _ ⟨⟨y₁, y₂⟩, ⟨⟩⟩
    exact Or.inr ⟨Subtype.coe_prop _, Set.mem_univ _⟩)

@[reassoc (attr := simp)]
lemma ι₁_ι : ι₁ S T ≫ (unionProd S T).ι = X ◁ T.ι := rfl

@[reassoc (attr := simp)]
lemma ι₂_ι : ι₂ S T ≫ (unionProd S T).ι = S.ι ▷ Y := rfl

lemma bicartSq : BicartSq (S.prod T) ((⊤ : X.Subcomplex).prod T) (S.prod ⊤) (unionProd S T) where
  sup_eq := rfl
  inf_eq := by
    ext n ⟨x, y⟩
    change _ ∧ _ ↔ _
    simp [prod, Set.prod, Membership.mem, Set.Mem, setOf]
    tauto

lemma isPushout : IsPushout (S.ι ▷ (T : SSet)) ((S : SSet) ◁ T.ι)
    (unionProd.ι₁ S T) (unionProd.ι₂ S T) :=
  (bicartSq S T).isPushout.of_iso (S.prodIso T)
    (prodIso _ _ ≪≫ whiskerRightIso (topIso X) _)
    (prodIso _ _ ≪≫ whiskerLeftIso _ (topIso Y))
    (Iso.refl _) rfl rfl rfl rfl

@[simp]
lemma preimage_β_hom : (unionProd S T).preimage (β_ _ _).hom = unionProd T S := by
  ext n ⟨x, y⟩
  simp only [mem_unionProd_iff, preimage_obj, Set.mem_preimage]
  tauto

@[simp]
lemma preimage_β_inv : (unionProd S T).preimage (β_ _ _).inv = unionProd T S := by
  apply preimage_β_hom

@[simp]
lemma image_β_hom : (unionProd S T).image (β_ _ _).hom = unionProd T S := by
  rw [← preimage_β_hom, preimage_image_of_isIso]

@[simp]
lemma image_β_inv : (unionProd S T).image (β_ _ _).inv = unionProd T S := by
  apply image_β_hom

/-- The isomorphism `unionProd S T ≅ unionProd T S` as simplicial sets. -/
@[simps]
noncomputable def symmIso : (unionProd S T : SSet) ≅ (unionProd T S : SSet) where
  hom := lift ((unionProd S T).ι ≫ (β_ _ _).hom) (by simp [range_comp])
  inv := lift ((unionProd T S).ι ≫ (β_ _ _).hom) (by simp [range_comp])

end unionProd

end Subcomplex

end

namespace Truncated

variable (n : ℕ)

open MonoidalCategory

instance : (truncation.{u} n).Monoidal :=
  inferInstanceAs ((Functor.whiskeringLeft _ _ _).obj _).Monoidal

variable {n} {X Y : Truncated.{u} n}

@[simp]
lemma tensor_map_apply_fst {d e : (SimplexCategory.Truncated n)ᵒᵖ}
    (f : d ⟶ e) (x : (X ⊗ Y : Truncated _).obj d) :
    ((X ⊗ Y : Truncated _).map f x).1 = X.map f x.1 := rfl

@[simp]
lemma tensor_map_apply_snd {d e : (SimplexCategory.Truncated n)ᵒᵖ}
    (f : d ⟶ e) (x : (X ⊗ Y : Truncated _).obj d) :
    ((X ⊗ Y : Truncated _).map f x).2 = Y.map f x.2 := rfl

end Truncated

end SSet
