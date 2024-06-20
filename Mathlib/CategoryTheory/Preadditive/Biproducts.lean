/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Group.Ext
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Tactic.Abel

#align_import category_theory.preadditive.biproducts from "leanprover-community/mathlib"@"a176cb1219e300e85793d44583dede42377b51af"

/-!
# Basic facts about biproducts in preadditive categories.

In (or between) preadditive categories,

* Any biproduct satisfies the equality
  `total : ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`,
  or, in the binary case, `total : fst ≫ inl + snd ≫ inr = 𝟙 X`.

* Any (binary) `product` or (binary) `coproduct` is a (binary) `biproduct`.

* In any category (with zero morphisms), if `biprod.map f g` is an isomorphism,
  then both `f` and `g` are isomorphisms.

* If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
  so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
  via Gaussian elimination.

* As a corollary of the previous two facts,
  if we have an isomorphism `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  we can construct an isomorphism `X₂ ≅ Y₂`.

* If `f : W ⊞ X ⟶ Y ⊞ Z` is an isomorphism, either `𝟙 W = 0`,
  or at least one of the component maps `W ⟶ Y` and `W ⟶ Z` is nonzero.

* If `f : ⨁ S ⟶ ⨁ T` is an isomorphism,
  then every column (corresponding to a nonzero summand in the domain)
  has some nonzero matrix entry.

* A functor preserves a biproduct if and only if it preserves
  the corresponding product if and only if it preserves the corresponding coproduct.

There are connections between this material and the special case of the category whose morphisms are
matrices over a ring, in particular the Schur complement (see
`Mathlib.LinearAlgebra.Matrix.SchurComplement`). In particular, the declarations
`CategoryTheory.Biprod.isoElim`, `CategoryTheory.Biprod.gaussian`
and `Matrix.invertibleOfFromBlocks₁₁Invertible` are all closely related.

-/


open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

open CategoryTheory.Functor

open CategoryTheory.Preadditive

open scoped Classical

universe v v' u u'

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace Limits

section Fintype

variable {J : Type} [Fintype J]

/-- In a preadditive category, we can construct a biproduct for `f : J → C` from
any bicone `b` for `f` satisfying `total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
def isBilimitOfTotal {f : J → C} (b : Bicone f) (total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt) :
    b.IsBilimit where
  isLimit :=
    { lift := fun s => ∑ j : J, s.π.app ⟨j⟩ ≫ b.ι j
      uniq := fun s m h => by
        erw [← Category.comp_id m, ← total, comp_sum]
        apply Finset.sum_congr rfl
        intro j _
        have reassoced : m ≫ Bicone.π b j ≫ Bicone.ι b j = s.π.app ⟨j⟩ ≫ Bicone.ι b j := by
          erw [← Category.assoc, eq_whisker (h ⟨j⟩)]
        rw [reassoced]
      fac := fun s j => by
        cases j
        simp only [sum_comp, Category.assoc, Bicone.toCone_π_app, b.ι_π, comp_dite]
        -- See note [dsimp, simp].
        dsimp;
        simp }
  isColimit :=
    { desc := fun s => ∑ j : J, b.π j ≫ s.ι.app ⟨j⟩
      uniq := fun s m h => by
        erw [← Category.id_comp m, ← total, sum_comp]
        apply Finset.sum_congr rfl
        intro j _
        erw [Category.assoc, h ⟨j⟩]
      fac := fun s j => by
        cases j
        simp only [comp_sum, ← Category.assoc, Bicone.toCocone_ι_app, b.ι_π, dite_comp]
        dsimp; simp }
#align category_theory.limits.is_bilimit_of_total CategoryTheory.Limits.isBilimitOfTotal

theorem IsBilimit.total {f : J → C} {b : Bicone f} (i : b.IsBilimit) :
    ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt :=
  i.isLimit.hom_ext fun j => by
    cases j
    simp [sum_comp, b.ι_π, comp_dite]
#align category_theory.limits.is_bilimit.total CategoryTheory.Limits.IsBilimit.total

/-- In a preadditive category, we can construct a biproduct for `f : J → C` from
any bicone `b` for `f` satisfying `total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
theorem hasBiproduct_of_total {f : J → C} (b : Bicone f)
    (total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt) : HasBiproduct f :=
  HasBiproduct.mk
    { bicone := b
      isBilimit := isBilimitOfTotal b total }
#align category_theory.limits.has_biproduct_of_total CategoryTheory.Limits.hasBiproduct_of_total

/-- In a preadditive category, any finite bicone which is a limit cone is in fact a bilimit
    bicone. -/
def isBilimitOfIsLimit {f : J → C} (t : Bicone f) (ht : IsLimit t.toCone) : t.IsBilimit :=
  isBilimitOfTotal _ <|
    ht.hom_ext fun j => by
      cases j
      simp [sum_comp, t.ι_π, dite_comp, comp_dite]
#align category_theory.limits.is_bilimit_of_is_limit CategoryTheory.Limits.isBilimitOfIsLimit

/-- We can turn any limit cone over a pair into a bilimit bicone. -/
def biconeIsBilimitOfLimitConeOfIsLimit {f : J → C} {t : Cone (Discrete.functor f)}
    (ht : IsLimit t) : (Bicone.ofLimitCone ht).IsBilimit :=
  isBilimitOfIsLimit _ <|
    IsLimit.ofIsoLimit ht <|
      Cones.ext (Iso.refl _)
        (by
          rintro ⟨j⟩
          aesop_cat)
#align category_theory.limits.bicone_is_bilimit_of_limit_cone_of_is_limit CategoryTheory.Limits.biconeIsBilimitOfLimitConeOfIsLimit

/-- In a preadditive category, any finite bicone which is a colimit cocone is in fact a bilimit
    bicone. -/
def isBilimitOfIsColimit {f : J → C} (t : Bicone f) (ht : IsColimit t.toCocone) : t.IsBilimit :=
  isBilimitOfTotal _ <|
    ht.hom_ext fun j => by
      cases j
      simp_rw [Bicone.toCocone_ι_app, comp_sum, ← Category.assoc, t.ι_π, dite_comp]
      simp
#align category_theory.limits.is_bilimit_of_is_colimit CategoryTheory.Limits.isBilimitOfIsColimit

/-- We can turn any limit cone over a pair into a bilimit bicone. -/
def biconeIsBilimitOfColimitCoconeOfIsColimit {f : J → C} {t : Cocone (Discrete.functor f)}
    (ht : IsColimit t) : (Bicone.ofColimitCocone ht).IsBilimit :=
  isBilimitOfIsColimit _ <| IsColimit.ofIsoColimit ht <| Cocones.ext (Iso.refl _) <| by
    rintro ⟨j⟩; simp
#align category_theory.limits.bicone_is_bilimit_of_colimit_cocone_of_is_colimit CategoryTheory.Limits.biconeIsBilimitOfColimitCoconeOfIsColimit

end Fintype

section Finite

variable {J : Type} [Finite J]

/-- In a preadditive category, if the product over `f : J → C` exists,
    then the biproduct over `f` exists. -/
theorem HasBiproduct.of_hasProduct (f : J → C) [HasProduct f] : HasBiproduct f := by
  cases nonempty_fintype J
  exact HasBiproduct.mk
    { bicone := _
      isBilimit := biconeIsBilimitOfLimitConeOfIsLimit (limit.isLimit _) }
#align category_theory.limits.has_biproduct.of_has_product CategoryTheory.Limits.HasBiproduct.of_hasProduct

/-- In a preadditive category, if the coproduct over `f : J → C` exists,
    then the biproduct over `f` exists. -/
theorem HasBiproduct.of_hasCoproduct (f : J → C) [HasCoproduct f] : HasBiproduct f := by
  cases nonempty_fintype J
  exact HasBiproduct.mk
    { bicone := _
      isBilimit := biconeIsBilimitOfColimitCoconeOfIsColimit (colimit.isColimit _) }
#align category_theory.limits.has_biproduct.of_has_coproduct CategoryTheory.Limits.HasBiproduct.of_hasCoproduct

end Finite

/-- A preadditive category with finite products has finite biproducts. -/
theorem HasFiniteBiproducts.of_hasFiniteProducts [HasFiniteProducts C] : HasFiniteBiproducts C :=
  ⟨fun _ => { has_biproduct := fun _ => HasBiproduct.of_hasProduct _ }⟩
#align category_theory.limits.has_finite_biproducts.of_has_finite_products CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-- A preadditive category with finite coproducts has finite biproducts. -/
theorem HasFiniteBiproducts.of_hasFiniteCoproducts [HasFiniteCoproducts C] :
    HasFiniteBiproducts C :=
  ⟨fun _ => { has_biproduct := fun _ => HasBiproduct.of_hasCoproduct _ }⟩
#align category_theory.limits.has_finite_biproducts.of_has_finite_coproducts CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteCoproducts

section HasBiproduct

variable {J : Type} [Fintype J] {f : J → C} [HasBiproduct f]

/-- In any preadditive category, any biproduct satsifies
`∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`
-/
@[simp]
theorem biproduct.total : ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f) :=
  IsBilimit.total (biproduct.isBilimit _)
#align category_theory.limits.biproduct.total CategoryTheory.Limits.biproduct.total

theorem biproduct.lift_eq {T : C} {g : ∀ j, T ⟶ f j} :
    biproduct.lift g = ∑ j, g j ≫ biproduct.ι f j := by
  ext j
  simp only [sum_comp, biproduct.ι_π, comp_dite, biproduct.lift_π, Category.assoc, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, eqToHom_refl, Category.comp_id, if_true]
#align category_theory.limits.biproduct.lift_eq CategoryTheory.Limits.biproduct.lift_eq

theorem biproduct.desc_eq {T : C} {g : ∀ j, f j ⟶ T} :
    biproduct.desc g = ∑ j, biproduct.π f j ≫ g j := by
  ext j
  simp [comp_sum, biproduct.ι_π_assoc, dite_comp]
#align category_theory.limits.biproduct.desc_eq CategoryTheory.Limits.biproduct.desc_eq

@[reassoc]
theorem biproduct.lift_desc {T U : C} {g : ∀ j, T ⟶ f j} {h : ∀ j, f j ⟶ U} :
    biproduct.lift g ≫ biproduct.desc h = ∑ j : J, g j ≫ h j := by
  simp [biproduct.lift_eq, biproduct.desc_eq, comp_sum, sum_comp, biproduct.ι_π_assoc, comp_dite,
    dite_comp]
#align category_theory.limits.biproduct.lift_desc CategoryTheory.Limits.biproduct.lift_desc

theorem biproduct.map_eq [HasFiniteBiproducts C] {f g : J → C} {h : ∀ j, f j ⟶ g j} :
    biproduct.map h = ∑ j : J, biproduct.π f j ≫ h j ≫ biproduct.ι g j := by
  ext
  simp [biproduct.ι_π, biproduct.ι_π_assoc, comp_sum, sum_comp, comp_dite, dite_comp]
#align category_theory.limits.biproduct.map_eq CategoryTheory.Limits.biproduct.map_eq

@[reassoc]
theorem biproduct.lift_matrix {K : Type} [Finite K] [HasFiniteBiproducts C] {f : J → C} {g : K → C}
    {P} (x : ∀ j, P ⟶ f j) (m : ∀ j k, f j ⟶ g k) :
    biproduct.lift x ≫ biproduct.matrix m = biproduct.lift fun k => ∑ j, x j ≫ m j k := by
  ext
  simp [biproduct.lift_desc]
#align category_theory.limits.biproduct.lift_matrix CategoryTheory.Limits.biproduct.lift_matrix

end HasBiproduct

section HasFiniteBiproducts

variable {J K : Type} [Finite J] {f : J → C} [HasFiniteBiproducts C]

@[reassoc]
theorem biproduct.matrix_desc [Fintype K] {f : J → C} {g : K → C}
    (m : ∀ j k, f j ⟶ g k) {P} (x : ∀ k, g k ⟶ P) :
    biproduct.matrix m ≫ biproduct.desc x = biproduct.desc fun j => ∑ k, m j k ≫ x k := by
  ext
  simp [lift_desc]
#align category_theory.limits.biproduct.matrix_desc CategoryTheory.Limits.biproduct.matrix_desc

variable [Finite K]

@[reassoc]
theorem biproduct.matrix_map {f : J → C} {g : K → C} {h : K → C} (m : ∀ j k, f j ⟶ g k)
    (n : ∀ k, g k ⟶ h k) :
    biproduct.matrix m ≫ biproduct.map n = biproduct.matrix fun j k => m j k ≫ n k := by
  ext
  simp
#align category_theory.limits.biproduct.matrix_map CategoryTheory.Limits.biproduct.matrix_map

@[reassoc]
theorem biproduct.map_matrix {f : J → C} {g : J → C} {h : K → C} (m : ∀ k, f k ⟶ g k)
    (n : ∀ j k, g j ⟶ h k) :
    biproduct.map m ≫ biproduct.matrix n = biproduct.matrix fun j k => m j ≫ n j k := by
  ext
  simp
#align category_theory.limits.biproduct.map_matrix CategoryTheory.Limits.biproduct.map_matrix

end HasFiniteBiproducts

/-- Reindex a categorical biproduct via an equivalence of the index types. -/
@[simps]
def biproduct.reindex {β γ : Type} [Finite β] (ε : β ≃ γ)
    (f : γ → C) [HasBiproduct f] [HasBiproduct (f ∘ ε)] : ⨁ f ∘ ε ≅ ⨁ f where
  hom := biproduct.desc fun b => biproduct.ι f (ε b)
  inv := biproduct.lift fun b => biproduct.π f (ε b)
  hom_inv_id := by
    ext b b'
    by_cases h : b' = b
    · subst h; simp
    · have : ε b' ≠ ε b := by simp [h]
      simp [biproduct.ι_π_ne _ h, biproduct.ι_π_ne _ this]
  inv_hom_id := by
    cases nonempty_fintype β
    ext g g'
    by_cases h : g' = g <;>
      simp [Preadditive.sum_comp, Preadditive.comp_sum, biproduct.lift_desc,
        biproduct.ι_π, biproduct.ι_π_assoc, comp_dite, Equiv.apply_eq_iff_eq_symm_apply,
        Finset.sum_dite_eq' Finset.univ (ε.symm g') _, h]
#align category_theory.limits.biproduct.reindex CategoryTheory.Limits.biproduct.reindex

/-- In a preadditive category, we can construct a binary biproduct for `X Y : C` from
any binary bicone `b` satisfying `total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
def isBinaryBilimitOfTotal {X Y : C} (b : BinaryBicone X Y)
    (total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt) : b.IsBilimit where
  isLimit :=
    { lift := fun s =>
      (BinaryFan.fst s ≫ b.inl : s.pt ⟶ b.pt) + (BinaryFan.snd s ≫ b.inr : s.pt ⟶ b.pt)
      uniq := fun s m h => by
        have reassoced (j : WalkingPair) {W : C} (h' : _ ⟶ W) :
          m ≫ b.toCone.π.app ⟨j⟩ ≫ h' = s.π.app ⟨j⟩ ≫ h' := by
            rw [← Category.assoc, eq_whisker (h ⟨j⟩)]
        erw [← Category.comp_id m, ← total, comp_add, reassoced WalkingPair.left,
          reassoced WalkingPair.right]
      fac := fun s j => by rcases j with ⟨⟨⟩⟩ <;> simp }
  isColimit :=
    { desc := fun s =>
        (b.fst ≫ BinaryCofan.inl s : b.pt ⟶ s.pt) + (b.snd ≫ BinaryCofan.inr s : b.pt ⟶ s.pt)
      uniq := fun s m h => by
        erw [← Category.id_comp m, ← total, add_comp, Category.assoc, Category.assoc,
          h ⟨WalkingPair.left⟩, h ⟨WalkingPair.right⟩]
      fac := fun s j => by rcases j with ⟨⟨⟩⟩ <;> simp }
#align category_theory.limits.is_binary_bilimit_of_total CategoryTheory.Limits.isBinaryBilimitOfTotal

theorem IsBilimit.binary_total {X Y : C} {b : BinaryBicone X Y} (i : b.IsBilimit) :
    b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt :=
  i.isLimit.hom_ext fun j => by rcases j with ⟨⟨⟩⟩ <;> simp
#align category_theory.limits.is_bilimit.binary_total CategoryTheory.Limits.IsBilimit.binary_total

/-- In a preadditive category, we can construct a binary biproduct for `X Y : C` from
any binary bicone `b` satisfying `total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
theorem hasBinaryBiproduct_of_total {X Y : C} (b : BinaryBicone X Y)
    (total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt) : HasBinaryBiproduct X Y :=
  HasBinaryBiproduct.mk
    { bicone := b
      isBilimit := isBinaryBilimitOfTotal b total }
#align category_theory.limits.has_binary_biproduct_of_total CategoryTheory.Limits.hasBinaryBiproduct_of_total

/-- We can turn any limit cone over a pair into a bicone. -/
@[simps]
def BinaryBicone.ofLimitCone {X Y : C} {t : Cone (pair X Y)} (ht : IsLimit t) :
    BinaryBicone X Y where
  pt := t.pt
  fst := t.π.app ⟨WalkingPair.left⟩
  snd := t.π.app ⟨WalkingPair.right⟩
  inl := ht.lift (BinaryFan.mk (𝟙 X) 0)
  inr := ht.lift (BinaryFan.mk 0 (𝟙 Y))
#align category_theory.limits.binary_bicone.of_limit_cone CategoryTheory.Limits.BinaryBicone.ofLimitCone

theorem inl_of_isLimit {X Y : C} {t : BinaryBicone X Y} (ht : IsLimit t.toCone) :
    t.inl = ht.lift (BinaryFan.mk (𝟙 X) 0) := by
  apply ht.uniq (BinaryFan.mk (𝟙 X) 0); rintro ⟨⟨⟩⟩ <;> dsimp <;> simp
#align category_theory.limits.inl_of_is_limit CategoryTheory.Limits.inl_of_isLimit

theorem inr_of_isLimit {X Y : C} {t : BinaryBicone X Y} (ht : IsLimit t.toCone) :
    t.inr = ht.lift (BinaryFan.mk 0 (𝟙 Y)) := by
  apply ht.uniq (BinaryFan.mk 0 (𝟙 Y)); rintro ⟨⟨⟩⟩ <;> dsimp <;> simp
#align category_theory.limits.inr_of_is_limit CategoryTheory.Limits.inr_of_isLimit

/-- In a preadditive category, any binary bicone which is a limit cone is in fact a bilimit
    bicone. -/
def isBinaryBilimitOfIsLimit {X Y : C} (t : BinaryBicone X Y) (ht : IsLimit t.toCone) :
    t.IsBilimit :=
  isBinaryBilimitOfTotal _ (by refine BinaryFan.IsLimit.hom_ext ht ?_ ?_ <;> simp)
#align category_theory.limits.is_binary_bilimit_of_is_limit CategoryTheory.Limits.isBinaryBilimitOfIsLimit

/-- We can turn any limit cone over a pair into a bilimit bicone. -/
def binaryBiconeIsBilimitOfLimitConeOfIsLimit {X Y : C} {t : Cone (pair X Y)} (ht : IsLimit t) :
    (BinaryBicone.ofLimitCone ht).IsBilimit :=
  isBinaryBilimitOfTotal _ <| BinaryFan.IsLimit.hom_ext ht (by simp) (by simp)
#align category_theory.limits.binary_bicone_is_bilimit_of_limit_cone_of_is_limit CategoryTheory.Limits.binaryBiconeIsBilimitOfLimitConeOfIsLimit

/-- In a preadditive category, if the product of `X` and `Y` exists, then the
    binary biproduct of `X` and `Y` exists. -/
theorem HasBinaryBiproduct.of_hasBinaryProduct (X Y : C) [HasBinaryProduct X Y] :
    HasBinaryBiproduct X Y :=
  HasBinaryBiproduct.mk
    { bicone := _
      isBilimit := binaryBiconeIsBilimitOfLimitConeOfIsLimit (limit.isLimit _) }
#align category_theory.limits.has_binary_biproduct.of_has_binary_product CategoryTheory.Limits.HasBinaryBiproduct.of_hasBinaryProduct

/-- In a preadditive category, if all binary products exist, then all binary biproducts exist. -/
theorem HasBinaryBiproducts.of_hasBinaryProducts [HasBinaryProducts C] : HasBinaryBiproducts C :=
  { has_binary_biproduct := fun X Y => HasBinaryBiproduct.of_hasBinaryProduct X Y }
#align category_theory.limits.has_binary_biproducts.of_has_binary_products CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryProducts

/-- We can turn any colimit cocone over a pair into a bicone. -/
@[simps]
def BinaryBicone.ofColimitCocone {X Y : C} {t : Cocone (pair X Y)} (ht : IsColimit t) :
    BinaryBicone X Y where
  pt := t.pt
  fst := ht.desc (BinaryCofan.mk (𝟙 X) 0)
  snd := ht.desc (BinaryCofan.mk 0 (𝟙 Y))
  inl := t.ι.app ⟨WalkingPair.left⟩
  inr := t.ι.app ⟨WalkingPair.right⟩
#align category_theory.limits.binary_bicone.of_colimit_cocone CategoryTheory.Limits.BinaryBicone.ofColimitCocone

theorem fst_of_isColimit {X Y : C} {t : BinaryBicone X Y} (ht : IsColimit t.toCocone) :
    t.fst = ht.desc (BinaryCofan.mk (𝟙 X) 0) := by
  apply ht.uniq (BinaryCofan.mk (𝟙 X) 0)
  rintro ⟨⟨⟩⟩ <;> dsimp <;> simp
#align category_theory.limits.fst_of_is_colimit CategoryTheory.Limits.fst_of_isColimit

theorem snd_of_isColimit {X Y : C} {t : BinaryBicone X Y} (ht : IsColimit t.toCocone) :
    t.snd = ht.desc (BinaryCofan.mk 0 (𝟙 Y)) := by
  apply ht.uniq (BinaryCofan.mk 0 (𝟙 Y))
  rintro ⟨⟨⟩⟩ <;> dsimp <;> simp
#align category_theory.limits.snd_of_is_colimit CategoryTheory.Limits.snd_of_isColimit

/-- In a preadditive category, any binary bicone which is a colimit cocone is in fact a
    bilimit bicone. -/
def isBinaryBilimitOfIsColimit {X Y : C} (t : BinaryBicone X Y) (ht : IsColimit t.toCocone) :
    t.IsBilimit :=
  isBinaryBilimitOfTotal _ <| by
    refine BinaryCofan.IsColimit.hom_ext ht ?_ ?_ <;> simp
#align category_theory.limits.is_binary_bilimit_of_is_colimit CategoryTheory.Limits.isBinaryBilimitOfIsColimit

/-- We can turn any colimit cocone over a pair into a bilimit bicone. -/
def binaryBiconeIsBilimitOfColimitCoconeOfIsColimit {X Y : C} {t : Cocone (pair X Y)}
    (ht : IsColimit t) : (BinaryBicone.ofColimitCocone ht).IsBilimit :=
  isBinaryBilimitOfIsColimit (BinaryBicone.ofColimitCocone ht) <|
    IsColimit.ofIsoColimit ht <|
      Cocones.ext (Iso.refl _) fun j => by
        rcases j with ⟨⟨⟩⟩ <;> simp
#align category_theory.limits.binary_bicone_is_bilimit_of_colimit_cocone_of_is_colimit CategoryTheory.Limits.binaryBiconeIsBilimitOfColimitCoconeOfIsColimit

/-- In a preadditive category, if the coproduct of `X` and `Y` exists, then the
    binary biproduct of `X` and `Y` exists. -/
theorem HasBinaryBiproduct.of_hasBinaryCoproduct (X Y : C) [HasBinaryCoproduct X Y] :
    HasBinaryBiproduct X Y :=
  HasBinaryBiproduct.mk
    { bicone := _
      isBilimit := binaryBiconeIsBilimitOfColimitCoconeOfIsColimit (colimit.isColimit _) }
#align category_theory.limits.has_binary_biproduct.of_has_binary_coproduct CategoryTheory.Limits.HasBinaryBiproduct.of_hasBinaryCoproduct

/-- In a preadditive category, if all binary coproducts exist, then all binary biproducts exist. -/
theorem HasBinaryBiproducts.of_hasBinaryCoproducts [HasBinaryCoproducts C] :
    HasBinaryBiproducts C :=
  { has_binary_biproduct := fun X Y => HasBinaryBiproduct.of_hasBinaryCoproduct X Y }
#align category_theory.limits.has_binary_biproducts.of_has_binary_coproducts CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryCoproducts

section

variable {X Y : C} [HasBinaryBiproduct X Y]

/-- In any preadditive category, any binary biproduct satsifies
`biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y)`.
-/
@[simp]
theorem biprod.total : biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y) := by
  ext <;> simp [add_comp]
#align category_theory.limits.biprod.total CategoryTheory.Limits.biprod.total

theorem biprod.lift_eq {T : C} {f : T ⟶ X} {g : T ⟶ Y} :
    biprod.lift f g = f ≫ biprod.inl + g ≫ biprod.inr := by ext <;> simp [add_comp]
#align category_theory.limits.biprod.lift_eq CategoryTheory.Limits.biprod.lift_eq

theorem biprod.desc_eq {T : C} {f : X ⟶ T} {g : Y ⟶ T} :
    biprod.desc f g = biprod.fst ≫ f + biprod.snd ≫ g := by ext <;> simp [add_comp]
#align category_theory.limits.biprod.desc_eq CategoryTheory.Limits.biprod.desc_eq

@[reassoc (attr := simp)]
theorem biprod.lift_desc {T U : C} {f : T ⟶ X} {g : T ⟶ Y} {h : X ⟶ U} {i : Y ⟶ U} :
    biprod.lift f g ≫ biprod.desc h i = f ≫ h + g ≫ i := by simp [biprod.lift_eq, biprod.desc_eq]
#align category_theory.limits.biprod.lift_desc CategoryTheory.Limits.biprod.lift_desc

theorem biprod.map_eq [HasBinaryBiproducts C] {W X Y Z : C} {f : W ⟶ Y} {g : X ⟶ Z} :
    biprod.map f g = biprod.fst ≫ f ≫ biprod.inl + biprod.snd ≫ g ≫ biprod.inr := by
  ext <;> simp
#align category_theory.limits.biprod.map_eq CategoryTheory.Limits.biprod.map_eq

/-- Every split mono `f` with a cokernel induces a binary bicone with `f` as its `inl` and
the cokernel map as its `snd`.
We will show in `is_bilimit_binary_bicone_of_split_mono_of_cokernel` that this binary bicone is in
fact already a biproduct. -/
@[simps]
def binaryBiconeOfIsSplitMonoOfCokernel {X Y : C} {f : X ⟶ Y} [IsSplitMono f] {c : CokernelCofork f}
    (i : IsColimit c) : BinaryBicone X c.pt where
  pt := Y
  fst := retraction f
  snd := c.π
  inl := f
  inr :=
    let c' : CokernelCofork (𝟙 Y - (𝟙 Y - retraction f ≫ f)) :=
      CokernelCofork.ofπ (Cofork.π c) (by simp)
    let i' : IsColimit c' := isCokernelEpiComp i (retraction f) (by simp)
    let i'' := isColimitCoforkOfCokernelCofork i'
    (splitEpiOfIdempotentOfIsColimitCofork C (by simp) i'').section_
  inl_fst := by simp
  inl_snd := by simp
  inr_fst := by
    dsimp only
    rw [splitEpiOfIdempotentOfIsColimitCofork_section_,
      isColimitCoforkOfCokernelCofork_desc, isCokernelEpiComp_desc]
    dsimp only [cokernelCoforkOfCofork_ofπ]
    letI := epi_of_isColimit_cofork i
    apply zero_of_epi_comp c.π
    simp only [sub_comp, comp_sub, Category.comp_id, Category.assoc, IsSplitMono.id, sub_self,
      Cofork.IsColimit.π_desc_assoc, CokernelCofork.π_ofπ, IsSplitMono.id_assoc]
    apply sub_eq_zero_of_eq
    apply Category.id_comp
  inr_snd := by apply SplitEpi.id
#align category_theory.limits.binary_bicone_of_is_split_mono_of_cokernel CategoryTheory.Limits.binaryBiconeOfIsSplitMonoOfCokernel

/-- The bicone constructed in `binaryBiconeOfSplitMonoOfCokernel` is a bilimit.
This is a version of the splitting lemma that holds in all preadditive categories. -/
def isBilimitBinaryBiconeOfIsSplitMonoOfCokernel {X Y : C} {f : X ⟶ Y} [IsSplitMono f]
    {c : CokernelCofork f} (i : IsColimit c) : (binaryBiconeOfIsSplitMonoOfCokernel i).IsBilimit :=
  isBinaryBilimitOfTotal _
    (by
      simp only [binaryBiconeOfIsSplitMonoOfCokernel_fst,
        binaryBiconeOfIsSplitMonoOfCokernel_inr,
        binaryBiconeOfIsSplitMonoOfCokernel_snd,
        splitEpiOfIdempotentOfIsColimitCofork_section_]
      dsimp only [binaryBiconeOfIsSplitMonoOfCokernel_pt]
      rw [isColimitCoforkOfCokernelCofork_desc, isCokernelEpiComp_desc]
      simp only [binaryBiconeOfIsSplitMonoOfCokernel_inl, Cofork.IsColimit.π_desc,
        cokernelCoforkOfCofork_π, Cofork.π_ofπ, add_sub_cancel])
#align category_theory.limits.is_bilimit_binary_bicone_of_is_split_mono_of_cokernel CategoryTheory.Limits.isBilimitBinaryBiconeOfIsSplitMonoOfCokernel

/-- If `b` is a binary bicone such that `b.inl` is a kernel of `b.snd`, then `b` is a bilimit
    bicone. -/
def BinaryBicone.isBilimitOfKernelInl {X Y : C} (b : BinaryBicone X Y)
    (hb : IsLimit b.sndKernelFork) : b.IsBilimit :=
  isBinaryBilimitOfIsLimit _ <|
    BinaryFan.IsLimit.mk _ (fun f g => f ≫ b.inl + g ≫ b.inr) (fun f g => by simp)
      (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : ((m : T ⟶ b.pt) - (f ≫ b.inl + g ≫ b.inr)) ≫ b.fst = 0 := by
        simpa using sub_eq_zero.2 h₁
      have h₂' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.snd = 0 := by simpa using sub_eq_zero.2 h₂
      obtain ⟨q : T ⟶ X, hq : q ≫ b.inl = m - (f ≫ b.inl + g ≫ b.inr)⟩ :=
        KernelFork.IsLimit.lift' hb _ h₂'
      rw [← sub_eq_zero, ← hq, ← Category.comp_id q, ← b.inl_fst, ← Category.assoc, hq, h₁',
        zero_comp]
#align category_theory.limits.binary_bicone.is_bilimit_of_kernel_inl CategoryTheory.Limits.BinaryBicone.isBilimitOfKernelInl

/-- If `b` is a binary bicone such that `b.inr` is a kernel of `b.fst`, then `b` is a bilimit
    bicone. -/
def BinaryBicone.isBilimitOfKernelInr {X Y : C} (b : BinaryBicone X Y)
    (hb : IsLimit b.fstKernelFork) : b.IsBilimit :=
  isBinaryBilimitOfIsLimit _ <|
    BinaryFan.IsLimit.mk _ (fun f g => f ≫ b.inl + g ≫ b.inr) (fun f g => by simp)
    (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.fst = 0 := by simpa using sub_eq_zero.2 h₁
      have h₂' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.snd = 0 := by simpa using sub_eq_zero.2 h₂
      obtain ⟨q : T ⟶ Y, hq : q ≫ b.inr = m - (f ≫ b.inl + g ≫ b.inr)⟩ :=
        KernelFork.IsLimit.lift' hb _ h₁'
      rw [← sub_eq_zero, ← hq, ← Category.comp_id q, ← b.inr_snd, ← Category.assoc, hq, h₂',
        zero_comp]
#align category_theory.limits.binary_bicone.is_bilimit_of_kernel_inr CategoryTheory.Limits.BinaryBicone.isBilimitOfKernelInr

/-- If `b` is a binary bicone such that `b.fst` is a cokernel of `b.inr`, then `b` is a bilimit
    bicone. -/
def BinaryBicone.isBilimitOfCokernelFst {X Y : C} (b : BinaryBicone X Y)
    (hb : IsColimit b.inrCokernelCofork) : b.IsBilimit :=
  isBinaryBilimitOfIsColimit _ <|
    BinaryCofan.IsColimit.mk _ (fun f g => b.fst ≫ f + b.snd ≫ g) (fun f g => by simp)
      (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : b.inl ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₁
      have h₂' : b.inr ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₂
      obtain ⟨q : X ⟶ T, hq : b.fst ≫ q = m - (b.fst ≫ f + b.snd ≫ g)⟩ :=
        CokernelCofork.IsColimit.desc' hb _ h₂'
      rw [← sub_eq_zero, ← hq, ← Category.id_comp q, ← b.inl_fst, Category.assoc, hq, h₁',
        comp_zero]
#align category_theory.limits.binary_bicone.is_bilimit_of_cokernel_fst CategoryTheory.Limits.BinaryBicone.isBilimitOfCokernelFst

/-- If `b` is a binary bicone such that `b.snd` is a cokernel of `b.inl`, then `b` is a bilimit
    bicone. -/
def BinaryBicone.isBilimitOfCokernelSnd {X Y : C} (b : BinaryBicone X Y)
    (hb : IsColimit b.inlCokernelCofork) : b.IsBilimit :=
  isBinaryBilimitOfIsColimit _ <|
    BinaryCofan.IsColimit.mk _ (fun f g => b.fst ≫ f + b.snd ≫ g) (fun f g => by simp)
      (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : b.inl ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₁
      have h₂' : b.inr ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₂
      obtain ⟨q : Y ⟶ T, hq : b.snd ≫ q = m - (b.fst ≫ f + b.snd ≫ g)⟩ :=
        CokernelCofork.IsColimit.desc' hb _ h₁'
      rw [← sub_eq_zero, ← hq, ← Category.id_comp q, ← b.inr_snd, Category.assoc, hq, h₂',
        comp_zero]
#align category_theory.limits.binary_bicone.is_bilimit_of_cokernel_snd CategoryTheory.Limits.BinaryBicone.isBilimitOfCokernelSnd

/-- Every split epi `f` with a kernel induces a binary bicone with `f` as its `snd` and
the kernel map as its `inl`.
We will show in `binary_bicone_of_is_split_mono_of_cokernel` that this binary bicone is in fact
already a biproduct. -/
@[simps]
def binaryBiconeOfIsSplitEpiOfKernel {X Y : C} {f : X ⟶ Y} [IsSplitEpi f] {c : KernelFork f}
    (i : IsLimit c) : BinaryBicone c.pt Y :=
  { pt := X
    fst :=
      let c' : KernelFork (𝟙 X - (𝟙 X - f ≫ section_ f)) := KernelFork.ofι (Fork.ι c) (by simp)
      let i' : IsLimit c' := isKernelCompMono i (section_ f) (by simp)
      let i'' := isLimitForkOfKernelFork i'
      (splitMonoOfIdempotentOfIsLimitFork C (by simp) i'').retraction
    snd := f
    inl := c.ι
    inr := section_ f
    inl_fst := by apply SplitMono.id
    inl_snd := by simp
    inr_fst := by
      dsimp only
      rw [splitMonoOfIdempotentOfIsLimitFork_retraction, isLimitForkOfKernelFork_lift,
        isKernelCompMono_lift]
      dsimp only [kernelForkOfFork_ι]
      letI := mono_of_isLimit_fork i
      apply zero_of_comp_mono c.ι
      simp only [comp_sub, Category.comp_id, Category.assoc, sub_self, Fork.IsLimit.lift_ι,
        Fork.ι_ofι, IsSplitEpi.id_assoc]
    inr_snd := by simp }
#align category_theory.limits.binary_bicone_of_is_split_epi_of_kernel CategoryTheory.Limits.binaryBiconeOfIsSplitEpiOfKernel

/-- The bicone constructed in `binaryBiconeOfIsSplitEpiOfKernel` is a bilimit.
This is a version of the splitting lemma that holds in all preadditive categories. -/
def isBilimitBinaryBiconeOfIsSplitEpiOfKernel {X Y : C} {f : X ⟶ Y} [IsSplitEpi f]
    {c : KernelFork f} (i : IsLimit c) : (binaryBiconeOfIsSplitEpiOfKernel i).IsBilimit :=
  BinaryBicone.isBilimitOfKernelInl _ <| i.ofIsoLimit <| Fork.ext (Iso.refl _) (by simp)
#align category_theory.limits.is_bilimit_binary_bicone_of_is_split_epi_of_kernel CategoryTheory.Limits.isBilimitBinaryBiconeOfIsSplitEpiOfKernel

end

section

variable {X Y : C} (f g : X ⟶ Y)

/-- The existence of binary biproducts implies that there is at most one preadditive structure. -/
theorem biprod.add_eq_lift_id_desc [HasBinaryBiproduct X X] :
    f + g = biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g := by simp
#align category_theory.limits.biprod.add_eq_lift_id_desc CategoryTheory.Limits.biprod.add_eq_lift_id_desc

/-- The existence of binary biproducts implies that there is at most one preadditive structure. -/
theorem biprod.add_eq_lift_desc_id [HasBinaryBiproduct Y Y] :
    f + g = biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y) := by simp
#align category_theory.limits.biprod.add_eq_lift_desc_id CategoryTheory.Limits.biprod.add_eq_lift_desc_id

end

end Limits

open CategoryTheory.Limits

section

attribute [local ext] Preadditive

/-- The existence of binary biproducts implies that there is at most one preadditive structure. -/
instance subsingleton_preadditive_of_hasBinaryBiproducts {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] [HasBinaryBiproducts C] : Subsingleton (Preadditive C) where
  allEq := fun a b => by
    apply Preadditive.ext; funext X Y; apply AddCommGroup.ext; funext f g
    have h₁ := @biprod.add_eq_lift_id_desc _ _ a _ _ f g
      (by convert (inferInstance : HasBinaryBiproduct X X); apply Subsingleton.elim)
    have h₂ := @biprod.add_eq_lift_id_desc _ _ b _ _ f g
      (by convert (inferInstance : HasBinaryBiproduct X X); apply Subsingleton.elim)
    refine h₁.trans (Eq.trans ?_ h₂.symm)
    congr! 2 <;> apply Subsingleton.elim
#align category_theory.subsingleton_preadditive_of_has_binary_biproducts CategoryTheory.subsingleton_preadditive_of_hasBinaryBiproducts

end

section

variable [HasBinaryBiproducts.{v} C]
variable {X₁ X₂ Y₁ Y₂ : C}
variable (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂)

/-- The "matrix" morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` with specified components.
-/
def Biprod.ofComponents : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂ :=
  biprod.fst ≫ f₁₁ ≫ biprod.inl + biprod.fst ≫ f₁₂ ≫ biprod.inr + biprod.snd ≫ f₂₁ ≫ biprod.inl +
    biprod.snd ≫ f₂₂ ≫ biprod.inr
#align category_theory.biprod.of_components CategoryTheory.Biprod.ofComponents

@[simp]
theorem Biprod.inl_ofComponents :
    biprod.inl ≫ Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ = f₁₁ ≫ biprod.inl + f₁₂ ≫ biprod.inr := by
  simp [Biprod.ofComponents]
#align category_theory.biprod.inl_of_components CategoryTheory.Biprod.inl_ofComponents

@[simp]
theorem Biprod.inr_ofComponents :
    biprod.inr ≫ Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ = f₂₁ ≫ biprod.inl + f₂₂ ≫ biprod.inr := by
  simp [Biprod.ofComponents]
#align category_theory.biprod.inr_of_components CategoryTheory.Biprod.inr_ofComponents

@[simp]
theorem Biprod.ofComponents_fst :
    Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.fst = biprod.fst ≫ f₁₁ + biprod.snd ≫ f₂₁ := by
  simp [Biprod.ofComponents]
#align category_theory.biprod.of_components_fst CategoryTheory.Biprod.ofComponents_fst

@[simp]
theorem Biprod.ofComponents_snd :
    Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.snd = biprod.fst ≫ f₁₂ + biprod.snd ≫ f₂₂ := by
  simp [Biprod.ofComponents]
#align category_theory.biprod.of_components_snd CategoryTheory.Biprod.ofComponents_snd

@[simp]
theorem Biprod.ofComponents_eq (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂) :
    Biprod.ofComponents (biprod.inl ≫ f ≫ biprod.fst) (biprod.inl ≫ f ≫ biprod.snd)
        (biprod.inr ≫ f ≫ biprod.fst) (biprod.inr ≫ f ≫ biprod.snd) =
      f := by
  ext <;>
    simp only [Category.comp_id, biprod.inr_fst, biprod.inr_snd, biprod.inl_snd, add_zero, zero_add,
      Biprod.inl_ofComponents, Biprod.inr_ofComponents, eq_self_iff_true, Category.assoc,
      comp_zero, biprod.inl_fst, Preadditive.add_comp]
#align category_theory.biprod.of_components_eq CategoryTheory.Biprod.ofComponents_eq

@[simp]
theorem Biprod.ofComponents_comp {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂)
    (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) (g₁₁ : Y₁ ⟶ Z₁) (g₁₂ : Y₁ ⟶ Z₂) (g₂₁ : Y₂ ⟶ Z₁)
    (g₂₂ : Y₂ ⟶ Z₂) :
    Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫ Biprod.ofComponents g₁₁ g₁₂ g₂₁ g₂₂ =
      Biprod.ofComponents (f₁₁ ≫ g₁₁ + f₁₂ ≫ g₂₁) (f₁₁ ≫ g₁₂ + f₁₂ ≫ g₂₂) (f₂₁ ≫ g₁₁ + f₂₂ ≫ g₂₁)
        (f₂₁ ≫ g₁₂ + f₂₂ ≫ g₂₂) := by
  dsimp [Biprod.ofComponents]
  ext <;>
    simp only [add_comp, comp_add, add_comp_assoc, add_zero, zero_add, biprod.inl_fst,
      biprod.inl_snd, biprod.inr_fst, biprod.inr_snd, biprod.inl_fst_assoc, biprod.inl_snd_assoc,
      biprod.inr_fst_assoc, biprod.inr_snd_assoc, comp_zero, zero_comp, Category.assoc]
#align category_theory.biprod.of_components_comp CategoryTheory.Biprod.ofComponents_comp

/-- The unipotent upper triangular matrix
```
(1 r)
(0 1)
```
as an isomorphism.
-/
@[simps]
def Biprod.unipotentUpper {X₁ X₂ : C} (r : X₁ ⟶ X₂) : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂ where
  hom := Biprod.ofComponents (𝟙 _) r 0 (𝟙 _)
  inv := Biprod.ofComponents (𝟙 _) (-r) 0 (𝟙 _)
#align category_theory.biprod.unipotent_upper CategoryTheory.Biprod.unipotentUpper

/-- The unipotent lower triangular matrix
```
(1 0)
(r 1)
```
as an isomorphism.
-/
@[simps]
def Biprod.unipotentLower {X₁ X₂ : C} (r : X₂ ⟶ X₁) : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂ where
  hom := Biprod.ofComponents (𝟙 _) 0 r (𝟙 _)
  inv := Biprod.ofComponents (𝟙 _) 0 (-r) (𝟙 _)
#align category_theory.biprod.unipotent_lower CategoryTheory.Biprod.unipotentLower

/-- If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
via Gaussian elimination.

(This is the version of `Biprod.gaussian` written in terms of components.)
-/
def Biprod.gaussian' [IsIso f₁₁] :
    Σ' (L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂) (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂) (g₂₂ : X₂ ⟶ Y₂),
      L.hom ≫ Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫ R.hom = biprod.map f₁₁ g₂₂ :=
  ⟨Biprod.unipotentLower (-f₂₁ ≫ inv f₁₁), Biprod.unipotentUpper (-inv f₁₁ ≫ f₁₂),
    f₂₂ - f₂₁ ≫ inv f₁₁ ≫ f₁₂, by ext <;> simp; abel⟩
#align category_theory.biprod.gaussian' CategoryTheory.Biprod.gaussian'

/-- If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
via Gaussian elimination.
-/
def Biprod.gaussian (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂) [IsIso (biprod.inl ≫ f ≫ biprod.fst)] :
    Σ' (L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂) (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂) (g₂₂ : X₂ ⟶ Y₂),
      L.hom ≫ f ≫ R.hom = biprod.map (biprod.inl ≫ f ≫ biprod.fst) g₂₂ := by
  let this :=
    Biprod.gaussian' (biprod.inl ≫ f ≫ biprod.fst) (biprod.inl ≫ f ≫ biprod.snd)
      (biprod.inr ≫ f ≫ biprod.fst) (biprod.inr ≫ f ≫ biprod.snd)
  rwa [Biprod.ofComponents_eq] at this
#align category_theory.biprod.gaussian CategoryTheory.Biprod.gaussian

/-- If `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` via a two-by-two matrix whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct an isomorphism `X₂ ≅ Y₂`, via Gaussian elimination.
-/
def Biprod.isoElim' [IsIso f₁₁] [IsIso (Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂)] : X₂ ≅ Y₂ := by
  obtain ⟨L, R, g, w⟩ := Biprod.gaussian' f₁₁ f₁₂ f₂₁ f₂₂
  letI : IsIso (biprod.map f₁₁ g) := by
    rw [← w]
    infer_instance
  letI : IsIso g := isIso_right_of_isIso_biprod_map f₁₁ g
  exact asIso g
#align category_theory.biprod.iso_elim' CategoryTheory.Biprod.isoElim'

/-- If `f` is an isomorphism `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct an isomorphism `X₂ ≅ Y₂`, via Gaussian elimination.
-/
def Biprod.isoElim (f : X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂) [IsIso (biprod.inl ≫ f.hom ≫ biprod.fst)] : X₂ ≅ Y₂ :=
  letI :
    IsIso
      (Biprod.ofComponents (biprod.inl ≫ f.hom ≫ biprod.fst) (biprod.inl ≫ f.hom ≫ biprod.snd)
        (biprod.inr ≫ f.hom ≫ biprod.fst) (biprod.inr ≫ f.hom ≫ biprod.snd)) := by
    simp only [Biprod.ofComponents_eq]
    infer_instance
  Biprod.isoElim' (biprod.inl ≫ f.hom ≫ biprod.fst) (biprod.inl ≫ f.hom ≫ biprod.snd)
    (biprod.inr ≫ f.hom ≫ biprod.fst) (biprod.inr ≫ f.hom ≫ biprod.snd)
#align category_theory.biprod.iso_elim CategoryTheory.Biprod.isoElim

theorem Biprod.column_nonzero_of_iso {W X Y Z : C} (f : W ⊞ X ⟶ Y ⊞ Z) [IsIso f] :
    𝟙 W = 0 ∨ biprod.inl ≫ f ≫ biprod.fst ≠ 0 ∨ biprod.inl ≫ f ≫ biprod.snd ≠ 0 := by
  by_contra! h
  rcases h with ⟨nz, a₁, a₂⟩
  set x := biprod.inl ≫ f ≫ inv f ≫ biprod.fst
  have h₁ : x = 𝟙 W := by simp [x]
  have h₀ : x = 0 := by
    dsimp [x]
    rw [← Category.id_comp (inv f), Category.assoc, ← biprod.total]
    conv_lhs =>
      slice 2 3
      rw [comp_add]
    simp only [Category.assoc]
    rw [comp_add_assoc, add_comp]
    conv_lhs =>
      congr
      next => skip
      slice 1 3
      rw [a₂]
    simp only [zero_comp, add_zero]
    conv_lhs =>
      slice 1 3
      rw [a₁]
    simp only [zero_comp]
  exact nz (h₁.symm.trans h₀)
#align category_theory.biprod.column_nonzero_of_iso CategoryTheory.Biprod.column_nonzero_of_iso

end

theorem Biproduct.column_nonzero_of_iso' {σ τ : Type} [Finite τ] {S : σ → C} [HasBiproduct S]
    {T : τ → C} [HasBiproduct T] (s : σ) (f : ⨁ S ⟶ ⨁ T) [IsIso f] :
    (∀ t : τ, biproduct.ι S s ≫ f ≫ biproduct.π T t = 0) → 𝟙 (S s) = 0 := by
  cases nonempty_fintype τ
  intro z
  have reassoced {t : τ} {W : C} (h : _ ⟶ W) :
    biproduct.ι S s ≫ f ≫ biproduct.π T t ≫ h = 0 ≫ h := by
    simp only [← Category.assoc]
    apply eq_whisker
    simp only [Category.assoc]
    apply z
  set x := biproduct.ι S s ≫ f ≫ inv f ≫ biproduct.π S s
  have h₁ : x = 𝟙 (S s) := by simp [x]
  have h₀ : x = 0 := by
    dsimp [x]
    rw [← Category.id_comp (inv f), Category.assoc, ← biproduct.total]
    simp only [comp_sum_assoc]
    conv_lhs =>
      congr
      congr
      next => skip
      intro j; simp only [reassoced]
    simp
  exact h₁.symm.trans h₀
#align category_theory.biproduct.column_nonzero_of_iso' CategoryTheory.Biproduct.column_nonzero_of_iso'

/-- If `f : ⨁ S ⟶ ⨁ T` is an isomorphism, and `s` is a non-trivial summand of the source,
then there is some `t` in the target so that the `s, t` matrix entry of `f` is nonzero.
-/
def Biproduct.columnNonzeroOfIso {σ τ : Type} [Fintype τ] {S : σ → C} [HasBiproduct S] {T : τ → C}
    [HasBiproduct T] (s : σ) (nz : 𝟙 (S s) ≠ 0) (f : ⨁ S ⟶ ⨁ T) [IsIso f] :
    Trunc (Σ't : τ, biproduct.ι S s ≫ f ≫ biproduct.π T t ≠ 0) := by
  classical
    apply truncSigmaOfExists
    have t := Biproduct.column_nonzero_of_iso'.{v} s f
    by_contra h
    simp only [not_exists_not] at h
    exact nz (t h)
#align category_theory.biproduct.column_nonzero_of_iso CategoryTheory.Biproduct.columnNonzeroOfIso

section Preadditive

variable {D : Type u'} [Category.{v'} D] [Preadditive.{v'} D]
variable (F : C ⥤ D) [PreservesZeroMorphisms F]

namespace Limits

section Fintype

variable {J : Type} [Fintype J]

/-- A functor between preadditive categories that preserves (zero morphisms and) finite biproducts
    preserves finite products. -/
def preservesProductOfPreservesBiproduct {f : J → C} [PreservesBiproduct f F] :
    PreservesLimit (Discrete.functor f) F where
  preserves hc :=
    IsLimit.ofIsoLimit
        ((IsLimit.postcomposeInvEquiv (Discrete.compNatIsoDiscrete _ _) _).symm
          (isBilimitOfPreserves F (biconeIsBilimitOfLimitConeOfIsLimit hc)).isLimit) <|
      Cones.ext (Iso.refl _) (by rintro ⟨⟩; simp)
#align category_theory.limits.preserves_product_of_preserves_biproduct CategoryTheory.Limits.preservesProductOfPreservesBiproduct

section

attribute [local instance] preservesProductOfPreservesBiproduct

/-- A functor between preadditive categories that preserves (zero morphisms and) finite biproducts
    preserves finite products. -/
def preservesProductsOfShapeOfPreservesBiproductsOfShape [PreservesBiproductsOfShape J F] :
    PreservesLimitsOfShape (Discrete J) F where
  preservesLimit {_} := preservesLimitOfIsoDiagram _ Discrete.natIsoFunctor.symm
#align category_theory.limits.preserves_products_of_shape_of_preserves_biproducts_of_shape CategoryTheory.Limits.preservesProductsOfShapeOfPreservesBiproductsOfShape

end

/-- A functor between preadditive categories that preserves (zero morphisms and) finite products
    preserves finite biproducts. -/
def preservesBiproductOfPreservesProduct {f : J → C} [PreservesLimit (Discrete.functor f) F] :
    PreservesBiproduct f F where
  preserves {b} hb :=
    isBilimitOfIsLimit _ <|
      IsLimit.ofIsoLimit
          ((IsLimit.postcomposeHomEquiv (Discrete.compNatIsoDiscrete _ _) (F.mapCone b.toCone)).symm
            (isLimitOfPreserves F hb.isLimit)) <|
        Cones.ext (Iso.refl _) (by rintro ⟨⟩; simp)
#align category_theory.limits.preserves_biproduct_of_preserves_product CategoryTheory.Limits.preservesBiproductOfPreservesProduct

/-- If the (product-like) biproduct comparison for `F` and `f` is a monomorphism, then `F`
    preserves the biproduct of `f`. For the converse, see `mapBiproduct`. -/
def preservesBiproductOfMonoBiproductComparison {f : J → C} [HasBiproduct f]
    [HasBiproduct (F.obj ∘ f)] [Mono (biproductComparison F f)] : PreservesBiproduct f F := by
  haveI : HasProduct fun b => F.obj (f b) := by
    change HasProduct (F.obj ∘ f)
    infer_instance
  have that : piComparison F f =
      (F.mapIso (biproduct.isoProduct f)).inv ≫
        biproductComparison F f ≫ (biproduct.isoProduct _).hom := by
    ext j
    convert piComparison_comp_π F f j; simp [← Functor.map_comp]
  haveI : IsIso (biproductComparison F f) := isIso_of_mono_of_isSplitEpi _
  haveI : IsIso (piComparison F f) := by
    rw [that]
    infer_instance
  haveI := PreservesProduct.ofIsoComparison F f
  apply preservesBiproductOfPreservesProduct
#align category_theory.limits.preserves_biproduct_of_mono_biproduct_comparison CategoryTheory.Limits.preservesBiproductOfMonoBiproductComparison

/-- If the (coproduct-like) biproduct comparison for `F` and `f` is an epimorphism, then `F`
    preserves the biproduct of `F` and `f`. For the converse, see `mapBiproduct`. -/
def preservesBiproductOfEpiBiproductComparison' {f : J → C} [HasBiproduct f]
    [HasBiproduct (F.obj ∘ f)] [Epi (biproductComparison' F f)] : PreservesBiproduct f F := by
  haveI : Epi (splitEpiBiproductComparison F f).section_ := by simpa
  haveI : IsIso (biproductComparison F f) :=
    IsIso.of_epi_section' (splitEpiBiproductComparison F f)
  apply preservesBiproductOfMonoBiproductComparison
#align category_theory.limits.preserves_biproduct_of_epi_biproduct_comparison' CategoryTheory.Limits.preservesBiproductOfEpiBiproductComparison'

/-- A functor between preadditive categories that preserves (zero morphisms and) finite products
    preserves finite biproducts. -/
def preservesBiproductsOfShapeOfPreservesProductsOfShape [PreservesLimitsOfShape (Discrete J) F] :
    PreservesBiproductsOfShape J F where
  preserves {_} := preservesBiproductOfPreservesProduct F
#align category_theory.limits.preserves_biproducts_of_shape_of_preserves_products_of_shape CategoryTheory.Limits.preservesBiproductsOfShapeOfPreservesProductsOfShape

/-- A functor between preadditive categories that preserves (zero morphisms and) finite biproducts
    preserves finite coproducts. -/
def preservesCoproductOfPreservesBiproduct {f : J → C} [PreservesBiproduct f F] :
    PreservesColimit (Discrete.functor f) F where
  preserves {c} hc :=
    IsColimit.ofIsoColimit
        ((IsColimit.precomposeHomEquiv (Discrete.compNatIsoDiscrete _ _) _).symm
          (isBilimitOfPreserves F (biconeIsBilimitOfColimitCoconeOfIsColimit hc)).isColimit) <|
      Cocones.ext (Iso.refl _) (by rintro ⟨⟩; simp)
#align category_theory.limits.preserves_coproduct_of_preserves_biproduct CategoryTheory.Limits.preservesCoproductOfPreservesBiproduct

section

attribute [local instance] preservesCoproductOfPreservesBiproduct

/-- A functor between preadditive categories that preserves (zero morphisms and) finite biproducts
    preserves finite coproducts. -/
def preservesCoproductsOfShapeOfPreservesBiproductsOfShape [PreservesBiproductsOfShape J F] :
    PreservesColimitsOfShape (Discrete J) F where
  preservesColimit {_} := preservesColimitOfIsoDiagram _ Discrete.natIsoFunctor.symm
#align category_theory.limits.preserves_coproducts_of_shape_of_preserves_biproducts_of_shape CategoryTheory.Limits.preservesCoproductsOfShapeOfPreservesBiproductsOfShape

end

/-- A functor between preadditive categories that preserves (zero morphisms and) finite coproducts
    preserves finite biproducts. -/
def preservesBiproductOfPreservesCoproduct {f : J → C} [PreservesColimit (Discrete.functor f) F] :
    PreservesBiproduct f F where
  preserves {b} hb :=
    isBilimitOfIsColimit _ <|
      IsColimit.ofIsoColimit
          ((IsColimit.precomposeInvEquiv (Discrete.compNatIsoDiscrete _ _)
                (F.mapCocone b.toCocone)).symm
            (isColimitOfPreserves F hb.isColimit)) <|
        Cocones.ext (Iso.refl _) (by rintro ⟨⟩; simp)
#align category_theory.limits.preserves_biproduct_of_preserves_coproduct CategoryTheory.Limits.preservesBiproductOfPreservesCoproduct

/-- A functor between preadditive categories that preserves (zero morphisms and) finite coproducts
    preserves finite biproducts. -/
def preservesBiproductsOfShapeOfPreservesCoproductsOfShape
    [PreservesColimitsOfShape (Discrete J) F] : PreservesBiproductsOfShape J F where
  preserves {_} := preservesBiproductOfPreservesCoproduct F
#align category_theory.limits.preserves_biproducts_of_shape_of_preserves_coproducts_of_shape CategoryTheory.Limits.preservesBiproductsOfShapeOfPreservesCoproductsOfShape

end Fintype

/-- A functor between preadditive categories that preserves (zero morphisms and) binary biproducts
    preserves binary products. -/
def preservesBinaryProductOfPreservesBinaryBiproduct {X Y : C} [PreservesBinaryBiproduct X Y F] :
    PreservesLimit (pair X Y) F where
  preserves {c} hc := IsLimit.ofIsoLimit
        ((IsLimit.postcomposeInvEquiv (diagramIsoPair _) _).symm
          (isBinaryBilimitOfPreserves F (binaryBiconeIsBilimitOfLimitConeOfIsLimit hc)).isLimit) <|
      Cones.ext (by dsimp; rfl) fun j => by
        rcases j with ⟨⟨⟩⟩ <;> simp
#align category_theory.limits.preserves_binary_product_of_preserves_binary_biproduct CategoryTheory.Limits.preservesBinaryProductOfPreservesBinaryBiproduct

section

attribute [local instance] preservesBinaryProductOfPreservesBinaryBiproduct

/-- A functor between preadditive categories that preserves (zero morphisms and) binary biproducts
    preserves binary products. -/
def preservesBinaryProductsOfPreservesBinaryBiproducts [PreservesBinaryBiproducts F] :
    PreservesLimitsOfShape (Discrete WalkingPair) F where
  preservesLimit {_} := preservesLimitOfIsoDiagram _ (diagramIsoPair _).symm
#align category_theory.limits.preserves_binary_products_of_preserves_binary_biproducts CategoryTheory.Limits.preservesBinaryProductsOfPreservesBinaryBiproducts

end

/-- A functor between preadditive categories that preserves (zero morphisms and) binary products
    preserves binary biproducts. -/
def preservesBinaryBiproductOfPreservesBinaryProduct {X Y : C} [PreservesLimit (pair X Y) F] :
    PreservesBinaryBiproduct X Y F where
  preserves {b} hb := isBinaryBilimitOfIsLimit _ <| IsLimit.ofIsoLimit
          ((IsLimit.postcomposeHomEquiv (diagramIsoPair _) (F.mapCone b.toCone)).symm
            (isLimitOfPreserves F hb.isLimit)) <|
        Cones.ext (by dsimp; rfl) fun j => by
          rcases j with ⟨⟨⟩⟩ <;> simp
#align category_theory.limits.preserves_binary_biproduct_of_preserves_binary_product CategoryTheory.Limits.preservesBinaryBiproductOfPreservesBinaryProduct

/-- If the (product-like) biproduct comparison for `F`, `X` and `Y` is a monomorphism, then
    `F` preserves the biproduct of `X` and `Y`. For the converse, see `map_biprod`. -/
def preservesBinaryBiproductOfMonoBiprodComparison {X Y : C} [HasBinaryBiproduct X Y]
    [HasBinaryBiproduct (F.obj X) (F.obj Y)] [Mono (biprodComparison F X Y)] :
    PreservesBinaryBiproduct X Y F := by
  have that :
    prodComparison F X Y =
      (F.mapIso (biprod.isoProd X Y)).inv ≫ biprodComparison F X Y ≫ (biprod.isoProd _ _).hom := by
    ext <;> simp [← Functor.map_comp]
  haveI : IsIso (biprodComparison F X Y) := isIso_of_mono_of_isSplitEpi _
  haveI : IsIso (prodComparison F X Y) := by
    rw [that]
    infer_instance
  haveI := PreservesLimitPair.ofIsoProdComparison F X Y
  apply preservesBinaryBiproductOfPreservesBinaryProduct
#align category_theory.limits.preserves_binary_biproduct_of_mono_biprod_comparison CategoryTheory.Limits.preservesBinaryBiproductOfMonoBiprodComparison

/-- If the (coproduct-like) biproduct comparison for `F`, `X` and `Y` is an epimorphism, then
    `F` preserves the biproduct of `X` and `Y`. For the converse, see `mapBiprod`. -/
def preservesBinaryBiproductOfEpiBiprodComparison' {X Y : C} [HasBinaryBiproduct X Y]
    [HasBinaryBiproduct (F.obj X) (F.obj Y)] [Epi (biprodComparison' F X Y)] :
    PreservesBinaryBiproduct X Y F := by
  haveI : Epi (splitEpiBiprodComparison F X Y).section_ := by simpa
  haveI : IsIso (biprodComparison F X Y) :=
    IsIso.of_epi_section' (splitEpiBiprodComparison F X Y)
  apply preservesBinaryBiproductOfMonoBiprodComparison
#align category_theory.limits.preserves_binary_biproduct_of_epi_biprod_comparison' CategoryTheory.Limits.preservesBinaryBiproductOfEpiBiprodComparison'

/-- A functor between preadditive categories that preserves (zero morphisms and) binary products
    preserves binary biproducts. -/
def preservesBinaryBiproductsOfPreservesBinaryProducts
    [PreservesLimitsOfShape (Discrete WalkingPair) F] : PreservesBinaryBiproducts F where
  preserves {_} {_} := preservesBinaryBiproductOfPreservesBinaryProduct F
#align category_theory.limits.preserves_binary_biproducts_of_preserves_binary_products CategoryTheory.Limits.preservesBinaryBiproductsOfPreservesBinaryProducts

/-- A functor between preadditive categories that preserves (zero morphisms and) binary biproducts
    preserves binary coproducts. -/
def preservesBinaryCoproductOfPreservesBinaryBiproduct {X Y : C} [PreservesBinaryBiproduct X Y F] :
    PreservesColimit (pair X Y) F where
  preserves {c} hc :=
    IsColimit.ofIsoColimit
        ((IsColimit.precomposeHomEquiv (diagramIsoPair _) _).symm
          (isBinaryBilimitOfPreserves F
              (binaryBiconeIsBilimitOfColimitCoconeOfIsColimit hc)).isColimit) <|
      Cocones.ext (by dsimp; rfl) fun j => by
        rcases j with ⟨⟨⟩⟩ <;> simp
#align category_theory.limits.preserves_binary_coproduct_of_preserves_binary_biproduct CategoryTheory.Limits.preservesBinaryCoproductOfPreservesBinaryBiproduct

section

attribute [local instance] preservesBinaryCoproductOfPreservesBinaryBiproduct

/-- A functor between preadditive categories that preserves (zero morphisms and) binary biproducts
    preserves binary coproducts. -/
def preservesBinaryCoproductsOfPreservesBinaryBiproducts [PreservesBinaryBiproducts F] :
    PreservesColimitsOfShape (Discrete WalkingPair) F where
  preservesColimit {_} := preservesColimitOfIsoDiagram _ (diagramIsoPair _).symm
#align category_theory.limits.preserves_binary_coproducts_of_preserves_binary_biproducts CategoryTheory.Limits.preservesBinaryCoproductsOfPreservesBinaryBiproducts

end

/-- A functor between preadditive categories that preserves (zero morphisms and) binary coproducts
    preserves binary biproducts. -/
def preservesBinaryBiproductOfPreservesBinaryCoproduct {X Y : C} [PreservesColimit (pair X Y) F] :
    PreservesBinaryBiproduct X Y F where
  preserves {b} hb :=
    isBinaryBilimitOfIsColimit _ <|
      IsColimit.ofIsoColimit
          ((IsColimit.precomposeInvEquiv (diagramIsoPair _) (F.mapCocone b.toCocone)).symm
            (isColimitOfPreserves F hb.isColimit)) <|
        Cocones.ext (Iso.refl _) fun j => by
          rcases j with ⟨⟨⟩⟩ <;> simp
#align category_theory.limits.preserves_binary_biproduct_of_preserves_binary_coproduct CategoryTheory.Limits.preservesBinaryBiproductOfPreservesBinaryCoproduct

/-- A functor between preadditive categories that preserves (zero morphisms and) binary coproducts
    preserves binary biproducts. -/
def preservesBinaryBiproductsOfPreservesBinaryCoproducts
    [PreservesColimitsOfShape (Discrete WalkingPair) F] : PreservesBinaryBiproducts F where
  preserves {_} {_} := preservesBinaryBiproductOfPreservesBinaryCoproduct F
#align category_theory.limits.preserves_binary_biproducts_of_preserves_binary_coproducts CategoryTheory.Limits.preservesBinaryBiproductsOfPreservesBinaryCoproducts

end Limits

end Preadditive

end CategoryTheory
