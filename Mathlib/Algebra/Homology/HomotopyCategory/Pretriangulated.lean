/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import Mathlib.CategoryTheory.Triangulated.Functor

/-! The pretriangulated structure on the homotopy category of complexes

In this file, we shall define the pretriangulated structure on the homotopy
category `HomotopyCategory C (ComplexShape.up ℤ)` of an additive category `C` (TODO).
The distinguished triangles are the triangles that are isomorphic to the
image in the homotopy category of the standard triangle
`K ⟶ L ⟶ mappingCone φ ⟶ K⟦(1 : ℤ)⟧` for some morphism of
cochain complexes `φ : K ⟶ L`.

This result first appeared in the Liquid Tensor Experiment. In the LTE, the
formalization followed the Stacks Project: in particular, the distinguished
triangles were defined using degreewise-split short exact sequences of cochain
complexes. Here, we follow the original definitions in [Verdiers's thesis, I.3][verdier1996]
(with the better sign conventions from the introduction of
[Brian Conrad's book *Grothendieck duality and base change*][conrad2000]).

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]
* [Brian Conrad, Grothendieck duality and base change][conrad2000]
* https://stacks.math.columbia.edu/tag/014P

-/

open CategoryTheory Category Limits CochainComplex.HomComplex Pretriangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

namespace CochainComplex

namespace mappingCone

/-- The standard triangle `K ⟶ L ⟶ mappingCone φ ⟶ K⟦(1 : ℤ)⟧` in `CochainComplex C ℤ`
attached to a morphism `φ : K ⟶ L`. It involves `φ`, `inr φ : L ⟶ mappingCone φ` and
the morphism induced by the `1`-cocycle `-mappingCone.fst φ`. -/
@[simps! obj₁ obj₂ obj₃ mor₁ mor₂]
noncomputable def triangle : Triangle (CochainComplex C ℤ) :=
  Triangle.mk φ (inr φ) (Cocycle.homOf ((-fst φ).rightShift 1 0 (zero_add 1)))

@[reassoc (attr := simp)]
lemma inl_v_triangle_mor₃_f (p q : ℤ) (hpq : p + (-1) = q) :
    (inl φ).v p q hpq ≫ (triangle φ).mor₃.f q =
      -(K.shiftFunctorObjXIso 1 q p (by rw [← hpq, neg_add_cancel_right])).inv := by
  simp [triangle, Cochain.rightShift_v _ 1 0 (zero_add 1) q q (add_zero q) p (by linarith)]

@[reassoc (attr := simp)]
lemma inr_f_triangle_mor₃_f (p : ℤ) : (inr φ).f p ≫ (triangle φ).mor₃.f p = 0 := by
  simp [triangle, Cochain.rightShift_v _ 1 0 _ p p (add_zero p) (p+1) rfl]

@[reassoc (attr := simp)]
lemma inr_triangleδ : inr φ ≫ (triangle φ).mor₃ = 0 := by aesop_cat

/-- The (distinguished) triangle in the homotopy category that is associated to
a morphism `φ : K ⟶ L` in the category `CochainComplex C ℤ`. -/
noncomputable abbrev triangleh : Triangle (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (HomotopyCategory.quotient _ _).mapTriangle.obj (triangle φ)

variable (K)

/-- The mapping cone of the identity is contractible. -/
noncomputable def homotopyToZeroOfId : Homotopy (𝟙 (mappingCone (𝟙 K))) 0 :=
  descHomotopy (𝟙 K) _ _ 0 (inl _) (by simp) (by simp)

variable {K}

section mapOfHomotopy

variable {K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex C ℤ} {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂}
  {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂} (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂))

/-- The morphism `mappingCone φ₁ ⟶ mappingCone φ₂` that is induced by a square that
is commutative up to homotopy. -/
noncomputable def mapOfHomotopy :
    mappingCone φ₁ ⟶ mappingCone φ₂ :=
  desc φ₁ ((Cochain.ofHom a).comp (inl φ₂) (zero_add _) +
    ((Cochain.equivHomotopy _ _) H).1.comp (Cochain.ofHom (inr φ₂)) (add_zero _))
    (b ≫ inr φ₂) (by simp)

@[reassoc]
lemma triangleMapOfHomotopy_comm₂ :
    inr φ₁ ≫ mapOfHomotopy H = b ≫ inr φ₂ := by
  simp [mapOfHomotopy]

@[reassoc]
lemma triangleMapOfHomotopy_comm₃ :
    mapOfHomotopy H ≫ (triangle φ₂).mor₃ = (triangle φ₁).mor₃ ≫ a⟦1⟧' := by
  ext p
  simp [ext_from_iff _ _ _ rfl, triangle, mapOfHomotopy,
    Cochain.rightShift_v _ 1 0 _ p p _ (p + 1) rfl]

/-- The morphism `triangleh φ₁ ⟶ triangleh φ₂` that is induced by a square that
is commutative up to homotopy. -/
@[simps]
noncomputable def trianglehMapOfHomotopy :
    triangleh φ₁ ⟶ triangleh φ₂ where
  hom₁ := (HomotopyCategory.quotient _ _).map a
  hom₂ := (HomotopyCategory.quotient _ _).map b
  hom₃ := (HomotopyCategory.quotient _ _).map (mapOfHomotopy H)
  comm₁ := by
    dsimp
    simp only [← Functor.map_comp]
    exact HomotopyCategory.eq_of_homotopy _ _ H
  comm₂ := by
    dsimp
    simp only [← Functor.map_comp, triangleMapOfHomotopy_comm₂]
  comm₃ := by
    dsimp
    rw [← Functor.map_comp_assoc, triangleMapOfHomotopy_comm₃, Functor.map_comp, assoc, assoc]
    erw [← NatTrans.naturality]
    rfl

end mapOfHomotopy

section map

variable {K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (φ₃ : K₃ ⟶ L₃)
  (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂)
  (a' : K₂ ⟶ K₃) (b' : L₂ ⟶ L₃) (comm' : φ₂ ≫ b' = a' ≫ φ₃)

/-- The morphism `mappingCone φ₁ ⟶ mappingCone φ₂` that is induced by a commutative square. -/
noncomputable def map : mappingCone φ₁ ⟶ mappingCone φ₂ :=
  desc φ₁ ((Cochain.ofHom a).comp (inl φ₂) (zero_add _)) (b ≫ inr φ₂)
    (by simp [reassoc_of% comm])

lemma map_eq_mapOfHomotopy : map φ₁ φ₂ a b comm = mapOfHomotopy (Homotopy.ofEq comm) := by
  simp [map, mapOfHomotopy]

lemma map_id : map φ φ (𝟙 _) (𝟙 _) (by rw [id_comp, comp_id]) = 𝟙 _ := by
  ext n
  simp [ext_from_iff _ (n + 1) n rfl, map]

@[reassoc]
lemma map_comp : map φ₁ φ₃ (a ≫ a') (b ≫ b') (by rw [reassoc_of% comm, comm', assoc]) =
    map φ₁ φ₂ a b comm ≫ map φ₂ φ₃ a' b' comm' := by
  ext n
  simp [ext_from_iff _ (n+1) n rfl, map]

/-- The morphism `triangle φ₁ ⟶ triangle φ₂` that is induced by a commutative square. -/
@[simps]
noncomputable def triangleMap :
    triangle φ₁ ⟶ triangle φ₂ where
  hom₁ := a
  hom₂ := b
  hom₃ := map φ₁ φ₂ a b comm
  comm₁ := comm
  comm₂ := by
    dsimp
    rw [map_eq_mapOfHomotopy, triangleMapOfHomotopy_comm₂]
  comm₃ := by
    dsimp
    rw [map_eq_mapOfHomotopy, triangleMapOfHomotopy_comm₃]

end map

end mappingCone

end CochainComplex
