/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# The distinguished triangle attached to a short exact sequence of cochain complexes

Given a short exact short complex `S` in the category `CochainComplex C ℤ`,
we construct a distinguished triangle
`Q.obj S.X₁ ⟶ Q.obj S.X₂ ⟶ Q.obj S.X₃ ⟶ (Q.obj S.X₃)⟦1⟧`
in the derived category of `C`.
(See `triangleOfSES` and `triangleOfSES_distinguished`.)

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w v u

open CategoryTheory Category Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)

/-- The connecting homomorphism `Q.obj (S.X₃) ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧`
in the derived category when `S` is a short exact short complex of
cochain complexes in an abelian category. -/
noncomputable def triangleOfSESδ :
    Q.obj (S.X₃) ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧ :=
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  inv (Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫
    Q.map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
    (Q.commShiftIso (1 : ℤ)).hom.app S.X₁

@[reassoc (attr := simp)]
lemma descShortComplex_triangleOfSESδ :
    Q.map (CochainComplex.mappingCone.descShortComplex S) ≫ triangleOfSESδ hS =
    Q.map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
      (Functor.commShiftIso Q 1).hom.app S.X₁ := by
  simp [triangleOfSESδ]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma triangleOfSESδ_naturality {S₁ S₂ : ShortComplex (CochainComplex C ℤ)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) :
    triangleOfSESδ hS₁ ≫ (Q.map f.τ₁)⟦1⟧' = Q.map f.τ₃ ≫ triangleOfSESδ hS₂ := by
  simp only [triangleOfSESδ, CochainComplex.mappingCone.triangle_obj₁, Category.assoc,
    IsIso.inv_comp_eq]
  rw [← Functor.comp_map, ← (Q.commShiftIso (1 : ℤ)).hom.naturality, ← Category.assoc,
    ← Category.assoc, ← Category.assoc, ← Category.assoc, ← Iso.app_hom,
    Iso.cancel_iso_hom_right, ← Q.map_comp]
  simp only [Functor.comp_obj, Functor.comp_map,
    ← CochainComplex.mappingCone.descShortComplex_naturality f,
    Functor.map_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← Q.map_comp, ← Q.map_comp]
  congr 1
  exact (CochainComplex.mappingCone.triangleMap S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm).comm₃

/-- The distinguished triangle in the derived category associated to a short
exact sequence of cochain complexes. -/
@[simps!]
noncomputable def triangleOfSES : Triangle (DerivedCategory C) :=
  Triangle.mk (Q.map S.f) (Q.map S.g) (triangleOfSESδ hS)

set_option backward.isDefEq.respectTransparency false in
/-- The triangle `triangleOfSES` attached to a short exact sequence `S` of cochain
complexes is isomorphic to the standard distinguished triangle associated to
the morphism `S.f`. -/
noncomputable def triangleOfSESIso :
    triangleOfSES hS ≅ Q.mapTriangle.obj (CochainComplex.mappingCone.triangle S.f) := by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  refine Iso.symm (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (asIso (Q.map (CochainComplex.mappingCone.descShortComplex S))) ?_ ?_ ?_)
  · dsimp [triangleOfSES]
    simp only [comp_id, id_comp]
  · dsimp
    simp only [← Q.map_comp, CochainComplex.mappingCone.inr_descShortComplex, id_comp]
  · dsimp [triangleOfSESδ]
    rw [CategoryTheory.Functor.map_id, comp_id, IsIso.hom_inv_id_assoc]

lemma triangleOfSES_distinguished :
    triangleOfSES hS ∈ distTriang (DerivedCategory C) := by
  rw [mem_distTriang_iff]
  exact ⟨_, _, S.f, ⟨triangleOfSESIso hS⟩⟩

section map

variable {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
  (f : S₁ ⟶ S₂)

set_option backward.isDefEq.respectTransparency false in
/--
The morphism `triangleOfSES h₁ ⟶ triangleOfSES h₂` that is induced by a morphism of short
exact sequences of cochain complexes.
-/
@[simps]
noncomputable def triangleOfSES.map : triangleOfSES h₁ ⟶ triangleOfSES h₂ where
  hom₁ := Q.map f.τ₁
  hom₂ := Q.map f.τ₂
  hom₃ := Q.map f.τ₃
  comm₁ := by simp [← Functor.map_comp, f.comm₁₂]
  comm₂ := by simp [← Functor.map_comp, f.comm₂₃]
  comm₃ := by
    dsimp [triangleOfSES, triangleOfSESδ]
    rw [assoc, assoc, IsIso.inv_comp_eq, ← Functor.map_comp_assoc,
      ← CochainComplex.mappingCone.map_descShortComplex,
      Functor.map_comp_assoc, IsIso.hom_inv_id_assoc,
      ← Functor.commShiftIso_hom_naturality,
      ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    congr 2
    exact (CochainComplex.mappingCone.triangleMap S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm).comm₃

end map

end DerivedCategory
