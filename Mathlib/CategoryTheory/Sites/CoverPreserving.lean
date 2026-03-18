/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.Tactic.ApplyFun
/-!
# Cover-preserving functors between sites.

In order to show that a functor is continuous, we define cover-preserving functors
between sites as functors that push covering sieves to covering sieves.
Then, a cover-preserving and compatible-preserving functor is continuous.

## Main definitions

* `CategoryTheory.CoverPreserving`: a functor between sites is cover-preserving if it
  pushes covering sieves to covering sieves
* `CategoryTheory.CompatiblePreserving`: a functor between sites is compatible-preserving
  if it pushes compatible families of elements to compatible families.

## Main results

- `CategoryTheory.isContinuous_of_coverPreserving`: If `G : C ⥤ D` is
  cover-preserving and compatible-preserving, then `G` is a continuous functor,
  i.e. `G.op ⋙ -` as a functor `(Dᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.3.
* https://stacks.math.columbia.edu/tag/00WU

-/

@[expose] public section


universe w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

open CategoryTheory Opposite CategoryTheory.Presieve.FamilyOfElements CategoryTheory.Presieve
  CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
variable {A : Type u₃} [Category.{v₃} A]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable {L : GrothendieckTopology A}

/-- A functor `G : (C, J) ⥤ (D, K)` between sites is *cover-preserving*
if for all covering sieves `R` in `C`, `R.functorPushforward G` is a covering sieve in `D`.
-/
structure CoverPreserving (G : C ⥤ D) : Prop where
  cover_preserve : ∀ {U : C} {S : Sieve U} (_ : S ∈ J U), S.functorPushforward G ∈ K (G.obj U)

/-- The identity functor on a site is cover-preserving. -/
theorem idCoverPreserving : CoverPreserving J J (𝟭 _) :=
  ⟨fun hS => by simpa using hS⟩

/-- The composition of two cover-preserving functors is cover-preserving. -/
theorem CoverPreserving.comp {F} (hF : CoverPreserving J K F) {G} (hG : CoverPreserving K L G) :
    CoverPreserving J L (F ⋙ G) :=
  ⟨fun hS => by
    rw [Sieve.functorPushforward_comp]
    exact hG.cover_preserve (hF.cover_preserve hS)⟩

/-- A functor `G : (C, J) ⥤ (D, K)` between sites is called compatible preserving if for each
compatible family of elements at `C` and valued in `G.op ⋙ ℱ`, and each commuting diagram
`f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂`, `x g₁` and `x g₂` coincide when restricted via `fᵢ`.
This is actually stronger than merely preserving compatible families because of the definition of
`functorPushforward` used.
-/
structure CompatiblePreserving (K : GrothendieckTopology D) (G : C ⥤ D) : Prop where
  compatible :
    ∀ (ℱ : Sheaf K (Type w)) {Z} {T : Presieve Z} {x : FamilyOfElements (G.op ⋙ ℱ.obj) T}
      (_ : x.Compatible) {Y₁ Y₂} {X} (f₁ : X ⟶ G.obj Y₁) (f₂ : X ⟶ G.obj Y₂) {g₁ : Y₁ ⟶ Z}
      {g₂ : Y₂ ⟶ Z} (hg₁ : T g₁) (hg₂ : T g₂) (_ : f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂),
      ℱ.obj.map f₁.op (x g₁ hg₁) = ℱ.obj.map f₂.op (x g₂ hg₂)

section
variable {J K} {G : C ⥤ D} (hG : CompatiblePreserving.{w} K G) (ℱ : Sheaf K (Type w)) {Z : C}
variable {T : Presieve Z} {x : FamilyOfElements (G.op ⋙ ℱ.obj) T} (h : x.Compatible)
include hG h

/-- `CompatiblePreserving` functors indeed preserve compatible families. -/
theorem Presieve.FamilyOfElements.Compatible.functorPushforward :
    (x.functorPushforward G).Compatible := by
  rintro Z₁ Z₂ W g₁ g₂ f₁' f₂' H₁ H₂ eq
  unfold FamilyOfElements.functorPushforward
  rcases getFunctorPushforwardStructure H₁ with ⟨X₁, f₁, h₁, hf₁, rfl⟩
  rcases getFunctorPushforwardStructure H₂ with ⟨X₂, f₂, h₂, hf₂, rfl⟩
  suffices ℱ.obj.map (g₁ ≫ h₁).op (x f₁ hf₁) = ℱ.obj.map (g₂ ≫ h₂).op (x f₂ hf₂) by
    simpa using this
  apply hG.compatible ℱ h _ _ hf₁ hf₂
  simpa using eq

@[simp]
theorem CompatiblePreserving.apply_map {Y : C} {f : Y ⟶ Z} (hf : T f) :
    x.functorPushforward G (G.map f) (image_mem_functorPushforward G T hf) = x f hf := by
  unfold FamilyOfElements.functorPushforward
  rcases getFunctorPushforwardStructure (image_mem_functorPushforward G T hf) with
    ⟨X, g, f', hg, eq⟩
  simpa using hG.compatible ℱ h f' (𝟙 _) hg hf (by simp [eq])

end

open Limits.WalkingCospan

set_option backward.isDefEq.respectTransparency false in
theorem compatiblePreservingOfFlat {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (K : GrothendieckTopology D) (G : C ⥤ D) [RepresentablyFlat G] : CompatiblePreserving K G := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ e
  -- First, `f₁` and `f₂` form a cone over `cospan g₁ g₂ ⋙ u`.
  let c : Cone (cospan g₁ g₂ ⋙ G) :=
    (Cone.postcompose (diagramIsoCospan (cospan g₁ g₂ ⋙ G)).inv).obj (PullbackCone.mk f₁ f₂ e)
  /-
    This can then be viewed as a cospan of structured arrows, and we may obtain an arbitrary cone
    over it since `StructuredArrow W u` is cofiltered.
    Then, it suffices to prove that it is compatible when restricted onto `u(c'.X.right)`.
    -/
  let c' := IsCofiltered.cone (c.toStructuredArrow ⋙ StructuredArrow.pre _ _ _)
  have eq₁ : f₁ = (c'.pt.hom ≫ G.map (c'.π.app left).right) ≫ eqToHom (by simp) := by simp [c]
  have eq₂ : f₂ = (c'.pt.hom ≫ G.map (c'.π.app right).right) ≫ eqToHom (by simp) := by simp [c]
  conv_lhs => rw [eq₁]
  conv_rhs => rw [eq₂]
  simp only [c, op_comp, Functor.map_comp, types_comp_apply, eqToHom_op, eqToHom_map]
  apply congr_arg -- Porting note: was `congr 1` which for some reason doesn't do anything here
  -- despite goal being of the form f a = f b, with f=`ℱ.val.map (Quiver.Hom.op c'.pt.hom)`
  /-
    Since everything now falls in the image of `u`,
    the result follows from the compatibility of `x` in the image of `u`.
    -/
  injection c'.π.naturality WalkingCospan.Hom.inl with _ e₁
  injection c'.π.naturality WalkingCospan.Hom.inr with _ e₂
  exact hx (c'.π.app left).right (c'.π.app right).right hg₁ hg₂ (e₁.symm.trans e₂)

theorem compatiblePreservingOfDownwardsClosed (F : C ⥤ D) [F.Full] [F.Faithful]
    (hF : ∀ {c : C} {d : D} (_ : d ⟶ F.obj c), Σ c', F.obj c' ≅ d) : CompatiblePreserving K F := by
  constructor
  introv hx he
  obtain ⟨X', e⟩ := hF f₁
  apply (ℱ.1.mapIso e.op).toEquiv.injective
  simp only [Iso.op_hom, Iso.toEquiv_fun, ℱ.1.mapIso_hom, ← FunctorToTypes.map_comp_apply]
  simpa using
    hx (F.preimage <| e.hom ≫ f₁) (F.preimage <| e.hom ≫ f₂) hg₁ hg₂
      (F.map_injective <| by simpa using he)

variable {F J K}

/-- If `F` is cover-preserving and compatible-preserving, then `F` is a continuous functor. -/
@[stacks 00WW "This is basically this Stacks entry."]
lemma Functor.isContinuous_of_coverPreserving (hF₁ : CompatiblePreserving.{max u₁ v₁ u₂ v₂} K F)
    (hF₂ : CoverPreserving J K F) : Functor.IsContinuous F J K where
  op_comp_isSheaf_of_types G X S hS x hx := by
    apply existsUnique_of_exists_of_unique
    · have H := (isSheaf_iff_isSheaf_of_type _ _).1 G.2 _ (hF₂.cover_preserve hS)
      exact ⟨H.amalgamate (x.functorPushforward F) (hx.functorPushforward hF₁),
        fun V f hf => (H.isAmalgamation (hx.functorPushforward hF₁) (F.map f) _).trans
          (hF₁.apply_map _ hx hf)⟩
    · intro y₁ y₂ hy₁ hy₂
      apply (((isSheaf_iff_isSheaf_of_type _ _).1 G.2).isSeparated _ (hF₂.cover_preserve hS)).ext
      rintro Y _ ⟨Z, g, h, hg, rfl⟩
      dsimp
      simp only [Functor.map_comp, types_comp_apply]
      have H := (hy₁ g hg).trans (hy₂ g hg).symm
      dsimp at H
      rw [H]

end CategoryTheory
