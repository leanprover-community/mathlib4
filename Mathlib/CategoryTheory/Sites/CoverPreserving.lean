/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.ApplyFun

#align_import category_theory.sites.cover_preserving from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"
/-!
# Cover-preserving and continuous functors between sites.

We define the notion of continuous functor between sites: these are functors `G` such that
the precomposition with `G.op` preserves sheaves of types (and actually sheaves in any
category).

In order to show that a functor is continuous, we define cover-preserving functors
between sites as functors that push covering sieves to covering sieves.
Then, a cover-preserving and compatible-preserving functor is continuous.

## Main definitions

* `CategoryTheory.Functor.IsContinuous`: a functor between sites is continuous if the
precomposition with this functor preserves sheaves.
* `CategoryTheory.CoverPreserving`: a functor between sites is cover-preserving if it
pushes covering sieves to covering sieves
* `CategoryTheory.CompatiblePreserving`: a functor between sites is compatible-preserving
if it pushes compatible families of elements to compatible families.
* `CategoryTheory.Functor.sheafPushforwardContinuous`: the induced functor
`Sheaf K A ⥤ Sheaf J A` for a continuous functor `G : (C, J) ⥤ (D, K)`. In case this is
part of a morphism of sites, this would be understood as the pushforward functor
even though it goes in the opposite direction as the functor `G`.

## Main results

- `CategoryTheory.isContinuous_of_coverPreserving`: If `G : C ⥤ D` is
cover-preserving and compatible-preserving, then `G` is a continuous functor,
i.e. `G.op ⋙ -` as a functor `(Dᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.3.
* https://stacks.math.columbia.edu/tag/00WU

-/


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
-- Porting note(#5171): removed `@[nolint has_nonempty_instance]`
structure CoverPreserving (G : C ⥤ D) : Prop where
  cover_preserve : ∀ {U : C} {S : Sieve U} (_ : S ∈ J U), S.functorPushforward G ∈ K (G.obj U)
#align category_theory.cover_preserving CategoryTheory.CoverPreserving

/-- The identity functor on a site is cover-preserving. -/
theorem idCoverPreserving : CoverPreserving J J (𝟭 _) :=
  ⟨fun hS => by simpa using hS⟩
#align category_theory.id_cover_preserving CategoryTheory.idCoverPreserving

/-- The composition of two cover-preserving functors is cover-preserving. -/
theorem CoverPreserving.comp {F} (hF : CoverPreserving J K F) {G} (hG : CoverPreserving K L G) :
    CoverPreserving J L (F ⋙ G) :=
  ⟨fun hS => by
    rw [Sieve.functorPushforward_comp]
    exact hG.cover_preserve (hF.cover_preserve hS)⟩
#align category_theory.cover_preserving.comp CategoryTheory.CoverPreserving.comp

/-- A functor `G : (C, J) ⥤ (D, K)` between sites is called compatible preserving if for each
compatible family of elements at `C` and valued in `G.op ⋙ ℱ`, and each commuting diagram
`f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂`, `x g₁` and `x g₂` coincide when restricted via `fᵢ`.
This is actually stronger than merely preserving compatible families because of the definition of
`functorPushforward` used.
-/
-- Porting note(#5171): linter not ported yet @[nolint has_nonempty_instance]
structure CompatiblePreserving (K : GrothendieckTopology D) (G : C ⥤ D) : Prop where
  compatible :
    ∀ (ℱ : SheafOfTypes.{w} K) {Z} {T : Presieve Z} {x : FamilyOfElements (G.op ⋙ ℱ.val) T}
      (_ : x.Compatible) {Y₁ Y₂} {X} (f₁ : X ⟶ G.obj Y₁) (f₂ : X ⟶ G.obj Y₂) {g₁ : Y₁ ⟶ Z}
      {g₂ : Y₂ ⟶ Z} (hg₁ : T g₁) (hg₂ : T g₂) (_ : f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂),
      ℱ.val.map f₁.op (x g₁ hg₁) = ℱ.val.map f₂.op (x g₂ hg₂)
#align category_theory.compatible_preserving CategoryTheory.CompatiblePreserving

variable {J K} {G : C ⥤ D} (hG : CompatiblePreserving.{w} K G) (ℱ : SheafOfTypes.{w} K) {Z : C}
variable {T : Presieve Z} {x : FamilyOfElements (G.op ⋙ ℱ.val) T} (h : x.Compatible)

/-- `CompatiblePreserving` functors indeed preserve compatible families. -/
theorem Presieve.FamilyOfElements.Compatible.functorPushforward :
    (x.functorPushforward G).Compatible := by
  rintro Z₁ Z₂ W g₁ g₂ f₁' f₂' H₁ H₂ eq
  unfold FamilyOfElements.functorPushforward
  rcases getFunctorPushforwardStructure H₁ with ⟨X₁, f₁, h₁, hf₁, rfl⟩
  rcases getFunctorPushforwardStructure H₂ with ⟨X₂, f₂, h₂, hf₂, rfl⟩
  suffices ℱ.val.map (g₁ ≫ h₁).op (x f₁ hf₁) = ℱ.val.map (g₂ ≫ h₂).op (x f₂ hf₂) by
    simpa using this
  apply hG.compatible ℱ h _ _ hf₁ hf₂
  simpa using eq
#align category_theory.presieve.family_of_elements.compatible.functor_pushforward CategoryTheory.Presieve.FamilyOfElements.Compatible.functorPushforward

@[simp]
theorem CompatiblePreserving.apply_map {Y : C} {f : Y ⟶ Z} (hf : T f) :
    x.functorPushforward G (G.map f) (image_mem_functorPushforward G T hf) = x f hf := by
  unfold FamilyOfElements.functorPushforward
  rcases getFunctorPushforwardStructure (image_mem_functorPushforward G T hf) with
    ⟨X, g, f', hg, eq⟩
  simpa using hG.compatible ℱ h f' (𝟙 _) hg hf (by simp [eq])
#align category_theory.compatible_preserving.apply_map CategoryTheory.CompatiblePreserving.apply_map

open Limits.WalkingCospan

theorem compatiblePreservingOfFlat {C : Type u₁} [Category.{v₁} C] {D : Type u₁} [Category.{v₁} D]
    (K : GrothendieckTopology D) (G : C ⥤ D) [RepresentablyFlat G] : CompatiblePreserving K G := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ e
  -- First, `f₁` and `f₂` form a cone over `cospan g₁ g₂ ⋙ u`.
  let c : Cone (cospan g₁ g₂ ⋙ G) :=
    (Cones.postcompose (diagramIsoCospan (cospan g₁ g₂ ⋙ G)).inv).obj (PullbackCone.mk f₁ f₂ e)
  /-
    This can then be viewed as a cospan of structured arrows, and we may obtain an arbitrary cone
    over it since `StructuredArrow W u` is cofiltered.
    Then, it suffices to prove that it is compatible when restricted onto `u(c'.X.right)`.
    -/
  let c' := IsCofiltered.cone (c.toStructuredArrow ⋙ StructuredArrow.pre _ _ _)
  have eq₁ : f₁ = (c'.pt.hom ≫ G.map (c'.π.app left).right) ≫ eqToHom (by simp) := by
    erw [← (c'.π.app left).w]
    dsimp [c]
    simp
  have eq₂ : f₂ = (c'.pt.hom ≫ G.map (c'.π.app right).right) ≫ eqToHom (by simp) := by
    erw [← (c'.π.app right).w]
    dsimp [c]
    simp
  conv_lhs => rw [eq₁]
  conv_rhs => rw [eq₂]
  simp only [op_comp, Functor.map_comp, types_comp_apply, eqToHom_op, eqToHom_map]
  apply congr_arg -- Porting note: was `congr 1` which for some reason doesn't do anything here
  -- despite goal being of the form f a = f b, with f=`ℱ.val.map (Quiver.Hom.op c'.pt.hom)`
  /-
    Since everything now falls in the image of `u`,
    the result follows from the compatibility of `x` in the image of `u`.
    -/
  injection c'.π.naturality WalkingCospan.Hom.inl with _ e₁
  injection c'.π.naturality WalkingCospan.Hom.inr with _ e₂
  exact hx (c'.π.app left).right (c'.π.app right).right hg₁ hg₂ (e₁.symm.trans e₂)
#align category_theory.compatible_preserving_of_flat CategoryTheory.compatiblePreservingOfFlat

theorem compatiblePreservingOfDownwardsClosed (F : C ⥤ D) [F.Full] [F.Faithful]
    (hF : ∀ {c : C} {d : D} (_ : d ⟶ F.obj c), Σc', F.obj c' ≅ d) : CompatiblePreserving K F := by
  constructor
  introv hx he
  obtain ⟨X', e⟩ := hF f₁
  apply (ℱ.1.mapIso e.op).toEquiv.injective
  simp only [Iso.op_hom, Iso.toEquiv_fun, ℱ.1.mapIso_hom, ← FunctorToTypes.map_comp_apply]
  simpa using
    hx (F.preimage <| e.hom ≫ f₁) (F.preimage <| e.hom ≫ f₂) hg₁ hg₂
      (F.map_injective <| by simpa using he)
#align category_theory.compatible_preserving_of_downwards_closed CategoryTheory.compatiblePreservingOfDownwardsClosed

variable (J K)

/-- A functor `F` is continuous if the precomposition with `F.op` sends sheaves of `Type w`
to sheaves. -/
class Functor.IsContinuous : Prop where
  op_comp_isSheafOfTypes (G : SheafOfTypes.{w} K) : Presieve.IsSheaf J (F.op ⋙ G.val)

lemma Functor.op_comp_isSheafOfTypes [Functor.IsContinuous.{w} F J K]
    (G : SheafOfTypes.{w} K) :
    Presieve.IsSheaf J (F.op ⋙ G.val) :=
  Functor.IsContinuous.op_comp_isSheafOfTypes _

lemma Functor.isContinuous_of_iso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Functor.IsContinuous.{w} F₁ J K] : Functor.IsContinuous.{w} F₂ J K where
  op_comp_isSheafOfTypes G :=
    Presieve.isSheaf_iso J (isoWhiskerRight (NatIso.op e.symm) _)
      (F₁.op_comp_isSheafOfTypes J K G)

instance Functor.isContinuous_id : Functor.IsContinuous.{w} (𝟭 C) J J where
  op_comp_isSheafOfTypes G := G.2

lemma Functor.isContinuous_comp (F₁ : C ⥤ D) (F₂ : D ⥤ A) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (L : GrothendieckTopology A)
    [Functor.IsContinuous.{w} F₁ J K] [Functor.IsContinuous.{w} F₂ K L] :
    Functor.IsContinuous.{w} (F₁ ⋙ F₂) J L where
  op_comp_isSheafOfTypes G := F₁.op_comp_isSheafOfTypes J K ⟨_, F₂.op_comp_isSheafOfTypes K L G⟩

lemma Functor.isContinuous_comp' {F₁ : C ⥤ D} {F₂ : D ⥤ A} {F₁₂ : C ⥤ A}
    (e : F₁ ⋙ F₂ ≅ F₁₂) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (L : GrothendieckTopology A)
    [Functor.IsContinuous.{w} F₁ J K] [Functor.IsContinuous.{w} F₂ K L] :
    Functor.IsContinuous.{w} F₁₂ J L := by
  have := Functor.isContinuous_comp F₁ F₂ J K L
  apply Functor.isContinuous_of_iso e

lemma Functor.op_comp_isSheaf [Functor.IsContinuous.{v₃} F J K] (G : Sheaf K A) :
    Presheaf.IsSheaf J (F.op ⋙ G.val) :=
  fun T => F.op_comp_isSheafOfTypes J K ⟨_, G.cond T⟩

variable {F J K}

/-- If `F` is cover-preserving and compatible-preserving,
then `F` is a continuous functor.

This result is basically <https://stacks.math.columbia.edu/tag/00WW>.
-/
lemma Functor.isContinuous_of_coverPreserving (hF₁ : CompatiblePreserving.{w} K F)
    (hF₂ : CoverPreserving J K F) : Functor.IsContinuous.{w} F J K where
  op_comp_isSheafOfTypes G X S hS x hx := by
    apply exists_unique_of_exists_of_unique
    · have H := G.2 _ (hF₂.cover_preserve hS)
      exact ⟨H.amalgamate (x.functorPushforward F) (hx.functorPushforward hF₁),
        fun V f hf => (H.isAmalgamation (hx.functorPushforward hF₁) (F.map f) _).trans
          (hF₁.apply_map _ hx hf)⟩
    · intro y₁ y₂ hy₁ hy₂
      apply (Presieve.isSeparated_of_isSheaf _ _ G.cond _ (hF₂.cover_preserve hS)).ext
      rintro Y _ ⟨Z, g, h, hg, rfl⟩
      dsimp
      simp only [Functor.map_comp, types_comp_apply]
      have H := (hy₁ g hg).trans (hy₂ g hg).symm
      dsimp at H
      rw [H]

variable (F J K A)

/-- The induced functor `Sheaf K A ⥤ Sheaf J A` given by `G.op ⋙ _`
if `G` is a continuous functor.
-/
def Functor.sheafPushforwardContinuous [Functor.IsContinuous.{v₃} F J K] :
    Sheaf K A ⥤ Sheaf J A where
  obj ℱ := ⟨F.op ⋙ ℱ.val, F.op_comp_isSheaf J K ℱ⟩
  map f := ⟨((whiskeringLeft _ _ _).obj F.op).map f.val⟩
  map_id ℱ := by
    ext1
    apply ((whiskeringLeft _ _ _).obj F.op).map_id
  map_comp f g := by
    ext1
    apply ((whiskeringLeft _ _ _).obj F.op).map_comp
#align category_theory.sites.pullback CategoryTheory.Functor.sheafPushforwardContinuous

end CategoryTheory
