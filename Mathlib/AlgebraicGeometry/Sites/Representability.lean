/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
-/
import Mathlib.CategoryTheory.MorphismProperty.Presheaf
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.GluingOneHypercover
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Representability of schemes is a local property

In this file we prove that a sheaf of types `F` on `Sch` is representable if it is
locally representable.

## References
* https://stacks.math.columbia.edu/tag/01JJ

-/

namespace AlgebraicGeometry

open CategoryTheory Category Limits Opposite

universe u

namespace Scheme

/-- Open immersions as a morphism property -/
abbrev openImmersion : MorphismProperty (Scheme.{u}) := @IsOpenImmersion

lemma openImmersion_le_monomorphisms :
    openImmersion ≤ MorphismProperty.monomorphisms Scheme.{u} := fun _ _ _ _ ↦
  MorphismProperty.monomorphisms.infer_property _

lemma mono_of_openImmersion_presheaf {F G : Scheme.{u}ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} (hf : openImmersion.presheaf f) : Mono f :=
  MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
    (MorphismProperty.presheaf_monotone (openImmersion_le_monomorphisms) _ hf)

/-
Consider the following setup:
* F is `Type u`-valued a sheaf on `Sch` with respect to the Zariski topology
* X : ι → Sch is a family of schemes
* f : Π i, yoneda.obj (X i) ⟶ F is a family relatively representable open immersions
* The family f is locally surjective with respect to the Zariski topology
-/
variable (F : Sheaf (Scheme.zariskiTopology.{u}) (Type u)) {ι : Type u}
  {X : ι → Scheme.{u}} (f : (i : ι) → yoneda.obj (X i) ⟶ F.1)
  (hf : ∀ i, openImmersion.presheaf (f i))

namespace Representability

variable {F f}
variable (i j k : ι)

/-- Let `V` denote an object representing `(X i) ×_{F} (X j)` -/
noncomputable abbrev V := (hf i).rep.pullback (f j)
/-- Let `p₁` denote the projection `V ⟶ X i` in the category `Sch`. -/
noncomputable abbrev p₁ : V hf i j ⟶ X i := (hf i).rep.fst' (f j)
/-- Let `p₂` denote the projection `V ⟶ X j` in the category `Sch`. -/
noncomputable abbrev p₂ : V hf i j ⟶ X j := (hf i).rep.snd (f j)

/-- The natural isomorphism `V i j ≅ V j i`. -/
noncomputable abbrev symmetryIso : V hf i j ≅ V hf j i :=
  ((hf i).rep.symmetryIso (hf j).rep)

lemma isOpenImmersion_p₂ (i j : ι) : IsOpenImmersion (p₂ hf i j) :=
  (hf i).property_snd (f j)

lemma symmetryIso_hom_comp_p₂ (i j : ι) :
    (symmetryIso hf i j).hom ≫ p₂ hf j i = p₁ hf i j := by
  simp

-- TODO: this should also follow from a general statement about pulling back property
-- through any choice pullback (no need to go through symmetryIso)
lemma isOpenImmersion_p₁ (i j : ι) :
    IsOpenImmersion (p₁ hf i j) := by
  have := isOpenImmersion_p₂ hf j i
  rw [← symmetryIso_hom_comp_p₂ hf]
  infer_instance

-- TODO: this should be a general statement about pullbacks of monomorphisms (might already be)
-- add in terms of both PullbackCone and CommSq API
lemma p₁_self_eq_p₂ (i : ι) :
    p₁ hf i i = p₂ hf i i := by
  have := mono_of_openImmersion_presheaf (hf i)
  apply yoneda.map_injective
  rw [← cancel_mono (f i), ((hf i).rep.isPullback' (f i)).w]

-- not sure if this is needed? (alt. should go in other file)
@[reassoc]
lemma condition (i j : ι) : yoneda.map (p₁ hf i j) ≫ f i = yoneda.map (p₂ hf i j) ≫ f j :=
  ((hf i).rep.isPullback' (f j)).w

-- again this should be a general lemma in terms of both PullbackCone and CommSq API
lemma isIso_p₁_self (i : ι) :
    IsIso (p₁ hf i i) := by
  refine ⟨(hf i).rep.lift' (𝟙 _) (𝟙 _) (by simp), ?_, by simp⟩
  dsimp
  apply Presheaf.representable.hom_ext'
  · simp
  · simp [p₁_self_eq_p₂ hf i]

-- the "triple" intersections of `X i`, `X j` and `X k`,
-- defined as a fibre product over `X i` of `V hf i j` and `V hf i k`
noncomputable def W := pullback (p₁ hf i j) (p₁ hf i k)

@[reassoc]
lemma condition₃ : (pullback.fst _ _ ≫ p₁ hf i j : W hf i j k ⟶ _ ) =
    pullback.snd _ _ ≫ p₁ hf i k := by
  apply pullback.condition

/-- TODO -/
noncomputable def q₁ : W hf i j k ⟶ X i := pullback.fst _ _ ≫ p₁ hf i j
/-- TODO -/
noncomputable def q₂ : W hf i j k ⟶ X j := pullback.fst _ _ ≫ p₂ hf i j
/-- TODO -/
noncomputable def q₃ : W hf i j k ⟶ X k := pullback.snd _ _ ≫ p₂ hf i k

/-- TODO -/
noncomputable def ιW : yoneda.obj (W hf i j k) ⟶ F.1 := yoneda.map (q₁ hf i j k) ≫ f i

@[reassoc (attr := simp)]
lemma yoneda_map_q₁_f : yoneda.map (q₁ hf i j k) ≫ f i = ιW hf i j k := rfl

@[reassoc (attr := simp)]
lemma yoneda_map_q₂_f : yoneda.map (q₂ hf i j k) ≫ f j = ιW hf i j k := by
  dsimp only [q₁, q₂, ιW]
  simp only [Functor.map_comp, assoc, condition]

@[reassoc (attr := simp)]
lemma yoneda_map_q₃_f : yoneda.map (q₃ hf i j k) ≫ f k = ιW hf i j k := by
  rw [← yoneda_map_q₁_f]
  dsimp only [q₃, q₁, ιW]
  rw [Functor.map_comp, assoc, ← condition hf i k, ← Functor.map_comp_assoc,
    ← condition₃, Functor.map_comp, assoc]

lemma eq_q₁ : pullback.snd _ _ ≫ p₁ hf i k = q₁ hf i j k := by
  apply yoneda.map_injective
  have := mono_of_openImmersion_presheaf (hf i)
  rw [← cancel_mono (f i), Functor.map_comp, assoc, yoneda_map_q₁_f,
    condition hf, ← Functor.map_comp_assoc]
  apply yoneda_map_q₃_f

variable {hf i j k} in
lemma hom_ext_W {Z : Scheme} {α β : Z ⟶ W hf i j k}
    (h₁ : α ≫ q₁ hf i j k = β ≫ q₁ hf i j k)
    (h₂ : α ≫ q₂ hf i j k = β ≫ q₂ hf i j k)
    (h₃ : α ≫ q₃ hf i j k = β ≫ q₃ hf i j k) : α = β := by
  dsimp [W]
  -- TODO: modify ext priority so that this is a single ext?
  ext1 <;> apply (hf i).rep.hom_ext'
  · simpa using h₁
  · simpa using h₂
  · simpa [eq_q₁] using h₁
  · simpa using h₃

section

variable {Z : Scheme} (a : Z ⟶ X i) (b : Z ⟶ X j) (c : Z ⟶ X k)
  (h₁ : yoneda.map a ≫ f i = yoneda.map b ≫ f j)
  (h₂ : yoneda.map a ≫ f i = yoneda.map c ≫ f k)

variable {i j k}

/-- TODO -/
noncomputable def liftW : Z ⟶ W hf i j k :=
  pullback.lift ((hf i).rep.lift' a b h₁)
    ((hf i).rep.lift' a c h₂) (by simp)

@[reassoc (attr := simp)]
lemma liftW_q₁ : liftW hf a b c h₁ h₂ ≫ q₁ hf i j k = a := by simp [liftW, q₁]

@[reassoc (attr := simp)]
lemma liftW_q₂ : liftW hf a b c h₁ h₂ ≫ q₂ hf i j k = b := by simp [liftW, q₂]

@[reassoc (attr := simp)]
lemma liftW_q₃ : liftW hf a b c h₁ h₂ ≫ q₃ hf i j k = c := by simp [liftW, q₃]

end

/-- TODO -/
@[simps]
noncomputable def glueData : GlueData where
  J := ι
  U := X
  V := fun (i, j) ↦ V hf i j
  f := p₁ hf
  f_mono i j := by
    have := isOpenImmersion_p₁ hf i j
    infer_instance
  f_id := isIso_p₁_self hf
  t i j := (hf i).rep.symmetry (hf j).rep
  t_id i := by apply (hf i).rep.hom_ext' <;> simp [p₁_self_eq_p₂ hf i]
  t' i j k := liftW hf (q₂ _ _ _ _) (q₃ _ _ _ _) (q₁ _ _ _ _) (by simp) (by simp)
  t_fac i j k := by
    dsimp
    apply (hf j).rep.hom_ext'
    · simp [eq_q₁]
      rfl
    · simpa using liftW_q₃ _ _ _ _ _ _
  cocycle i j k := by apply hom_ext_W; all_goals simp
  f_open := isOpenImmersion_p₁ hf

/-- TODO -/
noncomputable def toGlued (i : ι) : X i ⟶ (glueData hf).glued :=
  (glueData hf).ι i

/-- TODO -/
noncomputable def yonedaGluedToSheaf :
    subcanonical_zariskiTopology.yoneda.obj (glueData hf).glued ⟶ F :=
  Sheaf.homEquiv.symm (yonedaEquiv.symm
    ((glueData hf).sheafValGluedMk (fun i ↦ yonedaEquiv (f i)) (by
      intro i j
      dsimp
      apply yonedaEquiv.symm.injective
      rw [yonedaEquiv_naturality, Equiv.symm_apply_apply,
        FunctorToTypes.map_comp_apply, yonedaEquiv_naturality, yonedaEquiv_naturality,
        Equiv.symm_apply_apply, ← Functor.map_comp_assoc,
        Presheaf.representable.symmetry_fst, condition])))

@[simp]
lemma fac (i : ι) :
    yoneda.map (toGlued hf i) ≫ (yonedaGluedToSheaf hf).val = f i := by
  dsimp [yonedaGluedToSheaf, Sheaf.homEquiv, Functor.FullyFaithful.homEquiv]
  apply yonedaEquiv.injective
  rw [yonedaEquiv_apply, yonedaEquiv_apply]
  dsimp
  simp only [comp_id]
  apply GlueData.sheafValGluedMk_val

lemma fac' {i : ι} {V : Scheme.{u}} (a : V ⟶ X i) :
    (yonedaGluedToSheaf hf).val.app _ (a ≫ toGlued hf i) =
      yonedaEquiv (yoneda.map a ≫ f i) := by
  rw [← fac hf i]
  rfl

instance [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)] :
    Sheaf.IsLocallySurjective (yonedaGluedToSheaf hf) :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (show Sigma.desc (fun i ↦ yoneda.map (toGlued hf i)) ≫
      (yonedaGluedToSheaf hf).val = Sigma.desc f by aesop_cat)

lemma injective {U : Scheme} {i j : ι} (a : U ⟶ X i) (b : U ⟶ X j)
    (h : yoneda.map a ≫ f i = yoneda.map b ≫ f j) :
    a ≫ toGlued hf i = b ≫ toGlued hf j := by
  let φ : U ⟶ V hf i j := (hf i).rep.lift' a b h
  have h₁ : φ ≫ p₁ hf i j = a := by simp [φ]
  have h₂ : φ ≫ p₂ hf i j = b := by simp [φ]
  rw [← h₁, ← h₂, assoc, assoc]
  congr 1
  exact ((glueData hf).glue_condition i j).symm.trans (by simp; rfl)

instance : Sheaf.IsLocallyInjective (yonedaGluedToSheaf hf) where
  equalizerSieve_mem := by
    rintro ⟨U⟩ (α β : U ⟶ _) h
    dsimp at h
    have mem := zariskiTopology_openCover (glueData hf).openCover
    refine GrothendieckTopology.superset_covering _ ?_
      (zariskiTopology.intersection_covering (zariskiTopology.pullback_stable α mem)
        (zariskiTopology.pullback_stable β mem))
    rintro V (γ : _ ⟶ U) ⟨⟨W₁, a, _, ⟨i⟩, fac₁⟩, ⟨W₂, b, _, ⟨j⟩, fac₂⟩⟩
    change γ ≫ α = γ ≫ β
    rw [← fac₁, ← fac₂]
    apply injective
    replace h := congr_arg (F.1.map γ.op) h
    apply yonedaEquiv.injective
    simp at h
    have eq₁ := congr_fun ((yonedaGluedToSheaf hf).val.naturality γ.op) α
    have eq₂ := congr_fun ((yonedaGluedToSheaf hf).val.naturality γ.op) β
    dsimp at eq₁ eq₂
    convert h using 1
    · erw [← eq₁, ← fac₁, ← fac' hf]
      rfl
    · erw [← eq₂, ← fac₂, ← fac' hf]
      rfl

variable [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)]

instance : IsIso (yonedaGluedToSheaf hf) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (yonedaGluedToSheaf hf)]
  constructor <;> infer_instance

/-- TODO -/
noncomputable def yonedaIsoSheaf :
    subcanonical_zariskiTopology.yoneda.obj (glueData hf).glued ≅ F :=
  asIso (yonedaGluedToSheaf hf)

end Representability

include hf in
open Representability in
theorem representability [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)] :
    F.1.Representable where
  has_representation := ⟨(glueData hf).glued,
    ⟨(sheafToPresheaf _ _).mapIso (yonedaIsoSheaf hf)⟩⟩

end Scheme

end AlgebraicGeometry
