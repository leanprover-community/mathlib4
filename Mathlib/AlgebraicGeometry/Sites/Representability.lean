/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
-/
import Mathlib.CategoryTheory.MorphismProperty.Representable
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
-- Note(Calle): Should this be incorporated into the `OpenImmersion` file?
-- Furthermore, should this be an instance?
abbrev openImmersion : MorphismProperty (Scheme.{u}) := @IsOpenImmersion

lemma openImmersion_le_monomorphisms :
    openImmersion ≤ MorphismProperty.monomorphisms Scheme.{u} := fun _ _ _ _ ↦
  MorphismProperty.monomorphisms.infer_property _

/-
Consider the following setup:
* F is `Type u`-valued a sheaf on `Sch` with respect to the Zariski topology
* X : ι → Sch is a family of schemes
* f : Π i, yoneda.obj (X i) ⟶ F is a family relatively representable open immersions

Later, we will also assume:
* The family f is locally surjective with respect to the Zariski topology
-/
variable (F : Sheaf (Scheme.zariskiTopology.{u}) (Type u)) {ι : Type u}
  {X : ι → Scheme.{u}} (f : (i : ι) → yoneda.obj (X i) ⟶ F.1)
  (hf : ∀ i, openImmersion.presheaf (f i))

namespace Representability

variable {F f}
variable (i j k : ι)

lemma isOpenImmersion_snd (i j : ι) : IsOpenImmersion ((hf i).rep.snd (f j)) :=
  (hf i).property_snd (f j)

lemma isOpenImmersion_fst' (i j : ι) : IsOpenImmersion ((hf i).rep.fst' (f j)) :=
  (hf j).property _ _ _ ((hf i).1.isPullback' (f j)).flip

lemma fst'_self_eq_snd (i : ι) : (hf i).rep.fst' (f i) = (hf i).rep.snd (f i) :=
  openImmersion.fst'_self_eq_snd openImmersion_le_monomorphisms (hf i)

lemma isIso_fst'_self (i : ι) : IsIso ((hf i).rep.fst' (f i)) :=
  openImmersion.isIso_fst'_self openImmersion_le_monomorphisms (hf i)

open Functor.relativelyRepresentable in
/-- We get a family of gluing data by taking `U i = X i` and `V i j = (hf i).rep.pullback (f j)`. -/
@[simps]
noncomputable def glueData : GlueData where
  J := ι
  U := X
  V := fun (i, j) ↦ (hf i).rep.pullback (f j)
  f i j := (hf i).rep.fst' (f j)
  f_mono i j := by
    have := isOpenImmersion_fst' hf i j
    infer_instance
  f_id := isIso_fst'_self hf
  t i j := (hf i).rep.symmetry (hf j).rep
  t_id i := by apply (hf i).rep.hom_ext' <;> simp [fst'_self_eq_snd hf i]
  t' i j k := lift₃ _ _ _ (pullback₃.p₂ _ _ _) (pullback₃.p₃ _ _ _) (pullback₃.p₁ _ _ _)
    (by simp) (by simp)
  t_fac i j k := by apply (hf j).rep.hom_ext' <;> simp
  cocycle i j k := by apply pullback₃.hom_ext <;> simp
  f_open := isOpenImmersion_fst' hf

/-- The map from `X i` to the glued scheme `(glueData hf).glued` -/
noncomputable def toGlued (i : ι) : X i ⟶ (glueData hf).glued :=
  (glueData hf).ι i

/-- The map from the glued scheme `(glueData hf).glued`, treated as a sheaf, to `F`. -/
noncomputable def yonedaGluedToSheaf :
    subcanonical_zariskiTopology.yoneda.obj (glueData hf).glued ⟶ F :=
  -- The map is obtained by finding an object of `F((glueData hf).glued)`.
  Sheaf.homEquiv.symm (yonedaEquiv.symm
  -- This section is obtained from gluing the section corresponding to `f i : X i ⟶ F`.
    ((glueData hf).sheafValGluedMk (fun i ↦ yonedaEquiv (f i)) (by
      intro i j
      dsimp
      apply yonedaEquiv.symm.injective
      rw [yonedaEquiv_naturality, Equiv.symm_apply_apply,
        FunctorToTypes.map_comp_apply, yonedaEquiv_naturality, yonedaEquiv_naturality,
        Equiv.symm_apply_apply, ← Functor.map_comp_assoc,
        Functor.relativelyRepresentable.symmetry_fst, ((hf i).rep.isPullback' (f j)).w])))

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
  rw [← (hf i).rep.lift'_fst a b h, assoc]
  conv_rhs => rw [← (hf i).rep.lift'_snd a b h, assoc]
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

/-- The isomorphism between `yoneda.obj (glueData hf).glued` and `F`.

This implies that `F` is representable. -/
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
