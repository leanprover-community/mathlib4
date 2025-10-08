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

## Main result
- `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`:
  Suppose
  * F is a `Type u`-valued sheaf on `Sch` with respect to the Zariski topology
  * X : ι → Sch is a family of schemes
  * f : Π i, yoneda.obj (X i) ⟶ F is a family of relatively representable open immersions
  * f is jointly surjective

  Then `F` is representable.

## References
* https://stacks.math.columbia.edu/tag/01JJ

-/

namespace AlgebraicGeometry

open CategoryTheory Category Limits Opposite

attribute [local instance] Types.instFunLike Types.instConcreteCategory

universe u

namespace Scheme

/-
Consider the following setup:
* F is `Type u`-valued a sheaf on `Sch` with respect to the Zariski topology
* X : ι → Sch is a family of schemes
* f : Π i, yoneda.obj (X i) ⟶ F is a family of relatively representable open immersions

Later, we will also assume:
* The family f is locally surjective with respect to the Zariski topology
-/
variable (F : Sheaf Scheme.zariskiTopology.{u} (Type u))
  {ι : Type u} {X : ι → Scheme.{u}}
  (f : (i : ι) → yoneda.obj (X i) ⟶ F.1) (hf : ∀ i, IsOpenImmersion.presheaf (f i))

namespace LocalRepresentability

variable {F f} (i j k : ι)

open Functor.relativelyRepresentable in
/-- We get a family of gluing data by taking `U i = X i` and `V i j = (hf i).rep.pullback (f j)`. -/
@[simps]
noncomputable def glueData : GlueData where
  J := ι
  U := X
  V := fun (i, j) ↦ (hf i).rep.pullback (f j)
  f i j := (hf i).rep.fst' (f j)
  f_mono i j :=
    have := (hf j).property _ _ _ ((hf i).1.isPullback' (f j)).flip
    IsOpenImmersion.mono _
  f_id i := IsOpenImmersion.isIso_fst'_self IsOpenImmersion.le_monomorphisms (hf i)
  t i j := (hf i).rep.symmetry (hf j).rep
  t_id i := by apply (hf i).rep.hom_ext' <;>
    simp [IsOpenImmersion.fst'_self_eq_snd IsOpenImmersion.le_monomorphisms (hf i)]
  t' i j k := lift₃ _ _ _ (pullback₃.p₂ _ _ _) (pullback₃.p₃ _ _ _) (pullback₃.p₁ _ _ _)
    (by simp) (by simp)
  t_fac i j k := (hf j).rep.hom_ext' (by simp) (by simp)
  cocycle i j k := pullback₃.hom_ext (by simp) (by simp) (by simp)
  f_open i j := (hf j).property _ _ _ ((hf i).1.isPullback' (f j)).flip

/-- The map from `X i` to the glued scheme `(glueData hf).glued` -/
noncomputable def toGlued (i : ι) : X i ⟶ (glueData hf).glued :=
  (glueData hf).ι i

instance : IsOpenImmersion (toGlued hf i) :=
  inferInstanceAs (IsOpenImmersion ((glueData hf).ι i))

/-- The map from the glued scheme `(glueData hf).glued`, treated as a sheaf, to `F`. -/
noncomputable def yonedaGluedToSheaf :
    zariskiTopology.yoneda.obj (glueData hf).glued ⟶ F where
  -- The map is obtained by finding an object of `F((glueData hf).glued)`.
  val := yonedaEquiv.symm
  -- This section is obtained from gluing the section corresponding to `f i : Hom(-, X i) ⟶ F`.
    ((glueData hf).sheafValGluedMk (fun i ↦ yonedaEquiv (f i)) (by
      intro i j
      apply yonedaEquiv.symm.injective
      dsimp only [glueData_V, glueData_J, glueData_U, glueData_f, glueData_t]
      rw [yonedaEquiv_naturality, Equiv.symm_apply_apply,
        FunctorToTypes.map_comp_apply, yonedaEquiv_naturality, yonedaEquiv_naturality,
        Equiv.symm_apply_apply, ← Functor.map_comp_assoc,
        Functor.relativelyRepresentable.symmetry_fst, ((hf i).rep.isPullback' (f j)).w]))

@[reassoc (attr := simp)]
lemma yoneda_toGlued_yonedaGluedToSheaf (i : ι) :
    yoneda.map (toGlued hf i) ≫ (yonedaGluedToSheaf hf).val = f i := by
  apply yonedaEquiv.injective
  rw [yonedaGluedToSheaf, yonedaEquiv_apply, yonedaEquiv_apply,
    FunctorToTypes.comp, yoneda_map_app, id_comp, yonedaEquiv_symm_app_apply]
  apply GlueData.sheafValGluedMk_val

@[simp]
lemma yonedaGluedToSheaf_app_toGlued {i : ι} :
    (yonedaGluedToSheaf hf).val.app _ (toGlued hf i) = yonedaEquiv (f i) := by
  rw [← yoneda_toGlued_yonedaGluedToSheaf hf i, yonedaEquiv_comp,
    yonedaEquiv_yoneda_map]

@[simp]
lemma yonedaGluedToSheaf_app_comp {V U : Scheme.{u}} (γ : V ⟶ U) (α : U ⟶ (glueData hf).glued) :
    (yonedaGluedToSheaf hf).val.app (op V) (γ ≫ α) =
      F.val.map γ.op ((yonedaGluedToSheaf hf).val.app (op U) α) :=
  congr_fun ((yonedaGluedToSheaf hf).val.naturality γ.op) α

instance [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)] :
    Sheaf.IsLocallySurjective (yonedaGluedToSheaf hf) :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (show Sigma.desc (fun i ↦ yoneda.map (toGlued hf i)) ≫
      (yonedaGluedToSheaf hf).val = Sigma.desc f by cat_disch)

lemma comp_toGlued_eq {U : Scheme} {i j : ι} (a : U ⟶ X i) (b : U ⟶ X j)
    (h : yoneda.map a ≫ f i = yoneda.map b ≫ f j) :
    a ≫ toGlued hf i = b ≫ toGlued hf j := by
  rw [← (hf i).rep.lift'_fst a b h, assoc]
  conv_rhs => rw [← (hf i).rep.lift'_snd a b h, assoc]
  congr 1
  exact ((glueData hf).glue_condition i j).symm.trans (by simp [toGlued])

@[simp]
lemma glueData_openCover_map : (glueData hf).openCover.f j = toGlued hf j := rfl

instance : Sheaf.IsLocallyInjective (yonedaGluedToSheaf hf) where
  equalizerSieve_mem := by
    rintro ⟨U⟩ (α β : U ⟶ _) h
    replace h : (yonedaGluedToSheaf hf).val.app _ α = (yonedaGluedToSheaf hf).val.app _ β := h
    have mem := (glueData hf).openCover.mem_grothendieckTopology
    refine GrothendieckTopology.superset_covering _ ?_
      (zariskiTopology.intersection_covering (zariskiTopology.pullback_stable α mem)
        (zariskiTopology.pullback_stable β mem))
    rintro V (γ : _ ⟶ U) ⟨⟨W₁, a, _, ⟨i⟩, fac₁⟩, ⟨W₂, b, _, ⟨j⟩, fac₂⟩⟩
    change γ ≫ α = γ ≫ β
    replace h : (yonedaGluedToSheaf hf).val.app _ (γ ≫ α) =
        (yonedaGluedToSheaf hf).val.app _ (γ ≫ β) := by simp [h]
    rw [← fac₁, ← fac₂] at h ⊢
    apply comp_toGlued_eq
    simpa [Scheme.GlueData.openCover_X, yonedaEquiv_naturality] using h

variable [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)]

instance : IsIso (yonedaGluedToSheaf hf) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (yonedaGluedToSheaf hf)]
  constructor <;> infer_instance

/-- The isomorphism between `yoneda.obj (glueData hf).glued` and `F`.

This implies that `F` is representable. -/
noncomputable def yonedaIsoSheaf :
    zariskiTopology.yoneda.obj (glueData hf).glued ≅ F :=
  asIso (yonedaGluedToSheaf hf)

/--
Suppose
* F is a `Type u`-valued sheaf on `Sch` with respect to the Zariski topology
* X : ι → Sch is a family of schemes
* f : Π i, yoneda.obj (X i) ⟶ F is a family of relatively representable open immersions
* f is jointly surjective

Then `F` is representable, and the representing object is glued from the `X i`s
-/
noncomputable
def representableBy : F.1.RepresentableBy (glueData hf).glued :=
  Functor.representableByEquiv.symm ((sheafToPresheaf _ _).mapIso (yonedaIsoSheaf hf))


include hf in
/--
Suppose
* F is a `Type u`-valued sheaf on `Sch` with respect to the Zariski topology
* X : ι → Sch is a family of schemes
* f : Π i, yoneda.obj (X i) ⟶ F is a family of relatively representable open immersions
* f is jointly surjective

Then `F` is representable.
-/
@[stacks 01JJ]
theorem isRepresentable : F.1.IsRepresentable :=
  ⟨_, ⟨representableBy hf⟩⟩

end LocalRepresentability

end Scheme

end AlgebraicGeometry
