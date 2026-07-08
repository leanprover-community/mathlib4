/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.Points

/-!
# The skyscraper sheaf of modules at a point of a topos

Given a point `Φ` of a site `(C, J)` and a sheaf of rings `R`, and `M` a module over the fiber of
`R` at `P`, we construct the sheaf of modules  structure on the skyscraper sheaf
(`Φ.skyscraperSheaf M`) over `R`.
-/

@[expose] public section

open Opposite CategoryTheory Limits
section topos

namespace CategoryTheory.GrothendieckTopology.Point

universe w v u

open Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
section Presheaf

set_option backward.isDefEq.respectTransparency false

variable (R : Cᵒᵖ ⥤ RingCat.{w}) (M : ModuleCat.{w} ↑(Φ.presheafFiber.obj R))

/--
The action of a section `r : R.obj X` on the component at `x : Φ.fiber.obj X.unop` of the
skyscraper presheaf: the action of the germ of `r` at `x` on `M`.
-/
noncomputable def skyscraperSMulComponent (X : Cᵒᵖ) (r : ↑(R.obj X)) (x : Φ.fiber.obj X.unop) :
    AddCommGrpCat.of (↑M : Type w) ⟶ AddCommGrpCat.of (↑M : Type w) :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun m => (Φ.toPresheafFiber X.unop x R).hom r • m)
      (fun m n => smul_add _ m n))

@[simp]
lemma skyscraperSMulComponent_apply (X : Cᵒᵖ) (r : ↑(R.obj X)) (x : Φ.fiber.obj X.unop)
    (m : AddCommGrpCat.of (↑M : Type w)) :
    (skyscraperSMulComponent Φ R M X r x).hom m =
      (Φ.toPresheafFiber X.unop x R).hom r • m := by
  simp [skyscraperSMulComponent]

lemma skyscraperSMulComponent_one (X : Cᵒᵖ) (x : Φ.fiber.obj X.unop) :
    skyscraperSMulComponent Φ R M X (1 : ↑(R.obj X)) x = 𝟙 _ := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m => ?_)
  rw [skyscraperSMulComponent_apply]
  simp [map_one, one_smul]

lemma skyscraperSMulComponent_mul (X : Cᵒᵖ) (r s : ↑(R.obj X)) (x : Φ.fiber.obj X.unop) :
    skyscraperSMulComponent Φ R M X (r * s) x =
      skyscraperSMulComponent Φ R M X s x ≫ skyscraperSMulComponent Φ R M X r x := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m => ?_)
  rw [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, skyscraperSMulComponent_apply,
    skyscraperSMulComponent_apply, skyscraperSMulComponent_apply, map_mul, mul_smul]

lemma skyscraperSMulComponent_add (X : Cᵒᵖ) (r s : ↑(R.obj X)) (x : Φ.fiber.obj X.unop) :
    skyscraperSMulComponent Φ R M X (r + s) x =
      skyscraperSMulComponent Φ R M X r x + skyscraperSMulComponent Φ R M X s x := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m => ?_)
  rw [skyscraperSMulComponent_apply, AddCommGrpCat.hom_add, AddMonoidHom.add_apply,
    skyscraperSMulComponent_apply, skyscraperSMulComponent_apply, map_add, add_smul]

lemma skyscraperSMulComponent_zero (X : Cᵒᵖ) (x : Φ.fiber.obj X.unop) :
    skyscraperSMulComponent Φ R M X (0 : ↑(R.obj X)) x = 0 := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m => ?_)
  rw [skyscraperSMulComponent_apply, map_zero, zero_smul, AddCommGrpCat.hom_zero,
    AddMonoidHom.zero_apply]

lemma skyscraperSMulComponent_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : ↑(R.obj X))
    (y : Φ.fiber.obj Y.unop) :
    skyscraperSMulComponent Φ R M X r (Φ.fiber.map f.unop y) =
      skyscraperSMulComponent Φ R M Y ((R.map f).hom r) y := by
  have h0 := congrArg RingCat.Hom.hom (toPresheafFiber_w Φ f.unop y R)
  rw [RingCat.hom_comp] at h0
  have h : (Φ.toPresheafFiber X.unop (Φ.fiber.map f.unop y) R).hom r =
      (Φ.toPresheafFiber Y.unop y R).hom ((R.map f).hom r) :=
    (DFunLike.congr_fun h0 r).symm
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m => ?_)
  rw [skyscraperSMulComponent_apply, skyscraperSMulComponent_apply, h]

noncomputable def skyscraperSMul (X : Cᵒᵖ) (r : ↑(R.obj X)) :
    (Φ.skyscraperPresheaf (AddCommGrpCat.of (↑M : Type w))).obj X ⟶
      (Φ.skyscraperPresheaf (AddCommGrpCat.of (↑M : Type w))).obj X :=
  Limits.Pi.map fun x => skyscraperSMulComponent Φ R M X r x

@[reassoc (attr := simp)]
lemma skyscraperSMul_π (X : Cᵒᵖ) (r : ↑(R.obj X)) (x : Φ.fiber.obj X.unop) :
    skyscraperSMul Φ R M X r ≫ Limits.Pi.π _ x =
      Limits.Pi.π _ x ≫ skyscraperSMulComponent Φ R M X r x :=
  Limits.Pi.map_π _ x

lemma skyscraperSMul_one (X : Cᵒᵖ) :
    skyscraperSMul Φ R M X (1 : ↑(R.obj X)) = 𝟙 _ := by
  dsimp only [skyscraperSMul]
  simp only [skyscraperSMulComponent_one]
  exact Limits.Pi.map_id

lemma skyscraperSMul_mul (X : Cᵒᵖ) (r s : ↑(R.obj X)) :
    skyscraperSMul Φ R M X (r * s) =
      skyscraperSMul Φ R M X s ≫ skyscraperSMul Φ R M X r := by
  dsimp only [skyscraperSMul]
  rw [Limits.Pi.map_comp_map]
  simp only [skyscraperSMulComponent_mul]

lemma skyscraperSMul_add (X : Cᵒᵖ) (r s : ↑(R.obj X)) :
    skyscraperSMul Φ R M X (r + s) =
      skyscraperSMul Φ R M X r + skyscraperSMul Φ R M X s := by
  refine Limits.Pi.hom_ext _ _ fun x => ?_
  simp only [skyscraperSMul, Limits.Pi.map_π, skyscraperSMulComponent_add,
    Preadditive.add_comp, Preadditive.comp_add]

lemma skyscraperSMul_zero (X : Cᵒᵖ) :
    skyscraperSMul Φ R M X (0 : ↑(R.obj X)) = 0 := by
  refine Limits.Pi.hom_ext _ _ fun x => ?_
  simp only [skyscraperSMul, Limits.Pi.map_π, skyscraperSMulComponent_zero,
    Limits.comp_zero, Limits.zero_comp]

noncomputable instance skyscraperPresheafObjSMul (X : Cᵒᵖ) :
    SMul ↑(R.obj X)
      ↑((Φ.skyscraperPresheaf (AddCommGrpCat.of (↑M : Type w))).obj X) where
  smul r m := (skyscraperSMul Φ R M X r).hom m

lemma skyscraperPresheafObjSMul_def (X : Cᵒᵖ) (r : R.obj X)
      (m : (Φ.skyscraperPresheaf (AddCommGrpCat.of (↑M : Type w))).obj X) :
      r • m = (skyscraperSMul Φ R M X r).hom m := rfl

/--
The module structure on the value at `X` of the skyscraper presheaf associated to a module `M`
over the fiber of `R`: sections act componentwise through their germs. Note that this requires
no case distinction on whether the fiber at `X` is empty (where the empty product is zero).
-/
noncomputable instance skyscraperPresheafObjModule (X : Cᵒᵖ) :
    Module ↑(R.obj X)
      ↑((Φ.skyscraperPresheaf (AddCommGrpCat.of (↑M : Type w))).obj X) where
  one_smul m := by
    rw [skyscraperPresheafObjSMul_def, skyscraperSMul_one, AddCommGrpCat.hom_id,
      AddMonoidHom.id_apply]
  mul_smul r s m := by
    rw [skyscraperPresheafObjSMul_def, skyscraperPresheafObjSMul_def,
      skyscraperPresheafObjSMul_def, skyscraperSMul_mul, AddCommGrpCat.hom_comp,
      AddMonoidHom.comp_apply]
  smul_zero r := map_zero (skyscraperSMul Φ R M X r).hom
  smul_add r m n := map_add (skyscraperSMul Φ R M X r).hom m n
  add_smul r s m := by
    rw [skyscraperPresheafObjSMul_def, skyscraperPresheafObjSMul_def,
      skyscraperPresheafObjSMul_def, skyscraperSMul_add, AddCommGrpCat.hom_add,
      AddMonoidHom.add_apply]
  zero_smul m := by
    rw [skyscraperPresheafObjSMul_def, skyscraperSMul_zero, AddCommGrpCat.hom_zero,
      AddMonoidHom.zero_apply]

/-- The defining property of the scalar action on the values of the skyscraper presheaf,
componentwise: on the component at `x`, a section acts through its germ at `x`. This is the
form in which the action is consumed downstream. -/
lemma π_smul (X : Cᵒᵖ) (r : ↑(R.obj X)) (x : Φ.fiber.obj X.unop)
    (m : ↑((Φ.skyscraperPresheaf (AddCommGrpCat.of (↑M : Type w))).obj X)) :
    (Limits.Pi.π (fun _ => AddCommGrpCat.of (↑M : Type w)) x).hom (r • m) =
      (Φ.toPresheafFiber X.unop x R).hom r •
        (Limits.Pi.π (fun _ => AddCommGrpCat.of (↑M : Type w)) x).hom m := by
  rw [skyscraperPresheafObjSMul_def]
  exact (ConcreteCategory.congr_hom (skyscraperSMul_π Φ R M X r x) m).trans
    (skyscraperSMulComponent_apply Φ R M X r x _)

/-- The scalar action on the skyscraper presheaf is semilinear with respect to restriction. -/
lemma skyscraperSMul_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : ↑(R.obj X)) :
    skyscraperSMul Φ R M X r ≫
        (Φ.skyscraperPresheaf (AddCommGrpCat.of (↑M : Type w))).map f =
      (Φ.skyscraperPresheaf (AddCommGrpCat.of (↑M : Type w))).map f ≫
        skyscraperSMul Φ R M Y ((R.map f).hom r) := by
  rw [skyscraperPresheafFunctor_obj_map]
  dsimp only [skyscraperSMul]
  rw [Limits.Pi.map_comp_map', Limits.Pi.map'_comp_map]
  simp only [Category.comp_id, Category.id_comp, skyscraperSMulComponent_naturality]

/--
The skyscraper presheaf of modules at a point `Φ` of a site, valued in a module `M` over the
fiber of the presheaf of rings `R`: the underlying abelian presheaf is the skyscraper presheaf
`Φ.skyscraperPresheaf M`, and sections of `R` act componentwise through their germs.
-/
noncomputable def skyscraperPresheafOfModules : PresheafOfModules.{w} R :=
  PresheafOfModules.ofPresheaf
    (Φ.skyscraperPresheaf (AddCommGrpCat.of (↑M : Type w)))
    (fun _ _ f r m => CategoryTheory.congr_fun (skyscraperSMul_naturality Φ R M f r) m)

@[simp]
lemma skyscraperPresheafOfModules_presheaf :
    (skyscraperPresheafOfModules Φ R M).presheaf =
      Φ.skyscraperPresheaf (AddCommGrpCat.of (↑M : Type w)) := rfl

variable {M} in
lemma skyscraperSMulComponent_comm {N : ModuleCat.{w} ↑(Φ.presheafFiber.obj R)} (φ : M ⟶ N)
    (X : Cᵒᵖ) (r : ↑(R.obj X)) (x : Φ.fiber.obj X.unop) :
    skyscraperSMulComponent Φ R M X r x ≫
        (forget₂ (ModuleCat.{w} ↑(Φ.presheafFiber.obj R)) AddCommGrpCat).map φ =
      (forget₂ (ModuleCat.{w} ↑(Φ.presheafFiber.obj R)) AddCommGrpCat).map φ ≫
        skyscraperSMulComponent Φ R N X r x := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m => ?_)
  exact ((congrArg φ.hom (skyscraperSMulComponent_apply Φ R M X r x m)).trans
    (map_smul φ.hom _ m)).trans (skyscraperSMulComponent_apply Φ R N X r x _).symm

variable {M} in
/-- Morphisms of modules over the fiber induce componentwise `R`-linear morphisms of
skyscraper presheaves. -/
lemma skyscraperSMul_naturality₂ {N : ModuleCat.{w} ↑(Φ.presheafFiber.obj R)} (φ : M ⟶ N)
    (X : Cᵒᵖ) (r : ↑(R.obj X)) :
    skyscraperSMul Φ R M X r ≫
        (Φ.skyscraperPresheafFunctor.map
          ((forget₂ (ModuleCat.{w} ↑(Φ.presheafFiber.obj R)) AddCommGrpCat).map φ)).app X =
      (Φ.skyscraperPresheafFunctor.map
          ((forget₂ (ModuleCat.{w} ↑(Φ.presheafFiber.obj R)) AddCommGrpCat).map φ)).app X ≫
        skyscraperSMul Φ R N X r := by
  dsimp only [skyscraperSMul]
  rw [skyscraperPresheafFunctor_map_app, Limits.Pi.map_comp_map, Limits.Pi.map_comp_map]
  exact congrArg _ (funext fun a => skyscraperSMulComponent_comm Φ R φ X r a)

/-- The underlying morphism of abelian presheaves of `PresheafOfModules.homMk φ hφ` is `φ`. -/
@[simp]
lemma _root_.PresheafOfModules.toPresheaf_map_homMk {M₁ M₂ : PresheafOfModules.{w} R}
    (φ : M₁.presheaf ⟶ M₂.presheaf)
    (hφ : ∀ (X : Cᵒᵖ) (r : R.obj X) (m : M₁.obj X), φ.app X (r • m) = r • φ.app X m) :
    (PresheafOfModules.toPresheaf R).map (PresheafOfModules.homMk φ hφ) = φ := rfl

/--
The skyscraper presheaf-of-modules functor at a point `Φ` of a site: it sends a module over
the fiber of `R` to the associated skyscraper presheaf of modules.
-/
noncomputable def skyscraperPresheafOfModulesFunctor :
    ModuleCat.{w} ↑(Φ.presheafFiber.obj R) ⥤ PresheafOfModules.{w} R where
  obj M := skyscraperPresheafOfModules Φ R M
  map {M N} φ := PresheafOfModules.homMk
    (Φ.skyscraperPresheafFunctor.map
      ((forget₂ (ModuleCat.{w} ↑(Φ.presheafFiber.obj R)) AddCommGrpCat).map φ))
    (fun X r m => CategoryTheory.congr_fun (skyscraperSMul_naturality₂ Φ R φ X r) m)
  map_id M := by
    apply (PresheafOfModules.toPresheaf R).map_injective
    simp only [PresheafOfModules.toPresheaf_map_homMk, Functor.map_id]
    exact Φ.skyscraperPresheafFunctor.map_id _
  map_comp {M N P} φ ψ := by
    apply (PresheafOfModules.toPresheaf R).map_injective
    simp only [PresheafOfModules.toPresheaf_map_homMk, Functor.map_comp]

end Presheaf

section Sheaf

variable (R : Sheaf J RingCat.{w})

/--
The skyscraper sheaf-of-modules functor at a point `Φ` of a site: it sends a module over the
fiber of the sheaf of rings `R` to the associated skyscraper sheaf of modules. The underlying
abelian sheaf is the skyscraper sheaf `Φ.skyscraperSheaf`
(see `skyscraperSheafOfModules_eq_skyscraperSheaf`).
-/
noncomputable def skyscraperSheafOfModulesFunctor :
    ModuleCat.{w} ((Point.sheafFiber Φ).obj R).carrier ⥤ SheafOfModules.{w} R where
  obj M := ⟨(skyscraperPresheafOfModulesFunctor Φ R.obj).obj M,
    Φ.isSheaf_skyscraperPresheaf _⟩
  map φ := ⟨(skyscraperPresheafOfModulesFunctor Φ R.obj).map φ⟩
  map_id M := by
    ext1
    exact (skyscraperPresheafOfModulesFunctor Φ R.obj).map_id M
  map_comp φ ψ := by
    ext1
    exact (skyscraperPresheafOfModulesFunctor Φ R.obj).map_comp φ ψ

/--
The underlying sheaf of abelian groups of the skyscraper sheaf of modules is the
skyscraper sheaf.
-/
lemma skyscraperSheafOfModules_eq_skyscraperSheaf :
    (skyscraperSheafOfModulesFunctor Φ R) ⋙ SheafOfModules.toSheaf R =
    forget₂ (ModuleCat ((Point.sheafFiber Φ).obj R).carrier) Ab ⋙
    Φ.skyscraperSheafFunctor := rfl

end Sheaf

end CategoryTheory.GrothendieckTopology.Point
end topos

section TopCatPoint

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.GrothendieckTopology

universe u

variable {Y : TopCat.{u}} (p : ↑Y)

instance skyscraperSheaf_isFlasque (A : Ab.{u}) :
    TopCat.Presheaf.IsFlasque
      ((Opens.pointGrothendieckTopology p).skyscraperSheaf A).obj where
  epi {U V} i := by
    by_cases hp : p ∈ V.unop
    · have hsec : Limits.Pi.map' (fun _ => (⟨⟨hp⟩⟩ :
            (Opens.pointGrothendieckTopology p).fiber.obj V.unop)) (fun _ => 𝟙 A) ≫
          ((Opens.pointGrothendieckTopology p).skyscraperPresheaf A).map i = 𝟙 _ := by
        rw [Point.skyscraperPresheafFunctor_obj_map, Limits.Pi.map'_comp_map']
        refine (Limits.Pi.map'_eq (funext fun x =>
          Subsingleton.elim (α := (Opens.pointGrothendieckTopology p).fiber.obj V.unop) _ _)
          ?_).trans Limits.Pi.map'_id_id
        intro b
        simp
      exact CategoryTheory.SplitEpi.epi ⟨_, hsec⟩
    · have hterm : Limits.IsTerminal
          (((Opens.pointGrothendieckTopology p).skyscraperPresheaf A).obj V) :=
        Limits.IsTerminal.ofUniqueHom
          (fun Z => Limits.Pi.lift (fun x => absurd x.down.down hp))
          (fun Z m => Limits.Pi.hom_ext _ _ (fun x => absurd x.down.down hp))
      have hzero : Limits.IsZero
          ((((Opens.pointGrothendieckTopology p).skyscraperSheaf A).obj).obj V) := by
        rw [Point.skyscraperSheafFunctor_obj_obj]
        exact (Limits.isZero_zero _).of_iso (hterm.uniqueUpToIso (Limits.isZero_zero _).isTerminal)
      constructor
      intro Z g h _
      exact hzero.eq_of_src g h

variable (R : TopCat.Sheaf RingCat.{u} Y)

noncomputable def pointPresheafFiberToStalk :
    (Opens.pointGrothendieckTopology p).presheafFiber.obj R.presheaf ⟶ R.presheaf.stalk p :=
  (Opens.pointGrothendieckTopology p).presheafFiberDesc
    (fun U x => R.presheaf.germ U p x.down.down)
    (by intro U V f x; exact R.presheaf.germ_res f p x.down.down)

@[reassoc (attr := simp)]
lemma toPresheafFiber_pointPresheafFiberToStalk (U : TopologicalSpace.Opens ↑Y) (hp : p ∈ U) :
    (Opens.pointGrothendieckTopology p).toPresheafFiber U ⟨⟨hp⟩⟩ R.presheaf ≫
      pointPresheafFiberToStalk p R = R.presheaf.germ U p hp :=
  (Opens.pointGrothendieckTopology p).toPresheafFiber_presheafFiberDesc _ _ U ⟨⟨hp⟩⟩

variable (M : Type u) [AddCommGroup M] [Module ↑(R.presheaf.stalk p) M]

noncomputable instance pointSheafFiberModule :
    Module ↑((Opens.pointGrothendieckTopology p).sheafFiber.obj R) M :=
  Module.compHom M (pointPresheafFiberToStalk p R).hom

noncomputable def skyscraperSheafOfModules : SheafOfModules.{u} R :=
  ((Opens.pointGrothendieckTopology p).skyscraperSheafOfModulesFunctor R).obj
    (ModuleCat.of _ M)

lemma toSheaf_obj_skyscraperSheafOfModules :
    (SheafOfModules.toSheaf _).obj (skyscraperSheafOfModules p R M) =
      (Opens.pointGrothendieckTopology p).skyscraperSheaf (AddCommGrpCat.of M) := rfl

instance : TopCat.Sheaf.IsFlasque
    ((SheafOfModules.toSheaf _).obj (skyscraperSheafOfModules p R M)) :=
  inferInstanceAs (TopCat.Presheaf.IsFlasque
    ((Opens.pointGrothendieckTopology p).skyscraperSheaf (AddCommGrpCat.of M)).obj)

end TopCatPoint
