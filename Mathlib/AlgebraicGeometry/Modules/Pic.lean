/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Invertible
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFreeOfInvertible
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.AlgebraicGeometry.Modules.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import Mathlib.Geometry.RingedSpace.IsLocallyRinged

/-!
# Tensor-invertible sheaves of modules on a scheme

A sheaf of modules with a tensor inverse is locally free of rank one.
The group of tensor-invertible isomorphism classes of modules is small: every line bundle
embeds into a fixed product of pushforwards of the structure sheaf, whose subobjects form
a small type.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A tensor-invertible sheaf of modules on a scheme is locally free of rank one. -/
lemma tensor_inverse_isLocallyFreeOfRank_one {F G : X.Modules} (η : F ⊗ G ≅ (𝟙_ X.Modules)) :
    F.IsLocallyFreeOfRank 1 :=
  SheafOfModulesOfCommRing.isLocallyFreeOfRank_one_of_tensor_iso (R := X.sheaf) η

open Limits in
set_option backward.isDefEq.respectTransparency false in
/-- Every line bundle embeds into the product of the pushforwards of the structure sheaves
of all open subsets. -/
private lemma exists_mono_target (X : Scheme.{u}) :
    ∃ B : X.Modules, ∀ F : X.Modules, F.IsLocallyFreeOfRank 1 → ∃ f : F ⟶ B, Mono f := by
  classical
  let P (U : X.Opens) : X.Modules :=
    (SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := X.ringCatSheaf) U)).obj
      (SheafOfModules.unit (X.ringCatSheaf.over U))
  refine ⟨∏ᶜ P, ?_⟩
  intro F hF
  let t (U : X.Opens) : F.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U) :=
    if h : Nonempty (F.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) then
      h.some.hom else 0
  let s (U : X.Opens) : F ⟶ P U :=
    (SheafOfModules.overPushforwardOverAdj U).homEquiv _ _ (t U)
  refine ⟨Pi.lift s, ⟨?_⟩⟩
  intro T a b hab
  obtain ⟨q, hq⟩ := SheafOfModules.IsLocallyFreeOfRank.exists_isLocallyFreeDataOfRank
    (M := F) (n := 1)
  have hi (i : q.I) : a.over (q.X i) = b.over (q.X i) := by
    have h : Nonempty (F.over (q.X i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (q.X i))) :=
      ⟨q.isoUnit i⟩
    have : IsIso (t (q.X i)) := by dsimp [t]; rw [dite_eq_left h]; infer_instance
    apply (cancel_mono (t (q.X i))).mp
    apply ((SheafOfModules.overPushforwardOverAdj (q.X i)).homEquiv _ _).injective
    simpa only [SheafOfModules.Hom.over, SheafOfModules.overFunctor,
      Adjunction.homEquiv_naturality_left, Category.assoc, Pi.lift_comp_π, s] using
      congrArg (fun f ↦ f ≫ Pi.π P (q.X i)) hab
  apply (SheafOfModules.toSheaf X.ringCatSheaf).map_injective
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply F.isSheaf.hom_ext (q.coversTop.cover V.unop)
  rintro ⟨W, f, i, ⟨g⟩⟩
  have h : a.val.app (.op W) = b.val.app (.op W) :=
    congrArg (fun k ↦ k.val.app (.op (Over.mk g))) (hi i)
  ext x
  change F.val.map f.op (a.val.app V x) = F.val.map f.op (b.val.app V x)
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply, h]

/-- The tensor-invertible isomorphism classes of modules on a scheme form a small type. -/
instance small_pic : Small.{u} (Skeleton X.Modules)ˣ := by
  classical
  obtain ⟨B, hB⟩ := exists_mono_target X
  have hp (p : (Skeleton X.Modules)ˣ) : p.val.out.IsLocallyFreeOfRank 1 :=
    tensor_inverse_isLocallyFreeOfRank_one (Quotient.eq.mp p.val_inv).some
  choose f hf using fun p : (Skeleton X.Modules)ˣ ↦ hB p.val.out (hp p)
  have (p : (Skeleton X.Modules)ˣ) : Mono (f p) := hf p
  refine small_of_injective (f := fun p ↦ Subobject.mk (f p)) ?_
  intro p q h
  exact Units.ext (Quotient.out_equiv_out.mp ⟨Subobject.isoOfMkEqMk (f p) (f q) h⟩)

def Pic (X : Scheme.{u}) : Type u := Shrink.{u} (Skeleton X.Modules)ˣ

noncomputable instance : CommGroup <| Pic X :=
  inferInstanceAs <| CommGroup <| Shrink.{u} (Skeleton X.Modules)ˣ

instance (F : X.Modules) [F.IsLocallyFreeOfRank 1] : IsIso ((ihom.ev F).app (𝟙_ X.Modules)) :=
  SheafOfModulesOfCommRing.isIso_ihom_ev_app_of_isLocallyFreeOfRank_one F (𝟙_ X.Modules)

/-- The class of a line bundle in the Picard group. -/
noncomputable def Scheme.Modules.toPic (F : X.Modules) [F.IsLocallyFreeOfRank 1] : Pic X := by
  refine Shrink.mulEquiv.symm <| Units.mkOfMulEqOne
    (toSkeleton F) (toSkeleton (F ⟶[_] (𝟙_ _))) ?_
  rw [← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq]
  exact congr_toSkeleton_of_iso (asIso ((ihom.ev F).app (𝟙_ _)))

noncomputable def Pic.asModule (L : Pic X) : X.Modules :=
  (fromSkeleton X.Modules).obj <| Units.val <| Shrink.mulEquiv L

end AlgebraicGeometry
