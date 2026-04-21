/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# `sigmaConst.obj` preserves colimits

Given an object `R` in a category `C` with coproducts of size `w`,
the functor `sigmaConst.obj R : Type w ⥤ C` which sends
a type `T` to the coproduct of copies of `R` indexed by `T`
preserves all colimits.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe w v' v u' u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

set_option backward.isDefEq.respectTransparency false in
/- If the morphisms in `C` were in `Type w`, the functor
`sigmaConst.{w}`
would be a left adjoint (see `sigmaConstAdj`). In general, we cannot
expect this functor to be a left adjoint, but the commutation
with colimits always holds. -/
instance [HasCoproducts.{w} C] (R : C) :
    PreservesColimitsOfSize.{v', u'} (sigmaConst.{w}.obj R) where
  preservesColimitsOfShape {J _} := ⟨fun {K} ↦ ⟨fun {c} hc ↦ ⟨by
    replace hc := (Types.isColimit_iff_coconeTypesIsColimit ..).1 ⟨hc⟩
    let coconeTypes (s : Cocone (K ⋙ sigmaConst.obj R)) : K.CoconeTypes :=
      { pt := R ⟶ s.pt
        ι j k := Sigma.ι (fun _ ↦ R) k ≫ s.ι.app j
        ι_naturality g := by ext; simp [← s.w g] }
    exact {
      desc s := Sigma.desc (hc.desc (coconeTypes s))
      fac s j := by
        dsimp
        ext k
        simp [dsimp% hc.fac_apply, dsimp% Sigma.ι_desc (hc.desc (coconeTypes s)), coconeTypes]
      uniq s m hm := by
        dsimp
        ext x
        obtain ⟨j, k, rfl⟩ := Functor.CoconeTypes.IsColimit.ι_jointly_surjective hc x
        simp [coconeTypes, ← hm, dsimp% hc.fac_apply,
          dsimp% Sigma.ι_desc (hc.desc (coconeTypes s))] }⟩⟩⟩

variable [HasZeroMorphisms C] (R : C)

section

variable {α β : Type*} (f : α → β)
  [HasCoproduct (fun (_ : α) ↦ R)] [HasCoproduct (fun (_ : β) ↦ R)]
  [HasCoproduct (fun (_ : ((Set.range f)ᶜ : Set _)) ↦ R)]

open Classical in
/-- A colimit cokernel cofork for the map
`∐ fun (_ : α) ↦ R ⟶ ∐ fun (_ : β) ↦ R` induced by a map `f : α → β`. -/
@[simps! pt]
noncomputable def sigmaConstCokernelCofork :
    CokernelCofork
      (Sigma.map' (f := fun (_ : α) ↦ R) (g := fun (_ : β) ↦ R) f (fun _ ↦ 𝟙 R)) :=
  CokernelCofork.ofπ (Z := ∐ fun (_ : ((Set.range f)ᶜ : Set _)) ↦ R)
    (Sigma.desc (fun b ↦
      if hb : b ∈ (Set.range f)ᶜ then Sigma.ι (fun _ ↦ R) ⟨b, hb⟩ else 0))
    (by ext; simp [Sigma.ι_desc])

@[reassoc]
lemma ι_sigmaConstCokernelCofork_π (b : β) (hb : b ∉ Set.range f) :
    dsimp% Sigma.ι (fun _ ↦ R) b ≫ (sigmaConstCokernelCofork R f).π =
      Sigma.ι (fun _ ↦ R) ⟨b, hb⟩ := by
  dsimp [sigmaConstCokernelCofork]
  rw [Sigma.ι_desc]
  apply dif_pos

@[reassoc (attr := simp)]
lemma ι_sigmaConstCokernelCofork_π_eq_zero (a : α) :
    dsimp% Sigma.ι (fun _ ↦ R) (f a) ≫ (sigmaConstCokernelCofork R f).π = 0 := by
  dsimp [sigmaConstCokernelCofork]
  rw [Sigma.ι_desc]
  exact dif_neg (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The cokernel of the map `∐ fun (_ : α) ↦ R ⟶ ∐ fun (_ : β) ↦ R` induced
by a map `f : α → β` identifies to the coproduct of copies of `R`
indexed by the complement of the range of `f`. -/
noncomputable def isColimitSigmaConstCokernelCofork :
    IsColimit (sigmaConstCokernelCofork R f) :=
  Cofork.IsColimit.mk _
    (fun s ↦ Sigma.desc (fun ⟨b, _⟩ ↦ Sigma.ι (fun _ ↦ R) b ≫ s.π))
    (fun s ↦ by
      ext b
      by_cases hb : b ∈ Set.range f
      · obtain ⟨a, rfl⟩ := hb
        simpa [-CokernelCofork.condition] using Sigma.ι (fun _ ↦ R) a ≫= s.condition.symm
      · simp [ι_sigmaConstCokernelCofork_π_assoc _ _ _ hb])
    (fun s m hm ↦ by
      dsimp
      ext ⟨b, hb⟩
      rw [Sigma.ι_desc, ← hm, ι_sigmaConstCokernelCofork_π_assoc])

instance :
    HasCokernel (Sigma.map' (f := fun (_ : α) ↦ R) (g := fun (_ : β) ↦ R) f (fun _ ↦ 𝟙 R)) :=
  ⟨_, isColimitSigmaConstCokernelCofork R f⟩

end

instance [HasCoproducts.{w} C] {α β : Type w} (f : α ⟶ β) :
    HasCokernel ((sigmaConst.obj R).map f) := by
  dsimp; infer_instance

end CategoryTheory.Limits
