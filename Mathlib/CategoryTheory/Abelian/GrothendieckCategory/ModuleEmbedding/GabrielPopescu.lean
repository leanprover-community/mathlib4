/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Connected
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Generator.Preadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.LiftToFinset
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
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
# The Gabriel-Popescu theorem

We prove the following Gabriel-Popescu theorem: if `C` is a Grothendieck abelian category and
`G` is a separator, then the functor `preadditiveCoyonedaObj G : C ⥤ ModuleCat (End G)ᵐᵒᵖ` sending
`X` to `Hom(G, X)` is fully faithful and has an exact left adjoint.

We closely follow the elementary proof given by Barry Mitchell.

## Future work

The left adjoint `tensorObj G` actually exists as soon as `C` is cocomplete and additive, so the
construction could be generalized.

The theorem as stated here implies that `C` is a Serre quotient of `ModuleCat (End G)ᵐᵒᵖ`.

## References

* [Barry Mitchell, *A quick proof of the Gabriel-Popesco theorem*][mitchell1981]
-/

@[expose] public section

universe v u

open CategoryTheory Limits Abelian

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

instance {G : C} : (preadditiveCoyonedaObj G).IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_isCoseparating.{v} (isCoseparator_coseparator _) _

/-- The left adjoint of the functor `Hom(G, ·)`, which can be thought of as `· ⊗ G`. -/
noncomputable def tensorObj (G : C) : ModuleCat (End G)ᵐᵒᵖ ⥤ C :=
  (preadditiveCoyonedaObj G).leftAdjoint

/-- The tensor-hom adjunction `(· ⊗ G) ⊣ Hom(G, ·)`. -/
noncomputable def tensorObjPreadditiveCoyonedaObjAdjunction (G : C) :
    tensorObj G ⊣ preadditiveCoyonedaObj G :=
  Adjunction.ofIsRightAdjoint _

instance {G : C} : (tensorObj G).IsLeftAdjoint :=
  (tensorObjPreadditiveCoyonedaObjAdjunction G).isLeftAdjoint

namespace GabrielPopescuAux

open CoproductsFromFiniteFiltered

/-- This is the map `⨁ₘ G ⟶ A` induced by `M ⟶ Hom(G, A)`. -/
noncomputable def d {G A : C} {M : ModuleCat (End G)ᵐᵒᵖ}
    (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)) : ∐ (fun (_ : M) => G) ⟶ A :=
  Sigma.desc fun (m : M) => g m

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem ι_d {G A : C} {M : ModuleCat (End G)ᵐᵒᵖ} (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)) (m : M) :
    Sigma.ι _ m ≫ d g = g.hom m := by
  simp [d]

attribute [local instance] IsFiltered.isConnected in
/-- This is the "Lemma" in [mitchell1981]. -/
theorem kernel_ι_d_comp_d {G : C} (hG : IsSeparator G) {A B : C} {M : ModuleCat (End G)ᵐᵒᵖ}
    (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)) (hg : Mono g)
    (f : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ B)) :
    kernel.ι (d g) ≫ d f = 0 := by
  refine (isColimitFiniteSubproductsCocone (fun (_ : M) => G)).pullback_zero_ext (fun F => ?_)
  dsimp only [liftToFinsetObj_obj, Discrete.functor_obj_eq_as, finiteSubcoproductsCocone_pt,
    Functor.const_obj_obj]
  classical
  rw [finiteSubcoproductsCocone_ι_app_eq_sum, ← pullback.condition_assoc]
  refine (Preadditive.isSeparator_iff G).1 hG _ (fun h => ?_)
  rw [Preadditive.comp_sum_assoc, Preadditive.comp_sum_assoc, Preadditive.sum_comp]
  simp only [Category.assoc, ι_d]
  let r (x : F) : (End G)ᵐᵒᵖ := MulOpposite.op (h ≫ pullback.fst _ _ ≫ Sigma.π _ x)
  suffices ∑ x ∈ F.attach, r x • f.hom x.1.as = 0 by simpa [End.smul_left, r] using this
  simp only [← map_smul, ← map_sum]
  suffices ∑ x ∈ F.attach, r x • x.1.as = 0 by simp [this]
  simp only [← g.hom.map_eq_zero_iff ((ModuleCat.mono_iff_injective _).1 hg), map_sum, map_smul]
  simp only [← ι_d g, End.smul_left, MulOpposite.unop_op, Category.assoc, r]
  simp [← Preadditive.comp_sum, ← Preadditive.sum_comp', pullback.condition_assoc]

theorem exists_d_comp_eq_d {G : C} (hG : IsSeparator G) {A} (B : C) [Injective B]
    {M : ModuleCat (End G)ᵐᵒᵖ} (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)) (hg : Mono g)
    (f : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ B)) : ∃ (l : A ⟶ B), d g ≫ l = d f := by
  let l₁ : image (d g) ⟶ B := epiDesc (factorThruImage (d g)) (d f) (by
    rw [← kernelFactorThruImage_hom_comp_ι, Category.assoc, kernel_ι_d_comp_d hG _ hg, comp_zero])
  let l₂ : A ⟶ B := Injective.factorThru l₁ (Limits.image.ι (d g))
  refine ⟨l₂, ?_⟩
  simp only [l₂, l₁]
  conv_lhs => congr; rw [← Limits.image.fac (d g)]
  simp [-Limits.image.fac]

end GabrielPopescuAux

open GabrielPopescuAux

set_option backward.isDefEq.respectTransparency false in
/-- Faithfulness follows because `G` is a separator, see
`isSeparator_iff_faithful_preadditiveCoyonedaObj`. -/
theorem GabrielPopescu.full (G : C) (hG : IsSeparator G) : (preadditiveCoyonedaObj G).Full where
  map_surjective {A B} f := by
    have := (isSeparator_iff_epi G).1 hG A
    have h := kernel_ι_d_comp_d hG (𝟙 _) inferInstance f
    simp only [ModuleCat.hom_id, LinearMap.id_coe, id_eq, d] at h
    refine ⟨epiDesc _ _ h, ?_⟩
    ext q
    simpa [-comp_epiDesc] using Sigma.ι _ q ≫= comp_epiDesc _ _ h

set_option backward.isDefEq.respectTransparency false in
theorem GabrielPopescu.preservesInjectiveObjects (G : C) (hG : IsSeparator G) :
    (preadditiveCoyonedaObj G).PreservesInjectiveObjects where
  injective_obj {B} hB := by
    rw [← Module.injective_iff_injective_object]
    simp only [preadditiveCoyonedaObj_obj_carrier]
    refine Module.Baer.injective (fun M g => ?_)
    have h := exists_d_comp_eq_d hG B (ModuleCat.ofHom
      ⟨⟨fun i => i.1.unop, by cat_disch⟩, by cat_disch⟩) ?_ (ModuleCat.ofHom g)
    · obtain ⟨l, hl⟩ := h
      refine ⟨((preadditiveCoyonedaObj G).map l).hom ∘ₗ
        (Preadditive.homSelfLinearEquivEndMulOpposite G).symm.toLinearMap, ?_⟩
      intro f hf
      simpa [d] using Sigma.ι _ ⟨f, hf⟩ ≫= hl
    · rw [ModuleCat.mono_iff_injective]
      cat_disch

/-- `tensorObj G` is left exact: it is additive and preserves monomorphisms and cokernels,
so it preserves homology and therefore finite limits. -/
theorem GabrielPopescu.preservesFiniteLimits (G : C) (hG : IsSeparator G) :
    PreservesFiniteLimits (tensorObj G) := by
  have := preservesInjectiveObjects G hG
  have : (tensorObj G).PreservesMonomorphisms :=
    (tensorObj G).preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects
      (tensorObjPreadditiveCoyonedaObjAdjunction G)
  have : PreservesBinaryBiproducts (tensorObj G) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (tensorObj G).Additive := Functor.additive_of_preservesBinaryBiproducts _
  have : (tensorObj G).PreservesHomology :=
    (tensorObj G).preservesHomology_of_preservesMonos_and_cokernels
  exact (tensorObj G).preservesFiniteLimits_of_preservesHomology

end CategoryTheory.IsGrothendieckAbelian
