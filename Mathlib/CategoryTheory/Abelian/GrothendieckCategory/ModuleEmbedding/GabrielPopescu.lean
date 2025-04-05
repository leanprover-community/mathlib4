/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Connected
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Preadditive.LiftToFinset
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-!
# The Gabriel-Popescu theorem

We prove the following Gabriel-Popescu theorem: if `C` is a Grothendieck abelian category and
`G` is a separator, then the functor `preadditiveCoyonedaObj G : C ⥤ ModuleCat (End G)ᵐᵒᵖ` sending
`X` to `Hom(G, X)` is fully faithful and has an exact left adjoint.

We closely follow the elementary proof given by Barry Mitchell.

The Gabriel-Popescu theorem can also be stated by saying that if `C` is a Grothendieck
abelian category, then `C` identifies to a localization of a category of modules
with respect a Serre class: we introduce a structure `GabrielPopescuPackage C`
which contains the necessary data and properties and show that `GabrielPopescuPackage C`
is nonempty.

## Future work

The left adjoint `tensorObj G` actually exists as soon as `C` is cocomplete and additive, so the
construction could be generalized.

## References

* [Barry Mitchell, *A quick proof of the Gabriel-Popesco theorem*][mitchell1981]
-/

universe w v v' u u'

open CategoryTheory Limits Abelian

namespace CategoryTheory.IsGrothendieckAbelian

section

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

instance {G : C} : (preadditiveCoyonedaObj G).IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_isCoseparating (isCoseparator_coseparator _) _

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
  simp only [← LinearMap.map_smul, ← map_sum]
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

theorem GabrielPopescu.preservesInjectiveObjects (G : C) (hG : IsSeparator G) :
    (preadditiveCoyonedaObj G).PreservesInjectiveObjects where
  injective_obj {B} hB := by
    rw [← Module.injective_iff_injective_object]
    simp only [preadditiveCoyonedaObj_obj_carrier, preadditiveCoyonedaObj_obj_isAddCommGroup,
      preadditiveCoyonedaObj_obj_isModule]
    refine Module.Baer.injective (fun M g => ?_)
    have h := exists_d_comp_eq_d hG B (ModuleCat.ofHom
      ⟨⟨fun i => i.1.unop, by aesop_cat⟩, by aesop_cat⟩) ?_ (ModuleCat.ofHom g)
    · obtain ⟨l, hl⟩ := h
      refine ⟨((preadditiveCoyonedaObj G).map l).hom ∘ₗ
        (Preadditive.homSelfLinearEquivEndMulOpposite G).symm.toLinearMap, ?_⟩
      intro f hf
      simpa [d] using Sigma.ι _ ⟨f, hf⟩ ≫= hl
    · rw [ModuleCat.mono_iff_injective]
      aesop_cat

/-- Right exactness follows because `tensorObj G` is a left adjoint. -/
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

lemma GabrielPopescu.tensorObj_isLocalization (G : C) (hG : IsSeparator G) :
    letI := preservesFiniteLimits G hG
    (tensorObj G).IsLocalization ((tensorObj G).kernel.isoModSerre) := by
  letI := preservesFiniteLimits G hG
  have := full G hG
  have := (isSeparator_iff_faithful_preadditiveCoyonedaObj G).1 hG
  exact isLocalization_isoModSerre_kernel_of_leftAdjoint
    (tensorObjPreadditiveCoyonedaObjAdjunction G)

end

section

variable (C : Type u) [Category.{v} C]

/-- A Gabriel-Popescu package for an abelian category `C` consists in
the data of a Serre class `P` in a category of modules such
that `C` identifies to the localization of `ModuleCat R` with
respect to `P`, in such a way that the (exact) localization functor has
a fully faithful right adjunction. -/
structure GabrielPopescuPackage [Abelian C] where
  /-- the underlying type of a ring -/
  R : Type w
  /-- `R` is a ring -/
  ring : Ring R := by infer_instance
  /-- a Serre class in the category of modules over `R`. -/
  P : ObjectProperty (ModuleCat.{w} R)
  isSerreClass : P.IsSerreClass := by infer_instance
  /-- the localization functor -/
  L : ModuleCat.{w} R ⥤ C
  /-- the right adjoint of the localization functor -/
  F : C ⥤ ModuleCat.{w} R
  /-- the adjunction -/
  adj : L ⊣ F
  full : F.Full := by infer_instance
  faithful : F.Faithful := by infer_instance
  /-- the localization functor preserves finite limits (TODO: prove
  that it automatically follows from the `isLocalization` field.) -/
  preservesFiniteLimits : PreservesFiniteLimits L := by infer_instance
  isLocalization : L.IsLocalization P.isoModSerre := by infer_instance


variable [Abelian C]

namespace GabrielPopescuPackage

attribute [instance] ring isSerreClass full faithful preservesFiniteLimits isLocalization

variable {C} (p : GabrielPopescuPackage.{w} C)

instance isRightAdjoint : p.F.IsRightAdjoint := ⟨_, ⟨p.adj⟩⟩

instance isLeftAdjoint : p.L.IsLeftAdjoint := ⟨_, ⟨p.adj⟩⟩

instance : p.L.Additive := Functor.additive_of_preserves_binary_products _

instance : p.F.Additive := Functor.additive_of_preserves_binary_products _

instance reflective : Reflective p.F where
  adj := p.adj

/-- A Gabriel-Popescu can be transported from a category to an equivalent category. -/
def ofEquivalence {D : Type u'} [Category.{v'} D] [Abelian D] (e : C ≌ D) :
    GabrielPopescuPackage.{w} D where
  R := p.R
  P := p.P
  L := p.L ⋙ e.functor
  F := e.inverse ⋙ p.F
  adj := p.adj.comp e.toAdjunction

end GabrielPopescuPackage

variable {C} in
/-- The Gabriel-Popescu package obtained from a generator of a Grothendieck abelian category. -/
noncomputable def GabrielPopescu.package
    [IsGrothendieckAbelian.{v} C] (G : C) (hG : IsSeparator G) :
    GabrielPopescuPackage.{v} C := by
  have := preservesFiniteLimits G hG
  have := full G hG
  have := (isSeparator_iff_faithful_preadditiveCoyonedaObj G).1 hG
  exact {
    R := (End G)ᵐᵒᵖ
    P := (tensorObj G).kernel
    L := tensorObj G
    F := preadditiveCoyonedaObj G
    adj := tensorObjPreadditiveCoyonedaObjAdjunction G
    isLocalization := tensorObj_isLocalization G hG }

instance [IsGrothendieckAbelian.{w} C] :
    Nonempty (GabrielPopescuPackage.{w} C) :=
  ⟨GabrielPopescuPackage.ofEquivalence.{w}
    (GabrielPopescu.package.{w} _ (isSeparator_separator _)) (ShrinkHoms.equivalence C).symm⟩

/-- A choice of a Gabriel-Popescu package for any Grothendieck abelian category. -/
noncomputable def gabrielPopescuPackage [IsGrothendieckAbelian.{w} C] :
    GabrielPopescuPackage.{w} C :=
  Classical.arbitrary _

end

end CategoryTheory.IsGrothendieckAbelian
