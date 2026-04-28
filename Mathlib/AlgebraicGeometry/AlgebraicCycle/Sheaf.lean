/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Principal
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The sheaf 𝒪ₓ(D) associated to a Weil divisor D

In this file we construct the sheaf `𝒪(D)` associated to a Weil divisor `D`, defining it on `U`
to be rational functions such that `(f) + D ≥ 0` on `U`. By Weil divisor we just mean an algebraic
cycle purely of codimension `1`. In this file, we actually don't place any restrictions on `D`,
just taking it to be any cycle with coefficients in `ℤ`, just because the actual definitions do
not require this anywhere.

This definition gives good results on Noetherian, integral separated schemes which are regular in
codimension 1. In particular this is useful for working with normal varieties, where the map from
Cartier divisors to Weil divisors is injective.
-/

open AlgebraicGeometry Scheme CategoryTheory Order AlgebraicCycle Opposite

universe u v
variable {X : Scheme.{u}}
         [IsIntegral X]
         [IsLocallyNoetherian X]

open Function locallyFinsuppWithin Ring

class IsIntegralInCodimensionOne (X : Scheme.{u}) where
  domain : ∀ x : X, coheight x = 1 → IsDomain (X.presheaf.stalk x)

lemma IsIntegralInCodimensionOne.stalk_domain {X : Scheme.{u}}
    [h : IsIntegralInCodimensionOne X] (x : X) (hx : coheight x = 1) :
  IsDomain (X.presheaf.stalk x) := h.domain x hx

instance {X : Scheme.{u}} [IsIntegral X] : IsIntegralInCodimensionOne X := ⟨inferInstance⟩

/--
We define a scheme to be regular in codimension one if all its stalks at codimension one are DVRs.
This is equivalent to being regular since a ring is a DVR iff it is a regular local ring of dimension one.
-/
class IsRegularInCodimensionOne (X : Scheme.{u}) extends IsIntegralInCodimensionOne X where
  dvr : ∀ (x : X) (hx : coheight x = 1),
      have := IsIntegralInCodimensionOne.stalk_domain x hx
      IsDiscreteValuationRing (X.presheaf.stalk x)

lemma IsRegularInCodimensionOne.stalk_dvr {X : Scheme.{u}} [h : IsRegularInCodimensionOne X] (x : X)
    (hx : coheight x = 1) :
  have := IsIntegralInCodimensionOne.stalk_domain x hx
  IsDiscreteValuationRing (X.presheaf.stalk x) := h.dvr x hx

--variable [IsRegularInCodimensionOne X]

namespace AlgebraicCycle
namespace Sheaf

/--
The underlying set of `Γ(𝒪ₓ(D), U)`, defined to be:
`Γ(𝒪ₓ(D), U) := {s : k(X) | s ≠ 0 → Nonempty U ∧ s|_U + D|_U ≥ 0}`.
-/
def carrier (D : AlgebraicCycle X ℤ) (U : X.Opens) : Set X.functionField :=
    {s : (X.functionField) | (h : s ≠ 0) → Nonempty U ∧ (div s h).restrict U + D.restrict U ≥ 0}

def add_mem' [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (U : X.Opens)
    {a b : ↑X.functionField}
    (ha : a ∈ carrier D U) (hb : b ∈ carrier D U) : a + b ∈ carrier D U := by
    by_cases hU : Nonempty U
    · simp_all only [carrier, ne_eq, ge_iff_le, true_and, Set.mem_setOf_eq, Opens.nonempty_iff]
      intro h
      by_cases ha0 : a = 0
      · simp_all
      by_cases hb0 : b = 0
      · simp_all
      intro Z
      specialize ha ha0 Z
      specialize hb hb0 Z
      simp_all only [coe_zero, Pi.zero_apply, coe_add, Pi.add_apply]
      have hU : U.1 ⊆ ⊤ := by aesop
      suffices min ((div a ha0).restrict U Z) ((div b hb0).restrict U Z) ≤
              (div (a + b) h).restrict U Z by omega
      by_cases hZ : coheight Z = 1
      · have := krullDimLE_of_coheight hZ
        by_cases o : Z ∈ U
        · simp [restrict_eq_of_mem _ _ _ o,
                div_eq_ord_of_coheight_eq_one _ _ _ hZ, Scheme.ord]
          have : IsDiscreteValuationRing ↑(X.presheaf.stalk Z) :=
              IsRegularInCodimensionOne.stalk_dvr Z hZ
          have := @ordFrac_add (X.presheaf.stalk Z)
            _ _ _ (X.functionField) _ (stalkFunctionFieldAlgebra X Z) _ a b h
          simp_all
        · simp [restrict_eq_zero_of_not_mem _ _ _ o]
      · by_cases o : Z ∈ U
        · simp only [restrict_eq_of_mem _ _ _ o, inf_le_iff]
          rw[div_eq_zero_of_coheight_ne_one _ _ _ hZ, div_eq_zero_of_coheight_ne_one _ _ _ hZ,
            div_eq_zero_of_coheight_ne_one _ _ _ hZ]
          simp
        · simp [restrict_eq_zero_of_not_mem _ _ _ o]
    · simp_all [carrier]

def zero_mem' (D : AlgebraicCycle X ℤ) (U : X.Opens) : 0 ∈ carrier D U := by
  simp [carrier]

def neg_mem' (D : AlgebraicCycle X ℤ) (U : X.Opens) (f : X.functionField) (hf : f ∈ carrier D U) :
    (- f) ∈ carrier D U := by
  simp_all [carrier]

def smul_mem' (D : AlgebraicCycle X ℤ) (U : X.Opens) [Nonempty U] (a : Γ(X, U)) {f : X.functionField}
  (hf : f ∈ carrier D U) : a • f ∈ carrier D U := by
    simp_all only [carrier, true_and]
    intro nez z
    have h : ¬ f = 0 := by
      intro _
      simp_all
    specialize hf h z
    simp only [coe_zero, Pi.zero_apply, coe_add, Pi.add_apply] at hf
    have hU : U.1 ⊆ ⊤ := by simp_all
    suffices (div f h).restrict U z ≤ (div (a • f) nez).restrict U z by
      trans (div f h).restrict U z + D.restrict U z
      · exact hf
      · exact
        (Int.add_le_add_iff_right
              ((locallyFinsuppWithin.restrict D (of_eq_true (Set.subset_univ._simp_1 ↑U))) z)).mpr
          this
    by_cases hz : coheight z = 1
    · by_cases o : z ∈ U
      · simp [restrict_eq_of_mem _ _ _ o,
          div_eq_ord_of_coheight_eq_one _ _ _ hz, Scheme.ord]
        let i := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, o⟩
        have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk z) := krullDimLE_of_coheight hz
        let test : IsScalarTower ↑Γ(X, U) ↑(X.presheaf.stalk z) ↑X.functionField :=
            AlgebraicGeometry.functionField_isScalarTower X U ⟨z, o⟩
        apply @ordFrac_le_smul _ _ _ _ _ _ _ _ _ _ _ _ _ test a ?_ f
        · suffices ((algebraMap ↑Γ(X, U) ↑(X.presheaf.stalk z)) a) • f ≠ 0 by
            exact left_ne_zero_of_smul this
          simpa [algebraMap_smul]
      · simp [restrict_eq_zero_of_not_mem _ _ _ o]
    · by_cases o : z ∈ U
      · simp [restrict_eq_of_mem _ _ _ o,
              div_eq_zero_of_coheight_ne_one _ _ _ hz]
      · simp [restrict_eq_zero_of_not_mem _ _ _ o]

variable [IsRegularInCodimensionOne X]
def addSubgroup (D : AlgebraicCycle X ℤ) (U : X.Opens) : AddSubgroup X.functionField where
  carrier := carrier D U
  add_mem' := add_mem' D U
  zero_mem' := zero_mem' D U
  neg_mem' := by simp_all [carrier];

lemma memAddSubgroup {D : AlgebraicCycle X ℤ} {U : X.Opens} (f : carrier D U) :
    (f : X.functionField) ∈ addSubgroup D U := by simp

@[simps]
def mk_of_mem_subgroup {D : AlgebraicCycle X ℤ} {U : X.Opens} (f : X.functionField)
    (hf : f ∈ addSubgroup D U) : carrier D U := ⟨f, hf⟩

noncomputable section insts

variable {U : X.Opens} {D : AlgebraicCycle X ℤ}
instance : Zero (carrier D U) where
  zero := mk_of_mem_subgroup 0 <| zero_mem _

instance : Add (carrier D U) where
  add f g := mk_of_mem_subgroup (f + g) <| add_mem (AlgebraicCycle.Sheaf.memAddSubgroup f)
      (AlgebraicCycle.Sheaf.memAddSubgroup g)

instance : Neg (carrier D U) where
  neg f := mk_of_mem_subgroup (-f) <| neg_mem (Sheaf.memAddSubgroup f)

instance : Sub (carrier D U) where
  sub f g := mk_of_mem_subgroup (f - g) <| sub_mem (memAddSubgroup f) (memAddSubgroup g)

instance : SMul ℕ (carrier D U) where
  smul n f := mk_of_mem_subgroup (n • f) <| nsmul_mem (memAddSubgroup f) n

instance : SMul ℤ (carrier D U) where
  smul n f := mk_of_mem_subgroup (n • f) <| zsmul_mem (memAddSubgroup f) n

@[simp] lemma coe_zero : ((0 : carrier D U) : X.functionField) = 0 := rfl

@[simp] lemma coe_add (f g : carrier D U) :
    (↑(f + g) : X.functionField) = f + g := rfl

@[simp] lemma coe_neg (f : carrier D U) :
    (↑(-f) : X.functionField) = -(f : X.functionField) := rfl

@[simp] lemma coe_sub (f g : carrier D U) :
    (↑(f - g) : X.functionField) = f - g := rfl

@[simp] lemma coe_nsmul (f : carrier D U) (n : ℕ) :
    (↑(n • f) : X.functionField) = n • (f : X.functionField) := rfl

@[simp] lemma coe_zsmul (f : carrier D U) (n : ℤ) :
    (↑(n • f) : X.functionField) = n • (f : X.functionField) := rfl

instance : AddCommGroup (carrier D U) :=
  Injective.addCommGroup (M₁ := carrier D U) (M₂ := X.functionField)
    Subtype.val Subtype.coe_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

def moduleNonempty
    (D : AlgebraicCycle X ℤ) (U : X.Opens) [Nonempty U] :
    Submodule Γ(X, U) X.functionField where
  __ := addSubgroup D U
  smul_mem' := smul_mem' D U

lemma memModuleNonempty {D : AlgebraicCycle X ℤ} {U : X.Opens} [Nonempty U] (f : carrier D U) :
    (f : X.functionField) ∈ moduleNonempty D U := by simp

@[simps]
def mk_of_mem_module_nonempty {D : AlgebraicCycle X ℤ} {U : X.Opens} [Nonempty U]
    (f : X.functionField) (hf : f ∈ moduleNonempty D U) :
    carrier D U := ⟨f, hf⟩

-- Modified by Claude Opus 4.6: unconditional SMul to eliminate instance diamond.
-- The key invariant: smulVal does NOT depend on D, so (a • f).val is the same
-- for carrier D U and carrier D' U, making map_smul' in extend provable by rfl.
private noncomputable def smulVal (a : Γ(X, U)) (v : X.functionField) : X.functionField := by
  by_cases h : Nonempty U
  · haveI := h; exact a • v
  · exact v

private lemma smulVal_mem_carrier (a : Γ(X, U)) (f : carrier D U) :
    smulVal a f.val ∈ carrier D U := by
  simp only [smulVal]
  split_ifs with hU
  · exact smul_mem' D U a f.prop
  · exact f.prop

noncomputable instance : SMul Γ(X, U) (carrier D U) where
  smul a f := ⟨smulVal a f.val, smulVal_mem_carrier a f⟩

@[simp] lemma coe_smul [hU : Nonempty U] (a : Γ(X, U)) (f : carrier D U) :
    (↑(a • f) : X.functionField) = a • (f : X.functionField) := by
  show smulVal a f.val = a • (f : X.functionField)
  simp [smulVal, hU]

def moduleInstNonempty (D : AlgebraicCycle X ℤ) (U : X.Opens) [Nonempty U] :
  Module Γ(X, U) (carrier D U) :=
  let v : carrier D U →+ X.functionField := {
    toFun := Subtype.val
    map_zero' := by simp
    map_add' := by simp
  }
  Injective.module Γ(X, U) (M₂ := carrier D U) (M := X.functionField) v
  Subtype.coe_injective coe_smul

--instance : Subsingleton (carrier D ⊥) := by simp [carrier]
instance instSubsingleTonOfEmpty (h : ¬ Nonempty U) : Subsingleton (carrier D U) := by
  simp [carrier, h]

-- Modified by Claude Opus 4.6: define instModuleCarrier with smul := (· • ·) using
-- the global SMul instance. This ensures instModuleCarrier.toSMul is definitionally
-- the global SMul, eliminating the instance diamond across different divisors.
noncomputable instance instModuleCarrier : Module Γ(X, U) (carrier D U) where
  smul := (· • ·)
  one_smul a := by
    apply Subtype.ext
    change smulVal 1 a.val = a.val
    simp only [smulVal]
    split_ifs with h <;> simp
  mul_smul r s x := by
    apply Subtype.ext
    change smulVal (r * s) x.val = smulVal r (smulVal s x.val)
    simp only [smulVal]
    split_ifs with h <;> [exact mul_smul r s x.val; rfl]
  smul_zero r := by
    apply Subtype.ext
    change smulVal r (0 : carrier D U).val = (0 : carrier D U).val
    simp only [smulVal, coe_zero]
    split_ifs with h <;> simp
  smul_add r x y := by
    apply Subtype.ext
    change smulVal r (x + y).val = (⟨smulVal r x.val, _⟩ + ⟨smulVal r y.val, _⟩ : carrier D U).val
    simp only [coe_add, smulVal]
    split_ifs with h <;> [exact smul_add r x.val y.val; rfl]
  add_smul r s x := by
    apply Subtype.ext
    change smulVal (r + s) x.val = (⟨smulVal r x.val, _⟩ + ⟨smulVal s x.val, _⟩ : carrier D U).val
    simp only [coe_add, smulVal]; split_ifs with h
    · exact add_smul r s x.val
    · have : Subsingleton (carrier D U) := instSubsingleTonOfEmpty h
      have := Subsingleton.elim x 0; subst this; simp
  zero_smul x := by
    apply Subtype.ext
    change smulVal 0 x.val = (0 : carrier D U).val
    simp only [smulVal]; split_ifs with h
    · simp
    · have : Subsingleton (carrier D U) := instSubsingleTonOfEmpty h
      exact congr_arg Subtype.val (Subsingleton.elim x 0)

end insts

--open Pseudofunctor

noncomputable
def obj (D : AlgebraicCycle X ℤ) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
    ModuleCat (X.ringCatSheaf.obj.obj U) := .of Γ(X, unop U) <| carrier D (unop U)

open Classical in
lemma _root_.Function.locallyFinsuppWithin_le_iff {X Y : Type*} [TopologicalSpace X] {U : Set X}
    [Zero Y] [Lattice Y] (D D' : locallyFinsuppWithin U Y) : D ≤ D' ↔ ∀ z ∈ U, D z ≤ D' z :=
  ⟨fun h z _ ↦ h z, fun h z ↦ if hz : z ∈ U then h z hz else by simp [hz]⟩

lemma mapFunProof (D : AlgebraicCycle X ℤ) {U V : X.Opens}
    (r : V ≤ U) [hV : Nonempty V] (f : X.functionField) (hf : f ∈ carrier D U) :
    f ∈ carrier D V := by
  intro h
  specialize hf h
  refine ⟨hV, ?_⟩
  simp only [ge_iff_le]
  rw [homogeneous_le_iff (t := V)]
  on_goal 1 =>
    intro z hz
    have := hf.2 z
    simpa [hz, r hz] using this
  all_goals simp_all

open Classical in
noncomputable
def mapFun (D : AlgebraicCycle X ℤ) {U V : X.Opens} (r : V ≤ U) : carrier D U → carrier D V :=
  fun ⟨f, hf⟩ ↦ if hV : Nonempty V then ⟨f, mapFunProof D r f hf⟩ else ⟨0, by simp [carrier]⟩

@[simp]
lemma mapFunApplyNonempty (D : AlgebraicCycle X ℤ) {U V : X.Opens} (r : V ≤ U) [h : Nonempty V]
    (s : carrier D U) : (mapFun D r s).1 = s := by
  simp [mapFun, h]


instance algebra_restrict {U V : X.Opens} (k : V ≤ U) :
    Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map (homOfLE k).op).hom.toAlgebra

lemma _root_.Nonempty_le {U V : X.Opens} (k : V ≤ U) [Nonempty V] : Nonempty U := by
  rename_i hV
  obtain ⟨⟨a, b⟩⟩ := hV
  use a
  exact k b

instance [IrreducibleSpace X] {U V : X.Opens} (k : V ≤ U)
    [Nonempty V] :
    let o := algebra_restrict k
    have : Nonempty U := by
      rename_i hV
      obtain ⟨⟨a, b⟩⟩ := hV
      use a
      exact k b
    IsScalarTower Γ(X, U) Γ(X, V) X.functionField := by
  let o := algebra_restrict k
  have : Nonempty U := by
    rename_i hV
    obtain ⟨⟨a, b⟩⟩ := hV
    use a
    exact k b
  apply IsScalarTower.of_algebraMap_eq'
  simp_rw [RingHom.algebraMap_toAlgebra]
  change _ = (X.presheaf.map (homOfLE k).op ≫ _).hom
  simp

set_option backward.isDefEq.respectTransparency false in
noncomputable
def map (D : AlgebraicCycle X ℤ) {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ} (r : U ⟶ V) :
    obj D U ⟶ (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map r).hom).obj (obj D V) := by
  apply ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map r).hom).obj (obj D V))
  exact {
    toFun := mapFun D (leOfHom (unop r))
    map_add' x y := by
      by_cases hV : Nonempty V.unop
      · simp [mapFun, hV]
        rfl
      · simp [mapFun, hV]
        rfl
    map_smul' m a := by
      /-
      TODO: Clean this up and make it so this isn't such a pain to work with
      -/
      simp
      by_cases hV : Nonempty V.unop
      · rw [ModuleCat.restrictScalars.smul_def
            (X.sheaf.obj.map r).hom m (M := obj D V) (mapFun D (leOfHom (unop r)) a)]
        have := coe_smul (a := (X.sheaf.obj.map r) m) (f := mapFun D (leOfHom (unop r)) a)
        rw [coe_smul] at this

        convert this.symm
        simp
        apply Subtype.ext
        have : Nonempty U.unop := Nonempty_le (leOfHom r.unop)
        simp
        /-
        The below code worked on an older version of mathlib, however it's unclear to me what has
        changed. TODO: Figure out how to make the below code work again (I think it'll probably
        be a matter of feeding the right instances to coe_smul)
        -/
        sorry
        /-rw [coe_smul]
        simp [obj]
        rw [coe_smul]
        simp
        let o : Algebra Γ(X, U.unop) Γ(X, V.unop) := (X.sheaf.val.map r).hom.toAlgebra
        let k : Algebra Γ(X, V.unop) X.functionField := (X.germToFunctionField V.unop).hom.toAlgebra
        have : IsScalarTower Γ(X, U.unop) Γ(X, V.unop) X.functionField := by infer_instance
        change m • a = (algebraMap  Γ(X, U.unop) Γ(X, V.unop) m) • a.1
        exact algebra_compatible_smul (↑Γ(X, unop V)) m a.1-/

      · exact Subsingleton.elim (h := instSubsingleTonOfEmpty hV) _ _
  }

set_option backward.isDefEq.respectTransparency false in
def map_id (D : AlgebraicCycle X ℤ) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
    map D (𝟙 U) = (ModuleCat.restrictScalarsId' (RingCat.Hom.hom (X.ringCatSheaf.obj.map (𝟙 U)))
    (congrArg RingCat.Hom.hom (X.ringCatSheaf.obj.map_id U))).inv.app (obj D U) := by
  simp [map]
  by_cases h : Nonempty U.unop
  · apply ModuleCat.hom_ext
    rw [@LinearMap.ext_iff]
    intro x
    apply Subtype.ext
    simp
    rfl
  · apply ModuleCat.hom_ext
    rw [@LinearMap.ext_iff]
    intro x
    exact Subsingleton.elim (h := instSubsingleTonOfEmpty h) _ _

set_option backward.isDefEq.respectTransparency false in
def map_comp (D : AlgebraicCycle X ℤ)
  {U V W : (TopologicalSpace.Opens ↥X)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
  map D (f ≫ g) = map D f ≫
    (ModuleCat.restrictScalars (RingCat.Hom.hom (X.ringCatSheaf.val.map f))).map (map D g) ≫
    (ModuleCat.restrictScalarsComp' (RingCat.Hom.hom (X.ringCatSheaf.val.map f))
    (RingCat.Hom.hom (X.ringCatSheaf.obj.map g))
    (RingCat.Hom.hom (X.ringCatSheaf.obj.map (f ≫ g)))
    (congrArg RingCat.Hom.hom (X.ringCatSheaf.obj.map_comp f g))).inv.app (obj D W) := by
  apply ModuleCat.hom_ext
  rw [@LinearMap.ext_iff]
  intro x
  simp [map]
  by_cases h : Nonempty W.unop
  · have hV : Nonempty V.unop := Nonempty_le <| leOfHom g.unop
    apply Subtype.ext
    simp_all
    change x.1 = (mapFun D (map._proof_1 g) (mapFun D (map._proof_1 f) x))
    simp [hV, h]
  · exact Subsingleton.elim (h := instSubsingleTonOfEmpty h) _ _


open Classical in
noncomputable
def presheaf (D : AlgebraicCycle X ℤ) : PresheafOfModules X.ringCatSheaf.val where
  obj := obj D
  map := map D
  map_id := map_id D
  map_comp := map_comp D

lemma presheaf.obj_eq (D : AlgebraicCycle X ℤ) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
    (presheaf D).obj U = obj D U := rfl

lemma presheaf.obj_eq' (D : AlgebraicCycle X ℤ) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
    (presheaf D).presheaf.obj U = (forget₂ _ _).obj (obj D U) := rfl

lemma presheaf.map_eq (D : AlgebraicCycle X ℤ) {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (r : U ⟶ V) : (presheaf D).map r = map D r := rfl


/--
Something strange is going on with this as well, note that just by simp should work in the sorried
statement below

Now the grind statement is not working...
-/

lemma presheaf.map_eq' (D : AlgebraicCycle X ℤ) {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (r : U ⟶ V) : (presheaf D).presheaf.map r =
    AddCommGrpCat.ofHom (AddMonoidHom.mk' (map D r) sorry) := rfl

def connectedByCover {I : Type*} (𝒰 : I → X.Opens) :
  Rel I I := Relation.TransGen <| fun a b ↦ Nonempty (𝒰 a ⊓ 𝒰 b : X.Opens)

def sections_equal_of_nonempty_intersection {D : AlgebraicCycle X ℤ} {I : Type*}
    {𝒰 : I → X.Opens} {i j : I} (h : Nonempty (𝒰 i ⊓ 𝒰 j : X.Opens))
    (s : (i : I) → ToType ((presheaf D).presheaf.obj (op (𝒰 i))))
    (hs : TopCat.Presheaf.IsCompatible (presheaf D).presheaf 𝒰 s) : (s i).1 = (s j).1 := by
  specialize hs i j
  simp [presheaf, PresheafOfModules.presheaf, map] at hs
  change mapFun D (map._proof_1 (TopologicalSpace.Opens.infLELeft (𝒰 i) (𝒰 j)).op) (s i) =
    mapFun D (map._proof_1 (TopologicalSpace.Opens.infLERight (𝒰 i) (𝒰 j)).op) (s j) at hs
  simp [mapFun] at hs
  let f := (s i).1
  let hf := (s i).2
  have : s i = ⟨f, hf⟩ := rfl
  rw [this] at hs
  let g := (s j).1
  let hg := (s j).2
  have : s j = ⟨g, hg⟩ := rfl
  rw [this] at hs
  simpa [h] using hs

def sections_equal_of_connected_by_cover {D : AlgebraicCycle X ℤ} {I : Type*} {𝒰 : I → X.Opens}
    {i j : I} (h : connectedByCover 𝒰 i j)
    (s : (i : I) → ToType ((presheaf D).presheaf.obj (op (𝒰 i))))
    (hs : TopCat.Presheaf.IsCompatible (presheaf D).presheaf 𝒰 s) : (s i).1 = (s j).1 := by
  induction h
  · rename_i j h
    exact sections_equal_of_nonempty_intersection h s hs
  · rename_i j k ih m l
    rw [l]
    exact sections_equal_of_nonempty_intersection m s hs

/-
We now want to say that on an irreducible space, if we have a cover then any two elements of the
cover are connected by cover
-/
open TopologicalSpace
lemma connectedByCover_of_connected
    {I : Type*} {𝒰 : I → X.Opens}
    (h𝒰 : ConnectedSpace (iSup 𝒰).1)
    (i j : I)
    (hi : (𝒰 i).1.Nonempty) (hj : (𝒰 j).1.Nonempty) : connectedByCover 𝒰 i j := by
  by_contra! p
  simp [connectedByCover] at p
  let s := {k : I | connectedByCover 𝒰 i k}
  let U := ⨆ (k ∈ s), 𝒰 k
  let V := ⨆ (k ∈ sᶜ), 𝒰 k

  have hU : U ≤ iSup 𝒰 := iSup₂_le_iSup (Membership.mem s) 𝒰
  have hV : V ≤ iSup 𝒰 := iSup₂_le_iSup (Membership.mem sᶜ) 𝒰

  let U' : Set (iSup 𝒰).1 := {⟨a, b⟩ : (iSup 𝒰).1 | a ∈ U}
  let V' : Set (iSup 𝒰).1 := {⟨a, b⟩ : (iSup 𝒰).1 | a ∈ V}

  have hU' : IsOpen U' := isOpen_induced_eq.mpr ⟨U, U.2, rfl⟩

  have hV' : IsOpen V' := isOpen_induced_eq.mpr ⟨V, V.2, rfl⟩

  have univ_mem : Set.univ ⊆ U' ∪ V' := by
    have : (⨆ k ∈ s, 𝒰 k) ⊔ (⨆ k ∈ sᶜ, 𝒰 k) = (⨆ k, 𝒰 k) :=
      Eq.symm (iSup_split 𝒰 (Membership.mem s))
    simp [U', V']
    ext ⟨a, ha⟩
    simp [U, V]
    rw [Opens.ext_iff, Set.ext_iff] at this
    specialize this a
    simp at this
    rw [this]
    simp at ha
    exact ha

  have neU' : (Set.univ ∩ U').Nonempty := by
    simp [U', U]
    have nonsense := hi
    obtain ⟨x, hx⟩ := hi
    have : x ∈ iSup 𝒰 := by simp; exact ⟨i, hx⟩
    use ⟨x, this⟩
    simp
    use i
    constructor
    · simp [s, connectedByCover]
      apply Relation.TransGen.single
      aesop
    · exact hx
  have neV' : (Set.univ ∩ V').Nonempty := by
    simp [V', V]
    have nonsense := hj
    obtain ⟨x, hx⟩ := hj
    have : x ∈ iSup 𝒰 := by simp; exact ⟨j, hx⟩
    use ⟨x, this⟩
    simp
    use j
    constructor
    · simpa [s, connectedByCover] using p
    · exact hx


  have iBot : U ⊓ V = ⊥ := by
    ext a
    simp
    by_contra!
    simp [U, V, s] at this
    obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := this
    have : connectedByCover 𝒰 i l := by
      fapply Relation.TransGen.tail
      · exact k
      · exact hk.1
      · use a
        simp
        exact ⟨hk.2, hl.2⟩
    exact hl.1 this


  have ans := h𝒰.isPreconnected_univ U' V' hU' hV' univ_mem neU' neV'
  have : U.1 ∩ V.1 = ∅ := Opens.ext_iff.mp iBot
  have : U' ∩ V' = ∅ := by
    simp [U', V']
    ext ⟨a, b⟩
    rw [Set.ext_iff] at this
    specialize this a
    simp_all
  erw [this] at ans
  simp_all

open Presheaf
lemma isSheaf (D : AlgebraicCycle X ℤ) :
    TopCat.Presheaf.IsSheaf (presheaf D).presheaf := by

  rw[TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro I 𝒰 s hs

  simp [TopCat.Presheaf.IsGluing, presheaf.map_eq', map]
  wlog ne : Nonempty I
  · have : iSup 𝒰 = ⊥ := by aesop
    let s : (presheaf D).obj (op (iSup 𝒰)) := ⟨0, by simp [carrier]⟩
    have ss : Subsingleton ((presheaf D).obj (op (iSup 𝒰))) := by
      rw [this]
      simp [presheaf, obj, carrier]
      exact Unique.instSubsingleton
    have (i : I) : Subsingleton ↑((presheaf D).obj (op (𝒰 i))) := by
      simp at ne
      apply False.elim
      exact IsEmpty.false i
    use s
    constructor
    · intro i
      apply Subsingleton.elim
    · exact fun _ _ ↦ Subsingleton.elim ..


  obtain ⟨i⟩ := ne
  wlog h : (∀ i : I, Nonempty (𝒰 i))
  · have : Nonempty X := inferInstance


    sorry

  have : Nonempty (iSup 𝒰 : TopologicalSpace.Opens X) := by
    simp only [Scheme.Opens.nonempty_iff, Opens.coe_iSup, Set.nonempty_iUnion]
    use i
    exact (Scheme.Opens.nonempty_iff (𝒰 i)).mp (h i)

  have k : AlgebraicGeometry.IsIntegral (iSup 𝒰 : TopologicalSpace.Opens X) := by infer_instance
  /-
  We need to show here that if you have some rational function which is a
  section on some open set, then it should be a section globally.

  This is only true because we have stuff defined for all opens.


  -/
  let sec : carrier D (iSup 𝒰) := {
    val := (s i).1
    property := by

      have : (s i).1 ∈ carrier D (𝒰 i) := by exact Subtype.coe_prop (s i)
      have l : carrier D (𝒰 i) ≤ carrier D (iSup 𝒰) := by
        simp [carrier]
        intro f a b
        specialize a b
        constructor
        · exact ⟨i, a.1⟩
        · have := (a.2)
          rw [locallyFinsuppWithin_le_iff] at ⊢ this
          intro z hz

          simp at hz
          simp [restrict_apply, hz]
          specialize this z


          /-
          We should case match on whether or not z is in 𝒰 i.
          if it is then we're done, otherwise z must be in a set
          which is connected by cover to our 𝒰 i, so we're done.
          -/

          sorry
      exact l this

  }
  use sec
  simp
  constructor
  · intro j
   --unfold mapFun
    simp [sec, h j]
    change ⟨_, _⟩ = s j
    apply Subtype.ext
    simp
    apply sections_equal_of_connected_by_cover
    · apply connectedByCover_of_connected
      · exact IrreducibleSpace.connectedSpace (iSup 𝒰 : TopologicalSpace.Opens X)
      · exact Set.nonempty_coe_sort.mp (h i)
      · exact Set.nonempty_coe_sort.mp (h j)
    · exact hs

  · intro s' h'

    simp [sec]
    unfold mapFun at h'
    specialize h i
    specialize h' i
    simp [h] at h'
    change ⟨_, _⟩ = s i at h'
    rw [← h']
    simp


end Sheaf

/--
Given a Weil divisor `D` on a locally noetherian, integral scheme which is regular in
codimension one, this is a construction of `𝒪ₓ(D)`. Note that the definition does not depend on
`D` only being supported in codimension one, so this definition works for any cycle `D`.
-/
noncomputable
def sheafOfModules {X : Scheme} [AlgebraicGeometry.IsIntegral X] [IsLocallyNoetherian X]
  [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) : X.Modules where
  val := AlgebraicCycle.Sheaf.presheaf D
  isSheaf := AlgebraicCycle.Sheaf.isSheaf D

end AlgebraicCycle
