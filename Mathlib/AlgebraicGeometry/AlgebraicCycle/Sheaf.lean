/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Principal
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The sheaf 𝒪ₓ(D) associated to a Weil divisor D

In this file we construct the sheaf of modules `𝒪ₓ(D)` associated to a Weil divisor `D` on a locally
Noetherian, integral scheme which is regular in codimension 1, defining it on `U`
to be rational functions such that `(f) + D ≥ 0` on `U`. By Weil divisor we just mean an algebraic
cycle purely of codimension `1`. In this file, we actually don't place any restrictions on `D`,
just taking it to be any cycle with coefficients in `ℤ`, just because the actual definitions do
not require this anywhere.

This definition gives good results on locally Noetherian, integral schemes which are
regular in codimension 1. In particular this is useful for working with normal varieties,
where the map from Cartier divisors to Weil divisors is injective. Note that when applied to Weil
divisors which are not Cartier, this sheaf will not necessarily be invertible.

Note that we can extend the construction here to schemes which are not necessarily irreducible with
some extra bookkeeping. That said, in my opinion the most sensible way to do this goes via the
construction on integral schemes, and in any case the construction for integral schemes comes up the
most in applications, hence our decision to formalize the version for integral schemes  .
-/

open AlgebraicGeometry Scheme CategoryTheory Order AlgebraicCycle Opposite

universe u v
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

open Function locallyFinsuppWithin Ring

class IsIntegralInCodimensionOne (X : Scheme.{u}) where
  domain : ∀ x : X, coheight x = 1 → IsDomain (X.presheaf.stalk x)

lemma IsIntegralInCodimensionOne.stalk_domain {X : Scheme.{u}}
    [h : IsIntegralInCodimensionOne X] (x : X) (hx : coheight x = 1) :
  IsDomain (X.presheaf.stalk x) := h.domain x hx

instance {X : Scheme.{u}} [IsIntegral X] : IsIntegralInCodimensionOne X := ⟨inferInstance⟩

/--
We define a scheme to be regular in codimension one if all its stalks at codimension one are DVRs.
This is equivalent to being regular since a ring is a DVR iff it is a regular local ring of
dimension one.

NOTE: This definition and the surrounding lemmas will not be in the final PR - this will soon be
replaced with a definition of Serre's `Rₖ`, and this DVR characterisation will be proven as a lemma.
This requires that regular local rings are domains, which is not yet in Mathlib but will be merged
in soon.
-/
class IsRegularInCodimensionOne (X : Scheme.{u}) extends IsIntegralInCodimensionOne X where
  dvr : ∀ (x : X) (hx : coheight x = 1),
      have := IsIntegralInCodimensionOne.stalk_domain x hx
      IsDiscreteValuationRing (X.presheaf.stalk x)

lemma IsRegularInCodimensionOne.stalk_dvr {X : Scheme.{u}} [h : IsRegularInCodimensionOne X] (x : X)
    (hx : coheight x = 1) :
  have := IsIntegralInCodimensionOne.stalk_domain x hx
  IsDiscreteValuationRing (X.presheaf.stalk x) := h.dvr x hx

namespace AlgebraicCycle
namespace Sheaf

/--
The underlying set of `Γ(𝒪ₓ(D), U)`, defined to be:
`Γ(𝒪ₓ(D), U) := {s : k(X) | s ≠ 0 → Nonempty U ∧ s|_U + D|_U ≥ 0}`.
-/
def carrier (D : AlgebraicCycle X ℤ) (U : X.Opens) : Set X.functionField :=
    {s : (X.functionField) | (h : s ≠ 0) → Nonempty U ∧ (div s h).restrict U + D.restrict U ≥ 0}

/--
The sum of two sections in `Γ(𝒪ₓ(D), U)` is another section of `Γ(𝒪ₓ(D), U)` on a scheme which is
regular in codimension one. Note that we are using regulariy in codimension one in a fairly
essential way here. One should note that this is the key point where regularity in codimension one
is used in the construction of `𝒪ₓ(D)`.
-/
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
      suffices min ((div a ha0).restrict U Z) ((div b hb0).restrict U Z) ≤
              (div (a + b) h).restrict U Z by omega
      by_cases hZ : coheight Z = 1
      · have := krullDimLE_of_coheight hZ
        by_cases o : Z ∈ U
        · simp only [restrict_eq_of_mem _ _ _ o, div_eq_ord_of_coheight_eq_one _ _ _ hZ]
          have : IsDiscreteValuationRing ↑(X.presheaf.stalk Z) :=
              IsRegularInCodimensionOne.stalk_dvr Z hZ
          exact ordZ_add hZ ha0 hb0 h
        · simp [restrict_eq_zero_of_not_mem _ _ _ o]
      · by_cases o : Z ∈ U
        · simp only [restrict_eq_of_mem _ _ _ o, inf_le_iff]
          rw[div_eq_zero_of_coheight_ne_one _ _ _ hZ, div_eq_zero_of_coheight_ne_one _ _ _ hZ,
            div_eq_zero_of_coheight_ne_one _ _ _ hZ]
          simp
        · simp [restrict_eq_zero_of_not_mem _ _ _ o]
    · simp_all [carrier]

/--
Zero is an element of `Γ(𝒪ₓ(D), U)` by definition
-/
def zero_mem' (D : AlgebraicCycle X ℤ) (U : X.Opens) : 0 ∈ carrier D U := by
  simp [carrier]

/--
`Γ(𝒪ₓ(D), U)` is closed under negatives.
-/
def neg_mem' (D : AlgebraicCycle X ℤ) (U : X.Opens) {f : X.functionField} (hf : f ∈ carrier D U) :
    (- f) ∈ carrier D U := by simp_all [carrier]

/--
On a nonempty set `U`, `Γ(𝒪ₓ(D), U)` is closed scalar multiplication by elements of `Γ(X, U)`.
-/
def smul_mem_nonempty (D : AlgebraicCycle X ℤ) (U : X.Opens) [Nonempty U] (a : Γ(X, U))
    {f : X.functionField} (hf : f ∈ carrier D U) : a • f ∈ carrier D U := by
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
      · simp only [restrict_eq_of_mem _ _ _ o, div_eq_ord_of_coheight_eq_one _ _ _ hz]
        let i := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, o⟩
        have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk z) := krullDimLE_of_coheight hz
        let test : IsScalarTower ↑Γ(X, U) ↑(X.presheaf.stalk z) ↑X.functionField :=
            AlgebraicGeometry.functionField_isScalarTower X U ⟨z, o⟩
        exact ordZ_le_smul _ o (left_ne_zero_of_smul nez) _
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
  neg_mem' := neg_mem' D U

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

/--
At some level, the definition of scalar multiplication on `Γ(𝒪ₓ(D), U)` needs to have some case
distinction like this because the behaviour at the empty set and any other set is completely
different. Here, we have decided to put this case distinction into the definition of the scalar
multiplication function, rather than having two different module instances depending on whether
the set is empty or not. The thought is that this awkwardness is excusable in the SMul definition
because users shouldn't be unfolding this, but that comparing the action on different sets is going
to be really annoying if we always need to carry around some if then else.
-/
private noncomputable def smulVal (a : Γ(X, U)) (v : X.functionField) : X.functionField := by
  classical
  exact if h : Nonempty U then haveI := h; a • v else v

omit [IsRegularInCodimensionOne X] in
private lemma smulVal_mem_carrier (a : Γ(X, U)) (f : carrier D U) :
    smulVal a f.val ∈ carrier D U := by
  simp only [smulVal]
  split_ifs with hU
  · exact smul_mem_nonempty D U a f.prop
  · exact f.prop

noncomputable instance : SMul Γ(X, U) (carrier D U) where
  smul a f := ⟨smulVal a f.val, smulVal_mem_carrier a f⟩

omit [IsRegularInCodimensionOne X] in
@[simp] lemma coe_smul [hU : Nonempty U] (a : Γ(X, U)) (f : carrier D U) :
    (↑(a • f) : X.functionField) = a • (f : X.functionField) := by
  change smulVal a f.val = a • (f : X.functionField)
  simp [smulVal, hU]

instance instSubsingleTonOfEmpty (h : ¬ Nonempty U) : Subsingleton (carrier D U) := by
  simp [carrier, h]

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

/--
The action of `𝒪ₓ(D)` on objects.
-/
noncomputable
def obj (D : AlgebraicCycle X ℤ) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
    ModuleCat (X.ringCatSheaf.obj.obj U) := .of Γ(X, unop U) <| carrier D (unop U)

omit [IsRegularInCodimensionOne X] in
/--
TODO rename
-/
lemma mapFunProof (D : AlgebraicCycle X ℤ) {U V : X.Opens}
    (r : V ≤ U) [hV : Nonempty V] (f : X.functionField) (hf : f ∈ carrier D U) :
    f ∈ carrier D V := by
  refine fun h ↦ ⟨hV, ge_iff_le.mpr ?_⟩
  rw [homogeneous_le_iff (t := V)]
  on_goal 1 =>
    intro z hz
    have := (hf h).2 z
    simpa [hz, r hz] using this
  all_goals simp_all

open Classical in
/--
The function underlying the action of `𝒪ₓ(D)` on morphisms.
-/
noncomputable
def mapFun (D : AlgebraicCycle X ℤ) {U V : X.Opens} (r : V ≤ U) : carrier D U → carrier D V :=
  fun ⟨f, hf⟩ ↦ if hV : Nonempty V then ⟨f, mapFunProof D r f hf⟩ else ⟨0, by simp [carrier]⟩

omit [IsRegularInCodimensionOne X] in
@[simp]
lemma mapFunApplyNonempty (D : AlgebraicCycle X ℤ) {U V : X.Opens} (r : V ≤ U) [h : Nonempty V]
    (s : carrier D U) : (mapFun D r s).1 = s := by simp [mapFun, h]

instance algebra_restrict {U V : X.Opens} (k : V ≤ U) :
    Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map (homOfLE k).op).hom.toAlgebra

/--
TODO: Make this statement less cursed and put it in its own? PR (or at the very least in a
more sensible file).
-/
instance [IrreducibleSpace X] {U V : X.Opens} (k : V ≤ U) [Nonempty V] :
    letI o := algebra_restrict k
    haveI : Nonempty U := by
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
    obj D U ⟶ (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map r).hom).obj (obj D V) :=
  ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map r).hom).obj (obj D V))
  {
    toFun := mapFun D (leOfHom (unop r))
    map_add' x y := by
      by_cases hV : Nonempty V.unop
      · simp [mapFun, hV]
        rfl
      · simp [mapFun, hV]
        rfl
    map_smul' m a := by
      dsimp [mapFun]
      split_ifs
      · dsimp [smulVal]
        split_ifs
        · let : Algebra Γ(X, U.unop) Γ(X, V.unop) := (X.sheaf.obj.map r).hom.toAlgebra
          apply Subtype.ext
          erw [coe_smul]
          exact algebra_compatible_smul Γ(X, V.unop) m a.1
        · have : ¬ Nonempty ↑(unop V) := by
            have := leOfHom r.unop
            suffices (unop V) = ⊥ by simp_all only [Opens.nonempty_iff,
              TopologicalSpace.Opens.coe_bot, Set.not_nonempty_empty]
            have a : unop U = ⊥ := by
              rename_i _ hU
              rw [Opens.nonempty_iff, TopologicalSpace.Opens.nonempty_coe] at hU
              rw [← TopologicalSpace.Opens.coe_eq_empty, Set.eq_empty_iff_forall_notMem]
              tauto
            exact eq_bot_mono this a
          contradiction
      · rename_i _ hV
        exact Subsingleton.elim (h := instSubsingleTonOfEmpty hV) _ _
  }

set_option backward.isDefEq.respectTransparency false in
def map_id (D : AlgebraicCycle X ℤ) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
    map D (𝟙 U) = (ModuleCat.restrictScalarsId' (RingCat.Hom.hom (X.ringCatSheaf.obj.map (𝟙 U)))
    (congrArg RingCat.Hom.hom (X.ringCatSheaf.obj.map_id U))).inv.app (obj D U) := by
  by_cases h : Nonempty U.unop
  · apply ModuleCat.hom_ext
    rw [LinearMap.ext_iff]
    intro x
    apply Subtype.ext
    simp [map]
    rfl
  · apply ModuleCat.hom_ext
    rw [LinearMap.ext_iff]
    intro x
    exact Subsingleton.elim (h := instSubsingleTonOfEmpty h) _ _

set_option backward.isDefEq.respectTransparency false in
def map_comp (D : AlgebraicCycle X ℤ)
  {U V W : (TopologicalSpace.Opens ↥X)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
  map D (f ≫ g) = map D f ≫
    (ModuleCat.restrictScalars (RingCat.Hom.hom (X.ringCatSheaf.obj.map f))).map (map D g) ≫
    (ModuleCat.restrictScalarsComp' (RingCat.Hom.hom (X.ringCatSheaf.obj.map f))
    (RingCat.Hom.hom (X.ringCatSheaf.obj.map g))
    (RingCat.Hom.hom (X.ringCatSheaf.obj.map (f ≫ g)))
    (congrArg RingCat.Hom.hom (X.ringCatSheaf.obj.map_comp f g))).inv.app (obj D W) := by
  apply ModuleCat.hom_ext
  rw [LinearMap.ext_iff]
  intro x
  dsimp [map]
  by_cases h : Nonempty W.unop
  · have hV : Nonempty V.unop :=
      (Opens.nonempty_iff (unop V)).mpr <| Exists.imp (leOfHom g.unop) (nonempty_subtype.mp h)
    apply Subtype.ext
    simp only [mapFunApplyNonempty, op_unop, sheafCompose_obj_obj, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj, Functor.comp_map, CommRingCat.forgetToRingCat_map_hom]
    change x.1 = (mapFun D (map._proof_1 g) (mapFun D (map._proof_1 f) x))
    simp
  · exact Subsingleton.elim (h := instSubsingleTonOfEmpty h) _ _

open Classical in
noncomputable
def _root_.AlgebraicCycle.presheaf (D : AlgebraicCycle X ℤ) :
    PresheafOfModules X.ringCatSheaf.obj where
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
Given a family of sets indexed by `I`, `i` and `j` are `ConnectedByCover` if there is a series of
indices `i = i₀, i_1, ..., iₙ = j` such that `iₖ ∩ iₗ` is nonempty for `l = k + 1`.
-/
def ConnectedByCover {I : Type*} (𝒰 : I → X.Opens) :
  Rel I I := Relation.TransGen <| fun a b ↦ Nonempty (𝒰 a ⊓ 𝒰 b : X.Opens)

/--
If sections `s : Γ(𝒪ₓ(D), U)` and `s' : Γ(𝒪ₓ(D), V)` are equal on `U ∩ V` and `U ∩ V` is nonempty,
then `s` and `s'` have the same underlying rational function.
-/
lemma sections_equal_of_nonempty_intersection {D : AlgebraicCycle X ℤ} {I : Type*}
    {𝒰 : I → X.Opens} {i j : I} (h : Nonempty (𝒰 i ⊓ 𝒰 j : X.Opens))
    (s : (i : I) → ToType ((presheaf D).presheaf.obj (op (𝒰 i))))
    (hs : TopCat.Presheaf.IsCompatible (presheaf D).presheaf 𝒰 s) : (s i).1 = (s j).1 := by
  specialize hs i j
  dsimp [presheaf, PresheafOfModules.presheaf, map] at hs
  change mapFun D (map._proof_1 (TopologicalSpace.Opens.infLELeft (𝒰 i) (𝒰 j)).op) (s i) =
    mapFun D (map._proof_1 (TopologicalSpace.Opens.infLERight (𝒰 i) (𝒰 j)).op) (s j) at hs
  dsimp [mapFun] at hs
  let f := (s i).1
  let hf := (s i).2
  have : s i = ⟨f, hf⟩ := rfl
  rw [this] at hs
  let g := (s j).1
  let hg := (s j).2
  have : s j = ⟨g, hg⟩ := rfl
  rw [this] at hs
  simpa [h] using hs

lemma sections_equal_of_connected_by_cover {D : AlgebraicCycle X ℤ} {I : Type*} {𝒰 : I → X.Opens}
    {i j : I} (h : ConnectedByCover 𝒰 i j)
    (s : (i : I) → ToType ((presheaf D).presheaf.obj (op (𝒰 i))))
    (hs : TopCat.Presheaf.IsCompatible (presheaf D).presheaf 𝒰 s) : (s i).1 = (s j).1 := by
  induction h with
  | single h => exact sections_equal_of_nonempty_intersection h s hs
  | tail _ step ih => rw [ih]; exact sections_equal_of_nonempty_intersection step s hs


open TopologicalSpace
/--
If a family of sets has a connected supremum, then between any two sets of the cover there is a
sequence of sets in the cover which intersect nontrivially pairwise.
-/
lemma connectedByCover_of_connected {I : Type*} {𝒰 : I → X.Opens}
    (h𝒰 : _root_.IsConnected (iSup 𝒰).1) (i j : I) (hi : (𝒰 i).1.Nonempty)
    (hj : (𝒰 j).1.Nonempty) : ConnectedByCover 𝒰 i j := by
  by_contra hij
  let S : Set I := {k | ConnectedByCover 𝒰 i k}
  let U : X.Opens := ⨆ k ∈ S, 𝒰 k
  let V : X.Opens := ⨆ k ∈ Sᶜ, 𝒰 k
  have hsplit : iSup 𝒰 = U ⊔ V := iSup_split 𝒰 (· ∈ S)
  have hi_S : i ∈ S :=
    let ⟨x, hx⟩ := hi; Relation.TransGen.single ⟨x, hx, hx⟩
  have hcover : (iSup 𝒰).1 ⊆ U.1 ∪ V.1 := by rw [hsplit]; exact subset_rfl
  have mem_iSup_at {T : Set I} {k : I} (hk : k ∈ T) {x : X} (hx : x ∈ 𝒰 k) :
      x ∈ (⨆ l ∈ T, 𝒰 l : X.Opens) := Opens.mem_iSup.mpr ⟨k, Opens.mem_iSup.mpr ⟨hk, hx⟩⟩
  have hUne : ((iSup 𝒰).1 ∩ U.1).Nonempty :=
    let ⟨x, hx⟩ := hi; ⟨x, Opens.mem_iSup.mpr ⟨i, hx⟩, mem_iSup_at hi_S hx⟩
  have hVne : ((iSup 𝒰).1 ∩ V.1).Nonempty :=
    let ⟨x, hx⟩ := hj; ⟨x, Opens.mem_iSup.mpr ⟨j, hx⟩, mem_iSup_at hij hx⟩
  obtain ⟨x, -, hxU, hxV⟩ := h𝒰.isPreconnected U.1 V.1 U.2 V.2 hcover hUne hVne
  have hxU' : x ∈ U := hxU
  have hxV' : x ∈ V := hxV
  simp only [U, V, Opens.mem_iSup] at hxU' hxV'
  obtain ⟨k, hk, hxk⟩ := hxU'
  obtain ⟨l, hl, hxl⟩ := hxV'
  exact hl (hk.tail ⟨x, hxk, hxl⟩)

open Presheaf
/--
`𝒪ₓ(D)` is a sheaf
-/
lemma isSheaf (D : AlgebraicCycle X ℤ) :
    TopCat.Presheaf.IsSheaf (presheaf D).presheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluingNontrivial]
  on_goal 2 =>
    simp only [sheafCompose_obj_obj, presheaf, PresheafOfModules.presheaf_obj_coe, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj, obj, carrier, ne_eq, Opens.coe_bot, Set.coe_setOf,
      Opens.nonempty_iff, Set.not_nonempty_empty, ge_iff_le, false_and, imp_false, not_not]
    infer_instance
  intro I hI 𝒰 h𝒰 s hs
  obtain ⟨i⟩ := hI
  have : Nonempty (iSup 𝒰 : TopologicalSpace.Opens X) := by aesop
  have h_eq (j : I) : (s i).1 = (s j).1 := by
    apply sections_equal_of_connected_by_cover _ s hs
    apply connectedByCover_of_connected
    · apply IsIrreducible.isConnected
      have := irreducibleSpace_of_isIntegral ↑(iSup 𝒰)
      exact isIrreducible_iff_irreducibleSpace.mpr this
    · exact Set.nonempty_coe_sort.mp (h𝒰 i)
    · exact Set.nonempty_coe_sort.mp (h𝒰 j)
  let sec : carrier D (iSup 𝒰) := {
    val := (s i).1
    property := by
      simp only [carrier, ne_eq, Opens.nonempty_iff, Opens.coe_iSup, Set.nonempty_iUnion, ge_iff_le,
        Set.mem_setOf_eq]
      intro hf
      refine ⟨⟨i, Set.nonempty_coe_sort.mp (h𝒰 i)⟩, ?_⟩
      rw [homogeneous_le_iff (t := ⋃ i, ↑(𝒰 i))]
      · simp_all only [nonempty_subtype, sheafCompose_obj_obj, Opens.nonempty_iff, Opens.coe_iSup,
        Set.nonempty_iUnion, Set.mem_iUnion, SetLike.mem_coe, locallyFinsuppWithin.coe_zero,
        Pi.zero_apply, locallyFinsuppWithin.coe_add, Pi.add_apply, restrict_eq_of_mem,
        forall_exists_index]
        intro z j hz
        simp_rw [h_eq j]
        rw [h_eq j] at hf
        have hsj := (s j).2
        convert (hsj hf).2 z
        simp_all
      all_goals simp_all
  }
  refine ⟨sec, fun j ↦ ?_, fun s' h' ↦ ?_⟩
  · change mapFun D (map._proof_1 (Opens.leSupr 𝒰 j).op) sec = s j
    have : Nonempty ↑(𝒰 j) := h𝒰 j
    simp only [mapFun, this, sec]
    exact Subtype.ext (h_eq j)
  · simp only [sec]
    specialize h' i
    change mapFun D (map._proof_1 (Opens.leSupr 𝒰 i).op) s' = s i at h'
    simp_rw [← h']
    have : Nonempty (𝒰 i) := h𝒰 i
    obtain ⟨p, hp⟩ := s'
    simp

end Sheaf

/--
Given a Weil divisor `D` on a locally noetherian, integral scheme which is regular in
codimension one, this is a construction of `𝒪ₓ(D)`. Note that the definition does not depend on
`D` only being supported in codimension one, so this definition works for any cycle `D`. That said,
this definition is unlikely to give interesting results when `D` is not a Weil divisor.
-/
noncomputable
def sheaf {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) : X.Modules where
  val := D.presheaf
  isSheaf := AlgebraicCycle.Sheaf.isSheaf D


variable (D : AlgebraicCycle X ℤ) (x : X) [IsIntegral X] [IsLocallyNoetherian X]
  [IsRegularInCodimensionOne X]


noncomputable
instance : Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier D.sheaf.val x

open CategoryTheory
open Functor
open Limits
open TopologicalSpace OpenNhds

/-
noncomputable
def genericStalkToFunctionField {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) :
    (TopCat.Presheaf.stalk D.sheaf.val.presheaf (genericPoint X)) ⟶ ((forget₂ CommRingCat RingCat ⋙
    forget₂ RingCat Ab).obj X.functionField) := by
  let c : Cocone <| ((inclusion (genericPoint ↥X)).op ⋙ D.sheaf.val.presheaf) := {
    pt := (forget₂ RingCat Ab).obj ((forget₂ CommRingCat RingCat).obj X.functionField)
    ι := {
      app U :=
        AddCommGrpCat.ofHom {
          toFun f := f.1
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl
        }
      naturality U V f := by
        apply AddCommGrpCat.hom_ext
        simp
        by_cases t : Nonempty (V.unop.1)
        · sorry
        · sorry
    }
  }
  apply colimit.desc _ c

lemma genericStalkToFunctionField_isIso {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) :
    IsIso D.genericStalkToFunctionField := sorry

def genericStalkToFunctionFieldModuleHom {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) :
    ModuleCat.of X.functionField ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf (genericPoint X)) ⟶
    ModuleCat.of X.functionField X.functionField := sorry

lemma genericStalkToFunctionFieldModuleHom_isIso {X : Scheme} [IsIntegral X]
    [IsLocallyNoetherian X]
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) :
    IsIso D.genericStalkToFunctionFieldModuleHom := sorry-/

def Valuation.integer' {R : Type u} {Γ₀ : Type v} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation R Γ₀) (n : Γ₀) : Submodule v.integer R where
    carrier := {x : R | v x ≤ n}
    add_mem' {x y} hx hy := le_trans (v.map_add x y) (max_le hx hy)
    zero_mem' := by simp only [Set.mem_setOf_eq, map_zero, zero_le']
    smul_mem' := by
      intro ⟨x, hx⟩ y hy
      have : v x ≤ 1 := hx
      suffices x • y ∈ {x | v x ≤ n} by exact Set.mem_setOf.mpr this
      simp only [smul_eq_mul, Set.mem_setOf_eq, map_mul]
      exact mul_le_of_le_one_of_le hx hy

def testing {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (x : X) (hx : coheight x = 1) :
    (TopCat.Presheaf.stalk D.sheaf.val.presheaf x).1 =
    {f : X.functionField | X.ord x hx f ≥ WithZero.coe (Multiplicative.ofAdd D x)} := by

  sorry

noncomputable
def stalkCocone {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (x : X) :
    Cocone <| ((inclusion x).op ⋙ D.sheaf.val.presheaf) where
  pt := (forget₂ RingCat Ab).obj ((forget₂ CommRingCat RingCat).obj X.functionField)
  ι := {
    app U :=
      AddCommGrpCat.ofHom {
        toFun f := f.1
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl
      }
    naturality U V f := by
      haveI : Nonempty ((inclusion x).op.obj V).unop := ⟨⟨x, V.unop.2⟩⟩
      apply AddCommGrpCat.hom_ext
      ext s
      exact Sheaf.mapFunApplyNonempty D _ s
  }

noncomputable
def stalkToFunctionField {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (x : X) :
    (TopCat.Presheaf.stalk D.sheaf.val.presheaf x) ⟶ ((forget₂ CommRingCat RingCat ⋙
    forget₂ RingCat Ab).obj X.functionField) :=
  colimit.desc _ (D.stalkCocone x)

@[simp]
lemma stalkToFunctionField_germ {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (x : X) (U : X.Opens) (hxU : x ∈ U)
    (s : Sheaf.carrier D U) :
    D.stalkToFunctionField x (TopCat.Presheaf.germ D.sheaf.val.presheaf U x hxU s) = s.1 := by
  simpa [stalkToFunctionField, TopCat.Presheaf.germ] using colimit.ι_desc_apply _ _ _

lemma stalkToFunctionField_injective {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (x : X) :
    Function.Injective (D.stalkToFunctionField x) := by
  intro a b hab
  obtain ⟨U, hxU, sa, rfl⟩ := TopCat.Presheaf.germ_exist D.sheaf.val.presheaf x a
  obtain ⟨V, hxV, sb, rfl⟩ := TopCat.Presheaf.germ_exist D.sheaf.val.presheaf x b
  rw [stalkToFunctionField_germ, stalkToFunctionField_germ] at hab
  refine TopCat.Presheaf.germ_ext (F := D.sheaf.val.presheaf) (U ⊓ V) ⟨hxU, hxV⟩
    (homOfLE inf_le_left) (homOfLE inf_le_right) ?_
  haveI : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x, ⟨hxU, hxV⟩⟩⟩
  apply Subtype.ext
  exact (Sheaf.mapFunApplyNonempty D inf_le_left sa).trans
    (hab.trans (Sheaf.mapFunApplyNonempty D inf_le_right sb).symm)

noncomputable
def stalkToFunctionFieldLinearMap {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (x : X) :
    ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf x) →ₗ[X.presheaf.stalk x] X.functionField where
  __ := (D.stalkToFunctionField x).hom
  map_smul' r a := by
    -- Get representatives for `a` (in the module stalk) and `r` (in the ring stalk).
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.germ_exist D.sheaf.val.presheaf x a
    obtain ⟨V, hxV, r', rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf x r
    -- Move both germs to a common open `W = U ⊓ V` containing `x`.
    let W : X.Opens := U ⊓ V
    have hxW : x ∈ W := ⟨hxU, hxV⟩
    haveI hWne : Nonempty W := ⟨⟨x, hxW⟩⟩
    letI := X.presheaf.algebra_section_stalk ⟨x, hxW⟩
    letI := AlgebraicGeometry.functionField_isScalarTower X W ⟨x, hxW⟩
    set r_W : Γ(X, W) := (X.presheaf.map (homOfLE (inf_le_right : W ≤ V)).op).hom r' with hr_W_def
    set s_W : Sheaf.carrier D W :=
      (D.sheaf.val.presheaf.map (homOfLE (inf_le_left : W ≤ U)).op).hom s with hs_W_def
    rw [← TopCat.Presheaf.germ_res_apply D.sheaf.val.presheaf
          (homOfLE (inf_le_left : W ≤ U)) x hxW s,
        ← X.presheaf.germ_res_apply (homOfLE (inf_le_right : W ≤ V)) x hxW r']
    -- Combine the scalar action with the germ using `PresheafOfModules.germ_smul`,
    -- restated with `X.presheaf` (which is definitionally `(sheafToPresheaf _).obj X.sheaf`).
    have hgsmul :
        X.presheaf.germ W x hxW r_W •
            TopCat.Presheaf.germ D.sheaf.val.presheaf W x hxW s_W =
          TopCat.Presheaf.germ D.sheaf.val.presheaf W x hxW (r_W • s_W) :=
      (PresheafOfModules.germ_smul (M := D.sheaf.val) x W hxW r_W s_W).symm
    rw [hgsmul]
    -- After `hgsmul`, the LHS is `f (germ (r_W • s_W))`.
    -- We compute both sides via `stalkToFunctionField_germ` and finish with `algebraMap_smul`.
    have hL : (D.stalkToFunctionField x).hom
        (TopCat.Presheaf.germ D.sheaf.val.presheaf W x hxW (r_W • s_W)) = (r_W • s_W).1 :=
      stalkToFunctionField_germ D x W hxW (r_W • s_W)
    have hR : (D.stalkToFunctionField x).hom
        (TopCat.Presheaf.germ D.sheaf.val.presheaf (U ⊓ V) x hxW s_W) = s_W.1 :=
      stalkToFunctionField_germ D x W hxW s_W
    -- Equip the `Ab`-image of `X.functionField` with the module structure of `X.functionField`,
    -- so that the smul in the goal is recognized by typeclass search.
    haveI : Module (X.presheaf.stalk x)
        ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab).obj X.functionField) :=
      inferInstanceAs (Module (X.presheaf.stalk x) X.functionField)
    -- Combine via `Eq.trans`: LHS = (r_W • s_W).1 = r_W • s_W.1 = (germ r_W) • s_W.1
    -- = (germ r_W) • f(germ s_W) = RHS.
    exact hL.trans <|
      ((Sheaf.coe_smul r_W s_W).trans
        (IsScalarTower.algebraMap_smul (X.presheaf.stalk (⟨x, hxW⟩ : W).1) r_W
          (s_W.1 : X.functionField)).symm).trans
        (congrArg ((X.presheaf.germ W x hxW r_W : X.presheaf.stalk x) • ·) hR.symm)

/--
The range of the map from the stalk of O_X(D) at a codimension 1 point `p` is

TODO: Upgrade this to a statement about the range of this function at an arbitrary point (it should
be the same thing, but the condition should be on all points specializing to x)

Then we have 2 options. We can either do this easyish thing or prove the algebraic hartog lemma.
I'm inclined to just do the easier thing for right now
-/
lemma range_stalkToFunctionField {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (hD : D.support ⊆ {x | coheight x = 1})
    (x : X) (hx : coheight x = 1) :
    Set.range (D.stalkToFunctionField x).hom =
      {f : X.functionField | f ≠ 0 → - D x ≤ X.ordZ x hx f} := by
  ext f
  by_cases o : f = 0
  · simp only [o]
    constructor
    · intro h
      tauto
    · intro h
      erw [Set.mem_range]
      use 0
      exact AddMonoidHom.map_zero ((D.stalkToFunctionField x).hom)
  obtain ⟨U, hU1, hU2, hU3⟩ := Function.locallyFinsupp.exists_nhd_mem_support_implies_specializes
      (div f o) x
  obtain ⟨V, hV1, hV2, hV3⟩ := Function.locallyFinsupp.exists_nhd_mem_support_implies_specializes
      D x
  -- Helper: a point of coheight 1 that specializes to `x` (also coheight 1) must equal `x`.
  have spec_eq : ∀ (z : X), coheight z = 1 → z ⤳ x → z = x := by
    intro z hz hspec
    letI : Preorder X := specializationPreorder X
    have hxz : x ≤ z := hspec
    by_cases hzx : z ≤ x
    · exact (Specializes.antisymm hspec (hzx : x ⤳ z)).eq
    · exfalso
      have hlt : x < z := lt_of_le_not_ge hxz hzx
      have hbound := Order.coheight_add_one_le hlt
      rw [hz, hx] at hbound
      norm_num at hbound
  constructor
  · intro h hne
    rw [Set.mem_range] at h
    obtain ⟨g, hg⟩ := h
    obtain ⟨W, hxW, s, rfl⟩ := TopCat.Presheaf.germ_exist D.sheaf.val.presheaf x g
    -- The image of `germ ... s` under `stalkToFunctionField` is `s.1`, hence `s.1 = f`.
    rw [stalkToFunctionField_germ] at hg
    have hs_ne : (s.1 : X.functionField) ≠ 0 := hg ▸ hne
    obtain ⟨_, hcond⟩ := s.property hs_ne
    -- Specialize the section condition at `x`.
    have hatx := hcond x
    simp only [locallyFinsuppWithin.coe_zero, Pi.zero_apply, locallyFinsuppWithin.coe_add,
      Pi.add_apply, restrict_eq_of_mem _ _ _ hxW,
      div_eq_ord_of_coheight_eq_one _ _ _ hx] at hatx
    -- Replace `s.1` with `f`.
    rw [hg] at hatx
    linarith
  · intro h
    rw [Set.mem_range]
    let W : X.Opens := ⟨U ∩ V, hU1.inter hV1⟩
    have hxW : x ∈ W := ⟨hU2, hV2⟩
    have hf_carrier : f ∈ Sheaf.carrier D W := by
      intro hne
      refine ⟨⟨⟨x, hxW⟩⟩, ?_⟩
      intro z
      by_cases hzW : z ∈ W
      · simp only [locallyFinsuppWithin.coe_zero, Pi.zero_apply, locallyFinsuppWithin.coe_add,
          Pi.add_apply, restrict_eq_of_mem _ _ _ hzW]
        by_cases hzx : z = x
        · subst hzx
          rw [div_eq_ord_of_coheight_eq_one _ _ _ hx]
          linarith [h o]
        · -- z ≠ x. We show both `(div f o) z = 0` and `D z = 0`.
          have hdiv_z : (div f o) z = 0 := by
            by_cases hzcoh : coheight z = 1
            · rw [div_eq_ord_of_coheight_eq_one _ _ _ hzcoh]
              by_contra hord
              -- z ∈ (div f o).support gives z ⤳ x via hU3
              have hz_supp : z ∈ (div f o).support := by
                simp only [Function.mem_support, ne_eq, div_eq_ord_of_coheight_eq_one _ _ _ hzcoh]
                exact hord
              have hspec : z ⤳ x := hU3 z ⟨hzW.1, hz_supp⟩
              -- z ⤳ x, with both codim 1 in an integral scheme, forces z = x.
              exact hzx (spec_eq z hzcoh hspec)
            · exact div_eq_zero_of_coheight_ne_one _ _ _ hzcoh
          have hD_z : D z = 0 := by
            by_contra hD'
            have hz_supp : z ∈ D.support := hD'
            have hspec : z ⤳ x := hV3 z ⟨hzW.2, hz_supp⟩
            -- z ⤳ x and z ≠ x. We need to handle non-codim-1 case
            by_cases hzcoh : coheight z = 1
            · exact hzx (spec_eq z hzcoh hspec)
            · simp_all
          rw [hdiv_z, hD_z]
          simp
      · simp [restrict_eq_zero_of_not_mem _ _ _ hzW]
    use TopCat.Presheaf.germ D.sheaf.val.presheaf W x hxW ⟨f, hf_carrier⟩
    exact stalkToFunctionField_germ D x W hxW ⟨f, hf_carrier⟩

/-
Our map should go O_X(D)_P → K(X) → K(X) → O_X, P -> k

That map K(X) → K(X) should be multiplication by ϖⁿ (where n is D p)

This gets us (using some glue) to Subring.map (algebraMap (X.presheaf.stalk x) X.functionField) ⊤,
and I guess we can use Subring.comap + some lemma about Subring.comap of a subring which is
contained in the range composed with the ressidue map to give us our result.
-/

/-
This follows from mathlib + some stuff developed above.
-/
lemma bibo {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (hD : D.support ⊆ {x | coheight x = 1})
    (x : X) (hx : coheight x = 1)
    (ϖ : X.presheaf.stalk x) (hϖ : Irreducible ϖ)
    : Submodule.map (Algebra.linearMap (X.presheaf.stalk x) X.functionField) ⊤ =
      Submodule.map ((LinearMap.mulLeft (X.presheaf.stalk x)
      ((algebraMap (X.presheaf.stalk x) X.functionField ϖ)^(D x))) ∘ₗ
      D.stalkToFunctionFieldLinearMap x) ⊤ := by

    sorry
#check Submodule.comap_map_eq_of_injective
#check Submodule.comap (Algebra.linearMap (X.presheaf.stalk x) X.functionField)

/-
This is an isomorphism really.
-/
def zingo {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (hD : D.support ⊆ {x | coheight x = 1})
    (x : X) (hx : coheight x = 1)
    (ϖ : X.presheaf.stalk x) (hϖ : Irreducible ϖ) :
    ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf x) ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x := sorry
/-
We then want to define our map O_X(D)_P ->(stalkToFunctionFieldLinearMap) K(X) ->(mulLeft) K(X)
->(comap germToFunctionField) O_X, P ->(residue) k
-/

#check Submodule.map ((LinearMap.mulLeft (X.presheaf.stalk x) (1 : X.functionField)) ∘ₗ (Algebra.linearMap (X.presheaf.stalk x) X.functionField)) ⊤








noncomputable
def genericStalkToFunctionField {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) :
    (TopCat.Presheaf.stalk D.sheaf.val.presheaf (genericPoint X)) ⟶ ((forget₂ CommRingCat RingCat ⋙
    forget₂ RingCat Ab).obj X.functionField) := by
  let c : Cocone <| ((inclusion (genericPoint ↥X)).op ⋙ D.sheaf.val.presheaf) := {
    pt := (forget₂ RingCat Ab).obj ((forget₂ CommRingCat RingCat).obj X.functionField)
    ι := {
      app U :=
        AddCommGrpCat.ofHom {
          toFun f := f.1
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl
        }
      naturality U V f := by
        apply AddCommGrpCat.hom_ext
        simp
        by_cases t : Nonempty (V.unop.1)
        · sorry
        · sorry
    }
  }
  apply colimit.desc _ c

noncomputable
def genericStalkAddEquivFunctionField {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) :
    ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf (genericPoint X)) ≃+ X.functionField := by
  apply AddEquiv.ofBijective D.genericStalkToFunctionField.hom
  constructor
  . sorry
  · sorry

noncomputable
def genericStalkToFunctionFieldModuleHom {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) :
    ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf (genericPoint X))
    ≃ₗ[X.functionField] X.functionField where
      __ := D.genericStalkAddEquivFunctionField
      map_add' a b := AddMonoidHom.map_add (AddCommGrpCat.Hom.hom D.genericStalkToFunctionField) a b
      map_smul' := sorry

/-
Compose Topcat.Presheaf.stalkSpecializes with genericStalkToFunctionFieldModuleHom

For this we will require that Topcat.Presheaf.stalkSpecializes can be lifted to a module
homomorphism
-/
noncomputable
def genericStalkToFunctionFieldModuleHom' {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (x : X) :
    ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf x)
    →ₗ[X.presheaf.stalk x] X.functionField := sorry

/-
Here we need to show that the set of elements with valuation ≤ D p form a submodule (because of
course they do)

Then we should show that these are all isomorphic because we have a map which multiplies by some
power of a uniformizer

This shouldn't rely on anything here, so we can do this and maybe get it merged independently of
this nonsense


Now, what's the argument that we get an isomorphism here? Well, to give a map out of a coproduct
is to give a map out of the components. So we take a neighbourhood around p which has no points in
the support of D except p and in which our function has no zeros or poles.

Maybe we should just be doing this isomorphism directly instead of going via these stalk maps and
so on. It occurs to me that a colimit
-/

lemma dskan {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]:
    Submodule.map (D.genericStalkToFunctionFieldModuleHom' x) ⊤ =
    sorry := sorry

/-
Next: Show that this is an iso (the proof should be that (f) + D ≥ 0 on any set where
(f) has no poles)

This gives us a map 𝒪ₓ(D)ₐ → K(X) for any a : X.

If a is codimension one, we want to argue that the range of this map is precisely the
valuation subring of 𝒪ₓ,ₐ in the function field.
-/
end AlgebraicCycle
