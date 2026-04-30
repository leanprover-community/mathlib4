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
TODO: Rename this

On a nonempty set `U`, `Γ(𝒪ₓ(D), U)` is closed scalar multiplication by elements of `Γ(X, U)`.
-/
def smul_mem' (D : AlgebraicCycle X ℤ) (U : X.Opens) [Nonempty U] (a : Γ(X, U))
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
      · simp only [restrict_eq_of_mem _ _ _ o, div_eq_ord_of_coheight_eq_one _ _ _ hz, Scheme.ord,
        Multiplicative.toAdd_le, WithZero.unzero_le_unzero]
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

@[simp]
lemma mapFunApplyNonempty (D : AlgebraicCycle X ℤ) {U V : X.Opens} (r : V ≤ U) [h : Nonempty V]
    (s : carrier D U) : (mapFun D r s).1 = s := by
  simp [mapFun, h]


instance algebra_restrict {U V : X.Opens} (k : V ≤ U) :
    Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map (homOfLE k).op).hom.toAlgebra

/--
TODO: Put in a more sensible file
-/
lemma _root_.Nonempty_le {U V : X.Opens} (k : V ≤ U) [Nonempty V] : Nonempty U := by
  rename_i hV
  obtain ⟨⟨a, b⟩⟩ := hV
  use a
  exact k b

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
        · apply Subtype.ext
          erw [coe_smul]
          simp only [op_unop, sheafCompose_obj_obj, Functor.comp_obj,
            CommRingCat.forgetToRingCat_obj, Functor.comp_map, CommRingCat.forgetToRingCat_map_hom,
            RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
            MonoidHom.coe_coe, ZeroHom.coe_mk]
          let : Algebra Γ(X, U.unop) Γ(X, V.unop) := (X.sheaf.obj.map r).hom.toAlgebra
          have : IsScalarTower Γ(X, U.unop) Γ(X, V.unop) X.functionField := by infer_instance
          change m • a = (algebraMap  Γ(X, U.unop) Γ(X, V.unop) m) • a.1
          exact algebra_compatible_smul (↑Γ(X, unop V)) m a.1
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
  dsimp [map]
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
    (ModuleCat.restrictScalars (RingCat.Hom.hom (X.ringCatSheaf.obj.map f))).map (map D g) ≫
    (ModuleCat.restrictScalarsComp' (RingCat.Hom.hom (X.ringCatSheaf.obj.map f))
    (RingCat.Hom.hom (X.ringCatSheaf.obj.map g))
    (RingCat.Hom.hom (X.ringCatSheaf.obj.map (f ≫ g)))
    (congrArg RingCat.Hom.hom (X.ringCatSheaf.obj.map_comp f g))).inv.app (obj D W) := by
  apply ModuleCat.hom_ext
  rw [@LinearMap.ext_iff]
  intro x
  dsimp [map]
  by_cases h : Nonempty W.unop
  · have hV : Nonempty V.unop := Nonempty_le <| leOfHom g.unop
    apply Subtype.ext
    simp only [mapFunApplyNonempty, op_unop, sheafCompose_obj_obj, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj, Functor.comp_map, CommRingCat.forgetToRingCat_map_hom]
    change x.1 = (mapFun D (map._proof_1 g) (mapFun D (map._proof_1 f) x))
    simp
  · exact Subsingleton.elim (h := instSubsingleTonOfEmpty h) _ _


open Classical in
noncomputable
def presheaf (D : AlgebraicCycle X ℤ) : PresheafOfModules X.ringCatSheaf.obj where
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
def connectedByCover {I : Type*} (𝒰 : I → X.Opens) :
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
    {i j : I} (h : connectedByCover 𝒰 i j)
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
    (hj : (𝒰 j).1.Nonempty) : connectedByCover 𝒰 i j := by
  by_contra hij
  let S : Set I := {k | connectedByCover 𝒰 i k}
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
def sheafOfModules {X : Scheme} [AlgebraicGeometry.IsIntegral X] [IsLocallyNoetherian X]
  [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) : X.Modules where
  val := AlgebraicCycle.Sheaf.presheaf D
  isSheaf := AlgebraicCycle.Sheaf.isSheaf D

end AlgebraicCycle
