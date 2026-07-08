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

Note that we can extend the construction here to schemes which are not necessarily irreducible with
some extra bookkeeping. That said, in my opinion the most sensible way to do this goes via the
construction on integral schemes, and in any case the construction for integral schemes comes up the
most in applications, hence our decision to formalize the version for integral schemes.

Also note: the construction given here is now somewhat out of date, though a lot of the lemmas are
reused. In the file `SkyscraperViaSubmodule.lean` we develop the same sheaf via the skyscraper sheaf
API. I think this results in a cleaner and more reusable design, but this is a bit of a WIP.

-/
@[expose] public section

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

/--
On a scheme, a specialization between two points of coheight one is an equality: a strict
specialization would raise the coheight.
-/
lemma _root_.Specializes.eq_of_coheight_eq_one {X : Scheme.{u}} {z x : X}
    (h : z ⤳ x) (hz : coheight z = 1) (hx : coheight x = 1) : z = x := by
  have hxz : x ≤ z := h
  by_cases hzx : z ≤ x
  · exact (Specializes.antisymm h (hzx : x ⤳ z)).eq
  · have hbound := Order.coheight_add_one_le (lt_of_le_not_ge hxz hzx)
    rw [hz, hx] at hbound
    norm_num at hbound

namespace AlgebraicGeometry.AlgebraicCycle
namespace Sheaf

/--
The underlying set of `Γ(𝒪ₓ(D), U)`, defined to be:
`Γ(𝒪ₓ(D), U) := {s : k(X) | s ≠ 0 → Nonempty U ∧ s|_U + D|_U ≥ 0}`.
-/
def carrier (D : AlgebraicCycle X ℤ) (U : X.Opens) : Set X.functionField :=
    {s : (X.functionField) | (h : s ≠ 0) → Nonempty U ∧ (div s).restrict U + D.restrict U ≥ 0}

/--
Membership in `Γ(𝒪ₓ(D), U)`, pointwise: a nonzero rational function `f` is a section of
`𝒪ₓ(D)` over (nonempty) `U` iff `0 ≤ ord f z + D z` for every `z ∈ U`.
-/
lemma mem_carrier_iff {D : AlgebraicCycle X ℤ} {U : X.Opens} {f : X.functionField} :
    f ∈ carrier D U ↔ ((h : f ≠ 0) → Nonempty U ∧ ∀ z ∈ U, 0 ≤ X.ord f z + D z) := by
  simp only [carrier, ge_iff_le, Set.mem_setOf_eq]
  refine forall_congr' fun hf => and_congr_right fun _ => ⟨fun h z hz => ?_, fun h => ?_⟩
  · have h2 := h z
    simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply,
      Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
      AlgebraicGeometry.AlgebraicCycle.restrict_apply, div_eq_ord] at h2
    split_ifs at h2 with hzU
    · exact h2
    · exact absurd hz hzU
  · intro z
    simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply,
      Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
      AlgebraicGeometry.AlgebraicCycle.restrict_apply, div_eq_ord]
    split_ifs with hz
    · exact h z hz
    · exact le_rfl

open Classical in
/--
For a nonzero section `f` of `𝒪ₓ(D)` over `U ∋ p`, being a section of `𝒪ₓ(D - p)` is the
single additional order bound `1 ≤ D p + ord f p` at `p`: away from `p` the section
conditions for `D - single p 1` and `D` agree.
-/
lemma mem_carrier_sub_single_iff {D : AlgebraicCycle X ℤ} {U : X.Opens} {p : X} (hp' : p ∈ U)
    {f : X.functionField} (hf : f ≠ 0) (hfD : f ∈ carrier D U) :
    f ∈ carrier (D - single p 1) U ↔ 1 ≤ D p + X.ord f p := by
  rw [mem_carrier_iff]
  constructor
  · intro h
    have h2 := (h hf).2 p hp'
    simp only [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply,
      Function.locallyFinsuppWithin.single_apply, if_true] at h2
    omega
  · intro hle hne
    refine ⟨⟨⟨p, hp'⟩⟩, fun z hz => ?_⟩
    have h2 := (mem_carrier_iff.mp hfD hf).2 z hz
    simp only [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply,
      Function.locallyFinsuppWithin.single_apply]
    rcases eq_or_ne z p with rfl | hzp
    · simp only [if_true]
      omega
    · simp only [if_neg hzp, sub_zero]
      omega

/--
The sum of two sections in `Γ(𝒪ₓ(D), U)` is another section of `Γ(𝒪ₓ(D), U)` on a scheme which is
regular in codimension one. Note that we are using regulariy in codimension one in a fairly
essential way here. One should note that this is the key point where regularity in codimension one
is used in the construction of `𝒪ₓ(D)`.
-/
lemma add_mem' [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (U : X.Opens)
    {a b : ↑X.functionField}
    (ha : a ∈ carrier D U) (hb : b ∈ carrier D U) : a + b ∈ carrier D U := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simpa using hb
  rcases eq_or_ne b 0 with rfl | hb0
  · simpa using ha
  refine mem_carrier_iff.mpr fun h => ⟨(mem_carrier_iff.mp ha ha0).1, fun z hz => ?_⟩
  have hA := (mem_carrier_iff.mp ha ha0).2 z hz
  have hB := (mem_carrier_iff.mp hb hb0).2 z hz
  by_cases hZ : coheight z = 1
  · have := krullDimLE_of_coheight hZ
    haveI : IsDiscreteValuationRing ↑(X.presheaf.stalk z) :=
      IsRegularInCodimensionOne.stalk_dvr z hZ
    have := X.ord_add hZ h
    omega
  · have h1 : X.ord (a + b) z = 0 := ord_eq_zero_of_coheight_neq_one hZ _
    have h2 : X.ord a z = 0 := ord_eq_zero_of_coheight_neq_one hZ _
    omega

/--
Zero is an element of `Γ(𝒪ₓ(D), U)` by definition
-/
lemma zero_mem' (D : AlgebraicCycle X ℤ) (U : X.Opens) : 0 ∈ carrier D U := by
  simp [carrier]

/--
`Γ(𝒪ₓ(D), U)` is closed under negatives.
-/
lemma neg_mem' (D : AlgebraicCycle X ℤ) (U : X.Opens) {f : X.functionField} (hf : f ∈ carrier D U) :
    (- f) ∈ carrier D U := by simp_all [carrier]

/--
On a nonempty set `U`, `Γ(𝒪ₓ(D), U)` is closed scalar multiplication by elements of `Γ(X, U)`.
-/
lemma smul_mem_nonempty (D : AlgebraicCycle X ℤ) (U : X.Opens) [Nonempty U] (a : Γ(X, U))
    {f : X.functionField} (hf : f ∈ carrier D U) : a • f ∈ carrier D U := by
  refine mem_carrier_iff.mpr fun h => ⟨‹_›, fun z hz => ?_⟩
  have hf0 : f ≠ 0 := fun h0 => h (by simp [h0])
  have hF := (mem_carrier_iff.mp hf hf0).2 z hz
  by_cases hZ : coheight z = 1
  · have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk z) := krullDimLE_of_coheight hZ
    have := ord_le_smul hZ hz (left_ne_zero_of_smul h) f
    omega
  · have h1 : X.ord (a • f) z = 0 := ord_eq_zero_of_coheight_neq_one hZ _
    have h2 : X.ord f z = 0 := ord_eq_zero_of_coheight_neq_one hZ _
    omega

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
noncomputable def smulVal (a : Γ(X, U)) (v : X.functionField) : X.functionField := by
  classical
  exact if h : Nonempty U then haveI := h; a • v else v

omit [IsRegularInCodimensionOne X] in
lemma smulVal_mem_carrier (a : Γ(X, U)) (f : carrier D U) :
    smulVal a f.val ∈ carrier D U := by
  simp only [smulVal]
  split_ifs with hU
  · exact smul_mem_nonempty D U a f.prop
  · exact f.prop

noncomputable instance : SMul Γ(X, U) (carrier D U) where
  smul a f := ⟨smulVal a f.val, smulVal_mem_carrier a f⟩

omit [IsRegularInCodimensionOne X] in
lemma smul_eq_smulVal (a : Γ(X, U)) (f : carrier D U) :
    HSMul.hSMul a f = smulVal a f.val := rfl

omit [IsRegularInCodimensionOne X] in
@[simp] lemma coe_smul [hU : Nonempty U] (a : Γ(X, U)) (f : carrier D U) :
    (↑(a • f) : X.functionField) = a • (f : X.functionField) := by
  simp [smul_eq_smulVal, smulVal, hU]

omit [IsRegularInCodimensionOne X] in
lemma instSubsingleTonOfEmpty (h : ¬ Nonempty U) : Subsingleton (carrier D U) := by
  simp [carrier, h]

instance instModuleCarrier : Module Γ(X, U) (carrier D U) where
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
Sections of `𝒪ₓ(D)` restrict: a section over `U` is a section over any smaller nonempty `V`.
-/
lemma mem_carrier_of_le (D : AlgebraicCycle X ℤ) {U V : X.Opens}
    (r : V ≤ U) [hV : Nonempty V] {f : X.functionField} (hf : f ∈ carrier D U) :
    f ∈ carrier D V :=
  mem_carrier_iff.mpr fun h => ⟨hV, fun z hz => (mem_carrier_iff.mp hf h).2 z (r hz)⟩

open Classical in
/--
The function underlying the action of `𝒪ₓ(D)` on morphisms.
-/
noncomputable
def mapFun (D : AlgebraicCycle X ℤ) {U V : X.Opens} (r : V ≤ U) : carrier D U → carrier D V :=
  fun ⟨f, hf⟩ ↦ if hV : Nonempty V then ⟨f, mem_carrier_of_le D r hf⟩ else ⟨0, by simp [carrier]⟩

omit [IsRegularInCodimensionOne X] in
@[simp]
lemma mapFunApplyNonempty (D : AlgebraicCycle X ℤ) {U V : X.Opens} (r : V ≤ U) [h : Nonempty V]
    (s : carrier D U) : (mapFun D r s).1 = s := by simp [mapFun, h]

@[reducible]
def algebra_restrict {U V : X.Opens} (k : V ≤ U) :
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

lemma mapFun_add (D : AlgebraicCycle X ℤ) {U V : X.Opens} (r : V ≤ U) (a b : carrier D U) :
    mapFun D r (a + b) = mapFun D r a + mapFun D r b := by
  by_cases hV : Nonempty V
  · exact Subtype.ext (by simp)
  · exact Subsingleton.elim (h := instSubsingleTonOfEmpty hV) _ _

omit [IsRegularInCodimensionOne X] in
@[simp]
lemma mapFun_id (D : AlgebraicCycle X ℤ) {U : X.Opens} (s : carrier D U) :
    mapFun D le_rfl s = s := by
  by_cases hU : Nonempty U
  · exact Subtype.ext (by simp)
  · exact Subsingleton.elim (h := instSubsingleTonOfEmpty hU) _ _

omit [IsRegularInCodimensionOne X] in
@[simp]
lemma mapFun_comp (D : AlgebraicCycle X ℤ) {U V W : X.Opens} (rVU : V ≤ U) (rWV : W ≤ V)
    (s : carrier D U) : mapFun D rWV (mapFun D rVU s) = mapFun D (rWV.trans rVU) s := by
  by_cases hW : Nonempty W
  · haveI : Nonempty V := hW.map fun w => ⟨w.1, rWV w.2⟩
    exact Subtype.ext (by simp)
  · exact Subsingleton.elim (h := instSubsingleTonOfEmpty hW) _ _

/-- The `Ab`-valued presheaf underlying `𝒪ₓ(D)`: sections restrict via `mapFun`. -/
noncomputable
def abPresheaf (D : AlgebraicCycle X ℤ) : TopCat.Presheaf Ab ↑X.toPresheafedSpace where
  obj U := AddCommGrpCat.of (carrier D (unop U))
  map r := AddCommGrpCat.ofHom (AddMonoidHom.mk' (mapFun D r.unop.le) (mapFun_add D _))
  map_id U := by
    ext s
    exact congrArg Subtype.val (mapFun_id D s)
  map_comp f g := by
    ext s
    exact congrArg Subtype.val (mapFun_comp D f.unop.le g.unop.le s).symm

@[simp]
lemma abPresheaf_map_apply (D : AlgebraicCycle X ℤ) {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (r : U ⟶ V) (s : ↑((abPresheaf D).obj U)) :
    (abPresheaf D).map r s = mapFun D r.unop.le s := rfl

/-- Each value of `abPresheaf` is a module over the corresponding sections of the structure
sheaf, via `instModuleCarrier`. -/
noncomputable instance (D : AlgebraicCycle X ℤ) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
    Module ↑(X.ringCatSheaf.obj.obj U) ↑((abPresheaf D).obj U) :=
  instModuleCarrier (U := unop U) (D := D)

omit [IsRegularInCodimensionOne X] in
/-- Restriction of sections of `𝒪ₓ(D)` is semilinear with respect to restriction in the
structure sheaf. -/
lemma mapFun_smul (D : AlgebraicCycle X ℤ) {U V : X.Opens} (r : V ≤ U)
    (a : Γ(X, U)) (m : carrier D U) :
    mapFun D r (a • m) = X.presheaf.map (homOfLE r).op a • mapFun D r m := by
  by_cases hV : Nonempty V
  · haveI hU : Nonempty U := hV.map fun x => ⟨x.1, r x.2⟩
    letI := algebra_restrict r
    apply Subtype.ext
    simp only [mapFunApplyNonempty, coe_smul]
    exact algebra_compatible_smul Γ(X, V) a m.1
  · exact Subsingleton.elim (h := instSubsingleTonOfEmpty hV) _ _

noncomputable
def _root_.AlgebraicGeometry.AlgebraicCycle.presheaf (D : AlgebraicCycle X ℤ) :
    PresheafOfModules X.ringCatSheaf.obj :=
  PresheafOfModules.ofPresheaf (abPresheaf D) fun _ _ f a m => mapFun_smul D f.unop.le a m

lemma presheaf.obj_eq (D : AlgebraicCycle X ℤ) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
    (presheaf D).obj U = obj D U := rfl

lemma presheaf_presheaf (D : AlgebraicCycle X ℤ) :
    (presheaf D).presheaf = abPresheaf D := rfl

/--
If sections `s : Γ(𝒪ₓ(D), U)` and `s' : Γ(𝒪ₓ(D), V)` are equal on `U ∩ V` and `U ∩ V` is nonempty,
then `s` and `s'` have the same underlying rational function.
-/
lemma sections_equal_of_nonempty_intersection {D : AlgebraicCycle X ℤ} {I : Type*}
    {𝒰 : I → X.Opens} {i j : I} (h : Nonempty (𝒰 i ⊓ 𝒰 j : X.Opens))
    (s : (i : I) → ToType ((presheaf D).presheaf.obj (op (𝒰 i))))
    (hs : TopCat.Presheaf.IsCompatible (presheaf D).presheaf 𝒰 s) : (s i).1 = (s j).1 := by
  haveI : Nonempty ↥(𝒰 i ⊓ 𝒰 j) := h
  have hs' : mapFun D inf_le_left (s i) = mapFun D inf_le_right (s j) := hs i j
  simpa using congrArg Subtype.val hs'

/--
Compatible sections over the members of a cover linked by a chain of pairwise-intersecting
opens have the same underlying rational function.
-/
lemma sections_equal_of_transGen {D : AlgebraicCycle X ℤ} {I : Type*} {𝒰 : I → X.Opens}
    {i j : I} (h : Relation.TransGen (fun a b => ((𝒰 a : Set X) ∩ 𝒰 b).Nonempty) i j)
    (s : (i : I) → ToType ((presheaf D).presheaf.obj (op (𝒰 i))))
    (hs : TopCat.Presheaf.IsCompatible (presheaf D).presheaf 𝒰 s) : (s i).1 = (s j).1 := by
  induction h with
  | single h => exact sections_equal_of_nonempty_intersection (Set.nonempty_coe_sort.mpr h) s hs
  | tail _ step ih =>
    exact ih.trans
      (sections_equal_of_nonempty_intersection (Set.nonempty_coe_sort.mpr step) s hs)

open TopologicalSpace

open Presheaf
/--
`𝒪ₓ(D)` is a sheaf
-/
lemma isSheaf (D : AlgebraicCycle X ℤ) :
    TopCat.Presheaf.IsSheaf (presheaf D).presheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluingNontrivial]
  on_goal 2 =>
    -- Over `⊥` the only section is `0`.
    haveI : Subsingleton (ToType ((presheaf D).presheaf.obj (op ⊥))) :=
      instSubsingleTonOfEmpty (D := D) (U := (⊥ : X.Opens)) (by simp)
    exact uniqueOfSubsingleton (0 : carrier D (⊥ : X.Opens))
  intro I hI 𝒰 h𝒰 s hs
  obtain ⟨i⟩ := hI
  have : Nonempty (iSup 𝒰 : TopologicalSpace.Opens X) := by aesop
  -- All compatible sections share one underlying rational function: `X` is irreducible, so the
  -- union of the cover is (pre)connected and any two nonempty members are linked by a chain of
  -- pairwise-intersecting opens.
  have h_eq (j : I) : (s i).1 = (s j).1 := by
    refine sections_equal_of_transGen (IsPreconnected.transGen_of_iUnion ?_ (fun k => (𝒰 k).2)
      i j (Set.nonempty_coe_sort.mp (h𝒰 i)) (Set.nonempty_coe_sort.mp (h𝒰 j))) s hs
    have := irreducibleSpace_of_isIntegral ↑(iSup 𝒰)
    simpa [Opens.coe_iSup] using
      (isIrreducible_iff_irreducibleSpace.mpr this).isConnected.isPreconnected
  -- The common function is a section over the union: the bound at `z ∈ iSup 𝒰` is the bound for
  -- the section over any member `𝒰 j` containing `z`.
  let sec : carrier D (iSup 𝒰) :=
    ⟨(s i).1, mem_carrier_iff.mpr fun hf => by
      obtain ⟨x⟩ := h𝒰 i
      refine ⟨⟨⟨x.1, Opens.mem_iSup.mpr ⟨i, x.2⟩⟩⟩, fun z hz => ?_⟩
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hz
      rw [h_eq j]
      exact (mem_carrier_iff.mp (s j).2 (h_eq j ▸ hf)).2 z hj⟩
  refine ⟨sec, fun j ↦ ?_, fun s' h' ↦ ?_⟩
  · haveI : Nonempty ↑(𝒰 j) := h𝒰 j
    exact Subtype.ext ((mapFunApplyNonempty D (le_iSup 𝒰 j) sec).trans (h_eq j))
  · haveI : Nonempty ↑(𝒰 i) := h𝒰 i
    exact Subtype.ext ((mapFunApplyNonempty D (le_iSup 𝒰 i) s').symm.trans
      (congrArg Subtype.val (h' i)))

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

noncomputable
instance (D : AlgebraicCycle X ℤ) (x : X)
  [IsRegularInCodimensionOne X] :
  Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier D.sheaf.val x

open CategoryTheory
open Functor
open Limits
open TopologicalSpace OpenNhds

noncomputable
def stalkCocone
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
      have : Nonempty ((inclusion x).op.obj V).unop := ⟨⟨x, V.unop.2⟩⟩
      apply AddCommGrpCat.hom_ext
      ext s
      exact Sheaf.mapFunApplyNonempty D _ s
  }

noncomputable
def stalkToFunctionField
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (x : X) :
    (TopCat.Presheaf.stalk D.sheaf.val.presheaf x) ⟶ ((forget₂ CommRingCat RingCat ⋙
    forget₂ RingCat Ab).obj X.functionField) :=
  colimit.desc _ (D.stalkCocone x)

@[simp]
lemma stalkToFunctionField_germ
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (x : X) (U : X.Opens) (hxU : x ∈ U)
    (s : Sheaf.carrier D U) :
    D.stalkToFunctionField x (TopCat.Presheaf.germ D.sheaf.val.presheaf U x hxU s) = s.1 :=
  ConcreteCategory.congr_hom (colimit.ι_desc (D.stalkCocone x) (op ⟨U, hxU⟩)) s

lemma stalkToFunctionField_injective
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (x : X) :
    Function.Injective (D.stalkToFunctionField x) := by
  intro a b hab
  obtain ⟨U, hxU, sa, rfl⟩ := TopCat.Presheaf.exists_germ_eq D.sheaf.val.presheaf a
  obtain ⟨V, hxV, sb, rfl⟩ := TopCat.Presheaf.exists_germ_eq D.sheaf.val.presheaf b
  rw [stalkToFunctionField_germ, stalkToFunctionField_germ] at hab
  refine TopCat.Presheaf.germ_ext (F := D.sheaf.val.presheaf) (U ⊓ V) ⟨hxU, hxV⟩
    (homOfLE inf_le_left) (homOfLE inf_le_right) ?_
  have : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x, ⟨hxU, hxV⟩⟩⟩
  apply Subtype.ext
  exact (Sheaf.mapFunApplyNonempty D inf_le_left sa).trans
    (hab.trans (Sheaf.mapFunApplyNonempty D inf_le_right sb).symm)

noncomputable
def stalkToFunctionFieldLinearMap
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (x : X) :
    ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf x) →ₗ[X.presheaf.stalk x] X.functionField where
  __ := (D.stalkToFunctionField x).hom
  map_smul' r a := by
    -- Get representatives for `a` (in the module stalk) and `r` (in the ring stalk).
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq D.sheaf.val.presheaf a
    obtain ⟨V, hxV, r', rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
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

/-- The underlying function of `stalkToFunctionFieldLinearMap` is `stalkToFunctionField`. -/
lemma coe_stalkToFunctionFieldLinearMap
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (x : X) :
    ⇑(D.stalkToFunctionFieldLinearMap x) = ⇑(D.stalkToFunctionField x).hom := rfl

/--
The range of the map from the stalk of O_X(D) at a codimension 1 point `x` is the set of all
rational functions `f` whose order of vanishing at P is at least `- D x`.

TODO: Write a more general lemma saying that a point `x` with arbirary codimension is the set of
rational functions which vanish to order at least `-D p` for all codimension 1 `p` specializing to
`x`.
-/
lemma range_stalkToFunctionField
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (hD : D.support ⊆ {x | coheight x = 1})
    (x : X) :
    Set.range (D.stalkToFunctionField x).hom =
      {f : X.functionField | f ≠ 0 → ∀ z, coheight z = 1 → z ⤳ x → - D z ≤ X.ord f z} := by
  ext f
  by_cases o : f = 0
  · subst o
    exact iff_of_true ⟨0, map_zero _⟩ fun h => absurd rfl h
  obtain ⟨U, hU1, hU2, hU3⟩ := Function.locallyFinsupp.exists_nhd_mem_support_implies_specializes
      (div f) x
  obtain ⟨V, hV1, hV2, hV3⟩ := Function.locallyFinsupp.exists_nhd_mem_support_implies_specializes
      D x
  constructor
  · rintro ⟨g, hg⟩ hne z hz hzx
    obtain ⟨W, hxW, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq D.sheaf.val.presheaf g
    -- The image of `germ ... s` under `stalkToFunctionField` is `s.1`, hence `s.1 = f`.
    rw [stalkToFunctionField_germ] at hg
    -- A point specializing to `x` lies in every open around `x`; use the section condition there.
    have hatz := (Sheaf.mem_carrier_iff.mp s.property (hg ▸ hne)).2 z (hzx.mem_open W.2 hxW)
    rw [hg] at hatz
    linarith
  · intro h
    rw [Set.mem_range]
    let W : X.Opens := ⟨U ∩ V, hU1.inter hV1⟩
    have hxW : x ∈ W := ⟨hU2, hV2⟩
    have hf_carrier : f ∈ Sheaf.carrier D W := Sheaf.mem_carrier_iff.mpr fun hne =>
      ⟨⟨⟨x, hxW⟩⟩, fun z hzW => by
        -- If either `ord f z` or `D z` is nonzero, then `z` is a codimension-one point of the
        -- support of `div f` or of `D` inside `W`, so it specializes to `x` and the hypothesis
        -- applies; otherwise the bound is trivial.
        rcases eq_or_ne (X.ord f z) 0 with hf0 | hf0
        · rcases eq_or_ne (D z) 0 with hD0 | hD0
          · omega
          · have := h o z (hD hD0) (hV3 z ⟨hzW.2, hD0⟩)
            omega
        · have hzcoh : coheight z = 1 := by
            by_contra hzc
            exact hf0 (ord_eq_zero_of_coheight_neq_one hzc f)
          have hsupp : z ∈ (div f).support := by
            simp only [Function.mem_support, ne_eq, div_eq_ord]
            exact hf0
          have := h o z hzcoh (hU3 z ⟨hzW.1, hsupp⟩)
          omega⟩
    exact ⟨TopCat.Presheaf.germ D.sheaf.val.presheaf W x hxW ⟨f, hf_carrier⟩,
      stalkToFunctionField_germ D x W hxW ⟨f, hf_carrier⟩⟩

/--
At a codimension-one point `x`, the only codimension-one point specializing to `x` is `x`
itself, so the stalk of `𝒪ₓ(D)` at `x` is the set of rational functions of order at least
`- D x` at `x`.
-/
lemma range_stalkToFunctionField_of_coheight_eq_one
    [IsRegularInCodimensionOne X] (D : AlgebraicCycle X ℤ) (hD : D.support ⊆ {x | coheight x = 1})
    (x : X) (hx : coheight x = 1) :
    Set.range (D.stalkToFunctionField x).hom =
      {f : X.functionField | f ≠ 0 → - D x ≤ X.ord f x} := by
  rw [range_stalkToFunctionField D hD x]
  ext f
  simp only [Set.mem_setOf_eq]
  refine forall_congr' fun hne => ⟨fun h => h x hx specializes_rfl, fun h z hz hzx => ?_⟩
  obtain rfl := hzx.eq_of_coheight_eq_one hz hx
  exact h

omit [IsLocallyNoetherian X] in
/--
Nonzero elements of the local ring at a point map to nonzero rational functions.
-/
lemma algebraMap_functionField_ne_zero {x : X}
    {a : ↑(X.presheaf.stalk x)} (ha : a ≠ 0) :
    algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 :=
  (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr ha

/--
The order of vanishing of an integer power of a uniformizer at `x` is the exponent.
-/
lemma ord_zpow_algebraMap_irreducible [IsRegularInCodimensionOne X]
    {x : X} (hx : coheight x = 1) {ϖ : X.presheaf.stalk x} (hϖ : Irreducible ϖ) (n : ℤ) :
    X.ord ((algebraMap (X.presheaf.stalk x) X.functionField ϖ) ^ n) x = n := by
  haveI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    IsRegularInCodimensionOne.stalk_dvr x hx
  have h1 : ordHom x hx (algebraMap (X.presheaf.stalk x) X.functionField ϖ) = WithZero.exp 1 :=
    Ring.ordFrac_irreducible hϖ
  rw [ord_eq_iff hx (zpow_ne_zero n (algebraMap_functionField_ne_zero hϖ.ne_zero)),
    map_zpow₀, h1, ← WithZero.exp_zsmul, smul_eq_mul, mul_one, WithZero.exp_eq_coe_ofAdd]

/--
Rational functions coming from the local ring at `x` have nonnegative order of vanishing.
-/
lemma ord_algebraMap_nonneg [IsRegularInCodimensionOne X] {x : X} (hx : coheight x = 1)
    {a : ↑(X.presheaf.stalk x)} (ha : a ≠ 0) :
    0 ≤ X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x := by
  haveI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    IsRegularInCodimensionOne.stalk_dvr x hx
  rw [le_ord_iff hx (algebraMap_functionField_ne_zero ha), ofAdd_zero, WithZero.coe_one]
  exact Ring.ordFrac_ge_one_of_ne_zero ha

/--
A nonzero element of the local ring at a codimension one point `x` lies in the maximal ideal
iff the corresponding rational function vanishes at `x` to order at least one.
-/
lemma mem_maximalIdeal_iff_one_le_ord [IsRegularInCodimensionOne X] {x : X}
    (hx : coheight x = 1) {a : ↑(X.presheaf.stalk x)} (ha : a ≠ 0) :
    a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
      1 ≤ X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x := by
  haveI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    IsRegularInCodimensionOne.stalk_dvr x hx
  have hnn := ord_algebraMap_nonneg hx ha
  have hiff : IsUnit a ↔
      X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x = 0 := by
    rw [ord_eq_iff hx (algebraMap_functionField_ne_zero ha), ofAdd_zero, WithZero.coe_one]
    exact Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing (K := X.functionField)
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hiff]
  omega

/--
The image of the local ring at a codimension-one point `x` in the function field consists
exactly of the rational functions of nonnegative order of vanishing at `x`.
-/
lemma mem_range_algebraMap_iff_ord_nonneg [IsRegularInCodimensionOne X] {x : X}
    (hx : coheight x = 1) (z : X.functionField) :
    (∃ a, algebraMap (X.presheaf.stalk x) X.functionField a = z) ↔ (z ≠ 0 → 0 ≤ X.ord z x) := by
  haveI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    IsRegularInCodimensionOne.stalk_dvr x hx
  constructor
  · rintro ⟨a, rfl⟩ hz
    exact ord_algebraMap_nonneg hx fun h => hz (by simp [h])
  · intro h
    rcases eq_or_ne z 0 with rfl | hz
    · exact ⟨0, map_zero _⟩
    refine IsDiscreteValuationRing.exists_lift_of_le_one ?_
    have h1 : (1 : WithZero (Multiplicative ℤ)) ≤ Ring.ordFrac (X.presheaf.stalk x) z := by
      have h0 := (le_ord_iff hx hz (n := 0)).mp (h hz)
      rwa [ofAdd_zero, WithZero.coe_one] at h0
    rw [Ring.ordFrac_eq_valuation_inv] at h1
    exact (one_le_inv₀ (WithZero.pos_iff_ne_zero.mpr
      ((Valuation.ne_zero_iff _).mpr hz))).mp h1

end AlgebraicGeometry.AlgebraicCycle
