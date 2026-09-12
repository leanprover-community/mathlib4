/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# Order of vanishing in a scheme

In this file we define the order of vanishing of an element of the function field of a locally
Noetherian integral scheme at a point of codimension `1`, and develop its basic API.
-/

@[expose] public section

open WithZero AlgebraicGeometry Order TopologicalSpace CategoryTheory

universe u

variable {X : Scheme.{u}}

namespace AlgebraicGeometry.Scheme

variable [IsIntegral X] [IsLocallyNoetherian X]

/--
Order of vanishing on a locally Noetherian integral scheme as a monoid with zero hom to `ℤᵐ⁰`.
-/
noncomputable
def ordHom (z : X) (hz : coheight z = 1) : X.functionField →*₀ ℤᵐ⁰ :=
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  Ring.ordFrac (X.presheaf.stalk z)

lemma ordHom_of_isUnit {U : X.Opens}
    [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) {x : X} (hx : coheight x = 1) (hx' : x ∈ U) :
    ordHom x hx (X.germToFunctionField U f) = 1 := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  rw [← algebraMap_germ_eq_germToFunctionField _ hx']
  exact Ring.ordFrac_of_isUnit (hf.map (X.presheaf.germ U x hx').hom)

/--
The order of vanishing of an element of the function field of a locally Noetherian integral scheme
at a point. This has a junk value of `0` if `f = 0` or if `coheight z ≠ 1`.
-/
@[no_expose]
noncomputable
def ord (f : X.functionField) (z : X) : ℤ :=
  if hz : coheight z = 1
  then Multiplicative.toAdd <| (X.ordHom z hz f).unzeroD 1
  else 0

lemma ord_eq_ordHom_of_coheight_eq_one {z : X} (hz : coheight z = 1) (f : X.functionField) :
    ord f z = Multiplicative.toAdd ((X.ordHom z hz f).unzeroD 1) := dite_eq_left hz

@[simp]
lemma ord_eq_zero_of_coheight_neq_one {z : X} (hz : coheight z ≠ 1) (f : X.functionField) :
    ord f z = 0 := dite_eq_right hz

@[simp]
lemma ord_zero : ord (0 : X.functionField) = 0 := by
  ext z
  by_cases h : coheight z = 1
  · simp [ord_eq_ordHom_of_coheight_eq_one h, unzeroD]
  · simp [h]

lemma ord_eq_unzero_ordHom {x : X} (hx : coheight x = 1) {f : X.functionField} (hf : f ≠ 0) :
    ord f x = (WithZero.unzero ((map_ne_zero (ordHom x hx)).mpr hf)).toAdd := by
  simp [ord, hx, unzeroD_eq_unzero ((map_ne_zero (ordHom x hx)).mpr hf)]

lemma ord_eq_iff {z : X} (hz : coheight z = 1) {f : X.functionField} (hf : f ≠ 0) {n : ℤ} :
    ord f z = n ↔ ordHom z hz f = Multiplicative.ofAdd n := by
  rw [ord_eq_unzero_ordHom hz hf]
  exact WithZero.toAdd_unzero_eq_iff _ _

@[simp]
lemma ord_mul {x : X} {f g : X.functionField}
    (hf : f ≠ 0) (hg : g ≠ 0) : ord (f * g) x = ord f x + ord g x := by
  by_cases! hx : coheight x ≠ 1
  · simp [hx]
  rw [ord_eq_iff hx <| (mul_ne_zero_iff_right hg).mpr hf]
  simp [hf, hg, ord_eq_ordHom_of_coheight_eq_one hx, unzeroD_eq_unzero]

@[simp]
lemma ord_one : ord (1 : X.functionField) = 0 := by
  ext z
  by_cases! hz : coheight z ≠ 1
  · simp [hz]
  · simp only [Pi.zero_apply]
    rw [ord_eq_iff hz one_ne_zero]
    simp

lemma ord_inv {z : X} {f : X.functionField} (hf : f ≠ 0) : ord f⁻¹ z = -ord f z := by
  have h := ord_mul (x := z) hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf] at h
  simp only [ord_one, Pi.zero_apply] at h
  omega

lemma ord_div {z : X} {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord (f / g) z = ord f z - ord g z := by
  rw [div_eq_mul_inv, ord_mul hf (inv_ne_zero hg), ord_inv hg]
  ring

lemma ord_pow {z : X} {f : X.functionField} (hf : f ≠ 0) (n : ℕ) :
    ord (f ^ n) z = n * ord f z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ord_mul (pow_ne_zero n hf) hf, ih]
    push_cast
    ring

lemma ord_zpow {z : X} {f : X.functionField} (hf : f ≠ 0) (n : ℤ) :
    ord (f ^ n) z = n * ord f z := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, ord_pow hf]
  | negSucc n =>
    rw [zpow_negSucc, ord_inv (pow_ne_zero _ hf), ord_pow hf, Int.negSucc_eq]
    push_cast
    ring

lemma ord_prod {ι : Type*} {z : X} (T : Finset ι) (F : ι → X.functionField)
    (hF : ∀ i ∈ T, F i ≠ 0) : ord (∏ i ∈ T, F i) z = ∑ i ∈ T, ord (F i) z := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    have hprod : (∏ i ∈ T, F i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hF i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert haT, Finset.sum_insert haT,
      ord_mul (hF a (Finset.mem_insert_self a T)) hprod,
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

lemma ord_of_isUnit {U : X.Opens} [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) {x : X}
    (hx' : x ∈ U) : ord (X.germToFunctionField U f) x = 0 := by
  by_cases! hx : coheight x ≠ 1
  · simp [hx]
  simp [map_ne_zero_iff, germToFunctionField_injective, IsUnit.ne_zero hf,
    ord_eq_iff hx, ordHom_of_isUnit hf hx hx']

lemma ord_le_ord_iff {x y : X} (hx : coheight x = 1) (hy : coheight y = 1) {f g : X.functionField}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    ord f x ≤ ord g y ↔ ordHom x hx f ≤ ordHom y hy g := by
  simp [ord_eq_unzero_ordHom hx hf, ord_eq_unzero_ordHom hy hg, Multiplicative.toAdd_le]

lemma le_ord_iff {x : X} (hx : coheight x = 1) {f : X.functionField}
    (hf : f ≠ 0) {n : ℤ} :
    n ≤ ord f x ↔ Multiplicative.ofAdd n ≤ ordHom x hx f := by
  rw [ord_eq_unzero_ordHom hx hf]
  nth_rw 1 [← toAdd_ofAdd n]
  rw [Multiplicative.toAdd_le, le_unzero_iff]

lemma ord_le_smul {x : X} {U : X.Opens} [Nonempty U] (hxU : x ∈ U)
    {a : Γ(X, U)} (ha : a ≠ 0) (f : X.functionField) : ord f x ≤ ord (a • f) x := by
  by_cases! hx : coheight x ≠ 1
  · simp [hx]
  by_cases hf : f = 0
  · simp [hf]
  have : a • f ≠ 0 := by simp [ha, Algebra.smul_def, hf, germToFunctionField_injective,
    RingHom.algebraMap_toAlgebra, map_ne_zero_iff]
  rw [ord_le_ord_iff hx hx hf this]
  algebraize [(X.presheaf.germ U x hxU).hom]
  have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have : IsScalarTower ↑Γ(X, U) ↑(X.presheaf.stalk x) ↑X.functionField :=
    functionField_isScalarTower X U ⟨x, hxU⟩
  simp [ordHom, Ring.ordFrac_le_smul, RingHom.algebraMap_toAlgebra, map_ne_zero_iff,
    germ_injective_of_isIntegral, ha]

section Stalk

variable {x : X}

omit [IsLocallyNoetherian X] in
lemma algebraMap_functionField_ne_zero {a : X.presheaf.stalk x} (ha : a ≠ 0) :
    algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 :=
  (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr ha

lemma ord_algebraMap_nonneg {a : X.presheaf.stalk x} (ha : a ≠ 0) :
    0 ≤ ord (algebraMap (X.presheaf.stalk x) X.functionField a) x := by
  by_cases! hx : coheight x ≠ 1
  · simp [hx]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  rw [le_ord_iff hx (algebraMap_functionField_ne_zero ha), ofAdd_zero, WithZero.coe_one]
  exact Ring.ordFrac_ge_one_of_ne_zero ha

lemma ord_algebraMap_eq_zero_of_isUnit {a : X.presheaf.stalk x}
    (ha : IsUnit a) : ord (algebraMap (X.presheaf.stalk x) X.functionField a) x = 0 := by
  by_cases! hx : coheight x ≠ 1
  · simp [hx]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  rw [ord_eq_iff hx (algebraMap_functionField_ne_zero ha.ne_zero), ofAdd_zero]
  exact Ring.ordFrac_of_isUnit ha

end Stalk

section Chart

variable {U : X.Opens} [Nonempty U]

omit [IsLocallyNoetherian X] in
lemma algebraMap_section_stalk_ne_zero (w : U) {r : Γ(X, U)}
    (hr : algebraMap Γ(X, U) X.functionField r ≠ 0) :
    algebraMap Γ(X, U) (X.presheaf.stalk (w : X)) r ≠ 0 := fun h0 =>
  hr (by
    rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk (w : X)) X.functionField, h0,
      map_zero])

lemma ord_algebraMap_section_nonneg (w : U) {r : Γ(X, U)}
    (hr : algebraMap Γ(X, U) X.functionField r ≠ 0) :
    0 ≤ ord (algebraMap Γ(X, U) X.functionField r) (w : X) := by
  rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk (w : X)) X.functionField]
  exact ord_algebraMap_nonneg (algebraMap_section_stalk_ne_zero w hr)

end Chart

end AlgebraicGeometry.Scheme
