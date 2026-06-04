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
Noetherian integral scheme at a point of codimension `1`.
-/

@[expose] public section

open WithZero AlgebraicGeometry Order TopologicalSpace CategoryTheory

universe u

variable {X : Scheme.{u}}

namespace AlgebraicGeometry.Scheme

variable [IsIntegral X] [IsLocallyNoetherian X]

/--
Order of vanishing on a locally Noetherian integral scheme as a monoid with zero hom to `ℤᵐ⁰`
-/
noncomputable
def ordHom (z : X) (hz : coheight z = 1) : X.functionField →*₀ ℤᵐ⁰ :=
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight hz
  Ring.ordFrac (X.presheaf.stalk z)

lemma ordHom_ne_zero {Z : X} (hZ : coheight Z = 1) {f : X.functionField} (hf : f ≠ 0) :
    ordHom Z hZ f ≠ 0 := (map_ne_zero _).mpr hf

lemma ordHom_of_isUnit {U : X.Opens}
    [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) {x : X} (hx : coheight x = 1) (hx' : x ∈ U) :
    ordHom x hx (X.germToFunctionField U f) = 1 := by
  have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk x) := krullDimLE_of_coheight hx
  rw [← algebraMap_germ_eq_germToFunctionField hx']
  exact Ring.ordFrac_of_isUnit (hf.map (X.presheaf.germ U x hx').hom)

/--
The order of vanishing of an element of the function field of a locally Noetherian integral scheme
at a point. This has a junk value of `0` if `f = 0` or if `coheight z ≠ 1`.
-/
noncomputable
def ord (z : X) (f : X.functionField) : ℤ :=
  if hz : coheight z = 1
  then Multiplicative.toAdd <| WithZero.recZeroCoe 1 id <| X.ordHom z hz f
  else 0

lemma ord_eq_ordHom_of_coheight_eq_one {z : X} (hz : coheight z = 1) (f : X.functionField) :
    ord z f = Multiplicative.toAdd (WithZero.recZeroCoe 1 id <| X.ordHom z hz f) := dif_pos hz

@[simp]
lemma ord_eq_zero_of_coheight_neq_one {z : X} (hz : coheight z ≠ 1) (f : X.functionField) :
    ord z f = 0 := dif_neg hz

@[simp]
lemma ord_zero {z : X} : ord z 0 = 0 := by
  by_cases h : coheight z = 1
  · simp [ord_eq_ordHom_of_coheight_eq_one h]
  · simp [h]

lemma ord_eq_unzero_ordHom {x : X} (hx : coheight x = 1) {f : X.functionField} (hf : f ≠ 0) :
    ord x f = Multiplicative.toAdd WithZero.unzero (ordHom_ne_zero hx hf) := by
  simp only [ord]
  obtain ⟨a1, ha1⟩ := WithZero.ne_zero_iff_exists.mp <| ordHom_ne_zero hx hf
  simp only [← ha1, hx]
  change a1 = unzero _
  rw [← WithZero.coe_inj, ha1]
  exact Eq.symm (coe_unzero (ordHom_ne_zero hx hf))

lemma ord_eq_iff {z : X} (hz : coheight z = 1) {f : X.functionField} (hf : f ≠ 0) {n : ℤ} :
    ord z f = n ↔ ordHom z hz f = Multiplicative.ofAdd n := by
  rw [ord_eq_unzero_ordHom hz hf]
  exact WithZero.toAdd_unzero_eq_iff _ _

@[simp]
lemma ord_mul {x : X} (hx : coheight x = 1) {f g : X.functionField}
    (hf : f ≠ 0) (hg : g ≠ 0) : ord x (f*g) = ord x f + ord x g := by
  have : f * g ≠ 0 := (mul_ne_zero_iff_right hg).mpr hf
  rw [ord_eq_iff hx this]
  obtain ⟨a1, ha1⟩ := WithZero.ne_zero_iff_exists.mp <| ordHom_ne_zero hx hf
  obtain ⟨a1, ha2⟩ := WithZero.ne_zero_iff_exists.mp <| ordHom_ne_zero hx hg
  simp [ord_eq_ordHom_of_coheight_eq_one hx, ← ha1, ← ha2]

lemma ord_of_isUnit {U : X.Opens} [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) {x : X}
    (hx : coheight x = 1) (hx' : x ∈ U) : ord x (X.germToFunctionField U f) = 0 := by
  have hf' : X.germToFunctionField U f ≠ 0 :=
    (map_ne_zero_iff _ (germToFunctionField_injective X U)).mpr <| IsUnit.ne_zero hf
  simp [ord_eq_iff hx hf', ordHom_of_isUnit hf hx hx']

lemma ord_le_ord_iff {x y : X} (hx : coheight x = 1) (hy : coheight y = 1) {f g : X.functionField}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    ord x f ≤ ord y g ↔ ordHom x hx f ≤ ordHom y hy g := by
  rw [ord_eq_unzero_ordHom hx hf, ord_eq_unzero_ordHom hy hg]
  erw [Multiplicative.toAdd_le]
  simp

lemma ord_add {x : X} (hx : coheight x = 1) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {f g : X.functionField} (hfg : f + g ≠ 0) :
    min (ord x f) (ord x g) ≤ ord x (f + g) := by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  simp only [inf_le_iff]
  obtain h | h := inf_le_iff.mp <| Ring.ordFrac_add (R := X.presheaf.stalk x) _ _ hfg
  · left
    rwa [ord_le_ord_iff hx hx hf hfg]
  · right
    rwa [ord_le_ord_iff hx hx hg hfg]

lemma ord_le_smul {x : X} (hx : coheight x = 1) {U : X.Opens} [Nonempty U] (hxU : x ∈ U)
    {a : Γ(X, U)} (ha : a ≠ 0) (f : X.functionField) : ord x f ≤ ord x (a • f) := by
  by_cases hf : f = 0
  · simp [hf]
  have : a • f ≠ 0 := (mul_ne_zero_iff_right hf).mpr <|
    (map_ne_zero_iff _ (germToFunctionField_injective _ _)).mpr ha
  rw [ord_le_ord_iff hx hx hf this]
  let l : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk x) := krullDimLE_of_coheight hx
  have : IsScalarTower ↑Γ(X, U) ↑(X.presheaf.stalk x) ↑X.functionField :=
    functionField_isScalarTower X U ⟨x, hxU⟩
  have : (algebraMap Γ(X, U) (X.presheaf.stalk x) a) ≠ 0 :=
    (map_ne_zero_iff _ (germ_injective_of_isIntegral X x hxU)).mpr ha
  exact Ring.ordFrac_le_smul a this f

end AlgebraicGeometry.Scheme
