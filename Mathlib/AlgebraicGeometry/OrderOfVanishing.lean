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

namespace AlgebraicGeometry
namespace Scheme

lemma krullDimLE_of_coheight
    {Z : X} {n : ℕ} (hZ : coheight Z = n) : Ring.KrullDimLE n (X.presheaf.stalk Z) := by
  rw [Ring.krullDimLE_iff, ringKrullDim_stalk_eq_coheight Z]
  exact_mod_cast hZ.le

variable [IsIntegral X]

/--
For `f` an element of the function field of `X`, there exists some open set `U ⊆ X` such that
`f` is a unit in `Γ(X, U)`.
-/
lemma exists_isUnit_germ_eq (f : X.functionField) (hf : f ≠ 0) :
    ∃ U : X.Opens, ∃ f' : Γ(X, U), ∃ _ : Nonempty U,
    X.germToFunctionField U f' = f ∧ IsUnit f' := by
  obtain ⟨U, hU, g, hg⟩ := TopCat.Presheaf.germ_exist _ _ f
  have : Nonempty U := ⟨_, hU⟩
  have : Nonempty (X.basicOpen g) := by
    rw [Scheme.Opens.nonempty_iff]
    apply (Opens.ne_bot_iff_nonempty (X.basicOpen g)).mp
    intro a
    simp_all
  refine ⟨X.basicOpen g, X.presheaf.map (X.basicOpen_le g).hom.op g, ‹_›, ?_,
    X.toRingedSpace.isUnit_res_basicOpen g⟩
  rw [germToFunctionField_map, hg]

variable [IsLocallyNoetherian X]

/--
On a locally Noetherian integral scheme, we define the order of vanishing of an element of the
function field `f` at a point `Z` of codimension `1` to be `Ring.ordFrac (X.presheaf.stalk Z) f`.
Because of this definition, `Scheme.ord` is valued in `ℤᵐ⁰`.
-/
noncomputable
def ord (Z : X) (hZ : coheight Z = 1) : X.functionField →*₀ ℤᵐ⁰ :=
  have : Ring.KrullDimLE 1 _ := krullDimLE_of_coheight hZ
  Ring.ordFrac (X.presheaf.stalk Z)

/--
The order of vanishing of a non-zero element of the function field at any point is not zero. Since
`Scheme.ord` is valued in `ℤᵐ⁰`, `0` does not denote a value of `ℤ` but an added `⊥` element. With
that in mind, this theorem is really saying that the order of vanishing of any nonzero element of
the function field at any point of codimension one is some finite value.
-/
lemma ord_ne_zero {Z : X} (hZ : coheight Z = 1) {f : X.functionField} (hf : f ≠ 0) :
    Scheme.ord Z hZ f ≠ 0 := (map_ne_zero (Scheme.ord Z hZ)).mpr hf

/--
The order of vanishing of a unit is `1` everywhere.
-/
lemma ord_of_isUnit {U : X.Opens}
    [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) {x : X} (hx : coheight x = 1) (hx' : x ∈ U) :
    Scheme.ord x hx (X.germToFunctionField U f) = 1 := by
  have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk x) := krullDimLE_of_coheight hx
  rw [germToFunctionField_eq_algebraMap_germ hx']
  exact Ring.ordFrac_of_isUnit (hf.map (X.presheaf.germ U x hx').hom)

lemma not_mem_of_ord_neq_one (f : X.functionField) {U : X.Opens} [Nonempty U] {g : Γ(X, U)}
    (hg : IsUnit g) (hgf : X.germToFunctionField U g = f) {x : X} {hx : coheight x = 1}
    (h : Scheme.ord x hx f ≠ 1) : x ∉ U := fun a ↦ h (hgf ▸ ord_of_isUnit hg hx a)

lemma ord_add (x : X) (hx : coheight x = 1) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {f g : X.functionField} (h : f + g ≠ 0) :
    min (ord x hx f) (ord x hx g) ≤ ord x hx (f + g) := Ring.ordFrac_add f g h

/--
Order of vanishing function valued in `ℤ`.
-/
noncomputable
def ordZ (x : X) (hx : coheight x = 1) (f : X.functionField) : ℤ :=
    WithZero.recZeroCoe 0 id <| X.ord x hx f

lemma ord_eq_coe_ordZ {x : X} {hx : coheight x = 1} (f : X.functionField) (hf : f ≠ 0) :
    ord x hx f = ↑(Multiplicative.ofAdd (ordZ x hx f)) := by
  simp [ordZ]
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp <| ord_ne_zero hx hf
  simp [← ha]
  rfl
/-
lemma ordZ_eq_ord {x : X} {hx : coheight x = 1} (f : X.functionField) (hf : f ≠ 0) :
    ordZ x hx f = Multiplicative.toAdd WithZero.unzero (ord_ne_zero hx hf) := by
  simp [ordZ]
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp <| ord_ne_zero hx hf
  simp [← ha]
  have := ord_ne_zero hx hf
  rw [← ha] at this
  have o := WithZero.unzero_coe this
  rw [← o]

  /-
  I'm not sure if this lemma is actually useful...
  -/
  sorry-/


@[simp]
lemma ordZ_mul {x : X} {hx : coheight x = 1} {f g : X.functionField}
    {hf : f ≠ 0} {hg : g ≠ 0} : ordZ x hx (f*g) = ordZ x hx f + ordZ x hx g := by
  have : f * g ≠ 0 := (mul_ne_zero_iff_right hg).mpr hf
  obtain ⟨a1, ha1⟩ := WithZero.ne_zero_iff_exists.mp <| ord_ne_zero hx this
  obtain ⟨a2, ha2⟩ := WithZero.ne_zero_iff_exists.mp <| ord_ne_zero hx hf
  obtain ⟨a3, ha3⟩ := WithZero.ne_zero_iff_exists.mp <| ord_ne_zero hx hg
  simp only [ordZ, ← ha1, ← ha2, ← ha3]
  change a1 = a2 * a3
  rw [← WithZero.coe_inj]
  simp [ha1, ha2, ha3]

lemma ordZ_of_isUnit {U : X.Opens}
    [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) {x : X} (hx : coheight x = 1) (hx' : x ∈ U) :
    X.ordZ x hx (X.germToFunctionField U f) = 0 := by
  simp only [ordZ]
  have hf' : X.germToFunctionField U f ≠ 0 :=
    (map_ne_zero_iff _ (germToFunctionField_injective X U)).mpr <| IsUnit.ne_zero hf
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp <| ord_ne_zero hx hf'
  simp only [← ha]
  change a = 1
  rw [← WithZero.coe_inj (α := Multiplicative ℤ), ha]
  exact ord_of_isUnit hf hx hx'

lemma not_mem_of_ordZ_neq_zero (f : X.functionField) {U : X.Opens} [Nonempty U] {g : Γ(X, U)}
    (hg : IsUnit g) (hgf : X.germToFunctionField U g = f) {x : X} {hx : coheight x = 1}
    (h : ordZ x hx f ≠ 0) : x ∉ U := fun a ↦ h (hgf ▸ ordZ_of_isUnit hg hx a)

lemma ordZ_add {x : X} (hx : coheight x = 1) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {f g : X.functionField} (h1 : f ≠ 0) (h2 : g ≠ 0) (h3 : f + g ≠ 0) :
    min (ordZ x hx f) (ordZ x hx g) ≤ ordZ x hx (f + g) := by
  obtain ⟨a1, ha1⟩ := WithZero.ne_zero_iff_exists.mp <| ord_ne_zero hx h1
  obtain ⟨a2, ha2⟩ := WithZero.ne_zero_iff_exists.mp <| ord_ne_zero hx h2
  obtain ⟨a3, ha3⟩ := WithZero.ne_zero_iff_exists.mp <| ord_ne_zero hx h3
  simp only [ordZ, ← ha1, recZeroCoe_coe, id_eq, ← ha2, ← ha3]
  have := ord_add x hx h3
  change (min a1 a2 : Multiplicative ℤ) ≤ a3
  rw [← WithZero.coe_le_coe]
  suffices min (a1 : WithZero (Multiplicative ℤ)) ↑a2 ≤ (a3 : WithZero (Multiplicative ℤ)) by
    exact le_of_le_of_eq this rfl
  rw [ha1, ha2, ha3]
  exact ord_add x hx h3

lemma ordZ_le_smul {x : X} (hx : coheight x = 1) {U : X.Opens} [Nonempty U] (hxU : x ∈ U)
    {a : Γ(X, U)} (ha : a ≠ 0) (f : X.functionField) :
    ordZ x hx f ≤ ordZ x hx (a • f) := by
  simp [ordZ]
  by_cases o : f = 0
  · simp [o]
  · obtain ⟨a1, ha1⟩ := WithZero.ne_zero_iff_exists.mp <| ord_ne_zero hx o
    have : (a • f) ≠ 0 := sorry
    obtain ⟨a2, ha2⟩ := WithZero.ne_zero_iff_exists.mp <| ord_ne_zero hx this
    rw [← ha1, ← ha2]
    simp
    change a1 ≤ a2
    rw [← WithZero.coe_le_coe (α := Multiplicative ℤ)]
    simp [ha1, ha2]
    have : Ring.KrullDimLE 1 _ := krullDimLE_of_coheight hx
    let p : Algebra ↑Γ(X, U) ↑(X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
    let test : IsScalarTower ↑Γ(X, U) ↑(X.presheaf.stalk x) ↑X.functionField :=
            AlgebraicGeometry.functionField_isScalarTower X U ⟨x, hxU⟩
    refine Ring.ordFrac_le_smul a ?_ f
    exact (map_ne_zero_iff _ (germ_injective_of_isIntegral  X x hxU)).mpr ha


end Scheme
end AlgebraicGeometry
