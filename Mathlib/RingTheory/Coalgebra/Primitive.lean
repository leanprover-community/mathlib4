/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Coalgebra.Equiv

/-!
# Skew-primitive elements in a coalgebra

This file defines `(g, h)`-skew-primitive elements in a coalgebra, i.e. elements `a` such that
`ε a = 0` and `Δ a = g ⊗ₜ a + a ⊗ₜ h`, for group-like elements `g` and `h`.

## Main declarations

* `Coalgebra.IsSkewPrimitiveElem R g h a`: `a` is `(g, h)`-skew-primitive.
* `Coalgebra.skewPrimitive R g h`: the `(g, h)`-skew-primitive elements as a submodule.

## TODO

* `g - h` is `(g, h)`-skew-primitive, and the quotient of `skewPrimitive R g h` by
  `R ∙ (g - h)` is `Ext¹(h, g)`, where `g` and `h` are regarded as one-dimensional right
  comodules.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15]
-/

@[expose] public section

open TensorProduct

variable {F R A B : Type*} [CommSemiring R]

namespace Coalgebra

section AddCommMonoid
variable [AddCommMonoid A] [Module R A] [Coalgebra R A]
  [AddCommMonoid B] [Module R B] [Coalgebra R B] {g h a b : A}

variable (R) in
/-- An element `a` of a coalgebra is `(g, h)`-skew-primitive if `ε a = 0` and
`Δ a = g ⊗ₜ a + a ⊗ₜ h`, where `ε` and `Δ` are the counit and comultiplication respectively. -/
@[mk_iff]
structure IsSkewPrimitiveElem (g h a : A) : Prop where
  /-- A skew-primitive element `a` satisfies `ε(a) = 0`. -/
  counit_eq_zero : counit (R := R) a = 0
  /-- A `(g, h)`-skew-primitive element `a` satisfies `Δ(a) = g ⊗ₜ a + a ⊗ₜ h`. -/
  comul_eq_tmul_add_tmul : comul a = g ⊗ₜ[R] a + a ⊗ₜ[R] h

namespace IsSkewPrimitiveElem

@[simp] lemma zero : IsSkewPrimitiveElem R g h (0 : A) := by simp [isSkewPrimitiveElem_iff]

lemma add (ha : IsSkewPrimitiveElem R g h a) (hb : IsSkewPrimitiveElem R g h b) :
    IsSkewPrimitiveElem R g h (a + b) where
  counit_eq_zero := by simp [ha.counit_eq_zero, hb.counit_eq_zero]
  comul_eq_tmul_add_tmul := by
    simp [ha.comul_eq_tmul_add_tmul, hb.comul_eq_tmul_add_tmul, add_tmul, tmul_add,
      add_add_add_comm]

lemma smul (ha : IsSkewPrimitiveElem R g h a) (r : R) : IsSkewPrimitiveElem R g h (r • a) where
  counit_eq_zero := by simp [ha.counit_eq_zero]
  comul_eq_tmul_add_tmul := by simp [ha.comul_eq_tmul_add_tmul, smul_tmul']

/-- A coalgebra homomorphism sends `(g, h)`-skew-primitive elements to
`(f g, f h)`-skew-primitive elements. -/
lemma map [FunLike F A B] [CoalgHomClass F R A B] (f : F) (ha : IsSkewPrimitiveElem R g h a) :
    IsSkewPrimitiveElem R (f g) (f h) (f a) where
  counit_eq_zero := by simp [ha.counit_eq_zero]
  comul_eq_tmul_add_tmul := by
    simp [ha.comul_eq_tmul_add_tmul, ← CoalgHomClass.map_comp_comul_apply]

end IsSkewPrimitiveElem

/-- A coalgebra isomorphism preserves skew-primitivity. -/
@[simp] lemma isSkewPrimitiveElem_map_equiv [EquivLike F A B] [CoalgEquivClass F R A B] (f : F) :
    IsSkewPrimitiveElem R (f g) (f h) (f a) ↔ IsSkewPrimitiveElem R g h a where
  mp ha :=
    let e := CoalgEquivClass.toCoalgEquiv f
    e.symm_apply_apply g ▸ e.symm_apply_apply h ▸ e.symm_apply_apply a ▸ ha.map _
  mpr := .map f

variable (R g h) in
/-- The `(g, h)`-skew-primitive elements form a submodule. -/
def skewPrimitive : Submodule R A where
  carrier := {a | IsSkewPrimitiveElem R g h a}
  add_mem' := .add
  zero_mem' := .zero
  smul_mem' r _ ha := ha.smul r

@[simp] lemma mem_skewPrimitive :
    a ∈ skewPrimitive R g h ↔ IsSkewPrimitiveElem R g h a := Iff.rfl

variable [IsCancelAdd A]

/-- When `g` and `h` have counit `1` (e.g. when they are group-like), the counit condition
follows from the comultiplication condition. -/
lemma counit_eq_zero_of_comul_eq_tmul_add_tmul (hg : counit (R := R) g = 1)
    (hh : counit (R := R) h = 1) (ha : comul a = g ⊗ₜ[R] a + a ⊗ₜ[R] h) :
    counit (R := R) a = 0 := by
  have : counit (R := R) a • h = 0 := by
    simpa [ha, hg] using congr(TensorProduct.lid R A $(rTensor_counit_comul (R := R) a))
  simpa [hh] using congr(counit (R := R) $this)

lemma IsSkewPrimitiveElem.of_comul_eq_tmul_add_tmul (hg : counit (R := R) g = 1)
    (hh : counit (R := R) h = 1) (ha : comul a = g ⊗ₜ[R] a + a ⊗ₜ[R] h) :
    IsSkewPrimitiveElem R g h a :=
  ⟨counit_eq_zero_of_comul_eq_tmul_add_tmul hg hh ha, ha⟩

lemma isSkewPrimitiveElem_iff_comul_eq_tmul_add_tmul (hg : counit (R := R) g = 1)
    (hh : counit (R := R) h = 1) :
    IsSkewPrimitiveElem R g h a ↔ comul a = g ⊗ₜ[R] a + a ⊗ₜ[R] h :=
  ⟨IsSkewPrimitiveElem.comul_eq_tmul_add_tmul, .of_comul_eq_tmul_add_tmul hg hh⟩

end AddCommMonoid

section AddCommGroup
variable [AddCommGroup A] [Module R A] [Coalgebra R A] {g h a b : A}

namespace IsSkewPrimitiveElem

lemma neg (ha : IsSkewPrimitiveElem R g h a) : IsSkewPrimitiveElem R g h (-a) where
  counit_eq_zero := by simpa [ha.counit_eq_zero] using (map_add (counit (R := R)) (-a) a).symm
  comul_eq_tmul_add_tmul := by
    simp [ha.comul_eq_tmul_add_tmul, neg_tmul, tmul_neg, add_comm]

lemma sub (ha : IsSkewPrimitiveElem R g h a) (hb : IsSkewPrimitiveElem R g h b) :
    IsSkewPrimitiveElem R g h (a - b) :=
  sub_eq_add_neg a b ▸ ha.add hb.neg

end IsSkewPrimitiveElem

@[simp] lemma isSkewPrimitiveElem_neg :
    IsSkewPrimitiveElem R g h (-a) ↔ IsSkewPrimitiveElem R g h a :=
  ⟨fun ha ↦ neg_neg a ▸ ha.neg, .neg⟩

end AddCommGroup

end Coalgebra
