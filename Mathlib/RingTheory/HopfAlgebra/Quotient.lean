/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Quotient
public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Hopf algebra structure on quotients

If the antipode of an `R`-Hopf algebra `A` descends along a bialgebra congruence `c`, then
`c.Quotient` is again a Hopf algebra. A *Hopf ideal* of `A`, a biideal stable under the antipode,
induces such a congruence, so the quotient by a Hopf ideal is a Hopf algebra.

## Main definitions

* `RingCon.IsHopfAlgebraCon R c` : `IsBialgebraCon R c` together with descent of the antipode.
* `Ideal.IsHopfIdeal R I` : `I` is a coideal (as an `R`-submodule) stable under the antipode.

## Main results

* `HopfAlgebra R c.Quotient` instance when `[c.IsHopfAlgebraCon R]`.
* `HopfAlgebra R (A ⧸ I)` instance when `[I.IsTwoSided]` and `[I.IsHopfIdeal R]`.
-/

public section

open HopfAlgebra

section RingCon

variable {R A : Type*} [CommSemiring R] [Semiring A]

variable (R) in
/-- A ring congruence `c` on an `R`-Hopf algebra is a Hopf algebra congruence if it is a
bialgebra congruence along which the antipode also descends. -/
@[mk_iff]
class RingCon.IsHopfAlgebraCon [HopfAlgebraStruct R A] (c : RingCon A) : Prop
    extends RingCon.IsBialgebraCon R c where
  antipode_rel : ∀ ⦃x y : A⦄, c x y → c (antipode R x) (antipode R y)

namespace HopfAlgebra.Quotient

section HopfAlgebraStruct

variable [HopfAlgebraStruct R A] (c : RingCon A) [hc : c.IsHopfAlgebraCon R]

/-- The antipode of `c.Quotient`, sending `↑a` to `↑(antipode R a)`. -/
instance : HopfAlgebraStruct R c.Quotient where
  antipode :=
    { toFun := Quotient.map (antipode R) fun _ _ h ↦ hc.antipode_rel h
      map_add' := Quotient.ind₂ fun x y ↦
        congrArg ((↑) : A → c.Quotient) (map_add (antipode R) x y)
      map_smul' r := Quotient.ind fun x ↦
        congrArg ((↑) : A → c.Quotient) (map_smul (antipode R) r x) }

@[simp]
lemma antipode_coe (a : A) : antipode R (a : c.Quotient) = ↑(antipode R a) := rfl

end HopfAlgebraStruct

variable [HopfAlgebra R A] (c : RingCon A) [c.IsHopfAlgebraCon R]

/-- The Hopf algebra structure on `c.Quotient` when `c` is a Hopf algebra congruence. -/
noncomputable instance : HopfAlgebra R c.Quotient :=
  .ofSurjective (c.mkBialgHom R) c.mk'_surjective fun _ ↦ rfl

end HopfAlgebra.Quotient

end RingCon

section Ideal

variable {R A : Type*} [CommRing R] [Ring A]

section HopfAlgebraStruct

variable [HopfAlgebraStruct R A]

variable (R) in
/-- An ideal whose underlying `R`-submodule is a coideal and which is stable under the
antipode (`S(I) ⊆ I`). Together with `I.IsTwoSided`, this makes `I` a *Hopf ideal*. -/
@[mk_iff]
class Ideal.IsHopfIdeal (I : Ideal A) : Prop extends (I.restrictScalars R).IsCoideal where
  antipode_mem : ∀ ⦃x : A⦄, x ∈ I → antipode R x ∈ I

variable (I : Ideal A) [I.IsTwoSided] [I.IsHopfIdeal R]

/-- The ring congruence of a Hopf ideal is a Hopf algebra congruence. -/
instance : (Ideal.Quotient.ringCon I).IsHopfAlgebraCon R where
  antipode_rel _ _ h := Quotient.exact <| Ideal.Quotient.eq.mpr <| by
    rw [← map_sub]
    exact Ideal.IsHopfIdeal.antipode_mem (Ideal.Quotient.eq.mp (Quotient.sound h))

namespace HopfAlgebra.Quotient

/-- The antipode of `A ⧸ I` when `I` is a Hopf ideal. -/
instance : HopfAlgebraStruct R (A ⧸ I) :=
  { (inferInstance : Bialgebra R (A ⧸ I)),
    (inferInstance : HopfAlgebraStruct R (Ideal.Quotient.ringCon I).Quotient) with }

@[simp]
lemma antipode_mk (a : A) :
    antipode R (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (antipode R a) := rfl

@[deprecated antipode_mk +typeChanged (since := "2026-09-19")]
lemma antipode_comp_mkₐ :
    antipode R ∘ₗ (Ideal.Quotient.mkₐ R I).toLinearMap =
      (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ antipode R := by ext; simp

end HopfAlgebra.Quotient

end HopfAlgebraStruct

variable [HopfAlgebra R A] (I : Ideal A) [I.IsTwoSided] [I.IsHopfIdeal R]

namespace HopfAlgebra.Quotient

/-- The Hopf algebra structure on `A ⧸ I` when `I` is a Hopf ideal. -/
noncomputable instance : HopfAlgebra R (A ⧸ I) :=
  .ofSurjective (Bialgebra.Quotient.mkBialgHom I) Ideal.Quotient.mk_surjective fun _ ↦ rfl

end HopfAlgebra.Quotient

end Ideal
