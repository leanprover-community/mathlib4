/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.GroupTheory.Complement

/-!

## Pushouts of Monoids and Groups

This file defines wide pushouts of monoids and groups and proves some properties
of the amalgamated product of groups (i.e. the special case where all the maps
in the diagram are injective).

## Main definitions

- `Monoid.PushoutI`: the pushout of a diagram of monoids indexed by a type `ι`
- `Monoid.PushoutI.base`: the map from the amalgamating monoid to the pushout
- `Monoid.PushoutI.of`: the map from each Monoid in the family to the pushout
- `Monoid.PushoutI.lift`: the universal property used to define homomorphisms out of the pushout.

## References

* The normal form theorem follows these [notes](https://webspace.maths.qmul.ac.uk/i.m.chiswell/ggt/lecture_notes/lecture2.pdf)
from Queen Mary University

## Tags

amalgamated product, pushout, group

-/

namespace Monoid

open CoprodI Subgroup Coprod Function List

variable {ι : Type*} {G : ι → Type*} {H : Type*} {K : Type*} [Monoid K]

/-- The relation we quotient by to form the pushout -/
def PushoutI.con [∀ i, Monoid (G i)] [Monoid H] (φ : ∀ i, H →* G i) :
    Con (Coprod (CoprodI G) H) :=
  conGen (fun x y : Coprod (CoprodI G) H =>
    ∃ i x', x = inl (of (φ i x')) ∧ y = inr x')

/-- The indexed pushout of monoids, which is the pushout in the category of monoids,
or the category of groups. -/
def PushoutI [∀ i, Monoid (G i)] [Monoid H] (φ : ∀ i, H →* G i) : Type _ :=
  (PushoutI.con φ).Quotient

namespace PushoutI

section Monoid

variable [∀ i, Monoid (G i)] [Monoid H] {φ : ∀ i, H →* G i}

protected instance mul : Mul (PushoutI φ) := by
  delta PushoutI; infer_instance

protected instance one : One (PushoutI φ) := by
  delta PushoutI; infer_instance

instance monoid : Monoid (PushoutI φ) :=
  { Con.monoid _ with
    toMul := PushoutI.mul
    toOne := PushoutI.one }

/-- The map from each indexing group into the pushout -/
def of (i : ι) : G i →* PushoutI φ :=
  (Con.mk' _).comp <| inl.comp CoprodI.of

variable (φ) in
/-- The map from the base monoid into the pushout -/
def base : H →* PushoutI φ :=
  (Con.mk' _).comp inr

theorem of_comp_eq_base (i : ι) : (of i).comp (φ i) = (base φ) := by
  ext x
  apply (Con.eq _).2
  refine ConGen.Rel.of _ _ ?_
  simp only [MonoidHom.comp_apply, Set.mem_iUnion, Set.mem_range]
  exact ⟨_, _, rfl, rfl⟩

variable (φ) in
theorem of_apply_eq_base (i : ι) (x : H) : of i (φ i x) = base φ x := by
  rw [← MonoidHom.comp_apply, of_comp_eq_base]

/-- Define a homomorphism out of the pushout of monoids be defining it on each object in the
diagram -/
def lift (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (φ i) = k) :
    PushoutI φ →* K :=
  Con.lift _ (Coprod.lift (CoprodI.lift f) k) <| by
    apply Con.conGen_le <| fun x y => ?_
    rintro ⟨i, x', rfl, rfl⟩
    simp only [FunLike.ext_iff, MonoidHom.coe_comp, comp_apply] at hf
    simp [hf]

@[simp]
theorem lift_of (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (φ i) = k)
    {i : ι} (g : G i) : (lift f k hf) (of i g : PushoutI φ) = f i g := by
  delta PushoutI lift of
  simp only [MonoidHom.coe_comp, Con.coe_mk', comp_apply, Con.lift_coe,
    lift_apply_inl, CoprodI.lift_of]

@[simp]
theorem lift_base (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (φ i) = k)
    (g : H) : (lift f k hf) (base φ g : PushoutI φ) = k g := by
  delta PushoutI lift base
  simp only [MonoidHom.coe_comp, Con.coe_mk', comp_apply, Con.lift_coe, lift_apply_inr]

-- `ext` attribute should be lower priority then `hom_ext_nonempty`
@[ext 1199]
theorem hom_ext {f g : PushoutI φ →* K}
    (h : ∀ i, f.comp (of i : G i →* _) = g.comp (of i : G i →* _))
    (hbase : f.comp (base φ) = g.comp (base φ)) : f = g :=
  (MonoidHom.cancel_right Con.mk'_surjective).mp <|
    Coprod.hom_ext
      (CoprodI.ext_hom _ _ h)
      hbase

@[ext high]
theorem hom_ext_nonempty [hn : Nonempty ι]
    {f g : PushoutI φ →* K}
    (h : ∀ i, f.comp (of i : G i →* _) = g.comp (of i : G i →* _)) : f = g :=
  hom_ext h <| by
    cases hn with
    | intro i =>
      ext
      rw [← of_comp_eq_base i, ← MonoidHom.comp_assoc, h, MonoidHom.comp_assoc]

/-- The equivalence that is part of the universal property of the pushout. A hom out of
the pushout is just a morphism out of all groups in the pushout that satsifies a commutativity
condition. -/
@[simps]
def homEquiv :
    (PushoutI φ →* K) ≃ { f : (Π i, G i →* K) × (H →* K) // ∀ i, (f.1 i).comp (φ i) = f.2 } :=
  { toFun := fun f => ⟨(fun i => f.comp (of i), f.comp (base φ)),
      fun i => by rw [MonoidHom.comp_assoc, of_comp_eq_base]⟩
    invFun := fun f => lift f.1.1 f.1.2 f.2,
    left_inv := fun _ => hom_ext (by simp [FunLike.ext_iff])
      (by simp [FunLike.ext_iff])
    right_inv := fun ⟨⟨_, _⟩, _⟩ => by simp [FunLike.ext_iff, Function.funext_iff] }

/-- The map from the coproduct into the pushout -/
def ofCoprodI : CoprodI G →* PushoutI φ :=
  CoprodI.lift of

@[simp]
theorem ofCoprodI_of (i : ι) (g : G i) :
    (ofCoprodI (CoprodI.of g) : PushoutI φ) = of i g := by
  simp [ofCoprodI]

theorem induction_on {motive : PushoutI φ → Prop}
    (x : PushoutI φ)
    (of  : ∀ (i : ι) (g : G i), motive (of i g))
    (base : ∀ h, motive (base φ h))
    (mul : ∀ x y, motive x → motive y → motive (x * y)) : motive x := by
  delta PushoutI PushoutI.of PushoutI.base at *
  induction x using Con.induction_on with
  | H x =>
    induction x using Coprod.induction_on with
    | inl g =>
      induction g using CoprodI.induction_on with
      | h_of i g => exact of i g
      | h_mul x y ihx ihy =>
        rw [map_mul]
        exact mul _ _ ihx ihy
      | h_one => simpa using base 1
    | inr h => exact base h
    | mul x y ihx ihy => exact mul _ _ ihx ihy

end Monoid

variable [∀ i, Group (G i)] [Group H] {φ : ∀ i, H →* G i}

instance : Group (PushoutI φ) :=
  { Con.group (PushoutI.con φ) with
    toMonoid := PushoutI.monoid }
