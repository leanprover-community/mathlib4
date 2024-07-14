/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.GroupTheory.Congruence.Basic

#align_import ring_theory.congruence from "leanprover-community/mathlib"@"2f39bcbc98f8255490f8d4562762c9467694c809"

/-!
# Congruence relations on rings

This file defines congruence relations on rings, which extend `Con` and `AddCon` on monoids and
additive monoids.

Most of the time you likely want to use the `Ideal.Quotient` API that is built on top of this.

## Main Definitions

* `RingCon R`: the type of congruence relations respecting `+` and `*`.
* `RingConGen r`: the inductively defined smallest ring congruence relation containing a given
  binary relation.

## TODO

* Use this for `RingQuot` too.
* Copy across more API from `Con` and `AddCon` in `GroupTheory/Congruence.lean`.
-/


/-- A congruence relation on a type with an addition and multiplication is an equivalence relation
which preserves both. -/
structure RingCon (R : Type*) [Add R] [Mul R] extends Con R, AddCon R where
#align ring_con RingCon

/-- The induced multiplicative congruence from a `RingCon`. -/
add_decl_doc RingCon.toCon

/-- The induced additive congruence from a `RingCon`. -/
add_decl_doc RingCon.toAddCon

variable {α R : Type*}

/-- The inductively defined smallest ring congruence relation containing a given binary
    relation. -/
inductive RingConGen.Rel [Add R] [Mul R] (r : R → R → Prop) : R → R → Prop
  | of : ∀ x y, r x y → RingConGen.Rel r x y
  | refl : ∀ x, RingConGen.Rel r x x
  | symm : ∀ {x y}, RingConGen.Rel r x y → RingConGen.Rel r y x
  | trans : ∀ {x y z}, RingConGen.Rel r x y → RingConGen.Rel r y z → RingConGen.Rel r x z
  | add : ∀ {w x y z}, RingConGen.Rel r w x → RingConGen.Rel r y z →
      RingConGen.Rel r (w + y) (x + z)
  | mul : ∀ {w x y z}, RingConGen.Rel r w x → RingConGen.Rel r y z →
      RingConGen.Rel r (w * y) (x * z)
#align ring_con_gen.rel RingConGen.Rel

/-- The inductively defined smallest ring congruence relation containing a given binary
    relation. -/
def ringConGen [Add R] [Mul R] (r : R → R → Prop) : RingCon R where
  r := RingConGen.Rel r
  iseqv := ⟨RingConGen.Rel.refl, @RingConGen.Rel.symm _ _ _ _, @RingConGen.Rel.trans _ _ _ _⟩
  add' := RingConGen.Rel.add
  mul' := RingConGen.Rel.mul
#align ring_con_gen ringConGen

namespace RingCon

section Basic

variable [Add R] [Mul R] (c : RingCon R)

-- Porting note: upgrade to `FunLike`
/-- A coercion from a congruence relation to its underlying binary relation. -/
instance : FunLike (RingCon R) R (R → Prop) :=
  { coe := fun c => c.r,
    coe_injective' := fun x y h => by
      rcases x with ⟨⟨x, _⟩, _⟩
      rcases y with ⟨⟨y, _⟩, _⟩
      congr!
      rw [Setoid.ext_iff,(show x.Rel = y.Rel from h)]
      simp}

theorem rel_eq_coe : c.r = c :=
  rfl
#align ring_con.rel_eq_coe RingCon.rel_eq_coe

@[simp]
theorem toCon_coe_eq_coe : (c.toCon : R → R → Prop) = c :=
  rfl

protected theorem refl (x) : c x x :=
  c.refl' x
#align ring_con.refl RingCon.refl

protected theorem symm {x y} : c x y → c y x :=
  c.symm'
#align ring_con.symm RingCon.symm

protected theorem trans {x y z} : c x y → c y z → c x z :=
  c.trans'
#align ring_con.trans RingCon.trans

protected theorem add {w x y z} : c w x → c y z → c (w + y) (x + z) :=
  c.add'
#align ring_con.add RingCon.add

protected theorem mul {w x y z} : c w x → c y z → c (w * y) (x * z) :=
  c.mul'
#align ring_con.mul RingCon.mul

instance : Inhabited (RingCon R) :=
  ⟨ringConGen EmptyRelation⟩

@[simp]
theorem rel_mk {s : Con R} {h a b} : RingCon.mk s h a b ↔ s a b :=
  Iff.rfl

/-- The map sending a congruence relation to its underlying binary relation is injective. -/
theorem ext' {c d : RingCon R} (H : ⇑c = ⇑d) : c = d := DFunLike.coe_injective H

/-- Extensionality rule for congruence relations. -/
theorem ext {c d : RingCon R} (H : ∀ x y, c x y ↔ d x y) : c = d :=
  ext' <| by ext; apply H

end Basic

section Quotient

section Basic

variable [Add R] [Mul R] (c : RingCon R)

/-- Defining the quotient by a congruence relation of a type with addition and multiplication. -/
protected def Quotient :=
  Quotient c.toSetoid
#align ring_con.quotient RingCon.Quotient

variable {c}

/-- The morphism into the quotient by a congruence relation -/
@[coe] def toQuotient (r : R) : c.Quotient :=
  @Quotient.mk'' _ c.toSetoid r

variable (c)

/-- Coercion from a type with addition and multiplication to its quotient by a congruence relation.

See Note [use has_coe_t]. -/
instance : CoeTC R c.Quotient :=
  ⟨toQuotient⟩

-- Lower the priority since it unifies with any quotient type.
/-- The quotient by a decidable congruence relation has decidable equality. -/
instance (priority := 500) [_d : ∀ a b, Decidable (c a b)] : DecidableEq c.Quotient :=
  inferInstanceAs (DecidableEq (Quotient c.toSetoid))

@[simp]
theorem quot_mk_eq_coe (x : R) : Quot.mk c x = (x : c.Quotient) :=
  rfl
#align ring_con.quot_mk_eq_coe RingCon.quot_mk_eq_coe

/-- Two elements are related by a congruence relation `c` iff they are represented by the same
element of the quotient by `c`. -/
@[simp]
protected theorem eq {a b : R} : (a : c.Quotient) = (b : c.Quotient) ↔ c a b :=
  Quotient.eq''
#align ring_con.eq RingCon.eq

end Basic

/-! ### Basic notation

The basic algebraic notation, `0`, `1`, `+`, `*`, `-`, `^`, descend naturally under the quotient
-/


section Data

section add_mul

variable [Add R] [Mul R] (c : RingCon R)

instance : Add c.Quotient := inferInstanceAs (Add c.toAddCon.Quotient)

@[simp, norm_cast]
theorem coe_add (x y : R) : (↑(x + y) : c.Quotient) = ↑x + ↑y :=
  rfl
#align ring_con.coe_add RingCon.coe_add

instance : Mul c.Quotient := inferInstanceAs (Mul c.toCon.Quotient)

@[simp, norm_cast]
theorem coe_mul (x y : R) : (↑(x * y) : c.Quotient) = ↑x * ↑y :=
  rfl
#align ring_con.coe_mul RingCon.coe_mul

end add_mul

section Zero

variable [AddZeroClass R] [Mul R] (c : RingCon R)

instance : Zero c.Quotient := inferInstanceAs (Zero c.toAddCon.Quotient)

@[simp, norm_cast]
theorem coe_zero : (↑(0 : R) : c.Quotient) = 0 :=
  rfl
#align ring_con.coe_zero RingCon.coe_zero

end Zero

section One

variable [Add R] [MulOneClass R] (c : RingCon R)

instance : One c.Quotient := inferInstanceAs (One c.toCon.Quotient)

@[simp, norm_cast]
theorem coe_one : (↑(1 : R) : c.Quotient) = 1 :=
  rfl
#align ring_con.coe_one RingCon.coe_one

end One

section SMul

variable [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R] (c : RingCon R)

instance : SMul α c.Quotient := inferInstanceAs (SMul α c.toCon.Quotient)

@[simp, norm_cast]
theorem coe_smul (a : α) (x : R) : (↑(a • x) : c.Quotient) = a • (x : c.Quotient) :=
  rfl
#align ring_con.coe_smul RingCon.coe_smul

end SMul

section NegSubZSMul

variable [AddGroup R] [Mul R] (c : RingCon R)

instance : Neg c.Quotient := inferInstanceAs (Neg c.toAddCon.Quotient)

@[simp, norm_cast]
theorem coe_neg (x : R) : (↑(-x) : c.Quotient) = -x :=
  rfl
#align ring_con.coe_neg RingCon.coe_neg

instance : Sub c.Quotient := inferInstanceAs (Sub c.toAddCon.Quotient)

@[simp, norm_cast]
theorem coe_sub (x y : R) : (↑(x - y) : c.Quotient) = x - y :=
  rfl
#align ring_con.coe_sub RingCon.coe_sub

instance hasZSMul : SMul ℤ c.Quotient := inferInstanceAs (SMul ℤ c.toAddCon.Quotient)
#align ring_con.has_zsmul RingCon.hasZSMul

@[simp, norm_cast]
theorem coe_zsmul (z : ℤ) (x : R) : (↑(z • x) : c.Quotient) = z • (x : c.Quotient) :=
  rfl
#align ring_con.coe_zsmul RingCon.coe_zsmul

end NegSubZSMul

section NSMul

variable [AddMonoid R] [Mul R] (c : RingCon R)

instance hasNSMul : SMul ℕ c.Quotient := inferInstanceAs (SMul ℕ c.toAddCon.Quotient)
#align ring_con.has_nsmul RingCon.hasNSMul

@[simp, norm_cast]
theorem coe_nsmul (n : ℕ) (x : R) : (↑(n • x) : c.Quotient) = n • (x : c.Quotient) :=
  rfl
#align ring_con.coe_nsmul RingCon.coe_nsmul

end NSMul

section Pow

variable [Add R] [Monoid R] (c : RingCon R)

instance : Pow c.Quotient ℕ := inferInstanceAs (Pow c.toCon.Quotient ℕ)

@[simp, norm_cast]
theorem coe_pow (x : R) (n : ℕ) : (↑(x ^ n) : c.Quotient) = (x : c.Quotient) ^ n :=
  rfl
#align ring_con.coe_pow RingCon.coe_pow

end Pow

section NatCast

variable [AddMonoidWithOne R] [Mul R] (c : RingCon R)

instance : NatCast c.Quotient :=
  ⟨fun n => ↑(n : R)⟩

@[simp, norm_cast]
theorem coe_natCast (n : ℕ) : (↑(n : R) : c.Quotient) = n :=
  rfl
#align ring_con.coe_nat_cast RingCon.coe_natCast

@[deprecated (since := "2024-04-17")]
alias coe_nat_cast := coe_natCast

end NatCast

section IntCast

variable [AddGroupWithOne R] [Mul R] (c : RingCon R)

instance : IntCast c.Quotient :=
  ⟨fun z => ↑(z : R)⟩

@[simp, norm_cast]
theorem coe_intCast (n : ℕ) : (↑(n : R) : c.Quotient) = n :=
  rfl
#align ring_con.coe_int_cast RingCon.coe_intCast

@[deprecated (since := "2024-04-17")]
alias coe_int_cast := coe_intCast

end IntCast

instance [Inhabited R] [Add R] [Mul R] (c : RingCon R) : Inhabited c.Quotient :=
  ⟨↑(default : R)⟩

end Data

/-! ### Algebraic structure

The operations above on the quotient by `c : RingCon R` preserve the algebraic structure of `R`.
-/


section Algebraic

instance [NonUnitalNonAssocSemiring R] (c : RingCon R) : NonUnitalNonAssocSemiring c.Quotient :=
  Function.Surjective.nonUnitalNonAssocSemiring _ Quotient.surjective_Quotient_mk'' rfl
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [NonAssocSemiring R] (c : RingCon R) : NonAssocSemiring c.Quotient :=
  Function.Surjective.nonAssocSemiring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [NonUnitalSemiring R] (c : RingCon R) : NonUnitalSemiring c.Quotient :=
  Function.Surjective.nonUnitalSemiring _ Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance [Semiring R] (c : RingCon R) : Semiring c.Quotient :=
  Function.Surjective.semiring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [CommSemiring R] (c : RingCon R) : CommSemiring c.Quotient :=
  Function.Surjective.commSemiring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [NonUnitalNonAssocRing R] (c : RingCon R) : NonUnitalNonAssocRing c.Quotient :=
  Function.Surjective.nonUnitalNonAssocRing _ Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [NonAssocRing R] (c : RingCon R) : NonAssocRing c.Quotient :=
  Function.Surjective.nonAssocRing _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl

instance [NonUnitalRing R] (c : RingCon R) : NonUnitalRing c.Quotient :=
  Function.Surjective.nonUnitalRing _ Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [Ring R] (c : RingCon R) : Ring c.Quotient :=
  Function.Surjective.ring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

instance [CommRing R] (c : RingCon R) : CommRing c.Quotient :=
  Function.Surjective.commRing _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

instance isScalarTower_right [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
    (c : RingCon R) : IsScalarTower α c.Quotient c.Quotient where
  smul_assoc _ := Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' <| smul_mul_assoc _ _ _
#align ring_con.is_scalar_tower_right RingCon.isScalarTower_right

instance smulCommClass [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
    [SMulCommClass α R R] (c : RingCon R) : SMulCommClass α c.Quotient c.Quotient where
  smul_comm _ := Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' <| (mul_smul_comm _ _ _).symm
#align ring_con.smul_comm_class RingCon.smulCommClass

instance smulCommClass' [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
    [SMulCommClass R α R] (c : RingCon R) : SMulCommClass c.Quotient α c.Quotient :=
  haveI := SMulCommClass.symm R α R
  SMulCommClass.symm _ _ _
#align ring_con.smul_comm_class' RingCon.smulCommClass'

instance [Monoid α] [NonAssocSemiring R] [DistribMulAction α R] [IsScalarTower α R R]
    (c : RingCon R) : DistribMulAction α c.Quotient :=
  { c.toCon.mulAction with
    smul_zero := fun _ => congr_arg toQuotient <| smul_zero _
    smul_add := fun _ => Quotient.ind₂' fun _ _ => congr_arg toQuotient <| smul_add _ _ _ }

instance [Monoid α] [Semiring R] [MulSemiringAction α R] [IsScalarTower α R R] (c : RingCon R) :
    MulSemiringAction α c.Quotient :=
  { smul_one := fun _ => congr_arg toQuotient <| smul_one _
    smul_mul := fun _ => Quotient.ind₂' fun _ _ => congr_arg toQuotient <|
      MulSemiringAction.smul_mul _ _ _ }

end Algebraic

/-- The natural homomorphism from a ring to its quotient by a congruence relation. -/
def mk' [NonAssocSemiring R] (c : RingCon R) : R →+* c.Quotient where
  toFun := toQuotient
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
#align ring_con.mk' RingCon.mk'

end Quotient

/-! ### Lattice structure

The API in this section is copied from `Mathlib/GroupTheory/Congruence.lean`
-/


section Lattice

variable [Add R] [Mul R]

/-- For congruence relations `c, d` on a type `M` with multiplication and addition, `c ≤ d` iff
`∀ x y ∈ M`, `x` is related to `y` by `d` if `x` is related to `y` by `c`. -/
instance : LE (RingCon R) where
  le c d := ∀ ⦃x y⦄, c x y → d x y

/-- Definition of `≤` for congruence relations. -/
theorem le_def {c d : RingCon R} : c ≤ d ↔ ∀ {x y}, c x y → d x y :=
  Iff.rfl

/-- The infimum of a set of congruence relations on a given type with multiplication and
addition. -/
instance : InfSet (RingCon R) where
  sInf S :=
    { r := fun x y => ∀ c : RingCon R, c ∈ S → c x y
      iseqv :=
        ⟨fun x c _hc => c.refl x, fun h c hc => c.symm <| h c hc, fun h1 h2 c hc =>
          c.trans (h1 c hc) <| h2 c hc⟩
      add' := fun h1 h2 c hc => c.add (h1 c hc) <| h2 c hc
      mul' := fun h1 h2 c hc => c.mul (h1 c hc) <| h2 c hc }

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
    under the map to the underlying equivalence relation. -/
theorem sInf_toSetoid (S : Set (RingCon R)) : (sInf S).toSetoid = sInf ((·.toSetoid) '' S) :=
  Setoid.ext' fun x y =>
    ⟨fun h r ⟨c, hS, hr⟩ => by rw [← hr]; exact h c hS, fun h c hS => h c.toSetoid ⟨c, hS, rfl⟩⟩

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
    under the map to the underlying binary relation. -/
@[simp, norm_cast]
theorem coe_sInf (S : Set (RingCon R)) : ⇑(sInf S) = sInf ((⇑) '' S) := by
  ext; simp only [sInf_image, iInf_apply, iInf_Prop_eq]; rfl

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} (f : ι → RingCon R) : ⇑(iInf f) = ⨅ i, ⇑(f i) := by
  rw [iInf, coe_sInf, ← Set.range_comp, sInf_range, Function.comp]

instance : PartialOrder (RingCon R) where
  le_refl _c _ _ := id
  le_trans _c1 _c2 _c3 h1 h2 _x _y h := h2 <| h1 h
  le_antisymm _c _d hc hd := ext fun _x _y => ⟨fun h => hc h, fun h => hd h⟩

/-- The complete lattice of congruence relations on a given type with multiplication and
addition. -/
instance : CompleteLattice (RingCon R) where
  __ := completeLatticeOfInf (RingCon R) fun s =>
    ⟨fun r hr x y h => (h : ∀ r ∈ s, (r : RingCon R) x y) r hr,
      fun _r hr _x _y h _r' hr' => hr hr' h⟩
  inf c d :=
    { toSetoid := c.toSetoid ⊓ d.toSetoid
      mul' := fun h1 h2 => ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩
      add' := fun h1 h2 => ⟨c.add h1.1 h2.1, d.add h1.2 h2.2⟩ }
  inf_le_left _ _ := fun _ _ h => h.1
  inf_le_right _ _ := fun _ _ h => h.2
  le_inf _ _ _ hb hc := fun _ _ h => ⟨hb h, hc h⟩
  top :=
    { (⊤ : Setoid R) with
      mul' := fun _ _ => trivial
      add' := fun _ _ => trivial }
  le_top _ := fun _ _ _h => trivial
  bot :=
    { (⊥ : Setoid R) with
      mul' := congr_arg₂ _
      add' := congr_arg₂ _ }
  bot_le c := fun x _y h => h ▸ c.refl x

@[simp, norm_cast]
theorem coe_top : ⇑(⊤ : RingCon R) = ⊤ := rfl

@[simp, norm_cast]
theorem coe_bot : ⇑(⊥ : RingCon R) = Eq := rfl

/-- The infimum of two congruence relations equals the infimum of the underlying binary
operations. -/
@[simp, norm_cast]
theorem coe_inf {c d : RingCon R} : ⇑(c ⊓ d) = ⇑c ⊓ ⇑d := rfl

/-- Definition of the infimum of two congruence relations. -/
theorem inf_iff_and {c d : RingCon R} {x y} : (c ⊓ d) x y ↔ c x y ∧ d x y :=
  Iff.rfl

instance [Nontrivial R] : Nontrivial (RingCon R) where
  exists_pair_ne :=
    let ⟨x, y, ne⟩ := exists_pair_ne R
    ⟨⊥, ⊤, ne_of_apply_ne (· x y) <| by simp [ne]⟩

/-- The inductively defined smallest congruence relation containing a binary relation `r` equals
    the infimum of the set of congruence relations containing `r`. -/
theorem ringConGen_eq (r : R → R → Prop) :
    ringConGen r = sInf {s : RingCon R | ∀ x y, r x y → s x y} :=
  le_antisymm
    (fun _x _y H =>
      RingConGen.Rel.recOn H (fun _ _ h _ hs => hs _ _ h) (RingCon.refl _)
        (fun _ => RingCon.symm _) (fun _ _ => RingCon.trans _)
        (fun _ _ h1 h2 c hc => c.add (h1 c hc) <| h2 c hc)
        (fun _ _ h1 h2 c hc => c.mul (h1 c hc) <| h2 c hc))
    (sInf_le fun _ _ => RingConGen.Rel.of _ _)

/-- The smallest congruence relation containing a binary relation `r` is contained in any
    congruence relation containing `r`. -/
theorem ringConGen_le {r : R → R → Prop} {c : RingCon R}
    (h : ∀ x y, r x y → c x y) : ringConGen r ≤ c := by
  rw [ringConGen_eq]; exact sInf_le h

/-- Given binary relations `r, s` with `r` contained in `s`, the smallest congruence relation
    containing `s` contains the smallest congruence relation containing `r`. -/
theorem ringConGen_mono {r s : R → R → Prop} (h : ∀ x y, r x y → s x y) :
    ringConGen r ≤ ringConGen s :=
  ringConGen_le fun x y hr => RingConGen.Rel.of _ _ <| h x y hr

/-- Congruence relations equal the smallest congruence relation in which they are contained. -/
theorem ringConGen_of_ringCon (c : RingCon R) : ringConGen c = c :=
  le_antisymm (by rw [ringConGen_eq]; exact sInf_le fun _ _ => id) RingConGen.Rel.of

/-- The map sending a binary relation to the smallest congruence relation in which it is
    contained is idempotent. -/
theorem ringConGen_idem (r : R → R → Prop) : ringConGen (ringConGen r) = ringConGen r :=
  ringConGen_of_ringCon _

/-- The supremum of congruence relations `c, d` equals the smallest congruence relation containing
    the binary relation '`x` is related to `y` by `c` or `d`'. -/
theorem sup_eq_ringConGen (c d : RingCon R) : c ⊔ d = ringConGen fun x y => c x y ∨ d x y := by
  rw [ringConGen_eq]
  apply congr_arg sInf
  simp only [le_def, or_imp, ← forall_and]

/-- The supremum of two congruence relations equals the smallest congruence relation containing
    the supremum of the underlying binary operations. -/
theorem sup_def {c d : RingCon R} : c ⊔ d = ringConGen (⇑c ⊔ ⇑d) := by
  rw [sup_eq_ringConGen]; rfl

/-- The supremum of a set of congruence relations `S` equals the smallest congruence relation
    containing the binary relation 'there exists `c ∈ S` such that `x` is related to `y` by
    `c`'. -/
theorem sSup_eq_ringConGen (S : Set (RingCon R)) :
    sSup S = ringConGen fun x y => ∃ c : RingCon R, c ∈ S ∧ c x y := by
  rw [ringConGen_eq]
  apply congr_arg sInf
  ext
  exact ⟨fun h _ _ ⟨r, hr⟩ => h hr.1 hr.2, fun h r hS _ _ hr => h _ _ ⟨r, hS, hr⟩⟩

/-- The supremum of a set of congruence relations is the same as the smallest congruence relation
    containing the supremum of the set's image under the map to the underlying binary relation. -/
theorem sSup_def {S : Set (RingCon R)} :
    sSup S = ringConGen (sSup (@Set.image (RingCon R) (R → R → Prop) (⇑) S)) := by
  rw [sSup_eq_ringConGen, sSup_image]
  congr with (x y)
  simp only [sSup_image, iSup_apply, iSup_Prop_eq, exists_prop, rel_eq_coe]

variable (R)

/-- There is a Galois insertion of congruence relations on a type with multiplication and addition
`R` into binary relations on `R`. -/
protected def gi : @GaloisInsertion (R → R → Prop) (RingCon R) _ _ ringConGen (⇑) where
  choice r _h := ringConGen r
  gc _r c :=
    ⟨fun H _ _ h => H <| RingConGen.Rel.of _ _ h, fun H =>
      ringConGen_of_ringCon c ▸ ringConGen_mono H⟩
  le_l_u x := (ringConGen_of_ringCon x).symm ▸ le_refl x
  choice_eq _ _ := rfl

end Lattice

end RingCon
