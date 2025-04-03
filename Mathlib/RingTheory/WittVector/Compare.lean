/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathlib.RingTheory.WittVector.Truncated
import Mathlib.RingTheory.WittVector.Identities
import Mathlib.NumberTheory.Padics.RingHoms

#align_import ring_theory.witt_vector.compare from "leanprover-community/mathlib"@"168ad7fc5d8173ad38be9767a22d50b8ecf1cd00"

/-!

# Comparison isomorphism between `WittVector p (ZMod p)` and `ℤ_[p]`

We construct a ring isomorphism between `WittVector p (ZMod p)` and `ℤ_[p]`.
This isomorphism follows from the fact that both satisfy the universal property
of the inverse limit of `ZMod (p^n)`.

## Main declarations

* `WittVector.toZModPow`: a family of compatible ring homs `𝕎 (ZMod p) → ZMod (p^k)`
* `WittVector.equiv`: the isomorphism

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

namespace TruncatedWittVector

variable (p) (n : ℕ) (R : Type*) [CommRing R]

theorem eq_of_le_of_cast_pow_eq_zero [CharP R p] (i : ℕ) (hin : i ≤ n)
    (hpi : (p : TruncatedWittVector p n R) ^ i = 0) : i = n := by
  contrapose! hpi
  replace hin := lt_of_le_of_ne hin hpi; clear hpi
  have : (p : TruncatedWittVector p n R) ^ i = WittVector.truncate n ((p : 𝕎 R) ^ i) := by
    rw [RingHom.map_pow, map_natCast]
  rw [this, ne_eq, ext_iff, not_forall]; clear this
  use ⟨i, hin⟩
  rw [WittVector.coeff_truncate, coeff_zero, Fin.val_mk, WittVector.coeff_p_pow]
  haveI : Nontrivial R := CharP.nontrivial_of_char_ne_one hp.1.ne_one
  exact one_ne_zero
#align truncated_witt_vector.eq_of_le_of_cast_pow_eq_zero TruncatedWittVector.eq_of_le_of_cast_pow_eq_zero

section Iso

variable {R}

theorem card_zmod : Fintype.card (TruncatedWittVector p n (ZMod p)) = p ^ n := by
  rw [card, ZMod.card]
#align truncated_witt_vector.card_zmod TruncatedWittVector.card_zmod

theorem charP_zmod : CharP (TruncatedWittVector p n (ZMod p)) (p ^ n) :=
  charP_of_prime_pow_injective _ _ _ (card_zmod _ _) (eq_of_le_of_cast_pow_eq_zero p n (ZMod p))
#align truncated_witt_vector.char_p_zmod TruncatedWittVector.charP_zmod

attribute [local instance] charP_zmod

/-- The unique isomorphism between `ZMod p^n` and `TruncatedWittVector p n (ZMod p)`.

This isomorphism exists, because `TruncatedWittVector p n (ZMod p)` is a finite ring
with characteristic and cardinality `p^n`.
-/
def zmodEquivTrunc : ZMod (p ^ n) ≃+* TruncatedWittVector p n (ZMod p) :=
  ZMod.ringEquiv (TruncatedWittVector p n (ZMod p)) (card_zmod _ _)
#align truncated_witt_vector.zmod_equiv_trunc TruncatedWittVector.zmodEquivTrunc

theorem zmodEquivTrunc_apply {x : ZMod (p ^ n)} :
    zmodEquivTrunc p n x = ZMod.castHom (by rfl) (TruncatedWittVector p n (ZMod p)) x :=
  rfl
#align truncated_witt_vector.zmod_equiv_trunc_apply TruncatedWittVector.zmodEquivTrunc_apply

/-- The following diagram commutes:
```text
          zmod (p^n) ----------------------------> zmod (p^m)
            |                                        |
            |                                        |
            v                                        v
TruncatedWittVector p n (zmod p) ----> TruncatedWittVector p m (zmod p)
```
Here the vertical arrows are `TruncatedWittVector.zmodEquivTrunc`,
the horizontal arrow at the top is `ZMod.castHom`,
and the horizontal arrow at the bottom is `TruncatedWittVector.truncate`.
-/
theorem commutes {m : ℕ} (hm : n ≤ m) :
    (truncate hm).comp (zmodEquivTrunc p m).toRingHom =
      (zmodEquivTrunc p n).toRingHom.comp (ZMod.castHom (pow_dvd_pow p hm) _) :=
  RingHom.ext_zmod _ _
#align truncated_witt_vector.commutes TruncatedWittVector.commutes

theorem commutes' {m : ℕ} (hm : n ≤ m) (x : ZMod (p ^ m)) :
    truncate hm (zmodEquivTrunc p m x) = zmodEquivTrunc p n (ZMod.castHom (pow_dvd_pow p hm) _ x) :=
  show (truncate hm).comp (zmodEquivTrunc p m).toRingHom x = _ by rw [commutes _ _ hm]; rfl
#align truncated_witt_vector.commutes' TruncatedWittVector.commutes'

theorem commutes_symm' {m : ℕ} (hm : n ≤ m) (x : TruncatedWittVector p m (ZMod p)) :
    (zmodEquivTrunc p n).symm (truncate hm x) =
      ZMod.castHom (pow_dvd_pow p hm) _ ((zmodEquivTrunc p m).symm x) := by
  apply (zmodEquivTrunc p n).injective
  rw [← commutes' _ _ hm]
  simp
#align truncated_witt_vector.commutes_symm' TruncatedWittVector.commutes_symm'

/-- The following diagram commutes:
```text
TruncatedWittVector p n (zmod p) ----> TruncatedWittVector p m (zmod p)
            |                                        |
            |                                        |
            v                                        v
          zmod (p^n) ----------------------------> zmod (p^m)
```
Here the vertical arrows are `(TruncatedWittVector.zmodEquivTrunc p _).symm`,
the horizontal arrow at the top is `ZMod.castHom`,
and the horizontal arrow at the bottom is `TruncatedWittVector.truncate`.
-/
theorem commutes_symm {m : ℕ} (hm : n ≤ m) :
    (zmodEquivTrunc p n).symm.toRingHom.comp (truncate hm) =
      (ZMod.castHom (pow_dvd_pow p hm) _).comp (zmodEquivTrunc p m).symm.toRingHom := by
  ext; apply commutes_symm'
#align truncated_witt_vector.commutes_symm TruncatedWittVector.commutes_symm

end Iso

end TruncatedWittVector

namespace WittVector

open TruncatedWittVector

variable (p)

/-- `toZModPow` is a family of compatible ring homs. We get this family by composing
`TruncatedWittVector.zmodEquivTrunc` (in right-to-left direction) with `WittVector.truncate`. -/
def toZModPow (k : ℕ) : 𝕎 (ZMod p) →+* ZMod (p ^ k) :=
  (zmodEquivTrunc p k).symm.toRingHom.comp (truncate k)
#align witt_vector.to_zmod_pow WittVector.toZModPow

theorem toZModPow_compat (m n : ℕ) (h : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (toZModPow p n) = toZModPow p m :=
  calc
    (ZMod.castHom _ (ZMod (p ^ m))).comp ((zmodEquivTrunc p n).symm.toRingHom.comp (truncate n))
    _ = ((zmodEquivTrunc p m).symm.toRingHom.comp (TruncatedWittVector.truncate h)).comp
          (truncate n) := by
      rw [commutes_symm, RingHom.comp_assoc]
    _ = (zmodEquivTrunc p m).symm.toRingHom.comp (truncate m) := by
      rw [RingHom.comp_assoc, truncate_comp_wittVector_truncate]
#align witt_vector.to_zmod_pow_compat WittVector.toZModPow_compat

/-- `toPadicInt` lifts `toZModPow : 𝕎 (ZMod p) →+* ZMod (p ^ k)` to a ring hom to `ℤ_[p]`
using `PadicInt.lift`, the universal property of `ℤ_[p]`.
-/
def toPadicInt : 𝕎 (ZMod p) →+* ℤ_[p] :=
  PadicInt.lift <| toZModPow_compat p
#align witt_vector.to_padic_int WittVector.toPadicInt

theorem zmodEquivTrunc_compat (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂) :
    (TruncatedWittVector.truncate hk).comp
        ((zmodEquivTrunc p k₂).toRingHom.comp (PadicInt.toZModPow k₂)) =
      (zmodEquivTrunc p k₁).toRingHom.comp (PadicInt.toZModPow k₁) := by
  rw [← RingHom.comp_assoc, commutes, RingHom.comp_assoc,
    PadicInt.zmod_cast_comp_toZModPow _ _ hk]
#align witt_vector.zmod_equiv_trunc_compat WittVector.zmodEquivTrunc_compat

/-- `fromPadicInt` uses `WittVector.lift` to lift `TruncatedWittVector.zmodEquivTrunc`
composed with `PadicInt.toZModPow` to a ring hom `ℤ_[p] →+* 𝕎 (ZMod p)`.
-/
def fromPadicInt : ℤ_[p] →+* 𝕎 (ZMod p) :=
  (WittVector.lift fun k => (zmodEquivTrunc p k).toRingHom.comp (PadicInt.toZModPow k)) <|
    zmodEquivTrunc_compat _
#align witt_vector.from_padic_int WittVector.fromPadicInt

theorem toPadicInt_comp_fromPadicInt : (toPadicInt p).comp (fromPadicInt p) = RingHom.id ℤ_[p] := by
  rw [← PadicInt.toZModPow_eq_iff_ext]
  intro n
  rw [← RingHom.comp_assoc, toPadicInt, PadicInt.lift_spec]
  simp only [fromPadicInt, toZModPow, RingHom.comp_id]
  rw [RingHom.comp_assoc, truncate_comp_lift, ← RingHom.comp_assoc]
  simp only [RingEquiv.symm_toRingHom_comp_toRingHom, RingHom.id_comp]
#align witt_vector.to_padic_int_comp_from_padic_int WittVector.toPadicInt_comp_fromPadicInt

theorem toPadicInt_comp_fromPadicInt_ext (x) :
    (toPadicInt p).comp (fromPadicInt p) x = RingHom.id ℤ_[p] x := by
  rw [toPadicInt_comp_fromPadicInt]
#align witt_vector.to_padic_int_comp_from_padic_int_ext WittVector.toPadicInt_comp_fromPadicInt_ext

theorem fromPadicInt_comp_toPadicInt :
    (fromPadicInt p).comp (toPadicInt p) = RingHom.id (𝕎 (ZMod p)) := by
  apply WittVector.hom_ext
  intro n
  rw [fromPadicInt, ← RingHom.comp_assoc, truncate_comp_lift, RingHom.comp_assoc]
  simp only [toPadicInt, toZModPow, RingHom.comp_id, PadicInt.lift_spec, RingHom.id_comp, ←
    RingHom.comp_assoc, RingEquiv.toRingHom_comp_symm_toRingHom]
#align witt_vector.from_padic_int_comp_to_padic_int WittVector.fromPadicInt_comp_toPadicInt

theorem fromPadicInt_comp_toPadicInt_ext (x) :
    (fromPadicInt p).comp (toPadicInt p) x = RingHom.id (𝕎 (ZMod p)) x := by
  rw [fromPadicInt_comp_toPadicInt]
#align witt_vector.from_padic_int_comp_to_padic_int_ext WittVector.fromPadicInt_comp_toPadicInt_ext

/-- The ring of Witt vectors over `ZMod p` is isomorphic to the ring of `p`-adic integers. This
equivalence is witnessed by `WittVector.toPadicInt` with inverse `WittVector.fromPadicInt`.
-/
def equiv : 𝕎 (ZMod p) ≃+* ℤ_[p] where
  toFun := toPadicInt p
  invFun := fromPadicInt p
  left_inv := fromPadicInt_comp_toPadicInt_ext _
  right_inv := toPadicInt_comp_fromPadicInt_ext _
  map_mul' := RingHom.map_mul _
  map_add' := RingHom.map_add _
#align witt_vector.equiv WittVector.equiv

end WittVector
