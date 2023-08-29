/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.RingTheory.IntegralClosure
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FieldSimp

#align_import ring_theory.fractional_ideal from "leanprover-community/mathlib"@"ed90a7d327c3a5caf65a6faf7e8a0d63c4605df7"

/-!
# Fractional ideals

This file defines fractional ideals of an integral domain and proves basic facts about them.

## Main definitions
Let `S` be a submonoid of an integral domain `R`, `P` the localization of `R` at `S`, and `f` the
natural ring hom from `R` to `P`.
 * `IsFractional` defines which `R`-submodules of `P` are fractional ideals
 * `FractionalIdeal S P` is the type of fractional ideals in `P`
 * a coercion `coeIdeal : Ideal R → FractionalIdeal S P`
 * `CommSemiring (FractionalIdeal S P)` instance:
   the typical ideal operations generalized to fractional ideals
 * `Lattice (FractionalIdeal S P)` instance
 * `map` is the pushforward of a fractional ideal along an algebra morphism

Let `K` be the localization of `R` at `R⁰ = R \ {0}` (i.e. the field of fractions).
 * `FractionalIdeal R⁰ K` is the type of fractional ideals in the field of fractions
 * `Div (FractionalIdeal R⁰ K)` instance:
   the ideal quotient `I / J` (typically written $I : J$, but a `:` operator cannot be defined)

## Main statements

  * `mul_left_mono` and `mul_right_mono` state that ideal multiplication is monotone
  * `mul_div_self_cancel_iff` states that `1 / I` is the inverse of `I` if one exists
  * `isNoetherian` states that every fractional ideal of a noetherian integral domain is noetherian

## Implementation notes

Fractional ideals are considered equal when they contain the same elements,
independent of the denominator `a : R` such that `a I ⊆ R`.
Thus, we define `FractionalIdeal` to be the subtype of the predicate `IsFractional`,
instead of having `FractionalIdeal` be a structure of which `a` is a field.

Most definitions in this file specialize operations from submodules to fractional ideals,
proving that the result of this operation is fractional if the input is fractional.
Exceptions to this rule are defining `(+) := (⊔)` and `⊥ := 0`,
in order to re-use their respective proof terms.
We can still use `simp` to show `↑I + ↑J = ↑(I + J)` and `↑⊥ = ↑0`.

Many results in fact do not need that `P` is a localization, only that `P` is an
`R`-algebra. We omit the `IsLocalization` parameter whenever this is practical.
Similarly, we don't assume that the localization is a field until we need it to
define ideal quotients. When this assumption is needed, we replace `S` with `R⁰`,
making the localization a field.

## References

  * https://en.wikipedia.org/wiki/Fractional_ideal

## Tags

fractional ideal, fractional ideals, invertible ideal
-/


open IsLocalization

open Pointwise

open nonZeroDivisors

section Defs

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P]

variable [Algebra R P]

variable (S)

/-- A submodule `I` is a fractional ideal if `a I ⊆ R` for some `a ≠ 0`. -/
def IsFractional (I : Submodule R P) :=
  ∃ a ∈ S, ∀ b ∈ I, IsInteger R (a • b)
#align is_fractional IsFractional

variable (P)

/-- The fractional ideals of a domain `R` are ideals of `R` divided by some `a ∈ R`.

More precisely, let `P` be a localization of `R` at some submonoid `S`,
then a fractional ideal `I ⊆ P` is an `R`-submodule of `P`,
such that there is a nonzero `a : R` with `a I ⊆ R`.
-/
def FractionalIdeal :=
  { I : Submodule R P // IsFractional S I }
#align fractional_ideal FractionalIdeal

end Defs

namespace FractionalIdeal

open Set

open Submodule

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P]

variable [Algebra R P] [loc : IsLocalization S P]

/-- Map a fractional ideal `I` to a submodule by forgetting that `∃ a, a I ⊆ R`.

This implements the coercion `FractionalIdeal S P → Submodule R P`.
-/
@[coe]
def coeToSubmodule (I : FractionalIdeal S P) : Submodule R P :=
  I.val

/-- Map a fractional ideal `I` to a submodule by forgetting that `∃ a, a I ⊆ R`.

This coercion is typically called `coeToSubmodule` in lemma names
(or `coe` when the coercion is clear from the context),
not to be confused with `IsLocalization.coeSubmodule : Ideal R → Submodule R P`
(which we use to define `coe : Ideal R → FractionalIdeal S P`).
-/
instance : CoeOut (FractionalIdeal S P) (Submodule R P) :=
  ⟨coeToSubmodule⟩

protected theorem isFractional (I : FractionalIdeal S P) : IsFractional S (I : Submodule R P) :=
  I.prop
#align fractional_ideal.is_fractional FractionalIdeal.isFractional

section SetLike

instance : SetLike (FractionalIdeal S P) P where
  coe I := ↑(I : Submodule R P)
  coe_injective' := SetLike.coe_injective.comp Subtype.coe_injective

@[simp]
theorem mem_coe {I : FractionalIdeal S P} {x : P} : x ∈ (I : Submodule R P) ↔ x ∈ I :=
  Iff.rfl
#align fractional_ideal.mem_coe FractionalIdeal.mem_coe

@[ext]
theorem ext {I J : FractionalIdeal S P} : (∀ x, x ∈ I ↔ x ∈ J) → I = J :=
  SetLike.ext
#align fractional_ideal.ext FractionalIdeal.ext

/-- Copy of a `FractionalIdeal` with a new underlying set equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (p : FractionalIdeal S P) (s : Set P) (hs : s = ↑p) : FractionalIdeal S P :=
  ⟨Submodule.copy p s hs, by
    convert p.isFractional
    -- ⊢ Submodule.copy (↑p) s hs = ↑p
    ext
    -- ⊢ x✝ ∈ Submodule.copy (↑p) s hs ↔ x✝ ∈ ↑p
    simp only [hs]
    -- ⊢ x✝ ∈ Submodule.copy ↑p ↑p (_ : ↑p = ↑↑p) ↔ x✝ ∈ ↑p
    rfl⟩
    -- 🎉 no goals
#align fractional_ideal.copy FractionalIdeal.copy

@[simp]
theorem coe_copy (p : FractionalIdeal S P) (s : Set P) (hs : s = ↑p) : ↑(p.copy s hs) = s :=
  rfl
#align fractional_ideal.coe_copy FractionalIdeal.coe_copy

theorem coe_eq (p : FractionalIdeal S P) (s : Set P) (hs : s = ↑p) : p.copy s hs = p :=
  SetLike.coe_injective hs
#align fractional_ideal.coe_eq FractionalIdeal.coe_eq

end SetLike

-- Porting note: this seems to be needed a lot more than in Lean 3
@[simp]
theorem val_eq_coe (I : FractionalIdeal S P) : I.val = I :=
  rfl
#align fractional_ideal.val_eq_coe FractionalIdeal.val_eq_coe

-- Porting note: had to rephrase this to make it clear to `simp` what was going on.
@[simp, norm_cast]
theorem coe_mk (I : Submodule R P) (hI : IsFractional S I) :
    coeToSubmodule ⟨I, hI⟩ = I :=
  rfl
#align fractional_ideal.coe_mk FractionalIdeal.coe_mk

-- Porting note: added this lemma because Lean can't see through the composition of coercions.
theorem coeToSet_coeToSubmodule (I : FractionalIdeal S P) :
    ((I : Submodule R P) : Set P) = I :=
  rfl

/-! Transfer instances from `Submodule R P` to `FractionalIdeal S P`. -/

instance (I : FractionalIdeal S P) : AddCommGroup I :=
  Submodule.addCommGroup (I : Submodule R P)

instance (I : FractionalIdeal S P) : Module R I :=
  Submodule.module (I : Submodule R P)

theorem coeToSubmodule_injective :
    Function.Injective (fun (I : FractionalIdeal S P) ↦ (I : Submodule R P)) :=
  Subtype.coe_injective
#align fractional_ideal.coe_to_submodule_injective FractionalIdeal.coeToSubmodule_injective

theorem coeToSubmodule_inj {I J : FractionalIdeal S P} : (I : Submodule R P) = J ↔ I = J :=
  coeToSubmodule_injective.eq_iff
#align fractional_ideal.coe_to_submodule_inj FractionalIdeal.coeToSubmodule_inj

theorem isFractional_of_le_one (I : Submodule R P) (h : I ≤ 1) : IsFractional S I := by
  use 1, S.one_mem
  -- ⊢ ∀ (b : P), b ∈ I → IsInteger R (1 • b)
  intro b hb
  -- ⊢ IsInteger R (1 • b)
  rw [one_smul]
  -- ⊢ IsInteger R b
  obtain ⟨b', b'_mem, rfl⟩ := h hb
  -- ⊢ IsInteger R (↑(Algebra.linearMap R P) b')
  exact Set.mem_range_self b'
  -- 🎉 no goals
#align fractional_ideal.is_fractional_of_le_one FractionalIdeal.isFractional_of_le_one

theorem isFractional_of_le {I : Submodule R P} {J : FractionalIdeal S P} (hIJ : I ≤ J) :
    IsFractional S I := by
  obtain ⟨a, a_mem, ha⟩ := J.isFractional
  -- ⊢ IsFractional S I
  use a, a_mem
  -- ⊢ ∀ (b : P), b ∈ I → IsInteger R (a • b)
  intro b b_mem
  -- ⊢ IsInteger R (a • b)
  exact ha b (hIJ b_mem)
  -- 🎉 no goals
#align fractional_ideal.is_fractional_of_le FractionalIdeal.isFractional_of_le

/-- Map an ideal `I` to a fractional ideal by forgetting `I` is integral.

This is the function that implements the coercion `Ideal R → FractionalIdeal S P`. -/
@[coe]
def coeIdeal (I : Ideal R) : FractionalIdeal S P :=
  ⟨coeSubmodule P I,
   isFractional_of_le_one _ <| by simpa using coeSubmodule_mono P (le_top : I ≤ ⊤)⟩
                                  -- 🎉 no goals

-- Is a `CoeTC` rather than `Coe` to speed up failing inference, see library note [use has_coe_t]
/-- Map an ideal `I` to a fractional ideal by forgetting `I` is integral.

This is a bundled version of `IsLocalization.coeSubmodule : Ideal R → Submodule R P`,
which is not to be confused with the `coe : FractionalIdeal S P → Submodule R P`,
also called `coeToSubmodule` in theorem names.

This map is available as a ring hom, called `FractionalIdeal.coeIdealHom`.
-/
instance : CoeTC (Ideal R) (FractionalIdeal S P) :=
  ⟨fun I => coeIdeal I⟩

@[simp, norm_cast]
theorem coe_coeIdeal (I : Ideal R) :
    ((I : FractionalIdeal S P) : Submodule R P) = coeSubmodule P I :=
  rfl
#align fractional_ideal.coe_coe_ideal FractionalIdeal.coe_coeIdeal

variable (S)

@[simp]
theorem mem_coeIdeal {x : P} {I : Ideal R} :
    x ∈ (I : FractionalIdeal S P) ↔ ∃ x', x' ∈ I ∧ algebraMap R P x' = x :=
  mem_coeSubmodule _ _
#align fractional_ideal.mem_coe_ideal FractionalIdeal.mem_coeIdeal

theorem mem_coeIdeal_of_mem {x : R} {I : Ideal R} (hx : x ∈ I) :
    algebraMap R P x ∈ (I : FractionalIdeal S P) :=
  (mem_coeIdeal S).mpr ⟨x, hx, rfl⟩
#align fractional_ideal.mem_coe_ideal_of_mem FractionalIdeal.mem_coeIdeal_of_mem

theorem coeIdeal_le_coeIdeal' [IsLocalization S P] (h : S ≤ nonZeroDivisors R) {I J : Ideal R} :
    (I : FractionalIdeal S P) ≤ J ↔ I ≤ J :=
  coeSubmodule_le_coeSubmodule h
#align fractional_ideal.coe_ideal_le_coe_ideal' FractionalIdeal.coeIdeal_le_coeIdeal'

@[simp]
theorem coeIdeal_le_coeIdeal (K : Type*) [CommRing K] [Algebra R K] [IsFractionRing R K]
    {I J : Ideal R} : (I : FractionalIdeal R⁰ K) ≤ J ↔ I ≤ J :=
  IsFractionRing.coeSubmodule_le_coeSubmodule
#align fractional_ideal.coe_ideal_le_coe_ideal FractionalIdeal.coeIdeal_le_coeIdeal

instance : Zero (FractionalIdeal S P) :=
  ⟨(0 : Ideal R)⟩

@[simp]
theorem mem_zero_iff {x : P} : x ∈ (0 : FractionalIdeal S P) ↔ x = 0 :=
  ⟨fun ⟨x', x'_mem_zero, x'_eq_x⟩ => by
    have x'_eq_zero : x' = 0 := x'_mem_zero
    -- ⊢ x = 0
    simp [x'_eq_x.symm, x'_eq_zero], fun hx => ⟨0, rfl, by simp [hx]⟩⟩
    -- 🎉 no goals
                                                           -- 🎉 no goals
#align fractional_ideal.mem_zero_iff FractionalIdeal.mem_zero_iff

variable {S}

@[simp, norm_cast]
theorem coe_zero : ↑(0 : FractionalIdeal S P) = (⊥ : Submodule R P) :=
  Submodule.ext fun _ => mem_zero_iff S
#align fractional_ideal.coe_zero FractionalIdeal.coe_zero

@[simp, norm_cast]
theorem coeIdeal_bot : ((⊥ : Ideal R) : FractionalIdeal S P) = 0 :=
  rfl
#align fractional_ideal.coe_ideal_bot FractionalIdeal.coeIdeal_bot

variable (P)

@[simp]
theorem exists_mem_algebraMap_eq {x : R} {I : Ideal R} (h : S ≤ nonZeroDivisors R) :
    (∃ x', x' ∈ I ∧ algebraMap R P x' = algebraMap R P x) ↔ x ∈ I :=
  ⟨fun ⟨_, hx', Eq⟩ => IsLocalization.injective _ h Eq ▸ hx', fun h => ⟨x, h, rfl⟩⟩
#align fractional_ideal.exists_mem_to_map_eq FractionalIdeal.exists_mem_algebraMap_eq

variable {P}

theorem coeIdeal_injective' (h : S ≤ nonZeroDivisors R) :
    Function.Injective (fun (I : Ideal R) ↦ (I : FractionalIdeal S P)) := fun _ _ h' =>
  ((coeIdeal_le_coeIdeal' S h).mp h'.le).antisymm ((coeIdeal_le_coeIdeal' S h).mp
    h'.ge)
#align fractional_ideal.coe_ideal_injective' FractionalIdeal.coeIdeal_injective'

theorem coeIdeal_inj' (h : S ≤ nonZeroDivisors R) {I J : Ideal R} :
    (I : FractionalIdeal S P) = J ↔ I = J :=
  (coeIdeal_injective' h).eq_iff
#align fractional_ideal.coe_ideal_inj' FractionalIdeal.coeIdeal_inj'

-- Porting note: doesn't need to be @[simp] because it can be proved by coeIdeal_eq_zero
theorem coeIdeal_eq_zero' {I : Ideal R} (h : S ≤ nonZeroDivisors R) :
    (I : FractionalIdeal S P) = 0 ↔ I = (⊥ : Ideal R) :=
  coeIdeal_inj' h
#align fractional_ideal.coe_ideal_eq_zero' FractionalIdeal.coeIdeal_eq_zero'

theorem coeIdeal_ne_zero' {I : Ideal R} (h : S ≤ nonZeroDivisors R) :
    (I : FractionalIdeal S P) ≠ 0 ↔ I ≠ (⊥ : Ideal R) :=
  not_iff_not.mpr <| coeIdeal_eq_zero' h
#align fractional_ideal.coe_ideal_ne_zero' FractionalIdeal.coeIdeal_ne_zero'

theorem coeToSubmodule_eq_bot {I : FractionalIdeal S P} : (I : Submodule R P) = ⊥ ↔ I = 0 :=
  ⟨fun h => coeToSubmodule_injective (by simp [h]), fun h => by simp [h]⟩
                                         -- 🎉 no goals
                                                                -- 🎉 no goals
#align fractional_ideal.coe_to_submodule_eq_bot FractionalIdeal.coeToSubmodule_eq_bot

theorem coeToSubmodule_ne_bot {I : FractionalIdeal S P} : ↑I ≠ (⊥ : Submodule R P) ↔ I ≠ 0 :=
  not_iff_not.mpr coeToSubmodule_eq_bot
#align fractional_ideal.coe_to_submodule_ne_bot FractionalIdeal.coeToSubmodule_ne_bot

instance : Inhabited (FractionalIdeal S P) :=
  ⟨0⟩

instance : One (FractionalIdeal S P) :=
  ⟨(⊤ : Ideal R)⟩

variable (S)

@[simp, norm_cast]
theorem coeIdeal_top : ((⊤ : Ideal R) : FractionalIdeal S P) = 1 :=
  rfl
#align fractional_ideal.coe_ideal_top FractionalIdeal.coeIdeal_top

theorem mem_one_iff {x : P} : x ∈ (1 : FractionalIdeal S P) ↔ ∃ x' : R, algebraMap R P x' = x :=
  Iff.intro (fun ⟨x', _, h⟩ => ⟨x', h⟩) fun ⟨x', h⟩ => ⟨x', ⟨⟩, h⟩
#align fractional_ideal.mem_one_iff FractionalIdeal.mem_one_iff

theorem coe_mem_one (x : R) : algebraMap R P x ∈ (1 : FractionalIdeal S P) :=
  (mem_one_iff S).mpr ⟨x, rfl⟩
#align fractional_ideal.coe_mem_one FractionalIdeal.coe_mem_one

theorem one_mem_one : (1 : P) ∈ (1 : FractionalIdeal S P) :=
  (mem_one_iff S).mpr ⟨1, RingHom.map_one _⟩
#align fractional_ideal.one_mem_one FractionalIdeal.one_mem_one

variable {S}

/-- `(1 : FractionalIdeal S P)` is defined as the R-submodule `f(R) ≤ P`.

However, this is not definitionally equal to `1 : Submodule R P`,
which is proved in the actual `simp` lemma `coe_one`. -/
theorem coe_one_eq_coeSubmodule_top : ↑(1 : FractionalIdeal S P) = coeSubmodule P (⊤ : Ideal R) :=
  rfl
#align fractional_ideal.coe_one_eq_coe_submodule_top FractionalIdeal.coe_one_eq_coeSubmodule_top

@[simp, norm_cast]
theorem coe_one : (↑(1 : FractionalIdeal S P) : Submodule R P) = 1 := by
  rw [coe_one_eq_coeSubmodule_top, coeSubmodule_top]
  -- 🎉 no goals
#align fractional_ideal.coe_one FractionalIdeal.coe_one

section Lattice

/-!
### `Lattice` section

Defines the order on fractional ideals as inclusion of their underlying sets,
and ports the lattice structure on submodules to fractional ideals.
-/


@[simp]
theorem coe_le_coe {I J : FractionalIdeal S P} :
    (I : Submodule R P) ≤ (J : Submodule R P) ↔ I ≤ J :=
  Iff.rfl
#align fractional_ideal.coe_le_coe FractionalIdeal.coe_le_coe

theorem zero_le (I : FractionalIdeal S P) : 0 ≤ I := by
  intro x hx
  -- ⊢ x ∈ I
  -- Porting note: changed the proof from convert; simp into rw; exact
  rw [(mem_zero_iff _).mp hx]
  -- ⊢ 0 ∈ I
  exact zero_mem (I : Submodule R P)
  -- 🎉 no goals
#align fractional_ideal.zero_le FractionalIdeal.zero_le

instance orderBot : OrderBot (FractionalIdeal S P) where
  bot := 0
  bot_le := zero_le
#align fractional_ideal.order_bot FractionalIdeal.orderBot

@[simp]
theorem bot_eq_zero : (⊥ : FractionalIdeal S P) = 0 :=
  rfl
#align fractional_ideal.bot_eq_zero FractionalIdeal.bot_eq_zero

@[simp]
theorem le_zero_iff {I : FractionalIdeal S P} : I ≤ 0 ↔ I = 0 :=
  le_bot_iff
#align fractional_ideal.le_zero_iff FractionalIdeal.le_zero_iff

theorem eq_zero_iff {I : FractionalIdeal S P} : I = 0 ↔ ∀ x ∈ I, x = (0 : P) :=
  ⟨fun h x hx => by simpa [h, mem_zero_iff] using hx, fun h =>
                    -- 🎉 no goals
    le_bot_iff.mp fun x hx => (mem_zero_iff S).mpr (h x hx)⟩
#align fractional_ideal.eq_zero_iff FractionalIdeal.eq_zero_iff

theorem _root_.IsFractional.sup {I J : Submodule R P} :
    IsFractional S I → IsFractional S J → IsFractional S (I ⊔ J)
  | ⟨aI, haI, hI⟩, ⟨aJ, haJ, hJ⟩ =>
    ⟨aI * aJ, S.mul_mem haI haJ, fun b hb => by
      rcases mem_sup.mp hb with ⟨bI, hbI, bJ, hbJ, rfl⟩
      -- ⊢ IsInteger R ((aI * aJ) • (bI + bJ))
      rw [smul_add]
      -- ⊢ IsInteger R ((aI * aJ) • bI + (aI * aJ) • bJ)
      apply isInteger_add
      -- ⊢ IsInteger R ((aI * aJ) • bI)
      · rw [mul_smul, smul_comm]
        -- ⊢ IsInteger R (aJ • aI • bI)
        exact isInteger_smul (hI bI hbI)
        -- 🎉 no goals
      · rw [mul_smul]
        -- ⊢ IsInteger R (aI • aJ • bJ)
        exact isInteger_smul (hJ bJ hbJ)⟩
        -- 🎉 no goals
#align is_fractional.sup IsFractional.sup

theorem _root_.IsFractional.inf_right {I : Submodule R P} :
    IsFractional S I → ∀ J, IsFractional S (I ⊓ J)
  | ⟨aI, haI, hI⟩, J =>
    ⟨aI, haI, fun b hb => by
      rcases mem_inf.mp hb with ⟨hbI, _⟩
      -- ⊢ IsInteger R (aI • b)
      exact hI b hbI⟩
      -- 🎉 no goals
#align is_fractional.inf_right IsFractional.inf_right

instance : Inf (FractionalIdeal S P) :=
  ⟨fun I J => ⟨I ⊓ J, I.isFractional.inf_right J⟩⟩

@[simp, norm_cast]
theorem coe_inf (I J : FractionalIdeal S P) : ↑(I ⊓ J) = (I ⊓ J : Submodule R P) :=
  rfl
#align fractional_ideal.coe_inf FractionalIdeal.coe_inf

instance : Sup (FractionalIdeal S P) :=
  ⟨fun I J => ⟨I ⊔ J, I.isFractional.sup J.isFractional⟩⟩

@[norm_cast]
theorem coe_sup (I J : FractionalIdeal S P) : ↑(I ⊔ J) = (I ⊔ J : Submodule R P) :=
  rfl
#align fractional_ideal.coe_sup FractionalIdeal.coe_sup

instance lattice : Lattice (FractionalIdeal S P) :=
  Function.Injective.lattice _ Subtype.coe_injective coe_sup coe_inf
#align fractional_ideal.lattice FractionalIdeal.lattice

instance : SemilatticeSup (FractionalIdeal S P) :=
  { FractionalIdeal.lattice with }

end Lattice

section Semiring

instance : Add (FractionalIdeal S P) :=
  ⟨(· ⊔ ·)⟩

@[simp]
theorem sup_eq_add (I J : FractionalIdeal S P) : I ⊔ J = I + J :=
  rfl
#align fractional_ideal.sup_eq_add FractionalIdeal.sup_eq_add

@[simp, norm_cast]
theorem coe_add (I J : FractionalIdeal S P) : (↑(I + J) : Submodule R P) = I + J :=
  rfl
#align fractional_ideal.coe_add FractionalIdeal.coe_add

@[simp, norm_cast]
theorem coeIdeal_sup (I J : Ideal R) : ↑(I ⊔ J) = (I + J : FractionalIdeal S P) :=
  coeToSubmodule_injective <| coeSubmodule_sup _ _ _
#align fractional_ideal.coe_ideal_sup FractionalIdeal.coeIdeal_sup

theorem _root_.IsFractional.nsmul {I : Submodule R P} :
    ∀ n : ℕ, IsFractional S I → IsFractional S (n • I : Submodule R P)
  | 0, _ => by
    rw [zero_smul]
    -- ⊢ IsFractional S 0
    convert((0 : Ideal R) : FractionalIdeal S P).isFractional
    -- ⊢ 0 = ↑↑0
    simp
    -- 🎉 no goals
  | n + 1, h => by
    rw [succ_nsmul]
    -- ⊢ IsFractional S (I + n • I)
    exact h.sup (IsFractional.nsmul n h)
    -- 🎉 no goals
#align is_fractional.nsmul IsFractional.nsmul

instance : SMul ℕ (FractionalIdeal S P) where smul n I := ⟨n • ↑I, I.isFractional.nsmul n⟩

@[norm_cast]
theorem coe_nsmul (n : ℕ) (I : FractionalIdeal S P) :
    (↑(n • I) : Submodule R P) = n • (I : Submodule R P) :=
  rfl
#align fractional_ideal.coe_nsmul FractionalIdeal.coe_nsmul

theorem _root_.IsFractional.mul {I J : Submodule R P} :
    IsFractional S I → IsFractional S J → IsFractional S (I * J : Submodule R P)
  | ⟨aI, haI, hI⟩, ⟨aJ, haJ, hJ⟩ =>
    ⟨aI * aJ, S.mul_mem haI haJ, fun b hb => by
      refine Submodule.mul_induction_on hb ?_ ?_
      -- ⊢ ∀ (m : P), m ∈ I → ∀ (n : P), n ∈ J → IsInteger R ((aI * aJ) • (m * n))
      · intro m hm n hn
        -- ⊢ IsInteger R ((aI * aJ) • (m * n))
        obtain ⟨n', hn'⟩ := hJ n hn
        -- ⊢ IsInteger R ((aI * aJ) • (m * n))
        rw [mul_smul, mul_comm m, ← smul_mul_assoc, ← hn', ← Algebra.smul_def]
        -- ⊢ IsInteger R (aI • n' • m)
        apply hI
        -- ⊢ n' • m ∈ I
        exact Submodule.smul_mem _ _ hm
        -- 🎉 no goals
      · intro x y hx hy
        -- ⊢ IsInteger R ((aI * aJ) • (x + y))
        rw [smul_add]
        -- ⊢ IsInteger R ((aI * aJ) • x + (aI * aJ) • y)
        apply isInteger_add hx hy⟩
        -- 🎉 no goals
#align is_fractional.mul IsFractional.mul

theorem _root_.IsFractional.pow {I : Submodule R P} (h : IsFractional S I) :
    ∀ n : ℕ, IsFractional S (I ^ n : Submodule R P)
  | 0 => isFractional_of_le_one _ (pow_zero _).le
  | n + 1 => (pow_succ I n).symm ▸ h.mul (IsFractional.pow h n)
#align is_fractional.pow IsFractional.pow

/-- `FractionalIdeal.mul` is the product of two fractional ideals,
used to define the `Mul` instance.

This is only an auxiliary definition: the preferred way of writing `I.mul J` is `I * J`.

Elaborated terms involving `FractionalIdeal` tend to grow quite large,
so by making definitions irreducible, we hope to avoid deep unfolds.
-/
irreducible_def mul (lemma := mul_def') (I J : FractionalIdeal S P) : FractionalIdeal S P :=
  ⟨I * J, I.isFractional.mul J.isFractional⟩
#align fractional_ideal.mul FractionalIdeal.mul

-- local attribute [semireducible] mul
instance : Mul (FractionalIdeal S P) :=
  ⟨fun I J => mul I J⟩

@[simp]
theorem mul_eq_mul (I J : FractionalIdeal S P) : mul I J = I * J :=
  rfl
#align fractional_ideal.mul_eq_mul FractionalIdeal.mul_eq_mul

theorem mul_def (I J : FractionalIdeal S P) : I * J = ⟨I * J, I.isFractional.mul J.isFractional⟩ :=
  by simp only [← mul_eq_mul, mul]
     -- 🎉 no goals
#align fractional_ideal.mul_def FractionalIdeal.mul_def

@[simp, norm_cast]
theorem coe_mul (I J : FractionalIdeal S P) : (↑(I * J) : Submodule R P) = I * J := by
  simp only [mul_def]
  -- ⊢ ↑{ val := ↑I * ↑J, property := (_ : IsFractional S (↑I * ↑J)) } = ↑I * ↑J
  rfl
  -- 🎉 no goals
#align fractional_ideal.coe_mul FractionalIdeal.coe_mul

@[simp, norm_cast]
theorem coeIdeal_mul (I J : Ideal R) : (↑(I * J) : FractionalIdeal S P) = I * J := by
  simp only [mul_def]
  -- ⊢ ↑(I * J) = { val := ↑↑I * ↑↑J, property := (_ : IsFractional S (↑↑I * ↑↑J)) }
  exact coeToSubmodule_injective (coeSubmodule_mul _ _ _)
  -- 🎉 no goals
#align fractional_ideal.coe_ideal_mul FractionalIdeal.coeIdeal_mul

theorem mul_left_mono (I : FractionalIdeal S P) : Monotone ((· * ·) I) := by
  intro J J' h
  -- ⊢ (fun x x_1 => x * x_1) I J ≤ (fun x x_1 => x * x_1) I J'
  simp only [mul_def]
  -- ⊢ { val := ↑I * ↑J, property := (_ : IsFractional S (↑I * ↑J)) } ≤ { val := ↑I …
  exact mul_le.mpr fun x hx y hy => mul_mem_mul hx (h hy)
  -- 🎉 no goals
#align fractional_ideal.mul_left_mono FractionalIdeal.mul_left_mono

theorem mul_right_mono (I : FractionalIdeal S P) : Monotone fun J => J * I := by
  intro J J' h
  -- ⊢ (fun J => J * I) J ≤ (fun J => J * I) J'
  simp only [mul_def]
  -- ⊢ { val := ↑J * ↑I, property := (_ : IsFractional S (↑J * ↑I)) } ≤ { val := ↑J …
  exact mul_le.mpr fun x hx y hy => mul_mem_mul (h hx) hy
  -- 🎉 no goals
#align fractional_ideal.mul_right_mono FractionalIdeal.mul_right_mono

theorem mul_mem_mul {I J : FractionalIdeal S P} {i j : P} (hi : i ∈ I) (hj : j ∈ J) :
    i * j ∈ I * J := by
  simp only [mul_def]
  -- ⊢ i * j ∈ { val := ↑I * ↑J, property := (_ : IsFractional S (↑I * ↑J)) }
  exact Submodule.mul_mem_mul hi hj
  -- 🎉 no goals
#align fractional_ideal.mul_mem_mul FractionalIdeal.mul_mem_mul

theorem mul_le {I J K : FractionalIdeal S P} : I * J ≤ K ↔ ∀ i ∈ I, ∀ j ∈ J, i * j ∈ K := by
  simp only [mul_def]
  -- ⊢ { val := ↑I * ↑J, property := (_ : IsFractional S (↑I * ↑J)) } ≤ K ↔ ∀ (i :  …
  exact Submodule.mul_le
  -- 🎉 no goals
#align fractional_ideal.mul_le FractionalIdeal.mul_le

instance : Pow (FractionalIdeal S P) ℕ :=
  ⟨fun I n => ⟨(I : Submodule R P) ^ n, I.isFractional.pow n⟩⟩

@[simp, norm_cast]
theorem coe_pow (I : FractionalIdeal S P) (n : ℕ) : ↑(I ^ n) = (I : Submodule R P) ^ n :=
  rfl
#align fractional_ideal.coe_pow FractionalIdeal.coe_pow

@[elab_as_elim]
protected theorem mul_induction_on {I J : FractionalIdeal S P} {C : P → Prop} {r : P}
    (hr : r ∈ I * J) (hm : ∀ i ∈ I, ∀ j ∈ J, C (i * j)) (ha : ∀ x y, C x → C y → C (x + y)) :
    C r := by
  simp only [mul_def] at hr
  -- ⊢ C r
  exact Submodule.mul_induction_on hr hm ha
  -- 🎉 no goals
#align fractional_ideal.mul_induction_on FractionalIdeal.mul_induction_on

instance : NatCast (FractionalIdeal S P) :=
  ⟨Nat.unaryCast⟩

theorem coe_nat_cast (n : ℕ) : ((n : FractionalIdeal S P) : Submodule R P) = n :=
  show ((n.unaryCast : FractionalIdeal S P) : Submodule R P) = n
  by induction n <;> simp [*, Nat.unaryCast]
     -- ⊢ ↑(Nat.unaryCast Nat.zero) = ↑Nat.zero
                     -- 🎉 no goals
                     -- 🎉 no goals
#align fractional_ideal.coe_nat_cast FractionalIdeal.coe_nat_cast

instance commSemiring : CommSemiring (FractionalIdeal S P) :=
  Function.Injective.commSemiring _ Subtype.coe_injective coe_zero coe_one coe_add coe_mul
    (fun _ _ => coe_nsmul _ _) coe_pow coe_nat_cast

variable (S P)

/-- `FractionalIdeal.submodule.has_coe` as a bundled `RingHom`. -/
@[simps]
def coeSubmoduleHom : FractionalIdeal S P →+* Submodule R P where
  toFun := coeToSubmodule
  map_one' := coe_one
  map_mul' := coe_mul
  map_zero' := coe_zero (S := S)
  map_add' := coe_add
#align fractional_ideal.coe_submodule_hom FractionalIdeal.coeSubmoduleHom

variable {S P}

section Order

theorem add_le_add_left {I J : FractionalIdeal S P} (hIJ : I ≤ J) (J' : FractionalIdeal S P) :
    J' + I ≤ J' + J :=
  sup_le_sup_left hIJ J'
#align fractional_ideal.add_le_add_left FractionalIdeal.add_le_add_left

theorem mul_le_mul_left {I J : FractionalIdeal S P} (hIJ : I ≤ J) (J' : FractionalIdeal S P) :
    J' * I ≤ J' * J :=
  mul_le.mpr fun _ hk _ hj => mul_mem_mul hk (hIJ hj)
#align fractional_ideal.mul_le_mul_left FractionalIdeal.mul_le_mul_left

theorem le_self_mul_self {I : FractionalIdeal S P} (hI : 1 ≤ I) : I ≤ I * I := by
  convert mul_left_mono I hI
  -- ⊢ I = (fun x x_1 => x * x_1) I 1
  exact (mul_one I).symm
  -- 🎉 no goals
#align fractional_ideal.le_self_mul_self FractionalIdeal.le_self_mul_self

theorem mul_self_le_self {I : FractionalIdeal S P} (hI : I ≤ 1) : I * I ≤ I := by
  convert mul_left_mono I hI
  -- ⊢ I = (fun x x_1 => x * x_1) I 1
  exact (mul_one I).symm
  -- 🎉 no goals
#align fractional_ideal.mul_self_le_self FractionalIdeal.mul_self_le_self

theorem coeIdeal_le_one {I : Ideal R} : (I : FractionalIdeal S P) ≤ 1 := fun _ hx =>
  let ⟨y, _, hy⟩ := (mem_coeIdeal S).mp hx
  (mem_one_iff S).mpr ⟨y, hy⟩
#align fractional_ideal.coe_ideal_le_one FractionalIdeal.coeIdeal_le_one

theorem le_one_iff_exists_coeIdeal {J : FractionalIdeal S P} :
    J ≤ (1 : FractionalIdeal S P) ↔ ∃ I : Ideal R, ↑I = J := by
  constructor
  -- ⊢ J ≤ 1 → ∃ I, ↑I = J
  · intro hJ
    -- ⊢ ∃ I, ↑I = J
    refine' ⟨⟨⟨⟨{ x : R | algebraMap R P x ∈ J }, _⟩, _⟩, _⟩, _⟩
    · intro a b ha hb
      -- ⊢ a + b ∈ {x | ↑(algebraMap R P) x ∈ J}
      rw [mem_setOf, RingHom.map_add]
      -- ⊢ ↑(algebraMap R P) a + ↑(algebraMap R P) b ∈ J
      exact J.val.add_mem ha hb
      -- 🎉 no goals
    · rw [mem_setOf, RingHom.map_zero]
      -- ⊢ 0 ∈ J
      exact J.val.zero_mem
      -- 🎉 no goals
    · intro c x hx
      -- ⊢ c • x ∈ { toAddSubsemigroup := { carrier := {x | ↑(algebraMap R P) x ∈ J}, a …
      rw [smul_eq_mul, mem_setOf, RingHom.map_mul, ← Algebra.smul_def]
      -- ⊢ c • ↑(algebraMap R P) x ∈ J
      exact J.val.smul_mem c hx
      -- 🎉 no goals
    · ext x
      -- ⊢ x ∈ ↑{ toAddSubmonoid := { toAddSubsemigroup := { carrier := {x | ↑(algebraM …
      constructor
      -- ⊢ x ∈ ↑{ toAddSubmonoid := { toAddSubsemigroup := { carrier := {x | ↑(algebraM …
      · rintro ⟨y, hy, eq_y⟩
        -- ⊢ x ∈ J
        rwa [← eq_y]
        -- 🎉 no goals
      · intro hx
        -- ⊢ x ∈ ↑{ toAddSubmonoid := { toAddSubsemigroup := { carrier := {x | ↑(algebraM …
        obtain ⟨y, rfl⟩ := (mem_one_iff S).mp (hJ hx)
        -- ⊢ ↑(algebraMap R P) y ∈ ↑{ toAddSubmonoid := { toAddSubsemigroup := { carrier  …
        exact mem_setOf.mpr ⟨y, hx, rfl⟩
        -- 🎉 no goals
  · rintro ⟨I, hI⟩
    -- ⊢ J ≤ 1
    rw [← hI]
    -- ⊢ ↑I ≤ 1
    apply coeIdeal_le_one
    -- 🎉 no goals
#align fractional_ideal.le_one_iff_exists_coe_ideal FractionalIdeal.le_one_iff_exists_coeIdeal

@[simp]
theorem one_le {I : FractionalIdeal S P} : 1 ≤ I ↔ (1 : P) ∈ I := by
  rw [← coe_le_coe, coe_one, Submodule.one_le, mem_coe]
  -- 🎉 no goals
#align fractional_ideal.one_le FractionalIdeal.one_le

variable (S P)

/-- `coeIdealHom (S : Submonoid R) P` is `(↑) : Ideal R → FractionalIdeal S P` as a ring hom -/
@[simps]
def coeIdealHom : Ideal R →+* FractionalIdeal S P where
  toFun := coeIdeal
  map_add' := coeIdeal_sup
  map_mul' := coeIdeal_mul
  map_one' := by rw [Ideal.one_eq_top, coeIdeal_top]
                 -- 🎉 no goals
  map_zero' := coeIdeal_bot
#align fractional_ideal.coe_ideal_hom FractionalIdeal.coeIdealHom

theorem coeIdeal_pow (I : Ideal R) (n : ℕ) : ↑(I ^ n) = (I : FractionalIdeal S P) ^ n :=
  (coeIdealHom S P).map_pow _ n
#align fractional_ideal.coe_ideal_pow FractionalIdeal.coeIdeal_pow

open BigOperators

theorem coeIdeal_finprod [IsLocalization S P] {α : Sort*} {f : α → Ideal R}
    (hS : S ≤ nonZeroDivisors R) :
    ((∏ᶠ a : α, f a : Ideal R) : FractionalIdeal S P) = ∏ᶠ a : α, (f a : FractionalIdeal S P) :=
  MonoidHom.map_finprod_of_injective (coeIdealHom S P).toMonoidHom (coeIdeal_injective' hS) f
#align fractional_ideal.coe_ideal_finprod FractionalIdeal.coeIdeal_finprod

end Order

variable {P' : Type*} [CommRing P'] [Algebra R P'] [loc' : IsLocalization S P']

variable {P'' : Type*} [CommRing P''] [Algebra R P''] [loc'' : IsLocalization S P'']

theorem _root_.IsFractional.map (g : P →ₐ[R] P') {I : Submodule R P} :
    IsFractional S I → IsFractional S (Submodule.map g.toLinearMap I)
  | ⟨a, a_nonzero, hI⟩ =>
    ⟨a, a_nonzero, fun b hb => by
      obtain ⟨b', b'_mem, hb'⟩ := Submodule.mem_map.mp hb
      -- ⊢ IsInteger R (a • b)
      obtain ⟨x, hx⟩ := hI b' b'_mem
      -- ⊢ IsInteger R (a • b)
      use x
      -- ⊢ ↑(algebraMap R P') x = a • b
      erw [← g.commutes, hx, g.map_smul, hb']⟩
      -- 🎉 no goals
#align is_fractional.map IsFractional.map

/-- `I.map g` is the pushforward of the fractional ideal `I` along the algebra morphism `g` -/
def map (g : P →ₐ[R] P') : FractionalIdeal S P → FractionalIdeal S P' := fun I =>
  ⟨Submodule.map g.toLinearMap I, I.isFractional.map g⟩
#align fractional_ideal.map FractionalIdeal.map

@[simp, norm_cast]
theorem coe_map (g : P →ₐ[R] P') (I : FractionalIdeal S P) :
    ↑(map g I) = Submodule.map g.toLinearMap I :=
  rfl
#align fractional_ideal.coe_map FractionalIdeal.coe_map

@[simp]
theorem mem_map {I : FractionalIdeal S P} {g : P →ₐ[R] P'} {y : P'} :
    y ∈ I.map g ↔ ∃ x, x ∈ I ∧ g x = y :=
  Submodule.mem_map
#align fractional_ideal.mem_map FractionalIdeal.mem_map

variable (I J : FractionalIdeal S P) (g : P →ₐ[R] P')

@[simp]
theorem map_id : I.map (AlgHom.id _ _) = I :=
  coeToSubmodule_injective (Submodule.map_id (I : Submodule R P))
#align fractional_ideal.map_id FractionalIdeal.map_id

@[simp]
theorem map_comp (g' : P' →ₐ[R] P'') : I.map (g'.comp g) = (I.map g).map g' :=
  coeToSubmodule_injective (Submodule.map_comp g.toLinearMap g'.toLinearMap I)
#align fractional_ideal.map_comp FractionalIdeal.map_comp

@[simp, norm_cast]
theorem map_coeIdeal (I : Ideal R) : (I : FractionalIdeal S P).map g = I := by
  ext x
  -- ⊢ x ∈ map g ↑I ↔ x ∈ ↑I
  simp only [mem_coeIdeal]
  -- ⊢ x ∈ map g ↑I ↔ ∃ x', x' ∈ I ∧ ↑(algebraMap R P') x' = x
  constructor
  -- ⊢ x ∈ map g ↑I → ∃ x', x' ∈ I ∧ ↑(algebraMap R P') x' = x
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    -- ⊢ ∃ x', x' ∈ I ∧ ↑(algebraMap R P') x' = ↑(AlgHom.toLinearMap g) (↑(Algebra.li …
    exact ⟨y, hy, (g.commutes y).symm⟩
    -- 🎉 no goals
  · rintro ⟨y, hy, rfl⟩
    -- ⊢ ↑(algebraMap R P') y ∈ map g ↑I
    exact ⟨_, ⟨y, hy, rfl⟩, g.commutes y⟩
    -- 🎉 no goals
#align fractional_ideal.map_coe_ideal FractionalIdeal.map_coeIdeal

@[simp]
theorem map_one : (1 : FractionalIdeal S P).map g = 1 :=
  map_coeIdeal g ⊤
#align fractional_ideal.map_one FractionalIdeal.map_one

@[simp]
theorem map_zero : (0 : FractionalIdeal S P).map g = 0 :=
  map_coeIdeal g 0
#align fractional_ideal.map_zero FractionalIdeal.map_zero

@[simp]
theorem map_add : (I + J).map g = I.map g + J.map g :=
  coeToSubmodule_injective (Submodule.map_sup _ _ _)
#align fractional_ideal.map_add FractionalIdeal.map_add

@[simp]
theorem map_mul : (I * J).map g = I.map g * J.map g := by
  simp only [mul_def]
  -- ⊢ map g { val := ↑I * ↑J, property := (_ : IsFractional S (↑I * ↑J)) } = { val …
  exact coeToSubmodule_injective (Submodule.map_mul _ _ _)
  -- 🎉 no goals
#align fractional_ideal.map_mul FractionalIdeal.map_mul

@[simp]
theorem map_map_symm (g : P ≃ₐ[R] P') : (I.map (g : P →ₐ[R] P')).map (g.symm : P' →ₐ[R] P) = I := by
  rw [← map_comp, g.symm_comp, map_id]
  -- 🎉 no goals
#align fractional_ideal.map_map_symm FractionalIdeal.map_map_symm

@[simp]
theorem map_symm_map (I : FractionalIdeal S P') (g : P ≃ₐ[R] P') :
    (I.map (g.symm : P' →ₐ[R] P)).map (g : P →ₐ[R] P') = I := by
  rw [← map_comp, g.comp_symm, map_id]
  -- 🎉 no goals
#align fractional_ideal.map_symm_map FractionalIdeal.map_symm_map

theorem map_mem_map {f : P →ₐ[R] P'} (h : Function.Injective f) {x : P} {I : FractionalIdeal S P} :
    f x ∈ map f I ↔ x ∈ I :=
  mem_map.trans ⟨fun ⟨_, hx', x'_eq⟩ => h x'_eq ▸ hx', fun h => ⟨x, h, rfl⟩⟩
#align fractional_ideal.map_mem_map FractionalIdeal.map_mem_map

theorem map_injective (f : P →ₐ[R] P') (h : Function.Injective f) :
    Function.Injective (map f : FractionalIdeal S P → FractionalIdeal S P') := fun _ _ hIJ =>
  ext fun _ => (map_mem_map h).symm.trans (hIJ.symm ▸ map_mem_map h)
#align fractional_ideal.map_injective FractionalIdeal.map_injective

/-- If `g` is an equivalence, `map g` is an isomorphism -/
def mapEquiv (g : P ≃ₐ[R] P') : FractionalIdeal S P ≃+* FractionalIdeal S P' where
  toFun := map g
  invFun := map g.symm
  map_add' I J := map_add I J _
  map_mul' I J := map_mul I J _
  left_inv I := by rw [← map_comp, AlgEquiv.symm_comp, map_id]
                   -- 🎉 no goals
  right_inv I := by rw [← map_comp, AlgEquiv.comp_symm, map_id]
                    -- 🎉 no goals
#align fractional_ideal.map_equiv FractionalIdeal.mapEquiv

@[simp]
theorem coeFun_mapEquiv (g : P ≃ₐ[R] P') :
    (mapEquiv g : FractionalIdeal S P → FractionalIdeal S P') = map g :=
  rfl
#align fractional_ideal.coe_fun_map_equiv FractionalIdeal.coeFun_mapEquiv

@[simp]
theorem mapEquiv_apply (g : P ≃ₐ[R] P') (I : FractionalIdeal S P) : mapEquiv g I = map (↑g) I :=
  rfl
#align fractional_ideal.map_equiv_apply FractionalIdeal.mapEquiv_apply

@[simp]
theorem mapEquiv_symm (g : P ≃ₐ[R] P') :
    ((mapEquiv g).symm : FractionalIdeal S P' ≃+* _) = mapEquiv g.symm :=
  rfl
#align fractional_ideal.map_equiv_symm FractionalIdeal.mapEquiv_symm

@[simp]
theorem mapEquiv_refl : mapEquiv AlgEquiv.refl = RingEquiv.refl (FractionalIdeal S P) :=
  RingEquiv.ext fun x => by simp
                            -- 🎉 no goals
#align fractional_ideal.map_equiv_refl FractionalIdeal.mapEquiv_refl

theorem isFractional_span_iff {s : Set P} :
    IsFractional S (span R s) ↔ ∃ a ∈ S, ∀ b : P, b ∈ s → IsInteger R (a • b) :=
  ⟨fun ⟨a, a_mem, h⟩ => ⟨a, a_mem, fun b hb => h b (subset_span hb)⟩, fun ⟨a, a_mem, h⟩ =>
    ⟨a, a_mem, fun b hb =>
      span_induction hb h
        (by
          rw [smul_zero]
          -- ⊢ IsInteger R 0
          exact isInteger_zero)
          -- 🎉 no goals
        (fun x y hx hy => by
          rw [smul_add]
          -- ⊢ IsInteger R (a • x + a • y)
          exact isInteger_add hx hy)
          -- 🎉 no goals
        fun s x hx => by
        rw [smul_comm]
        -- ⊢ IsInteger R (s • a • x)
        exact isInteger_smul hx⟩⟩
        -- 🎉 no goals
#align fractional_ideal.is_fractional_span_iff FractionalIdeal.isFractional_span_iff

theorem isFractional_of_fg {I : Submodule R P} (hI : I.FG) : IsFractional S I := by
  rcases hI with ⟨I, rfl⟩
  -- ⊢ IsFractional S (span R ↑I)
  rcases exist_integer_multiples_of_finset S I with ⟨⟨s, hs1⟩, hs⟩
  -- ⊢ IsFractional S (span R ↑I)
  rw [isFractional_span_iff]
  -- ⊢ ∃ a, a ∈ S ∧ ∀ (b : P), b ∈ ↑I → IsInteger R (a • b)
  exact ⟨s, hs1, hs⟩
  -- 🎉 no goals
#align fractional_ideal.is_fractional_of_fg FractionalIdeal.isFractional_of_fg

theorem mem_span_mul_finite_of_mem_mul {I J : FractionalIdeal S P} {x : P} (hx : x ∈ I * J) :
    ∃ T T' : Finset P, (T : Set P) ⊆ I ∧ (T' : Set P) ⊆ J ∧ x ∈ span R (T * T' : Set P) :=
  Submodule.mem_span_mul_finite_of_mem_mul (by simpa using mem_coe.mpr hx)
                                               -- 🎉 no goals
#align fractional_ideal.mem_span_mul_finite_of_mem_mul FractionalIdeal.mem_span_mul_finite_of_mem_mul

variable (S)

theorem coeIdeal_fg (inj : Function.Injective (algebraMap R P)) (I : Ideal R) :
    FG ((I : FractionalIdeal S P) : Submodule R P) ↔ I.FG :=
  coeSubmodule_fg _ inj _
#align fractional_ideal.coe_ideal_fg FractionalIdeal.coeIdeal_fg

variable {S}

theorem fg_unit (I : (FractionalIdeal S P)ˣ) : FG (I : Submodule R P) :=
  Submodule.fg_unit <| Units.map (coeSubmoduleHom S P).toMonoidHom I
#align fractional_ideal.fg_unit FractionalIdeal.fg_unit

theorem fg_of_isUnit (I : FractionalIdeal S P) (h : IsUnit I) : FG (I : Submodule R P) :=
  fg_unit h.unit
#align fractional_ideal.fg_of_is_unit FractionalIdeal.fg_of_isUnit

theorem _root_.Ideal.fg_of_isUnit (inj : Function.Injective (algebraMap R P)) (I : Ideal R)
    (h : IsUnit (I : FractionalIdeal S P)) : I.FG := by
  rw [← coeIdeal_fg S inj I]
  -- ⊢ FG ↑↑I
  exact FractionalIdeal.fg_of_isUnit I h
  -- 🎉 no goals
#align ideal.fg_of_is_unit Ideal.fg_of_isUnit

variable (S P P')

/-- `canonicalEquiv f f'` is the canonical equivalence between the fractional
ideals in `P` and in `P'`, which are both localizations of `R` at `S`. -/
noncomputable irreducible_def canonicalEquiv : FractionalIdeal S P ≃+* FractionalIdeal S P' :=
  mapEquiv
    {
      ringEquivOfRingEquiv P P' (RingEquiv.refl R)
        (show S.map _ = S by rw [RingEquiv.toMonoidHom_refl, Submonoid.map_id]) with
                             -- 🎉 no goals
      commutes' := fun r => ringEquivOfRingEquiv_eq _ _ }
#align fractional_ideal.canonical_equiv FractionalIdeal.canonicalEquiv

@[simp]
theorem mem_canonicalEquiv_apply {I : FractionalIdeal S P} {x : P'} :
    x ∈ canonicalEquiv S P P' I ↔
      ∃ y ∈ I,
        IsLocalization.map P' (RingHom.id R) (fun y (hy : y ∈ S) => show RingHom.id R y ∈ S from hy)
            (y : P) =
          x := by
  rw [canonicalEquiv, mapEquiv_apply, mem_map]
  -- ⊢ (∃ x_1,
  exact ⟨fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩, fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩⟩
  -- 🎉 no goals
#align fractional_ideal.mem_canonical_equiv_apply FractionalIdeal.mem_canonicalEquiv_apply

@[simp]
theorem canonicalEquiv_symm : (canonicalEquiv S P P').symm = canonicalEquiv S P' P :=
  RingEquiv.ext fun I =>
    SetLike.ext_iff.mpr fun x => by
      rw [mem_canonicalEquiv_apply, canonicalEquiv, mapEquiv_symm, mapEquiv_apply,
        mem_map]
      exact ⟨fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩, fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩⟩
      -- 🎉 no goals
#align fractional_ideal.canonical_equiv_symm FractionalIdeal.canonicalEquiv_symm

theorem canonicalEquiv_flip (I) : canonicalEquiv S P P' (canonicalEquiv S P' P I) = I := by
  rw [← canonicalEquiv_symm, RingEquiv.apply_symm_apply]
  -- 🎉 no goals
#align fractional_ideal.canonical_equiv_flip FractionalIdeal.canonicalEquiv_flip

@[simp]
theorem canonicalEquiv_canonicalEquiv (P'' : Type*) [CommRing P''] [Algebra R P'']
    [IsLocalization S P''] (I : FractionalIdeal S P) :
    canonicalEquiv S P' P'' (canonicalEquiv S P P' I) = canonicalEquiv S P P'' I := by
  ext
  -- ⊢ x✝ ∈ ↑(canonicalEquiv S P' P'') (↑(canonicalEquiv S P P') I) ↔ x✝ ∈ ↑(canoni …
  simp only [IsLocalization.map_map, RingHomInvPair.comp_eq₂, mem_canonicalEquiv_apply,
    exists_prop, exists_exists_and_eq_and]
#align fractional_ideal.canonical_equiv_canonical_equiv FractionalIdeal.canonicalEquiv_canonicalEquiv

theorem canonicalEquiv_trans_canonicalEquiv (P'' : Type*) [CommRing P''] [Algebra R P'']
    [IsLocalization S P''] :
    (canonicalEquiv S P P').trans (canonicalEquiv S P' P'') = canonicalEquiv S P P'' :=
  RingEquiv.ext (canonicalEquiv_canonicalEquiv S P P' P'')
#align fractional_ideal.canonical_equiv_trans_canonical_equiv FractionalIdeal.canonicalEquiv_trans_canonicalEquiv

@[simp]
theorem canonicalEquiv_coeIdeal (I : Ideal R) : canonicalEquiv S P P' I = I := by
  ext
  -- ⊢ x✝ ∈ ↑(canonicalEquiv S P P') ↑I ↔ x✝ ∈ ↑I
  simp [IsLocalization.map_eq]
  -- 🎉 no goals
#align fractional_ideal.canonical_equiv_coe_ideal FractionalIdeal.canonicalEquiv_coeIdeal

@[simp]
theorem canonicalEquiv_self : canonicalEquiv S P P = RingEquiv.refl _ := by
  rw [← canonicalEquiv_trans_canonicalEquiv S P P]
  -- ⊢ RingEquiv.trans (canonicalEquiv S P P) (canonicalEquiv S P P) = RingEquiv.re …
  convert(canonicalEquiv S P P).symm_trans_self
  -- ⊢ canonicalEquiv S P P = RingEquiv.symm (canonicalEquiv S P P)
  exact (canonicalEquiv_symm S P P).symm
  -- 🎉 no goals
#align fractional_ideal.canonical_equiv_self FractionalIdeal.canonicalEquiv_self

end Semiring

section IsFractionRing

/-!
### `IsFractionRing` section

This section concerns fractional ideals in the field of fractions,
i.e. the type `FractionalIdeal R⁰ K` where `IsFractionRing R K`.
-/


variable {K K' : Type*} [Field K] [Field K']

variable [Algebra R K] [IsFractionRing R K] [Algebra R K'] [IsFractionRing R K']

variable {I J : FractionalIdeal R⁰ K} (h : K →ₐ[R] K')

/-- Nonzero fractional ideals contain a nonzero integer. -/
theorem exists_ne_zero_mem_isInteger [Nontrivial R] (hI : I ≠ 0) :
    ∃ (x : R) (_ : x ≠ 0), algebraMap R K x ∈ I := by
  obtain ⟨y : K, y_mem, y_not_mem⟩ :=
    SetLike.exists_of_lt (by simpa only using bot_lt_iff_ne_bot.mpr hI)
  have y_ne_zero : y ≠ 0 := by simpa using y_not_mem
  -- ⊢ ∃ x x_1, ↑(algebraMap R K) x ∈ I
  obtain ⟨z, ⟨x, hx⟩⟩ := exists_integer_multiple R⁰ y
  -- ⊢ ∃ x x_1, ↑(algebraMap R K) x ∈ I
  refine' ⟨x, _, _⟩
  -- ⊢ x ≠ 0
  · rw [Ne.def, ← @IsFractionRing.to_map_eq_zero_iff R _ K, hx, Algebra.smul_def]
    -- ⊢ ¬↑(algebraMap R K) ↑z * y = 0
    exact mul_ne_zero (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors z.2) y_ne_zero
    -- 🎉 no goals
  · rw [hx]
    -- ⊢ ↑z • y ∈ I
    exact smul_mem _ _ y_mem
    -- 🎉 no goals
#align fractional_ideal.exists_ne_zero_mem_is_integer FractionalIdeal.exists_ne_zero_mem_isInteger

theorem map_ne_zero [Nontrivial R] (hI : I ≠ 0) : I.map h ≠ 0 := by
  obtain ⟨x, x_ne_zero, hx⟩ := exists_ne_zero_mem_isInteger hI
  -- ⊢ map h I ≠ 0
  contrapose! x_ne_zero with map_eq_zero
  -- ⊢ x = 0
  refine' IsFractionRing.to_map_eq_zero_iff.mp (eq_zero_iff.mp map_eq_zero _ (mem_map.mpr _))
  -- ⊢ ∃ x_1, x_1 ∈ I ∧ ↑h x_1 = ↑(algebraMap R K') x
  exact ⟨algebraMap R K x, hx, h.commutes x⟩
  -- 🎉 no goals
#align fractional_ideal.map_ne_zero FractionalIdeal.map_ne_zero

@[simp]
theorem map_eq_zero_iff [Nontrivial R] : I.map h = 0 ↔ I = 0 :=
  ⟨not_imp_not.mp (map_ne_zero _), fun hI => hI.symm ▸ map_zero h⟩
#align fractional_ideal.map_eq_zero_iff FractionalIdeal.map_eq_zero_iff

theorem coeIdeal_injective : Function.Injective (fun (I : Ideal R) ↦ (I : FractionalIdeal R⁰ K)) :=
  coeIdeal_injective' le_rfl
#align fractional_ideal.coe_ideal_injective FractionalIdeal.coeIdeal_injective

theorem coeIdeal_inj {I J : Ideal R} :
    (I : FractionalIdeal R⁰ K) = (J : FractionalIdeal R⁰ K) ↔ I = J :=
  coeIdeal_inj' le_rfl
#align fractional_ideal.coe_ideal_inj FractionalIdeal.coeIdeal_inj

@[simp]
theorem coeIdeal_eq_zero {I : Ideal R} : (I : FractionalIdeal R⁰ K) = 0 ↔ I = ⊥ :=
  coeIdeal_eq_zero' le_rfl
#align fractional_ideal.coe_ideal_eq_zero FractionalIdeal.coeIdeal_eq_zero

theorem coeIdeal_ne_zero {I : Ideal R} : (I : FractionalIdeal R⁰ K) ≠ 0 ↔ I ≠ ⊥ :=
  coeIdeal_ne_zero' le_rfl
#align fractional_ideal.coe_ideal_ne_zero FractionalIdeal.coeIdeal_ne_zero

@[simp]
theorem coeIdeal_eq_one {I : Ideal R} : (I : FractionalIdeal R⁰ K) = 1 ↔ I = 1 := by
  simpa only [Ideal.one_eq_top] using coeIdeal_inj
  -- 🎉 no goals
#align fractional_ideal.coe_ideal_eq_one FractionalIdeal.coeIdeal_eq_one

theorem coeIdeal_ne_one {I : Ideal R} : (I : FractionalIdeal R⁰ K) ≠ 1 ↔ I ≠ 1 :=
  not_iff_not.mpr coeIdeal_eq_one
#align fractional_ideal.coe_ideal_ne_one FractionalIdeal.coeIdeal_ne_one

end IsFractionRing

section Quotient

/-!
### `quotient` section

This section defines the ideal quotient of fractional ideals.

In this section we need that each non-zero `y : R` has an inverse in
the localization, i.e. that the localization is a field. We satisfy this
assumption by taking `S = nonZeroDivisors R`, `R`'s localization at which
is a field because `R` is a domain.
-/


open Classical

variable {R₁ : Type*} [CommRing R₁] {K : Type*} [Field K]

variable [Algebra R₁ K] [frac : IsFractionRing R₁ K]

instance : Nontrivial (FractionalIdeal R₁⁰ K) :=
  ⟨⟨0, 1, fun h =>
      have this : (1 : K) ∈ (0 : FractionalIdeal R₁⁰ K) := by
        rw [← (algebraMap R₁ K).map_one]
        -- ⊢ ↑(algebraMap R₁ K) 1 ∈ 0
        simpa only [h] using coe_mem_one R₁⁰ 1
        -- 🎉 no goals
      one_ne_zero ((mem_zero_iff _).mp this)⟩⟩

theorem ne_zero_of_mul_eq_one (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) : I ≠ 0 := fun hI =>
  zero_ne_one' (FractionalIdeal R₁⁰ K)
    (by
      convert h
      -- ⊢ 0 = I * J
      simp [hI])
      -- 🎉 no goals
#align fractional_ideal.ne_zero_of_mul_eq_one FractionalIdeal.ne_zero_of_mul_eq_one

variable [IsDomain R₁]

theorem _root_.IsFractional.div_of_nonzero {I J : Submodule R₁ K} :
    IsFractional R₁⁰ I → IsFractional R₁⁰ J → J ≠ 0 → IsFractional R₁⁰ (I / J)
  | ⟨aI, haI, hI⟩, ⟨aJ, haJ, hJ⟩, h => by
    obtain ⟨y, mem_J, not_mem_zero⟩ :=
      SetLike.exists_of_lt (show 0 < J by simpa only using bot_lt_iff_ne_bot.mpr h)
    obtain ⟨y', hy'⟩ := hJ y mem_J
    -- ⊢ IsFractional R₁⁰ (I / J)
    use aI * y'
    -- ⊢ aI * y' ∈ R₁⁰ ∧ ∀ (b : K), b ∈ I / J → IsInteger R₁ ((aI * y') • b)
    constructor
    -- ⊢ aI * y' ∈ R₁⁰
    · apply (nonZeroDivisors R₁).mul_mem haI (mem_nonZeroDivisors_iff_ne_zero.mpr _)
      -- ⊢ y' ≠ 0
      intro y'_eq_zero
      -- ⊢ False
      have : algebraMap R₁ K aJ * y = 0 := by
        rw [← Algebra.smul_def, ← hy', y'_eq_zero, RingHom.map_zero]
      have y_zero :=
        (mul_eq_zero.mp this).resolve_left
          (mt ((injective_iff_map_eq_zero (algebraMap R₁ K)).1 (IsFractionRing.injective _ _) _)
            (mem_nonZeroDivisors_iff_ne_zero.mp haJ))
      apply not_mem_zero
      -- ⊢ y ∈ 0
      simpa
      -- 🎉 no goals
    intro b hb
    -- ⊢ IsInteger R₁ ((aI * y') • b)
    convert hI _ (hb _ (Submodule.smul_mem _ aJ mem_J)) using 1
    -- ⊢ (aI * y') • b = aI • (b * aJ • y)
    rw [← hy', mul_comm b, ← Algebra.smul_def, mul_smul]
    -- 🎉 no goals
#align is_fractional.div_of_nonzero IsFractional.div_of_nonzero

theorem fractional_div_of_nonzero {I J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    IsFractional R₁⁰ (I / J : Submodule R₁ K) :=
  I.isFractional.div_of_nonzero J.isFractional fun H =>
    h <| coeToSubmodule_injective <| H.trans coe_zero.symm
#align fractional_ideal.fractional_div_of_nonzero FractionalIdeal.fractional_div_of_nonzero

noncomputable instance : Div (FractionalIdeal R₁⁰ K) :=
  ⟨fun I J => if h : J = 0 then 0 else ⟨I / J, fractional_div_of_nonzero h⟩⟩

variable {I J : FractionalIdeal R₁⁰ K}

@[simp]
theorem div_zero {I : FractionalIdeal R₁⁰ K} : I / 0 = 0 :=
  dif_pos rfl
#align fractional_ideal.div_zero FractionalIdeal.div_zero

theorem div_nonzero {I J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    I / J = ⟨I / J, fractional_div_of_nonzero h⟩ :=
  dif_neg h
#align fractional_ideal.div_nonzero FractionalIdeal.div_nonzero

@[simp]
theorem coe_div {I J : FractionalIdeal R₁⁰ K} (hJ : J ≠ 0) :
    (↑(I / J) : Submodule R₁ K) = ↑I / (↑J : Submodule R₁ K) :=
  congr_arg _ (dif_neg hJ)
#align fractional_ideal.coe_div FractionalIdeal.coe_div

theorem mem_div_iff_of_nonzero {I J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) {x} :
    x ∈ I / J ↔ ∀ y ∈ J, x * y ∈ I := by
  rw [div_nonzero h]
  -- ⊢ x ∈ { val := ↑I / ↑J, property := (_ : IsFractional R₁⁰ (↑I / ↑J)) } ↔ ∀ (y  …
  exact Submodule.mem_div_iff_forall_mul_mem
  -- 🎉 no goals
#align fractional_ideal.mem_div_iff_of_nonzero FractionalIdeal.mem_div_iff_of_nonzero

theorem mul_one_div_le_one {I : FractionalIdeal R₁⁰ K} : I * (1 / I) ≤ 1 := by
  by_cases hI : I = 0
  -- ⊢ I * (1 / I) ≤ 1
  · rw [hI, div_zero, mul_zero]
    -- ⊢ 0 ≤ 1
    exact zero_le 1
    -- 🎉 no goals
  · rw [← coe_le_coe, coe_mul, coe_div hI, coe_one]
    -- ⊢ ↑I * (1 / ↑I) ≤ 1
    apply Submodule.mul_one_div_le_one
    -- 🎉 no goals
#align fractional_ideal.mul_one_div_le_one FractionalIdeal.mul_one_div_le_one

theorem le_self_mul_one_div {I : FractionalIdeal R₁⁰ K} (hI : I ≤ (1 : FractionalIdeal R₁⁰ K)) :
    I ≤ I * (1 / I) := by
  by_cases hI_nz : I = 0
  -- ⊢ I ≤ I * (1 / I)
  · rw [hI_nz, div_zero, mul_zero]
    -- 🎉 no goals
  · rw [← coe_le_coe, coe_mul, coe_div hI_nz, coe_one]
    -- ⊢ ↑I ≤ ↑I * (1 / ↑I)
    rw [← coe_le_coe, coe_one] at hI
    -- ⊢ ↑I ≤ ↑I * (1 / ↑I)
    exact Submodule.le_self_mul_one_div hI
    -- 🎉 no goals
#align fractional_ideal.le_self_mul_one_div FractionalIdeal.le_self_mul_one_div

theorem le_div_iff_of_nonzero {I J J' : FractionalIdeal R₁⁰ K} (hJ' : J' ≠ 0) :
    I ≤ J / J' ↔ ∀ x ∈ I, ∀ y ∈ J', x * y ∈ J :=
  ⟨fun h _ hx => (mem_div_iff_of_nonzero hJ').mp (h hx), fun h x hx =>
    (mem_div_iff_of_nonzero hJ').mpr (h x hx)⟩
#align fractional_ideal.le_div_iff_of_nonzero FractionalIdeal.le_div_iff_of_nonzero

theorem le_div_iff_mul_le {I J J' : FractionalIdeal R₁⁰ K} (hJ' : J' ≠ 0) :
    I ≤ J / J' ↔ I * J' ≤ J := by
  rw [div_nonzero hJ']
  -- ⊢ I ≤ { val := ↑J / ↑J', property := (_ : IsFractional R₁⁰ (↑J / ↑J')) } ↔ I * …
  -- Porting note: this used to be { convert; rw }, flipped the order.
  rw [← coe_le_coe (I := I * J') (J := J), coe_mul]
  -- ⊢ I ≤ { val := ↑J / ↑J', property := (_ : IsFractional R₁⁰ (↑J / ↑J')) } ↔ ↑I  …
  exact Submodule.le_div_iff_mul_le
  -- 🎉 no goals
#align fractional_ideal.le_div_iff_mul_le FractionalIdeal.le_div_iff_mul_le

@[simp]
theorem div_one {I : FractionalIdeal R₁⁰ K} : I / 1 = I := by
  rw [div_nonzero (one_ne_zero' (FractionalIdeal R₁⁰ K))]
  -- ⊢ { val := ↑I / ↑1, property := (_ : IsFractional R₁⁰ (↑I / ↑1)) } = I
  ext
  -- ⊢ x✝ ∈ { val := ↑I / ↑1, property := (_ : IsFractional R₁⁰ (↑I / ↑1)) } ↔ x✝ ∈ I
  constructor <;> intro h
  -- ⊢ x✝ ∈ { val := ↑I / ↑1, property := (_ : IsFractional R₁⁰ (↑I / ↑1)) } → x✝ ∈ I
                  -- ⊢ x✝ ∈ I
                  -- ⊢ x✝ ∈ { val := ↑I / ↑1, property := (_ : IsFractional R₁⁰ (↑I / ↑1)) }
  · simpa using mem_div_iff_forall_mul_mem.mp h 1 ((algebraMap R₁ K).map_one ▸ coe_mem_one R₁⁰ 1)
    -- 🎉 no goals
  · apply mem_div_iff_forall_mul_mem.mpr
    -- ⊢ ∀ (y : K), y ∈ ↑1 → x✝ * y ∈ ↑I
    rintro y ⟨y', _, rfl⟩
    -- ⊢ x✝ * ↑(Algebra.linearMap R₁ K) y' ∈ ↑I
    -- Porting note: this used to be { convert; rw }, flipped the order.
    rw [mul_comm, Algebra.linearMap_apply, ← Algebra.smul_def]
    -- ⊢ y' • x✝ ∈ ↑I
    exact Submodule.smul_mem _ y' h
    -- 🎉 no goals
#align fractional_ideal.div_one FractionalIdeal.div_one

theorem eq_one_div_of_mul_eq_one_right (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) :
    J = 1 / I := by
  have hI : I ≠ 0 := ne_zero_of_mul_eq_one I J h
  -- ⊢ J = 1 / I
  suffices h' : I * (1 / I) = 1
  -- ⊢ J = 1 / I
  · exact
      congr_arg Units.inv <|
        @Units.ext _ _ (Units.mkOfMulEqOne _ _ h) (Units.mkOfMulEqOne _ _ h') rfl
  apply le_antisymm
  -- ⊢ I * (1 / I) ≤ 1
  · apply mul_le.mpr _
    -- ⊢ ∀ (i : K), i ∈ I → ∀ (j : K), j ∈ 1 / I → i * j ∈ 1
    intro x hx y hy
    -- ⊢ x * y ∈ 1
    rw [mul_comm]
    -- ⊢ y * x ∈ 1
    exact (mem_div_iff_of_nonzero hI).mp hy x hx
    -- 🎉 no goals
  rw [← h]
  -- ⊢ I * J ≤ I * (I * J / I)
  apply mul_left_mono I
  -- ⊢ J ≤ I * J / I
  apply (le_div_iff_of_nonzero hI).mpr _
  -- ⊢ ∀ (x : K), x ∈ J → ∀ (y : K), y ∈ I → x * y ∈ I * J
  intro y hy x hx
  -- ⊢ y * x ∈ I * J
  rw [mul_comm]
  -- ⊢ x * y ∈ I * J
  exact mul_mem_mul hx hy
  -- 🎉 no goals
#align fractional_ideal.eq_one_div_of_mul_eq_one_right FractionalIdeal.eq_one_div_of_mul_eq_one_right

theorem mul_div_self_cancel_iff {I : FractionalIdeal R₁⁰ K} : I * (1 / I) = 1 ↔ ∃ J, I * J = 1 :=
  ⟨fun h => ⟨1 / I, h⟩, fun ⟨J, hJ⟩ => by rwa [← eq_one_div_of_mul_eq_one_right I J hJ]⟩
                                          -- 🎉 no goals
#align fractional_ideal.mul_div_self_cancel_iff FractionalIdeal.mul_div_self_cancel_iff

variable {K' : Type*} [Field K'] [Algebra R₁ K'] [IsFractionRing R₁ K']

@[simp]
theorem map_div (I J : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') :
    (I / J).map (h : K →ₐ[R₁] K') = I.map h / J.map h := by
  by_cases H : J = 0
  -- ⊢ map (↑h) (I / J) = map (↑h) I / map (↑h) J
  · rw [H, div_zero, map_zero, div_zero]
    -- 🎉 no goals
  · -- Porting note: `simp` wouldn't apply these lemmas so do them manually using `rw`
    rw [← coeToSubmodule_inj, div_nonzero H, div_nonzero (map_ne_zero _ H)]
    -- ⊢ ↑(map ↑h { val := ↑I / ↑J, property := (_ : IsFractional R₁⁰ (↑I / ↑J)) }) = …
    simp [Submodule.map_div]
    -- 🎉 no goals
#align fractional_ideal.map_div FractionalIdeal.map_div

-- Porting note: doesn't need to be @[simp] because this follows from `map_one` and `map_div`
theorem map_one_div (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') :
    (1 / I).map (h : K →ₐ[R₁] K') = 1 / I.map h := by rw [map_div, map_one]
                                                      -- 🎉 no goals
#align fractional_ideal.map_one_div FractionalIdeal.map_one_div

end Quotient

section Field

variable {R₁ K L : Type*} [CommRing R₁] [Field K] [Field L]

variable [Algebra R₁ K] [IsFractionRing R₁ K] [Algebra K L] [IsFractionRing K L]

theorem eq_zero_or_one (I : FractionalIdeal K⁰ L) : I = 0 ∨ I = 1 := by
  rw [or_iff_not_imp_left]
  -- ⊢ ¬I = 0 → I = 1
  intro hI
  -- ⊢ I = 1
  simp_rw [@SetLike.ext_iff _ _ _ I 1, mem_one_iff]
  -- ⊢ ∀ (x : L), x ∈ I ↔ ∃ x', ↑(algebraMap K L) x' = x
  intro x
  -- ⊢ x ∈ I ↔ ∃ x', ↑(algebraMap K L) x' = x
  constructor
  -- ⊢ x ∈ I → ∃ x', ↑(algebraMap K L) x' = x
  · intro x_mem
    -- ⊢ ∃ x', ↑(algebraMap K L) x' = x
    obtain ⟨n, d, rfl⟩ := IsLocalization.mk'_surjective K⁰ x
    -- ⊢ ∃ x', ↑(algebraMap K L) x' = mk' L n d
    refine' ⟨n / d, _⟩
    -- ⊢ ↑(algebraMap K L) (n / ↑d) = mk' L n d
    rw [map_div₀, IsFractionRing.mk'_eq_div]
    -- 🎉 no goals
  · rintro ⟨x, rfl⟩
    -- ⊢ ↑(algebraMap K L) x ∈ I
    obtain ⟨y, y_ne, y_mem⟩ := exists_ne_zero_mem_isInteger hI
    -- ⊢ ↑(algebraMap K L) x ∈ I
    rw [← div_mul_cancel x y_ne, RingHom.map_mul, ← Algebra.smul_def]
    -- ⊢ (x / y) • ↑(algebraMap K L) y ∈ I
    exact smul_mem (M := L) I (x / y) y_mem
    -- 🎉 no goals
#align fractional_ideal.eq_zero_or_one FractionalIdeal.eq_zero_or_one

theorem eq_zero_or_one_of_isField (hF : IsField R₁) (I : FractionalIdeal R₁⁰ K) : I = 0 ∨ I = 1 :=
  letI : Field R₁ := hF.toField
  eq_zero_or_one I
#align fractional_ideal.eq_zero_or_one_of_is_field FractionalIdeal.eq_zero_or_one_of_isField

end Field

section PrincipalIdealRing

variable {R₁ : Type*} [CommRing R₁] {K : Type*} [Field K]

variable [Algebra R₁ K] [IsFractionRing R₁ K]

open Classical

variable (R₁)

/-- `FractionalIdeal.span_finset R₁ s f` is the fractional ideal of `R₁` generated by `f '' s`. -/
-- Porting note: `@[simps]` generated a `Subtype.val` coercion instead of a
-- `FractionalIdeal.coeToSubmodule` coercion
def spanFinset {ι : Type*} (s : Finset ι) (f : ι → K) : FractionalIdeal R₁⁰ K :=
  ⟨Submodule.span R₁ (f '' s), by
    obtain ⟨a', ha'⟩ := IsLocalization.exist_integer_multiples R₁⁰ s f
    -- ⊢ IsFractional R₁⁰ (span R₁ (f '' ↑s))
    refine' ⟨a', a'.2, fun x hx => Submodule.span_induction hx _ _ _ _⟩
    · rintro _ ⟨i, hi, rfl⟩
      -- ⊢ IsInteger R₁ (↑a' • f i)
      exact ha' i hi
      -- 🎉 no goals
    · rw [smul_zero]
      -- ⊢ IsInteger R₁ 0
      exact IsLocalization.isInteger_zero
      -- 🎉 no goals
    · intro x y hx hy
      -- ⊢ IsInteger R₁ (↑a' • (x + y))
      rw [smul_add]
      -- ⊢ IsInteger R₁ (↑a' • x + ↑a' • y)
      exact IsLocalization.isInteger_add hx hy
      -- 🎉 no goals
    · intro c x hx
      -- ⊢ IsInteger R₁ (↑a' • c • x)
      rw [smul_comm]
      -- ⊢ IsInteger R₁ (c • ↑a' • x)
      exact IsLocalization.isInteger_smul hx⟩
      -- 🎉 no goals
#align fractional_ideal.span_finset FractionalIdeal.spanFinset

@[simp] lemma spanFinset_coe {ι : Type*} (s : Finset ι) (f : ι → K) :
    (spanFinset R₁ s f : Submodule R₁ K) = Submodule.span R₁ (f '' s) :=
  rfl

variable {R₁}

@[simp]
theorem spanFinset_eq_zero {ι : Type*} {s : Finset ι} {f : ι → K} :
    spanFinset R₁ s f = 0 ↔ ∀ j ∈ s, f j = 0 := by
  simp only [← coeToSubmodule_inj, spanFinset_coe, coe_zero, Submodule.span_eq_bot,
    Set.mem_image, Finset.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
#align fractional_ideal.span_finset_eq_zero FractionalIdeal.spanFinset_eq_zero

theorem spanFinset_ne_zero {ι : Type*} {s : Finset ι} {f : ι → K} :
    spanFinset R₁ s f ≠ 0 ↔ ∃ j ∈ s, f j ≠ 0 := by simp
                                                   -- 🎉 no goals
#align fractional_ideal.span_finset_ne_zero FractionalIdeal.spanFinset_ne_zero

open Submodule.IsPrincipal

theorem isFractional_span_singleton (x : P) : IsFractional S (span R {x} : Submodule R P) :=
  let ⟨a, ha⟩ := exists_integer_multiple S x
  isFractional_span_iff.mpr ⟨a, a.2, fun _ hx' => (Set.mem_singleton_iff.mp hx').symm ▸ ha⟩
#align fractional_ideal.is_fractional_span_singleton FractionalIdeal.isFractional_span_singleton

variable (S)

/-- `spanSingleton x` is the fractional ideal generated by `x` if `0 ∉ S` -/
irreducible_def spanSingleton (x : P) : FractionalIdeal S P :=
  ⟨span R {x}, isFractional_span_singleton x⟩
#align fractional_ideal.span_singleton FractionalIdeal.spanSingleton

-- local attribute [semireducible] span_singleton
@[simp]
theorem coe_spanSingleton (x : P) : (spanSingleton S x : Submodule R P) = span R {x} := by
  rw [spanSingleton]
  -- ⊢ ↑{ val := span R {x}, property := (_ : IsFractional S (span R {x})) } = span …
  rfl
  -- 🎉 no goals
#align fractional_ideal.coe_span_singleton FractionalIdeal.coe_spanSingleton

@[simp]
theorem mem_spanSingleton {x y : P} : x ∈ spanSingleton S y ↔ ∃ z : R, z • y = x := by
  rw [spanSingleton]
  -- ⊢ x ∈ { val := span R {y}, property := (_ : IsFractional S (span R {y})) } ↔ ∃ …
  exact Submodule.mem_span_singleton
  -- 🎉 no goals
#align fractional_ideal.mem_span_singleton FractionalIdeal.mem_spanSingleton

theorem mem_spanSingleton_self (x : P) : x ∈ spanSingleton S x :=
  (mem_spanSingleton S).mpr ⟨1, one_smul _ _⟩
#align fractional_ideal.mem_span_singleton_self FractionalIdeal.mem_spanSingleton_self

variable {S}

@[simp]
theorem spanSingleton_le_iff_mem {x : P} {I : FractionalIdeal S P} :
    spanSingleton S x ≤ I ↔ x ∈ I := by
  rw [← coe_le_coe, coe_spanSingleton, Submodule.span_singleton_le_iff_mem, mem_coe]
  -- 🎉 no goals
#align fractional_ideal.span_singleton_le_iff_mem FractionalIdeal.spanSingleton_le_iff_mem

theorem spanSingleton_eq_spanSingleton [NoZeroSMulDivisors R P] {x y : P} :
    spanSingleton S x = spanSingleton S y ↔ ∃ z : Rˣ, z • x = y := by
  rw [← Submodule.span_singleton_eq_span_singleton, spanSingleton, spanSingleton]
  -- ⊢ { val := span R {x}, property := (_ : IsFractional S (span R {x})) } = { val …
  exact Subtype.mk_eq_mk
  -- 🎉 no goals
#align fractional_ideal.span_singleton_eq_span_singleton FractionalIdeal.spanSingleton_eq_spanSingleton

theorem eq_spanSingleton_of_principal (I : FractionalIdeal S P) [IsPrincipal (I : Submodule R P)] :
    I = spanSingleton S (generator (I : Submodule R P)) := by
  -- Porting note: this used to be `coeToSubmodule_injective (span_singleton_generator ↑I).symm`
  -- but Lean 4 struggled to unify everything. Turned it into an explicit `rw`.
  rw [spanSingleton, ← coeToSubmodule_inj, coe_mk, span_singleton_generator]
  -- 🎉 no goals
#align fractional_ideal.eq_span_singleton_of_principal FractionalIdeal.eq_spanSingleton_of_principal

theorem isPrincipal_iff (I : FractionalIdeal S P) :
    IsPrincipal (I : Submodule R P) ↔ ∃ x, I = spanSingleton S x :=
  ⟨fun h => ⟨@generator _ _ _ _ _ (↑I) h, @eq_spanSingleton_of_principal _ _ _ _ _ _ _ I h⟩,
    fun ⟨x, hx⟩ => { principal' := ⟨x, Eq.trans (congr_arg _ hx) (coe_spanSingleton _ x)⟩ }⟩
#align fractional_ideal.is_principal_iff FractionalIdeal.isPrincipal_iff

@[simp]
theorem spanSingleton_zero : spanSingleton S (0 : P) = 0 := by
  ext
  -- ⊢ x✝ ∈ spanSingleton S 0 ↔ x✝ ∈ 0
  simp [Submodule.mem_span_singleton, eq_comm]
  -- 🎉 no goals
#align fractional_ideal.span_singleton_zero FractionalIdeal.spanSingleton_zero

theorem spanSingleton_eq_zero_iff {y : P} : spanSingleton S y = 0 ↔ y = 0 :=
  ⟨fun h =>
    span_eq_bot.mp (by simpa using congr_arg Subtype.val h : span R {y} = ⊥) y (mem_singleton y),
                       -- 🎉 no goals
    fun h => by simp [h]⟩
                -- 🎉 no goals
#align fractional_ideal.span_singleton_eq_zero_iff FractionalIdeal.spanSingleton_eq_zero_iff

theorem spanSingleton_ne_zero_iff {y : P} : spanSingleton S y ≠ 0 ↔ y ≠ 0 :=
  not_congr spanSingleton_eq_zero_iff
#align fractional_ideal.span_singleton_ne_zero_iff FractionalIdeal.spanSingleton_ne_zero_iff

@[simp]
theorem spanSingleton_one : spanSingleton S (1 : P) = 1 := by
  ext
  -- ⊢ x✝ ∈ spanSingleton S 1 ↔ x✝ ∈ 1
  refine' (mem_spanSingleton S).trans ((exists_congr _).trans (mem_one_iff S).symm)
  -- ⊢ ∀ (a : R), a • 1 = x✝ ↔ ↑(algebraMap R P) a = x✝
  intro x'
  -- ⊢ x' • 1 = x✝ ↔ ↑(algebraMap R P) x' = x✝
  rw [Algebra.smul_def, mul_one]
  -- 🎉 no goals
#align fractional_ideal.span_singleton_one FractionalIdeal.spanSingleton_one

@[simp]
theorem spanSingleton_mul_spanSingleton (x y : P) :
    spanSingleton S x * spanSingleton S y = spanSingleton S (x * y) := by
  apply coeToSubmodule_injective
  -- ⊢ (fun I => ↑I) (spanSingleton S x * spanSingleton S y) = (fun I => ↑I) (spanS …
  simp only [coe_mul, coe_spanSingleton, span_mul_span, singleton_mul_singleton]
  -- 🎉 no goals
#align fractional_ideal.span_singleton_mul_span_singleton FractionalIdeal.spanSingleton_mul_spanSingleton

@[simp]
theorem spanSingleton_pow (x : P) (n : ℕ) : spanSingleton S x ^ n = spanSingleton S (x ^ n) := by
  induction' n with n hn
  -- ⊢ spanSingleton S x ^ Nat.zero = spanSingleton S (x ^ Nat.zero)
  · rw [pow_zero, pow_zero, spanSingleton_one]
    -- 🎉 no goals
  · rw [pow_succ, hn, spanSingleton_mul_spanSingleton, pow_succ]
    -- 🎉 no goals
#align fractional_ideal.span_singleton_pow FractionalIdeal.spanSingleton_pow

@[simp]
theorem coeIdeal_span_singleton (x : R) :
    (↑(Ideal.span {x} : Ideal R) : FractionalIdeal S P) = spanSingleton S (algebraMap R P x) := by
  ext y
  -- ⊢ y ∈ ↑(Ideal.span {x}) ↔ y ∈ spanSingleton S (↑(algebraMap R P) x)
  refine' (mem_coeIdeal S).trans (Iff.trans _ (mem_spanSingleton S).symm)
  -- ⊢ (∃ x', x' ∈ Ideal.span {x} ∧ ↑(algebraMap R P) x' = y) ↔ ∃ z, z • ↑(algebraM …
  constructor
  -- ⊢ (∃ x', x' ∈ Ideal.span {x} ∧ ↑(algebraMap R P) x' = y) → ∃ z, z • ↑(algebraM …
  · rintro ⟨y', hy', rfl⟩
    -- ⊢ ∃ z, z • ↑(algebraMap R P) x = ↑(algebraMap R P) y'
    obtain ⟨x', rfl⟩ := Submodule.mem_span_singleton.mp hy'
    -- ⊢ ∃ z, z • ↑(algebraMap R P) x = ↑(algebraMap R P) (x' • x)
    use x'
    -- ⊢ x' • ↑(algebraMap R P) x = ↑(algebraMap R P) (x' • x)
    rw [smul_eq_mul, RingHom.map_mul, Algebra.smul_def]
    -- 🎉 no goals
  · rintro ⟨y', rfl⟩
    -- ⊢ ∃ x', x' ∈ Ideal.span {x} ∧ ↑(algebraMap R P) x' = y' • ↑(algebraMap R P) x
    refine' ⟨y' * x, Submodule.mem_span_singleton.mpr ⟨y', rfl⟩, _⟩
    -- ⊢ ↑(algebraMap R P) (y' * x) = y' • ↑(algebraMap R P) x
    rw [RingHom.map_mul, Algebra.smul_def]
    -- 🎉 no goals
#align fractional_ideal.coe_ideal_span_singleton FractionalIdeal.coeIdeal_span_singleton

@[simp]
theorem canonicalEquiv_spanSingleton {P'} [CommRing P'] [Algebra R P'] [IsLocalization S P']
    (x : P) :
    canonicalEquiv S P P' (spanSingleton S x) =
      spanSingleton S
        (IsLocalization.map P' (RingHom.id R)
          (fun y (hy : y ∈ S) => show RingHom.id R y ∈ S from hy) x) := by
  apply SetLike.ext_iff.mpr
  -- ⊢ ∀ (x_1 : P'), x_1 ∈ ↑(canonicalEquiv S P P') (spanSingleton S x) ↔ x_1 ∈ spa …
  intro y
  -- ⊢ y ∈ ↑(canonicalEquiv S P P') (spanSingleton S x) ↔ y ∈ spanSingleton S (↑(Is …
  constructor <;> intro h
  -- ⊢ y ∈ ↑(canonicalEquiv S P P') (spanSingleton S x) → y ∈ spanSingleton S (↑(Is …
                  -- ⊢ y ∈ spanSingleton S (↑(IsLocalization.map P' (RingHom.id R) (_ : ∀ (y : R),  …
                  -- ⊢ y ∈ ↑(canonicalEquiv S P P') (spanSingleton S x)
  · rw [mem_spanSingleton]
    -- ⊢ ∃ z, z • ↑(IsLocalization.map P' (RingHom.id R) (_ : ∀ (y : R), y ∈ S → ↑(Ri …
    obtain ⟨x', hx', rfl⟩ := (mem_canonicalEquiv_apply _ _ _).mp h
    -- ⊢ ∃ z, z • ↑(IsLocalization.map P' (RingHom.id R) (_ : ∀ (y : R), y ∈ S → ↑(Ri …
    obtain ⟨z, rfl⟩ := (mem_spanSingleton _).mp hx'
    -- ⊢ ∃ z_1, z_1 • ↑(IsLocalization.map P' (RingHom.id R) (_ : ∀ (y : R), y ∈ S →  …
    use z
    -- ⊢ z • ↑(IsLocalization.map P' (RingHom.id R) (_ : ∀ (y : R), y ∈ S → ↑(RingHom …
    rw [IsLocalization.map_smul]
    -- ⊢ z • ↑(IsLocalization.map P' (RingHom.id R) (_ : ∀ (y : R), y ∈ S → ↑(RingHom …
    rfl
    -- 🎉 no goals
  · rw [mem_canonicalEquiv_apply]
    -- ⊢ ∃ y_1, y_1 ∈ spanSingleton S x ∧ ↑(IsLocalization.map P' (RingHom.id R) (_ : …
    obtain ⟨z, rfl⟩ := (mem_spanSingleton _).mp h
    -- ⊢ ∃ y, y ∈ spanSingleton S x ∧ ↑(IsLocalization.map P' (RingHom.id R) (_ : ∀ ( …
    use z • x
    -- ⊢ z • x ∈ spanSingleton S x ∧ ↑(IsLocalization.map P' (RingHom.id R) (_ : ∀ (y …
    use (mem_spanSingleton _).mpr ⟨z, rfl⟩
    -- ⊢ ↑(IsLocalization.map P' (RingHom.id R) (_ : ∀ (y : R), y ∈ S → ↑(RingHom.id  …
    simp [IsLocalization.map_smul]
    -- 🎉 no goals
#align fractional_ideal.canonical_equiv_span_singleton FractionalIdeal.canonicalEquiv_spanSingleton

theorem mem_singleton_mul {x y : P} {I : FractionalIdeal S P} :
    y ∈ spanSingleton S x * I ↔ ∃ y' ∈ I, y = x * y' := by
  constructor
  -- ⊢ y ∈ spanSingleton S x * I → ∃ y', y' ∈ I ∧ y = x * y'
  · intro h
    -- ⊢ ∃ y', y' ∈ I ∧ y = x * y'
    refine FractionalIdeal.mul_induction_on h ?_ ?_
    -- ⊢ ∀ (i : P), i ∈ spanSingleton S x → ∀ (j : P), j ∈ I → ∃ y', y' ∈ I ∧ i * j = …
    · intro x' hx' y' hy'
      -- ⊢ ∃ y'_1, y'_1 ∈ I ∧ x' * y' = x * y'_1
      obtain ⟨a, ha⟩ := (mem_spanSingleton S).mp hx'
      -- ⊢ ∃ y'_1, y'_1 ∈ I ∧ x' * y' = x * y'_1
      use a • y', Submodule.smul_mem (I : Submodule R P) a hy'
      -- ⊢ x' * y' = x * a • y'
      rw [← ha, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      -- 🎉 no goals
    · rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
      -- ⊢ ∃ y'_1, y'_1 ∈ I ∧ x * y + x * y' = x * y'_1
      exact ⟨y + y', Submodule.add_mem (I : Submodule R P) hy hy', (mul_add _ _ _).symm⟩
      -- 🎉 no goals
  · rintro ⟨y', hy', rfl⟩
    -- ⊢ x * y' ∈ spanSingleton S x * I
    exact mul_mem_mul ((mem_spanSingleton S).mpr ⟨1, one_smul _ _⟩) hy'
    -- 🎉 no goals
#align fractional_ideal.mem_singleton_mul FractionalIdeal.mem_singleton_mul

variable (K)

theorem mk'_mul_coeIdeal_eq_coeIdeal {I J : Ideal R₁} {x y : R₁} (hy : y ∈ R₁⁰) :
    spanSingleton R₁⁰ (IsLocalization.mk' K x ⟨y, hy⟩) * I = (J : FractionalIdeal R₁⁰ K) ↔
      Ideal.span {x} * I = Ideal.span {y} * J := by
  have :
    spanSingleton R₁⁰ (IsLocalization.mk' _ (1 : R₁) ⟨y, hy⟩) *
        spanSingleton R₁⁰ (algebraMap R₁ K y) =
      1 := by
    rw [spanSingleton_mul_spanSingleton, mul_comm, ← IsLocalization.mk'_eq_mul_mk'_one,
      IsLocalization.mk'_self, spanSingleton_one]
  let y' : (FractionalIdeal R₁⁰ K)ˣ := Units.mkOfMulEqOne _ _ this
  -- ⊢ spanSingleton R₁⁰ (mk' K x { val := y, property := hy }) * ↑I = ↑J ↔ Ideal.s …
  have coe_y' : ↑y' = spanSingleton R₁⁰ (IsLocalization.mk' K (1 : R₁) ⟨y, hy⟩) := rfl
  -- ⊢ spanSingleton R₁⁰ (mk' K x { val := y, property := hy }) * ↑I = ↑J ↔ Ideal.s …
  refine' Iff.trans _ (y'.mul_right_inj.trans coeIdeal_inj)
  -- ⊢ spanSingleton R₁⁰ (mk' K x { val := y, property := hy }) * ↑I = ↑J ↔ ↑y' * ↑ …
  rw [coe_y', coeIdeal_mul, coeIdeal_span_singleton, coeIdeal_mul, coeIdeal_span_singleton, ←
    mul_assoc, spanSingleton_mul_spanSingleton, ← mul_assoc, spanSingleton_mul_spanSingleton,
    mul_comm (mk' _ _ _), ← IsLocalization.mk'_eq_mul_mk'_one, mul_comm (mk' _ _ _), ←
    IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_self, spanSingleton_one, one_mul]
#align fractional_ideal.mk'_mul_coe_ideal_eq_coe_ideal FractionalIdeal.mk'_mul_coeIdeal_eq_coeIdeal

variable {K}

theorem spanSingleton_mul_coeIdeal_eq_coeIdeal {I J : Ideal R₁} {z : K} :
    spanSingleton R₁⁰ z * (I : FractionalIdeal R₁⁰ K) = J ↔
      Ideal.span {((IsLocalization.sec R₁⁰ z).1 : R₁)} * I =
        Ideal.span {((IsLocalization.sec R₁⁰ z).2 : R₁)} * J :=
  by-- `erw` to deal with the distinction between `y` and `⟨y.1, y.2⟩`
  erw [← mk'_mul_coeIdeal_eq_coeIdeal K (IsLocalization.sec R₁⁰ z).2.prop,
    IsLocalization.mk'_sec K z]
#align fractional_ideal.span_singleton_mul_coe_ideal_eq_coe_ideal FractionalIdeal.spanSingleton_mul_coeIdeal_eq_coeIdeal

variable [IsDomain R₁]

theorem one_div_spanSingleton (x : K) : 1 / spanSingleton R₁⁰ x = spanSingleton R₁⁰ x⁻¹ :=
  if h : x = 0 then by simp [h] else (eq_one_div_of_mul_eq_one_right _ _ (by simp [h])).symm
                       -- 🎉 no goals
                                                                             -- 🎉 no goals
#align fractional_ideal.one_div_span_singleton FractionalIdeal.one_div_spanSingleton

@[simp]
theorem div_spanSingleton (J : FractionalIdeal R₁⁰ K) (d : K) :
    J / spanSingleton R₁⁰ d = spanSingleton R₁⁰ d⁻¹ * J := by
  rw [← one_div_spanSingleton]
  -- ⊢ J / spanSingleton R₁⁰ d = 1 / spanSingleton R₁⁰ d * J
  by_cases hd : d = 0
  -- ⊢ J / spanSingleton R₁⁰ d = 1 / spanSingleton R₁⁰ d * J
  · simp only [hd, spanSingleton_zero, div_zero, zero_mul]
    -- 🎉 no goals
  have h_spand : spanSingleton R₁⁰ d ≠ 0 := mt spanSingleton_eq_zero_iff.mp hd
  -- ⊢ J / spanSingleton R₁⁰ d = 1 / spanSingleton R₁⁰ d * J
  apply le_antisymm
  -- ⊢ J / spanSingleton R₁⁰ d ≤ 1 / spanSingleton R₁⁰ d * J
  · intro x hx
    -- ⊢ x ∈ (fun a => ↑a) (1 / spanSingleton R₁⁰ d * J)
    dsimp only [val_eq_coe] at hx ⊢ -- Porting note: get rid of the partially applied `coe`s
    -- ⊢ x ∈ ↑(1 / spanSingleton R₁⁰ d * J)
    rw [coe_div h_spand, Submodule.mem_div_iff_forall_mul_mem] at hx
    -- ⊢ x ∈ ↑(1 / spanSingleton R₁⁰ d * J)
    specialize hx d (mem_spanSingleton_self R₁⁰ d)
    -- ⊢ x ∈ ↑(1 / spanSingleton R₁⁰ d * J)
    have h_xd : x = d⁻¹ * (x * d) := by field_simp
    -- ⊢ x ∈ ↑(1 / spanSingleton R₁⁰ d * J)
    rw [coe_mul, one_div_spanSingleton, h_xd]
    -- ⊢ d⁻¹ * (x * d) ∈ ↑(spanSingleton R₁⁰ d⁻¹) * ↑J
    exact Submodule.mul_mem_mul (mem_spanSingleton_self R₁⁰ _) hx
    -- 🎉 no goals
  · rw [le_div_iff_mul_le h_spand, mul_assoc, mul_left_comm, one_div_spanSingleton,
      spanSingleton_mul_spanSingleton, inv_mul_cancel hd, spanSingleton_one, mul_one]
#align fractional_ideal.div_span_singleton FractionalIdeal.div_spanSingleton

theorem exists_eq_spanSingleton_mul (I : FractionalIdeal R₁⁰ K) :
    ∃ (a : R₁) (aI : Ideal R₁), a ≠ 0 ∧ I = spanSingleton R₁⁰ (algebraMap R₁ K a)⁻¹ * aI := by
  obtain ⟨a_inv, nonzero, ha⟩ := I.isFractional
  -- ⊢ ∃ a aI, a ≠ 0 ∧ I = spanSingleton R₁⁰ (↑(algebraMap R₁ K) a)⁻¹ * ↑aI
  have nonzero := mem_nonZeroDivisors_iff_ne_zero.mp nonzero
  -- ⊢ ∃ a aI, a ≠ 0 ∧ I = spanSingleton R₁⁰ (↑(algebraMap R₁ K) a)⁻¹ * ↑aI
  have map_a_nonzero : algebraMap R₁ K a_inv ≠ 0 :=
    mt IsFractionRing.to_map_eq_zero_iff.mp nonzero
  refine'
    ⟨a_inv,
      Submodule.comap (Algebra.linearMap R₁ K) ↑(spanSingleton R₁⁰ (algebraMap R₁ K a_inv) * I),
      nonzero, ext fun x => Iff.trans ⟨_, _⟩ mem_singleton_mul.symm⟩
  · intro hx
    -- ⊢ ∃ y', y' ∈ ↑(comap (Algebra.linearMap R₁ K) ↑(spanSingleton R₁⁰ (↑(algebraMa …
    obtain ⟨x', hx'⟩ := ha x hx
    -- ⊢ ∃ y', y' ∈ ↑(comap (Algebra.linearMap R₁ K) ↑(spanSingleton R₁⁰ (↑(algebraMa …
    rw [Algebra.smul_def] at hx'
    -- ⊢ ∃ y', y' ∈ ↑(comap (Algebra.linearMap R₁ K) ↑(spanSingleton R₁⁰ (↑(algebraMa …
    refine' ⟨algebraMap R₁ K x', (mem_coeIdeal _).mpr ⟨x', mem_singleton_mul.mpr _, rfl⟩, _⟩
    -- ⊢ ∃ y', y' ∈ I ∧ ↑(Algebra.linearMap R₁ K) x' = ↑(algebraMap R₁ K) a_inv * y'
    · exact ⟨x, hx, hx'⟩
      -- 🎉 no goals
    · rw [hx', ← mul_assoc, inv_mul_cancel map_a_nonzero, one_mul]
      -- 🎉 no goals
  · rintro ⟨y, hy, rfl⟩
    -- ⊢ (↑(algebraMap R₁ K) a_inv)⁻¹ * y ∈ I
    obtain ⟨x', hx', rfl⟩ := (mem_coeIdeal _).mp hy
    -- ⊢ (↑(algebraMap R₁ K) a_inv)⁻¹ * ↑(algebraMap R₁ K) x' ∈ I
    obtain ⟨y', hy', hx'⟩ := mem_singleton_mul.mp hx'
    -- ⊢ (↑(algebraMap R₁ K) a_inv)⁻¹ * ↑(algebraMap R₁ K) x' ∈ I
    rw [Algebra.linearMap_apply] at hx'
    -- ⊢ (↑(algebraMap R₁ K) a_inv)⁻¹ * ↑(algebraMap R₁ K) x' ∈ I
    rwa [hx', ← mul_assoc, inv_mul_cancel map_a_nonzero, one_mul]
    -- 🎉 no goals
#align fractional_ideal.exists_eq_span_singleton_mul FractionalIdeal.exists_eq_spanSingleton_mul

instance isPrincipal {R} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Algebra R K]
    [IsFractionRing R K] (I : FractionalIdeal R⁰ K) : (I : Submodule R K).IsPrincipal := by
  obtain ⟨a, aI, -, ha⟩ := exists_eq_spanSingleton_mul I
  -- ⊢ IsPrincipal ↑I
  use (algebraMap R K a)⁻¹ * algebraMap R K (generator aI)
  -- ⊢ ↑I = span R {(↑(algebraMap R K) a)⁻¹ * ↑(algebraMap R K) (generator aI)}
  suffices I = spanSingleton R⁰ ((algebraMap R K a)⁻¹ * algebraMap R K (generator aI)) by
    rw [spanSingleton] at this
    exact congr_arg Subtype.val this
  conv_lhs => rw [ha, ← span_singleton_generator aI]
  -- ⊢ spanSingleton R⁰ (↑(algebraMap R K) a)⁻¹ * ↑(span R {generator aI}) = spanSi …
  rw [Ideal.submodule_span_eq, coeIdeal_span_singleton (generator aI),
    spanSingleton_mul_spanSingleton]
#align fractional_ideal.is_principal FractionalIdeal.isPrincipal

theorem le_spanSingleton_mul_iff {x : P} {I J : FractionalIdeal S P} :
    I ≤ spanSingleton S x * J ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI :=
  show (∀ {zI} (hzI : zI ∈ I), zI ∈ spanSingleton _ x * J) ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI by
    simp only [mem_singleton_mul, eq_comm]
    -- 🎉 no goals
#align fractional_ideal.le_span_singleton_mul_iff FractionalIdeal.le_spanSingleton_mul_iff

theorem spanSingleton_mul_le_iff {x : P} {I J : FractionalIdeal S P} :
    spanSingleton _ x * I ≤ J ↔ ∀ z ∈ I, x * z ∈ J := by
  simp only [mul_le, mem_singleton_mul, mem_spanSingleton]
  -- ⊢ (∀ (i : P), (∃ z, z • x = i) → ∀ (j : P), j ∈ I → i * j ∈ J) ↔ ∀ (z : P), z  …
  constructor
  -- ⊢ (∀ (i : P), (∃ z, z • x = i) → ∀ (j : P), j ∈ I → i * j ∈ J) → ∀ (z : P), z  …
  · intro h zI hzI
    -- ⊢ x * zI ∈ J
    exact h x ⟨1, one_smul _ _⟩ zI hzI
    -- 🎉 no goals
  · rintro h _ ⟨z, rfl⟩ zI hzI
    -- ⊢ z • x * zI ∈ J
    rw [Algebra.smul_mul_assoc]
    -- ⊢ z • (x * zI) ∈ J
    exact Submodule.smul_mem J.1 _ (h zI hzI)
    -- 🎉 no goals
#align fractional_ideal.span_singleton_mul_le_iff FractionalIdeal.spanSingleton_mul_le_iff

theorem eq_spanSingleton_mul {x : P} {I J : FractionalIdeal S P} :
    I = spanSingleton _ x * J ↔ (∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI) ∧ ∀ z ∈ J, x * z ∈ I := by
  simp only [le_antisymm_iff, le_spanSingleton_mul_iff, spanSingleton_mul_le_iff]
  -- 🎉 no goals
#align fractional_ideal.eq_span_singleton_mul FractionalIdeal.eq_spanSingleton_mul

end PrincipalIdealRing

variable {R₁ : Type*} [CommRing R₁]

variable {K : Type*} [Field K] [Algebra R₁ K] [frac : IsFractionRing R₁ K]

attribute [local instance] Classical.propDecidable

theorem isNoetherian_zero : IsNoetherian R₁ (0 : FractionalIdeal R₁⁰ K) :=
  isNoetherian_submodule.mpr fun I (hI : I ≤ (0 : FractionalIdeal R₁⁰ K)) => by
    rw [coe_zero] at hI
    -- ⊢ FG I
    rw [le_bot_iff.mp hI]
    -- ⊢ FG ⊥
    exact fg_bot
    -- 🎉 no goals
#align fractional_ideal.is_noetherian_zero FractionalIdeal.isNoetherian_zero

theorem isNoetherian_iff {I : FractionalIdeal R₁⁰ K} :
    IsNoetherian R₁ I ↔ ∀ J ≤ I, (J : Submodule R₁ K).FG :=
  isNoetherian_submodule.trans ⟨fun h _ hJ => h _ hJ, fun h J hJ => h ⟨J, isFractional_of_le hJ⟩ hJ⟩
#align fractional_ideal.is_noetherian_iff FractionalIdeal.isNoetherian_iff

theorem isNoetherian_coeIdeal [IsNoetherianRing R₁] (I : Ideal R₁) :
    IsNoetherian R₁ (I : FractionalIdeal R₁⁰ K) := by
  rw [isNoetherian_iff]
  -- ⊢ ∀ (J : FractionalIdeal R₁⁰ K), J ≤ ↑I → FG ↑J
  intro J hJ
  -- ⊢ FG ↑J
  obtain ⟨J, rfl⟩ := le_one_iff_exists_coeIdeal.mp (le_trans hJ coeIdeal_le_one)
  -- ⊢ FG ↑↑J
  exact (IsNoetherian.noetherian J).map _
  -- 🎉 no goals
#align fractional_ideal.is_noetherian_coe_ideal FractionalIdeal.isNoetherian_coeIdeal

variable [IsDomain R₁]

theorem isNoetherian_spanSingleton_inv_to_map_mul (x : R₁) {I : FractionalIdeal R₁⁰ K}
    (hI : IsNoetherian R₁ I) :
    IsNoetherian R₁ (spanSingleton R₁⁰ (algebraMap R₁ K x)⁻¹ * I : FractionalIdeal R₁⁰ K) := by
  by_cases hx : x = 0
  -- ⊢ IsNoetherian R₁ { x_1 // x_1 ∈ ↑(spanSingleton R₁⁰ (↑(algebraMap R₁ K) x)⁻¹  …
  · rw [hx, RingHom.map_zero, inv_zero, spanSingleton_zero, zero_mul]
    -- ⊢ IsNoetherian R₁ { x // x ∈ ↑0 }
    exact isNoetherian_zero
    -- 🎉 no goals
  have h_gx : algebraMap R₁ K x ≠ 0 :=
    mt ((injective_iff_map_eq_zero (algebraMap R₁ K)).mp (IsFractionRing.injective _ _) x) hx
  have h_spanx : spanSingleton R₁⁰ (algebraMap R₁ K x) ≠ 0 := spanSingleton_ne_zero_iff.mpr h_gx
  -- ⊢ IsNoetherian R₁ { x_1 // x_1 ∈ ↑(spanSingleton R₁⁰ (↑(algebraMap R₁ K) x)⁻¹  …
  rw [isNoetherian_iff] at hI ⊢
  -- ⊢ ∀ (J : FractionalIdeal R₁⁰ ((fun x => K) x)), J ≤ spanSingleton R₁⁰ (↑(algeb …
  intro J hJ
  -- ⊢ FG ↑J
  rw [← div_spanSingleton, le_div_iff_mul_le h_spanx] at hJ
  -- ⊢ FG ↑J
  obtain ⟨s, hs⟩ := hI _ hJ
  -- ⊢ FG ↑J
  use s * {(algebraMap R₁ K x)⁻¹}
  -- ⊢ span R₁ ↑(s * {(↑(algebraMap R₁ K) x)⁻¹}) = ↑J
  rw [Finset.coe_mul, Finset.coe_singleton, ← span_mul_span, hs, ← coe_spanSingleton R₁⁰, ←
    coe_mul, mul_assoc, spanSingleton_mul_spanSingleton, mul_inv_cancel h_gx, spanSingleton_one,
    mul_one]
#align fractional_ideal.is_noetherian_span_singleton_inv_to_map_mul FractionalIdeal.isNoetherian_spanSingleton_inv_to_map_mul

/-- Every fractional ideal of a noetherian integral domain is noetherian. -/
theorem isNoetherian [IsNoetherianRing R₁] (I : FractionalIdeal R₁⁰ K) : IsNoetherian R₁ I := by
  obtain ⟨d, J, _, rfl⟩ := exists_eq_spanSingleton_mul I
  -- ⊢ IsNoetherian R₁ { x // x ∈ ↑(spanSingleton R₁⁰ (↑(algebraMap R₁ K) d)⁻¹ * ↑J …
  apply isNoetherian_spanSingleton_inv_to_map_mul
  -- ⊢ IsNoetherian R₁ { x // x ∈ ↑↑J }
  apply isNoetherian_coeIdeal
  -- 🎉 no goals
#align fractional_ideal.is_noetherian FractionalIdeal.isNoetherian

section Adjoin

variable (S)
variable (x : P) (hx : IsIntegral R x)

/-- `A[x]` is a fractional ideal for every integral `x`. -/
theorem isFractional_adjoin_integral :
    IsFractional S (Subalgebra.toSubmodule (Algebra.adjoin R ({x} : Set P))) :=
  isFractional_of_fg (FG_adjoin_singleton_of_integral x hx)
#align fractional_ideal.is_fractional_adjoin_integral FractionalIdeal.isFractional_adjoin_integral

/-- `FractionalIdeal.adjoinIntegral (S : Submonoid R) x hx` is `R[x]` as a fractional ideal,
where `hx` is a proof that `x : P` is integral over `R`. -/
-- Porting note: `@[simps]` generated a `Subtype.val` coercion instead of a
-- `FractionalIdeal.coeToSubmodule` coercion
def adjoinIntegral : FractionalIdeal S P :=
  ⟨_, isFractional_adjoin_integral S x hx⟩
#align fractional_ideal.adjoin_integral FractionalIdeal.adjoinIntegral

@[simp]
theorem adjoinIntegral_coe :
    (adjoinIntegral S x hx : Submodule R P) =
      (Subalgebra.toSubmodule (Algebra.adjoin R ({x} : Set P))) :=
  rfl

theorem mem_adjoinIntegral_self : x ∈ adjoinIntegral S x hx :=
  Algebra.subset_adjoin (Set.mem_singleton x)
#align fractional_ideal.mem_adjoin_integral_self FractionalIdeal.mem_adjoinIntegral_self

end Adjoin

end FractionalIdeal
