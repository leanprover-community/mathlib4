/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge
-/
import Mathlib.GroupTheory.MonoidLocalization
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.RingTheory.OreLocalization.OreSet
import Mathlib.Tactic.NoncommRing

#align_import ring_theory.ore_localization.basic from "leanprover-community/mathlib"@"861a26926586cd46ff80264d121cdb6fa0e35cc1"

/-!

# Localization over right Ore sets.

This file defines the localization of a monoid over a right Ore set and proves its universal
mapping property. It then extends the definition and its properties first to semirings and then
to rings. We show that in the case of a commutative monoid this definition coincides with the
common monoid localization. Finally we show that in a ring without zero divisors, taking the Ore
localization at `R - {0}` results in a division ring.

## Notations

Introduces the notation `R[S⁻¹]` for the Ore localization of a monoid `R` at a right Ore
subset `S`. Also defines a new heterogeneous division notation `r /ₒ s` for a numerator `r : R` and
a denominator `s : S`.

## References

* <https://ncatlab.org/nlab/show/Ore+localization>
* [Zoran Škoda, *Noncommutative localization in noncommutative geometry*][skoda2006]


## Tags
localization, Ore, non-commutative

-/


universe u

open OreLocalization

namespace OreLocalization

variable (R : Type*) [Monoid R] (S : Submonoid R) [OreSet S]

/-- The setoid on `R × S` used for the Ore localization. -/
def oreEqv : Setoid (R × S) where
  r rs rs' := ∃ (u : S) (v : R), rs'.1 * u = rs.1 * v ∧ (rs'.2 : R) * u = rs.2 * v
  iseqv := by
    refine ⟨fun _ => ⟨1, 1, by simp⟩, ?_, ?_⟩
    · rintro ⟨r, s⟩ ⟨r', s'⟩ ⟨u, v, hru, hsu⟩; dsimp only at *
      rcases oreCondition (s : R) s' with ⟨r₂, s₂, h₁⟩
      rcases oreCondition r₂ u with ⟨r₃, s₃, h₂⟩
      have : (s : R) * ((v : R) * r₃) = (s : R) * (s₂ * s₃) := by
        -- Porting note: the proof used `assoc_rw`
        rw [← mul_assoc _ (s₂ : R), h₁, mul_assoc, h₂, ← mul_assoc, ← hsu, mul_assoc]
      rcases ore_left_cancel (v * r₃) (s₂ * s₃) s this with ⟨w, hw⟩
      refine ⟨s₂ * s₃ * w, u * r₃ * w, ?_, ?_⟩ <;> simp only [Submonoid.coe_mul, ← hw]
      · simp only [← mul_assoc, hru]
      · simp only [← mul_assoc, hsu]
    · rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨r₃, s₃⟩ ⟨u, v, hur₁, hs₁u⟩ ⟨u', v', hur₂, hs₂u⟩
      rcases oreCondition v' u with ⟨r', s', h⟩; dsimp only at *
      refine ⟨u' * s', v * r', ?_, ?_⟩ <;> simp only [Submonoid.coe_mul, ← mul_assoc]
      · rw [hur₂, mul_assoc, h, ← mul_assoc, hur₁]
      · rw [hs₂u, mul_assoc, h, ← mul_assoc, hs₁u]
#align ore_localization.ore_eqv OreLocalization.oreEqv

end OreLocalization

/-- The ore localization of a monoid and a submonoid fulfilling the ore condition. -/
def OreLocalization (R : Type*) [Monoid R] (S : Submonoid R) [OreSet S] :=
  Quotient (OreLocalization.oreEqv R S)
#align ore_localization OreLocalization

namespace OreLocalization

section Monoid

variable {R : Type*} [Monoid R] {S : Submonoid R}
variable (R S) [OreSet S]

@[inherit_doc OreLocalization]
scoped syntax:1075 term noWs atomic("[" term "⁻¹" noWs "]") : term
macro_rules | `($R[$S⁻¹]) => ``(OreLocalization $R $S)

attribute [local instance] oreEqv

variable {R S}

/-- The division in the ore localization `R[S⁻¹]`, as a fraction of an element of `R` and `S`. -/
def oreDiv (r : R) (s : S) : R[S⁻¹] :=
  Quotient.mk' (r, s)
#align ore_localization.ore_div OreLocalization.oreDiv

@[inherit_doc]
infixl:70 " /ₒ " => oreDiv

@[elab_as_elim]
protected theorem ind {β : R[S⁻¹] → Prop} (c : ∀ (r : R) (s : S), β (r /ₒ s)) : ∀ q, β q := by
  apply Quotient.ind
  rintro ⟨r, s⟩
  exact c r s
#align ore_localization.ind OreLocalization.ind

theorem oreDiv_eq_iff {r₁ r₂ : R} {s₁ s₂ : S} :
    r₁ /ₒ s₁ = r₂ /ₒ s₂ ↔ ∃ (u : S) (v : R), r₂ * u = r₁ * v ∧ (s₂ : R) * u = s₁ * v :=
  Quotient.eq''
#align ore_localization.ore_div_eq_iff OreLocalization.oreDiv_eq_iff

/-- A fraction `r /ₒ s` is equal to its expansion by an arbitrary factor `t` if `s * t ∈ S`. -/
protected theorem expand (r : R) (s : S) (t : R) (hst : (s : R) * t ∈ S) :
    r /ₒ s = r * t /ₒ ⟨s * t, hst⟩ := by
  apply Quotient.sound
  refine ⟨s, t * s, ?_, ?_⟩ <;> dsimp <;> rw [mul_assoc]
#align ore_localization.expand OreLocalization.expand

/-- A fraction is equal to its expansion by a factor from s. -/
protected theorem expand' (r : R) (s s' : S) : r /ₒ s = r * s' /ₒ (s * s') :=
  OreLocalization.expand r s s' (by norm_cast; apply SetLike.coe_mem)
#align ore_localization.expand' OreLocalization.expand'

/-- Fractions which differ by a factor of the numerator can be proven equal if
those factors expand to equal elements of `R`. -/
protected theorem eq_of_num_factor_eq {r r' r₁ r₂ : R} {s t : S} (h : r * t = r' * t) :
    r₁ * r * r₂ /ₒ s = r₁ * r' * r₂ /ₒ s := by
  rcases oreCondition r₂ t with ⟨r₂', t', hr₂⟩
  -- Porting note (#11215): TODO: use `assoc_rw`?
  calc
    r₁ * r * r₂ /ₒ s = r₁ * r * r₂ * t' /ₒ (s * t') := OreLocalization.expand (r₁ * r * r₂) s t' _
    _ = r₁ * r * (r₂ * t') /ₒ (s * t') := by simp [← mul_assoc]
    _ = r₁ * r * (t * r₂') /ₒ (s * t') := by rw [hr₂]
    _ = r₁ * (r * t) * r₂' /ₒ (s * t') := by simp [← mul_assoc]
    _ = r₁ * (r' * t) * r₂' /ₒ (s * t') := by rw [h]
    _ = r₁ * r' * (t * r₂') /ₒ (s * t') := by simp [← mul_assoc]
    _ = r₁ * r' * (r₂ * t') /ₒ (s * t') := by rw [hr₂]
    _ = r₁ * r' * r₂ * t' /ₒ (s * t') := by simp [← mul_assoc]
    _ = r₁ * r' * r₂ /ₒ s := (OreLocalization.expand _ _ _ _).symm
#align ore_localization.eq_of_num_factor_eq OreLocalization.eq_of_num_factor_eq

/-- A function or predicate over `R` and `S` can be lifted to `R[S⁻¹]` if it is invariant
under expansion on the right. -/
def liftExpand {C : Sort*} (P : R → S → C)
    (hP : ∀ (r t : R) (s : S) (ht : (s : R) * t ∈ S), P r s = P (r * t) ⟨s * t, ht⟩) : R[S⁻¹] → C :=
  Quotient.lift (fun p : R × S => P p.1 p.2) fun (r₁, s₁) (r₂, s₂) ⟨u, v, hr₂, hs₂⟩ => by
    dsimp at *
    have s₁vS : (s₁ : R) * v ∈ S := by
      rw [← hs₂, ← S.coe_mul]
      exact SetLike.coe_mem (s₂ * u)
    replace hs₂ : s₂ * u = ⟨(s₁ : R) * v, s₁vS⟩ := by ext; simp [hs₂]
    rw [hP r₁ v s₁ s₁vS, hP r₂ u s₂ (by norm_cast; rwa [hs₂]), hr₂]
    simp only [← hs₂]; rfl
#align ore_localization.lift_expand OreLocalization.liftExpand

@[simp]
theorem liftExpand_of {C : Sort*} {P : R → S → C}
    {hP : ∀ (r t : R) (s : S) (ht : (s : R) * t ∈ S), P r s = P (r * t) ⟨s * t, ht⟩} (r : R)
    (s : S) : liftExpand P hP (r /ₒ s) = P r s :=
  rfl
#align ore_localization.lift_expand_of OreLocalization.liftExpand_of

/-- A version of `liftExpand` used to simultaneously lift functions with two arguments
in `R[S⁻¹]`. -/
def lift₂Expand {C : Sort*} (P : R → S → R → S → C)
    (hP :
      ∀ (r₁ t₁ : R) (s₁ : S) (ht₁ : (s₁ : R) * t₁ ∈ S) (r₂ t₂ : R) (s₂ : S)
        (ht₂ : (s₂ : R) * t₂ ∈ S),
        P r₁ s₁ r₂ s₂ = P (r₁ * t₁) ⟨s₁ * t₁, ht₁⟩ (r₂ * t₂) ⟨s₂ * t₂, ht₂⟩) :
    R[S⁻¹] → R[S⁻¹] → C :=
  liftExpand
    (fun r₁ s₁ => liftExpand (P r₁ s₁) fun r₂ t₂ s₂ ht₂ => by
      have := hP r₁ 1 s₁ (by simp) r₂ t₂ s₂ ht₂
      simp [this])
    fun r₁ t₁ s₁ ht₁ => by
    ext x; induction' x using OreLocalization.ind with r₂ s₂
    dsimp only
    rw [liftExpand_of, liftExpand_of, hP r₁ t₁ s₁ ht₁ r₂ 1 s₂ (by simp)]; simp
#align ore_localization.lift₂_expand OreLocalization.lift₂Expand

@[simp]
theorem lift₂Expand_of {C : Sort*} {P : R → S → R → S → C}
    {hP :
      ∀ (r₁ t₁ : R) (s₁ : S) (ht₁ : (s₁ : R) * t₁ ∈ S) (r₂ t₂ : R) (s₂ : S)
        (ht₂ : (s₂ : R) * t₂ ∈ S),
        P r₁ s₁ r₂ s₂ = P (r₁ * t₁) ⟨s₁ * t₁, ht₁⟩ (r₂ * t₂) ⟨s₂ * t₂, ht₂⟩}
    (r₁ : R) (s₁ : S) (r₂ : R) (s₂ : S) : lift₂Expand P hP (r₁ /ₒ s₁) (r₂ /ₒ s₂) = P r₁ s₁ r₂ s₂ :=
  rfl
#align ore_localization.lift₂_expand_of OreLocalization.lift₂Expand_of

private def mul' (r₁ : R) (s₁ : S) (r₂ : R) (s₂ : S) : R[S⁻¹] :=
  r₁ * oreNum r₂ s₁ /ₒ (s₂ * oreDenom r₂ s₁)

private theorem mul'_char (r₁ r₂ : R) (s₁ s₂ : S) (u : S) (v : R) (huv : r₂ * (u : R) = s₁ * v) :
    OreLocalization.mul' r₁ s₁ r₂ s₂ = r₁ * v /ₒ (s₂ * u) := by
  -- Porting note: `assoc_rw` was not ported yet
  simp only [mul']
  have h₀ := ore_eq r₂ s₁; set v₀ := oreNum r₂ s₁; set u₀ := oreDenom r₂ s₁
  rcases oreCondition (u₀ : R) u with ⟨r₃, s₃, h₃⟩
  have :=
    calc
      (s₁ : R) * (v * r₃) = r₂ * u * r₃ := by rw [← mul_assoc, ← huv]
      _ = r₂ * u₀ * s₃ := by rw [mul_assoc, mul_assoc, h₃]
      _ = s₁ * (v₀ * s₃) := by rw [← mul_assoc, h₀]
  rcases ore_left_cancel _ _ _ this with ⟨s₄, hs₄⟩
  symm; rw [oreDiv_eq_iff]
  use s₃ * s₄; use r₃ * s₄; simp only [Submonoid.coe_mul]; constructor
  · rw [mul_assoc (b := v₀), ← mul_assoc (a := v₀), ← hs₄]
    simp only [mul_assoc]
  · rw [mul_assoc (b := (u₀ : R)), ← mul_assoc (a := (u₀ : R)), h₃]
    simp only [mul_assoc]

/-- The multiplication on the Ore localization of monoids. -/
protected def mul : R[S⁻¹] → R[S⁻¹] → R[S⁻¹] :=
  lift₂Expand mul' fun r₂ p s₂ hp r₁ r s₁ hr => by
    have h₁ := ore_eq r₁ s₂
    set r₁' := oreNum r₁ s₂
    set s₂' := oreDenom r₁ s₂
    rcases oreCondition (↑s₂ * r₁') ⟨s₂ * p, hp⟩ with ⟨p', s_star, h₂⟩
    dsimp at h₂
    rcases oreCondition r (s₂' * s_star) with ⟨p_flat, s_flat, h₃⟩
    simp only [S.coe_mul] at h₃
    have : r₁ * r * s_flat = s₂ * p * (p' * p_flat) := by
      rw [← mul_assoc, ← h₂, ← h₁, mul_assoc, h₃]
      simp only [mul_assoc]
    rw [mul'_char (r₂ * p) (r₁ * r) ⟨↑s₂ * p, hp⟩ ⟨↑s₁ * r, hr⟩ _ _ this]
    clear this
    have hsssp : ↑s₁ * ↑s₂' * ↑s_star * p_flat ∈ S := by
      rw [mul_assoc, mul_assoc, ← mul_assoc (s₂' : R), ← h₃, ← mul_assoc]
      exact S.mul_mem hr (SetLike.coe_mem s_flat)
    have : (⟨↑s₁ * r, hr⟩ : S) * s_flat = ⟨s₁ * s₂' * s_star * p_flat, hsssp⟩ := by
      ext
      simp only [Submonoid.coe_mul]
      rw [mul_assoc, h₃, ← mul_assoc, ← mul_assoc]
    rw [this]
    clear this
    rcases ore_left_cancel (p * p') (r₁' * (s_star : R)) s₂ (by simp [← mul_assoc, h₂])
      with ⟨s₂'', h₂''⟩
    rw [← mul_assoc, mul_assoc r₂, OreLocalization.eq_of_num_factor_eq h₂'']
    norm_cast at hsssp ⊢
    rw [← OreLocalization.expand _ _ _ hsssp, ← mul_assoc]
    apply OreLocalization.expand
#align ore_localization.mul OreLocalization.mul

instance instMulOreLocalization : Mul R[S⁻¹] :=
  ⟨OreLocalization.mul⟩

theorem oreDiv_mul_oreDiv {r₁ r₂ : R} {s₁ s₂ : S} :
    r₁ /ₒ s₁ * (r₂ /ₒ s₂) = r₁ * oreNum r₂ s₁ /ₒ (s₂ * oreDenom r₂ s₁) :=
  rfl
#align ore_localization.ore_div_mul_ore_div OreLocalization.oreDiv_mul_oreDiv

/-- A characterization lemma for the multiplication on the Ore localization, allowing for a choice
of Ore numerator and Ore denominator. -/
theorem oreDiv_mul_char (r₁ r₂ : R) (s₁ s₂ : S) (r' : R) (s' : S) (huv : r₂ * (s' : R) = s₁ * r') :
    r₁ /ₒ s₁ * (r₂ /ₒ s₂) = r₁ * r' /ₒ (s₂ * s') :=
  mul'_char r₁ r₂ s₁ s₂ s' r' huv
#align ore_localization.ore_div_mul_char OreLocalization.oreDiv_mul_char

/-- Another characterization lemma for the multiplication on the Ore localizaion delivering
Ore witnesses and conditions bundled in a sigma type. -/
def oreDivMulChar' (r₁ r₂ : R) (s₁ s₂ : S) :
    Σ'r' : R, Σ's' : S, r₂ * (s' : R) = s₁ * r' ∧ r₁ /ₒ s₁ * (r₂ /ₒ s₂) = r₁ * r' /ₒ (s₂ * s') :=
  ⟨oreNum r₂ s₁, oreDenom r₂ s₁, ore_eq r₂ s₁, oreDiv_mul_oreDiv⟩
#align ore_localization.ore_div_mul_char' OreLocalization.oreDivMulChar'

instance instOneOreLocalization : One R[S⁻¹] :=
  ⟨1 /ₒ 1⟩

protected theorem one_def : (1 : R[S⁻¹]) = 1 /ₒ 1 :=
  rfl
#align ore_localization.one_def OreLocalization.one_def

instance : Inhabited R[S⁻¹] :=
  ⟨1⟩

@[simp]
protected theorem div_eq_one' {r : R} (hr : r ∈ S) : r /ₒ ⟨r, hr⟩ = 1 := by
  rw [OreLocalization.one_def, oreDiv_eq_iff]
  exact ⟨⟨r, hr⟩, 1, by simp, by simp⟩
#align ore_localization.div_eq_one' OreLocalization.div_eq_one'

@[simp]
protected theorem div_eq_one {s : S} : (s : R) /ₒ s = 1 :=
  OreLocalization.div_eq_one' _
#align ore_localization.div_eq_one OreLocalization.div_eq_one

protected theorem one_mul (x : R[S⁻¹]) : 1 * x = x := by
  induction' x using OreLocalization.ind with r s
  simp [OreLocalization.one_def, oreDiv_mul_char (1 : R) r (1 : S) s r 1 (by simp)]
#align ore_localization.one_mul OreLocalization.one_mul

protected theorem mul_one (x : R[S⁻¹]) : x * 1 = x := by
  induction' x using OreLocalization.ind with r s
  simp [OreLocalization.one_def, oreDiv_mul_char r 1 s 1 1 s (by simp)]
#align ore_localization.mul_one OreLocalization.mul_one

protected theorem mul_assoc (x y z : R[S⁻¹]) : x * y * z = x * (y * z) := by
  -- Porting note: `assoc_rw` was not ported yet
  induction' x using OreLocalization.ind with r₁ s₁
  induction' y using OreLocalization.ind with r₂ s₂
  induction' z using OreLocalization.ind with r₃ s₃
  rcases oreDivMulChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
  rcases oreDivMulChar' r₂ r₃ s₂ s₃ with ⟨rb, sb, hb, hb'⟩; rw [hb']; clear hb'
  rcases oreCondition rb sa with ⟨rc, sc, hc⟩
  rw [oreDiv_mul_char (r₁ * ra) r₃ (s₂ * sa) s₃ rc (sb * sc)
      (by
        simp only [Submonoid.coe_mul]
        rw [← mul_assoc, hb, mul_assoc, hc, ← mul_assoc])]
  rw [mul_assoc, ← mul_assoc s₃]
  symm; apply oreDiv_mul_char
  rw [mul_assoc, hc, ← mul_assoc (b := ra), ← ha, mul_assoc]
#align ore_localization.mul_assoc OreLocalization.mul_assoc

instance instMonoidOreLocalization : Monoid R[S⁻¹] :=
  { OreLocalization.instMulOreLocalization,
    OreLocalization.instOneOreLocalization with
    one_mul := OreLocalization.one_mul
    mul_one := OreLocalization.mul_one
    mul_assoc := OreLocalization.mul_assoc }

protected theorem mul_inv (s s' : S) : ((s : R) /ₒ s') * ((s' : R) /ₒ s) = 1 := by
  simp [oreDiv_mul_char (s : R) s' s' s 1 1 (by simp)]
#align ore_localization.mul_inv OreLocalization.mul_inv

@[simp]
protected theorem mul_one_div {r : R} {s t : S} : (r /ₒ s) * (1 /ₒ t) = r /ₒ (t * s) := by
  simp [oreDiv_mul_char r 1 s t 1 s (by simp)]
#align ore_localization.mul_one_div OreLocalization.mul_one_div

@[simp]
protected theorem mul_cancel {r : R} {s t : S} : (r /ₒ s) * ((s : R) /ₒ t) = r /ₒ t := by
  simp [oreDiv_mul_char r s s t 1 1 (by simp)]
#align ore_localization.mul_cancel OreLocalization.mul_cancel

@[simp]
protected theorem mul_cancel' {r₁ r₂ : R} {s t : S} :
    (r₁ /ₒ s) * ((s * r₂) /ₒ t) = (r₁ * r₂) /ₒ t := by
  simp [oreDiv_mul_char r₁ (s * r₂) s t r₂ 1 (by simp)]
#align ore_localization.mul_cancel' OreLocalization.mul_cancel'

@[simp]
theorem div_one_mul {p r : R} {s : S} : (r /ₒ 1) * (p /ₒ s) = (r * p) /ₒ s := by
  --TODO use coercion r ↦ r /ₒ 1
  simp [oreDiv_mul_char r p 1 s p 1 (by simp)]
#align ore_localization.div_one_mul OreLocalization.div_one_mul

/-- The fraction `s /ₒ 1` as a unit in `R[S⁻¹]`, where `s : S`. -/
def numeratorUnit (s : S) : Units R[S⁻¹] where
  val := (s : R) /ₒ 1
  inv := (1 : R) /ₒ s
  val_inv := OreLocalization.mul_inv s 1
  inv_val := OreLocalization.mul_inv 1 s
#align ore_localization.numerator_unit OreLocalization.numeratorUnit

/-- The multiplicative homomorphism from `R` to `R[S⁻¹]`, mapping `r : R` to the
fraction `r /ₒ 1`. -/
def numeratorHom : R →* R[S⁻¹] where
  toFun r := r /ₒ 1
  map_one' := rfl
  map_mul' _ _ := div_one_mul.symm
#align ore_localization.numerator_hom OreLocalization.numeratorHom

theorem numeratorHom_apply {r : R} : numeratorHom r = r /ₒ (1 : S) :=
  rfl
#align ore_localization.numerator_hom_apply OreLocalization.numeratorHom_apply

theorem numerator_isUnit (s : S) : IsUnit (numeratorHom (s : R) : R[S⁻¹]) :=
  ⟨numeratorUnit s, rfl⟩
#align ore_localization.numerator_is_unit OreLocalization.numerator_isUnit

section UMP

variable {T : Type*} [Monoid T]
variable (f : R →* T) (fS : S →* Units T)
variable (hf : ∀ s : S, f s = fS s)

/-- The universal lift from a morphism `R →* T`, which maps elements of `S` to units of `T`,
to a morphism `R[S⁻¹] →* T`. -/
def universalMulHom : R[S⁻¹] →* T where
  -- Porting note(#12129): additional beta reduction needed
  toFun x :=
    x.liftExpand (fun r s => f r * ((fS s)⁻¹ : Units T)) fun r t s ht => by
      beta_reduce
      have : (fS ⟨s * t, ht⟩ : T) = fS s * f t := by
        simp only [← hf, MonoidHom.map_mul]
      conv_rhs =>
        rw [MonoidHom.map_mul, ← mul_one (f r), ← Units.val_one, ← mul_left_inv (fS s)]
        rw [Units.val_mul, ← mul_assoc, mul_assoc _ (fS s : T), ← this, mul_assoc]
      simp only [mul_one, Units.mul_inv]
  map_one' := by beta_reduce; rw [OreLocalization.one_def, liftExpand_of]; simp
  map_mul' x y := by
    -- Porting note: `simp only []` required, not just for beta reductions
    beta_reduce
    simp only [] -- TODO more!
    induction' x using OreLocalization.ind with r₁ s₁
    induction' y using OreLocalization.ind with r₂ s₂
    rcases oreDivMulChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
    rw [liftExpand_of, liftExpand_of, liftExpand_of]
    conv_rhs =>
      congr
      · skip
      congr
      rw [← mul_one (f r₂), ← (fS sa).mul_inv, ← mul_assoc, ← hf, ← f.map_mul, ha, f.map_mul]
    rw [mul_assoc, mul_assoc, mul_assoc, ← mul_assoc _ (f s₁), hf s₁, (fS s₁).inv_mul, one_mul,
      f.map_mul, mul_assoc, fS.map_mul, ← Units.val_mul]
    rfl
#align ore_localization.universal_mul_hom OreLocalization.universalMulHom

theorem universalMulHom_apply {r : R} {s : S} :
    universalMulHom f fS hf (r /ₒ s) = f r * ((fS s)⁻¹ : Units T) :=
  rfl
#align ore_localization.universal_mul_hom_apply OreLocalization.universalMulHom_apply

theorem universalMulHom_commutes {r : R} : universalMulHom f fS hf (numeratorHom r) = f r := by
  simp [numeratorHom_apply, universalMulHom_apply]
#align ore_localization.universal_mul_hom_commutes OreLocalization.universalMulHom_commutes

/-- The universal morphism `universalMulHom` is unique. -/
theorem universalMulHom_unique (φ : R[S⁻¹] →* T) (huniv : ∀ r : R, φ (numeratorHom r) = f r) :
    φ = universalMulHom f fS hf := by
  ext x; induction' x using OreLocalization.ind with r s
  rw [universalMulHom_apply, ← huniv r, numeratorHom_apply, ← mul_one (φ (r /ₒ s)), ←
    Units.val_one, ← mul_right_inv (fS s), Units.val_mul, ← mul_assoc, ← hf, ← huniv, ← φ.map_mul,
    numeratorHom_apply, OreLocalization.mul_cancel]
#align ore_localization.universal_mul_hom_unique OreLocalization.universalMulHom_unique

end UMP

end Monoid

section CommMonoid

variable {R : Type*} [CommMonoid R] {S : Submonoid R} [OreSet S]

theorem oreDiv_mul_oreDiv_comm {r₁ r₂ : R} {s₁ s₂ : S} :
    r₁ /ₒ s₁ * (r₂ /ₒ s₂) = r₁ * r₂ /ₒ (s₁ * s₂) := by
  rw [oreDiv_mul_char r₁ r₂ s₁ s₂ r₂ s₁ (by simp [mul_comm]), mul_comm s₂]
#align ore_localization.ore_div_mul_ore_div_comm OreLocalization.oreDiv_mul_oreDiv_comm

instance : CommMonoid R[S⁻¹] :=
  { OreLocalization.instMonoidOreLocalization with
    mul_comm := fun x y => by
      induction' x using OreLocalization.ind with r₁ s₁
      induction' y using OreLocalization.ind with r₂ s₂
      rw [oreDiv_mul_oreDiv_comm, oreDiv_mul_oreDiv_comm, mul_comm r₁, mul_comm s₁] }

variable (R S)

/-- The morphism `numeratorHom` is a monoid localization map in the case of commutative `R`. -/
protected def localizationMap : S.LocalizationMap R[S⁻¹] where
  toFun := numeratorHom
  map_one' := rfl
  map_mul' r₁ r₂ := by simp
  map_units' := numerator_isUnit
  surj' z := by
    induction' z using OreLocalization.ind with r s
    use (r, s); dsimp
    rw [numeratorHom_apply, numeratorHom_apply]; simp
  exists_of_eq r₁ r₂ := by
    dsimp
    intro h
    rw [numeratorHom_apply, numeratorHom_apply, oreDiv_eq_iff] at h
    rcases h with ⟨u, v, h₁, h₂⟩
    dsimp at h₂
    rw [one_mul, one_mul] at h₂
    subst h₂
    use u
    simpa only [mul_comm] using h₁.symm
#align ore_localization.localization_map OreLocalization.localizationMap

/-- If `R` is commutative, Ore localization and monoid localization are isomorphic. -/
protected noncomputable def equivMonoidLocalization : Localization S ≃* R[S⁻¹] :=
  Localization.mulEquivOfQuotient (OreLocalization.localizationMap R S)
#align ore_localization.equiv_monoid_localization OreLocalization.equivMonoidLocalization

end CommMonoid

section Semiring

variable {R : Type*} [Semiring R] {S : Submonoid R} [OreSet S]

private def add'' (r₁ : R) (s₁ : S) (r₂ : R) (s₂ : S) : R[S⁻¹] :=
  (r₁ * oreDenom (s₁ : R) s₂ + r₂ * oreNum (s₁ : R) s₂) /ₒ (s₁ * oreDenom (s₁ : R) s₂)

private theorem add''_char (r₁ : R) (s₁ : S) (r₂ : R) (s₂ : S) (rb : R) (sb : S)
    (hb : (s₁ : R) * sb = (s₂ : R) * rb) :
    add'' r₁ s₁ r₂ s₂ = (r₁ * sb + r₂ * rb) /ₒ (s₁ * sb) := by
  -- Porting note: `noncomm_ring` was not ported yet
  simp only [add'']
  have ha := ore_eq (s₁ : R) s₂
  set! ra := oreNum (s₁ : R) s₂ with h
  rw [← h] at *
  clear h
  -- r tilde
  set! sa := oreDenom (s₁ : R) s₂ with h
  rw [← h] at *
  clear h
  -- s tilde
  rcases oreCondition (sa : R) sb with ⟨rc, sc, hc⟩
  -- s*, r*
  have : (s₂ : R) * (rb * rc) = s₂ * (ra * sc) := by
    rw [← mul_assoc, ← hb, mul_assoc, ← hc, ← mul_assoc, ← mul_assoc, ha]
  rcases ore_left_cancel _ _ s₂ this with ⟨sd, hd⟩
  -- s#
  symm
  rw [oreDiv_eq_iff]
  use sc * sd
  use rc * sd
  constructor <;> simp only [Submonoid.coe_mul]
  · noncomm_ring
    rw [← mul_assoc (a := rb), hd, ← mul_assoc (a := (sa : R)), hc]
    noncomm_ring
  · rw [mul_assoc (a := (s₁ : R)), ← mul_assoc (a := (sa : R)), hc]
    noncomm_ring

attribute [local instance] OreLocalization.oreEqv

private def add' (r₂ : R) (s₂ : S) : R[S⁻¹] → R[S⁻¹] :=
  (--plus tilde
      Quotient.lift
      fun r₁s₁ : R × S => add'' r₁s₁.1 r₁s₁.2 r₂ s₂) <| by
    -- Porting note: `assoc_rw` & `noncomm_ring` were not ported yet
    rintro ⟨r₁', s₁'⟩ ⟨r₁, s₁⟩ ⟨sb, rb, hb, hb'⟩
    -- s*, r*
    rcases oreCondition (s₁' : R) s₂ with ⟨rc, sc, hc⟩
    --s~~, r~~
    rcases oreCondition rb sc with ⟨rd, sd, hd⟩
    -- s#, r#
    dsimp at *
    rw [add''_char _ _ _ _ rc sc hc]
    have : ↑s₁ * ↑(sb * sd) = ↑s₂ * (rc * rd) := by
      simp only [Submonoid.coe_mul]
      rw [← mul_assoc, hb', mul_assoc, hd, ← mul_assoc, hc, mul_assoc]
    rw [add''_char _ _ _ _ (rc * rd : R) (sb * sd : S) this]
    simp only [Submonoid.coe_mul]
    rw [← mul_assoc (a := r₁) (b := (sb : R)), hb, mul_assoc (a := r₁') (b := (rb : R)), hd,
      ← mul_assoc, ← mul_assoc, ← add_mul, oreDiv_eq_iff]
    use 1
    use rd
    constructor
    · simp
    · simp only [mul_one, Submonoid.coe_one, Submonoid.coe_mul] at this ⊢
      rw [hc, this, mul_assoc]

private theorem add'_comm (r₁ r₂ : R) (s₁ s₂ : S) :
    add' r₁ s₁ (r₂ /ₒ s₂) = add' r₂ s₂ (r₁ /ₒ s₁) := by
  -- Porting note: `assoc_rw` & `noncomm_ring` were not ported yet
  -- Porting note: `Quotient.mk'` required
  simp only [add', oreDiv, add'', Quotient.mk', Quotient.lift_mk]
  -- Porting note: `Quotient.eq` should be used in `rw` instead of `simp`
  rw [Quotient.eq]
  have hb := ore_eq (↑s₂) s₁
  -- Porting note: `set ... with h; rw [← h]; clear h`s aren't required anymore
  set rb := oreNum (↑s₂) s₁
  set sb := oreDenom (↑s₂) s₁
  have ha := ore_eq (↑s₁) s₂
  set ra := oreNum (↑s₁) s₂
  set sa := oreDenom (↑s₁) s₂
  rcases oreCondition ra sb with ⟨rc, sc, hc⟩
  -- r#, s#
  have : (s₁ : R) * (rb * rc) = s₁ * (sa * sc) := by
    rw [← mul_assoc, ← hb, mul_assoc, ← hc, ← mul_assoc, ← ha, mul_assoc]
  rcases ore_left_cancel _ _ s₁ this with ⟨sd, hd⟩
  -- s+
  use sc * sd
  use rc * sd
  dsimp
  constructor
  · rw [add_mul, add_mul, add_comm, mul_assoc (a := r₁) (b := (sa : R)),
      ← mul_assoc (a := (sa : R)), ← hd, mul_assoc (a := r₂) (b := ra),
      ← mul_assoc (a := ra) (b := (sc : R)), hc]
    simp only [mul_assoc]
  · rw [mul_assoc, ← mul_assoc (sa : R), ← hd, hb]
    simp only [mul_assoc]

/-- The addition on the Ore localization. -/
private def add : R[S⁻¹] → R[S⁻¹] → R[S⁻¹] := fun x =>
  Quotient.lift (fun rs : R × S => add' rs.1 rs.2 x)
    (by
      rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ hyz
      induction' x using OreLocalization.ind with r₃ s₃
      dsimp; rw [add'_comm, add'_comm r₂]
      -- Porting note: `Quotient.mk'` required
      simp [(· /ₒ ·), Quotient.mk', Quotient.sound hyz])

instance instAddOreLocalization : Add R[S⁻¹] :=
  ⟨add⟩

theorem oreDiv_add_oreDiv {r r' : R} {s s' : S} :
    r /ₒ s + r' /ₒ s' =
      (r * oreDenom (s : R) s' + r' * oreNum (s : R) s') /ₒ (s * oreDenom (s : R) s') :=
  rfl
#align ore_localization.ore_div_add_ore_div OreLocalization.oreDiv_add_oreDiv

/-- A characterization of the addition on the Ore localizaion, allowing for arbitrary Ore
numerator and Ore denominator. -/
theorem oreDiv_add_char {r r' : R} (s s' : S) (rb : R) (sb : S) (h : (s : R) * sb = s' * rb) :
    r /ₒ s + r' /ₒ s' = (r * sb + r' * rb) /ₒ (s * sb) :=
  add''_char r s r' s' rb sb h
#align ore_localization.ore_div_add_char OreLocalization.oreDiv_add_char

/-- Another characterization of the addition on the Ore localization, bundling up all witnesses
and conditions into a sigma type. -/
def oreDivAddChar' (r r' : R) (s s' : S) :
    Σ'r'' : R,
      Σ's'' : S, (s : R) * s'' = s' * r'' ∧ r /ₒ s + r' /ₒ s' = (r * s'' + r' * r'') /ₒ (s * s'') :=
  ⟨oreNum (s : R) s', oreDenom (s : R) s', ore_eq (s : R) s', oreDiv_add_oreDiv⟩
#align ore_localization.ore_div_add_char' OreLocalization.oreDivAddChar'

@[simp]
theorem add_oreDiv {r r' : R} {s : S} : r /ₒ s + r' /ₒ s = (r + r') /ₒ s := by
  simp [oreDiv_add_char s s 1 1 (by simp)]
#align ore_localization.add_ore_div OreLocalization.add_oreDiv

protected theorem add_assoc (x y z : R[S⁻¹]) : x + y + z = x + (y + z) := by
  -- Porting note: `assoc_rw` was not ported yet
  induction' x using OreLocalization.ind with r₁ s₁
  induction' y using OreLocalization.ind with r₂ s₂
  induction' z using OreLocalization.ind with r₃ s₃
  rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
  rcases oreDivAddChar' r₂ r₃ s₂ s₃ with ⟨rb, sb, hb, hb'⟩; rw [hb']; clear hb'
  rcases oreDivAddChar' (r₁ * sa + r₂ * ra) r₃ (s₁ * sa) s₃ with ⟨rc, sc, hc, q⟩; rw [q]; clear q
  rcases oreDivAddChar' r₁ (r₂ * sb + r₃ * rb) s₁ (s₂ * sb) with ⟨rd, sd, hd, q⟩; rw [q]; clear q
  simp only [right_distrib, mul_assoc, add_assoc]
  -- Porting note: `simp` required because `repeat' rw` behaves differently
  simp only [← add_oreDiv]
  congr 1
  · rw [← OreLocalization.expand', ← mul_assoc, ← mul_assoc, ← OreLocalization.expand', ←
      OreLocalization.expand']
  congr 1
  · simp_rw [← Submonoid.coe_mul] at ha hd
    rw [Subtype.coe_eq_of_eq_mk hd, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← OreLocalization.expand,
      ← OreLocalization.expand', Subtype.coe_eq_of_eq_mk ha, ← OreLocalization.expand]
    apply OreLocalization.expand'
  · rcases oreCondition (sd : R) (sa * sc) with ⟨re, _, _⟩
    simp_rw [← Submonoid.coe_mul] at hb hc hd
    rw [← mul_assoc, Subtype.coe_eq_of_eq_mk hc]
    rw [← OreLocalization.expand, Subtype.coe_eq_of_eq_mk hd, ← mul_assoc, ←
      OreLocalization.expand, Subtype.coe_eq_of_eq_mk hb]
    apply OreLocalization.expand
#align ore_localization.add_assoc OreLocalization.add_assoc

private def zero : R[S⁻¹] :=
  0 /ₒ 1

instance : Zero R[S⁻¹] :=
  ⟨zero⟩

protected theorem zero_def : (0 : R[S⁻¹]) = 0 /ₒ 1 :=
  rfl
#align ore_localization.zero_def OreLocalization.zero_def

@[simp]
theorem zero_div_eq_zero (s : S) : 0 /ₒ s = 0 := by
  rw [OreLocalization.zero_def, oreDiv_eq_iff]
  exact ⟨s, 1, by simp⟩
#align ore_localization.zero_div_eq_zero OreLocalization.zero_div_eq_zero

protected theorem zero_add (x : R[S⁻¹]) : 0 + x = x := by
  induction x using OreLocalization.ind
  rw [← zero_div_eq_zero, add_oreDiv]; simp
#align ore_localization.zero_add OreLocalization.zero_add

protected theorem add_comm (x y : R[S⁻¹]) : x + y = y + x := by
  induction x using OreLocalization.ind
  induction y using OreLocalization.ind
  change add' _ _ (_ /ₒ _) = _; apply add'_comm
#align ore_localization.add_comm OreLocalization.add_comm

instance instAddCommMonoidOreLocalization : AddCommMonoid R[S⁻¹] :=
  { OreLocalization.instAddOreLocalization with
    add_comm := OreLocalization.add_comm
    add_assoc := OreLocalization.add_assoc
    zero := zero
    zero_add := OreLocalization.zero_add
    add_zero := fun x => by rw [OreLocalization.add_comm, OreLocalization.zero_add]
    nsmul := nsmulRec }

protected theorem zero_mul (x : R[S⁻¹]) : 0 * x = 0 := by
  induction' x using OreLocalization.ind with r s
  rw [OreLocalization.zero_def, oreDiv_mul_char 0 r 1 s r 1 (by simp)]; simp
#align ore_localization.zero_mul OreLocalization.zero_mul

protected theorem mul_zero (x : R[S⁻¹]) : x * 0 = 0 := by
  induction' x using OreLocalization.ind with r s
  rw [OreLocalization.zero_def, oreDiv_mul_char r 0 s 1 0 1 (by simp)]; simp
#align ore_localization.mul_zero OreLocalization.mul_zero

protected theorem left_distrib (x y z : R[S⁻¹]) : x * (y + z) = x * y + x * z := by
  induction' x using OreLocalization.ind with r₁ s₁
  induction' y using OreLocalization.ind with r₂ s₂
  induction' z using OreLocalization.ind with r₃ s₃
  rcases oreDivAddChar' r₂ r₃ s₂ s₃ with ⟨ra, sa, ha, q⟩
  rw [q]
  clear q
  rw [OreLocalization.expand' r₂ s₂ sa]
  rcases oreDivMulChar' r₁ (r₂ * sa) s₁ (s₂ * sa) with ⟨rb, sb, hb, q⟩
  rw [q]
  clear q
  have hs₃rasb : ↑s₃ * (ra * sb) ∈ S := by
    rw [← mul_assoc, ← ha]
    norm_cast
    apply SetLike.coe_mem
  rw [OreLocalization.expand _ _ _ hs₃rasb]
  have ha' : ↑(s₂ * sa * sb) = ↑s₃ * (ra * sb) := by simp [ha, ← mul_assoc]
  rw [← Subtype.coe_eq_of_eq_mk ha']
  rcases oreDivMulChar' r₁ (r₃ * (ra * sb)) s₁ (s₂ * sa * sb) with ⟨rc, sc, hc, hc'⟩
  rw [hc']
  rw [oreDiv_add_char (s₂ * sa * sb) (s₂ * sa * sb * sc) 1 sc (by simp)]
  rw [OreLocalization.expand' (r₂ * ↑sa + r₃ * ra) (s₂ * sa) (sb * sc)]
  conv_lhs =>
    congr
    · skip
    congr
    rw [add_mul, S.coe_mul, ← mul_assoc, hb, ← mul_assoc, mul_assoc r₃, hc, mul_assoc, ← mul_add]
  rw [OreLocalization.mul_cancel']
  simp only [mul_one, Submonoid.coe_mul, mul_add, ← mul_assoc]
#align ore_localization.left_distrib OreLocalization.left_distrib

theorem right_distrib (x y z : R[S⁻¹]) : (x + y) * z = x * z + y * z := by
  induction' x using OreLocalization.ind with r₁ s₁
  induction' y using OreLocalization.ind with r₂ s₂
  induction' z using OreLocalization.ind with r₃ s₃
  rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'; norm_cast at ha
  rw [OreLocalization.expand' r₁ s₁ sa]
  rw [OreLocalization.expand r₂ s₂ ra (by rw [← ha]; apply SetLike.coe_mem)]
  rw [← Subtype.coe_eq_of_eq_mk ha]
  repeat rw [oreDiv_mul_oreDiv]
  simp only [add_mul, add_oreDiv]
#align ore_localization.right_distrib OreLocalization.right_distrib

instance instSemiringOreLocalization : Semiring R[S⁻¹] :=
  { OreLocalization.instAddCommMonoidOreLocalization,
    OreLocalization.instMonoidOreLocalization with
    zero_mul := OreLocalization.zero_mul
    mul_zero := OreLocalization.mul_zero
    left_distrib := OreLocalization.left_distrib
    right_distrib := right_distrib }

section UMP

variable {T : Type*} [Semiring T]
variable (f : R →+* T) (fS : S →* Units T)
variable (hf : ∀ s : S, f s = fS s)

/-- The universal lift from a ring homomorphism `f : R →+* T`, which maps elements in `S` to
units of `T`, to a ring homomorphism `R[S⁻¹] →+* T`. This extends the construction on
monoids. -/
def universalHom : R[S⁻¹] →+* T :=
  {
    universalMulHom f.toMonoidHom fS
      hf with
    map_zero' := by
      -- Porting note: `change` required because of new `Coe`
      change (universalMulHom f.toMonoidHom fS hf : R[S⁻¹] → T) 0 = 0
      rw [OreLocalization.zero_def, universalMulHom_apply]
      simp
    map_add' := fun x y => by
      -- Porting note: `change` required because of new `Coe`
      change (universalMulHom f.toMonoidHom fS hf : R[S⁻¹] → T) (x + y)
        = (universalMulHom f.toMonoidHom fS hf : R[S⁻¹] → T) x
        + (universalMulHom f.toMonoidHom fS hf : R[S⁻¹] → T) y
      induction' x using OreLocalization.ind with r₁ s₁
      induction' y using OreLocalization.ind with r₂ s₂
      rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨r₃, s₃, h₃, h₃'⟩
      rw [h₃']
      clear h₃'
      simp only [universalMulHom_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      simp only [mul_inv_rev, MonoidHom.map_mul, RingHom.map_add, RingHom.map_mul, Units.val_mul]
      rw [add_mul, ← mul_assoc, mul_assoc (f r₁), hf, ← Units.val_mul]
      simp only [mul_one, mul_right_inv, Units.val_one]
      congr 1
      rw [mul_assoc]
      congr 1
      norm_cast at h₃
      have h₃' := Subtype.coe_eq_of_eq_mk h₃
      rw [← Units.val_mul, ← mul_inv_rev, ← fS.map_mul, h₃']
      have hs₂r₃ : ↑s₂ * r₃ ∈ S := by
        rw [← h₃]
        exact SetLike.coe_mem (s₁ * s₃)
      apply (Units.inv_mul_cancel_left (fS s₂) _).symm.trans
      conv_lhs =>
        congr
        · skip
        rw [← Units.mul_inv_cancel_left (fS ⟨s₂ * r₃, hs₂r₃⟩) (fS s₂), mul_assoc, mul_assoc]
        congr
        · skip
        rw [← hf, ← mul_assoc (f s₂), ← f.map_mul]
        conv =>
          congr
          · skip
          congr
          rw [← h₃]
        rw [hf, ← mul_assoc, ← h₃', Units.inv_mul]
      rw [one_mul, ← h₃', Units.mul_inv, mul_one] }
#align ore_localization.universal_hom OreLocalization.universalHom

theorem universalHom_apply {r : R} {s : S} :
    universalHom f fS hf (r /ₒ s) = f r * ((fS s)⁻¹ : Units T) :=
  rfl
#align ore_localization.universal_hom_apply OreLocalization.universalHom_apply

theorem universalHom_commutes {r : R} : universalHom f fS hf (numeratorHom r) = f r := by
  simp [numeratorHom_apply, universalHom_apply]
#align ore_localization.universal_hom_commutes OreLocalization.universalHom_commutes

theorem universalHom_unique (φ : R[S⁻¹] →+* T) (huniv : ∀ r : R, φ (numeratorHom r) = f r) :
    φ = universalHom f fS hf :=
  RingHom.coe_monoidHom_injective <| universalMulHom_unique (RingHom.toMonoidHom f) fS hf (↑φ) huniv
#align ore_localization.universal_hom_unique OreLocalization.universalHom_unique

end UMP

end Semiring

section Ring

variable {R : Type*} [Ring R] {S : Submonoid R} [OreSet S]

/-- Negation on the Ore localization is defined via negation on the numerator. -/
protected def neg : R[S⁻¹] → R[S⁻¹] :=
  liftExpand (fun (r : R) (s : S) => -r /ₒ s) fun r t s ht => by
    -- Porting note(#12129): additional beta reduction needed
    beta_reduce
    rw [neg_mul_eq_neg_mul, ← OreLocalization.expand]
#align ore_localization.neg OreLocalization.neg

instance instNegOreLocalization : Neg R[S⁻¹] :=
  ⟨OreLocalization.neg⟩

@[simp]
protected theorem neg_def (r : R) (s : S) : -(r /ₒ s) = -r /ₒ s :=
  rfl
#align ore_localization.neg_def OreLocalization.neg_def

protected theorem add_left_neg (x : R[S⁻¹]) : -x + x = 0 := by
  induction' x using OreLocalization.ind with r s; simp
#align ore_localization.add_left_neg OreLocalization.add_left_neg

instance ring : Ring R[S⁻¹] :=
  { OreLocalization.instSemiringOreLocalization,
    OreLocalization.instNegOreLocalization with
    add_left_neg := OreLocalization.add_left_neg
    zsmul := zsmulRec }

open nonZeroDivisors

theorem numeratorHom_inj (hS : S ≤ R⁰) : Function.Injective (numeratorHom : R → R[S⁻¹]) :=
  fun r₁ r₂ h => by
  rw [numeratorHom_apply, numeratorHom_apply, oreDiv_eq_iff] at h
  rcases h with ⟨u, v, h₁, h₂⟩
  simp only [S.coe_one, one_mul] at h₂
  rwa [← h₂, mul_cancel_right_mem_nonZeroDivisors (hS (SetLike.coe_mem u)), eq_comm] at h₁
#align ore_localization.numerator_hom_inj OreLocalization.numeratorHom_inj

theorem nontrivial_of_nonZeroDivisors [Nontrivial R] (hS : S ≤ R⁰) : Nontrivial R[S⁻¹] :=
  ⟨⟨0, 1, fun h => by
      rw [OreLocalization.one_def, OreLocalization.zero_def] at h
      apply nonZeroDivisors.coe_ne_zero 1 (numeratorHom_inj hS h).symm⟩⟩
#align ore_localization.nontrivial_of_non_zero_divisors OreLocalization.nontrivial_of_nonZeroDivisors

end Ring

noncomputable section DivisionRing

open nonZeroDivisors

open scoped Classical

variable {R : Type*} [Ring R] [Nontrivial R] [OreSet R⁰]

instance nontrivial : Nontrivial R[R⁰⁻¹] :=
  nontrivial_of_nonZeroDivisors (refl R⁰)

variable [NoZeroDivisors R]

/-- The inversion of Ore fractions for a ring without zero divisors, satisying `0⁻¹ = 0` and
`(r /ₒ r')⁻¹ = r' /ₒ r` for `r ≠ 0`. -/
protected def inv : R[R⁰⁻¹] → R[R⁰⁻¹] :=
  liftExpand
    (fun r s =>
      if hr : r = (0 : R) then (0 : R[R⁰⁻¹])
      else s /ₒ ⟨r, fun _ => eq_zero_of_ne_zero_of_mul_right_eq_zero hr⟩)
    (by
      intro r t s hst
      by_cases hr : r = 0
      · simp [hr]
      · by_cases ht : t = 0
        · exfalso
          apply nonZeroDivisors.coe_ne_zero ⟨_, hst⟩
          simp [ht, mul_zero]
        · simp only [hr, ht, dif_neg, not_false_iff, or_self_iff, mul_eq_zero]
          apply OreLocalization.expand)
#align ore_localization.inv OreLocalization.inv

instance inv' : Inv R[R⁰⁻¹] :=
  ⟨OreLocalization.inv⟩

protected theorem inv_def {r : R} {s : R⁰} :
    (r /ₒ s)⁻¹ =
      if hr : r = (0 : R) then (0 : R[R⁰⁻¹])
      else s /ₒ ⟨r, fun _ => eq_zero_of_ne_zero_of_mul_right_eq_zero hr⟩ :=
  rfl
#align ore_localization.inv_def OreLocalization.inv_def

protected theorem mul_inv_cancel (x : R[R⁰⁻¹]) (h : x ≠ 0) : x * x⁻¹ = 1 := by
  induction' x using OreLocalization.ind with r s
  rw [OreLocalization.inv_def, OreLocalization.one_def]
  by_cases hr : r = 0
  · exfalso
    apply h
    simp [hr]
  · simp [hr]
    apply OreLocalization.div_eq_one'
#align ore_localization.mul_inv_cancel OreLocalization.mul_inv_cancel

protected theorem inv_zero : (0 : R[R⁰⁻¹])⁻¹ = 0 := by
  rw [OreLocalization.zero_def, OreLocalization.inv_def]
  simp
#align ore_localization.inv_zero OreLocalization.inv_zero

instance divisionRing : DivisionRing R[R⁰⁻¹] where
  __ := ring
  __ := nontrivial
  __ := inv'
  mul_inv_cancel := OreLocalization.mul_inv_cancel
  inv_zero := OreLocalization.inv_zero
  nnqsmul := _
  qsmul := _

end DivisionRing

end OreLocalization
