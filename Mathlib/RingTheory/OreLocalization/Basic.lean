/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge
-/
import Mathlib.GroupTheory.MonoidLocalization
import Mathlib.RingTheory.NonZeroDivisors
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
    -- ⊢ ∀ {x y : R × { x // x ∈ S }}, (∃ u v, y.fst * ↑u = x.fst * v ∧ ↑y.snd * ↑u = …
    · rintro ⟨r, s⟩ ⟨r', s'⟩ ⟨u, v, hru, hsu⟩; dsimp only at *
      -- ⊢ ∃ u v, (r, s).fst * ↑u = (r', s').fst * v ∧ ↑(r, s).snd * ↑u = ↑(r', s').snd …
                                               -- ⊢ ∃ u v, r * ↑u = r' * v ∧ ↑s * ↑u = ↑s' * v
      rcases oreCondition (s : R) s' with ⟨r₂, s₂, h₁⟩
      -- ⊢ ∃ u v, r * ↑u = r' * v ∧ ↑s * ↑u = ↑s' * v
      rcases oreCondition r₂ u with ⟨r₃, s₃, h₂⟩
      -- ⊢ ∃ u v, r * ↑u = r' * v ∧ ↑s * ↑u = ↑s' * v
      have : (s : R) * ((v : R) * r₃) = (s : R) * (s₂ * s₃) := by
        -- porting note: the proof used `assoc_rw`
        rw [← mul_assoc _ (s₂ : R), h₁, mul_assoc, h₂, ← mul_assoc, ← hsu, mul_assoc]
      rcases ore_left_cancel (v * r₃) (s₂ * s₃) s this with ⟨w, hw⟩
      -- ⊢ ∃ u v, r * ↑u = r' * v ∧ ↑s * ↑u = ↑s' * v
      refine ⟨s₂ * s₃ * w, u * r₃ * w, ?_, ?_⟩ <;> simp only [Submonoid.coe_mul, ← hw]
      -- ⊢ r * ↑(s₂ * s₃ * w) = r' * (↑u * r₃ * ↑w)
                                                   -- ⊢ r * (v * r₃ * ↑w) = r' * (↑u * r₃ * ↑w)
                                                   -- ⊢ ↑s * (v * r₃ * ↑w) = ↑s' * (↑u * r₃ * ↑w)
      · simp only [← mul_assoc, hru]
        -- 🎉 no goals
      · simp only [← mul_assoc, hsu]
        -- 🎉 no goals
    · rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨r₃, s₃⟩ ⟨u, v, hur₁, hs₁u⟩ ⟨u', v', hur₂, hs₂u⟩
      -- ⊢ ∃ u v, (r₃, s₃).fst * ↑u = (r₁, s₁).fst * v ∧ ↑(r₃, s₃).snd * ↑u = ↑(r₁, s₁) …
      rcases oreCondition v' u with ⟨r', s', h⟩; dsimp only at *
      -- ⊢ ∃ u v, (r₃, s₃).fst * ↑u = (r₁, s₁).fst * v ∧ ↑(r₃, s₃).snd * ↑u = ↑(r₁, s₁) …
                                                 -- ⊢ ∃ u v, r₃ * ↑u = r₁ * v ∧ ↑s₃ * ↑u = ↑s₁ * v
      refine ⟨u' * s', v * r', ?_, ?_⟩ <;> simp only [Submonoid.coe_mul, ← mul_assoc]
      -- ⊢ r₃ * ↑(u' * s') = r₁ * (v * r')
                                           -- ⊢ r₃ * ↑u' * ↑s' = r₁ * v * r'
                                           -- ⊢ ↑s₃ * ↑u' * ↑s' = ↑s₁ * v * r'
      · rw [hur₂, mul_assoc, h, ← mul_assoc, hur₁]
        -- 🎉 no goals
      · rw [hs₂u, mul_assoc, h, ← mul_assoc, hs₁u]
        -- 🎉 no goals
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

-- mathport name: «expr /ₒ »
@[inherit_doc]
infixl:70 " /ₒ " => oreDiv

@[elab_as_elim]
protected theorem ind {β : R[S⁻¹] → Prop} (c : ∀ (r : R) (s : S), β (r /ₒ s)) : ∀ q, β q := by
  apply Quotient.ind
  -- ⊢ ∀ (a : R × { x // x ∈ S }), β (Quotient.mk (oreEqv R S) a)
  rintro ⟨r, s⟩
  -- ⊢ β (Quotient.mk (oreEqv R S) (r, s))
  exact c r s
  -- 🎉 no goals
#align ore_localization.ind OreLocalization.ind

theorem oreDiv_eq_iff {r₁ r₂ : R} {s₁ s₂ : S} :
    r₁ /ₒ s₁ = r₂ /ₒ s₂ ↔ ∃ (u : S) (v : R), r₂ * u = r₁ * v ∧ (s₂ : R) * u = s₁ * v :=
  Quotient.eq''
#align ore_localization.ore_div_eq_iff OreLocalization.oreDiv_eq_iff

/-- A fraction `r /ₒ s` is equal to its expansion by an arbitrary factor `t` if `s * t ∈ S`. -/
protected theorem expand (r : R) (s : S) (t : R) (hst : (s : R) * t ∈ S) :
    r /ₒ s = r * t /ₒ ⟨s * t, hst⟩ := by
  apply Quotient.sound
  -- ⊢ (r, s) ≈ (r * t, { val := ↑s * t, property := hst })
  refine' ⟨s, t * s, _, _⟩ <;> dsimp <;> rw [mul_assoc]
  -- ⊢ (r * t, { val := ↑s * t, property := hst }).fst * ↑s = (r, s).fst * (t * ↑s)
                               -- ⊢ r * t * ↑s = r * (t * ↑s)
                               -- ⊢ ↑s * t * ↑s = ↑s * (t * ↑s)
                                         -- 🎉 no goals
                                         -- 🎉 no goals
#align ore_localization.expand OreLocalization.expand

/-- A fraction is equal to its expansion by a factor from s. -/
protected theorem expand' (r : R) (s s' : S) : r /ₒ s = r * s' /ₒ (s * s') :=
  OreLocalization.expand r s s' (by norm_cast; apply SetLike.coe_mem)
                                    -- ⊢ ↑(s * s') ∈ S
                                               -- 🎉 no goals
#align ore_localization.expand' OreLocalization.expand'

/-- Fractions which differ by a factor of the numerator can be proven equal if
those factors expand to equal elements of `R`. -/
protected theorem eq_of_num_factor_eq {r r' r₁ r₂ : R} {s t : S} (h : r * t = r' * t) :
    r₁ * r * r₂ /ₒ s = r₁ * r' * r₂ /ₒ s := by
  rcases oreCondition r₂ t with ⟨r₂', t', hr₂⟩
  -- ⊢ r₁ * r * r₂ /ₒ s = r₁ * r' * r₂ /ₒ s
  -- porting note: todo: use `assoc_rw`?
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
    -- ⊢ P r₁ s₁ = P r₂ s₂
    have s₁vS : (s₁ : R) * v ∈ S := by
      rw [← hs₂, ← S.coe_mul]
      exact SetLike.coe_mem (s₂ * u)
    replace hs₂ : s₂ * u = ⟨(s₁ : R) * v, s₁vS⟩
    -- ⊢ s₂ * u = { val := ↑s₁ * v, property := s₁vS }
    · ext; simp [hs₂]
      -- ⊢ ↑(s₂ * u) = ↑{ val := ↑s₁ * v, property := s₁vS }
           -- 🎉 no goals
    rw [hP r₁ v s₁ s₁vS, hP r₂ u s₂ (by norm_cast; rwa [hs₂]), hr₂]
    -- ⊢ P (r₁ * v) { val := ↑s₁ * v, property := s₁vS } = P (r₁ * v) { val := ↑s₂ *  …
    simp only [← hs₂]; rfl
    -- ⊢ P (r₁ * v) (s₂ * u) = P (r₁ * v) { val := ↑s₂ * ↑u, property := (_ : ↑s₂ * ↑ …
                       -- 🎉 no goals
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
      -- ⊢ P r₁ s₁ r₂ s₂ = P r₁ s₁ (r₂ * t₂) { val := ↑s₂ * t₂, property := ht₂ }
      simp [this])
      -- 🎉 no goals
    fun r₁ t₁ s₁ ht₁ => by
    ext x; induction' x using OreLocalization.ind with r₂ s₂
    -- ⊢ (fun r₁ s₁ => liftExpand (P r₁ s₁) (_ : ∀ (r₂ t₂ : R) (s₂ : { x // x ∈ S })  …
           -- ⊢ (fun r₁ s₁ => liftExpand (P r₁ s₁) (_ : ∀ (r₂ t₂ : R) (s₂ : { x // x ∈ S })  …
    dsimp only
    -- ⊢ liftExpand (P r₁ s₁) (_ : ∀ (r₂ t₂ : R) (s₂ : { x // x ∈ S }) (ht₂ : ↑s₂ * t …
    rw [liftExpand_of, liftExpand_of, hP r₁ t₁ s₁ ht₁ r₂ 1 s₂ (by simp)]; simp
    -- ⊢ P (r₁ * t₁) { val := ↑s₁ * t₁, property := ht₁ } (r₂ * 1) { val := ↑s₂ * 1,  …
                                                                          -- 🎉 no goals
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
  -- ⊢ r₁ * oreNum r₂ s₁ /ₒ (s₂ * oreDenom r₂ s₁) = r₁ * v /ₒ (s₂ * u)
  have h₀ := ore_eq r₂ s₁; set v₀ := oreNum r₂ s₁; set u₀ := oreDenom r₂ s₁
  -- ⊢ r₁ * oreNum r₂ s₁ /ₒ (s₂ * oreDenom r₂ s₁) = r₁ * v /ₒ (s₂ * u)
                           -- ⊢ r₁ * v₀ /ₒ (s₂ * oreDenom r₂ s₁) = r₁ * v /ₒ (s₂ * u)
                                                   -- ⊢ r₁ * v₀ /ₒ (s₂ * u₀) = r₁ * v /ₒ (s₂ * u)
  rcases oreCondition (u₀ : R) u with ⟨r₃, s₃, h₃⟩
  -- ⊢ r₁ * v₀ /ₒ (s₂ * u₀) = r₁ * v /ₒ (s₂ * u)
  have :=
    calc
      (s₁ : R) * (v * r₃) = r₂ * u * r₃ := by rw [← mul_assoc, ← huv]
      _ = r₂ * u₀ * s₃ := by rw [mul_assoc, mul_assoc, h₃]
      _ = s₁ * (v₀ * s₃) := by rw [← mul_assoc, h₀]
  rcases ore_left_cancel _ _ _ this with ⟨s₄, hs₄⟩
  -- ⊢ r₁ * v₀ /ₒ (s₂ * u₀) = r₁ * v /ₒ (s₂ * u)
  symm; rw [oreDiv_eq_iff]
  -- ⊢ r₁ * v /ₒ (s₂ * u) = r₁ * v₀ /ₒ (s₂ * u₀)
        -- ⊢ ∃ u_1 v_1, r₁ * v₀ * ↑u_1 = r₁ * v * v_1 ∧ ↑(s₂ * u₀) * ↑u_1 = ↑(s₂ * u) * v_1
  use s₃ * s₄; use r₃ * s₄; simp only [Submonoid.coe_mul]; constructor
  -- ⊢ ∃ v_1, r₁ * v₀ * ↑(s₃ * s₄) = r₁ * v * v_1 ∧ ↑(s₂ * u₀) * ↑(s₃ * s₄) = ↑(s₂  …
               -- ⊢ r₁ * v₀ * ↑(s₃ * s₄) = r₁ * v * (r₃ * ↑s₄) ∧ ↑(s₂ * u₀) * ↑(s₃ * s₄) = ↑(s₂  …
                            -- ⊢ r₁ * oreNum r₂ s₁ * (↑s₃ * ↑s₄) = r₁ * v * (r₃ * ↑s₄) ∧ ↑s₂ * ↑(oreDenom r₂  …
                                                           -- ⊢ r₁ * oreNum r₂ s₁ * (↑s₃ * ↑s₄) = r₁ * v * (r₃ * ↑s₄)
  · rw [mul_assoc (b := v₀), ← mul_assoc (a := v₀), ← hs₄]
    -- ⊢ r₁ * (v * r₃ * ↑s₄) = r₁ * v * (r₃ * ↑s₄)
    simp only [mul_assoc]
    -- 🎉 no goals
  · rw [mul_assoc (b := (u₀ : R)), ← mul_assoc (a := (u₀ : R)), h₃]
    -- ⊢ ↑s₂ * (↑u * r₃ * ↑s₄) = ↑s₂ * ↑u * (r₃ * ↑s₄)
    simp only [mul_assoc]
    -- 🎉 no goals

/-- The multiplication on the Ore localization of monoids. -/
protected def mul : R[S⁻¹] → R[S⁻¹] → R[S⁻¹] :=
  lift₂Expand mul' fun r₂ p s₂ hp r₁ r s₁ hr => by
    have h₁ := ore_eq r₁ s₂
    -- ⊢ OreLocalization.mul' r₂ s₂ r₁ s₁ = OreLocalization.mul' (r₂ * p) { val := ↑s …
    set r₁' := oreNum r₁ s₂
    -- ⊢ OreLocalization.mul' r₂ s₂ r₁ s₁ = OreLocalization.mul' (r₂ * p) { val := ↑s …
    set s₂' := oreDenom r₁ s₂
    -- ⊢ OreLocalization.mul' r₂ s₂ r₁ s₁ = OreLocalization.mul' (r₂ * p) { val := ↑s …
    rcases oreCondition (↑s₂ * r₁') ⟨s₂ * p, hp⟩ with ⟨p', s_star, h₂⟩
    -- ⊢ OreLocalization.mul' r₂ s₂ r₁ s₁ = OreLocalization.mul' (r₂ * p) { val := ↑s …
    dsimp at h₂
    -- ⊢ OreLocalization.mul' r₂ s₂ r₁ s₁ = OreLocalization.mul' (r₂ * p) { val := ↑s …
    rcases oreCondition r (s₂' * s_star) with ⟨p_flat, s_flat, h₃⟩
    -- ⊢ OreLocalization.mul' r₂ s₂ r₁ s₁ = OreLocalization.mul' (r₂ * p) { val := ↑s …
    simp only [S.coe_mul] at h₃
    -- ⊢ OreLocalization.mul' r₂ s₂ r₁ s₁ = OreLocalization.mul' (r₂ * p) { val := ↑s …
    have : r₁ * r * s_flat = s₂ * p * (p' * p_flat) := by
      rw [← mul_assoc, ← h₂, ← h₁, mul_assoc, h₃]
      simp only [mul_assoc]
    rw [mul'_char (r₂ * p) (r₁ * r) ⟨↑s₂ * p, hp⟩ ⟨↑s₁ * r, hr⟩ _ _ this]
    -- ⊢ OreLocalization.mul' r₂ s₂ r₁ s₁ = r₂ * p * (p' * p_flat) /ₒ ({ val := ↑s₁ * …
    clear this
    -- ⊢ OreLocalization.mul' r₂ s₂ r₁ s₁ = r₂ * p * (p' * p_flat) /ₒ ({ val := ↑s₁ * …
    have hsssp : ↑s₁ * ↑s₂' * ↑s_star * p_flat ∈ S := by
      rw [mul_assoc, mul_assoc, ← mul_assoc (s₂' : R), ← h₃, ← mul_assoc]
      exact S.mul_mem hr (SetLike.coe_mem s_flat)
    have : (⟨↑s₁ * r, hr⟩ : S) * s_flat = ⟨s₁ * s₂' * s_star * p_flat, hsssp⟩ := by
      ext
      simp only [Submonoid.coe_mul]
      rw [mul_assoc, h₃, ← mul_assoc, ← mul_assoc]
    rw [this]
    -- ⊢ OreLocalization.mul' r₂ s₂ r₁ s₁ = r₂ * p * (p' * p_flat) /ₒ { val := ↑s₁ *  …
    clear this
    -- ⊢ OreLocalization.mul' r₂ s₂ r₁ s₁ = r₂ * p * (p' * p_flat) /ₒ { val := ↑s₁ *  …
    rcases ore_left_cancel (p * p') (r₁' * (s_star : R)) s₂ (by simp [← mul_assoc, h₂])
      with ⟨s₂'', h₂''⟩
    rw [← mul_assoc, mul_assoc r₂, OreLocalization.eq_of_num_factor_eq h₂'']
    -- ⊢ OreLocalization.mul' r₂ s₂ r₁ s₁ = r₂ * (r₁' * ↑s_star) * p_flat /ₒ { val := …
    norm_cast at hsssp ⊢
    -- ⊢ OreLocalization.mul' r₂ s₂ r₁ s₁ = r₂ * (r₁' * ↑s_star) * p_flat /ₒ { val := …
    rw [← OreLocalization.expand _ _ _ hsssp, ← mul_assoc]
    -- ⊢ OreLocalization.mul' r₂ s₂ r₁ s₁ = r₂ * r₁' * ↑s_star /ₒ (s₁ * s₂' * s_star)
    apply OreLocalization.expand
    -- 🎉 no goals
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
  -- ⊢ ∃ u v, 1 * ↑u = r * v ∧ ↑1 * ↑u = ↑{ val := r, property := hr } * v
  exact ⟨⟨r, hr⟩, 1, by simp, by simp⟩
  -- 🎉 no goals
#align ore_localization.div_eq_one' OreLocalization.div_eq_one'

@[simp]
protected theorem div_eq_one {s : S} : (s : R) /ₒ s = 1 :=
  OreLocalization.div_eq_one' _
#align ore_localization.div_eq_one OreLocalization.div_eq_one

protected theorem one_mul (x : R[S⁻¹]) : 1 * x = x := by
  induction' x using OreLocalization.ind with r s
  -- ⊢ 1 * (r /ₒ s) = r /ₒ s
  simp [OreLocalization.one_def, oreDiv_mul_char (1 : R) r (1 : S) s r 1 (by simp)]
  -- 🎉 no goals
#align ore_localization.one_mul OreLocalization.one_mul

protected theorem mul_one (x : R[S⁻¹]) : x * 1 = x := by
  induction' x using OreLocalization.ind with r s
  -- ⊢ r /ₒ s * 1 = r /ₒ s
  simp [OreLocalization.one_def, oreDiv_mul_char r 1 s 1 1 s (by simp)]
  -- 🎉 no goals
#align ore_localization.mul_one OreLocalization.mul_one

protected theorem mul_assoc (x y z : R[S⁻¹]) : x * y * z = x * (y * z) := by
  -- Porting note: `assoc_rw` was not ported yet
  induction' x using OreLocalization.ind with r₁ s₁
  -- ⊢ r₁ /ₒ s₁ * y * z = r₁ /ₒ s₁ * (y * z)
  induction' y using OreLocalization.ind with r₂ s₂
  -- ⊢ r₁ /ₒ s₁ * (r₂ /ₒ s₂) * z = r₁ /ₒ s₁ * (r₂ /ₒ s₂ * z)
  induction' z using OreLocalization.ind with r₃ s₃
  -- ⊢ r₁ /ₒ s₁ * (r₂ /ₒ s₂) * (r₃ /ₒ s₃) = r₁ /ₒ s₁ * (r₂ /ₒ s₂ * (r₃ /ₒ s₃))
  rcases oreDivMulChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
  -- ⊢ r₁ /ₒ s₁ * (r₂ /ₒ s₂) * (r₃ /ₒ s₃) = r₁ /ₒ s₁ * (r₂ /ₒ s₂ * (r₃ /ₒ s₃))
                                                            -- ⊢ r₁ * ra /ₒ (s₂ * sa) * (r₃ /ₒ s₃) = r₁ /ₒ s₁ * (r₂ /ₒ s₂ * (r₃ /ₒ s₃))
                                                                      -- ⊢ r₁ * ra /ₒ (s₂ * sa) * (r₃ /ₒ s₃) = r₁ /ₒ s₁ * (r₂ /ₒ s₂ * (r₃ /ₒ s₃))
  rcases oreDivMulChar' r₂ r₃ s₂ s₃ with ⟨rb, sb, hb, hb'⟩; rw [hb']; clear hb'
  -- ⊢ r₁ * ra /ₒ (s₂ * sa) * (r₃ /ₒ s₃) = r₁ /ₒ s₁ * (r₂ /ₒ s₂ * (r₃ /ₒ s₃))
                                                            -- ⊢ r₁ * ra /ₒ (s₂ * sa) * (r₃ /ₒ s₃) = r₁ /ₒ s₁ * (r₂ * rb /ₒ (s₃ * sb))
                                                                      -- ⊢ r₁ * ra /ₒ (s₂ * sa) * (r₃ /ₒ s₃) = r₁ /ₒ s₁ * (r₂ * rb /ₒ (s₃ * sb))
  rcases oreCondition rb sa with ⟨rc, sc, hc⟩
  -- ⊢ r₁ * ra /ₒ (s₂ * sa) * (r₃ /ₒ s₃) = r₁ /ₒ s₁ * (r₂ * rb /ₒ (s₃ * sb))
  rw [oreDiv_mul_char (r₁ * ra) r₃ (s₂ * sa) s₃ rc (sb * sc)
      (by
        simp only [Submonoid.coe_mul]
        rw [← mul_assoc, hb, mul_assoc, hc, ← mul_assoc])]
  rw [mul_assoc, ← mul_assoc s₃]
  -- ⊢ r₁ * (ra * rc) /ₒ (s₃ * sb * sc) = r₁ /ₒ s₁ * (r₂ * rb /ₒ (s₃ * sb))
  symm; apply oreDiv_mul_char
  -- ⊢ r₁ /ₒ s₁ * (r₂ * rb /ₒ (s₃ * sb)) = r₁ * (ra * rc) /ₒ (s₃ * sb * sc)
        -- ⊢ r₂ * rb * ↑sc = ↑s₁ * (ra * rc)
  rw [mul_assoc, hc, ← mul_assoc (b := ra), ← ha, mul_assoc]
  -- 🎉 no goals
#align ore_localization.mul_assoc OreLocalization.mul_assoc

instance instMonoidOreLocalization : Monoid R[S⁻¹] :=
  { OreLocalization.instMulOreLocalization,
    OreLocalization.instOneOreLocalization with
    one_mul := OreLocalization.one_mul
    mul_one := OreLocalization.mul_one
    mul_assoc := OreLocalization.mul_assoc }

protected theorem mul_inv (s s' : S) : ((s : R) /ₒ s') * ((s' : R) /ₒ s) = 1 := by
  simp [oreDiv_mul_char (s : R) s' s' s 1 1 (by simp)]
  -- 🎉 no goals
#align ore_localization.mul_inv OreLocalization.mul_inv

@[simp]
protected theorem mul_one_div {r : R} {s t : S} : (r /ₒ s) * (1 /ₒ t) = r /ₒ (t * s) := by
  simp [oreDiv_mul_char r 1 s t 1 s (by simp)]
  -- 🎉 no goals
#align ore_localization.mul_one_div OreLocalization.mul_one_div

@[simp]
protected theorem mul_cancel {r : R} {s t : S} : (r /ₒ s) * ((s : R) /ₒ t) = r /ₒ t := by
  simp [oreDiv_mul_char r s s t 1 1 (by simp)]
  -- 🎉 no goals
#align ore_localization.mul_cancel OreLocalization.mul_cancel

@[simp]
protected theorem mul_cancel' {r₁ r₂ : R} {s t : S} :
    (r₁ /ₒ s) * ((s * r₂) /ₒ t) = (r₁ * r₂) /ₒ t := by
  simp [oreDiv_mul_char r₁ (s * r₂) s t r₂ 1 (by simp)]
  -- 🎉 no goals
#align ore_localization.mul_cancel' OreLocalization.mul_cancel'

@[simp]
theorem div_one_mul {p r : R} {s : S} : (r /ₒ 1) * (p /ₒ s) = (r * p) /ₒ s := by
  --TODO use coercion r ↦ r /ₒ 1
  simp [oreDiv_mul_char r p 1 s p 1 (by simp)]
  -- 🎉 no goals
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
def universalMulHom : R[S⁻¹] →* T
    where
  -- Porting note: `simp only []` required for beta reductions
  toFun x :=
    x.liftExpand (fun r s => f r * ((fS s)⁻¹ : Units T)) fun r t s ht => by
      simp only []
      -- ⊢ ↑f r * ↑(↑fS s)⁻¹ = ↑f (r * t) * ↑(↑fS { val := ↑s * t, property := ht })⁻¹
      have : (fS ⟨s * t, ht⟩ : T) = fS s * f t := by
        simp only [← hf, MonoidHom.map_mul]
      conv_rhs =>
        rw [MonoidHom.map_mul, ← mul_one (f r), ← Units.val_one, ← mul_left_inv (fS s)]
        rw [Units.val_mul, ← mul_assoc, mul_assoc _ (fS s : T), ← this, mul_assoc]
      simp only [mul_one, Units.mul_inv]
      -- 🎉 no goals
  map_one' := by simp only []; rw [OreLocalization.one_def, liftExpand_of]; simp
                 -- ⊢ liftExpand (fun r s => ↑f r * ↑(↑fS s)⁻¹) (_ : ∀ (r t : R) (s : { x // x ∈ S …
                               -- ⊢ ↑f 1 * ↑(↑fS 1)⁻¹ = 1
                                                                            -- 🎉 no goals
  map_mul' x y := by
    simp only []
    -- ⊢ liftExpand (fun r s => ↑f r * ↑(↑fS s)⁻¹) (_ : ∀ (r t : R) (s : { x // x ∈ S …
    induction' x using OreLocalization.ind with r₁ s₁
    -- ⊢ liftExpand (fun r s => ↑f r * ↑(↑fS s)⁻¹) (_ : ∀ (r t : R) (s : { x // x ∈ S …
    induction' y using OreLocalization.ind with r₂ s₂
    -- ⊢ liftExpand (fun r s => ↑f r * ↑(↑fS s)⁻¹) (_ : ∀ (r t : R) (s : { x // x ∈ S …
    rcases oreDivMulChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
    -- ⊢ liftExpand (fun r s => ↑f r * ↑(↑fS s)⁻¹) (_ : ∀ (r t : R) (s : { x // x ∈ S …
                                                              -- ⊢ liftExpand (fun r s => ↑f r * ↑(↑fS s)⁻¹) (_ : ∀ (r t : R) (s : { x // x ∈ S …
                                                                        -- ⊢ liftExpand (fun r s => ↑f r * ↑(↑fS s)⁻¹) (_ : ∀ (r t : R) (s : { x // x ∈ S …
    rw [liftExpand_of, liftExpand_of, liftExpand_of]
    -- ⊢ ↑f (r₁ * ra) * ↑(↑fS (s₂ * sa))⁻¹ = ↑f r₁ * ↑(↑fS s₁)⁻¹ * (↑f r₂ * ↑(↑fS s₂) …
    conv_rhs =>
      congr
      · skip
      congr
      rw [← mul_one (f r₂), ← (fS sa).mul_inv, ← mul_assoc, ← hf, ← f.map_mul, ha, f.map_mul]
    rw [mul_assoc, mul_assoc, mul_assoc, ← mul_assoc _ (f s₁), hf s₁, (fS s₁).inv_mul, one_mul,
      f.map_mul, mul_assoc, fS.map_mul, ← Units.val_mul]
    rfl
    -- 🎉 no goals
#align ore_localization.universal_mul_hom OreLocalization.universalMulHom

theorem universalMulHom_apply {r : R} {s : S} :
    universalMulHom f fS hf (r /ₒ s) = f r * ((fS s)⁻¹ : Units T) :=
  rfl
#align ore_localization.universal_mul_hom_apply OreLocalization.universalMulHom_apply

theorem universalMulHom_commutes {r : R} : universalMulHom f fS hf (numeratorHom r) = f r := by
  simp [numeratorHom_apply, universalMulHom_apply]
  -- 🎉 no goals
#align ore_localization.universal_mul_hom_commutes OreLocalization.universalMulHom_commutes

/-- The universal morphism `universalMulHom` is unique. -/
theorem universalMulHom_unique (φ : R[S⁻¹] →* T) (huniv : ∀ r : R, φ (numeratorHom r) = f r) :
    φ = universalMulHom f fS hf := by
  ext x; induction' x using OreLocalization.ind with r s
  -- ⊢ ↑φ x = ↑(universalMulHom f fS hf) x
         -- ⊢ ↑φ (r /ₒ s) = ↑(universalMulHom f fS hf) (r /ₒ s)
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
  -- 🎉 no goals
#align ore_localization.ore_div_mul_ore_div_comm OreLocalization.oreDiv_mul_oreDiv_comm

instance : CommMonoid R[S⁻¹] :=
  { OreLocalization.instMonoidOreLocalization with
    mul_comm := fun x y => by
      induction' x using OreLocalization.ind with r₁ s₁
      -- ⊢ r₁ /ₒ s₁ * y = y * (r₁ /ₒ s₁)
      induction' y using OreLocalization.ind with r₂ s₂
      -- ⊢ r₁ /ₒ s₁ * (r₂ /ₒ s₂) = r₂ /ₒ s₂ * (r₁ /ₒ s₁)
      rw [oreDiv_mul_oreDiv_comm, oreDiv_mul_oreDiv_comm, mul_comm r₁, mul_comm s₁] }
      -- 🎉 no goals

variable (R S)

/-- The morphism `numeratorHom` is a monoid localization map in the case of commutative `R`. -/
protected def localizationMap : S.LocalizationMap R[S⁻¹]
    where
  toFun := numeratorHom
  map_one' := rfl
  map_mul' r₁ r₂ := by simp
                       -- 🎉 no goals
  map_units' := numerator_isUnit
  surj' z := by
    induction' z using OreLocalization.ind with r s
    -- ⊢ ∃ x, r /ₒ s * OneHom.toFun ↑{ toOneHom := { toFun := ↑numeratorHom, map_one' …
    use (r, s); dsimp
    -- ⊢ r /ₒ s * OneHom.toFun ↑{ toOneHom := { toFun := ↑numeratorHom, map_one' := ( …
                -- ⊢ r /ₒ s * ↑numeratorHom ↑s = ↑numeratorHom r
    rw [numeratorHom_apply, numeratorHom_apply]; simp
    -- ⊢ r /ₒ s * (↑s /ₒ 1) = r /ₒ 1
                                                 -- 🎉 no goals
  eq_iff_exists' r₁ r₂ := by
    dsimp; constructor
    -- ⊢ ↑numeratorHom r₁ = ↑numeratorHom r₂ ↔ ∃ c, ↑c * r₁ = ↑c * r₂
           -- ⊢ ↑numeratorHom r₁ = ↑numeratorHom r₂ → ∃ c, ↑c * r₁ = ↑c * r₂
    · intro h
      -- ⊢ ∃ c, ↑c * r₁ = ↑c * r₂
      rw [numeratorHom_apply, numeratorHom_apply, oreDiv_eq_iff] at h
      -- ⊢ ∃ c, ↑c * r₁ = ↑c * r₂
      rcases h with ⟨u, v, h₁, h₂⟩
      -- ⊢ ∃ c, ↑c * r₁ = ↑c * r₂
      dsimp at h₂
      -- ⊢ ∃ c, ↑c * r₁ = ↑c * r₂
      rw [one_mul, one_mul] at h₂
      -- ⊢ ∃ c, ↑c * r₁ = ↑c * r₂
      subst h₂
      -- ⊢ ∃ c, ↑c * r₁ = ↑c * r₂
      use u
      -- ⊢ ↑u * r₁ = ↑u * r₂
      simpa only [mul_comm] using h₁.symm
      -- 🎉 no goals
    · rintro ⟨s, h⟩
      -- ⊢ ↑numeratorHom r₁ = ↑numeratorHom r₂
      rw [numeratorHom_apply, numeratorHom_apply, oreDiv_eq_iff]
      -- ⊢ ∃ u v, r₂ * ↑u = r₁ * v ∧ ↑1 * ↑u = ↑1 * v
      refine' ⟨s, s, _, _⟩
      -- ⊢ r₂ * ↑s = r₁ * ↑s
      · simpa [mul_comm] using h.symm
        -- 🎉 no goals
      · simp [one_mul]
        -- 🎉 no goals
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
  -- ⊢ (r₁ * ↑(oreDenom (↑s₁) s₂) + r₂ * oreNum (↑s₁) s₂) /ₒ (s₁ * oreDenom (↑s₁) s …
  have ha := ore_eq (s₁ : R) s₂
  -- ⊢ (r₁ * ↑(oreDenom (↑s₁) s₂) + r₂ * oreNum (↑s₁) s₂) /ₒ (s₁ * oreDenom (↑s₁) s …
  set! ra := oreNum (s₁ : R) s₂ with h
  -- ⊢ (r₁ * ↑(oreDenom (↑s₁) s₂) + r₂ * oreNum (↑s₁) s₂) /ₒ (s₁ * oreDenom (↑s₁) s …
  rw [← h] at *
  -- ⊢ (r₁ * ↑(oreDenom (↑s₁) s₂) + r₂ * ra) /ₒ (s₁ * oreDenom (↑s₁) s₂) = (r₁ * ↑s …
  clear h
  -- ⊢ (r₁ * ↑(oreDenom (↑s₁) s₂) + r₂ * ra) /ₒ (s₁ * oreDenom (↑s₁) s₂) = (r₁ * ↑s …
  -- r tilde
  set! sa := oreDenom (s₁ : R) s₂ with h
  -- ⊢ (r₁ * ↑(oreDenom (↑s₁) s₂) + r₂ * ra) /ₒ (s₁ * oreDenom (↑s₁) s₂) = (r₁ * ↑s …
  rw [← h] at *
  -- ⊢ (r₁ * ↑sa + r₂ * ra) /ₒ (s₁ * sa) = (r₁ * ↑sb + r₂ * rb) /ₒ (s₁ * sb)
  clear h
  -- ⊢ (r₁ * ↑sa + r₂ * ra) /ₒ (s₁ * sa) = (r₁ * ↑sb + r₂ * rb) /ₒ (s₁ * sb)
  -- s tilde
  rcases oreCondition (sa : R) sb with ⟨rc, sc, hc⟩
  -- ⊢ (r₁ * ↑sa + r₂ * ra) /ₒ (s₁ * sa) = (r₁ * ↑sb + r₂ * rb) /ₒ (s₁ * sb)
  -- s*, r*
  have : (s₂ : R) * (rb * rc) = s₂ * (ra * sc) := by
    rw [← mul_assoc, ← hb, mul_assoc, ← hc, ← mul_assoc, ← mul_assoc, ha]
  rcases ore_left_cancel _ _ s₂ this with ⟨sd, hd⟩
  -- ⊢ (r₁ * ↑sa + r₂ * ra) /ₒ (s₁ * sa) = (r₁ * ↑sb + r₂ * rb) /ₒ (s₁ * sb)
  -- s#
  symm
  -- ⊢ (r₁ * ↑sb + r₂ * rb) /ₒ (s₁ * sb) = (r₁ * ↑sa + r₂ * ra) /ₒ (s₁ * sa)
  rw [oreDiv_eq_iff]
  -- ⊢ ∃ u v, (r₁ * ↑sa + r₂ * ra) * ↑u = (r₁ * ↑sb + r₂ * rb) * v ∧ ↑(s₁ * sa) * ↑ …
  use sc * sd
  -- ⊢ ∃ v, (r₁ * ↑sa + r₂ * ra) * ↑(sc * sd) = (r₁ * ↑sb + r₂ * rb) * v ∧ ↑(s₁ * s …
  use rc * sd
  -- ⊢ (r₁ * ↑sa + r₂ * ra) * ↑(sc * sd) = (r₁ * ↑sb + r₂ * rb) * (rc * ↑sd) ∧ ↑(s₁ …
  constructor <;> simp only [Submonoid.coe_mul]
  -- ⊢ (r₁ * ↑sa + r₂ * ra) * ↑(sc * sd) = (r₁ * ↑sb + r₂ * rb) * (rc * ↑sd)
                  -- ⊢ (r₁ * ↑(oreDenom (↑s₁) s₂) + r₂ * oreNum (↑s₁) s₂) * (↑sc * ↑sd) = (r₁ * ↑sb …
                  -- ⊢ ↑s₁ * ↑(oreDenom (↑s₁) s₂) * (↑sc * ↑sd) = ↑s₁ * ↑sb * (rc * ↑sd)
  · noncomm_ring
    -- ⊢ r₁ * (↑(oreDenom (↑s₁) s₂) * (↑sc * ↑sd)) + r₂ * (oreNum (↑s₁) s₂ * (↑sc * ↑ …
    rw [← mul_assoc (a := rb), hd, ← mul_assoc (a := (sa : R)), hc]
    -- ⊢ r₁ * (↑sb * rc * ↑sd) + r₂ * (oreNum (↑s₁) s₂ * (↑sc * ↑sd)) = r₁ * (↑sb * ( …
    noncomm_ring
    -- 🎉 no goals
  · rw [mul_assoc (a := (s₁ : R)), ← mul_assoc (a := (sa : R)), hc]
    -- ⊢ ↑s₁ * (↑sb * rc * ↑sd) = ↑s₁ * ↑sb * (rc * ↑sd)
    noncomm_ring
    -- 🎉 no goals

attribute [local instance] OreLocalization.oreEqv

private def add' (r₂ : R) (s₂ : S) : R[S⁻¹] → R[S⁻¹] :=
  (--plus tilde
      Quotient.lift
      fun r₁s₁ : R × S => add'' r₁s₁.1 r₁s₁.2 r₂ s₂) <| by
    -- Porting note: `assoc_rw` & `noncomm_ring` were not ported yet
    rintro ⟨r₁', s₁'⟩ ⟨r₁, s₁⟩ ⟨sb, rb, hb, hb'⟩
    -- ⊢ OreLocalization.add'' (r₁', s₁').fst (r₁', s₁').snd r₂ s₂ = OreLocalization. …
    -- s*, r*
    rcases oreCondition (s₁' : R) s₂ with ⟨rc, sc, hc⟩
    -- ⊢ OreLocalization.add'' (r₁', s₁').fst (r₁', s₁').snd r₂ s₂ = OreLocalization. …
    --s~~, r~~
    rcases oreCondition rb sc with ⟨rd, sd, hd⟩
    -- ⊢ OreLocalization.add'' (r₁', s₁').fst (r₁', s₁').snd r₂ s₂ = OreLocalization. …
    -- s#, r#
    dsimp at *
    -- ⊢ OreLocalization.add'' r₁' s₁' r₂ s₂ = OreLocalization.add'' r₁ s₁ r₂ s₂
    rw [add''_char _ _ _ _ rc sc hc]
    -- ⊢ (r₁' * ↑sc + r₂ * rc) /ₒ (s₁' * sc) = OreLocalization.add'' r₁ s₁ r₂ s₂
    have : ↑s₁ * ↑(sb * sd) = ↑s₂ * (rc * rd) := by
      simp only [Submonoid.coe_mul]
      rw [← mul_assoc, hb', mul_assoc, hd, ← mul_assoc, hc, mul_assoc]
    rw [add''_char _ _ _ _ (rc * rd : R) (sb * sd : S) this]
    -- ⊢ (r₁' * ↑sc + r₂ * rc) /ₒ (s₁' * sc) = (r₁ * ↑(sb * sd) + r₂ * (rc * rd)) /ₒ  …
    simp only [Submonoid.coe_mul]
    -- ⊢ (r₁' * ↑sc + r₂ * rc) /ₒ (s₁' * sc) = (r₁ * (↑sb * ↑sd) + r₂ * (rc * rd)) /ₒ …
    rw [← mul_assoc (a := r₁) (b := (sb : R)), hb, mul_assoc (a := r₁') (b := (rb : R)), hd,
      ← mul_assoc, ← mul_assoc, ← add_mul, oreDiv_eq_iff]
    use 1
    -- ⊢ ∃ v, (r₁' * ↑sc + r₂ * rc) * rd * ↑1 = (r₁' * ↑sc + r₂ * rc) * v ∧ ↑(s₁ * (s …
    use rd
    -- ⊢ (r₁' * ↑sc + r₂ * rc) * rd * ↑1 = (r₁' * ↑sc + r₂ * rc) * rd ∧ ↑(s₁ * (sb *  …
    constructor
    -- ⊢ (r₁' * ↑sc + r₂ * rc) * rd * ↑1 = (r₁' * ↑sc + r₂ * rc) * rd
    · simp
      -- 🎉 no goals
    · simp only [mul_one, Submonoid.coe_one, Submonoid.coe_mul] at this ⊢
      -- ⊢ ↑s₁ * (↑sb * ↑sd) = ↑s₁' * ↑sc * rd
      rw [hc, this, mul_assoc]
      -- 🎉 no goals

private theorem add'_comm (r₁ r₂ : R) (s₁ s₂ : S) :
    add' r₁ s₁ (r₂ /ₒ s₂) = add' r₂ s₂ (r₁ /ₒ s₁) := by
  -- Porting note: `assoc_rw` & `noncomm_ring` were not ported yet
  -- Porting note: `Quotient.mk'` required
  simp only [add', oreDiv, add'', Quotient.mk', Quotient.lift_mk]
  -- ⊢ Quotient.mk (oreEqv R S) (r₂ * ↑(oreDenom (↑s₂) s₁) + r₁ * oreNum (↑s₂) s₁,  …
  -- Porting note: `Quotient.eq` should be used in `rw` instead of `simp`
  rw [Quotient.eq]
  -- ⊢ (r₂ * ↑(oreDenom (↑s₂) s₁) + r₁ * oreNum (↑s₂) s₁, s₂ * oreDenom (↑s₂) s₁) ≈ …
  have hb := ore_eq (↑s₂) s₁
  -- ⊢ (r₂ * ↑(oreDenom (↑s₂) s₁) + r₁ * oreNum (↑s₂) s₁, s₂ * oreDenom (↑s₂) s₁) ≈ …
  -- Porting note: `set ... with h; rw [← h]; clear h`s aren't required anymore
  set rb := oreNum (↑s₂) s₁
  -- ⊢ (r₂ * ↑(oreDenom (↑s₂) s₁) + r₁ * rb, s₂ * oreDenom (↑s₂) s₁) ≈ (r₁ * ↑(oreD …
  set sb := oreDenom (↑s₂) s₁
  -- ⊢ (r₂ * ↑sb + r₁ * rb, s₂ * sb) ≈ (r₁ * ↑(oreDenom (↑s₁) s₂) + r₂ * oreNum (↑s …
  have ha := ore_eq (↑s₁) s₂
  -- ⊢ (r₂ * ↑sb + r₁ * rb, s₂ * sb) ≈ (r₁ * ↑(oreDenom (↑s₁) s₂) + r₂ * oreNum (↑s …
  set ra := oreNum (↑s₁) s₂
  -- ⊢ (r₂ * ↑sb + r₁ * rb, s₂ * sb) ≈ (r₁ * ↑(oreDenom (↑s₁) s₂) + r₂ * ra, s₁ * o …
  set sa := oreDenom (↑s₁) s₂
  -- ⊢ (r₂ * ↑sb + r₁ * rb, s₂ * sb) ≈ (r₁ * ↑sa + r₂ * ra, s₁ * sa)
  rcases oreCondition ra sb with ⟨rc, sc, hc⟩
  -- ⊢ (r₂ * ↑sb + r₁ * rb, s₂ * sb) ≈ (r₁ * ↑sa + r₂ * ra, s₁ * sa)
  -- r#, s#
  have : (s₁ : R) * (rb * rc) = s₁ * (sa * sc) := by
    rw [← mul_assoc, ← hb, mul_assoc, ← hc, ← mul_assoc, ← ha, mul_assoc]
  rcases ore_left_cancel _ _ s₁ this with ⟨sd, hd⟩
  -- ⊢ (r₂ * ↑sb + r₁ * rb, s₂ * sb) ≈ (r₁ * ↑sa + r₂ * ra, s₁ * sa)
  -- s+
  use sc * sd
  -- ⊢ ∃ v, (r₁ * ↑sa + r₂ * ra, s₁ * sa).fst * ↑(sc * sd) = (r₂ * ↑sb + r₁ * rb, s …
  use rc * sd
  -- ⊢ (r₁ * ↑sa + r₂ * ra, s₁ * sa).fst * ↑(sc * sd) = (r₂ * ↑sb + r₁ * rb, s₂ * s …
  dsimp
  -- ⊢ (r₁ * ↑(oreDenom (↑s₁) s₂) + r₂ * oreNum (↑s₁) s₂) * (↑sc * ↑sd) = (r₂ * ↑(o …
  constructor
  -- ⊢ (r₁ * ↑(oreDenom (↑s₁) s₂) + r₂ * oreNum (↑s₁) s₂) * (↑sc * ↑sd) = (r₂ * ↑(o …
  · rw [add_mul, add_mul, add_comm, mul_assoc (a := r₁) (b := (sa : R)),
      ← mul_assoc (a := (sa : R)), ← hd, mul_assoc (a := r₂) (b := ra),
      ← mul_assoc (a := ra) (b := (sc : R)), hc]
    simp only [mul_assoc]
    -- 🎉 no goals
  · rw [mul_assoc, ← mul_assoc (sa : R), ← hd, hb]
    -- ⊢ ↑s₁ * (rb * rc * ↑sd) = ↑s₁ * rb * (rc * ↑sd)
    simp only [mul_assoc]
    -- 🎉 no goals

/-- The addition on the Ore localization. -/
private def add : R[S⁻¹] → R[S⁻¹] → R[S⁻¹] := fun x =>
  Quotient.lift (fun rs : R × S => add' rs.1 rs.2 x)
    (by
      rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ hyz
      -- ⊢ (fun rs => OreLocalization.add' rs.fst rs.snd x) (r₁, s₁) = (fun rs => OreLo …
      induction' x using OreLocalization.ind with r₃ s₃
      -- ⊢ (fun rs => OreLocalization.add' rs.fst rs.snd (r₃ /ₒ s₃)) (r₁, s₁) = (fun rs …
      dsimp; rw [add'_comm, add'_comm r₂]
      -- ⊢ OreLocalization.add' r₁ s₁ (r₃ /ₒ s₃) = OreLocalization.add' r₂ s₂ (r₃ /ₒ s₃)
             -- ⊢ OreLocalization.add' r₃ s₃ (r₁ /ₒ s₁) = OreLocalization.add' r₃ s₃ (r₂ /ₒ s₂)
      -- Porting note: `Quotient.mk'` required
      simp [(· /ₒ ·), Quotient.mk', Quotient.sound hyz])
      -- 🎉 no goals

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
  -- 🎉 no goals
#align ore_localization.add_ore_div OreLocalization.add_oreDiv

protected theorem add_assoc (x y z : R[S⁻¹]) : x + y + z = x + (y + z) := by
  -- Porting note: `assoc_rw` was not ported yet
  induction' x using OreLocalization.ind with r₁ s₁
  -- ⊢ r₁ /ₒ s₁ + y + z = r₁ /ₒ s₁ + (y + z)
  induction' y using OreLocalization.ind with r₂ s₂
  -- ⊢ r₁ /ₒ s₁ + r₂ /ₒ s₂ + z = r₁ /ₒ s₁ + (r₂ /ₒ s₂ + z)
  induction' z using OreLocalization.ind with r₃ s₃
  -- ⊢ r₁ /ₒ s₁ + r₂ /ₒ s₂ + r₃ /ₒ s₃ = r₁ /ₒ s₁ + (r₂ /ₒ s₂ + r₃ /ₒ s₃)
  rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
  -- ⊢ r₁ /ₒ s₁ + r₂ /ₒ s₂ + r₃ /ₒ s₃ = r₁ /ₒ s₁ + (r₂ /ₒ s₂ + r₃ /ₒ s₃)
                                                            -- ⊢ (r₁ * ↑sa + r₂ * ra) /ₒ (s₁ * sa) + r₃ /ₒ s₃ = r₁ /ₒ s₁ + (r₂ /ₒ s₂ + r₃ /ₒ  …
                                                                      -- ⊢ (r₁ * ↑sa + r₂ * ra) /ₒ (s₁ * sa) + r₃ /ₒ s₃ = r₁ /ₒ s₁ + (r₂ /ₒ s₂ + r₃ /ₒ  …
  rcases oreDivAddChar' r₂ r₃ s₂ s₃ with ⟨rb, sb, hb, hb'⟩; rw [hb']; clear hb'
  -- ⊢ (r₁ * ↑sa + r₂ * ra) /ₒ (s₁ * sa) + r₃ /ₒ s₃ = r₁ /ₒ s₁ + (r₂ /ₒ s₂ + r₃ /ₒ  …
                                                            -- ⊢ (r₁ * ↑sa + r₂ * ra) /ₒ (s₁ * sa) + r₃ /ₒ s₃ = r₁ /ₒ s₁ + (r₂ * ↑sb + r₃ * r …
                                                                      -- ⊢ (r₁ * ↑sa + r₂ * ra) /ₒ (s₁ * sa) + r₃ /ₒ s₃ = r₁ /ₒ s₁ + (r₂ * ↑sb + r₃ * r …
  rcases oreDivAddChar' (r₁ * sa + r₂ * ra) r₃ (s₁ * sa) s₃ with ⟨rc, sc, hc, q⟩; rw [q]; clear q
  -- ⊢ (r₁ * ↑sa + r₂ * ra) /ₒ (s₁ * sa) + r₃ /ₒ s₃ = r₁ /ₒ s₁ + (r₂ * ↑sb + r₃ * r …
                                                                                  -- ⊢ ((r₁ * ↑sa + r₂ * ra) * ↑sc + r₃ * rc) /ₒ (s₁ * sa * sc) = r₁ /ₒ s₁ + (r₂ *  …
                                                                                          -- ⊢ ((r₁ * ↑sa + r₂ * ra) * ↑sc + r₃ * rc) /ₒ (s₁ * sa * sc) = r₁ /ₒ s₁ + (r₂ *  …
  rcases oreDivAddChar' r₁ (r₂ * sb + r₃ * rb) s₁ (s₂ * sb) with ⟨rd, sd, hd, q⟩; rw [q]; clear q
  -- ⊢ ((r₁ * ↑sa + r₂ * ra) * ↑sc + r₃ * rc) /ₒ (s₁ * sa * sc) = r₁ /ₒ s₁ + (r₂ *  …
                                                                                  -- ⊢ ((r₁ * ↑sa + r₂ * ra) * ↑sc + r₃ * rc) /ₒ (s₁ * sa * sc) = (r₁ * ↑sd + (r₂ * …
                                                                                          -- ⊢ ((r₁ * ↑sa + r₂ * ra) * ↑sc + r₃ * rc) /ₒ (s₁ * sa * sc) = (r₁ * ↑sd + (r₂ * …
  simp only [right_distrib, mul_assoc, add_assoc]
  -- ⊢ (r₁ * (↑sa * ↑sc) + (r₂ * (ra * ↑sc) + r₃ * rc)) /ₒ (s₁ * (sa * sc)) = (r₁ * …
  -- Porting note: `simp` required because `repeat' rw` behaves differently
  simp only [← add_oreDiv]
  -- ⊢ r₁ * (↑sa * ↑sc) /ₒ (s₁ * (sa * sc)) + (r₂ * (ra * ↑sc) /ₒ (s₁ * (sa * sc))  …
  congr 1
  -- ⊢ r₁ * (↑sa * ↑sc) /ₒ (s₁ * (sa * sc)) = r₁ * ↑sd /ₒ (s₁ * sd)
  · rw [← OreLocalization.expand', ← mul_assoc, ← mul_assoc, ← OreLocalization.expand', ←
      OreLocalization.expand']
  congr 1
  -- ⊢ r₂ * (ra * ↑sc) /ₒ (s₁ * (sa * sc)) = r₂ * (↑sb * rd) /ₒ (s₁ * sd)
  · simp_rw [← Submonoid.coe_mul] at ha hd
    -- ⊢ r₂ * (ra * ↑sc) /ₒ (s₁ * (sa * sc)) = r₂ * (↑sb * rd) /ₒ (s₁ * sd)
    rw [Subtype.coe_eq_of_eq_mk hd, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← OreLocalization.expand,
      ← OreLocalization.expand', Subtype.coe_eq_of_eq_mk ha, ← OreLocalization.expand]
    apply OreLocalization.expand'
    -- 🎉 no goals
  · rcases oreCondition (sd : R) (sa * sc) with ⟨re, _, _⟩
    -- ⊢ r₃ * rc /ₒ (s₁ * (sa * sc)) = r₃ * (rb * rd) /ₒ (s₁ * sd)
    · simp_rw [← Submonoid.coe_mul] at hb hc hd
      -- ⊢ r₃ * rc /ₒ (s₁ * (sa * sc)) = r₃ * (rb * rd) /ₒ (s₁ * sd)
      rw [← mul_assoc, Subtype.coe_eq_of_eq_mk hc]
      -- ⊢ r₃ * rc /ₒ { val := ↑s₃ * rc, property := (_ : ↑s₃ * rc ∈ ↑S) } = r₃ * (rb * …
      rw [← OreLocalization.expand, Subtype.coe_eq_of_eq_mk hd, ← mul_assoc, ←
        OreLocalization.expand, Subtype.coe_eq_of_eq_mk hb]
      apply OreLocalization.expand
      -- 🎉 no goals
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
  -- ⊢ ∃ u v, 0 * ↑u = 0 * v ∧ ↑1 * ↑u = ↑s * v
  exact ⟨s, 1, by simp⟩
  -- 🎉 no goals
#align ore_localization.zero_div_eq_zero OreLocalization.zero_div_eq_zero

protected theorem zero_add (x : R[S⁻¹]) : 0 + x = x := by
  induction x using OreLocalization.ind
  -- ⊢ 0 + r✝ /ₒ s✝ = r✝ /ₒ s✝
  rw [← zero_div_eq_zero, add_oreDiv]; simp
  -- ⊢ (0 + r✝) /ₒ s✝ = r✝ /ₒ s✝
                                       -- 🎉 no goals
#align ore_localization.zero_add OreLocalization.zero_add

protected theorem add_comm (x y : R[S⁻¹]) : x + y = y + x := by
  induction x using OreLocalization.ind
  -- ⊢ r✝ /ₒ s✝ + y = y + r✝ /ₒ s✝
  induction y using OreLocalization.ind
  -- ⊢ r✝¹ /ₒ s✝¹ + r✝ /ₒ s✝ = r✝ /ₒ s✝ + r✝¹ /ₒ s✝¹
  change add' _ _ (_ /ₒ _) = _; apply add'_comm
  -- ⊢ OreLocalization.add' (r✝, s✝).fst (r✝, s✝).snd (r✝¹ /ₒ s✝¹) = r✝ /ₒ s✝ + r✝¹ …
                                -- 🎉 no goals
#align ore_localization.add_comm OreLocalization.add_comm

instance instAddCommMonoidOreLocalization : AddCommMonoid R[S⁻¹] :=
  { OreLocalization.instAddOreLocalization with
    add_comm := OreLocalization.add_comm
    add_assoc := OreLocalization.add_assoc
    zero := zero
    zero_add := OreLocalization.zero_add
    add_zero := fun x => by rw [OreLocalization.add_comm, OreLocalization.zero_add] }
                            -- 🎉 no goals

protected theorem zero_mul (x : R[S⁻¹]) : 0 * x = 0 := by
  induction' x using OreLocalization.ind with r s
  -- ⊢ 0 * (r /ₒ s) = 0
  rw [OreLocalization.zero_def, oreDiv_mul_char 0 r 1 s r 1 (by simp)]; simp
  -- ⊢ 0 * r /ₒ (s * 1) = 0 /ₒ 1
                                                                        -- 🎉 no goals
#align ore_localization.zero_mul OreLocalization.zero_mul

protected theorem mul_zero (x : R[S⁻¹]) : x * 0 = 0 := by
  induction' x using OreLocalization.ind with r s
  -- ⊢ r /ₒ s * 0 = 0
  rw [OreLocalization.zero_def, oreDiv_mul_char r 0 s 1 0 1 (by simp)]; simp
  -- ⊢ r * 0 /ₒ (1 * 1) = 0 /ₒ 1
                                                                        -- 🎉 no goals
#align ore_localization.mul_zero OreLocalization.mul_zero

protected theorem left_distrib (x y z : R[S⁻¹]) : x * (y + z) = x * y + x * z := by
  induction' x using OreLocalization.ind with r₁ s₁
  -- ⊢ r₁ /ₒ s₁ * (y + z) = r₁ /ₒ s₁ * y + r₁ /ₒ s₁ * z
  induction' y using OreLocalization.ind with r₂ s₂
  -- ⊢ r₁ /ₒ s₁ * (r₂ /ₒ s₂ + z) = r₁ /ₒ s₁ * (r₂ /ₒ s₂) + r₁ /ₒ s₁ * z
  induction' z using OreLocalization.ind with r₃ s₃
  -- ⊢ r₁ /ₒ s₁ * (r₂ /ₒ s₂ + r₃ /ₒ s₃) = r₁ /ₒ s₁ * (r₂ /ₒ s₂) + r₁ /ₒ s₁ * (r₃ /ₒ …
  rcases oreDivAddChar' r₂ r₃ s₂ s₃ with ⟨ra, sa, ha, q⟩
  -- ⊢ r₁ /ₒ s₁ * (r₂ /ₒ s₂ + r₃ /ₒ s₃) = r₁ /ₒ s₁ * (r₂ /ₒ s₂) + r₁ /ₒ s₁ * (r₃ /ₒ …
  rw [q]
  -- ⊢ r₁ /ₒ s₁ * ((r₂ * ↑sa + r₃ * ra) /ₒ (s₂ * sa)) = r₁ /ₒ s₁ * (r₂ /ₒ s₂) + r₁  …
  clear q
  -- ⊢ r₁ /ₒ s₁ * ((r₂ * ↑sa + r₃ * ra) /ₒ (s₂ * sa)) = r₁ /ₒ s₁ * (r₂ /ₒ s₂) + r₁  …
  rw [OreLocalization.expand' r₂ s₂ sa]
  -- ⊢ r₁ /ₒ s₁ * ((r₂ * ↑sa + r₃ * ra) /ₒ (s₂ * sa)) = r₁ /ₒ s₁ * (r₂ * ↑sa /ₒ (s₂ …
  rcases oreDivMulChar' r₁ (r₂ * sa) s₁ (s₂ * sa) with ⟨rb, sb, hb, q⟩
  -- ⊢ r₁ /ₒ s₁ * ((r₂ * ↑sa + r₃ * ra) /ₒ (s₂ * sa)) = r₁ /ₒ s₁ * (r₂ * ↑sa /ₒ (s₂ …
  rw [q]
  -- ⊢ r₁ /ₒ s₁ * ((r₂ * ↑sa + r₃ * ra) /ₒ (s₂ * sa)) = r₁ * rb /ₒ (s₂ * sa * sb) + …
  clear q
  -- ⊢ r₁ /ₒ s₁ * ((r₂ * ↑sa + r₃ * ra) /ₒ (s₂ * sa)) = r₁ * rb /ₒ (s₂ * sa * sb) + …
  have hs₃rasb : ↑s₃ * (ra * sb) ∈ S := by
    rw [← mul_assoc, ← ha]
    norm_cast
    apply SetLike.coe_mem
  rw [OreLocalization.expand _ _ _ hs₃rasb]
  -- ⊢ r₁ /ₒ s₁ * ((r₂ * ↑sa + r₃ * ra) /ₒ (s₂ * sa)) = r₁ * rb /ₒ (s₂ * sa * sb) + …
  have ha' : ↑(s₂ * sa * sb) = ↑s₃ * (ra * sb) := by simp [ha, ← mul_assoc]
  -- ⊢ r₁ /ₒ s₁ * ((r₂ * ↑sa + r₃ * ra) /ₒ (s₂ * sa)) = r₁ * rb /ₒ (s₂ * sa * sb) + …
  rw [← Subtype.coe_eq_of_eq_mk ha']
  -- ⊢ r₁ /ₒ s₁ * ((r₂ * ↑sa + r₃ * ra) /ₒ (s₂ * sa)) = r₁ * rb /ₒ (s₂ * sa * sb) + …
  rcases oreDivMulChar' r₁ (r₃ * (ra * sb)) s₁ (s₂ * sa * sb) with ⟨rc, sc, hc, hc'⟩
  -- ⊢ r₁ /ₒ s₁ * ((r₂ * ↑sa + r₃ * ra) /ₒ (s₂ * sa)) = r₁ * rb /ₒ (s₂ * sa * sb) + …
  rw [hc']
  -- ⊢ r₁ /ₒ s₁ * ((r₂ * ↑sa + r₃ * ra) /ₒ (s₂ * sa)) = r₁ * rb /ₒ (s₂ * sa * sb) + …
  rw [oreDiv_add_char (s₂ * sa * sb) (s₂ * sa * sb * sc) 1 sc (by simp)]
  -- ⊢ r₁ /ₒ s₁ * ((r₂ * ↑sa + r₃ * ra) /ₒ (s₂ * sa)) = (r₁ * rb * ↑sc + r₁ * rc *  …
  rw [OreLocalization.expand' (r₂ * ↑sa + r₃ * ra) (s₂ * sa) (sb * sc)]
  -- ⊢ r₁ /ₒ s₁ * ((r₂ * ↑sa + r₃ * ra) * ↑(sb * sc) /ₒ (s₂ * sa * (sb * sc))) = (r …
  conv_lhs =>
    congr
    · skip
    congr
    rw [add_mul, S.coe_mul, ← mul_assoc, hb, ← mul_assoc, mul_assoc r₃, hc, mul_assoc, ← mul_add]
  rw [OreLocalization.mul_cancel']
  -- ⊢ r₁ * (rb * ↑sc + rc) /ₒ (s₂ * sa * (sb * sc)) = (r₁ * rb * ↑sc + r₁ * rc * 1 …
  simp only [mul_one, Submonoid.coe_mul, mul_add, ← mul_assoc]
  -- 🎉 no goals
#align ore_localization.left_distrib OreLocalization.left_distrib

theorem right_distrib (x y z : R[S⁻¹]) : (x + y) * z = x * z + y * z := by
  induction' x using OreLocalization.ind with r₁ s₁
  -- ⊢ (r₁ /ₒ s₁ + y) * z = r₁ /ₒ s₁ * z + y * z
  induction' y using OreLocalization.ind with r₂ s₂
  -- ⊢ (r₁ /ₒ s₁ + r₂ /ₒ s₂) * z = r₁ /ₒ s₁ * z + r₂ /ₒ s₂ * z
  induction' z using OreLocalization.ind with r₃ s₃
  -- ⊢ (r₁ /ₒ s₁ + r₂ /ₒ s₂) * (r₃ /ₒ s₃) = r₁ /ₒ s₁ * (r₃ /ₒ s₃) + r₂ /ₒ s₂ * (r₃  …
  rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'; norm_cast at ha
  -- ⊢ (r₁ /ₒ s₁ + r₂ /ₒ s₂) * (r₃ /ₒ s₃) = r₁ /ₒ s₁ * (r₃ /ₒ s₃) + r₂ /ₒ s₂ * (r₃  …
                                                            -- ⊢ (r₁ * ↑sa + r₂ * ra) /ₒ (s₁ * sa) * (r₃ /ₒ s₃) = r₁ /ₒ s₁ * (r₃ /ₒ s₃) + r₂  …
                                                                      -- ⊢ (r₁ * ↑sa + r₂ * ra) /ₒ (s₁ * sa) * (r₃ /ₒ s₃) = r₁ /ₒ s₁ * (r₃ /ₒ s₃) + r₂  …
                                                                                 -- ⊢ (r₁ * ↑sa + r₂ * ra) /ₒ (s₁ * sa) * (r₃ /ₒ s₃) = r₁ /ₒ s₁ * (r₃ /ₒ s₃) + r₂  …
  rw [OreLocalization.expand' r₁ s₁ sa]
  -- ⊢ (r₁ * ↑sa + r₂ * ra) /ₒ (s₁ * sa) * (r₃ /ₒ s₃) = r₁ * ↑sa /ₒ (s₁ * sa) * (r₃ …
  rw [OreLocalization.expand r₂ s₂ ra (by rw [← ha]; apply SetLike.coe_mem)]
  -- ⊢ (r₁ * ↑sa + r₂ * ra) /ₒ (s₁ * sa) * (r₃ /ₒ s₃) = r₁ * ↑sa /ₒ (s₁ * sa) * (r₃ …
  rw [← Subtype.coe_eq_of_eq_mk ha]
  -- ⊢ (r₁ * ↑sa + r₂ * ra) /ₒ (s₁ * sa) * (r₃ /ₒ s₃) = r₁ * ↑sa /ₒ (s₁ * sa) * (r₃ …
  repeat rw [oreDiv_mul_oreDiv]
  -- ⊢ (r₁ * ↑sa + r₂ * ra) * oreNum r₃ (s₁ * sa) /ₒ (s₃ * oreDenom r₃ (s₁ * sa)) = …
  simp only [add_mul, add_oreDiv]
  -- 🎉 no goals
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
      -- ⊢ ↑(universalMulHom (↑f) fS hf) 0 = 0
      rw [OreLocalization.zero_def, universalMulHom_apply]
      -- ⊢ ↑↑f 0 * ↑(↑fS 1)⁻¹ = 0
      simp
      -- 🎉 no goals
    map_add' := fun x y => by
      -- Porting note: `change` required because of new `Coe`
      change (universalMulHom f.toMonoidHom fS hf : R[S⁻¹] → T) (x + y)
        = (universalMulHom f.toMonoidHom fS hf : R[S⁻¹] → T) x
        + (universalMulHom f.toMonoidHom fS hf : R[S⁻¹] → T) y
      induction' x using OreLocalization.ind with r₁ s₁
      -- ⊢ ↑(universalMulHom (↑f) fS hf) (r₁ /ₒ s₁ + y) = ↑(universalMulHom (↑f) fS hf) …
      induction' y using OreLocalization.ind with r₂ s₂
      -- ⊢ ↑(universalMulHom (↑f) fS hf) (r₁ /ₒ s₁ + r₂ /ₒ s₂) = ↑(universalMulHom (↑f) …
      rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨r₃, s₃, h₃, h₃'⟩
      -- ⊢ ↑(universalMulHom (↑f) fS hf) (r₁ /ₒ s₁ + r₂ /ₒ s₂) = ↑(universalMulHom (↑f) …
      rw [h₃']
      -- ⊢ ↑(universalMulHom (↑f) fS hf) ((r₁ * ↑s₃ + r₂ * r₃) /ₒ (s₁ * s₃)) = ↑(univer …
      clear h₃'
      -- ⊢ ↑(universalMulHom (↑f) fS hf) ((r₁ * ↑s₃ + r₂ * r₃) /ₒ (s₁ * s₃)) = ↑(univer …
      simp only [universalMulHom_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      -- ⊢ ↑f (r₁ * ↑s₃ + r₂ * r₃) * ↑(↑fS (s₁ * s₃))⁻¹ = ↑f r₁ * ↑(↑fS s₁)⁻¹ + ↑f r₂ * …
      simp only [mul_inv_rev, MonoidHom.map_mul, RingHom.map_add, RingHom.map_mul, Units.val_mul]
      -- ⊢ (↑f r₁ * ↑f ↑s₃ + ↑f r₂ * ↑f r₃) * (↑(↑fS s₃)⁻¹ * ↑(↑fS s₁)⁻¹) = ↑f r₁ * ↑(↑ …
      rw [add_mul, ← mul_assoc, mul_assoc (f r₁), hf, ← Units.val_mul]
      -- ⊢ ↑f r₁ * ↑(↑fS s₃ * (↑fS s₃)⁻¹) * ↑(↑fS s₁)⁻¹ + ↑f r₂ * ↑f r₃ * (↑(↑fS s₃)⁻¹  …
      simp only [mul_one, mul_right_inv, Units.val_one]
      -- ⊢ ↑f r₁ * ↑(↑fS s₁)⁻¹ + ↑f r₂ * ↑f r₃ * (↑(↑fS s₃)⁻¹ * ↑(↑fS s₁)⁻¹) = ↑f r₁ *  …
      congr 1
      -- ⊢ ↑f r₂ * ↑f r₃ * (↑(↑fS s₃)⁻¹ * ↑(↑fS s₁)⁻¹) = ↑f r₂ * ↑(↑fS s₂)⁻¹
      rw [mul_assoc]
      -- ⊢ ↑f r₂ * (↑f r₃ * (↑(↑fS s₃)⁻¹ * ↑(↑fS s₁)⁻¹)) = ↑f r₂ * ↑(↑fS s₂)⁻¹
      congr 1
      -- ⊢ ↑f r₃ * (↑(↑fS s₃)⁻¹ * ↑(↑fS s₁)⁻¹) = ↑(↑fS s₂)⁻¹
      norm_cast at h₃
      -- ⊢ ↑f r₃ * (↑(↑fS s₃)⁻¹ * ↑(↑fS s₁)⁻¹) = ↑(↑fS s₂)⁻¹
      have h₃' := Subtype.coe_eq_of_eq_mk h₃
      -- ⊢ ↑f r₃ * (↑(↑fS s₃)⁻¹ * ↑(↑fS s₁)⁻¹) = ↑(↑fS s₂)⁻¹
      rw [← Units.val_mul, ← mul_inv_rev, ← fS.map_mul, h₃']
      -- ⊢ ↑f r₃ * ↑(↑fS { val := ↑s₂ * r₃, property := (_ : ↑s₂ * r₃ ∈ ↑S) })⁻¹ = ↑(↑f …
      have hs₂r₃ : ↑s₂ * r₃ ∈ S := by
        rw [← h₃]
        exact SetLike.coe_mem (s₁ * s₃)
      apply (Units.inv_mul_cancel_left (fS s₂) _).symm.trans
      -- ⊢ ↑(↑fS s₂)⁻¹ * (↑(↑fS s₂) * (↑f r₃ * ↑(↑fS { val := ↑s₂ * r₃, property := (_  …
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
      -- 🎉 no goals
#align ore_localization.universal_hom OreLocalization.universalHom

theorem universalHom_apply {r : R} {s : S} :
    universalHom f fS hf (r /ₒ s) = f r * ((fS s)⁻¹ : Units T) :=
  rfl
#align ore_localization.universal_hom_apply OreLocalization.universalHom_apply

theorem universalHom_commutes {r : R} : universalHom f fS hf (numeratorHom r) = f r := by
  simp [numeratorHom_apply, universalHom_apply]
  -- 🎉 no goals
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
    -- Porting note: `simp only []` required for beta reductions
    simp only []
    -- ⊢ -r /ₒ s = -(r * t) /ₒ { val := ↑s * t, property := ht }
    rw [neg_mul_eq_neg_mul, ← OreLocalization.expand]
    -- 🎉 no goals
#align ore_localization.neg OreLocalization.neg

instance instNegOreLocalization : Neg R[S⁻¹] :=
  ⟨OreLocalization.neg⟩

@[simp]
protected theorem neg_def (r : R) (s : S) : -(r /ₒ s) = -r /ₒ s :=
  rfl
#align ore_localization.neg_def OreLocalization.neg_def

protected theorem add_left_neg (x : R[S⁻¹]) : -x + x = 0 := by
  induction' x using OreLocalization.ind with r s; simp
  -- ⊢ -(r /ₒ s) + r /ₒ s = 0
                                                   -- 🎉 no goals
#align ore_localization.add_left_neg OreLocalization.add_left_neg

instance ring : Ring R[S⁻¹] :=
  { OreLocalization.instSemiringOreLocalization,
    OreLocalization.instNegOreLocalization with
    add_left_neg := OreLocalization.add_left_neg }

open nonZeroDivisors

theorem numeratorHom_inj (hS : S ≤ R⁰) : Function.Injective (numeratorHom : R → R[S⁻¹]) :=
  fun r₁ r₂ h => by
  rw [numeratorHom_apply, numeratorHom_apply, oreDiv_eq_iff] at h
  -- ⊢ r₁ = r₂
  rcases h with ⟨u, v, h₁, h₂⟩
  -- ⊢ r₁ = r₂
  simp only [S.coe_one, one_mul] at h₂
  -- ⊢ r₁ = r₂
  rwa [← h₂, mul_cancel_right_mem_nonZeroDivisors (hS (SetLike.coe_mem u)), eq_comm] at h₁
  -- 🎉 no goals
#align ore_localization.numerator_hom_inj OreLocalization.numeratorHom_inj

theorem nontrivial_of_nonZeroDivisors [Nontrivial R] (hS : S ≤ R⁰) : Nontrivial R[S⁻¹] :=
  ⟨⟨0, 1, fun h => by
      rw [OreLocalization.one_def, OreLocalization.zero_def] at h
      -- ⊢ False
      apply nonZeroDivisors.coe_ne_zero 1 (numeratorHom_inj hS h).symm⟩⟩
      -- 🎉 no goals
#align ore_localization.nontrivial_of_non_zero_divisors OreLocalization.nontrivial_of_nonZeroDivisors

end Ring

noncomputable section DivisionRing

open nonZeroDivisors

open Classical

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
      -- ⊢ (fun r s => if hr : r = 0 then 0 else ↑s /ₒ { val := r, property := (_ : ∀ ( …
      by_cases hr : r = 0
      -- ⊢ (fun r s => if hr : r = 0 then 0 else ↑s /ₒ { val := r, property := (_ : ∀ ( …
      · simp [hr]
        -- 🎉 no goals
      · by_cases ht : t = 0
        -- ⊢ (fun r s => if hr : r = 0 then 0 else ↑s /ₒ { val := r, property := (_ : ∀ ( …
        · exfalso
          -- ⊢ False
          apply nonZeroDivisors.coe_ne_zero ⟨_, hst⟩
          -- ⊢ ↑{ val := ↑s * t, property := hst } = 0
          simp [ht, mul_zero]
          -- 🎉 no goals
        · simp only [hr, ht, dif_neg, not_false_iff, or_self_iff, mul_eq_zero]
          -- ⊢ ↑s /ₒ { val := r, property := (_ : ∀ (x : R), x * r = 0 → x = 0) } = ↑s * t  …
          apply OreLocalization.expand)
          -- 🎉 no goals
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
  -- ⊢ r /ₒ s * (r /ₒ s)⁻¹ = 1
  rw [OreLocalization.inv_def, OreLocalization.one_def]
  -- ⊢ (r /ₒ s * if hr : r = 0 then 0 else ↑s /ₒ { val := r, property := (_ : ∀ (x  …
  by_cases hr : r = 0
  -- ⊢ (r /ₒ s * if hr : r = 0 then 0 else ↑s /ₒ { val := r, property := (_ : ∀ (x  …
  · exfalso
    -- ⊢ False
    apply h
    -- ⊢ r /ₒ s = 0
    simp [hr]
    -- 🎉 no goals
  · simp [hr]
    -- ⊢ 1 = 1 /ₒ 1
    apply OreLocalization.div_eq_one'
    -- 🎉 no goals
#align ore_localization.mul_inv_cancel OreLocalization.mul_inv_cancel

protected theorem inv_zero : (0 : R[R⁰⁻¹])⁻¹ = 0 := by
  rw [OreLocalization.zero_def, OreLocalization.inv_def]
  -- ⊢ (if hr : 0 = 0 then 0 else ↑1 /ₒ { val := 0, property := (_ : ∀ (x : R), x * …
  simp
  -- 🎉 no goals
#align ore_localization.inv_zero OreLocalization.inv_zero

instance divisionRing : DivisionRing R[R⁰⁻¹] :=
  { OreLocalization.nontrivial,
    OreLocalization.inv',
    OreLocalization.ring with
    mul_inv_cancel := OreLocalization.mul_inv_cancel
    inv_zero := OreLocalization.inv_zero }

end DivisionRing

end OreLocalization
