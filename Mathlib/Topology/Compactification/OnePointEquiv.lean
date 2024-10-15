/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Compactification.OnePoint

/-!
# One-point compactification and projectivization

We construct a set-theoretic equivalence between
`OnePoint K` and the projectivization `ℙ K (Fin 2 → K)` for an arbitrary division ring `K`.

TODO: Add the extension of this equivalence to a homeomorphism in the case `K = ℝ`,
where `OnePoint ℝ` gets the topology of one-point compactification.


## Main definitions

* `divOnePoint`: Division on `K` taking values in `OnePoint K`. Notation: `÷`.
* `divSlope`: Lowering `divOnePoint` to a map `ℙ K (Fin 2 → K) → OnePoint K`.

## Main results

* `divSlope_equiv` proves that `ℙ K (Fin 2 → K) ≃ OnePoint K`.

## Tags

one-point extension, projectivization
-/

open scoped LinearAlgebra.Projectivization OnePoint
open Projectivization Classical

/-!
### Definition and basic properties

We define a division operation `divOnePoint`, with notation `÷`.
It takes inputs from a division ring `K` and outputs a value in `K ∪ {∞}`, i.e.,  `OnePoint K`.
We prove that `÷` preserves projective equivalence: `(c•a)÷(c•b)=a÷b`.
Hence `÷` projects down to a map `divSlope` from `ℙ K (Fin 2 → K)` to `OnePoint K`
that takes a line through the origin and returns its slope. For a vertical line
the slope is `∞`.
-/
variable {K : Type*}
/-- A modified division from a structure with `Zero` and `Div` to its
 `OnePoint` extension. With notation `÷` for `divOnePoint`,
  we have in particular that `1 ÷ 0 = ∞`. -/
noncomputable def divOnePoint [Zero K] [Inv K] [Mul K] (a : K) (r : K): OnePoint K :=
  if r ≠ 0 then r⁻¹ * a else ∞

/-- Uncurried version of `divOnePoint`, with nonzeroness assumption. -/
noncomputable def divOnePoint' [Zero K] [Inv K] [Mul K]
  (u : {v : Fin 2 → K // v ≠ 0}) : OnePoint K :=
  if u.1 1 ≠ 0 then some ((u.1 1)⁻¹ * u.1 0) else ∞

/-- Notation `÷` showing that `divOnePoint` is distinct from
 ordinary division `/`. -/
infix:50 " ÷ " => divOnePoint

/-- `divOnePoint` can be lifted to the projective line (see `divSlope`.) -/
lemma divOnePoint_lifts [DivisionRing K] (a b : {v : Fin 2 → K // v ≠ 0})
    (h : ∃ c : Kˣ, c • b.1 = a.1) :
    (a.1 0 ÷ a.1 1) = (b.1 0 ÷ b.1 1) := by
  obtain ⟨c,hc⟩ : ∃ c : Kˣ, (fun m : Kˣ ↦ m.1 • b.1) c = a.1 := h
  rw [← hc]
  simp only [divOnePoint, ne_eq, Fin.isValue, Pi.smul_apply, smul_eq_mul, ite_not]
  split_ifs with hbc hb hb
  · rfl
  · simp only [ne_eq, OnePoint.infty_ne_coe]
    exact hb <| (Units.mul_right_eq_zero c).mp hbc
  · rw [hb] at hbc
    simp at hbc
  · apply congrArg some
    simp [mul_assoc]

/-- Equivalence between the projective line and the one-point extension. -/
noncomputable def divSlope [DivisionRing K] (p : ℙ K (Fin 2 → K)) : OnePoint K :=
  Quotient.lift (fun u => divOnePoint (u.1 0) (u.1 1)) divOnePoint_lifts p

/-! ### Equivalence
We establish the equivalence between `OnePoint K` and `ℙ K (Fin 2 → K)` for a division ring `K`.
-/

/-- In a division ring, if `a₁ ≠ 0 ≠ b₁` then `(a₁ b₁⁻¹) (b₁ a₁⁻¹) = 1`. -/
lemma rev_div_assoc {K : Type*} [DivisionRing K] {a b : { v : Fin 2 → K // v ≠ 0 }}
    (ga : ¬a.1 1 = 0) (gb : ¬b.1 1 = 0) : a.1 1 * (b.1 1)⁻¹ * (b.1 1 * (a.1 1)⁻¹) = 1 := by
  nth_rewrite 1 [mul_assoc]
  nth_rewrite 2 [← mul_assoc]
  rw [inv_mul_cancel gb]
  simp only [ne_eq, Fin.isValue, one_mul]
  exact GroupWithZero.mul_inv_cancel (a.1 1) ga

/-- `divSlope` respects projective equivalence. -/
lemma divSlope_inj_lifted [DivisionRing K] (a b : {v : Fin 2 → K // v ≠ 0})
    (h : divSlope ⟦a⟧ = divSlope ⟦b⟧) : (⟦a⟧ : Quotient (projectivizationSetoid K _)) = ⟦b⟧ :=
  Quotient.sound <| by
  by_cases ga : a.1 1 = 0
  · by_cases gb : b.1 1 = 0
    · simp only [ne_eq, Decidable.not_not]
      have : a.1 0 ≠ 0 := fun hc => .elim <|a.2 <|funext fun j => by fin_cases j <;> simp [hc,ga]
      have : b.1 0 ≠ 0 := fun hc => .elim <|b.2 <|funext fun j => by fin_cases j <;> simp [hc,gb]
      use Units.mk ((a.1 0) / (b.1 0)) ((b.1 0) / (a.1 0)) (by field_simp) (by field_simp)
      apply List.ofFn_inj.mp
      simp only [List.ofFn_succ, Pi.smul_apply, Fin.succ_zero_eq_one]
      rw [ga, gb]
      field_simp
    · simp [divSlope, divOnePoint, ga, gb] at h
  · by_cases gb : b.1 1 = 0
    · simp [divSlope, divOnePoint, ga, gb] at h
    · use Units.mk (a.1 1 * (b.1 1)⁻¹) (b.1 1 * (a.1 1)⁻¹)
        (rev_div_assoc ga gb) (rev_div_assoc gb ga)
      ext s
      fin_cases s
      · simp only [divSlope, divOnePoint, ite_not, Quotient.lift_mk, smul_eq_mul, ga, gb] at h
        have h' : (a.1 1)⁻¹ * a.1 0  = (b.1 1)⁻¹ * b.1 0 := Option.some_injective K h
        simp only [ne_eq, Fin.isValue, Fin.zero_eta, Pi.smul_apply, Units.smul_mk_apply,
          smul_eq_mul]
        rw [mul_assoc]
        rw [← h']
        rw [← mul_assoc]
        simp only [Fin.isValue, ne_eq]
        field_simp at h' ⊢
      · simp [h, ga, gb]

/-- Over any division ring `K`, `divSlope` is injective. -/
lemma divSlope_injective [DivisionRing K] : Function.Injective (@divSlope K _) :=
  Quotient.ind (fun a ↦ Quotient.ind (divSlope_inj_lifted a))

/-- An inverse of `divSlope`. -/
def slope_inv [DivisionRing K] (p : OnePoint K) : ℙ K (Fin 2 → K) := match p with
|some t => mk' K ⟨![t, 1], by simp⟩
|∞      => mk' K ⟨![1, 0], by simp⟩


/-- `slope_inv` is an inverse of `divSlope`. -/
lemma divSlope_inv [DivisionRing K] : Function.LeftInverse (@divSlope K _) slope_inv := by
  intro a
  have g₀       : divOnePoint' ⟨![(1:K), 0], by simp⟩ =      ∞ := by simp [divOnePoint']
  have g₁ (t:K) : divOnePoint' ⟨![    t, 1], by simp⟩ = some t := by simp [divOnePoint']
  cases a with
  |none => exact g₀
  |some t => exact g₁ t

/-- `divSlope` is surjective. -/
lemma divSlope_surjective [DivisionRing K] : Function.Surjective (@divSlope K _) :=
  fun r ↦ ⟨slope_inv r, divSlope_inv r⟩

/-- An equivalence between the one-point extension of a division ring `K`
and the projective line over `K`. -/
noncomputable def divSlope_equiv [DivisionRing K] :
  OnePoint K ≃ ℙ K (Fin 2 → K) where
  toFun     := slope_inv
  invFun    := divSlope
  left_inv  := divSlope_inv
  right_inv := Function.rightInverse_of_injective_of_leftInverse
    divSlope_injective divSlope_inv
