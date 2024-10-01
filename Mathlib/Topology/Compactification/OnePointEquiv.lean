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
`OnePoint K` and the projectivization `ℙ K (Fin 2 → K)` for an arbitrary field `K`.

(This equivalence can be extended to a homeomorphism
in the case `K = ℝ`, where `OnePoint ℝ` gets the topology of one-point compactification.
This result is to be added in a different file.)

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
It takes inputs from a field `K` and outputs a value in `K ∪ {∞}`, i.e.,  `OnePoint K`.
We prove that `÷` preserves projective equivalence: `(c•a)÷(c•b)=a÷b`.
Hence `÷` projects down to a map `divSlope` from `ℙ K (Fin 2 → K)` to `OnePoint K`
that takes a line through the origin and returns its slope. For a vertical line
the slope is `∞`.
-/
variable {K : Type*}
/-- A modified division from a structure with `Zero` and `Div` to its
 `OnePoint` extension. With notation `÷` for `divOnePoint`,
  we have in particular that `1 ÷ 0 = ∞`. -/
noncomputable def divOnePoint [Zero K] [Div K] (a : K) (r : K): OnePoint K :=
  if r ≠ 0 then a / r else ∞

/-- Uncurried version of `divOnePoint`, with nonzeroness assumption. -/
noncomputable def divOnePoint' [Zero K] [Div K]
  (u : {v : Fin 2 → K // v ≠ 0}) : OnePoint K :=
  if u.1 1 ≠ 0 then some (u.1 0 / u.1 1) else ∞

/-- Notation `÷` showing that `divOnePoint` is distinct from
 ordinary division `/`. -/
infix:50 " ÷ " => divOnePoint

/-- `divOnePoint` can be lifted to the projective line (see `divSlope`.) -/
lemma divOnePoint_lifts [Field K] (a b : {v : Fin 2 → K // v ≠ 0})
    (h : ∃ c : Kˣ, (fun m : Kˣ ↦ m.1 • b.1) c = a.1) :
    (a.1 0 ÷ a.1 1) = (b.1 0 ÷ b.1 1) := by
  obtain ⟨c,hc⟩ := h
  rw [← hc]
  simp only [divOnePoint, ne_eq, Fin.isValue, Pi.smul_apply, ite_not]
  split_ifs with hbc hb hb
  · rfl
  · simp only [ne_eq, OnePoint.infty_ne_coe]
    exact hb <| (Units.mul_right_eq_zero c).mp hbc
  · rw [hb] at hbc
    simp at hbc
  · apply congrArg some
    field_simp
    ring

/-- Equivalence between the projective line and the one-point extension. -/
noncomputable def divSlope [Field K] (p : ℙ K (Fin 2 → K)) : OnePoint K :=
  Quotient.lift (fun u => divOnePoint (u.1 0) (u.1 1)) divOnePoint_lifts p

/-! ### Equivalence
We establish the equivalence between `OnePoint K` and `ℙ K (Fin 2 → K)` for a field `K`.
-/

/-- Extensionality for functions from `Fin 2`. -/
lemma funext_fin2 [Zero K] {a b : Fin 2 → K} (h₀ : a 0 = b 0) (h₁ : a 1 = b 1) : a = b :=
  funext <| fun j => by fin_cases j <;> simp[h₀,h₁]

local instance [DivisionRing K] : Setoid ({v : Fin 2 → K // v ≠ 0}) :=
  projectivizationSetoid K (Fin 2 → K)

/-- `divSlope` respects projective equivalence. -/
lemma divSlope_inj_lifted [Field K] (a b : {v : Fin 2 → K // v ≠ 0})
    (h : divSlope ⟦a⟧ = divSlope ⟦b⟧) : (⟦a⟧ : Quotient (projectivizationSetoid K _)) = ⟦b⟧ :=
  Quotient.sound <| by
  by_cases ga : a.1 1 = 0
  · by_cases gb : b.1 1 = 0
    · simp only [ne_eq, Decidable.not_not]
      have h₀ : a.1 0 ≠ 0 := fun hc => False.elim <| a.2 <|funext_fin2 hc ga
      have h₁ : b.1 0 ≠ 0 := fun hc => False.elim <| b.2 <|funext_fin2 hc gb
      use Units.mk ((a.1 0) / (b.1 0)) ((b.1 0) / (a.1 0)) (by field_simp) (by field_simp)
      apply List.ofFn_inj.mp
      simp only [List.ofFn_succ, Pi.smul_apply, Fin.succ_zero_eq_one]
      rw [ga, gb]
      field_simp
    · simp_all[divSlope, divOnePoint]
  · by_cases gb : b.1 1 = 0
    · simp_all[divSlope, divOnePoint]
    · use Units.mk (a.1 1 / b.1 1) (b.1 1 / a.1 1) (by field_simp) (by field_simp)
      ext s
      fin_cases s
      · simp_all only [divSlope, divOnePoint, ite_not, Quotient.lift_mk, smul_eq_mul]
        have h' : a.1 0 / a.1 1 = b.1 0 / b.1 1 := Option.some_injective K h
        field_simp at *
        rw [h', mul_comm]
      · simp_all

/-- Over any field `K`, `divSlope` is injective. -/
lemma divSlope_injective [Field K] : Function.Injective (@divSlope K _) :=
  Quotient.ind (fun a ↦ Quotient.ind (divSlope_inj_lifted a))

/-- An inverse of `divSlope`. -/
def slope_inv [DivisionRing K] (p : OnePoint K) : ℙ K (Fin 2 → K) := match p with
|some t => mk' K ⟨![t, 1], by simp⟩
|∞      => mk' K ⟨![1, 0], by simp⟩


/-- `slope_inv` is an inverse of `divSlope`. -/
lemma divSlope_inv [Field K] : Function.LeftInverse (@divSlope K _) slope_inv := by
  intro a
  have g₀       : divOnePoint' ⟨![(1:K), 0], by simp⟩ =      ∞ := by simp[divOnePoint']
  have g₁ (t:K) : divOnePoint' ⟨![    t, 1], by simp⟩ = some t := by simp[divOnePoint']
  cases a with
  |none => exact g₀
  |some t => exact g₁ t

/-- `divSlope` is surjective. -/
lemma divSlope_surjective [Field K]:
    Function.Surjective (@divSlope K _) :=
  fun r ↦ ⟨slope_inv r, divSlope_inv r⟩

/-- An equivalence between the one-point extension of a field `K`
and the projective line over `K`. -/
noncomputable def divSlope_equiv [Field K] :
  OnePoint K ≃ ℙ K (Fin 2 → K) where
  toFun     := slope_inv
  invFun    := divSlope
  left_inv  := divSlope_inv
  right_inv := Function.rightInverse_of_injective_of_leftInverse
    divSlope_injective divSlope_inv
