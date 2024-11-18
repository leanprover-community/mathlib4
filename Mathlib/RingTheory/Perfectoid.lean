import Mathlib.RingTheory.Perfection

/-!
# Perfectoid Rings and Perfectoid Fields
-/

open Valuation Valued

class PerfectoidField (K : Type u) {Γ : outParam Type*} [Field K] [LinearOrderedCommGroup Γ] [vK : Valued K Γ] [vK.v.RankOne] [CompleteSpace K] : Prop where
  exists_p_mem_span_pow_p : ∃ π : 𝒪[K], ¬ IsUnit π ∧ (p : 𝒪[K]) ∈ Ideal.span {π ^ p}
  exist_p_th_root : ∀ x : 𝒪[K]⧸Ideal.span {(p : 𝒪[K])}, ∃ y : 𝒪[K]⧸Ideal.span {(p : 𝒪[K])} , x = y ^ p
