/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.RingTheory.PicardGroup
public meta import Mathlib.Tactic.DeriveFintype

/-!
# An invertible semimodule over a finite commutative semiring with lower cardinality

This file presents an example of an invertible semimodule with 6 elements over a finite
commutative semiring with 7 elements, from a working note by Sixuan Gu and Wei Qi
(private communication).
-/

namespace Counterexample.FiniteInvertibleSemimodule

set_option backward.isDefEq.respectTransparency false in -- for deriving Fintype
/-- The underlying type of the seven-element commutative semiring. -/
inductive R₇ : Type | zero | ε | g | a | b | one | ω deriving Fintype, DecidableEq

namespace R₇

/-- The addition on the seven-element commutative semiring. -/
def add : R₇ → R₇ → R₇
  | zero, r => r
  | r, zero => r
  | ω, _ => ω
  | _, ω => ω
  | g, g => g
  | g, _ => ω
  | _, g => ω
  | one, _ => one
  | _, one => one
  | ε, ε => ε
  | ε, r => r
  | r, ε => r
  | a, a => a
  | a, b => one
  | b, a => one
  | b, b => b

/-- The multiplication on the seven-element semiring. -/
def mul : R₇ → R₇ → R₇
  | one, r => r
  | r, one => r
  | zero, _ => zero
  | _, zero => zero
  | ω, _ => ω
  | _, ω => ω
  | g, g => ε
  | g, _ => g
  | _, g => g
  | ε, _ => ε
  | _, ε => ε
  | a, a => a
  | a, b => ε
  | b, a => ε
  | b, b => b

instance : Zero R₇ where zero := zero
instance : Add R₇ where add := add

instance : CommSemiring R₇ where
  add_assoc := by rintro (_|_) (_|_) (_|_) <;> rfl
  zero_add := by rintro (_|_) <;> rfl
  add_zero := by rintro (_|_) <;> rfl
  nsmul := nsmulRec
  add_comm := by rintro (_|_) (_|_) <;> rfl
  mul := mul
  mul_assoc := by rintro (_|_) (_|_) (_|_) <;> rfl
  one := one
  one_mul := by rintro (_|_) <;> rfl
  mul_one := by rintro (_|_) <;> rfl
  mul_comm := by rintro (_|_) (_|_) <;> rfl
  zero_mul := by rintro (_|_) <;> rfl
  mul_zero := by rintro (_|_) <;> rfl
  left_distrib := by rintro (_|_) (_|_) (_|_) <;> rfl
  right_distrib := by rintro (_|_) (_|_) (_|_) <;> rfl

end R₇

open R₇

/-- The six-element semimodule over the seven-element commutative semiring. -/
def M₆ : Submodule R₇ (R₇ × R₇) where
  carrier := {(0,0),(ε,g),(g,ε),(a,g),(g,b),(ω,ω)}
  add_mem' := by rintro _ _ (rfl|rfl|rfl|rfl|rfl|rfl) (rfl|rfl|rfl|rfl|rfl|rfl) <;> tauto
  zero_mem' := .inl rfl
  smul_mem' := by rintro (_|_) _ (rfl|rfl|rfl|rfl|rfl|rfl) <;> tauto

theorem M₆_eq_finset : SetLike.coe M₆ = ({(0,0),(ε,g),(g,ε),(a,g),(g,b),(ω,ω)} : Finset _) := by
  ext; simp [M₆, ← Submodule.carrier_eq_coe]

/-- The element (a,g) ∈ M₆. -/
def c₁ : M₆ := ⟨(a,g), .inr <| .inr <| .inr <| .inl rfl⟩

/-- The element (g,b) ∈ M₆. -/
def c₂ : M₆ := ⟨(g,b), .inr <| .inr <| .inr <| .inr <| .inl rfl⟩

theorem gc₁_eq_ac₂ : g • c₁ = a • c₂ := rfl
theorem gc₂_eq_bc₁ : g • c₂ = b • c₁ := rfl

open Submodule in
theorem span_c₁_c₂ : span R₇ {c₁, c₂} = ⊤ := top_unique <| by
  rintro ⟨_, (rfl|rfl|rfl|rfl|rfl|rfl)⟩ _
  · exact zero_mem _
  · exact smul_mem _ (x := c₁) ε (subset_span <| .inl rfl)
  · exact smul_mem _ (x := c₁) g (subset_span <| .inl rfl)
  · exact subset_span (.inl rfl)
  · exact subset_span (.inr rfl)
  · exact smul_mem _ (x := c₁) ω (subset_span <| .inl rfl)

open TensorProduct

/-- The forward direction of the isomorphism between M₆ ⊗ M₆ and R₇. -/
def linearMap : M₆ ⊗[R₇] M₆ →ₗ[R₇] R₇ :=
  TensorProduct.lift
  { toFun m₁ := { toFun m₂ := m₁.1.1 * m₂.1.1 + m₁.1.2 * m₂.1.2,
                  map_add' _ _ := by simp [mul_add, add_add_add_comm]
                  map_smul' _ _ := by simp [mul_add, mul_left_comm] }
    map_add' _ _ := LinearMap.ext fun _ ↦ by simp [add_mul, add_add_add_comm]
    map_smul' _ _ := LinearMap.ext fun _ ↦ by simp [mul_add, mul_assoc] }

/-- The element that maps to 1 under `linearMap`. -/
def Θ : M₆ ⊗[R₇] M₆ := c₁ ⊗ₜ c₁ + c₂ ⊗ₜ c₂

/-- The isomorphism between -/
def linearEquiv : M₆ ⊗[R₇] M₆ ≃ₗ[R₇] R₇ :=
  .ofLinearMap (σ₁₂ := .id _) linearMap (.toSpanSingleton R₇ _ (c₁ ⊗ₜ c₁ + c₂ ⊗ₜ c₂))
  (LinearMap.ext_ring rfl) <| ext <| LinearMap.ext_on span_c₁_c₂ <| by
    rintro _ (rfl|rfl) <;> refine LinearMap.ext_on span_c₁_c₂ ?_ <;> rintro _ (rfl|rfl) <;>
      simp only [LinearMap.compr₂ₛₗ_apply, mk_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.toSpanSingleton_apply, smul_add, LinearMap.compr₂ₛₗ_id]
    · rw [show linearMap (c₁ ⊗ₜ c₁) = a from rfl,
        smul_tmul', ← tmul_smul, ← gc₁_eq_ac₂, ← smul_tmul, ← add_tmul]; rfl
    · rw [show linearMap (c₁ ⊗ₜ c₂) = g from rfl,
        ← tmul_smul, smul_tmul', gc₁_eq_ac₂, ← smul_tmul, ← add_tmul]; rfl
    · rw [show linearMap (c₂ ⊗ₜ c₁) = g from rfl,
        smul_tmul', ← tmul_smul, gc₂_eq_bc₁, ← smul_tmul, ← add_tmul]; rfl
    · rw [show linearMap (c₂ ⊗ₜ c₂) = b from rfl,
        ← tmul_smul, smul_tmul', ← gc₂_eq_bc₁, ← smul_tmul, ← add_tmul]; rfl

instance : Module.Invertible R₇ M₆ := .left linearEquiv

theorem cardinalMk_R₇ : Cardinal.mk R₇ = 7 := Cardinal.mk_fintype _
theorem cardinalMk_M₆ : Cardinal.mk M₆ = 6 :=
  show Cardinal.mk (SetLike.coe M₆) = 6 by simp [M₆_eq_finset]

instance : Nontrivial (CommRing.Pic R₇) where
  exists_pair_ne := ⟨.mk _ M₆, 1, fun h ↦ by
    obtain ⟨e⟩ := CommRing.Pic.mk_eq_one_iff.mp h
    have := e.cardinal_eq
    rw [cardinalMk_R₇, cardinalMk_M₆] at this
    simp at this⟩

/-- It is not the case that every invertible semimodule over a finite commutative semiring has
the same cardinality as the semiring. -/
theorem not_cardinalMk_eq_of_moduleInvertible :
    ¬ ∀ (R M : Type) [CommSemiring R] [AddCommMonoid M] [Module R M] [Module.Invertible R M]
      [Finite R] [Finite M], Cardinal.mk R = Cardinal.mk M :=
  fun h ↦ have := h R₇ M₆; by rw [cardinalMk_R₇, cardinalMk_M₆] at this; simp at this

/-- It is not the case that every finite commutative semiring has trivial Picard group. -/
theorem not_subsingleton_Pic_of_finite :
    ¬ ∀ (R : Type) [CommSemiring R] [Finite R], Subsingleton (CommRing.Pic R) :=
  fun h ↦ not_subsingleton _ (h R₇)

/-- It is not the case that every semi-local commutative semiring has trivial Picard group. -/
theorem not_subsingleton_Pic_of_finite_maximalSpectrum :
    ¬ ∀ (R : Type) [CommSemiring R] [Finite (MaximalSpectrum R)], Subsingleton (CommRing.Pic R) :=
  fun h ↦ not_subsingleton _ (h R₇)

end Counterexample.FiniteInvertibleSemimodule

set_option linter.privateModule false
