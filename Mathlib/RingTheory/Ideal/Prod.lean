/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.RingTheory.Ideal.Operations

#align_import ring_theory.ideal.prod from "leanprover-community/mathlib"@"052f6013363326d50cb99c6939814a4b8eb7b301"

/-!
# Ideals in product rings

For commutative rings `R` and `S` and ideals `I ≤ R`, `J ≤ S`, we define `Ideal.prod I J` as the
product `I × J`, viewed as an ideal of `R × S`. In `ideal_prod_eq` we show that every ideal of
`R × S` is of this form.  Furthermore, we show that every prime ideal of `R × S` is of the form
`p × S` or `R × p`, where `p` is a prime ideal.
-/


universe u v

variable {R : Type u} {S : Type v} [Ring R] [Ring S] (I I' : Ideal R) (J J' : Ideal S)

namespace Ideal

/-- `I × J` as an ideal of `R × S`. -/
def prod : Ideal (R × S) where
  carrier := { x | x.fst ∈ I ∧ x.snd ∈ J }
  zero_mem' := by simp
                  -- 🎉 no goals
  add_mem' := by
    -- ⊢ (a₁, a₂) + (b₁, b₂) ∈ {x | x.fst ∈ I ∧ x.snd ∈ J}
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨ha₁, ha₂⟩ ⟨hb₁, hb₂⟩
    -- 🎉 no goals
    exact ⟨I.add_mem ha₁ hb₁, J.add_mem ha₂ hb₂⟩
  smul_mem' := by
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨hb₁, hb₂⟩
    -- ⊢ (a₁, a₂) • (b₁, b₂) ∈ { toAddSubsemigroup := { carrier := {x | x.fst ∈ I ∧ x …
    exact ⟨I.mul_mem_left _ hb₁, J.mul_mem_left _ hb₂⟩
    -- 🎉 no goals
#align ideal.prod Ideal.prod

@[simp]
theorem mem_prod {r : R} {s : S} : (⟨r, s⟩ : R × S) ∈ prod I J ↔ r ∈ I ∧ s ∈ J :=
  Iff.rfl
#align ideal.mem_prod Ideal.mem_prod

@[simp]
theorem prod_top_top : prod (⊤ : Ideal R) (⊤ : Ideal S) = ⊤ :=
  Ideal.ext <| by simp
                  -- 🎉 no goals
#align ideal.prod_top_top Ideal.prod_top_top

/-- Every ideal of the product ring is of the form `I × J`, where `I` and `J` can be explicitly
    given as the image under the projection maps. -/
theorem ideal_prod_eq (I : Ideal (R × S)) :
    I = Ideal.prod (map (RingHom.fst R S) I : Ideal R) (map (RingHom.snd R S) I) := by
  apply Ideal.ext
  -- ⊢ ∀ (x : R × S), x ∈ I ↔ x ∈ prod (map (RingHom.fst R S) I) (map (RingHom.snd  …
  rintro ⟨r, s⟩
  -- ⊢ (r, s) ∈ I ↔ (r, s) ∈ prod (map (RingHom.fst R S) I) (map (RingHom.snd R S) I)
  rw [mem_prod, mem_map_iff_of_surjective (RingHom.fst R S) Prod.fst_surjective,
    mem_map_iff_of_surjective (RingHom.snd R S) Prod.snd_surjective]
  refine' ⟨fun h => ⟨⟨_, ⟨h, rfl⟩⟩, ⟨_, ⟨h, rfl⟩⟩⟩, _⟩
  -- ⊢ ((∃ x, x ∈ I ∧ ↑(RingHom.fst R S) x = r) ∧ ∃ x, x ∈ I ∧ ↑(RingHom.snd R S) x …
  rintro ⟨⟨⟨r, s'⟩, ⟨h₁, rfl⟩⟩, ⟨⟨r', s⟩, ⟨h₂, rfl⟩⟩⟩
  -- ⊢ (↑(RingHom.fst R S) (r, s'), ↑(RingHom.snd R S) (r', s)) ∈ I
  simpa using I.add_mem (I.mul_mem_left (1, 0) h₁) (I.mul_mem_left (0, 1) h₂)
  -- 🎉 no goals
#align ideal.ideal_prod_eq Ideal.ideal_prod_eq

@[simp]
theorem map_fst_prod (I : Ideal R) (J : Ideal S) : map (RingHom.fst R S) (prod I J) = I := by
  ext x
  -- ⊢ x ∈ map (RingHom.fst R S) (prod I J) ↔ x ∈ I
  rw [mem_map_iff_of_surjective (RingHom.fst R S) Prod.fst_surjective]
  -- ⊢ (∃ x_1, x_1 ∈ prod I J ∧ ↑(RingHom.fst R S) x_1 = x) ↔ x ∈ I
  exact
    ⟨by
      rintro ⟨x, ⟨h, rfl⟩⟩
      exact h.1, fun h => ⟨⟨x, 0⟩, ⟨⟨h, Ideal.zero_mem _⟩, rfl⟩⟩⟩
#align ideal.map_fst_prod Ideal.map_fst_prod

@[simp]
theorem map_snd_prod (I : Ideal R) (J : Ideal S) : map (RingHom.snd R S) (prod I J) = J := by
  ext x
  -- ⊢ x ∈ map (RingHom.snd R S) (prod I J) ↔ x ∈ J
  rw [mem_map_iff_of_surjective (RingHom.snd R S) Prod.snd_surjective]
  -- ⊢ (∃ x_1, x_1 ∈ prod I J ∧ ↑(RingHom.snd R S) x_1 = x) ↔ x ∈ J
  exact
    ⟨by
      rintro ⟨x, ⟨h, rfl⟩⟩
      exact h.2, fun h => ⟨⟨0, x⟩, ⟨⟨Ideal.zero_mem _, h⟩, rfl⟩⟩⟩
#align ideal.map_snd_prod Ideal.map_snd_prod

@[simp]
theorem map_prodComm_prod :
    map ((RingEquiv.prodComm : R × S ≃+* S × R) : R × S →+* S × R) (prod I J) = prod J I := by
  refine' Trans.trans (ideal_prod_eq _) _
  -- ⊢ prod (map (RingHom.fst S R) (map (↑RingEquiv.prodComm) (prod I J))) (map (Ri …
  simp [map_map]
  -- 🎉 no goals
#align ideal.map_prod_comm_prod Ideal.map_prodComm_prod

/-- Ideals of `R × S` are in one-to-one correspondence with pairs of ideals of `R` and ideals of
    `S`. -/
def idealProdEquiv : Ideal (R × S) ≃ Ideal R × Ideal S
    where
  toFun I := ⟨map (RingHom.fst R S) I, map (RingHom.snd R S) I⟩
  invFun I := prod I.1 I.2
  left_inv I := (ideal_prod_eq I).symm
  right_inv := fun ⟨I, J⟩ => by simp
                                -- 🎉 no goals
#align ideal.ideal_prod_equiv Ideal.idealProdEquiv

@[simp]
theorem idealProdEquiv_symm_apply (I : Ideal R) (J : Ideal S) :
    idealProdEquiv.symm ⟨I, J⟩ = prod I J :=
  rfl
#align ideal.ideal_prod_equiv_symm_apply Ideal.idealProdEquiv_symm_apply

theorem prod.ext_iff {I I' : Ideal R} {J J' : Ideal S} :
    prod I J = prod I' J' ↔ I = I' ∧ J = J' := by
  simp only [← idealProdEquiv_symm_apply, idealProdEquiv.symm.injective.eq_iff, Prod.mk.inj_iff]
  -- 🎉 no goals
#align ideal.prod.ext_iff Ideal.prod.ext_iff

theorem isPrime_of_isPrime_prod_top {I : Ideal R} (h : (Ideal.prod I (⊤ : Ideal S)).IsPrime) :
    I.IsPrime := by
  constructor
  -- ⊢ I ≠ ⊤
  · contrapose! h
    -- ⊢ ¬IsPrime (prod I ⊤)
    rw [h, prod_top_top, isPrime_iff]
    -- ⊢ ¬(⊤ ≠ ⊤ ∧ ∀ {x y : R × S}, x * y ∈ ⊤ → x ∈ ⊤ ∨ y ∈ ⊤)
    simp [isPrime_iff, h]
    -- 🎉 no goals
  · intro x y hxy
    -- ⊢ x ∈ I ∨ y ∈ I
    have : (⟨x, 1⟩ : R × S) * ⟨y, 1⟩ ∈ prod I ⊤ := by
      rw [Prod.mk_mul_mk, mul_one, mem_prod]
      exact ⟨hxy, trivial⟩
    simpa using h.mem_or_mem this
    -- 🎉 no goals
#align ideal.is_prime_of_is_prime_prod_top Ideal.isPrime_of_isPrime_prod_top

theorem isPrime_of_isPrime_prod_top' {I : Ideal S} (h : (Ideal.prod (⊤ : Ideal R) I).IsPrime) :
    I.IsPrime := by
  apply @isPrime_of_isPrime_prod_top _ R
  -- ⊢ IsPrime (prod I ⊤)
  rw [← map_prodComm_prod]
  -- ⊢ IsPrime (map (↑RingEquiv.prodComm) (prod ⊤ I))
  exact map_isPrime_of_equiv _
  -- 🎉 no goals
#align ideal.is_prime_of_is_prime_prod_top' Ideal.isPrime_of_isPrime_prod_top'

theorem isPrime_ideal_prod_top {I : Ideal R} [h : I.IsPrime] : (prod I (⊤ : Ideal S)).IsPrime := by
  constructor
  -- ⊢ prod I ⊤ ≠ ⊤
  · rcases h with ⟨h, -⟩
    -- ⊢ prod I ⊤ ≠ ⊤
    contrapose! h
    -- ⊢ I = ⊤
    rw [← prod_top_top, prod.ext_iff] at h
    -- ⊢ I = ⊤
    exact h.1
    -- 🎉 no goals
  rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨h₁, _⟩
  -- ⊢ (r₁, s₁) ∈ prod I ⊤ ∨ (r₂, s₂) ∈ prod I ⊤
  cases' h.mem_or_mem h₁ with h h
  -- ⊢ (r₁, s₁) ∈ prod I ⊤ ∨ (r₂, s₂) ∈ prod I ⊤
  · exact Or.inl ⟨h, trivial⟩
    -- 🎉 no goals
  · exact Or.inr ⟨h, trivial⟩
    -- 🎉 no goals
#align ideal.is_prime_ideal_prod_top Ideal.isPrime_ideal_prod_top

theorem isPrime_ideal_prod_top' {I : Ideal S} [h : I.IsPrime] : (prod (⊤ : Ideal R) I).IsPrime := by
  letI : IsPrime (prod I (⊤ : Ideal R)) := isPrime_ideal_prod_top
  -- ⊢ IsPrime (prod ⊤ I)
  rw [← map_prodComm_prod]
  -- ⊢ IsPrime (map (↑RingEquiv.prodComm) (prod I ⊤))
  apply map_isPrime_of_equiv _
  -- 🎉 no goals
#align ideal.is_prime_ideal_prod_top' Ideal.isPrime_ideal_prod_top'

theorem ideal_prod_prime_aux {I : Ideal R} {J : Ideal S} :
    (Ideal.prod I J).IsPrime → I = ⊤ ∨ J = ⊤ := by
  contrapose!
  -- ⊢ I ≠ ⊤ ∧ J ≠ ⊤ → ¬IsPrime (prod I J)
  simp only [ne_top_iff_one, isPrime_iff, not_and, not_forall, not_or]
  -- ⊢ ¬1 ∈ I ∧ ¬1 ∈ J → ¬1 ∈ prod I J → ∃ x x_1 h, ¬x ∈ prod I J ∧ ¬x_1 ∈ prod I J
  exact fun ⟨hI, hJ⟩ _ => ⟨⟨0, 1⟩, ⟨1, 0⟩, by simp, by simp [hJ], by simp [hI]⟩
  -- 🎉 no goals
#align ideal.ideal_prod_prime_aux Ideal.ideal_prod_prime_aux

/-- Classification of prime ideals in product rings: the prime ideals of `R × S` are precisely the
    ideals of the form `p × S` or `R × p`, where `p` is a prime ideal of `R` or `S`. -/
theorem ideal_prod_prime (I : Ideal (R × S)) :
    I.IsPrime ↔
      (∃ p : Ideal R, p.IsPrime ∧ I = Ideal.prod p ⊤) ∨
        ∃ p : Ideal S, p.IsPrime ∧ I = Ideal.prod ⊤ p := by
  constructor
  -- ⊢ IsPrime I → (∃ p, IsPrime p ∧ I = prod p ⊤) ∨ ∃ p, IsPrime p ∧ I = prod ⊤ p
  · rw [ideal_prod_eq I]
    -- ⊢ IsPrime (prod (map (RingHom.fst R S) I) (map (RingHom.snd R S) I)) → (∃ p, I …
    intro hI
    -- ⊢ (∃ p, IsPrime p ∧ prod (map (RingHom.fst R S) I) (map (RingHom.snd R S) I) = …
    rcases ideal_prod_prime_aux hI with (h | h)
    -- ⊢ (∃ p, IsPrime p ∧ prod (map (RingHom.fst R S) I) (map (RingHom.snd R S) I) = …
    · right
      -- ⊢ ∃ p, IsPrime p ∧ prod (map (RingHom.fst R S) I) (map (RingHom.snd R S) I) =  …
      rw [h] at hI ⊢
      -- ⊢ ∃ p, IsPrime p ∧ prod ⊤ (map (RingHom.snd R S) I) = prod ⊤ p
      exact ⟨_, ⟨isPrime_of_isPrime_prod_top' hI, rfl⟩⟩
      -- 🎉 no goals
    · left
      -- ⊢ ∃ p, IsPrime p ∧ prod (map (RingHom.fst R S) I) (map (RingHom.snd R S) I) =  …
      rw [h] at hI ⊢
      -- ⊢ ∃ p, IsPrime p ∧ prod (map (RingHom.fst R S) I) ⊤ = prod p ⊤
      exact ⟨_, ⟨isPrime_of_isPrime_prod_top hI, rfl⟩⟩
      -- 🎉 no goals
  · rintro (⟨p, ⟨h, rfl⟩⟩ | ⟨p, ⟨h, rfl⟩⟩)
    -- ⊢ IsPrime (prod p ⊤)
    · exact isPrime_ideal_prod_top
      -- 🎉 no goals
    · exact isPrime_ideal_prod_top'
      -- 🎉 no goals
#align ideal.ideal_prod_prime Ideal.ideal_prod_prime

end Ideal
