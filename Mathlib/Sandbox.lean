module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-! # Sandbox: junk-value absNorm without `Infinite S` -/

public section

open Submodule UniqueFactorizationMonoid

variable {S : Type*} [CommRing S] [IsDedekindDomain S]

/-- The junk-value version: no `Infinite S`. -/
noncomputable def absNorm' : Ideal S →*₀ ℕ where
  toFun I := if I = ⊥ then 0 else cardQuot I
  map_mul' I J := by
    refine multiplicative_of_coprime (fun I ↦ if I = ⊥ then 0 else cardQuot I) I J (by simp)
      (fun {I J} hI ↦ ?_) (fun {I} i hI ↦ ?_) (fun {I J} hIJ ↦ ?_)
    · simp [Ideal.isUnit_iff.mp hI, Ideal.mul_top]
    · have : Ideal.IsPrime I := Ideal.isPrime_of_prime hI
      have h₀ : I ≠ ⊥ := hI.ne_zero
      have : I ^ i ≠ ⊥ := pow_ne_zero _ h₀
      simp only [if_neg h₀, if_neg this]
      exact cardQuot_pow_of_prime hI.ne_zero
    · by_cases hI : I = ⊥
      · subst hI
        have : IsUnit J := hIJ (Dvd.intro 0 (by simp)) dvd_rfl
        simp [Ideal.isUnit_iff.mp this]
      · by_cases hJ : J = ⊥
        · subst hJ
          have : IsUnit I := hIJ dvd_rfl (Dvd.intro 0 (by simp))
          simp [Ideal.isUnit_iff.mp this]
        · have : I * J ≠ ⊥ := mul_ne_zero hI hJ
          simp only [if_neg hI, if_neg hJ, if_neg this]
          exact cardQuot_mul_of_coprime <| Ideal.isCoprime_iff_sup_eq.mpr
            (Ideal.isUnit_iff.mp (hIJ (Ideal.dvd_iff_le.mpr le_sup_left)
              (Ideal.dvd_iff_le.mpr le_sup_right)))
  map_one' := by rw [Ideal.one_eq_top, if_neg (by simp), cardQuot_top]
  map_zero' := by simp

-- mathlib-review test: is `absNorm I = cardQuot I` provable for `I ≠ ⊥` with no `[Infinite S]`?
section AbsNormReview

variable {S : Type*} [CommRing S] [IsDedekindDomain S]

example {I : Ideal S} (hI : I ≠ ⊥) : Ideal.absNorm I = Submodule.cardQuot I := by
  simp [Ideal.absNorm, hI]

example {I : Ideal S} (hI : I ≠ ⊥) : Ideal.absNorm I = Submodule.cardQuot I :=
  ite_eq_right hI

end AbsNormReview

-- mathlib-review finding 3: is the `finite_or_infinite` split in
-- `absNorm_ne_zero_iff_mem_nonZeroDivisors'` dead scaffolding?
section Finding3

open scoped nonZeroDivisors

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Ring.HasFiniteQuotients S]

example {I : Ideal S} : Ideal.absNorm I ≠ 0 ↔ I ∈ (Ideal S)⁰ := by
  simp_rw [ne_eq, Ideal.absNorm_eq_zero_iff', mem_nonZeroDivisors_iff_ne_zero,
    Submodule.zero_eq_bot]

end Finding3

-- mathlib-review finding 4: `absNorm_mem` through `absNorm_of_ne_bot`, no finite/infinite split
section Finding4

variable {S : Type*} [CommRing S] [IsDedekindDomain S]

example (I : Ideal S) : ↑(Ideal.absNorm I) ∈ I := by
  obtain rfl | hI := eq_or_ne I ⊥
  · simp
  · rw [Ideal.absNorm_of_ne_bot hI, cardQuot, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast,
      Ideal.Quotient.index_eq_zero]

end Finding4

-- finding 6, second attempt: the ring quotient `S ⧸ I` and `S ⧸ I.toAddSubgroup` are only defeq
section Finding6b

variable {S : Type*} [CommRing S] [Ring.HasFiniteQuotients S]

example {I : Ideal S} (hI : I ≠ ⊥) : I.toAddSubgroup.FiniteIndex :=
  have := Ring.HasFiniteQuotients.finiteQuotient hI
  ⟨Nat.card_ne_zero.mpr ⟨⟨0⟩, ‹Finite (S ⧸ I)›⟩⟩

example {I : Ideal S} (hI : I ≠ ⊥) : I.toAddSubgroup.FiniteIndex := by
  have := Ring.HasFiniteQuotients.finiteQuotient hI
  exact ⟨Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstanceAs (Finite (S ⧸ I))⟩⟩

example {I : Ideal S} (hI : I ≠ ⊥) : I.toAddSubgroup.FiniteIndex := by
  have : Finite (S ⧸ I.toAddSubgroup) := Ring.HasFiniteQuotients.finiteQuotient hI
  exact AddSubgroup.finiteIndex_of_finite_quotient

end Finding6b

-- finding 6: resulting signatures
#check @Ideal.finiteIndex'
#check @Ideal.isFiniteRelIndex'
#check @Ideal.finiteIndex

-- mathlib-review finding 15b: golf `absNorm_ne_zero_iff`
section Finding15b

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Infinite S]

-- (1) eta-reduced
example (I : Ideal S) : Ideal.absNorm I ≠ 0 ↔ Finite (S ⧸ I) := by
  rw [Ideal.absNorm_eq_natCard]
  exact ⟨Nat.finite_of_card_ne_zero, fun h => Nat.card_ne_zero.mpr ⟨⟨0⟩, h⟩⟩

-- (2) the one-liner the reviewer suggested does NOT close it: it leaves
-- `Finite (S ⧸ I) → Nonempty (S ⧸ I)`
-- example (I : Ideal S) : Ideal.absNorm I ≠ 0 ↔ Finite (S ⧸ I) := by
--   simp [Ideal.absNorm_eq_natCard, Nat.card_ne_zero]

end Finding15b
