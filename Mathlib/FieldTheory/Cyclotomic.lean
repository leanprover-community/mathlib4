/-
Copyright (c) 2024 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

theorem exists_isPrimitiveRoot_of_isSepClosed (n : ℕ) [IsSepClosed K] [NeZero (n : K)] :
    ∃ (ξ : K), IsPrimitiveRoot ξ n := by
  apply exists_isPrimitiveRoot_of_splits_cyclotomic
  apply IsSepClosed.splits_domain (Polynomial.cyclotomic n K)
  apply Polynomial.separable_cyclotomic

noncomputable
def cyclotomicCharacter (n : ℕ+) [IsSepClosure k K] [NeZero (n : K)] :
    (K ≃ₐ[k] K) →* (ZMod n)ˣ :=
  letI : IsSepClosed K := IsSepClosure.sep_closed k
  IsPrimitiveRoot.autToPow k (exists_isPrimitiveRoot_of_isSepClosed K n).choose_spec

lemma cyclotomicCharacter_spec (n : ℕ+) [IsSepClosure k K] [NeZero (n : K)]
    (ξ : Kˣ) (hξ : ξ ∈ rootsOfUnity n K) (σ : (K ≃ₐ[k] K)) :
    ξ ^ (cyclotomicCharacter k K n σ : ZMod n).val = σ ξ := by
  letI : IsSepClosed K := IsSepClosure.sep_closed k
  let hζ := exists_isPrimitiveRoot_of_isSepClosed K n |>.choose_spec
  let ζ' : Kˣ := hζ.toRootsOfUnity.val
  have hζ' : IsPrimitiveRoot ζ' n := IsPrimitiveRoot.coe_units_iff.mp hζ
  obtain ⟨i,_,rfl⟩ := hζ'.eq_pow_of_mem_rootsOfUnity hξ
  push_cast
  rw [σ.map_pow, ← pow_mul, mul_comm, pow_mul]
  congr 1
  exact IsPrimitiveRoot.autToPow_spec k hζ σ

lemma cyclotomicCharacter_unique (n : ℕ+) [IsSepClosure k K] [NeZero (n : K)]
    (χ : (K ≃ₐ[k] K) →* (ZMod n)ˣ)
    (hχ : ∀ (ξ : Kˣ) (_ : ξ ∈ rootsOfUnity n K) (σ : (K ≃ₐ[k] K)),
      ξ ^ (χ σ : ZMod n).val = σ ξ) :
    χ = cyclotomicCharacter k K n := by
  letI : IsSepClosed K := IsSepClosure.sep_closed k
  let hζ := exists_isPrimitiveRoot_of_isSepClosed K n |>.choose_spec
  let ζ' : Kˣ := hζ.toRootsOfUnity.val
  have hζ' : IsPrimitiveRoot ζ' n := IsPrimitiveRoot.coe_units_iff.mp hζ
  apply IsPrimitiveRoot.autToPow_unique
  intro σ
  apply hχ ζ'
  exact IsPrimitiveRoot.mem_rootsOfUnity hζ'
