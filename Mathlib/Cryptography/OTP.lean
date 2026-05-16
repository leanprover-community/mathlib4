/-
Copyright (c) 2026 Jay Scambler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jay Scambler
-/
module

public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Data.Fintype.Basic

/-!
# The one-time pad

Shannon's one-time pad (1949). Plaintext, key, and ciphertext live in
a finite abelian group `G`; encryption is `c := m + k`, decryption
`m := c - k`. Under a uniformly random key, the ciphertext
distribution is uniform on `G`, independent of the plaintext.

## Main results

* `OTP.correct`: `decrypt k (encrypt k m) = m`.
* `OTP.perfect_secrecy`: for any `m₀, m₁`, the ciphertext
  distributions under a uniform key are equal (both
  `PMF.uniformOfFintype G`).

## References

* Claude E. Shannon, "Communication theory of secrecy systems",
  *Bell System Technical Journal* 28(4): 656-715, 1949.
-/

namespace OTP

@[expose] public section

/-- One-time pad encryption: `c = m + k`. -/
def encrypt {G : Type*} [AddCommGroup G] (k m : G) : G := m + k

/-- One-time pad decryption: `m = c - k`. -/
def decrypt {G : Type*} [AddCommGroup G] (k c : G) : G := c - k

/-- Correctness: decrypting an honest encryption recovers the message. -/
theorem correct {G : Type*} [AddCommGroup G] (k m : G) :
    decrypt k (encrypt k m) = m := by
  unfold decrypt encrypt
  abel

/-- Perfect secrecy: the ciphertext distribution under a uniform key
is independent of the plaintext. -/
theorem perfect_secrecy {G : Type*} [AddCommGroup G] [Fintype G] [Nonempty G]
    (m₀ m₁ : G) :
    (PMF.uniformOfFintype G).map (encrypt · m₀)
      = (PMF.uniformOfFintype G).map (encrypt · m₁) := by
  have heq : ∀ (m : G),
      (PMF.uniformOfFintype G).map (encrypt · m) = PMF.uniformOfFintype G := by
    intro m
    let shift : G ≃ G := Equiv.addLeft m
    have hmap : (fun k : G => encrypt k m) = shift := by
      funext k; rfl
    rw [hmap]
    apply PMF.ext
    intro c
    rw [PMF.map_apply, PMF.uniformOfFintype_apply]
    rw [tsum_eq_single (shift.symm c)]
    · simp [PMF.uniformOfFintype_apply, shift]
    · intro b hb
      have hne : shift b ≠ c :=
        fun heq => hb (by simp [← heq, Equiv.symm_apply_apply])
      simp [Ne.symm hne]
  rw [heq m₀, heq m₁]

end

end OTP
