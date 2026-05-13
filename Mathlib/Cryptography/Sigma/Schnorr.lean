/-
Copyright (c) 2026 Jay Scambler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jay Scambler
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The Schnorr sigma protocol and signature scheme

This file formalizes the Schnorr identification scheme as a sigma protocol
over an abstract commutative group `G` of order `q`, and wraps it as a
non-interactive signature scheme via Fiat-Shamir. The exponent space
`Exp q := ZMod q` is the additive group of integers mod `q`; group
elements are exponentiated by `gpow x s := x ^ s.val`.

A sigma protocol is a three-message public-coin interactive proof
satisfying three properties: completeness, special soundness, and
honest-verifier zero-knowledge. We prove all three for the Schnorr
scheme. The signature scheme is a thin wrapper that derives the
challenge from a hash function `H : G → M → ZMod q` rather than from an
interactive verifier; correctness follows from the sigma-protocol
correctness theorem under a rename.

## Main results

* `Schnorr.correct`: the honest verifier always accepts the honest
  signer's transcript. (Completeness.)
* `Schnorr.specialSoundness`: from two accepting transcripts with the
  same commitment but distinct challenges, the witness `x` is recovered
  as `(s - s') / (c - c')`. (Special soundness; requires `q` prime so
  `c - c'` is invertible in `ZMod q`.)
* `Schnorr.hvzkAccepts`: the simulator `hvzkSim g y c s := g^s · (y^c)⁻¹`
  always produces accepting transcripts. (HVZK simulator correctness.
  The distributional statement is intentionally out of scope here.)
* `Schnorr.Signature.correct`: the Fiat-Shamir non-interactive
  signature scheme is correct, as a corollary of `Schnorr.correct`.

A concrete instantiation on `Multiplicative (ZMod q)` (a small toy
cyclic group of prime order `q`) is included as an `example` showing
the API typechecks.

## Auxiliary results

* `Schnorr.gpow_sub`: subtraction in `ZMod q` corresponds to group
  division when `Fintype.card G = q`.
* `Schnorr.gpow_mul`: iterated exponentiation collapses to multiplication
  in `ZMod q` under the same hypothesis.

These auxiliary lemmas are bundled here rather than placed in a more
general location because the surrounding `gpow` API is itself local to
the cryptographic setting; in a more general future setting where
`ZMod q`-graded group actions are formalized, both lemmas become
instances of the action's identities.

## Design notes

The exponent space is `Exp q := ZMod q` (an abbreviation) rather than
`Fin q` or `ℕ`, because the natural arithmetic on the prover's response
and the verifier's challenge is `ZMod q` arithmetic.

`gpow x s := x ^ s.val` is the natural way to lift a `ZMod q` exponent
to a group operation, but it only respects the `ZMod q` arithmetic when
the group has exponent dividing `q`. This is the content of `gpow_sub`
and `gpow_mul`, which are needed for the soundness proof. The
auxiliary lemmas could be subsumed by a future `ZMod q`-graded group
action framework; until that lands, we bundle them locally.

## References

* C. P. Schnorr, *Efficient Identification and Signatures for Smart
  Cards*, Advances in Cryptology - CRYPTO '89, Lecture Notes in
  Computer Science vol. 435, 1990. (Original identification scheme.)
* C. P. Schnorr, *Efficient Signature Generation by Smart Cards*,
  Journal of Cryptology vol. 4 no. 3, 1991. (Signature scheme via
  Fiat-Shamir.)
* D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*,
  Chapter 19 (Sigma protocols). Free online at
  <https://toc.cryptobook.us>.

## Tags

cryptography, schnorr, sigma protocol, identification scheme,
signature scheme, discrete logarithm
-/

@[expose] public section

namespace Schnorr

/-- The exponent space for a group of order `q`. -/
abbrev Exp (q : ℕ) := ZMod q

/-- Exponentiation of a group element by a `ZMod q` value, via the
underlying natural number representative `s.val ∈ {0, ..., q-1}`.

The group law on `Exp q` (addition modulo `q`) corresponds to
multiplication in the ambient group exactly when the group has order
`q`. The lemmas `gpow_sub` and `gpow_mul` below witness this
correspondence under the cardinality hypothesis `Fintype.card G = q`,
which forces `g ^ q = 1` via `pow_card_eq_one`. -/
def gpow {G : Type*} [CommGroup G] {q : ℕ} (x : G) (s : Exp q) : G :=
  x ^ s.val

/-- A Schnorr transcript: a commitment `R : G` and a response `s : ZMod q`.

The challenge `c` is supplied externally — in the interactive sigma
protocol by the verifier, in the non-interactive Fiat-Shamir variant by
a hash function `H : G → M → ZMod q`. -/
structure Sig (G : Type*) (q : ℕ) where
  commitment : G
  response : Exp q

/-- The honest signer's algorithm. Given a private key `x`, ephemeral
randomness `k`, and a message `m`, produces `(g^k, k + c · x)` where
`c = H(g^k, m)`. -/
def honestSig {G : Type*} [CommGroup G] {q : ℕ} {M : Type*}
    (g : G) (H : G → M → Exp q) (x k : Exp q) (m : M) : Sig G q :=
  let R := gpow g k
  let c := H R m
  ⟨R, k + c * x⟩

/-- The honest verifier's check (non-interactive form, with the
challenge derived from a hash `H`): `g^s = R · y^c`. -/
def verifyHash {G : Type*} [CommGroup G] {q : ℕ} {M : Type*}
    (g : G) (H : G → M → Exp q) (y : G) (m : M) (sig : Sig G q) : Prop :=
  gpow g sig.response = sig.commitment * gpow y (H sig.commitment m)

/-- The honest verifier's check (interactive form, with the challenge
given explicitly): `g^s = R · y^c`. -/
def sigmaVerify {G : Type*} [CommGroup G] {q : ℕ}
    (g y R : G) (c s : Exp q) : Prop :=
  gpow g s = R * gpow y c

/-- The HVZK simulator: given a public key `y`, challenge `c`, and
response `s`, produces the commitment `R = g^s · (y^c)⁻¹` that makes
the transcript `(R, c, s)` accept. -/
def hvzkSim {G : Type*} [CommGroup G] {q : ℕ}
    (g y : G) (c s : Exp q) : G :=
  gpow g s * (gpow y c)⁻¹

/-! ### Auxiliary identities -/

/-- `gpow_sub`: subtraction in `Exp q` corresponds to group division
when the group has order `q`. -/
theorem gpow_sub {G : Type*} [CommGroup G] [Fintype G] {q : ℕ} [NeZero q]
    (hcard : Fintype.card G = q) (g : G) (a b : Exp q) :
    gpow g (a - b) = gpow g a * (gpow g b)⁻¹ := by
  unfold gpow
  have hg : g ^ q = 1 := by rw [← hcard]; exact pow_card_eq_one
  have hmod : ∀ n : ℕ, g ^ n = g ^ (n % q) := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n q]
    rw [pow_add, pow_mul, hg, one_pow, one_mul]
  have hsum_mod : ((a - b).val + b.val) % q = a.val := by
    rw [← ZMod.val_add, sub_add_cancel]
  rw [eq_mul_inv_iff_mul_eq, ← pow_add, hmod ((a - b).val + b.val), hsum_mod]

/-- `gpow_mul`: iterated exponentiation collapses to multiplication in
`Exp q` when the group has order `q`. -/
theorem gpow_mul {G : Type*} [CommGroup G] [Fintype G] {q : ℕ} [NeZero q]
    (hcard : Fintype.card G = q) (g : G) (a b : Exp q) :
    gpow (gpow g a) b = gpow g (a * b) := by
  unfold gpow
  have hg : g ^ q = 1 := by rw [← hcard]; exact pow_card_eq_one
  have hmod : ∀ n : ℕ, g ^ n = g ^ (n % q) := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n q]
    rw [pow_add, pow_mul, hg, one_pow, one_mul]
  rw [← pow_mul, ZMod.val_mul, ← hmod]

/-! ### Completeness -/

/-- **Schnorr sigma protocol completeness.**

The honest verifier always accepts a transcript produced by the honest
signer. -/
theorem correct {G : Type*} [CommGroup G] [Fintype G] {q : ℕ} {M : Type*}
    (hcard : Fintype.card G = q) (g : G) (H : G → M → Exp q)
    (x k : Exp q) (m : M) :
    verifyHash g H (gpow g x) m (honestSig g H x k m) := by
  have hq_pos : 0 < q := by
    rw [← hcard]; exact Fintype.card_pos_iff.mpr ⟨1⟩
  haveI : NeZero q := ⟨hq_pos.ne'⟩
  have hg : g ^ q = 1 := by rw [← hcard]; exact pow_card_eq_one
  have hmod : ∀ n : ℕ, g ^ (n % q) = g ^ n := by
    intro n
    conv_rhs => rw [← Nat.div_add_mod n q]
    rw [pow_add, pow_mul, hg, one_pow, one_mul]
  change g ^ (k + H (g ^ k.val) m * x).val
      = g ^ k.val * (g ^ x.val) ^ (H (g ^ k.val) m).val
  set c := H (g ^ k.val) m
  rw [ZMod.val_add, hmod, pow_add, ZMod.val_mul, hmod,
      Nat.mul_comm c.val x.val, pow_mul]

/-! ### Special soundness -/

/-- Helper for `specialSoundness`: from two accepting transcripts
sharing the commitment `R`, the commitment cancels and we are left
with `g^s · (g^s')⁻¹ = y^c · (y^c')⁻¹` (an equation in `G` alone,
with `R` no longer appearing). -/
private theorem cancel_R {G : Type*} [CommGroup G] {q : ℕ}
    (g y R : G) (c c' s s' : Exp q)
    (h1 : sigmaVerify g y R c s) (h2 : sigmaVerify g y R c' s') :
    g ^ s.val * (g ^ s'.val)⁻¹ = y ^ c.val * (y ^ c'.val)⁻¹ := by
  unfold sigmaVerify gpow at h1 h2
  rw [h1, h2, ← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]

/-- Helper for `specialSoundness`: given the cancelled equation and
`c ≠ c'` (so `c - c'` is a unit in the field `ZMod q`), extract the
witness as `y = g^((s - s') / (c - c'))` by raising both sides of the
cancelled equation to the power `(c - c')⁻¹`. -/
private theorem extract_witness
    {G : Type*} [CommGroup G] [Fintype G] {q : ℕ} [Fact q.Prime]
    (hcard : Fintype.card G = q) (g y : G)
    (c c' s s' : Exp q) (hc_ne : c ≠ c')
    (hcanceled : g ^ s.val * (g ^ s'.val)⁻¹ = y ^ c.val * (y ^ c'.val)⁻¹) :
    y = gpow g ((s - s') / (c - c')) := by
  have hprime : Nat.Prime q := Fact.out
  have hq2 : 2 ≤ q := hprime.two_le
  haveI : NeZero q := ⟨by omega⟩
  haveI : Fact (1 < q) := ⟨by omega⟩
  have hkey : gpow g (s - s') = gpow y (c - c') := by
    rw [gpow_sub hcard g s s', gpow_sub hcard y c c']
    exact hcanceled
  have hδ : c - c' ≠ 0 := sub_ne_zero.mpr hc_ne
  have hraise :
      gpow g ((s - s') * (c - c')⁻¹) = gpow y ((c - c') * (c - c')⁻¹) := by
    rw [← gpow_mul hcard g (s - s') (c - c')⁻¹,
        ← gpow_mul hcard y (c - c') (c - c')⁻¹, hkey]
  rw [mul_inv_cancel₀ hδ] at hraise
  have hy1 : gpow y (1 : Exp q) = y := by
    change y ^ (1 : ZMod q).val = y
    rw [ZMod.val_one, pow_one]
  rw [hy1] at hraise
  rw [div_eq_mul_inv]
  exact hraise.symm

/-- **Schnorr special soundness.**

Given two accepting sigma-protocol transcripts `(R, c, s)` and
`(R, c', s')` that share the commitment `R` but have distinct challenges
`c ≠ c'`, the discrete log of `y` relative to `g` is
`x = (s - s') / (c - c')`.

Requires `q` prime so that `c - c'` is invertible in `ZMod q`. -/
theorem specialSoundness
    {G : Type*} [CommGroup G] [Fintype G] {q : ℕ} [Fact q.Prime]
    (hcard : Fintype.card G = q) (g y R : G)
    (c c' s s' : Exp q) (hc_ne : c ≠ c')
    (h1 : sigmaVerify g y R c s) (h2 : sigmaVerify g y R c' s') :
    y = gpow g ((s - s') / (c - c')) :=
  extract_witness hcard g y c c' s s' hc_ne (cancel_R g y R c c' s s' h1 h2)

/-! ### Honest-verifier zero-knowledge -/

/-- **Schnorr HVZK simulator correctness.**

For any challenge `c` and response `s`, the simulator
`hvzkSim g y c s := g^s · (y^c)⁻¹` produces a commitment that makes
the transcript `(R, c, s)` accept.

This is the structural-correctness half of HVZK. The full
honest-verifier zero-knowledge statement also requires showing that the
simulator's output distribution matches the honest signer's; that
distributional statement is intentionally out of scope here. -/
theorem hvzkAccepts {G : Type*} [CommGroup G] {q : ℕ}
    (g y : G) (c s : Exp q) :
    sigmaVerify g y (hvzkSim g y c s) c s := by
  unfold sigmaVerify hvzkSim
  rw [inv_mul_cancel_right]

end Schnorr

/-! ## The Schnorr signature scheme (Fiat-Shamir form)

A thin wrapper exposing the sigma protocol as a non-interactive
signature scheme. The challenge is derived by a hash
`H : G → M → ZMod q` rather than chosen by an interactive verifier;
otherwise the algorithms and the correctness theorem coincide with the
sigma-protocol ones above.

This packaging matches how the scheme is used in practice (signing
messages, not running interactive identification) without duplicating
proofs: `Signature.correct` is `Schnorr.correct` under a rename. -/

namespace Schnorr.Signature

/-- A Schnorr secret key is an element of `ZMod q`. -/
abbrev SecretKey (q : ℕ) := Schnorr.Exp q

/-- A Schnorr public key is a group element (`g^x` for some secret key
`x`). -/
abbrev PublicKey (G : Type*) := G

/-- Public-key derivation: `pk = g^sk`. -/
def keyGen {G : Type*} [CommGroup G] {q : ℕ}
    (g : G) (sk : SecretKey q) : PublicKey G :=
  Schnorr.gpow g sk

/-- Signing: produce `(g^k, k + H(g^k, m) · sk)`. -/
def sign {G : Type*} [CommGroup G] {q : ℕ} {M : Type*}
    (g : G) (H : G → M → Schnorr.Exp q)
    (sk k : SecretKey q) (m : M) : Schnorr.Sig G q :=
  Schnorr.honestSig g H sk k m

/-- Verification: check `g^s = R · pk^c` where `c = H(R, m)`. -/
def verify {G : Type*} [CommGroup G] {q : ℕ} {M : Type*}
    (g : G) (pk : PublicKey G) (H : G → M → Schnorr.Exp q)
    (m : M) (sig : Schnorr.Sig G q) : Prop :=
  Schnorr.verifyHash g H pk m sig

/-- **Schnorr signature scheme correctness.**

For any secret key `sk`, ephemeral randomness `k`, and message `m`, the
verifier accepts the honest signer's signature. -/
theorem correct {G : Type*} [CommGroup G] [Fintype G] {q : ℕ} {M : Type*}
    (hcard : Fintype.card G = q) (g : G)
    (H : G → M → Schnorr.Exp q) (sk k : SecretKey q) (m : M) :
    verify g (keyGen g sk) H m (sign g H sk k m) :=
  Schnorr.correct hcard g H sk k m

/-! ### Concrete instantiation on `Multiplicative (ZMod q)`

A pedagogical demonstration that the abstract API instantiates cleanly.
For prime `q`, `Multiplicative (ZMod q)` is a cyclic group of order
`q`, satisfying the `Fintype.card G = q` hypothesis of `correct`.

This is a toy instantiation: the discrete log problem in
`Multiplicative (ZMod q)` is trivial (linear modular arithmetic), so
the security claims do not hold. Real instantiations use prime-order
subgroups of `(ZMod p)ˣ` (Schnorr groups) or elliptic-curve points. -/

/-- Schnorr's signature scheme instantiated on `Multiplicative (ZMod q)`
for prime `q`. The verifier accepts honest signatures, by `correct`. -/
example (q : ℕ) [Fact q.Prime] (sk k : Schnorr.Exp q)
    (H : Multiplicative (ZMod q) → Unit → Schnorr.Exp q) :
    let g : Multiplicative (ZMod q) := Multiplicative.ofAdd 1
    verify g (keyGen g sk) H () (sign g H sk k ()) := by
  haveI : NeZero q := ⟨(Fact.out (p := q.Prime)).ne_zero⟩
  apply correct
  rw [Fintype.card_multiplicative, ZMod.card]

end Schnorr.Signature
