/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
module

public import Mathlib.RingTheory.WittVector.InitTail
public import Mathlib.RingTheory.Ideal.Maps
import Batteries.Tactic.Congr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.RingTheory.Ideal.Lattice
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!

# Truncated Witt vectors

The ring of truncated Witt vectors (of length `n`) is a quotient of the ring of Witt vectors.
It retains the first `n` coefficients of each Witt vector.
In this file, we set up the basic quotient API for this ring.

The ring of Witt vectors is the projective limit of all the rings of truncated Witt vectors.

## Main declarations

- `TruncatedWittVector`: the underlying type of the ring of truncated Witt vectors
- `TruncatedWittVector.instCommRing`: the ring structure on truncated Witt vectors
- `WittVector.truncate`: the quotient homomorphism that truncates a Witt vector,
  to obtain a truncated Witt vector
- `TruncatedWittVector.truncate`: the homomorphism that truncates
  a truncated Witt vector of length `n` to one of length `m` (for some `m ≤ n`)
- `WittVector.lift`: the unique ring homomorphism into the ring of Witt vectors
  that is compatible with a family of ring homomorphisms to the truncated Witt vectors:
  this realizes the ring of Witt vectors as projective limit of the rings of truncated Witt vectors

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

@[expose] public section


open Function (Injective Surjective)

noncomputable section

variable {p : ℕ} (n : ℕ) (R : Type*)

local notation "𝕎" => WittVector p -- type as `\bbW`

/-- A truncated Witt vector over `R` is a vector of elements of `R`,
i.e., the first `n` coefficients of a Witt vector.
We will define operations on this type that are compatible with the (untruncated) Witt
vector operations.

`TruncatedWittVector p n R` takes a parameter `p : ℕ` that is not used in the definition.
In practice, this number `p` is assumed to be a prime number,
and under this assumption we construct a ring structure on `TruncatedWittVector p n R`.
(`TruncatedWittVector p₁ n R` and `TruncatedWittVector p₂ n R` are definitionally
equal as types but will have different ring operations.)
-/
@[nolint unusedArguments]
def TruncatedWittVector (_ : ℕ) (n : ℕ) (R : Type*) :=
  Fin n → R

instance (p n : ℕ) (R : Type*) [Inhabited R] : Inhabited (TruncatedWittVector p n R) :=
  ⟨fun _ => default⟩

variable {n R}

namespace TruncatedWittVector

variable (p) in
/-- Create a `TruncatedWittVector` from a vector `x`. -/
def mk (x : Fin n → R) : TruncatedWittVector p n R :=
  x

/-- `x.coeff i` is the `i`th entry of `x`. -/
def coeff (i : Fin n) (x : TruncatedWittVector p n R) : R :=
  x i

@[ext]
theorem ext {x y : TruncatedWittVector p n R} (h : ∀ i, x.coeff i = y.coeff i) : x = y :=
  funext h

@[simp]
theorem coeff_mk (x : Fin n → R) (i : Fin n) : (mk p x).coeff i = x i :=
  rfl

@[simp]
theorem mk_coeff (x : TruncatedWittVector p n R) : (mk p fun i => x.coeff i) = x := by
  ext i; rw [coeff_mk]

variable [CommRing R]

/-- We can turn a truncated Witt vector `x` into a Witt vector
by setting all coefficients after `x` to be 0.
-/
def out (x : TruncatedWittVector p n R) : 𝕎 R :=
  @WittVector.mk' p _ fun i => if h : i < n then x.coeff ⟨i, h⟩ else 0

@[simp]
theorem coeff_out (x : TruncatedWittVector p n R) (i : Fin n) : x.out.coeff i = x.coeff i := by
  rw [out]; dsimp only; rw [dif_pos i.is_lt, Fin.eta]

theorem out_injective : Injective (@out p n R _) := by
  intro x y h
  ext i
  rw [WittVector.ext_iff] at h
  simpa only [coeff_out] using h ↑i

end TruncatedWittVector

namespace WittVector

variable (n)

section

/-- `truncateFun n x` uses the first `n` entries of `x` to construct a `TruncatedWittVector`,
which has the same base `p` as `x`.
This function is bundled into a ring homomorphism in `WittVector.truncate` -/
def truncateFun (x : 𝕎 R) : TruncatedWittVector p n R :=
  TruncatedWittVector.mk p fun i => x.coeff i

end

variable {n}

@[simp]
theorem coeff_truncateFun (x : 𝕎 R) (i : Fin n) : (truncateFun n x).coeff i = x.coeff i := by
  rw [truncateFun, TruncatedWittVector.coeff_mk]

variable [CommRing R]

@[simp]
theorem out_truncateFun (x : 𝕎 R) : (truncateFun n x).out = init n x := by
  ext i
  dsimp [TruncatedWittVector.out, init, select, coeff_mk]
  split_ifs with hi; swap; · rfl
  rw [coeff_truncateFun, Fin.val_mk]

end WittVector

namespace TruncatedWittVector

variable [CommRing R]

@[simp]
theorem truncateFun_out (x : TruncatedWittVector p n R) : x.out.truncateFun n = x := by
  simp only [WittVector.truncateFun, coeff_out, mk_coeff]

open WittVector

variable (p n R)
variable [Fact p.Prime]

instance : Zero (TruncatedWittVector p n R) :=
  ⟨truncateFun n 0⟩

instance : One (TruncatedWittVector p n R) :=
  ⟨truncateFun n 1⟩

instance : NatCast (TruncatedWittVector p n R) :=
  ⟨fun i => truncateFun n i⟩

instance : IntCast (TruncatedWittVector p n R) :=
  ⟨fun i => truncateFun n i⟩

instance : Add (TruncatedWittVector p n R) :=
  ⟨fun x y => truncateFun n (x.out + y.out)⟩

instance : Mul (TruncatedWittVector p n R) :=
  ⟨fun x y => truncateFun n (x.out * y.out)⟩

instance : Neg (TruncatedWittVector p n R) :=
  ⟨fun x => truncateFun n (-x.out)⟩

instance : Sub (TruncatedWittVector p n R) :=
  ⟨fun x y => truncateFun n (x.out - y.out)⟩

instance hasNatScalar : SMul ℕ (TruncatedWittVector p n R) :=
  ⟨fun m x => truncateFun n (m • x.out)⟩

instance hasIntScalar : SMul ℤ (TruncatedWittVector p n R) :=
  ⟨fun m x => truncateFun n (m • x.out)⟩

instance hasNatPow : Pow (TruncatedWittVector p n R) ℕ :=
  ⟨fun x m => truncateFun n (x.out ^ m)⟩

@[simp]
theorem coeff_zero (i : Fin n) : (0 : TruncatedWittVector p n R).coeff i = 0 := by
  change coeff i (truncateFun _ 0 : TruncatedWittVector p n R) = 0
  rw [coeff_truncateFun, WittVector.zero_coeff]

end TruncatedWittVector

/-- A macro tactic used to prove that `truncateFun` respects ring operations. -/
macro (name := witt_truncateFun_tac) "witt_truncateFun_tac" : tactic =>
  `(tactic|
    { show _ = WittVector.truncateFun n _
      apply TruncatedWittVector.out_injective
      iterate rw [WittVector.out_truncateFun]
      first
      | rw [WittVector.init_add]
      | rw [WittVector.init_mul]
      | rw [WittVector.init_neg]
      | rw [WittVector.init_sub]
      | rw [WittVector.init_nsmul]
      | rw [WittVector.init_zsmul]
      | rw [WittVector.init_pow]})

namespace WittVector

variable (p n R)
variable [CommRing R]

theorem truncateFun_surjective : Surjective (@truncateFun p n R) :=
  Function.RightInverse.surjective TruncatedWittVector.truncateFun_out

variable [Fact p.Prime]

@[simp]
theorem truncateFun_zero : truncateFun n (0 : 𝕎 R) = 0 := rfl

@[simp]
theorem truncateFun_one : truncateFun n (1 : 𝕎 R) = 1 := rfl

variable {p R}

@[simp]
theorem truncateFun_add (x y : 𝕎 R) :
    truncateFun n (x + y) = truncateFun n x + truncateFun n y := by
  witt_truncateFun_tac

@[simp]
theorem truncateFun_mul (x y : 𝕎 R) :
    truncateFun n (x * y) = truncateFun n x * truncateFun n y := by
  witt_truncateFun_tac

theorem truncateFun_neg (x : 𝕎 R) : truncateFun n (-x) = -truncateFun n x := by
  witt_truncateFun_tac

theorem truncateFun_sub (x y : 𝕎 R) :
    truncateFun n (x - y) = truncateFun n x - truncateFun n y := by
  witt_truncateFun_tac

theorem truncateFun_nsmul (m : ℕ) (x : 𝕎 R) : truncateFun n (m • x) = m • truncateFun n x := by
  witt_truncateFun_tac

theorem truncateFun_zsmul (m : ℤ) (x : 𝕎 R) : truncateFun n (m • x) = m • truncateFun n x := by
  witt_truncateFun_tac

theorem truncateFun_pow (x : 𝕎 R) (m : ℕ) : truncateFun n (x ^ m) = truncateFun n x ^ m := by
  witt_truncateFun_tac

theorem truncateFun_natCast (m : ℕ) : truncateFun n (m : 𝕎 R) = m := rfl

theorem truncateFun_intCast (m : ℤ) : truncateFun n (m : 𝕎 R) = m := rfl

end WittVector

namespace TruncatedWittVector

open WittVector

variable (p n R)
variable [CommRing R]
variable [Fact p.Prime]

instance instCommRing : CommRing (TruncatedWittVector p n R) :=
  (truncateFun_surjective p n R).commRing _ (truncateFun_zero p n R) (truncateFun_one p n R)
    (truncateFun_add n) (truncateFun_mul n) (truncateFun_neg n) (truncateFun_sub n)
    (truncateFun_nsmul n) (truncateFun_zsmul n) (truncateFun_pow n) (truncateFun_natCast n)
    (truncateFun_intCast n)

end TruncatedWittVector

namespace WittVector

open TruncatedWittVector

variable (n)
variable [CommRing R]
variable [Fact p.Prime]

/-- `truncate n` is a ring homomorphism that truncates `x` to its first `n` entries
to obtain a `TruncatedWittVector`, which has the same base `p` as `x`. -/
noncomputable def truncate : 𝕎 R →+* TruncatedWittVector p n R where
  toFun := truncateFun n
  map_zero' := truncateFun_zero p n R
  map_add' := truncateFun_add n
  map_one' := truncateFun_one p n R
  map_mul' := truncateFun_mul n

variable (p R)

theorem truncate_surjective : Surjective (truncate n : 𝕎 R → TruncatedWittVector p n R) :=
  truncateFun_surjective p n R

variable {p n R}

@[simp]
theorem coeff_truncate (x : 𝕎 R) (i : Fin n) : (truncate n x).coeff i = x.coeff i :=
  coeff_truncateFun _ _

variable (n)

theorem mem_ker_truncate (x : 𝕎 R) :
    x ∈ RingHom.ker (truncate (p := p) n) ↔ ∀ i < n, x.coeff i = 0 := by
  simp only [RingHom.mem_ker, truncate, RingHom.coe_mk, TruncatedWittVector.ext_iff,
    coeff_zero]
  exact Fin.forall_iff

variable (p)

@[simp]
theorem truncate_mk' (f : ℕ → R) :
    truncate n (@mk' p _ f) = TruncatedWittVector.mk _ fun k => f k := by
  ext i
  simp only [coeff_truncate, TruncatedWittVector.coeff_mk]

end WittVector

namespace TruncatedWittVector

variable [CommRing R]

section
variable [Fact p.Prime]

/-- A ring homomorphism that truncates a truncated Witt vector of length `m` to
a truncated Witt vector of length `n`, for `n ≤ m`.
-/
def truncate {m : ℕ} (hm : n ≤ m) : TruncatedWittVector p m R →+* TruncatedWittVector p n R :=
  RingHom.liftOfRightInverse (WittVector.truncate m) out truncateFun_out
    ⟨WittVector.truncate n, by
      intro x
      simp only [WittVector.mem_ker_truncate]
      intro h i hi
      exact h i (lt_of_lt_of_le hi hm)⟩

@[simp]
theorem truncate_comp_wittVector_truncate {m : ℕ} (hm : n ≤ m) :
    (truncate (p := p) (R := R) hm).comp (WittVector.truncate m) = WittVector.truncate n :=
  RingHom.liftOfRightInverse_comp _ _ _ _

@[simp]
theorem truncate_wittVector_truncate {m : ℕ} (hm : n ≤ m) (x : 𝕎 R) :
    truncate hm (WittVector.truncate m x) = WittVector.truncate n x :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

@[simp]
theorem truncate_truncate {n₁ n₂ n₃ : ℕ} (h1 : n₁ ≤ n₂) (h2 : n₂ ≤ n₃)
    (x : TruncatedWittVector p n₃ R) :
    (truncate h1) (truncate h2 x) = truncate (h1.trans h2) x := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) n₃ R x
  simp only [truncate_wittVector_truncate]

@[simp]
theorem truncate_comp {n₁ n₂ n₃ : ℕ} (h1 : n₁ ≤ n₂) (h2 : n₂ ≤ n₃) :
    (truncate (p := p) (R := R) h1).comp (truncate h2) = truncate (h1.trans h2) := by
  ext1 x; simp only [truncate_truncate, Function.comp_apply, RingHom.coe_comp]

theorem truncate_surjective {m : ℕ} (hm : n ≤ m) : Surjective (truncate (p := p) (R := R) hm) := by
  intro x
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) _ R x
  exact ⟨WittVector.truncate _ x, truncate_wittVector_truncate _ _⟩

@[simp]
theorem coeff_truncate {m : ℕ} (hm : n ≤ m) (i : Fin n) (x : TruncatedWittVector p m R) :
    (truncate hm x).coeff i = x.coeff (Fin.castLE hm i) := by
  obtain ⟨y, rfl⟩ := @WittVector.truncate_surjective p _ _ _ _ x
  simp only [truncate_wittVector_truncate, WittVector.coeff_truncate, Fin.val_castLE]

end

section Fintype

instance {R : Type*} [Fintype R] : Fintype (TruncatedWittVector p n R) :=
  Pi.instFintype

variable (p n R)

theorem card {R : Type*} [Fintype R] :
    Fintype.card (TruncatedWittVector p n R) = Fintype.card R ^ n := by
  simp only [TruncatedWittVector, Fintype.card_fin, Fintype.card_fun]

end Fintype

variable [Fact p.Prime]

theorem iInf_ker_truncate : ⨅ i : ℕ, RingHom.ker (WittVector.truncate (p := p) (R := R) i) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  ext
  simp only [WittVector.mem_ker_truncate, Ideal.mem_iInf, WittVector.zero_coeff] at hx ⊢
  exact hx _ _ (Nat.lt_succ_self _)

end TruncatedWittVector

namespace WittVector

open TruncatedWittVector hiding truncate coeff

section lift

variable [CommRing R]
variable [Fact p.Prime]
variable {S : Type*} [Semiring S]
variable (f : ∀ k : ℕ, S →+* TruncatedWittVector p k R)
variable
  (f_compat : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂), (TruncatedWittVector.truncate hk).comp (f k₂) = f k₁)

variable (n)

/-- Given a family `fₖ : S → TruncatedWittVector p k R` and `s : S`, we produce a Witt vector by
defining the `k`th entry to be the final entry of `fₖ s`.
-/
def liftFun (s : S) : 𝕎 R :=
  @WittVector.mk' p _ fun k => TruncatedWittVector.coeff (Fin.last k) (f (k + 1) s)

variable {f} in
include f_compat in
@[simp]
theorem truncate_liftFun (s : S) : WittVector.truncate n (liftFun f s) = f n s := by
  ext i
  simp only [liftFun, TruncatedWittVector.coeff_mk, WittVector.truncate_mk']
  rw [← f_compat (i + 1) n i.is_lt, RingHom.comp_apply, TruncatedWittVector.coeff_truncate]
  congr 1 with _

/--
Given compatible ring homs from `S` into `TruncatedWittVector n` for each `n`, we can lift these
to a ring hom `S → 𝕎 R`.

`lift` defines the universal property of `𝕎 R` as the inverse limit of `TruncatedWittVector n`.
-/
def lift : S →+* 𝕎 R := by
  refine { toFun := liftFun f
           map_zero' := ?_
           map_one' := ?_
           map_add' := ?_
           map_mul' := ?_ } <;>
  ( intros
    rw [← sub_eq_zero, ← Ideal.mem_bot, ← iInf_ker_truncate, Ideal.mem_iInf]
    simp [RingHom.mem_ker, f_compat])

variable {f}

@[simp]
theorem truncate_lift (s : S) : WittVector.truncate n (lift _ f_compat s) = f n s :=
  truncate_liftFun _ f_compat s

@[simp]
theorem truncate_comp_lift : (WittVector.truncate n).comp (lift _ f_compat) = f n := by
  ext1; rw [RingHom.comp_apply, truncate_lift]

/-- The uniqueness part of the universal property of `𝕎 R`. -/
theorem lift_unique (g : S →+* 𝕎 R) (g_compat : ∀ k, (WittVector.truncate k).comp g = f k) :
    lift _ f_compat = g := by
  ext1 x
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← iInf_ker_truncate, Ideal.mem_iInf]
  intro i
  simp only [RingHom.mem_ker, g_compat, ← RingHom.comp_apply, truncate_comp_lift, map_sub, sub_self]

/-- The universal property of `𝕎 R` as projective limit of truncated Witt vector rings. -/
@[simps]
def liftEquiv : { f : ∀ k, S →+* TruncatedWittVector p k R // ∀ (k₁ k₂) (hk : k₁ ≤ k₂),
    (TruncatedWittVector.truncate hk).comp (f k₂) = f k₁ } ≃ (S →+* 𝕎 R) where
  toFun f := lift f.1 f.2
  invFun g :=
    ⟨fun k => (truncate k).comp g, by
      intro _ _ h
      simp only [← RingHom.comp_assoc, truncate_comp_wittVector_truncate]⟩
  left_inv := by rintro ⟨f, hf⟩; simp only [truncate_comp_lift]
  right_inv _ := lift_unique _ _ fun _ => rfl

theorem hom_ext (g₁ g₂ : S →+* 𝕎 R) (h : ∀ k, (truncate k).comp g₁ = (truncate k).comp g₂) :
    g₁ = g₂ :=
  liftEquiv.symm.injective <| Subtype.ext <| funext h

end lift

end WittVector
