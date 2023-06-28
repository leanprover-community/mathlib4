/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis

! This file was ported from Lean 3 source module ring_theory.witt_vector.truncated
! leanprover-community/mathlib commit acbe099ced8be9c9754d62860110295cde0d7181
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RingTheory.WittVector.InitTail

/-!

# Truncated Witt vectors

The ring of truncated Witt vectors (of length `n`) is a quotient of the ring of Witt vectors.
It retains the first `n` coefficients of each Witt vector.
In this file, we set up the basic quotient API for this ring.

The ring of Witt vectors is the projective limit of all the rings of truncated Witt vectors.

## Main declarations

- `truncated_witt_vector`: the underlying type of the ring of truncated Witt vectors
- `truncated_witt_vector.comm_ring`: the ring structure on truncated Witt vectors
- `witt_vector.truncate`: the quotient homomorphism that truncates a Witt vector,
  to obtain a truncated Witt vector
- `truncated_witt_vector.truncate`: the homomorphism that truncates
  a truncated Witt vector of length `n` to one of length `m` (for some `m ≤ n`)
- `witt_vector.lift`: the unique ring homomorphism into the ring of Witt vectors
  that is compatible with a family of ring homomorphisms to the truncated Witt vectors:
  this realizes the ring of Witt vectors as projective limit of the rings of truncated Witt vectors

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


open Function (Injective Surjective)

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime] (n : ℕ) (R : Type _)

local notation "𝕎" => WittVector p

-- type as `\bbW`
/-- A truncated Witt vector over `R` is a vector of elements of `R`,
i.e., the first `n` coefficients of a Witt vector.
We will define operations on this type that are compatible with the (untruncated) Witt
vector operations.

`truncated_witt_vector p n R` takes a parameter `p : ℕ` that is not used in the definition.
In practice, this number `p` is assumed to be a prime number,
and under this assumption we construct a ring structure on `truncated_witt_vector p n R`.
(`truncated_witt_vector p₁ n R` and `truncated_witt_vector p₂ n R` are definitionally
equal as types but will have different ring operations.)
-/
@[nolint unused_arguments]
def TruncatedWittVector (p : ℕ) (n : ℕ) (R : Type _) :=
  Fin n → R
#align truncated_witt_vector TruncatedWittVector

instance (p n : ℕ) (R : Type _) [Inhabited R] : Inhabited (TruncatedWittVector p n R) :=
  ⟨fun _ => default⟩

variable {n R}

namespace TruncatedWittVector

variable (p)

/-- Create a `truncated_witt_vector` from a vector `x`. -/
def mk (x : Fin n → R) : TruncatedWittVector p n R :=
  x
#align truncated_witt_vector.mk TruncatedWittVector.mk

variable {p}

/-- `x.coeff i` is the `i`th entry of `x`. -/
def coeff (i : Fin n) (x : TruncatedWittVector p n R) : R :=
  x i
#align truncated_witt_vector.coeff TruncatedWittVector.coeff

@[ext]
theorem ext {x y : TruncatedWittVector p n R} (h : ∀ i, x.coeff i = y.coeff i) : x = y :=
  funext h
#align truncated_witt_vector.ext TruncatedWittVector.ext

theorem ext_iff {x y : TruncatedWittVector p n R} : x = y ↔ ∀ i, x.coeff i = y.coeff i :=
  ⟨fun h i => by rw [h], ext⟩
#align truncated_witt_vector.ext_iff TruncatedWittVector.ext_iff

@[simp]
theorem coeff_mk (x : Fin n → R) (i : Fin n) : (mk p x).coeff i = x i :=
  rfl
#align truncated_witt_vector.coeff_mk TruncatedWittVector.coeff_mk

@[simp]
theorem mk_coeff (x : TruncatedWittVector p n R) : (mk p fun i => x.coeff i) = x := by ext i;
  rw [coeff_mk]
#align truncated_witt_vector.mk_coeff TruncatedWittVector.mk_coeff

variable [CommRing R]

/-- We can turn a truncated Witt vector `x` into a Witt vector
by setting all coefficients after `x` to be 0.
-/
def out (x : TruncatedWittVector p n R) : 𝕎 R :=
  WittVector.mk' p fun i => if h : i < n then x.coeff ⟨i, h⟩ else 0
#align truncated_witt_vector.out TruncatedWittVector.out

@[simp]
theorem coeff_out (x : TruncatedWittVector p n R) (i : Fin n) : x.out.coeff i = x.coeff i := by
  rw [out, WittVector.coeff_mk, dif_pos i.is_lt, Fin.eta]
#align truncated_witt_vector.coeff_out TruncatedWittVector.coeff_out

theorem out_injective : Injective (@out p n R _) := by
  intro x y h
  ext i
  rw [WittVector.ext_iff] at h 
  simpa only [coeff_out] using h ↑i
#align truncated_witt_vector.out_injective TruncatedWittVector.out_injective

end TruncatedWittVector

namespace WittVector

variable {p} (n)

section

/-- `truncate_fun n x` uses the first `n` entries of `x` to construct a `truncated_witt_vector`,
which has the same base `p` as `x`.
This function is bundled into a ring homomorphism in `witt_vector.truncate` -/
def truncateFun (x : 𝕎 R) : TruncatedWittVector p n R :=
  TruncatedWittVector.mk p fun i => x.coeff i
#align witt_vector.truncate_fun WittVector.truncateFun

end

variable {n}

@[simp]
theorem coeff_truncateFun (x : 𝕎 R) (i : Fin n) : (truncateFun n x).coeff i = x.coeff i := by
  rw [truncate_fun, TruncatedWittVector.coeff_mk]
#align witt_vector.coeff_truncate_fun WittVector.coeff_truncateFun

variable [CommRing R]

@[simp]
theorem out_truncateFun (x : 𝕎 R) : (truncateFun n x).out = init n x := by
  ext i
  dsimp [TruncatedWittVector.out, init, select]
  split_ifs with hi; swap; · rfl
  rw [coeff_truncate_fun, Fin.val_mk]
#align witt_vector.out_truncate_fun WittVector.out_truncateFun

end WittVector

namespace TruncatedWittVector

variable [CommRing R]

@[simp]
theorem truncateFun_out (x : TruncatedWittVector p n R) : x.out.truncateFun n = x := by
  simp only [WittVector.truncateFun, coeff_out, mk_coeff]
#align truncated_witt_vector.truncate_fun_out TruncatedWittVector.truncateFun_out

open WittVector

variable (p n R)

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
#align truncated_witt_vector.has_nat_scalar TruncatedWittVector.hasNatScalar

instance hasIntScalar : SMul ℤ (TruncatedWittVector p n R) :=
  ⟨fun m x => truncateFun n (m • x.out)⟩
#align truncated_witt_vector.has_int_scalar TruncatedWittVector.hasIntScalar

instance hasNatPow : Pow (TruncatedWittVector p n R) ℕ :=
  ⟨fun x m => truncateFun n (x.out ^ m)⟩
#align truncated_witt_vector.has_nat_pow TruncatedWittVector.hasNatPow

@[simp]
theorem coeff_zero (i : Fin n) : (0 : TruncatedWittVector p n R).coeff i = 0 := by
  show coeff i (truncate_fun _ 0 : TruncatedWittVector p n R) = 0
  rw [coeff_truncate_fun, WittVector.zero_coeff]
#align truncated_witt_vector.coeff_zero TruncatedWittVector.coeff_zero

end TruncatedWittVector

/- ./././Mathport/Syntax/Translate/Expr.lean:336:4: warning: unsupported (TODO): `[tacs] -/
/-- A macro tactic used to prove that `truncate_fun` respects ring operations. -/
unsafe def tactic.interactive.witt_truncate_fun_tac : tactic Unit :=
  sorry
#align tactic.interactive.witt_truncate_fun_tac tactic.interactive.witt_truncate_fun_tac

namespace WittVector

variable (p n R)

variable [CommRing R]

theorem truncateFun_surjective : Surjective (@truncateFun p n R) :=
  Function.RightInverse.surjective TruncatedWittVector.truncateFun_out
#align witt_vector.truncate_fun_surjective WittVector.truncateFun_surjective

@[simp]
theorem truncateFun_zero : truncateFun n (0 : 𝕎 R) = 0 :=
  rfl
#align witt_vector.truncate_fun_zero WittVector.truncateFun_zero

@[simp]
theorem truncateFun_one : truncateFun n (1 : 𝕎 R) = 1 :=
  rfl
#align witt_vector.truncate_fun_one WittVector.truncateFun_one

variable {p R}

@[simp]
theorem truncateFun_add (x y : 𝕎 R) : truncateFun n (x + y) = truncateFun n x + truncateFun n y :=
  by witt_truncate_fun_tac; rw [init_add]
#align witt_vector.truncate_fun_add WittVector.truncateFun_add

@[simp]
theorem truncateFun_mul (x y : 𝕎 R) : truncateFun n (x * y) = truncateFun n x * truncateFun n y :=
  by witt_truncate_fun_tac; rw [init_mul]
#align witt_vector.truncate_fun_mul WittVector.truncateFun_mul

theorem truncateFun_neg (x : 𝕎 R) : truncateFun n (-x) = -truncateFun n x := by
  witt_truncate_fun_tac; rw [init_neg]
#align witt_vector.truncate_fun_neg WittVector.truncateFun_neg

theorem truncateFun_sub (x y : 𝕎 R) : truncateFun n (x - y) = truncateFun n x - truncateFun n y :=
  by witt_truncate_fun_tac; rw [init_sub]
#align witt_vector.truncate_fun_sub WittVector.truncateFun_sub

theorem truncateFun_nsmul (x : 𝕎 R) (m : ℕ) : truncateFun n (m • x) = m • truncateFun n x := by
  witt_truncate_fun_tac; rw [init_nsmul]
#align witt_vector.truncate_fun_nsmul WittVector.truncateFun_nsmul

theorem truncateFun_zsmul (x : 𝕎 R) (m : ℤ) : truncateFun n (m • x) = m • truncateFun n x := by
  witt_truncate_fun_tac; rw [init_zsmul]
#align witt_vector.truncate_fun_zsmul WittVector.truncateFun_zsmul

theorem truncateFun_pow (x : 𝕎 R) (m : ℕ) : truncateFun n (x ^ m) = truncateFun n x ^ m := by
  witt_truncate_fun_tac; rw [init_pow]
#align witt_vector.truncate_fun_pow WittVector.truncateFun_pow

theorem truncateFun_nat_cast (m : ℕ) : truncateFun n (m : 𝕎 R) = m :=
  rfl
#align witt_vector.truncate_fun_nat_cast WittVector.truncateFun_nat_cast

theorem truncateFun_int_cast (m : ℤ) : truncateFun n (m : 𝕎 R) = m :=
  rfl
#align witt_vector.truncate_fun_int_cast WittVector.truncateFun_int_cast

end WittVector

namespace TruncatedWittVector

open WittVector

variable (p n R)

variable [CommRing R]

instance : CommRing (TruncatedWittVector p n R) :=
  (truncateFun_surjective p n R).CommRing _ (truncateFun_zero p n R) (truncateFun_one p n R)
    (truncateFun_add n) (truncateFun_mul n) (truncateFun_neg n) (truncateFun_sub n)
    (truncateFun_nsmul n) (truncateFun_zsmul n) (truncateFun_pow n) (truncateFun_nat_cast n)
    (truncateFun_int_cast n)

end TruncatedWittVector

namespace WittVector

open TruncatedWittVector

variable (n)

variable [CommRing R]

/-- `truncate n` is a ring homomorphism that truncates `x` to its first `n` entries
to obtain a `truncated_witt_vector`, which has the same base `p` as `x`. -/
noncomputable def truncate : 𝕎 R →+* TruncatedWittVector p n R where
  toFun := truncateFun n
  map_zero' := truncateFun_zero p n R
  map_add' := truncateFun_add n
  map_one' := truncateFun_one p n R
  map_mul' := truncateFun_mul n
#align witt_vector.truncate WittVector.truncate

variable (p n R)

theorem truncate_surjective : Surjective (truncate n : 𝕎 R → TruncatedWittVector p n R) :=
  truncateFun_surjective p n R
#align witt_vector.truncate_surjective WittVector.truncate_surjective

variable {p n R}

@[simp]
theorem coeff_truncate (x : 𝕎 R) (i : Fin n) : (truncate n x).coeff i = x.coeff i :=
  coeff_truncateFun _ _
#align witt_vector.coeff_truncate WittVector.coeff_truncate

variable (n)

theorem mem_ker_truncate (x : 𝕎 R) : x ∈ (@truncate p _ n R _).ker ↔ ∀ i < n, x.coeff i = 0 := by
  simp only [RingHom.mem_ker, truncate, truncate_fun, RingHom.coe_mk, TruncatedWittVector.ext_iff,
    TruncatedWittVector.coeff_mk, coeff_zero]
  exact Fin.forall_iff
#align witt_vector.mem_ker_truncate WittVector.mem_ker_truncate

variable (p)

@[simp]
theorem truncate_mk' (f : ℕ → R) : truncate n (mk' p f) = TruncatedWittVector.mk _ fun k => f k :=
  by
  ext i
  rw [coeff_truncate, coeff_mk, TruncatedWittVector.coeff_mk]
#align witt_vector.truncate_mk WittVector.truncate_mk'

end WittVector

namespace TruncatedWittVector

variable [CommRing R]

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
#align truncated_witt_vector.truncate TruncatedWittVector.truncate

@[simp]
theorem truncate_comp_wittVector_truncate {m : ℕ} (hm : n ≤ m) :
    (@truncate p _ n R _ m hm).comp (WittVector.truncate m) = WittVector.truncate n :=
  RingHom.liftOfRightInverse_comp _ _ _ _
#align truncated_witt_vector.truncate_comp_witt_vector_truncate TruncatedWittVector.truncate_comp_wittVector_truncate

@[simp]
theorem truncate_wittVector_truncate {m : ℕ} (hm : n ≤ m) (x : 𝕎 R) :
    truncate hm (WittVector.truncate m x) = WittVector.truncate n x :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _
#align truncated_witt_vector.truncate_witt_vector_truncate TruncatedWittVector.truncate_wittVector_truncate

@[simp]
theorem truncate_truncate {n₁ n₂ n₃ : ℕ} (h1 : n₁ ≤ n₂) (h2 : n₂ ≤ n₃)
    (x : TruncatedWittVector p n₃ R) : (truncate h1) (truncate h2 x) = truncate (h1.trans h2) x :=
  by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n₃ R x
  simp only [truncate_witt_vector_truncate]
#align truncated_witt_vector.truncate_truncate TruncatedWittVector.truncate_truncate

@[simp]
theorem truncate_comp {n₁ n₂ n₃ : ℕ} (h1 : n₁ ≤ n₂) (h2 : n₂ ≤ n₃) :
    (@truncate p _ _ R _ _ h1).comp (truncate h2) = truncate (h1.trans h2) := by ext1 x;
  simp only [truncate_truncate, Function.comp_apply, RingHom.coe_comp]
#align truncated_witt_vector.truncate_comp TruncatedWittVector.truncate_comp

theorem truncate_surjective {m : ℕ} (hm : n ≤ m) : Surjective (@truncate p _ _ R _ _ hm) := by
  intro x
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p _ R x
  exact ⟨WittVector.truncate _ x, truncate_witt_vector_truncate _ _⟩
#align truncated_witt_vector.truncate_surjective TruncatedWittVector.truncate_surjective

@[simp]
theorem coeff_truncate {m : ℕ} (hm : n ≤ m) (i : Fin n) (x : TruncatedWittVector p m R) :
    (truncate hm x).coeff i = x.coeff (Fin.castLE hm i) := by
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p _ _ x
  simp only [truncate_witt_vector_truncate, WittVector.coeff_truncate, Fin.coe_castLE]
#align truncated_witt_vector.coeff_truncate TruncatedWittVector.coeff_truncate

section Fintype

instance {R : Type _} [Fintype R] : Fintype (TruncatedWittVector p n R) :=
  Pi.fintype

variable (p n R)

theorem card {R : Type _} [Fintype R] :
    Fintype.card (TruncatedWittVector p n R) = Fintype.card R ^ n := by
  simp only [TruncatedWittVector, Fintype.card_fin, Fintype.card_fun]
#align truncated_witt_vector.card TruncatedWittVector.card

end Fintype

theorem iInf_ker_truncate : (⨅ i : ℕ, (@WittVector.truncate p _ i R _).ker) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  ext
  simp only [WittVector.mem_ker_truncate, Ideal.mem_iInf, WittVector.zero_coeff] at hx ⊢
  exact hx _ _ (Nat.lt_succ_self _)
#align truncated_witt_vector.infi_ker_truncate TruncatedWittVector.iInf_ker_truncate

end TruncatedWittVector

namespace WittVector

open TruncatedWittVector hiding truncate coeff

section lift

variable [CommRing R]

variable {S : Type _} [Semiring S]

variable (f : ∀ k : ℕ, S →+* TruncatedWittVector p k R)

variable
  (f_compat : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂), (TruncatedWittVector.truncate hk).comp (f k₂) = f k₁)

variable {p R}

variable (n)

/-- Given a family `fₖ : S → truncated_witt_vector p k R` and `s : S`, we produce a Witt vector by
defining the `k`th entry to be the final entry of `fₖ s`.
-/
def liftFun (s : S) : 𝕎 R :=
  WittVector.mk' p fun k => TruncatedWittVector.coeff (Fin.last k) (f (k + 1) s)
#align witt_vector.lift_fun WittVector.liftFun

variable {f}

@[simp]
theorem truncate_liftFun (s : S) : WittVector.truncate n (liftFun f s) = f n s := by
  ext i
  simp only [lift_fun, TruncatedWittVector.coeff_mk, WittVector.truncate_mk']
  rw [← f_compat (i + 1) n i.is_lt, RingHom.comp_apply, TruncatedWittVector.coeff_truncate]
  -- this is a bit unfortunate
  congr with _
  simp only [Fin.val_last, Fin.coe_castLE]
#align witt_vector.truncate_lift_fun WittVector.truncate_liftFun

variable (f)

/--
Given compatible ring homs from `S` into `truncated_witt_vector n` for each `n`, we can lift these
to a ring hom `S → 𝕎 R`.

`lift` defines the universal property of `𝕎 R` as the inverse limit of `truncated_witt_vector n`.
-/
def lift : S →+* 𝕎 R := by
  refine_struct { toFun := lift_fun f } <;>
    · intros
      rw [← sub_eq_zero, ← Ideal.mem_bot, ← infi_ker_truncate, Ideal.mem_iInf]
      simp [RingHom.mem_ker, f_compat]
#align witt_vector.lift WittVector.lift

variable {f}

@[simp]
theorem truncate_lift (s : S) : WittVector.truncate n (lift _ f_compat s) = f n s :=
  truncate_liftFun _ f_compat s
#align witt_vector.truncate_lift WittVector.truncate_lift

@[simp]
theorem truncate_comp_lift : (WittVector.truncate n).comp (lift _ f_compat) = f n := by ext1;
  rw [RingHom.comp_apply, truncate_lift]
#align witt_vector.truncate_comp_lift WittVector.truncate_comp_lift

/-- The uniqueness part of the universal property of `𝕎 R`. -/
theorem lift_unique (g : S →+* 𝕎 R) (g_compat : ∀ k, (WittVector.truncate k).comp g = f k) :
    lift _ f_compat = g := by
  ext1 x
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← infi_ker_truncate, Ideal.mem_iInf]
  intro i
  simp only [RingHom.mem_ker, g_compat, ← RingHom.comp_apply, truncate_comp_lift, RingHom.map_sub,
    sub_self]
#align witt_vector.lift_unique WittVector.lift_unique

/-- The universal property of `𝕎 R` as projective limit of truncated Witt vector rings. -/
@[simps]
def liftEquiv :
    { f : ∀ k, S →+* TruncatedWittVector p k R //
        ∀ (k₁ k₂) (hk : k₁ ≤ k₂), (TruncatedWittVector.truncate hk).comp (f k₂) = f k₁ } ≃
      (S →+* 𝕎 R) where
  toFun f := lift f.1 f.2
  invFun g :=
    ⟨fun k => (truncate k).comp g, by intro _ _ h;
      simp only [← RingHom.comp_assoc, truncate_comp_witt_vector_truncate]⟩
  left_inv := by rintro ⟨f, hf⟩; simp only [truncate_comp_lift]
  right_inv g := lift_unique _ _ fun _ => rfl
#align witt_vector.lift_equiv WittVector.liftEquiv

theorem hom_ext (g₁ g₂ : S →+* 𝕎 R) (h : ∀ k, (truncate k).comp g₁ = (truncate k).comp g₂) :
    g₁ = g₂ :=
  liftEquiv.symm.Injective <| Subtype.ext <| funext h
#align witt_vector.hom_ext WittVector.hom_ext

end lift

end WittVector

