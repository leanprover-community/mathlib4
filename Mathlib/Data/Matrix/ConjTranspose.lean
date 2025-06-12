/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.RingEquiv
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Mul

/-!
# Matrices over star rings.

## Notation

The locale `Matrix` gives the following notation:

* `ᴴ` for `Matrix.conjTranspose`

-/


universe u u' v w

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}
variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

namespace Matrix


/-- The conjugate transpose of a matrix defined in term of `star`. -/
def conjTranspose [Star α] (M : Matrix m n α) : Matrix n m α :=
  M.transpose.map star

@[inherit_doc]
scoped postfix:1024 "ᴴ" => Matrix.conjTranspose

@[simp]
lemma conjTranspose_single [DecidableEq n] [DecidableEq m] [AddMonoid α]
    [StarAddMonoid α] (i : m) (j : n) (a : α) :
    (single i j a)ᴴ = single j i (star a) := by
  show (single i j a).transpose.map starAddEquiv = single j i (star a)
  simp

@[deprecated (since := "2025-05-05")] alias conjTranspose_stdBasisMatrix := conjTranspose_single

section Diagonal

variable [DecidableEq n]

@[simp]
theorem diagonal_conjTranspose [AddMonoid α] [StarAddMonoid α] (v : n → α) :
    (diagonal v)ᴴ = diagonal (star v) := by
  rw [conjTranspose, diagonal_transpose, diagonal_map (star_zero _)]
  rfl

end Diagonal

section Diag

@[simp]
theorem diag_conjTranspose [Star α] (A : Matrix n n α) :
    diag Aᴴ = star (diag A) :=
  rfl

end Diag

section DotProduct

variable [Fintype m] [Fintype n]

section StarRing

variable [NonUnitalSemiring α] [StarRing α] (v w : m → α)

theorem star_dotProduct_star : star v ⬝ᵥ star w = star (w ⬝ᵥ v) := by simp [dotProduct]

theorem star_dotProduct : star v ⬝ᵥ w = star (star w ⬝ᵥ v) := by simp [dotProduct]

theorem dotProduct_star : v ⬝ᵥ star w = star (w ⬝ᵥ star v) := by simp [dotProduct]

end StarRing

end DotProduct

section NonUnitalSemiring

variable [NonUnitalSemiring α]

theorem star_mulVec [Fintype n] [StarRing α] (M : Matrix m n α) (v : n → α) :
    star (M *ᵥ v) = star v ᵥ* Mᴴ :=
  funext fun _ => (star_dotProduct_star _ _).symm

theorem star_vecMul [Fintype m] [StarRing α] (M : Matrix m n α) (v : m → α) :
    star (v ᵥ* M) = Mᴴ *ᵥ star v :=
  funext fun _ => (star_dotProduct_star _ _).symm

theorem mulVec_conjTranspose [Fintype m] [StarRing α] (A : Matrix m n α) (x : m → α) :
    Aᴴ *ᵥ x = star (star x ᵥ* A) :=
  funext fun _ => star_dotProduct _ _

theorem vecMul_conjTranspose [Fintype n] [StarRing α] (A : Matrix m n α) (x : n → α) :
    x ᵥ* Aᴴ = star (A *ᵥ star x) :=
  funext fun _ => dotProduct_star _ _

end NonUnitalSemiring

section ConjTranspose

open Matrix

/-- Tell `simp` what the entries are in a conjugate transposed matrix.

  Compare with `mul_apply`, `diagonal_apply_eq`, etc.
-/
@[simp]
theorem conjTranspose_apply [Star α] (M : Matrix m n α) (i j) :
    M.conjTranspose j i = star (M i j) :=
  rfl

@[simp]
theorem conjTranspose_conjTranspose [InvolutiveStar α] (M : Matrix m n α) : Mᴴᴴ = M :=
  Matrix.ext <| by simp

theorem conjTranspose_injective [InvolutiveStar α] :
    Function.Injective (conjTranspose : Matrix m n α → Matrix n m α) :=
  (map_injective star_injective).comp transpose_injective

@[simp] theorem conjTranspose_inj [InvolutiveStar α] {A B : Matrix m n α} : Aᴴ = Bᴴ ↔ A = B :=
  conjTranspose_injective.eq_iff

@[simp]
theorem conjTranspose_eq_diagonal [DecidableEq n] [AddMonoid α] [StarAddMonoid α]
    {M : Matrix n n α} {v : n → α} :
    Mᴴ = diagonal v ↔ M = diagonal (star v) :=
  (Function.Involutive.eq_iff conjTranspose_conjTranspose).trans <|
    by rw [diagonal_conjTranspose]

@[simp]
theorem conjTranspose_zero [AddMonoid α] [StarAddMonoid α] : (0 : Matrix m n α)ᴴ = 0 :=
  Matrix.ext <| by simp

@[simp]
theorem conjTranspose_eq_zero [AddMonoid α] [StarAddMonoid α] {M : Matrix m n α} :
    Mᴴ = 0 ↔ M = 0 := by
  rw [← conjTranspose_inj (A := M), conjTranspose_zero]

@[simp]
theorem conjTranspose_one [DecidableEq n] [NonAssocSemiring α] [StarRing α] :
    (1 : Matrix n n α)ᴴ = 1 := by
  simp [conjTranspose]

@[simp]
theorem conjTranspose_eq_one [DecidableEq n] [NonAssocSemiring α] [StarRing α] {M : Matrix n n α} :
    Mᴴ = 1 ↔ M = 1 :=
  (Function.Involutive.eq_iff conjTranspose_conjTranspose).trans <|
    by rw [conjTranspose_one]

@[simp]
theorem conjTranspose_natCast [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d : ℕ) :
    (d : Matrix n n α)ᴴ = d := by
  simp [conjTranspose, Matrix.map_natCast, diagonal_natCast]

@[simp]
theorem conjTranspose_eq_natCast [DecidableEq n] [NonAssocSemiring α] [StarRing α]
    {M : Matrix n n α} {d : ℕ} :
    Mᴴ = d ↔ M = d :=
  (Function.Involutive.eq_iff conjTranspose_conjTranspose).trans <|
    by rw [conjTranspose_natCast]

@[simp]
theorem conjTranspose_ofNat [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d : ℕ)
    [d.AtLeastTwo] : (ofNat(d) : Matrix n n α)ᴴ = OfNat.ofNat d :=
  conjTranspose_natCast _

@[simp]
theorem conjTranspose_eq_ofNat [DecidableEq n] [Semiring α] [StarRing α]
    {M : Matrix n n α} {d : ℕ} [d.AtLeastTwo] :
    Mᴴ = ofNat(d) ↔ M = OfNat.ofNat d :=
  conjTranspose_eq_natCast

@[simp]
theorem conjTranspose_intCast [DecidableEq n] [Ring α] [StarRing α] (d : ℤ) :
    (d : Matrix n n α)ᴴ = d := by
  simp [conjTranspose, Matrix.map_intCast, diagonal_intCast]

@[simp]
theorem conjTranspose_eq_intCast [DecidableEq n] [Ring α] [StarRing α]
    {M : Matrix n n α} {d : ℤ} :
    Mᴴ = d ↔ M = d :=
  (Function.Involutive.eq_iff conjTranspose_conjTranspose).trans <|
    by rw [conjTranspose_intCast]

@[simp]
theorem conjTranspose_add [AddMonoid α] [StarAddMonoid α] (M N : Matrix m n α) :
    (M + N)ᴴ = Mᴴ + Nᴴ :=
  Matrix.ext <| by simp

@[simp]
theorem conjTranspose_sub [AddGroup α] [StarAddMonoid α] (M N : Matrix m n α) :
    (M - N)ᴴ = Mᴴ - Nᴴ :=
  Matrix.ext <| by simp

/-- Note that `StarModule` is quite a strong requirement; as such we also provide the following
variants which this lemma would not apply to:
* `Matrix.conjTranspose_smul_non_comm`
* `Matrix.conjTranspose_nsmul`
* `Matrix.conjTranspose_zsmul`
* `Matrix.conjTranspose_natCast_smul`
* `Matrix.conjTranspose_intCast_smul`
* `Matrix.conjTranspose_inv_natCast_smul`
* `Matrix.conjTranspose_inv_intCast_smul`
* `Matrix.conjTranspose_ratCast_smul`
-/
@[simp]
theorem conjTranspose_smul [Star R] [Star α] [SMul R α] [StarModule R α] (c : R)
    (M : Matrix m n α) : (c • M)ᴴ = star c • Mᴴ :=
  Matrix.ext fun _ _ => star_smul _ _

@[simp]
theorem conjTranspose_smul_non_comm [Star R] [Star α] [SMul R α] [SMul Rᵐᵒᵖ α] (c : R)
    (M : Matrix m n α) (h : ∀ (r : R) (a : α), star (r • a) = MulOpposite.op (star r) • star a) :
    (c • M)ᴴ = MulOpposite.op (star c) • Mᴴ :=
  Matrix.ext <| by simp [h]

theorem conjTranspose_smul_self [Mul α] [StarMul α] (c : α) (M : Matrix m n α) :
    (c • M)ᴴ = MulOpposite.op (star c) • Mᴴ :=
  conjTranspose_smul_non_comm c M star_mul

@[simp]
theorem conjTranspose_nsmul [AddMonoid α] [StarAddMonoid α] (c : ℕ) (M : Matrix m n α) :
    (c • M)ᴴ = c • Mᴴ :=
  Matrix.ext <| by simp

@[simp]
theorem conjTranspose_zsmul [AddGroup α] [StarAddMonoid α] (c : ℤ) (M : Matrix m n α) :
    (c • M)ᴴ = c • Mᴴ :=
  Matrix.ext <| by simp

@[simp]
theorem conjTranspose_natCast_smul [Semiring R] [AddCommMonoid α] [StarAddMonoid α] [Module R α]
    (c : ℕ) (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ :=
  Matrix.ext <| by simp

@[simp]
theorem conjTranspose_ofNat_smul [Semiring R] [AddCommMonoid α] [StarAddMonoid α] [Module R α]
    (c : ℕ) [c.AtLeastTwo] (M : Matrix m n α) :
    ((ofNat(c) : R) • M)ᴴ = (OfNat.ofNat c : R) • Mᴴ :=
  conjTranspose_natCast_smul c M

@[simp]
theorem conjTranspose_intCast_smul [Ring R] [AddCommGroup α] [StarAddMonoid α] [Module R α] (c : ℤ)
    (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ :=
  Matrix.ext <| by simp

@[simp]
theorem conjTranspose_inv_natCast_smul [DivisionSemiring R] [AddCommMonoid α] [StarAddMonoid α]
    [Module R α] (c : ℕ) (M : Matrix m n α) : ((c : R)⁻¹ • M)ᴴ = (c : R)⁻¹ • Mᴴ :=
  Matrix.ext <| by simp

@[simp]
theorem conjTranspose_inv_ofNat_smul [DivisionSemiring R] [AddCommMonoid α] [StarAddMonoid α]
    [Module R α] (c : ℕ) [c.AtLeastTwo] (M : Matrix m n α) :
    ((ofNat(c) : R)⁻¹ • M)ᴴ = (OfNat.ofNat c : R)⁻¹ • Mᴴ :=
  conjTranspose_inv_natCast_smul c M

@[simp]
theorem conjTranspose_inv_intCast_smul [DivisionRing R] [AddCommGroup α] [StarAddMonoid α]
    [Module R α] (c : ℤ) (M : Matrix m n α) : ((c : R)⁻¹ • M)ᴴ = (c : R)⁻¹ • Mᴴ :=
  Matrix.ext <| by simp

@[simp]
theorem conjTranspose_ratCast_smul [DivisionRing R] [AddCommGroup α] [StarAddMonoid α] [Module R α]
    (c : ℚ) (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ :=
  Matrix.ext <| by simp

theorem conjTranspose_rat_smul [AddCommGroup α] [StarAddMonoid α] [Module ℚ α] (c : ℚ)
    (M : Matrix m n α) : (c • M)ᴴ = c • Mᴴ :=
  Matrix.ext <| by simp

@[simp]
theorem conjTranspose_mul [Fintype n] [NonUnitalNonAssocSemiring α] [StarRing α] (M : Matrix m n α)
    (N : Matrix n l α) : (M * N)ᴴ = Nᴴ * Mᴴ :=
  Matrix.ext <| by simp [mul_apply]

@[simp]
theorem conjTranspose_neg [AddGroup α] [StarAddMonoid α] (M : Matrix m n α) : (-M)ᴴ = -Mᴴ :=
  Matrix.ext <| by simp

theorem conjTranspose_map [Star α] [Star β] {A : Matrix m n α} (f : α → β)
    (hf : Function.Semiconj f star star) : Aᴴ.map f = (A.map f)ᴴ :=
  Matrix.ext fun _ _ => hf _

/-- When `star x = x` on the coefficients (such as the real numbers) `conjTranspose` and `transpose`
are the same operation. -/
@[simp]
theorem conjTranspose_eq_transpose_of_trivial [Star α] [TrivialStar α] (A : Matrix m n α) :
    Aᴴ = Aᵀ := Matrix.ext fun _ _ => star_trivial _

variable (m n α)

/-- `Matrix.conjTranspose` as an `AddEquiv` -/
@[simps apply]
def conjTransposeAddEquiv [AddMonoid α] [StarAddMonoid α] : Matrix m n α ≃+ Matrix n m α where
  toFun := conjTranspose
  invFun := conjTranspose
  left_inv := conjTranspose_conjTranspose
  right_inv := conjTranspose_conjTranspose
  map_add' := conjTranspose_add

@[simp]
theorem conjTransposeAddEquiv_symm [AddMonoid α] [StarAddMonoid α] :
    (conjTransposeAddEquiv m n α).symm = conjTransposeAddEquiv n m α :=
  rfl

variable {m n α}

theorem conjTranspose_list_sum [AddMonoid α] [StarAddMonoid α] (l : List (Matrix m n α)) :
    l.sumᴴ = (l.map conjTranspose).sum :=
  map_list_sum (conjTransposeAddEquiv m n α) l

theorem conjTranspose_multiset_sum [AddCommMonoid α] [StarAddMonoid α]
    (s : Multiset (Matrix m n α)) : s.sumᴴ = (s.map conjTranspose).sum :=
  (conjTransposeAddEquiv m n α).toAddMonoidHom.map_multiset_sum s

theorem conjTranspose_sum [AddCommMonoid α] [StarAddMonoid α] {ι : Type*} (s : Finset ι)
    (M : ι → Matrix m n α) : (∑ i ∈ s, M i)ᴴ = ∑ i ∈ s, (M i)ᴴ :=
  map_sum (conjTransposeAddEquiv m n α) _ s

variable (m n R α)

/-- `Matrix.conjTranspose` as a `LinearMap` -/
@[simps apply]
def conjTransposeLinearEquiv [CommSemiring R] [StarRing R] [AddCommMonoid α] [StarAddMonoid α]
    [Module R α] [StarModule R α] : Matrix m n α ≃ₗ⋆[R] Matrix n m α :=
  { conjTransposeAddEquiv m n α with map_smul' := conjTranspose_smul }

@[simp]
theorem conjTransposeLinearEquiv_symm [CommSemiring R] [StarRing R] [AddCommMonoid α]
    [StarAddMonoid α] [Module R α] [StarModule R α] :
    (conjTransposeLinearEquiv m n R α).symm = conjTransposeLinearEquiv n m R α :=
  rfl

variable {m n R α}
variable (m α)

/-- `Matrix.conjTranspose` as a `RingEquiv` to the opposite ring -/
@[simps]
def conjTransposeRingEquiv [Semiring α] [StarRing α] [Fintype m] :
    Matrix m m α ≃+* (Matrix m m α)ᵐᵒᵖ :=
  { (conjTransposeAddEquiv m m α).trans MulOpposite.opAddEquiv with
    toFun := fun M => MulOpposite.op Mᴴ
    invFun := fun M => M.unopᴴ
    map_mul' := fun M N =>
      (congr_arg MulOpposite.op (conjTranspose_mul M N)).trans (MulOpposite.op_mul _ _) }

variable {m α}

@[simp]
theorem conjTranspose_pow [Semiring α] [StarRing α] [Fintype m] [DecidableEq m] (M : Matrix m m α)
    (k : ℕ) : (M ^ k)ᴴ = Mᴴ ^ k :=
  MulOpposite.op_injective <| map_pow (conjTransposeRingEquiv m α) M k

theorem conjTranspose_list_prod [Semiring α] [StarRing α] [Fintype m] [DecidableEq m]
    (l : List (Matrix m m α)) : l.prodᴴ = (l.map conjTranspose).reverse.prod :=
  (conjTransposeRingEquiv m α).unop_map_list_prod l

end ConjTranspose

section Star

/-- When `α` has a star operation, square matrices `Matrix n n α` have a star
operation equal to `Matrix.conjTranspose`. -/
instance [Star α] : Star (Matrix n n α) where star := conjTranspose

theorem star_eq_conjTranspose [Star α] (M : Matrix m m α) : star M = Mᴴ :=
  rfl

@[simp]
theorem star_apply [Star α] (M : Matrix n n α) (i j) : (star M) i j = star (M j i) :=
  rfl

instance [InvolutiveStar α] : InvolutiveStar (Matrix n n α) where
  star_involutive := conjTranspose_conjTranspose

/-- When `α` is a `*`-additive monoid, `Matrix.star` is also a `*`-additive monoid. -/
instance [AddMonoid α] [StarAddMonoid α] : StarAddMonoid (Matrix n n α) where
  star_add := conjTranspose_add

instance [Star α] [Star β] [SMul α β] [StarModule α β] : StarModule α (Matrix n n β) where
  star_smul := conjTranspose_smul

/-- When `α` is a `*`-(semi)ring, `Matrix.star` is also a `*`-(semi)ring. -/
instance [Fintype n] [NonUnitalSemiring α] [StarRing α] : StarRing (Matrix n n α) where
  star_add := conjTranspose_add
  star_mul := conjTranspose_mul

/-- A version of `star_mul` for `*` instead of `*`. -/
theorem star_mul [Fintype n] [NonUnitalNonAssocSemiring α] [StarRing α] (M N : Matrix n n α) :
    star (M * N) = star N * star M :=
  conjTranspose_mul _ _

end Star

@[simp]
theorem conjTranspose_submatrix [Star α] (A : Matrix m n α) (r_reindex : l → m)
    (c_reindex : o → n) : (A.submatrix r_reindex c_reindex)ᴴ = Aᴴ.submatrix c_reindex r_reindex :=
  ext fun _ _ => rfl

theorem conjTranspose_reindex [Star α] (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    (reindex eₘ eₙ M)ᴴ = reindex eₙ eₘ Mᴴ :=
  rfl

end Matrix
