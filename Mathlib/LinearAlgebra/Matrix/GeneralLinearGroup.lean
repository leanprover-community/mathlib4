/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Algebra.Ring.Subring.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Matrix.Rank
import Mathlib.RingTheory.LittleWedderburn

#align_import linear_algebra.matrix.general_linear_group from "leanprover-community/mathlib"@"2705404e701abc6b3127da906f40bae062a169c9"

/-!
# The General Linear group $GL(n, R)$

This file defines the elements of the General Linear group `Matrix.GeneralLinearGroup n R`,
consisting of all invertible `n` by `n` `R`-matrices.

## Main definitions

* `Matrix.GeneralLinearGroup` is the type of matrices over R which are units in the matrix ring.
* `Matrix.GLPos` gives the subgroup of matrices with
  positive determinant (over a linear ordered ring).

## Tags

matrix group, group, matrix inverse
-/


namespace Matrix

universe u v

open Matrix

open LinearMap

-- disable this instance so we do not accidentally use it in lemmas.
attribute [-instance] SpecialLinearGroup.instCoeFun

/-- `GL n R` is the group of `n` by `n` `R`-matrices with unit determinant.
Defined as a subtype of matrices-/
abbrev GeneralLinearGroup (n : Type u) (R : Type v) [DecidableEq n] [Fintype n] [CommRing R] :
    Type _ :=
  (Matrix n n R)ˣ
#align matrix.general_linear_group Matrix.GeneralLinearGroup

@[inherit_doc] notation "GL" => GeneralLinearGroup

namespace GeneralLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

section CoeFnInstance

-- Porting note: this instance was not the simp-normal form in mathlib3 but it is fine in mathlib4
-- because coercions get unfolded.
/-- This instance is here for convenience, but is not the simp-normal form. -/
instance instCoeFun : CoeFun (GL n R) fun _ => n → n → R where
  coe A := (A : Matrix n n R)

end CoeFnInstance

/-- The determinant of a unit matrix is itself a unit. -/
@[simps]
def det : GL n R →* Rˣ where
  toFun A :=
    { val := (↑A : Matrix n n R).det
      inv := (↑A⁻¹ : Matrix n n R).det
      val_inv := by rw [← det_mul, A.mul_inv, det_one]
      inv_val := by rw [← det_mul, A.inv_mul, det_one] }
  map_one' := Units.ext det_one
  map_mul' A B := Units.ext <| det_mul _ _
#align matrix.general_linear_group.det Matrix.GeneralLinearGroup.det
#align matrix.general_linear_group.coe_det_apply Matrix.GeneralLinearGroup.val_det_apply

/-- The `GL n R` and `Matrix.GeneralLinearGroup R n` groups are multiplicatively equivalent-/
def toLin : GL n R ≃* LinearMap.GeneralLinearGroup R (n → R) :=
  Units.mapEquiv toLinAlgEquiv'.toMulEquiv
#align matrix.general_linear_group.to_lin Matrix.GeneralLinearGroup.toLin

/-- Given a matrix with invertible determinant we get an element of `GL n R`-/
def mk' (A : Matrix n n R) (_ : Invertible (Matrix.det A)) : GL n R :=
  unitOfDetInvertible A
#align matrix.general_linear_group.mk' Matrix.GeneralLinearGroup.mk'

/-- Given a matrix with unit determinant we get an element of `GL n R`-/
noncomputable def mk'' (A : Matrix n n R) (h : IsUnit (Matrix.det A)) : GL n R :=
  nonsingInvUnit A h
#align matrix.general_linear_group.mk'' Matrix.GeneralLinearGroup.mk''

/-- Given a matrix with non-zero determinant over a field, we get an element of `GL n K`-/
def mkOfDetNeZero {K : Type*} [Field K] (A : Matrix n n K) (h : Matrix.det A ≠ 0) : GL n K :=
  mk' A (invertibleOfNonzero h)
#align matrix.general_linear_group.mk_of_det_ne_zero Matrix.GeneralLinearGroup.mkOfDetNeZero

theorem ext_iff (A B : GL n R) : A = B ↔ ∀ i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j :=
  Units.ext_iff.trans Matrix.ext_iff.symm
#align matrix.general_linear_group.ext_iff Matrix.GeneralLinearGroup.ext_iff

/-- Not marked `@[ext]` as the `ext` tactic already solves this. -/
theorem ext ⦃A B : GL n R⦄ (h : ∀ i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j) : A = B :=
  Units.ext <| Matrix.ext h
#align matrix.general_linear_group.ext Matrix.GeneralLinearGroup.ext

section CoeLemmas

variable (A B : GL n R)

@[simp]
theorem coe_mul : ↑(A * B) = (↑A : Matrix n n R) * (↑B : Matrix n n R) :=
  rfl
#align matrix.general_linear_group.coe_mul Matrix.GeneralLinearGroup.coe_mul

@[simp]
theorem coe_one : ↑(1 : GL n R) = (1 : Matrix n n R) :=
  rfl
#align matrix.general_linear_group.coe_one Matrix.GeneralLinearGroup.coe_one

theorem coe_inv : ↑A⁻¹ = (↑A : Matrix n n R)⁻¹ :=
  letI := A.invertible
  invOf_eq_nonsing_inv (↑A : Matrix n n R)
#align matrix.general_linear_group.coe_inv Matrix.GeneralLinearGroup.coe_inv

/-- An element of the matrix general linear group on `(n) [Fintype n]` can be considered as an
element of the endomorphism general linear group on `n → R`. -/
def toLinear : GeneralLinearGroup n R ≃* LinearMap.GeneralLinearGroup R (n → R) :=
  Units.mapEquiv Matrix.toLinAlgEquiv'.toRingEquiv.toMulEquiv
#align matrix.general_linear_group.to_linear Matrix.GeneralLinearGroup.toLinear

-- Note that without the `@` and `‹_›`, Lean infers `fun a b ↦ _inst a b` instead of `_inst` as the
-- decidability argument, which prevents `simp` from obtaining the instance by unification.
-- These `fun a b ↦ _inst a b` terms also appear in the type of `A`, but simp doesn't get confused
-- by them so for now we do not care.
@[simp]
theorem coe_toLinear : (@toLinear n ‹_› ‹_› _ _ A : (n → R) →ₗ[R] n → R) = Matrix.mulVecLin A :=
  rfl
#align matrix.general_linear_group.coe_to_linear Matrix.GeneralLinearGroup.coe_toLinear

-- Porting note: is inserting toLinearEquiv here correct?
@[simp]
theorem toLinear_apply (v : n → R) : (toLinear A).toLinearEquiv v = Matrix.mulVecLin (↑A) v :=
  rfl
#align matrix.general_linear_group.to_linear_apply Matrix.GeneralLinearGroup.toLinear_apply

end CoeLemmas

variable {S T : Type*} [CommRing S] [CommRing T]

/-- A ring homomorphism ``f : R →+* S`` induces a homomorphism ``GLₙ(f) : GLₙ(R) →* GLₙ(S)``. -/
def map (f : R →+* S) : GL n R →* GL n S := Units.map <| (RingHom.mapMatrix f).toMonoidHom

@[simp]
theorem map_id : map (RingHom.id R) = MonoidHom.id (GL n R) :=
  rfl

@[simp]
theorem map_comp (f : T →+* R) (g : R →+* S) :
    map (g.comp f) = (map g).comp (map (n := n) f) :=
  rfl

@[simp]
theorem map_comp_apply (f : T →+* R) (g : R →+* S) (x : GL n T) :
    (map g).comp (map f) x = map g (map f x) :=
  rfl

end GeneralLinearGroup

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

-- Porting note: added implementation for the Coe
/-- The map from SL(n) to GL(n) underlying the coercion, forgetting the value of the determinant.
-/
@[coe]
def coeToGL (A : SpecialLinearGroup n R) : GL n R :=
  ⟨↑A, ↑A⁻¹,
    congr_arg ((↑) : _ → Matrix n n R) (mul_right_inv A),
    congr_arg ((↑) : _ → Matrix n n R) (mul_left_inv A)⟩

instance hasCoeToGeneralLinearGroup : Coe (SpecialLinearGroup n R) (GL n R) :=
  ⟨coeToGL⟩
#align matrix.special_linear_group.has_coe_to_general_linear_group Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup

@[simp]
theorem coeToGL_det (g : SpecialLinearGroup n R) :
    Matrix.GeneralLinearGroup.det (g : GL n R) = 1 :=
  Units.ext g.prop
set_option linter.uppercaseLean3 false in
#align matrix.special_linear_group.coe_to_GL_det Matrix.SpecialLinearGroup.coeToGL_det

end SpecialLinearGroup

section

variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n] [LinearOrderedCommRing R]

section

variable (n R)

/-- This is the subgroup of `nxn` matrices with entries over a
linear ordered ring and positive determinant. -/
def GLPos : Subgroup (GL n R) :=
  (Units.posSubgroup R).comap GeneralLinearGroup.det
set_option linter.uppercaseLean3 false in
#align matrix.GL_pos Matrix.GLPos

end

@[simp]
theorem mem_glpos (A : GL n R) : A ∈ GLPos n R ↔ 0 < (Matrix.GeneralLinearGroup.det A : R) :=
  Iff.rfl
set_option linter.uppercaseLean3 false in
#align matrix.mem_GL_pos Matrix.mem_glpos

theorem GLPos.det_ne_zero (A : GLPos n R) : ((A : GL n R) : Matrix n n R).det ≠ 0 :=
  ne_of_gt A.prop
set_option linter.uppercaseLean3 false in
#align matrix.GL_pos.det_ne_zero Matrix.GLPos.det_ne_zero

end

section Neg

variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n] [LinearOrderedCommRing R]
  [Fact (Even (Fintype.card n))]

/-- Formal operation of negation on general linear group on even cardinality `n` given by negating
each element. -/
instance : Neg (GLPos n R) :=
  ⟨fun g =>
    ⟨-g, by
      rw [mem_glpos, GeneralLinearGroup.val_det_apply, Units.val_neg, det_neg,
        (Fact.out (p := Even <| Fintype.card n)).neg_one_pow, one_mul]
      exact g.prop⟩⟩

@[simp]
theorem GLPos.coe_neg_GL (g : GLPos n R) : ↑(-g) = -(g : GL n R) :=
  rfl
set_option linter.uppercaseLean3 false in
#align matrix.GL_pos.coe_neg_GL Matrix.GLPos.coe_neg_GL

@[simp]
theorem GLPos.coe_neg (g : GLPos n R) : (↑(-g) : GL n R) = -((g : GL n R) : Matrix n n R) :=
  rfl
set_option linter.uppercaseLean3 false in
#align matrix.GL_pos.coe_neg Matrix.GLPos.coe_neg

@[simp]
theorem GLPos.coe_neg_apply (g : GLPos n R) (i j : n) :
    ((↑(-g) : GL n R) : Matrix n n R) i j = -((g : GL n R) : Matrix n n R) i j :=
  rfl
set_option linter.uppercaseLean3 false in
#align matrix.GL_pos.coe_neg_apply Matrix.GLPos.coe_neg_apply

instance : HasDistribNeg (GLPos n R) :=
  Subtype.coe_injective.hasDistribNeg _ GLPos.coe_neg_GL (GLPos n R).coe_mul

end Neg

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [LinearOrderedCommRing R]

/-- `Matrix.SpecialLinearGroup n R` embeds into `GL_pos n R` -/
def toGLPos : SpecialLinearGroup n R →* GLPos n R where
  toFun A := ⟨(A : GL n R), show 0 < (↑A : Matrix n n R).det from A.prop.symm ▸ zero_lt_one⟩
  map_one' := Subtype.ext <| Units.ext <| rfl
  map_mul' _ _ := Subtype.ext <| Units.ext <| rfl
set_option linter.uppercaseLean3 false in
#align matrix.special_linear_group.to_GL_pos Matrix.SpecialLinearGroup.toGLPos

instance : Coe (SpecialLinearGroup n R) (GLPos n R) :=
  ⟨toGLPos⟩

#noalign matrix.special_linear_group.coe_eq_to_GL_pos

theorem toGLPos_injective : Function.Injective (toGLPos : SpecialLinearGroup n R → GLPos n R) :=
  -- Porting note: had to rewrite this to hint the correct types to Lean
  -- (It can't find the coercion GLPos n R → Matrix n n R)
  Function.Injective.of_comp
    (f := fun (A : GLPos n R) ↦ ((A : GL n R) : Matrix n n R))
    (show Function.Injective (_ ∘ (toGLPos : SpecialLinearGroup n R → GLPos n R))
      from Subtype.coe_injective)
set_option linter.uppercaseLean3 false in
#align matrix.special_linear_group.to_GL_pos_injective Matrix.SpecialLinearGroup.toGLPos_injective

/-- Coercing a `Matrix.SpecialLinearGroup` via `GL_pos` and `GL` is the same as coercing straight to
a matrix. -/
@[simp]
theorem coe_GLPos_coe_GL_coe_matrix (g : SpecialLinearGroup n R) :
    (↑(↑(↑g : GLPos n R) : GL n R) : Matrix n n R) = ↑g :=
  rfl
set_option linter.uppercaseLean3 false in
#align matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix Matrix.SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix

@[simp]
theorem coe_to_GLPos_to_GL_det (g : SpecialLinearGroup n R) :
    Matrix.GeneralLinearGroup.det ((g : GLPos n R) : GL n R) = 1 :=
  Units.ext g.prop
set_option linter.uppercaseLean3 false in
#align matrix.special_linear_group.coe_to_GL_pos_to_GL_det Matrix.SpecialLinearGroup.coe_to_GLPos_to_GL_det

variable [Fact (Even (Fintype.card n))]

@[norm_cast]
theorem coe_GLPos_neg (g : SpecialLinearGroup n R) : ↑(-g) = -(↑g : GLPos n R) :=
  Subtype.ext <| Units.ext rfl
set_option linter.uppercaseLean3 false in
#align matrix.special_linear_group.coe_GL_pos_neg Matrix.SpecialLinearGroup.coe_GLPos_neg

end SpecialLinearGroup

section Examples

/-- The matrix [a, -b; b, a] (inspired by multiplication by a complex number); it is an element of
$GL_2(R)$ if `a ^ 2 + b ^ 2` is nonzero. -/
@[simps! (config := .asFn) val]
def planeConformalMatrix {R} [Field R] (a b : R) (hab : a ^ 2 + b ^ 2 ≠ 0) :
    Matrix.GeneralLinearGroup (Fin 2) R :=
  GeneralLinearGroup.mkOfDetNeZero !![a, -b; b, a] (by simpa [det_fin_two, sq] using hab)
#align matrix.plane_conformal_matrix Matrix.planeConformalMatrix

/- TODO: Add Iwasawa matrices `n_x=!![1,x; 0,1]`, `a_t=!![exp(t/2),0;0,exp(-t/2)]` and
  `k_θ=!![cos θ, sin θ; -sin θ, cos θ]`
-/
end Examples


section LinearIndependant

variable {K : Type*} {V : Type*} [DivisionRing K] [AddCommGroup V]
variable [Module K V]

/-- Equivalence between `k + 1` vectors of length `n` and `k` vectors of length `n` along with a
vector in the complement of their span.
-/
def inductiveStepEquiv {k : ℕ} :
    { s : Fin (k + 1) → V // LinearIndependent K s } ≃
      Σ s : { s : Fin k → V // LinearIndependent K s },
        ((Submodule.span K (Set.range (s : Fin k → V)))ᶜ : Set V) where
  toFun s := ⟨⟨Fin.tail s.val, (linearIndependent_fin_succ.mp s.property).left⟩,
    ⟨s.val 0, (linearIndependent_fin_succ.mp s.property).right⟩⟩
  invFun s := ⟨Fin.cons s.2.val s.1.val,
    linearIndependent_fin_cons.mpr ⟨s.1.property, s.2.property⟩⟩
  left_inv _ := by simp only [Fin.cons_self_tail, Subtype.coe_eta]
  right_inv := fun ⟨_, _⟩ => by simp only [Fin.cons_zero, Subtype.coe_eta, Sigma.mk.inj_iff,
    Fin.tail_cons, heq_eq_eq, and_self]

variable [Fintype K] [Fintype V]

local notation "q" => Fintype.card K
local notation "n" => FiniteDimensional.finrank K V

attribute [local instance] Fintype.ofFinite in
open Fintype in
lemma card_LinearInependent_subtype {k : ℕ} (hk : k ≤ n) :
    Nat.card { s : Fin k → V // LinearIndependent K s } =
      ∏ i : Fin k, ((q) ^ n - (q) ^ i.val) := by
  rw [Nat.card_eq_fintype_card]
  induction k with
  | zero => simp only [LinearIndependent, Finsupp.total_fin_zero, ker_zero, card_ofSubsingleton,
      Finset.univ_eq_empty, Finset.prod_empty]
  | succ k ih =>
      have (s : { s : Fin k → V // LinearIndependent K s }) :
          card ((Submodule.span K (Set.range (s : Fin k → V)))ᶜ : Set (V)) =
          (q) ^ n - (q) ^ k := by
            rw [card_compl_set, card_eq_pow_finrank (K := K)
            (V:=((Submodule.span K (Set.range (s : Fin k → V))) : Set (V)))]
            simp only [SetLike.coe_sort_coe, finrank_span_eq_card s.2, card_fin]
            rw [card_eq_pow_finrank (K := K)]
      simp [card_congr (inductiveStepEquiv), sum_congr _ _ this, ih (Nat.le_of_succ_le hk),
        mul_comm, Fin.prod_univ_succAbove _ k]

end LinearIndependant

section cardinal

variable (n : ℕ) {𝔽 : Type*} [DivisionRing 𝔽] [Fintype 𝔽]

local notation "q" => Fintype.card 𝔽

/-- Equivalence between `GL n F` and `n` vectors of length `n` that are linearly independent. Given
by sending a matrix to its coloumns. -/
noncomputable def equiv_GL_linearindependent (hn : 0 < n) :
    GL (Fin n) 𝔽 ≃ { s : Fin n → (Fin n → 𝔽) // LinearIndependent 𝔽 s } where
  toFun M := ⟨transpose M, by
    apply linearIndependent_iff_card_eq_finrank_span.2
    rw [Set.finrank, ← rank_eq_finrank_span_cols, rank_unit]⟩
  invFun M := GeneralLinearGroup.mk'' (transpose (M.1)) <| by
    have : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 hn
    rw [← Basis.coePiBasisFun.toMatrix_eq_transpose,
      ← coe_basisOfLinearIndependentOfCardEqFinrank M.2]
    let b := basisOfLinearIndependentOfCardEqFinrank M.2 (by simp)
    have := (Pi.basisFun 𝔽 (Fin n)).invertibleToMatrix b
    exact isUnit_det_of_invertible _
  left_inv := fun x ↦ Units.ext (ext fun i j ↦ rfl)
  right_inv := by exact congrFun rfl

theorem card_GL : Nat.card (GL (Fin n) 𝔽) = ∏ i : (Fin n), (q ^ (n) - q ^ ( i : ℕ )) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.card_eq_fintype_card]
  · rw [Nat.card_congr (equiv_GL_linearindependent n hn), card_LinearInependent_subtype,
    FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]
    simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin, le_refl]

end cardinal

end Matrix
