import Mathlib.Analysis.Normed.Ring.Seminorm
import Mathlib.Analysis.Seminorm
import Mathlib.RingTheory.Algebraic
import Mathlib.FieldTheory.Minpoly.Basic

/-
In this file, we state Maria and Fillipo's result. waiting for their work wo be merged into Mathlib.

-/

noncomputable section

def FunctionExtends {α : Type _} [CommRing α] (g : α → ℝ) {β : Type _} [Ring β] [Algebra α β]
    (f : β → ℝ) : Prop :=
  ∀ x : α, f (algebraMap α β x) = g x

/-- An algebra norm on an `R`-algebra norm `S` is a ring norm on `S` compatible with the
  action of `R`. -/
structure AlgebraNorm (R : Type _) [SeminormedCommRing R] (S : Type _) [Ring S]
    [Algebra R S] extends RingNorm S, Seminorm R S

attribute [nolint docBlame] AlgebraNorm.toSeminorm AlgebraNorm.toRingNorm

instance (K : Type _) [NormedField K] : Inhabited (AlgebraNorm K K) :=
  ⟨{  toFun     := norm
      map_zero' := norm_zero
      add_le'   := norm_add_le
      neg'      := norm_neg
      smul'     := norm_mul
      mul_le'   := norm_mul_le
      eq_zero_of_map_eq_zero' := fun _ => norm_eq_zero.mp }⟩

/-- `algebra_norm_class F α` states that `F` is a type of algebra norms on the ring `β`.
You should extend this class when you extend `algebra_norm`. -/
class AlgebraNormClass (F : Type _) (R : outParam <| Type _) [SeminormedCommRing R]
    (S : outParam <| Type _) [Ring S] [Algebra R S] [FunLike F S ℝ] extends RingNormClass F S ℝ,
    SeminormClass F R S

-- `R` is an `out_param`, so this is a false positive.
--attribute [nolint DangerousInstance] AlgebraNormClass.toRingNormClass

namespace AlgebraNorm

variable {R : Type _} [SeminormedCommRing R] {S : Type _} [Ring S] [Algebra R S]
  {f : AlgebraNorm R S}

/-- The ring_seminorm underlying an algebra norm. -/
def toRingSeminorm' (f : AlgebraNorm R S) : RingSeminorm S :=
  f.toRingNorm.toRingSeminorm

instance : FunLike (AlgebraNorm R S) S ℝ where
  coe f := f.toFun
  coe_injective' f f' h := by
    simp only [AddGroupSeminorm.toFun_eq_coe, RingSeminorm.toFun_eq_coe] at h
    cases f; cases f'; congr;
    simp only at h
    ext s
    erw [h]
    rfl

instance algebraNormClass : AlgebraNormClass (AlgebraNorm R S) R S where
  map_zero f        := f.map_zero'
  map_add_le_add f  := f.add_le'
  map_mul_le_mul f  := f.mul_le'
  map_neg_eq_map f  := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _
  map_smul_eq_mul f := f.smul'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : CoeFun (AlgebraNorm R S) fun _ => S → ℝ :=
  DFunLike.hasCoeToFun

theorem toFun_eq_coe (p : AlgebraNorm R S) : p.toFun = p := rfl

@[ext]
theorem ext {p q : AlgebraNorm R S} : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q

/-- An `R`-algebra norm such that `f 1 = 1` extends the norm on `R`. -/
theorem extends_norm' {f : AlgebraNorm R S} (hf1 : f 1 = 1) (a : R) : f (a • (1 : S)) = ‖a‖ := by
  rw [← mul_one ‖a‖, ← hf1]; exact f.smul' _ _

/-- An `R`-algebra norm such that `f 1 = 1` extends the norm on `R`. -/
theorem extends_norm {f : AlgebraNorm R S} (hf1 : f 1 = 1) (a : R) : f (algebraMap R S a) = ‖a‖ :=
  by rw [Algebra.algebraMap_eq_smul_one]; exact extends_norm' hf1 _

end AlgebraNorm

noncomputable
section spectralNorm

variable (K : Type _) [NormedField K] (L : Type _) [Field L] [Algebra K L]

variable {R : Type _} [SeminormedRing R]
open Polynomial

/-- The function `ℕ → ℝ` sending `n` to `‖ p.coeff n ‖^(1/(p.natDegree - n : ℝ))`, if
  `n < p.natDegree`, or to `0` otherwise. -/
def spectralValueTerms (p : R[X]) : ℕ → ℝ := fun n : ℕ =>
  if n < p.natDegree then ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)) else 0

/-- The spectral value of a polynomial in `R[X]`. -/
def spectralValue (p : R[X]) : ℝ :=
  iSup (spectralValueTerms p)

/-- The spectral norm `|y|_sp` is the spectral value of the minimal of `y` over `K`. -/
def spectralNorm (y : L) : ℝ :=
  spectralValue (minpoly K y)

/-- The `K`-algebra automorphisms of `L` are isometries with respect to the spectral norm. -/
theorem spectralNorm_aut_isom (σ : L ≃ₐ[K] L) (x : L) :
    spectralNorm K L x = spectralNorm K L (σ x) := by sorry

theorem spectralNorm_isNonarchimedean (h : IsNonarchimedean (norm : K → ℝ)) :
    IsNonarchimedean (spectralNorm K L) := by sorry

/-- The spectral norm extends the norm on `K`. -/
theorem spectralNorm_extends (k : K) : spectralNorm K L (algebraMap K L k) = ‖k‖ := sorry

variable {K L : Type _} [NormedField K] [Field L] [Algebra K L]

/-- The spectral norm is a `K`-algebra norm on `L`. -/
def spectralAlgNorm (hna : IsNonarchimedean (norm : K → ℝ)) :
    AlgebraNorm K L where
      toFun := spectralNorm K L
      map_zero' := sorry
      add_le' := sorry
      neg' := sorry
      mul_le' := sorry
      eq_zero_of_map_eq_zero' := sorry
      smul' := sorry



end spectralNorm

variable {K : Type _} [NontriviallyNormedField K] {L : Type _} [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

theorem spectral_norm_unique' [CompleteSpace K] {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hna : IsNonarchimedean (norm : K → ℝ)) : f = spectralAlgNorm hna := sorry

/-- If `K` is a field complete with respect to a nontrivial nonarchimedean multiplicative norm and
  `L/K` is an algebraic extension, then any multiplicative ring norm on `L` extending the norm on
  `K` coincides with the spectral norm. -/
theorem spectralNorm_unique_field_norm_ext [CompleteSpace K]
    {f : MulRingNorm L} (hf_ext : FunctionExtends (norm : K → ℝ) f)
    (hna : IsNonarchimedean (norm : K → ℝ)) (x : L) : f x = spectralNorm K L x := sorry

/-- `L` with the spectral norm is a `normed_field`. -/
def spectralNormToNormedField [CompleteSpace K] (h : IsNonarchimedean (norm : K → ℝ)) :
    NormedField L :=
  { (inferInstance : Field L) with
    norm := fun x : L => (spectralNorm K L x : ℝ)
    dist := fun x y : L => (spectralNorm K L (x - y) : ℝ)
    dist_self := sorry
    dist_comm := sorry
    dist_triangle := sorry
    edist_dist := sorry
    eq_of_dist_eq_zero := sorry
    dist_eq := sorry
    norm_mul' := sorry
  }

/-- `L` with the spectral norm is a `normed_add_comm_group`. -/
def spectralNormToNormedAddCommGroup [CompleteSpace K] (h : IsNonarchimedean (norm : K → ℝ)) :
     NormedAddCommGroup L :=
  by
  haveI : NormedField L := spectralNormToNormedField h
  infer_instance

/-- `L` with the spectral norm is a `seminormed_add_comm_group`. -/
def spectralNormToSeminormedAddCommGroup [CompleteSpace K] (h : IsNonarchimedean (norm : K → ℝ)) :
    SeminormedAddCommGroup L := by
  have : NormedField L := spectralNormToNormedField h
  infer_instance

/-- `L` with the spectral norm is a `normed_space` over `K`. -/
def spectralNormToNormedSpace [CompleteSpace K]
    (h : IsNonarchimedean (norm : K → ℝ)) :
    @NormedSpace K L _ (spectralNormToSeminormedAddCommGroup h) := sorry

/-- The metric space structure on `L` induced by the spectral norm. -/
def ms [CompleteSpace K] (h : IsNonarchimedean (norm : K → ℝ)) : MetricSpace L :=
  (spectralNormToNormedField h).toMetricSpace

/-- The uniform space structure on `L` induced by the spectral norm. -/
def us [CompleteSpace K] (h : IsNonarchimedean (norm : K → ℝ)) : UniformSpace L :=
  (ms h).toUniformSpace

-- normed_field.to_uniform_space
/-- If `L/K` is finite dimensional, then `L` is a complete space with respect to topology induced
  by the spectral norm. -/
instance (priority := 100) spectral_norm_completeSpace [CompleteSpace K]
    (h : IsNonarchimedean (norm : K → ℝ)) [h_fin : FiniteDimensional K L] :
    @CompleteSpace L (us h) := by
  letI := (spectralNormToNormedAddCommGroup (L := L) h)
  letI := (spectralNormToNormedSpace (L :=L) h)
  sorry--exact FiniteDimensional.complete K L

/-- A multiplicative algebra norm on an `R`-algebra norm `S` is a multiplicative ring norm on `S`
  compatible with the action of `R`. -/
structure MulAlgebraNorm (R : Type _) [SeminormedCommRing R] (S : Type _) [Ring S]
    [Algebra R S] extends MulRingNorm S, Seminorm R S

attribute [nolint docBlame] MulAlgebraNorm.toSeminorm MulAlgebraNorm.toMulRingNorm

-- FromMathlib.RingSeminorm
/-- The norm on a `normed_field`, as a `mul_ring_norm`. -/
def NormedField.toMulRingNorm (R : Type _) [NormedField R] : MulRingNorm R where
  toFun     := norm
  map_zero' := norm_zero
  map_one'  := norm_one
  add_le'   := norm_add_le
  map_mul'  := norm_mul
  neg'      := norm_neg
  eq_zero_of_map_eq_zero' x hx := by rw [← norm_eq_zero]; exact hx


/-- The spectral norm is a multiplicative `K`-algebra norm on `L`.-/
def spectralMulAlgNorm [CompleteSpace K] (hna : IsNonarchimedean (norm : K → ℝ)) :
    MulAlgebraNorm K L :=
  { spectralAlgNorm hna with
    map_one' := sorry--spectralAlgNorm_is_norm_one_class hna
    map_mul' := sorry }
