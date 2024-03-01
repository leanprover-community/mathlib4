import Mathlib.Topology.GMetric.WellSpaced
import Mathlib.Topology.GMetric.Isometry
import Mathlib.Topology.GMetric.GNorm
import Mathlib.InformationTheory.Hamming

open Set
open GMetric

section hamming
variable {ι K:Type*} [Fintype ι] [DecidableEq K]

abbrev hdist :GMetric (∀ _:ι,K) ℕ∞ := hammingENatDist

-- maybe sensitive to universe problems? because the choice of ι is *very* unimportant
def trivdist : GMetric K ℕ∞ where
  toFun := fun x y => hammingENatDist (Function.const (Fin 1) x) (Function.const (Fin 1) y)
  gdist_self := fun x => by simp
  comm' := fun x y => by
    apply hammingENatDist.comm'
  triangle' := fun x y z => by apply hammingENatDist.triangle'
  eq_of_dist_eq_zero := by simp

@[simp, push_cast]
theorem trivdist_eq_cast_hammingDist (x y : K) :
    trivdist x y = hammingENatDist (Function.const (Fin 1) x) (Function.const (Fin 1) y) :=
  rfl

instance Hamming.instAddGNorm [AddMonoid K] [IsCancelAdd K]: AddGNorm (∀ _:ι,K) ℕ∞ hdist where
  gdist_absorb_add := fun z => by
    ext x y
    rw [Function.onFun]
    simp only [hammingENatdist_eq_cast_hammingDist, Nat.cast_inj]
    rw[hammingDist,hammingDist]
    simp

-- prefer [AddMonoid K] [IsCancelAdd K] over [CancelAddMonoid],
-- because i want [Semiring K] and [IsCancelAdd K]
instance trivdist.instAddGNorm [AddMonoid K] [IsCancelAdd K]: AddGNorm K ℕ∞ trivdist where
  gdist_absorb_add := fun z => by
    ext x y
    rw [Function.onFun]
    simp only [trivdist_eq_cast_hammingDist, hammingENatdist_eq_cast_hammingDist, Nat.cast_inj]
    rw [hammingDist,hammingDist]
    simp

lemma trivdist_eq (x y:K): trivdist x y = if x = y then 0 else 1 := by
  if h:x=y then
    rw [h]
    simp
  else
    simp only [trivdist_eq_cast_hammingDist, hammingENatdist_eq_cast_hammingDist]
    rw [hammingDist]
    simp_all

-- noncomputable because we depend on CompleteLinearOrder ENat
-- i'm not sure this is how this should be, but who knows
noncomputable instance Hamming.instStrictModuleGNorm_SemiRing_Domain
    [Semiring K] [IsDomain K] [IsCancelAdd K]: StrictModuleGNorm K K trivdist trivdist where
  norm_smul_le' := fun a b => by
    apply Eq.le
    rw [addGNorm,addGNorm,addGNorm]
    rw [trivdist_eq,trivdist_eq,trivdist_eq]
    simp only [smul_eq_mul, mul_eq_zero, mul_ite, mul_zero, mul_one]
    if ha:a=0 then
      rw [ha]
      simp only [true_or, ↓reduceIte, ite_self]
    else if hb:b=0 then
      rw [hb]
      simp only [or_true, ↓reduceIte]
    else
      simp_all only [or_self, ite_false]
  smul_norm_le' := fun a b => by
    apply Eq.le
    rw [addGNorm,addGNorm,addGNorm]
    rw [trivdist_eq,trivdist_eq,trivdist_eq]
    simp only [smul_eq_mul, mul_eq_zero, mul_ite, mul_zero, mul_one]
    if ha:a=0 then
      rw [ha]
      simp only [true_or, ↓reduceIte, ite_self]
    else if hb:b=0 then
      rw [hb]
      simp only [or_true, ↓reduceIte]
    else
      simp_all only [or_self, ite_false]


-- look into: hamming distance as measure on the set of indices where the things differ
-- look into: hamming distance as the sum of trivial distances in each of the dimensions

private lemma norm_eq_smul
    [Semiring K] [IsCancelAdd K] [IsDomain K] (a : K) (b : ι → K) :
    addGNorm hdist (a • b) = addGNorm trivdist a * addGNorm hdist b := by
  rw [addGNorm,addGNorm,addGNorm]
  if ha:a=0 then
    rw [ha]
    simp_all
  else if hb:b=0 then
    rw [hb]
    simp_all
  else
    simp_all
    rw [hammingNorm,hammingNorm,hammingNorm]
    simp_all

noncomputable instance Hamming.instStrictModuleGNorm_Module
    [Semiring K] [IsCancelAdd K] [IsDomain K]: StrictModuleGNorm K (ι → K) trivdist hdist where
  norm_smul_le' := fun a b => (norm_eq_smul a b).le
  smul_norm_le' := fun a b => (norm_eq_smul a b).ge


end hamming

section code_def
-- these are all the parameters needed to assume s ⊆ α.univ is a code with metric to γ

-- [LinearlyOrderedAddCommMonoid γ] [CompleteLinearOrder γ] but no diamond
variable {γ : Type*} [CompleteLinearOrder γ] [AddCommMonoid γ] [CovariantClass γ γ (.+.) (.≤.)]

-- [PseudoMetricSpace M]
variable {M : Type*}
variable {Tₘ : Type*} [FunLike Tₘ M (M → γ)] [GPseudoMetricClass Tₘ M γ]
variable (gdist:Tₘ)

--
variable (s:Set M) {hdel:IsDelone gdist s}

end code_def

section linearcode
-- these are the variables needed to assume that s ⊆ M.univ is a K-linear code with metrics to γ

-- [LinearlyOrderedSemiRing γ] [CompleteLinearOrder γ] but no diamond
variable {γ : Type*} [Nontrivial γ] [CompleteLinearOrder γ] [Semiring γ]
variable [CovariantClass γ γ (.+.) (.≤.)] [ContravariantClass γ γ (.+.) (.≤.)]
variable [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ]

-- [NormedField K]
variable {K : Type*} [Field K]
variable {Tₖ : Type*} [FunLike Tₖ K (K → γ)] [GPseudoMetricClass Tₖ K γ]
variable (gdist_k:Tₖ) [AddGNorm K γ gdist_k] [StrictModuleGNorm K K gdist_k gdist_k]

-- [NormedSpace K M]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable {Tₘ : Type*} [FunLike Tₘ M (M → γ)] [GPseudoMetricClass Tₘ M γ]
variable (gdist_m:Tₘ) [AddGNorm M γ gdist_m] [StrictModuleGNorm K M gdist_k gdist_m]

--
variable (s : Submodule K M) {hdel:IsDelone gdist_m s}
end linearcode
