module

public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Analysis.Normed.Operator.Bilinear

public section

variable {ι R M M₂ : Type*} [NontriviallyNormedField R] [SeminormedAddCommGroup M] [NormedSpace R M]
  [SeminormedAddCommGroup M₂] [NormedSpace R M₂]

theorem ContinuousLinearMap.hasSum_apply {f : ι → M →L[R] M₂} {g : M →L[R] M₂} (hf : HasSum f g)
    (x : M) :
    HasSum (f · x) (g x) :=
  (ContinuousLinearMap.apply R M₂ x).hasSum hf

theorem ContinuousLinearMap.summable_apply {f : ι → M →L[R] M₂} (hf : Summable f) (x : M) :
    Summable (f · x) :=
  (ContinuousLinearMap.apply R M₂ x).summable hf

theorem ContinuousLinearMap.tsum_apply [T2Space M₂] {f : ι → M →L[R] M₂} (hf : Summable f) (x : M) :
    (∑' n, f n) x = ∑' n, f n x :=
  (ContinuousLinearMap.apply R M₂ x).map_tsum hf
