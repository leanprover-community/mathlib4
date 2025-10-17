import Mathlib.Topology.Algebra.TopologicallyNilpotent
import Mathlib.Topology.Algebra.UniformRing

open Filter
open scoped Uniformity Topology

class IsLinearUniformity (R : Type*) [Semiring R] [UniformSpace R] where
  hasBasis_ringCon : (𝓤 R).HasBasis
    (fun 𝓡 : RingCon R ↦ {xy : R × R | 𝓡 xy.1 xy.2} ∈ 𝓤 R)
    (fun 𝓡 : RingCon R ↦ {xy : R × R | 𝓡 xy.1 xy.2})

-- TODO: better name
def RingCon.ideal {R : Type*} [Semiring R] (𝓡 : RingCon R) : Ideal R where
  carrier := {x | 𝓡 x 0}
  zero_mem' := 𝓡.refl 0
  add_mem' hx hy := by simpa using 𝓡.add hx hy
  smul_mem' x y hy := by simpa using 𝓡.mul (𝓡.refl x) hy

theorem IsLinearUniformity.hasBasis_nhds_zero
    {R : Type*} [Semiring R] [UniformSpace R] [IsLinearUniformity R] :
    (𝓝 0 : Filter R).HasBasis
      (fun 𝓡 : RingCon R ↦ {xy : R × R | 𝓡 xy.1 xy.2} ∈ 𝓤 R)
      (fun 𝓡 ↦ 𝓡.ideal) :=
  nhds_basis_uniformity IsLinearUniformity.hasBasis_ringCon

theorem IsLinearUniformity.tendsto_mul_right_uniformity
    {R : Type*} [Semiring R] [UniformSpace R] [IsLinearUniformity R]
    {ι : Type*} {f : Filter ι}
    (a : ι → R × R) (b : ι → R) (ha : Tendsto a f (𝓤 R)) :
    Tendsto (fun i ↦ ((a i).1 * b i, (a i).2 * b i)) f (𝓤 R) := by
  rw [IsLinearUniformity.hasBasis_ringCon.tendsto_right_iff]
  intro 𝓡 h𝓡
  filter_upwards [ha.eventually h𝓡] using fun i hi ↦ 𝓡.mul hi <| 𝓡.refl _

theorem IsLinearUniformity.tendsto_mul_left_uniformity
    {R : Type*} [Semiring R] [UniformSpace R] [IsLinearUniformity R]
    {ι : Type*} {f : Filter ι}
    (a : ι → R × R) (b : ι → R) (ha : Tendsto a f (𝓤 R)) :
    Tendsto (fun i ↦ ((a i).1 * b i, (a i).2 * b i)) f (𝓤 R) := by
  rw [IsLinearUniformity.hasBasis_ringCon.tendsto_right_iff]
  intro 𝓡 h𝓡
  filter_upwards [ha.eventually h𝓡] using fun i hi ↦ 𝓡.mul hi <| 𝓡.refl _
