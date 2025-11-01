import Mathlib.Algebra.Module.Congruence.Defs
import Mathlib.Topology.Algebra.TopologicallyNilpotent
import Mathlib.Topology.Algebra.UniformRing

open Filter
open scoped Uniformity Topology

-- TODO: better name
def RingCon.ideal {R : Type*} [Semiring R] (𝓡 : RingCon R) : Ideal R where
  carrier := {x | 𝓡 x 0}
  zero_mem' := 𝓡.refl 0
  add_mem' hx hy := by simpa using 𝓡.add hx hy
  smul_mem' x y hy := by simpa using 𝓡.mul (𝓡.refl x) hy

-- TODO: better name
def ModuleCon.submodule {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (𝓡 : ModuleCon R M) : Submodule R M where
  carrier := {x | 𝓡 x 0}
  zero_mem' := 𝓡.refl 0
  add_mem' hx hy := by simpa using 𝓡.add hx hy
  smul_mem' x y hy := by simpa using 𝓡.smul x hy

namespace IsLinearUniformity

section Module

variable {R R' M : Type*} [Semiring R] [Semiring R'] [AddCommMonoid M] [Module R M] [Module R' M]
  [SMulCommClass R R' M] [UniformSpace M]

variable (R M) in
/-- Consider a (left-)module `M` over a ring `R`. A topology on `M` is *`R`-linear*
if the open sub-`R`-modules of `M` form a basis of neighborhoods of zero.

Typically one would also that the topology is invariant by translation (`ContinuousConstVAdd M M`),
or equivalently that `M` is a topological group, but we do not assume it for the definition.

In particular, we say that a topology on the ring `R` is *linear* if it is both
`R`-linear and `Rᵐᵒᵖ`-linear for the obvious module structures. To spell this in Lean,
simply use `[IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R]`. -/
class _root_.IsLinearUniformity where
  hasBasis_moduleCon' : (𝓤 M).HasBasis
    (fun 𝓡 : ModuleCon R M ↦ {xy : M × M | 𝓡 xy.1 xy.2} ∈ 𝓤 M)
    (fun 𝓡 : ModuleCon R M ↦ {xy : M × M | 𝓡 xy.1 xy.2})

variable (R) in
lemma hasBasis_moduleCon [IsLinearUniformity R M] : (𝓤 M).HasBasis
    (fun 𝓡 : ModuleCon R M ↦ {xy : M × M | 𝓡 xy.1 xy.2} ∈ 𝓤 M)
    (fun 𝓡 : ModuleCon R M ↦ {xy : M × M | 𝓡 xy.1 xy.2}) :=
  IsLinearUniformity.hasBasis_moduleCon'

variable (R) in
/-- To show that `M` is linearly-topologized as an `R`-module, it suffices to show
that it has a basis of neighborhoods of zero made of `R`-submodules. -/
lemma mk_of_hasBasis_moduleCon {ι : Sort*} {p : ι → Prop} (𝓡 : ι → ModuleCon R M)
    (h : (𝓤 M).HasBasis p (fun i ↦ {xy : M × M | 𝓡 i xy.1 xy.2})) :
    IsLinearUniformity R M where
  hasBasis_moduleCon' := h.to_hasBasis
    (fun i hi ↦ ⟨𝓡 i, h.mem_of_mem hi, subset_rfl⟩)
    (fun _ ↦ h.mem_iff.mp)

theorem _root_.isLinearUniformity_iff_hasBasis_moduleCon :
    IsLinearUniformity R M ↔ (𝓤 M).HasBasis
      (fun 𝓡 : ModuleCon R M ↦ {xy : M × M | 𝓡 xy.1 xy.2} ∈ 𝓤 M)
      (fun 𝓡 : ModuleCon R M ↦ {xy : M × M | 𝓡 xy.1 xy.2}) :=
  ⟨fun _ ↦ hasBasis_moduleCon R, fun h ↦ .mk_of_hasBasis_moduleCon R _ h⟩

variable (R) in
theorem hasBasis_nhds_zero [IsLinearUniformity R M] :
    (𝓝 0 : Filter M).HasBasis
      (fun 𝓡 : ModuleCon R M ↦ {xy : M × M | 𝓡 xy.1 xy.2} ∈ 𝓤 M)
      (fun 𝓡 ↦ 𝓡.submodule) :=
  nhds_basis_uniformity <| IsLinearUniformity.hasBasis_moduleCon R

instance [IsLinearUniformity R M] : IsLinearTopology R M :=
  .mk_of_hasBasis R (hasBasis_nhds_zero R)

-- TODO: add `⊥` as a `ModuleCon`
/-- The discrete uniformity on any `R`-module is `R`-linear. -/
instance [DiscreteUniformity M] : IsLinearUniformity R M :=
  have : HasBasis (𝓤 M) (fun _ ↦ True) (fun (_ : Unit) ↦ SetRel.id) := by
    rw [DiscreteUniformity.eq_principal_relId]
    exact hasBasis_principal _
  mk_of_hasBasis_moduleCon R (fun _ ↦ ⟨⊥, fun s _ _ heq ↦ heq ▸ rfl⟩) this

variable (R R' M) in
open Set Pointwise in
/-- Assume that `M` is a module over two rings `R` and `R'`, and that its topology
is linear with respect to each of these rings. Then, it has a basis of neighborhoods of zero
made of sub-`(R, R')`-bimodules.

The proof is inspired by lemma 9 in [I. Kaplansky, *Topological Rings*](kaplansky_topological_1947).
TODO: Formalize the lemma in its full strength.

Note: due to the lack of a satisfying theory of sub-bimodules, we use `AddSubmonoid`s with
extra conditions. -/
lemma hasBasis_bimoduleCon [IsLinearUniformity R M] [IsLinearUniformity R' M] :
    (𝓤 M).HasBasis
      (fun 𝓡 : AddCon M ↦ {xy : M × M | 𝓡 xy.1 xy.2} ∈ 𝓤 M ∧
        (∀ r : R, ∀ x y, 𝓡 x y → 𝓡 (r • x) (r • y)) ∧
        (∀ r' : R', ∀ x y, 𝓡 x y → 𝓡 (r' • x) (r' • y)))
      (fun 𝓡 : AddCon M ↦ {xy : M × M | 𝓡 xy.1 xy.2}) := by
  -- Start from a neighborhood `V`. It contains some open sub-`R`-module `I`.
  refine hasBasis_moduleCon R |>.to_hasBasis (fun I hI ↦ ?_)
    (fun 𝓡 h𝓡 ↦ ⟨{𝓡 with smul := fun r x hx ↦ h𝓡.2.1 r x hx}, h𝓡.1, subset_rfl⟩)
  -- `I` itself is a neighborhood of zero, so it contains some open sub-`R'`-module `J`.
  rcases (hasBasis_moduleCon R').mem_iff.mp hI with ⟨J, hJ, J_sub_I⟩
  have hRJ (r : R) {x y} : J x y → I (r • x) (r • y) := fun hxy ↦ I.smul r (@J_sub_I ⟨x, y⟩ hxy)
  set 𝓐 : ModuleCon R M := moduleConGen R 𝓢
  sorry

theorem tendsto_smul_uniformity [IsLinearUniformity R M]
    {ι : Type*} {f : Filter ι}
    (a b : ι → M) (c : ι → R) (hab : Tendsto (fun i ↦ (a i, b i)) f (𝓤 M)) :
    Tendsto (fun i ↦ (c i • a i, c i • b i)) f (𝓤 M) := by
  rw [hasBasis_moduleCon R |>.tendsto_right_iff]
  intro 𝓡 h𝓡
  filter_upwards [hab.eventually h𝓡] using fun i hi ↦ 𝓡.smul _ hi

variable (R) in
/-- If the left and right actions of `R` on `M` coincide, then a topology is `Rᵐᵒᵖ`-linear
if and only if it is `R`-linear. -/
theorem _root_.IsCentralScalar.isLinearUniformity_iff [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    IsLinearUniformity Rᵐᵒᵖ M ↔ IsLinearUniformity R M := by
  sorry

end Module

section Ring



end Ring

end IsLinearUniformity

class IsLinearUniformity (R : Type*) [Semiring R] [UniformSpace R] where
  hasBasis_ringCon : (𝓤 R).HasBasis
    (fun 𝓡 : RingCon R ↦ {xy : R × R | 𝓡 xy.1 xy.2} ∈ 𝓤 R)
    (fun 𝓡 : RingCon R ↦ {xy : R × R | 𝓡 xy.1 xy.2})

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
