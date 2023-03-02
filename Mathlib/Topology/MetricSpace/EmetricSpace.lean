/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.metric_space.emetric_space
! leanprover-community/mathlib commit 195fcd60ff2bfe392543bceb0ec2adcdb472db4c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Interval
import Mathbin.Data.Real.Ennreal
import Mathbin.Topology.UniformSpace.Pi
import Mathbin.Topology.UniformSpace.UniformConvergence
import Mathbin.Topology.UniformSpace.UniformEmbedding

/-!
# Extended metric spaces

This file is devoted to the definition and study of `emetric_spaces`, i.e., metric
spaces in which the distance is allowed to take the value ∞. This extended distance is
called `edist`, and takes values in `ℝ≥0∞`.

Many definitions and theorems expected on emetric spaces are already introduced on uniform spaces
and topological spaces. For example: open and closed sets, compactness, completeness, continuity and
uniform continuity.

The class `emetric_space` therefore extends `uniform_space` (and `topological_space`).

Since a lot of elementary properties don't require `eq_of_edist_eq_zero` we start setting up the
theory of `pseudo_emetric_space`, where we don't require `edist x y = 0 → x = y` and we specialize
to `emetric_space` at the end.
-/


open Set Filter Classical

open uniformity Topology BigOperators Filter NNReal ENNReal

universe u v w

variable {α : Type u} {β : Type v} {X : Type _}

/-- Characterizing uniformities associated to a (generalized) distance function `D`
in terms of the elements of the uniformity. -/
theorem uniformity_dist_of_mem_uniformity [LinearOrder β] {U : Filter (α × α)} (z : β)
    (D : α → α → β) (H : ∀ s, s ∈ U ↔ ∃ ε > z, ∀ {a b : α}, D a b < ε → (a, b) ∈ s) :
    U = ⨅ ε > z, 𝓟 { p : α × α | D p.1 p.2 < ε } :=
  HasBasis.eq_binfᵢ ⟨fun s => by simp only [H, subset_def, Prod.forall, mem_set_of]⟩
#align uniformity_dist_of_mem_uniformity uniformity_dist_of_mem_uniformity

/-- `has_edist α` means that `α` is equipped with an extended distance. -/
class HasEdist (α : Type _) where
  edist : α → α → ℝ≥0∞
#align has_edist HasEdist

export HasEdist (edist)

/-- Creating a uniform space from an extended distance. -/
noncomputable def uniformSpaceOfEdist (edist : α → α → ℝ≥0∞) (edist_self : ∀ x : α, edist x x = 0)
    (edist_comm : ∀ x y : α, edist x y = edist y x)
    (edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z) : UniformSpace α :=
  UniformSpace.ofFun edist edist_self edist_comm edist_triangle fun ε ε0 =>
    ⟨ε / 2, ENNReal.half_pos ε0.lt.ne', fun _ h₁ _ h₂ =>
      (ENNReal.add_lt_add h₁ h₂).trans_eq (ENNReal.add_halves _)⟩
#align uniform_space_of_edist uniformSpaceOfEdist

-- the uniform structure is embedded in the emetric space structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].
/-- Extended (pseudo) metric spaces, with an extended distance `edist` possibly taking the
value ∞

Each pseudo_emetric space induces a canonical `uniform_space` and hence a canonical
`topological_space`.
This is enforced in the type class definition, by extending the `uniform_space` structure. When
instantiating a `pseudo_emetric_space` structure, the uniformity fields are not necessary, they
will be filled in by default. There is a default value for the uniformity, that can be substituted
in cases of interest, for instance when instantiating a `pseudo_emetric_space` structure
on a product.

Continuity of `edist` is proved in `topology.instances.ennreal`
-/
class PseudoEmetricSpace (α : Type u) extends HasEdist α : Type u where
  edist_self : ∀ x : α, edist x x = 0
  edist_comm : ∀ x y : α, edist x y = edist y x
  edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z
  toUniformSpace : UniformSpace α := uniformSpaceOfEdist edist edist_self edist_comm edist_triangle
  uniformity_edist :
    𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α |
            edist p.1 p.2 < ε } := by
    intros
    rfl
#align pseudo_emetric_space PseudoEmetricSpace

attribute [instance] PseudoEmetricSpace.toUniformSpace

/- Pseudoemetric spaces are less common than metric spaces. Therefore, we work in a dedicated
namespace, while notions associated to metric spaces are mostly in the root namespace. -/
variable [PseudoEmetricSpace α]

export PseudoEmetricSpace (edist_self edist_comm edist_triangle)

attribute [simp] edist_self

/-- Triangle inequality for the extended distance -/
theorem edist_triangle_left (x y z : α) : edist x y ≤ edist z x + edist z y := by
  rw [edist_comm z] <;> apply edist_triangle
#align edist_triangle_left edist_triangle_left

theorem edist_triangle_right (x y z : α) : edist x y ≤ edist x z + edist y z := by
  rw [edist_comm y] <;> apply edist_triangle
#align edist_triangle_right edist_triangle_right

theorem edist_congr_right {x y z : α} (h : edist x y = 0) : edist x z = edist y z :=
  by
  apply le_antisymm
  · rw [← zero_add (edist y z), ← h]
    apply edist_triangle
  · rw [edist_comm] at h
    rw [← zero_add (edist x z), ← h]
    apply edist_triangle
#align edist_congr_right edist_congr_right

theorem edist_congr_left {x y z : α} (h : edist x y = 0) : edist z x = edist z y :=
  by
  rw [edist_comm z x, edist_comm z y]
  apply edist_congr_right h
#align edist_congr_left edist_congr_left

theorem edist_triangle4 (x y z t : α) : edist x t ≤ edist x y + edist y z + edist z t :=
  calc
    edist x t ≤ edist x z + edist z t := edist_triangle x z t
    _ ≤ edist x y + edist y z + edist z t := add_le_add_right (edist_triangle x y z) _
    
#align edist_triangle4 edist_triangle4

/-- The triangle (polygon) inequality for sequences of points; `finset.Ico` version. -/
theorem edist_le_Ico_sum_edist (f : ℕ → α) {m n} (h : m ≤ n) :
    edist (f m) (f n) ≤ ∑ i in Finset.Ico m n, edist (f i) (f (i + 1)) :=
  by
  revert n
  refine' Nat.le_induction _ _
  · simp only [Finset.sum_empty, Finset.Ico_self, edist_self]
    -- TODO: Why doesn't Lean close this goal automatically? `exact le_rfl` fails too.
    exact le_refl (0 : ℝ≥0∞)
  · intro n hn hrec
    calc
      edist (f m) (f (n + 1)) ≤ edist (f m) (f n) + edist (f n) (f (n + 1)) := edist_triangle _ _ _
      _ ≤ (∑ i in Finset.Ico m n, _) + _ := (add_le_add hrec le_rfl)
      _ = ∑ i in Finset.Ico m (n + 1), _ := by
        rw [Nat.Ico_succ_right_eq_insert_Ico hn, Finset.sum_insert, add_comm] <;> simp
      
#align edist_le_Ico_sum_edist edist_le_Ico_sum_edist

/-- The triangle (polygon) inequality for sequences of points; `finset.range` version. -/
theorem edist_le_range_sum_edist (f : ℕ → α) (n : ℕ) :
    edist (f 0) (f n) ≤ ∑ i in Finset.range n, edist (f i) (f (i + 1)) :=
  Nat.Ico_zero_eq_range ▸ edist_le_Ico_sum_edist f (Nat.zero_le n)
#align edist_le_range_sum_edist edist_le_range_sum_edist

/-- A version of `edist_le_Ico_sum_edist` with each intermediate distance replaced
with an upper estimate. -/
theorem edist_le_Ico_sum_of_edist_le {f : ℕ → α} {m n} (hmn : m ≤ n) {d : ℕ → ℝ≥0∞}
    (hd : ∀ {k}, m ≤ k → k < n → edist (f k) (f (k + 1)) ≤ d k) :
    edist (f m) (f n) ≤ ∑ i in Finset.Ico m n, d i :=
  le_trans (edist_le_Ico_sum_edist f hmn) <|
    Finset.sum_le_sum fun k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2
#align edist_le_Ico_sum_of_edist_le edist_le_Ico_sum_of_edist_le

/-- A version of `edist_le_range_sum_edist` with each intermediate distance replaced
with an upper estimate. -/
theorem edist_le_range_sum_of_edist_le {f : ℕ → α} (n : ℕ) {d : ℕ → ℝ≥0∞}
    (hd : ∀ {k}, k < n → edist (f k) (f (k + 1)) ≤ d k) :
    edist (f 0) (f n) ≤ ∑ i in Finset.range n, d i :=
  Nat.Ico_zero_eq_range ▸ edist_le_Ico_sum_of_edist_le (zero_le n) fun _ _ => hd
#align edist_le_range_sum_of_edist_le edist_le_range_sum_of_edist_le

/-- Reformulation of the uniform structure in terms of the extended distance -/
theorem uniformity_pseudoedist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε } :=
  PseudoEmetricSpace.uniformity_edist
#align uniformity_pseudoedist uniformity_pseudoedist

theorem uniformSpace_edist :
    ‹PseudoEmetricSpace α›.toUniformSpace =
      uniformSpaceOfEdist edist edist_self edist_comm edist_triangle :=
  uniformSpace_eq uniformity_pseudoedist
#align uniform_space_edist uniformSpace_edist

theorem uniformity_basis_edist :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε } :=
  (@uniformSpace_edist α _).symm ▸ UniformSpace.hasBasis_ofFun ⟨1, one_pos⟩ _ _ _ _ _
#align uniformity_basis_edist uniformity_basis_edist

/-- Characterization of the elements of the uniformity in terms of the extended distance -/
theorem mem_uniformity_edist {s : Set (α × α)} :
    s ∈ 𝓤 α ↔ ∃ ε > 0, ∀ {a b : α}, edist a b < ε → (a, b) ∈ s :=
  uniformity_basis_edist.mem_uniformity_iff
#align mem_uniformity_edist mem_uniformity_edist

/-- Given `f : β → ℝ≥0∞`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_edist`, `uniformity_basis_edist'`,
`uniformity_basis_edist_nnreal`, and `uniformity_basis_edist_inv_nat`. -/
protected theorem Emetric.mk_uniformity_basis {β : Type _} {p : β → Prop} {f : β → ℝ≥0∞}
    (hf₀ : ∀ x, p x → 0 < f x) (hf : ∀ ε, 0 < ε → ∃ (x : _)(hx : p x), f x ≤ ε) :
    (𝓤 α).HasBasis p fun x => { p : α × α | edist p.1 p.2 < f x } :=
  by
  refine' ⟨fun s => uniformity_basis_edist.mem_iff.trans _⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases hf ε ε₀ with ⟨i, hi, H⟩
    exact ⟨i, hi, fun x hx => hε <| lt_of_lt_of_le hx H⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, H⟩
#align emetric.mk_uniformity_basis Emetric.mk_uniformity_basis

/-- Given `f : β → ℝ≥0∞`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then closed `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_edist_le` and `uniformity_basis_edist_le'`. -/
protected theorem Emetric.mk_uniformity_basis_le {β : Type _} {p : β → Prop} {f : β → ℝ≥0∞}
    (hf₀ : ∀ x, p x → 0 < f x) (hf : ∀ ε, 0 < ε → ∃ (x : _)(hx : p x), f x ≤ ε) :
    (𝓤 α).HasBasis p fun x => { p : α × α | edist p.1 p.2 ≤ f x } :=
  by
  refine' ⟨fun s => uniformity_basis_edist.mem_iff.trans _⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases exists_between ε₀ with ⟨ε', hε'⟩
    rcases hf ε' hε'.1 with ⟨i, hi, H⟩
    exact ⟨i, hi, fun x hx => hε <| lt_of_le_of_lt (le_trans hx H) hε'.2⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, fun x hx => H (le_of_lt hx)⟩
#align emetric.mk_uniformity_basis_le Emetric.mk_uniformity_basis_le

theorem uniformity_basis_edist_le :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 ≤ ε } :=
  Emetric.mk_uniformity_basis_le (fun _ => id) fun ε ε₀ => ⟨ε, ε₀, le_refl ε⟩
#align uniformity_basis_edist_le uniformity_basis_edist_le

theorem uniformity_basis_edist' (ε' : ℝ≥0∞) (hε' : 0 < ε') :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => ε ∈ Ioo 0 ε') fun ε => { p : α × α | edist p.1 p.2 < ε } :=
  Emetric.mk_uniformity_basis (fun _ => And.left) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := exists_between hε'
    ⟨min ε δ, ⟨lt_min ε₀ hδ.1, lt_of_le_of_lt (min_le_right _ _) hδ.2⟩, min_le_left _ _⟩
#align uniformity_basis_edist' uniformity_basis_edist'

theorem uniformity_basis_edist_le' (ε' : ℝ≥0∞) (hε' : 0 < ε') :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => ε ∈ Ioo 0 ε') fun ε => { p : α × α | edist p.1 p.2 ≤ ε } :=
  Emetric.mk_uniformity_basis_le (fun _ => And.left) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := exists_between hε'
    ⟨min ε δ, ⟨lt_min ε₀ hδ.1, lt_of_le_of_lt (min_le_right _ _) hδ.2⟩, min_le_left _ _⟩
#align uniformity_basis_edist_le' uniformity_basis_edist_le'

theorem uniformity_basis_edist_nNReal :
    (𝓤 α).HasBasis (fun ε : ℝ≥0 => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε } :=
  Emetric.mk_uniformity_basis (fun _ => ENNReal.coe_pos.2) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ε₀
    ⟨δ, ENNReal.coe_pos.1 hδ.1, le_of_lt hδ.2⟩
#align uniformity_basis_edist_nnreal uniformity_basis_edist_nNReal

theorem uniformity_basis_edist_nNReal_le :
    (𝓤 α).HasBasis (fun ε : ℝ≥0 => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 ≤ ε } :=
  Emetric.mk_uniformity_basis_le (fun _ => ENNReal.coe_pos.2) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ε₀
    ⟨δ, ENNReal.coe_pos.1 hδ.1, le_of_lt hδ.2⟩
#align uniformity_basis_edist_nnreal_le uniformity_basis_edist_nNReal_le

theorem uniformity_basis_edist_inv_nat :
    (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | edist p.1 p.2 < (↑n)⁻¹ } :=
  Emetric.mk_uniformity_basis (fun n _ => ENNReal.inv_pos.2 <| ENNReal.nat_ne_top n) fun ε ε₀ =>
    let ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt ε₀)
    ⟨n, trivial, le_of_lt hn⟩
#align uniformity_basis_edist_inv_nat uniformity_basis_edist_inv_nat

theorem uniformity_basis_edist_inv_two_pow :
    (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | edist p.1 p.2 < 2⁻¹ ^ n } :=
  Emetric.mk_uniformity_basis (fun n _ => ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.two_ne_top) _)
    fun ε ε₀ =>
    let ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt (ne_of_gt ε₀)
    ⟨n, trivial, le_of_lt hn⟩
#align uniformity_basis_edist_inv_two_pow uniformity_basis_edist_inv_two_pow

/-- Fixed size neighborhoods of the diagonal belong to the uniform structure -/
theorem edist_mem_uniformity {ε : ℝ≥0∞} (ε0 : 0 < ε) : { p : α × α | edist p.1 p.2 < ε } ∈ 𝓤 α :=
  mem_uniformity_edist.2 ⟨ε, ε0, fun a b => id⟩
#align edist_mem_uniformity edist_mem_uniformity

namespace Emetric

instance (priority := 900) : IsCountablyGenerated (𝓤 α) :=
  isCountablyGenerated_of_seq ⟨_, uniformity_basis_edist_inv_nat.eq_infᵢ⟩

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection {a b «expr ∈ » s} -/
/-- ε-δ characterization of uniform continuity on a set for pseudoemetric spaces -/
theorem uniformContinuousOn_iff [PseudoEmetricSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a} {_ : a ∈ s} {b} {_ : b ∈ s}, edist a b < δ → edist (f a) (f b) < ε :=
  uniformity_basis_edist.uniformContinuousOn_iff uniformity_basis_edist
#align emetric.uniform_continuous_on_iff Emetric.uniformContinuousOn_iff

/-- ε-δ characterization of uniform continuity on pseudoemetric spaces -/
theorem uniformContinuous_iff [PseudoEmetricSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε :=
  uniformity_basis_edist.uniformContinuous_iff uniformity_basis_edist
#align emetric.uniform_continuous_iff Emetric.uniformContinuous_iff

/-- ε-δ characterization of uniform embeddings on pseudoemetric spaces -/
theorem uniformEmbedding_iff [PseudoEmetricSpace β] {f : α → β} :
    UniformEmbedding f ↔
      Function.Injective f ∧
        UniformContinuous f ∧
          ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  by
  simp only [uniformity_basis_edist.uniform_embedding_iff uniformity_basis_edist, exists_prop]
  rfl
#align emetric.uniform_embedding_iff Emetric.uniformEmbedding_iff

/-- If a map between pseudoemetric spaces is a uniform embedding then the edistance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y`. -/
theorem controlled_of_uniformEmbedding [PseudoEmetricSpace β] {f : α → β} :
    UniformEmbedding f →
      (∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε) ∧
        ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  fun h => ⟨uniformContinuous_iff.1 (uniformEmbedding_iff.1 h).2.1, (uniformEmbedding_iff.1 h).2.2⟩
#align emetric.controlled_of_uniform_embedding Emetric.controlled_of_uniformEmbedding

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » t) -/
/-- ε-δ characterization of Cauchy sequences on pseudoemetric spaces -/
protected theorem cauchy_iff {f : Filter α} :
    Cauchy f ↔ f ≠ ⊥ ∧ ∀ ε > 0, ∃ t ∈ f, ∀ (x) (_ : x ∈ t) (y) (_ : y ∈ t), edist x y < ε := by
  rw [← ne_bot_iff] <;> exact uniformity_basis_edist.cauchy_iff
#align emetric.cauchy_iff Emetric.cauchy_iff

/-- A very useful criterion to show that a space is complete is to show that all sequences
which satisfy a bound of the form `edist (u n) (u m) < B N` for all `n m ≥ N` are
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast convergence to
`0`, which makes it possible to use arguments of converging series, while this is impossible
to do in general for arbitrary Cauchy sequences. -/
theorem complete_of_convergent_controlled_sequences (B : ℕ → ℝ≥0∞) (hB : ∀ n, 0 < B n)
    (H :
      ∀ u : ℕ → α,
        (∀ N n m : ℕ, N ≤ n → N ≤ m → edist (u n) (u m) < B N) → ∃ x, Tendsto u atTop (𝓝 x)) :
    CompleteSpace α :=
  UniformSpace.complete_of_convergent_controlled_sequences
    (fun n => { p : α × α | edist p.1 p.2 < B n }) (fun n => edist_mem_uniformity <| hB n) H
#align emetric.complete_of_convergent_controlled_sequences Emetric.complete_of_convergent_controlled_sequences

/-- A sequentially complete pseudoemetric space is complete. -/
theorem complete_of_cauchySeq_tendsto :
    (∀ u : ℕ → α, CauchySeq u → ∃ a, Tendsto u atTop (𝓝 a)) → CompleteSpace α :=
  UniformSpace.complete_of_cauchySeq_tendsto
#align emetric.complete_of_cauchy_seq_tendsto Emetric.complete_of_cauchySeq_tendsto

/-- Expressing locally uniform convergence on a set using `edist`. -/
theorem tendstoLocallyUniformlyOn_iff {ι : Type _} [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} {s : Set β} :
    TendstoLocallyUniformlyOn F f p s ↔
      ∀ ε > 0, ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, edist (f y) (F n y) < ε :=
  by
  refine' ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu x hx => _⟩
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
  rcases H ε εpos x hx with ⟨t, ht, Ht⟩
  exact ⟨t, ht, Ht.mono fun n hs x hx => hε (hs x hx)⟩
#align emetric.tendsto_locally_uniformly_on_iff Emetric.tendstoLocallyUniformlyOn_iff

/-- Expressing uniform convergence on a set using `edist`. -/
theorem tendstoUniformlyOn_iff {ι : Type _} {F : ι → β → α} {f : β → α} {p : Filter ι} {s : Set β} :
    TendstoUniformlyOn F f p s ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x ∈ s, edist (f x) (F n x) < ε :=
  by
  refine' ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu => _⟩
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hs x hx => hε (hs x hx)
#align emetric.tendsto_uniformly_on_iff Emetric.tendstoUniformlyOn_iff

/-- Expressing locally uniform convergence using `edist`. -/
theorem tendstoLocallyUniformly_iff {ι : Type _} [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} :
    TendstoLocallyUniformly F f p ↔
      ∀ ε > 0, ∀ x : β, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, edist (f y) (F n y) < ε :=
  by
  simp only [← tendstoLocallyUniformlyOn_univ, tendsto_locally_uniformly_on_iff, mem_univ,
    forall_const, exists_prop, nhdsWithin_univ]
#align emetric.tendsto_locally_uniformly_iff Emetric.tendstoLocallyUniformly_iff

/-- Expressing uniform convergence using `edist`. -/
theorem tendstoUniformly_iff {ι : Type _} {F : ι → β → α} {f : β → α} {p : Filter ι} :
    TendstoUniformly F f p ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x, edist (f x) (F n x) < ε := by
  simp only [← tendstoUniformlyOn_univ, tendsto_uniformly_on_iff, mem_univ, forall_const]
#align emetric.tendsto_uniformly_iff Emetric.tendstoUniformly_iff

end Emetric

open Emetric

/-- Auxiliary function to replace the uniformity on a pseudoemetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct a pseudoemetric space with a
specified uniformity. See Note [forgetful inheritance] explaining why having definitionally
the right uniformity is often important.
-/
def PseudoEmetricSpace.replaceUniformity {α} [U : UniformSpace α] (m : PseudoEmetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEmetricSpace.toUniformSpace]) : PseudoEmetricSpace α
    where
  edist := @edist _ m.toHasEdist
  edist_self := edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := U
  uniformity_edist := H.trans (@PseudoEmetricSpace.uniformity_edist α _)
#align pseudo_emetric_space.replace_uniformity PseudoEmetricSpace.replaceUniformity

/-- The extended pseudometric induced by a function taking values in a pseudoemetric space. -/
def PseudoEmetricSpace.induced {α β} (f : α → β) (m : PseudoEmetricSpace β) : PseudoEmetricSpace α
    where
  edist x y := edist (f x) (f y)
  edist_self x := edist_self _
  edist_comm x y := edist_comm _ _
  edist_triangle x y z := edist_triangle _ _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_edist := (uniformity_basis_edist.comap _).eq_binfᵢ
#align pseudo_emetric_space.induced PseudoEmetricSpace.induced

/-- Pseudoemetric space instance on subsets of pseudoemetric spaces -/
instance {α : Type _} {p : α → Prop} [PseudoEmetricSpace α] : PseudoEmetricSpace (Subtype p) :=
  PseudoEmetricSpace.induced coe ‹_›

/-- The extended psuedodistance on a subset of a pseudoemetric space is the restriction of
the original pseudodistance, by definition -/
theorem Subtype.edist_eq {p : α → Prop} (x y : Subtype p) : edist x y = edist (x : α) y :=
  rfl
#align subtype.edist_eq Subtype.edist_eq

namespace MulOpposite

/-- Pseudoemetric space instance on the multiplicative opposite of a pseudoemetric space. -/
@[to_additive "Pseudoemetric space instance on the additive opposite of a pseudoemetric space."]
instance {α : Type _} [PseudoEmetricSpace α] : PseudoEmetricSpace αᵐᵒᵖ :=
  PseudoEmetricSpace.induced unop ‹_›

@[to_additive]
theorem edist_unop (x y : αᵐᵒᵖ) : edist (unop x) (unop y) = edist x y :=
  rfl
#align mul_opposite.edist_unop MulOpposite.edist_unop
#align add_opposite.edist_unop AddOpposite.edist_unop

@[to_additive]
theorem edist_op (x y : α) : edist (op x) (op y) = edist x y :=
  rfl
#align mul_opposite.edist_op MulOpposite.edist_op
#align add_opposite.edist_op AddOpposite.edist_op

end MulOpposite

section ULift

instance : PseudoEmetricSpace (ULift α) :=
  PseudoEmetricSpace.induced ULift.down ‹_›

theorem ULift.edist_eq (x y : ULift α) : edist x y = edist x.down y.down :=
  rfl
#align ulift.edist_eq ULift.edist_eq

@[simp]
theorem ULift.edist_up_up (x y : α) : edist (ULift.up x) (ULift.up y) = edist x y :=
  rfl
#align ulift.edist_up_up ULift.edist_up_up

end ULift

/-- The product of two pseudoemetric spaces, with the max distance, is an extended
pseudometric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
instance Prod.pseudoEmetricSpaceMax [PseudoEmetricSpace β] : PseudoEmetricSpace (α × β)
    where
  edist x y := edist x.1 y.1 ⊔ edist x.2 y.2
  edist_self x := by simp
  edist_comm x y := by simp [edist_comm]
  edist_triangle x y z :=
    max_le (le_trans (edist_triangle _ _ _) (add_le_add (le_max_left _ _) (le_max_left _ _)))
      (le_trans (edist_triangle _ _ _) (add_le_add (le_max_right _ _) (le_max_right _ _)))
  uniformity_edist := by
    refine' uniformity_prod.trans _
    simp only [PseudoEmetricSpace.uniformity_edist, comap_infi]
    rw [← infᵢ_inf_eq]; congr ; funext
    rw [← infᵢ_inf_eq]; congr ; funext
    simp [inf_principal, ext_iff, max_lt_iff]
  toUniformSpace := Prod.uniformSpace
#align prod.pseudo_emetric_space_max Prod.pseudoEmetricSpaceMax

theorem Prod.edist_eq [PseudoEmetricSpace β] (x y : α × β) :
    edist x y = max (edist x.1 y.1) (edist x.2 y.2) :=
  rfl
#align prod.edist_eq Prod.edist_eq

section Pi

open Finset

variable {π : β → Type _} [Fintype β]

/-- The product of a finite number of pseudoemetric spaces, with the max distance, is still
a pseudoemetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces. -/
instance pseudoEmetricSpacePi [∀ b, PseudoEmetricSpace (π b)] : PseudoEmetricSpace (∀ b, π b)
    where
  edist f g := Finset.sup univ fun b => edist (f b) (g b)
  edist_self f := bot_unique <| Finset.sup_le <| by simp
  edist_comm f g := by unfold edist <;> congr <;> funext a <;> exact edist_comm _ _
  edist_triangle f g h := by
    simp only [Finset.sup_le_iff]
    intro b hb
    exact le_trans (edist_triangle _ (g b) _) (add_le_add (le_sup hb) (le_sup hb))
  toUniformSpace := Pi.uniformSpace _
  uniformity_edist :=
    by
    simp only [Pi.uniformity, PseudoEmetricSpace.uniformity_edist, comap_infi, gt_iff_lt,
      preimage_set_of_eq, comap_principal]
    rw [infᵢ_comm]; congr ; funext ε
    rw [infᵢ_comm]; congr ; funext εpos
    change 0 < ε at εpos
    simp [Set.ext_iff, εpos]
#align pseudo_emetric_space_pi pseudoEmetricSpacePi

theorem edist_pi_def [∀ b, PseudoEmetricSpace (π b)] (f g : ∀ b, π b) :
    edist f g = Finset.sup univ fun b => edist (f b) (g b) :=
  rfl
#align edist_pi_def edist_pi_def

theorem edist_le_pi_edist [∀ b, PseudoEmetricSpace (π b)] (f g : ∀ b, π b) (b : β) :
    edist (f b) (g b) ≤ edist f g :=
  Finset.le_sup (Finset.mem_univ b)
#align edist_le_pi_edist edist_le_pi_edist

theorem edist_pi_le_iff [∀ b, PseudoEmetricSpace (π b)] {f g : ∀ b, π b} {d : ℝ≥0∞} :
    edist f g ≤ d ↔ ∀ b, edist (f b) (g b) ≤ d :=
  Finset.sup_le_iff.trans <| by simp only [Finset.mem_univ, forall_const]
#align edist_pi_le_iff edist_pi_le_iff

theorem edist_pi_const_le (a b : α) : (edist (fun _ : β => a) fun _ => b) ≤ edist a b :=
  edist_pi_le_iff.2 fun _ => le_rfl
#align edist_pi_const_le edist_pi_const_le

@[simp]
theorem edist_pi_const [Nonempty β] (a b : α) : (edist (fun x : β => a) fun _ => b) = edist a b :=
  Finset.sup_const univ_nonempty (edist a b)
#align edist_pi_const edist_pi_const

end Pi

namespace Emetric

variable {x y z : α} {ε ε₁ ε₂ : ℝ≥0∞} {s t : Set α}

/-- `emetric.ball x ε` is the set of all points `y` with `edist y x < ε` -/
def ball (x : α) (ε : ℝ≥0∞) : Set α :=
  { y | edist y x < ε }
#align emetric.ball Emetric.ball

@[simp]
theorem mem_ball : y ∈ ball x ε ↔ edist y x < ε :=
  Iff.rfl
#align emetric.mem_ball Emetric.mem_ball

theorem mem_ball' : y ∈ ball x ε ↔ edist x y < ε := by rw [edist_comm, mem_ball]
#align emetric.mem_ball' Emetric.mem_ball'

/-- `emetric.closed_ball x ε` is the set of all points `y` with `edist y x ≤ ε` -/
def closedBall (x : α) (ε : ℝ≥0∞) :=
  { y | edist y x ≤ ε }
#align emetric.closed_ball Emetric.closedBall

@[simp]
theorem mem_closedBall : y ∈ closedBall x ε ↔ edist y x ≤ ε :=
  Iff.rfl
#align emetric.mem_closed_ball Emetric.mem_closedBall

theorem mem_closed_ball' : y ∈ closedBall x ε ↔ edist x y ≤ ε := by rw [edist_comm, mem_closed_ball]
#align emetric.mem_closed_ball' Emetric.mem_closed_ball'

@[simp]
theorem closedBall_top (x : α) : closedBall x ∞ = univ :=
  eq_univ_of_forall fun y => le_top
#align emetric.closed_ball_top Emetric.closedBall_top

theorem ball_subset_closedBall : ball x ε ⊆ closedBall x ε := fun y hy => le_of_lt hy
#align emetric.ball_subset_closed_ball Emetric.ball_subset_closedBall

theorem pos_of_mem_ball (hy : y ∈ ball x ε) : 0 < ε :=
  lt_of_le_of_lt (zero_le _) hy
#align emetric.pos_of_mem_ball Emetric.pos_of_mem_ball

theorem mem_ball_self (h : 0 < ε) : x ∈ ball x ε :=
  show edist x x < ε by rw [edist_self] <;> assumption
#align emetric.mem_ball_self Emetric.mem_ball_self

theorem mem_closedBall_self : x ∈ closedBall x ε :=
  show edist x x ≤ ε by rw [edist_self] <;> exact bot_le
#align emetric.mem_closed_ball_self Emetric.mem_closedBall_self

theorem mem_ball_comm : x ∈ ball y ε ↔ y ∈ ball x ε := by rw [mem_ball', mem_ball]
#align emetric.mem_ball_comm Emetric.mem_ball_comm

theorem mem_closedBall_comm : x ∈ closedBall y ε ↔ y ∈ closedBall x ε := by
  rw [mem_closed_ball', mem_closed_ball]
#align emetric.mem_closed_ball_comm Emetric.mem_closedBall_comm

theorem ball_subset_ball (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂ := fun y (yx : _ < ε₁) =>
  lt_of_lt_of_le yx h
#align emetric.ball_subset_ball Emetric.ball_subset_ball

theorem closedBall_subset_closedBall (h : ε₁ ≤ ε₂) : closedBall x ε₁ ⊆ closedBall x ε₂ :=
  fun y (yx : _ ≤ ε₁) => le_trans yx h
#align emetric.closed_ball_subset_closed_ball Emetric.closedBall_subset_closedBall

theorem ball_disjoint (h : ε₁ + ε₂ ≤ edist x y) : Disjoint (ball x ε₁) (ball y ε₂) :=
  Set.disjoint_left.mpr fun z h₁ h₂ =>
    (edist_triangle_left x y z).not_lt <| (ENNReal.add_lt_add h₁ h₂).trans_le h
#align emetric.ball_disjoint Emetric.ball_disjoint

theorem ball_subset (h : edist x y + ε₁ ≤ ε₂) (h' : edist x y ≠ ∞) : ball x ε₁ ⊆ ball y ε₂ :=
  fun z zx =>
  calc
    edist z y ≤ edist z x + edist x y := edist_triangle _ _ _
    _ = edist x y + edist z x := (add_comm _ _)
    _ < edist x y + ε₁ := (ENNReal.add_lt_add_left h' zx)
    _ ≤ ε₂ := h
    
#align emetric.ball_subset Emetric.ball_subset

theorem exists_ball_subset_ball (h : y ∈ ball x ε) : ∃ ε' > 0, ball y ε' ⊆ ball x ε :=
  by
  have : 0 < ε - edist y x := by simpa using h
  refine' ⟨ε - edist y x, this, ball_subset _ (ne_top_of_lt h)⟩
  exact (add_tsub_cancel_of_le (mem_ball.mp h).le).le
#align emetric.exists_ball_subset_ball Emetric.exists_ball_subset_ball

theorem ball_eq_empty_iff : ball x ε = ∅ ↔ ε = 0 :=
  eq_empty_iff_forall_not_mem.trans
    ⟨fun h => le_bot_iff.1 (le_of_not_gt fun ε0 => h _ (mem_ball_self ε0)), fun ε0 y h =>
      not_lt_of_le (le_of_eq ε0) (pos_of_mem_ball h)⟩
#align emetric.ball_eq_empty_iff Emetric.ball_eq_empty_iff

theorem ordConnected_setOf_closedBall_subset (x : α) (s : Set α) :
    OrdConnected { r | closedBall x r ⊆ s } :=
  ⟨fun r₁ hr₁ r₂ hr₂ r hr => (closedBall_subset_closedBall hr.2).trans hr₂⟩
#align emetric.ord_connected_set_of_closed_ball_subset Emetric.ordConnected_setOf_closedBall_subset

theorem ordConnected_setOf_ball_subset (x : α) (s : Set α) : OrdConnected { r | ball x r ⊆ s } :=
  ⟨fun r₁ hr₁ r₂ hr₂ r hr => (ball_subset_ball hr.2).trans hr₂⟩
#align emetric.ord_connected_set_of_ball_subset Emetric.ordConnected_setOf_ball_subset

/-- Relation “two points are at a finite edistance” is an equivalence relation. -/
def edistLtTopSetoid : Setoid α where
  R x y := edist x y < ⊤
  iseqv :=
    ⟨fun x => by
      rw [edist_self]
      exact ENNReal.coe_lt_top, fun x y h => by rwa [edist_comm], fun x y z hxy hyz =>
      lt_of_le_of_lt (edist_triangle x y z) (ENNReal.add_lt_top.2 ⟨hxy, hyz⟩)⟩
#align emetric.edist_lt_top_setoid Emetric.edistLtTopSetoid

@[simp]
theorem ball_zero : ball x 0 = ∅ := by rw [Emetric.ball_eq_empty_iff]
#align emetric.ball_zero Emetric.ball_zero

theorem nhds_basis_eball : (𝓝 x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) (ball x) :=
  nhds_basis_uniformity uniformity_basis_edist
#align emetric.nhds_basis_eball Emetric.nhds_basis_eball

theorem nhdsWithin_basis_eball : (𝓝[s] x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => ball x ε ∩ s :=
  nhdsWithin_hasBasis nhds_basis_eball s
#align emetric.nhds_within_basis_eball Emetric.nhdsWithin_basis_eball

theorem nhds_basis_closed_eball : (𝓝 x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) (closedBall x) :=
  nhds_basis_uniformity uniformity_basis_edist_le
#align emetric.nhds_basis_closed_eball Emetric.nhds_basis_closed_eball

theorem nhdsWithin_basis_closed_eball :
    (𝓝[s] x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => closedBall x ε ∩ s :=
  nhdsWithin_hasBasis nhds_basis_closed_eball s
#align emetric.nhds_within_basis_closed_eball Emetric.nhdsWithin_basis_closed_eball

theorem nhds_eq : 𝓝 x = ⨅ ε > 0, 𝓟 (ball x ε) :=
  nhds_basis_eball.eq_binfᵢ
#align emetric.nhds_eq Emetric.nhds_eq

theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ ε > 0, ball x ε ⊆ s :=
  nhds_basis_eball.mem_iff
#align emetric.mem_nhds_iff Emetric.mem_nhds_iff

theorem mem_nhdsWithin_iff : s ∈ 𝓝[t] x ↔ ∃ ε > 0, ball x ε ∩ t ⊆ s :=
  nhdsWithin_basis_eball.mem_iff
#align emetric.mem_nhds_within_iff Emetric.mem_nhdsWithin_iff

section

variable [PseudoEmetricSpace β] {f : α → β}

theorem tendsto_nhdsWithin_nhdsWithin {t : Set β} {a b} :
    Tendsto f (𝓝[s] a) (𝓝[t] b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ ⦃x⦄, x ∈ s → edist x a < δ → f x ∈ t ∧ edist (f x) b < ε :=
  (nhdsWithin_basis_eball.tendsto_iffₓ nhdsWithin_basis_eball).trans <|
    forall₂_congr fun ε hε => exists₂_congr fun δ hδ => forall_congr' fun x => by simp <;> itauto
#align emetric.tendsto_nhds_within_nhds_within Emetric.tendsto_nhdsWithin_nhdsWithin

theorem tendsto_nhdsWithin_nhds {a b} :
    Tendsto f (𝓝[s] a) (𝓝 b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {x : α}, x ∈ s → edist x a < δ → edist (f x) b < ε :=
  by
  rw [← nhdsWithin_univ b, tendsto_nhds_within_nhds_within]
  simp only [mem_univ, true_and_iff]
#align emetric.tendsto_nhds_within_nhds Emetric.tendsto_nhdsWithin_nhds

theorem tendsto_nhds_nhds {a b} :
    Tendsto f (𝓝 a) (𝓝 b) ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x⦄, edist x a < δ → edist (f x) b < ε :=
  nhds_basis_eball.tendsto_iffₓ nhds_basis_eball
#align emetric.tendsto_nhds_nhds Emetric.tendsto_nhds_nhds

end

theorem isOpen_iff : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ball x ε ⊆ s := by
  simp [isOpen_iff_nhds, mem_nhds_iff]
#align emetric.is_open_iff Emetric.isOpen_iff

theorem isOpen_ball : IsOpen (ball x ε) :=
  isOpen_iff.2 fun y => exists_ball_subset_ball
#align emetric.is_open_ball Emetric.isOpen_ball

theorem isClosed_ball_top : IsClosed (ball x ⊤) :=
  isOpen_compl_iff.1 <|
    isOpen_iff.2 fun y hy =>
      ⟨⊤, ENNReal.coe_lt_top,
        (ball_disjoint <| by
            rw [top_add]
            exact le_of_not_lt hy).subset_compl_right⟩
#align emetric.is_closed_ball_top Emetric.isClosed_ball_top

theorem ball_mem_nhds (x : α) {ε : ℝ≥0∞} (ε0 : 0 < ε) : ball x ε ∈ 𝓝 x :=
  isOpen_ball.mem_nhds (mem_ball_self ε0)
#align emetric.ball_mem_nhds Emetric.ball_mem_nhds

theorem closedBall_mem_nhds (x : α) {ε : ℝ≥0∞} (ε0 : 0 < ε) : closedBall x ε ∈ 𝓝 x :=
  mem_of_superset (ball_mem_nhds x ε0) ball_subset_closedBall
#align emetric.closed_ball_mem_nhds Emetric.closedBall_mem_nhds

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem ball_prod_same [PseudoEmetricSpace β] (x : α) (y : β) (r : ℝ≥0∞) :
    ball x r ×ˢ ball y r = ball (x, y) r :=
  ext fun z => max_lt_iff.symm
#align emetric.ball_prod_same Emetric.ball_prod_same

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem closedBall_prod_same [PseudoEmetricSpace β] (x : α) (y : β) (r : ℝ≥0∞) :
    closedBall x r ×ˢ closedBall y r = closedBall (x, y) r :=
  ext fun z => max_le_iff.symm
#align emetric.closed_ball_prod_same Emetric.closedBall_prod_same

/-- ε-characterization of the closure in pseudoemetric spaces -/
theorem mem_closure_iff : x ∈ closure s ↔ ∀ ε > 0, ∃ y ∈ s, edist x y < ε :=
  (mem_closure_iff_nhds_basis nhds_basis_eball).trans <| by simp only [mem_ball, edist_comm x]
#align emetric.mem_closure_iff Emetric.mem_closure_iff

theorem tendsto_nhds {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in f, edist (u x) a < ε :=
  nhds_basis_eball.tendsto_right_iff
#align emetric.tendsto_nhds Emetric.tendsto_nhds

theorem tendsto_atTop [Nonempty β] [SemilatticeSup β] {u : β → α} {a : α} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, edist (u n) a < ε :=
  (atTop_basis.tendsto_iffₓ nhds_basis_eball).trans <| by
    simp only [exists_prop, true_and_iff, mem_Ici, mem_ball]
#align emetric.tendsto_at_top Emetric.tendsto_atTop

theorem inseparable_iff : Inseparable x y ↔ edist x y = 0 := by
  simp [inseparable_iff_mem_closure, mem_closure_iff, edist_comm, forall_lt_iff_le']
#align emetric.inseparable_iff Emetric.inseparable_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (m n «expr ≥ » N) -/
-- see Note [nolint_ge]
/-- In a pseudoemetric space, Cauchy sequences are characterized by the fact that, eventually,
the pseudoedistance between its elements is arbitrarily small -/
@[nolint ge_or_gt]
theorem cauchySeq_iff [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ (m) (_ : m ≥ N) (n) (_ : n ≥ N), edist (u m) (u n) < ε :=
  uniformity_basis_edist.cauchySeq_iff
#align emetric.cauchy_seq_iff Emetric.cauchySeq_iff

/-- A variation around the emetric characterization of Cauchy sequences -/
theorem cauchySeq_iff' [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀ ε > (0 : ℝ≥0∞), ∃ N, ∀ n ≥ N, edist (u n) (u N) < ε :=
  uniformity_basis_edist.cauchySeq_iff'
#align emetric.cauchy_seq_iff' Emetric.cauchySeq_iff'

/-- A variation of the emetric characterization of Cauchy sequences that deals with
`ℝ≥0` upper bounds. -/
theorem cauchySeq_iff_nNReal [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀ ε : ℝ≥0, 0 < ε → ∃ N, ∀ n, N ≤ n → edist (u n) (u N) < ε :=
  uniformity_basis_edist_nNReal.cauchySeq_iff'
#align emetric.cauchy_seq_iff_nnreal Emetric.cauchySeq_iff_nNReal

theorem totallyBounded_iff {s : Set α} :
    TotallyBounded s ↔ ∀ ε > 0, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, ball y ε :=
  ⟨fun H ε ε0 => H _ (edist_mem_uniformity ε0), fun H r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru
    let ⟨t, ft, h⟩ := H ε ε0
    ⟨t, ft, h.trans <| unionᵢ₂_mono fun y yt z => hε⟩⟩
#align emetric.totally_bounded_iff Emetric.totallyBounded_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
theorem totallyBounded_iff' {s : Set α} :
    TotallyBounded s ↔ ∀ ε > 0, ∃ (t : _)(_ : t ⊆ s), Set.Finite t ∧ s ⊆ ⋃ y ∈ t, ball y ε :=
  ⟨fun H ε ε0 => (totallyBounded_iff_subset.1 H) _ (edist_mem_uniformity ε0), fun H r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru
    let ⟨t, _, ft, h⟩ := H ε ε0
    ⟨t, ft, h.trans <| unionᵢ₂_mono fun y yt z => hε⟩⟩
#align emetric.totally_bounded_iff' Emetric.totallyBounded_iff'

section Compact

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
/-- For a set `s` in a pseudo emetric space, if for every `ε > 0` there exists a countable
set that is `ε`-dense in `s`, then there exists a countable subset `t ⊆ s` that is dense in `s`. -/
theorem subset_countable_closure_of_almost_dense_set (s : Set α)
    (hs : ∀ ε > 0, ∃ t : Set α, t.Countable ∧ s ⊆ ⋃ x ∈ t, closedBall x ε) :
    ∃ (t : _)(_ : t ⊆ s), t.Countable ∧ s ⊆ closure t :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨x₀, hx₀⟩)
  · exact ⟨∅, empty_subset _, countable_empty, empty_subset _⟩
  choose! T hTc hsT using fun n : ℕ => hs n⁻¹ (by simp)
  have : ∀ r x, ∃ y ∈ s, closed_ball x r ∩ s ⊆ closed_ball y (r * 2) :=
    by
    intro r x
    rcases(closed_ball x r ∩ s).eq_empty_or_nonempty with (he | ⟨y, hxy, hys⟩)
    · refine' ⟨x₀, hx₀, _⟩
      rw [he]
      exact empty_subset _
    · refine' ⟨y, hys, fun z hz => _⟩
      calc
        edist z y ≤ edist z x + edist y x := edist_triangle_right _ _ _
        _ ≤ r + r := (add_le_add hz.1 hxy)
        _ = r * 2 := (mul_two r).symm
        
  choose f hfs hf
  refine'
    ⟨⋃ n : ℕ, f n⁻¹ '' T n, Union_subset fun n => image_subset_iff.2 fun z hz => hfs _ _,
      countable_Union fun n => (hTc n).image _, _⟩
  refine' fun x hx => mem_closure_iff.2 fun ε ε0 => _
  rcases ENNReal.exists_inv_nat_lt (ENNReal.half_pos ε0.lt.ne').ne' with ⟨n, hn⟩
  rcases mem_Union₂.1 (hsT n hx) with ⟨y, hyn, hyx⟩
  refine' ⟨f n⁻¹ y, mem_Union.2 ⟨n, mem_image_of_mem _ hyn⟩, _⟩
  calc
    edist x (f n⁻¹ y) ≤ n⁻¹ * 2 := hf _ _ ⟨hyx, hx⟩
    _ < ε := ENNReal.mul_lt_of_lt_div hn
    
#align emetric.subset_countable_closure_of_almost_dense_set Emetric.subset_countable_closure_of_almost_dense_set

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
/-- A compact set in a pseudo emetric space is separable, i.e., it is a subset of the closure of a
countable set.  -/
theorem subset_countable_closure_of_compact {s : Set α} (hs : IsCompact s) :
    ∃ (t : _)(_ : t ⊆ s), t.Countable ∧ s ⊆ closure t :=
  by
  refine' subset_countable_closure_of_almost_dense_set s fun ε hε => _
  rcases totally_bounded_iff'.1 hs.totally_bounded ε hε with ⟨t, hts, htf, hst⟩
  exact ⟨t, htf.countable, subset.trans hst <| Union₂_mono fun _ _ => ball_subset_closed_ball⟩
#align emetric.subset_countable_closure_of_compact Emetric.subset_countable_closure_of_compact

end Compact

section SecondCountable

open _Root_.TopologicalSpace

variable (α)

/-- A sigma compact pseudo emetric space has second countable topology. This is not an instance
to avoid a loop with `sigma_compact_space_of_locally_compact_second_countable`.  -/
theorem second_countable_of_sigma_compact [SigmaCompactSpace α] : SecondCountableTopology α :=
  by
  suffices separable_space α by exact UniformSpace.secondCountable_of_separable α
  choose T hTsub hTc hsubT using fun n =>
    subset_countable_closure_of_compact (isCompact_compactCovering α n)
  refine' ⟨⟨⋃ n, T n, countable_Union hTc, fun x => _⟩⟩
  rcases Union_eq_univ_iff.1 (unionᵢ_compactCovering α) x with ⟨n, hn⟩
  exact closure_mono (subset_Union _ n) (hsubT _ hn)
#align emetric.second_countable_of_sigma_compact Emetric.second_countable_of_sigma_compact

variable {α}

theorem second_countable_of_almost_dense_set
    (hs : ∀ ε > 0, ∃ t : Set α, t.Countable ∧ (⋃ x ∈ t, closedBall x ε) = univ) :
    SecondCountableTopology α :=
  by
  suffices separable_space α by exact UniformSpace.secondCountable_of_separable α
  rcases subset_countable_closure_of_almost_dense_set (univ : Set α) fun ε ε0 => _ with
    ⟨t, -, htc, ht⟩
  · exact ⟨⟨t, htc, fun x => ht (mem_univ x)⟩⟩
  · rcases hs ε ε0 with ⟨t, htc, ht⟩
    exact ⟨t, htc, univ_subset_iff.2 ht⟩
#align emetric.second_countable_of_almost_dense_set Emetric.second_countable_of_almost_dense_set

end SecondCountable

section Diam

/-- The diameter of a set in a pseudoemetric space, named `emetric.diam` -/
noncomputable def diam (s : Set α) :=
  ⨆ (x ∈ s) (y ∈ s), edist x y
#align emetric.diam Emetric.diam

theorem diam_le_iff {d : ℝ≥0∞} : diam s ≤ d ↔ ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ d := by
  simp only [diam, supᵢ_le_iff]
#align emetric.diam_le_iff Emetric.diam_le_iff

theorem diam_image_le_iff {d : ℝ≥0∞} {f : β → α} {s : Set β} :
    diam (f '' s) ≤ d ↔ ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) ≤ d := by
  simp only [diam_le_iff, ball_image_iff]
#align emetric.diam_image_le_iff Emetric.diam_image_le_iff

theorem edist_le_of_diam_le {d} (hx : x ∈ s) (hy : y ∈ s) (hd : diam s ≤ d) : edist x y ≤ d :=
  diam_le_iff.1 hd x hx y hy
#align emetric.edist_le_of_diam_le Emetric.edist_le_of_diam_le

/-- If two points belong to some set, their edistance is bounded by the diameter of the set -/
theorem edist_le_diam_of_mem (hx : x ∈ s) (hy : y ∈ s) : edist x y ≤ diam s :=
  edist_le_of_diam_le hx hy le_rfl
#align emetric.edist_le_diam_of_mem Emetric.edist_le_diam_of_mem

/-- If the distance between any two points in a set is bounded by some constant, this constant
bounds the diameter. -/
theorem diam_le {d : ℝ≥0∞} (h : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ d) : diam s ≤ d :=
  diam_le_iff.2 h
#align emetric.diam_le Emetric.diam_le

/-- The diameter of a subsingleton vanishes. -/
theorem diam_subsingleton (hs : s.Subsingleton) : diam s = 0 :=
  nonpos_iff_eq_zero.1 <| diam_le fun x hx y hy => (hs hx hy).symm ▸ edist_self y ▸ le_rfl
#align emetric.diam_subsingleton Emetric.diam_subsingleton

/-- The diameter of the empty set vanishes -/
@[simp]
theorem diam_empty : diam (∅ : Set α) = 0 :=
  diam_subsingleton subsingleton_empty
#align emetric.diam_empty Emetric.diam_empty

/-- The diameter of a singleton vanishes -/
@[simp]
theorem diam_singleton : diam ({x} : Set α) = 0 :=
  diam_subsingleton subsingleton_singleton
#align emetric.diam_singleton Emetric.diam_singleton

theorem diam_unionᵢ_mem_option {ι : Type _} (o : Option ι) (s : ι → Set α) :
    diam (⋃ i ∈ o, s i) = ⨆ i ∈ o, diam (s i) := by cases o <;> simp
#align emetric.diam_Union_mem_option Emetric.diam_unionᵢ_mem_option

theorem diam_insert : diam (insert x s) = max (⨆ y ∈ s, edist x y) (diam s) :=
  eq_of_forall_ge_iff fun d => by
    simp only [diam_le_iff, ball_insert_iff, edist_self, edist_comm x, max_le_iff, supᵢ_le_iff,
      zero_le, true_and_iff, forall_and, and_self_iff, ← and_assoc']
#align emetric.diam_insert Emetric.diam_insert

theorem diam_pair : diam ({x, y} : Set α) = edist x y := by
  simp only [supᵢ_singleton, diam_insert, diam_singleton, ENNReal.max_zero_right]
#align emetric.diam_pair Emetric.diam_pair

theorem diam_triple : diam ({x, y, z} : Set α) = max (max (edist x y) (edist x z)) (edist y z) := by
  simp only [diam_insert, supᵢ_insert, supᵢ_singleton, diam_singleton, ENNReal.max_zero_right,
    ENNReal.sup_eq_max]
#align emetric.diam_triple Emetric.diam_triple

/-- The diameter is monotonous with respect to inclusion -/
theorem diam_mono {s t : Set α} (h : s ⊆ t) : diam s ≤ diam t :=
  diam_le fun x hx y hy => edist_le_diam_of_mem (h hx) (h hy)
#align emetric.diam_mono Emetric.diam_mono

/-- The diameter of a union is controlled by the diameter of the sets, and the edistance
between two points in the sets. -/
theorem diam_union {t : Set α} (xs : x ∈ s) (yt : y ∈ t) :
    diam (s ∪ t) ≤ diam s + edist x y + diam t :=
  by
  have A : ∀ a ∈ s, ∀ b ∈ t, edist a b ≤ diam s + edist x y + diam t := fun a ha b hb =>
    calc
      edist a b ≤ edist a x + edist x y + edist y b := edist_triangle4 _ _ _ _
      _ ≤ diam s + edist x y + diam t :=
        add_le_add (add_le_add (edist_le_diam_of_mem ha xs) le_rfl) (edist_le_diam_of_mem yt hb)
      
  refine' diam_le fun a ha b hb => _
  cases' (mem_union _ _ _).1 ha with h'a h'a <;> cases' (mem_union _ _ _).1 hb with h'b h'b
  ·
    calc
      edist a b ≤ diam s := edist_le_diam_of_mem h'a h'b
      _ ≤ diam s + (edist x y + diam t) := le_self_add
      _ = diam s + edist x y + diam t := (add_assoc _ _ _).symm
      
  · exact A a h'a b h'b
  · have Z := A b h'b a h'a
    rwa [edist_comm] at Z
  ·
    calc
      edist a b ≤ diam t := edist_le_diam_of_mem h'a h'b
      _ ≤ diam s + edist x y + diam t := le_add_self
      
#align emetric.diam_union Emetric.diam_union

theorem diam_union' {t : Set α} (h : (s ∩ t).Nonempty) : diam (s ∪ t) ≤ diam s + diam t :=
  by
  let ⟨x, ⟨xs, xt⟩⟩ := h
  simpa using diam_union xs xt
#align emetric.diam_union' Emetric.diam_union'

theorem diam_closedBall {r : ℝ≥0∞} : diam (closedBall x r) ≤ 2 * r :=
  diam_le fun a ha b hb =>
    calc
      edist a b ≤ edist a x + edist b x := edist_triangle_right _ _ _
      _ ≤ r + r := (add_le_add ha hb)
      _ = 2 * r := (two_mul r).symm
      
#align emetric.diam_closed_ball Emetric.diam_closedBall

theorem diam_ball {r : ℝ≥0∞} : diam (ball x r) ≤ 2 * r :=
  le_trans (diam_mono ball_subset_closedBall) diam_closedBall
#align emetric.diam_ball Emetric.diam_ball

theorem diam_pi_le_of_le {π : β → Type _} [Fintype β] [∀ b, PseudoEmetricSpace (π b)]
    {s : ∀ b : β, Set (π b)} {c : ℝ≥0∞} (h : ∀ b, diam (s b) ≤ c) : diam (Set.pi univ s) ≤ c :=
  by
  apply diam_le fun x hx y hy => edist_pi_le_iff.mpr _
  rw [mem_univ_pi] at hx hy
  exact fun b => diam_le_iff.1 (h b) (x b) (hx b) (y b) (hy b)
#align emetric.diam_pi_le_of_le Emetric.diam_pi_le_of_le

end Diam

end Emetric

--namespace
/-- We now define `emetric_space`, extending `pseudo_emetric_space`. -/
class EmetricSpace (α : Type u) extends PseudoEmetricSpace α : Type u where
  eq_of_edist_eq_zero : ∀ {x y : α}, edist x y = 0 → x = y
#align emetric_space EmetricSpace

variable {γ : Type w} [EmetricSpace γ]

export EmetricSpace (eq_of_edist_eq_zero)

/-- Characterize the equality of points by the vanishing of their extended distance -/
@[simp]
theorem edist_eq_zero {x y : γ} : edist x y = 0 ↔ x = y :=
  Iff.intro eq_of_edist_eq_zero fun this : x = y => this ▸ edist_self _
#align edist_eq_zero edist_eq_zero

@[simp]
theorem zero_eq_edist {x y : γ} : 0 = edist x y ↔ x = y :=
  Iff.intro (fun h => eq_of_edist_eq_zero h.symm) fun this : x = y => this ▸ (edist_self _).symm
#align zero_eq_edist zero_eq_edist

theorem edist_le_zero {x y : γ} : edist x y ≤ 0 ↔ x = y :=
  nonpos_iff_eq_zero.trans edist_eq_zero
#align edist_le_zero edist_le_zero

@[simp]
theorem edist_pos {x y : γ} : 0 < edist x y ↔ x ≠ y := by simp [← not_le]
#align edist_pos edist_pos

/-- Two points coincide if their distance is `< ε` for all positive ε -/
theorem eq_of_forall_edist_le {x y : γ} (h : ∀ ε > 0, edist x y ≤ ε) : x = y :=
  eq_of_edist_eq_zero (eq_of_le_of_forall_le_of_dense bot_le h)
#align eq_of_forall_edist_le eq_of_forall_edist_le

-- see Note [lower instance priority]
/-- An emetric space is separated -/
instance (priority := 100) to_separated : SeparatedSpace γ :=
  separated_def.2 fun x y h =>
    eq_of_forall_edist_le fun ε ε0 => le_of_lt (h _ (edist_mem_uniformity ε0))
#align to_separated to_separated

/-- A map between emetric spaces is a uniform embedding if and only if the edistance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y` and conversely. -/
theorem Emetric.uniformEmbedding_iff' [EmetricSpace β] {f : γ → β} :
    UniformEmbedding f ↔
      (∀ ε > 0, ∃ δ > 0, ∀ {a b : γ}, edist a b < δ → edist (f a) (f b) < ε) ∧
        ∀ δ > 0, ∃ ε > 0, ∀ {a b : γ}, edist (f a) (f b) < ε → edist a b < δ :=
  by
  simp only [uniformEmbedding_iff_uniformInducing,
    uniformity_basis_edist.uniform_inducing_iff uniformity_basis_edist, exists_prop]
  rfl
#align emetric.uniform_embedding_iff' Emetric.uniformEmbedding_iff'

/-- If a `pseudo_emetric_space` is a T₀ space, then it is an `emetric_space`. -/
def EmetricSpace.ofT0PseudoEmetricSpace (α : Type _) [PseudoEmetricSpace α] [T0Space α] :
    EmetricSpace α :=
  { ‹PseudoEmetricSpace α› with
    eq_of_edist_eq_zero := fun x y hdist => (Emetric.inseparable_iff.2 hdist).Eq }
#align emetric_space.of_t0_pseudo_emetric_space EmetricSpace.ofT0PseudoEmetricSpace

/-- Auxiliary function to replace the uniformity on an emetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct an emetric space with a
specified uniformity. See Note [forgetful inheritance] explaining why having definitionally
the right uniformity is often important.
-/
def EmetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : EmetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEmetricSpace.toUniformSpace]) : EmetricSpace γ
    where
  edist := @edist _ m.toHasEdist
  edist_self := edist_self
  eq_of_edist_eq_zero := @eq_of_edist_eq_zero _ _
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := U
  uniformity_edist := H.trans (@PseudoEmetricSpace.uniformity_edist γ _)
#align emetric_space.replace_uniformity EmetricSpace.replaceUniformity

/-- The extended metric induced by an injective function taking values in a emetric space. -/
def EmetricSpace.induced {γ β} (f : γ → β) (hf : Function.Injective f) (m : EmetricSpace β) :
    EmetricSpace γ where
  edist x y := edist (f x) (f y)
  edist_self x := edist_self _
  eq_of_edist_eq_zero x y h := hf (edist_eq_zero.1 h)
  edist_comm x y := edist_comm _ _
  edist_triangle x y z := edist_triangle _ _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_edist := (uniformity_basis_edist.comap _).eq_binfᵢ
#align emetric_space.induced EmetricSpace.induced

/-- Emetric space instance on subsets of emetric spaces -/
instance {α : Type _} {p : α → Prop} [EmetricSpace α] : EmetricSpace (Subtype p) :=
  EmetricSpace.induced coe Subtype.coe_injective ‹_›

/-- Emetric space instance on the multiplicative opposite of an emetric space. -/
@[to_additive "Emetric space instance on the additive opposite of an emetric space."]
instance {α : Type _} [EmetricSpace α] : EmetricSpace αᵐᵒᵖ :=
  EmetricSpace.induced MulOpposite.unop MulOpposite.unop_injective ‹_›

instance {α : Type _} [EmetricSpace α] : EmetricSpace (ULift α) :=
  EmetricSpace.induced ULift.down ULift.down_injective ‹_›

/-- The product of two emetric spaces, with the max distance, is an extended
metric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
instance Prod.emetricSpaceMax [EmetricSpace β] : EmetricSpace (γ × β) :=
  { Prod.pseudoEmetricSpaceMax with
    eq_of_edist_eq_zero := fun x y h =>
      by
      cases' max_le_iff.1 (le_of_eq h) with h₁ h₂
      have A : x.fst = y.fst := edist_le_zero.1 h₁
      have B : x.snd = y.snd := edist_le_zero.1 h₂
      exact Prod.ext_iff.2 ⟨A, B⟩ }
#align prod.emetric_space_max Prod.emetricSpaceMax

/-- Reformulation of the uniform structure in terms of the extended distance -/
theorem uniformity_edist : 𝓤 γ = ⨅ ε > 0, 𝓟 { p : γ × γ | edist p.1 p.2 < ε } :=
  PseudoEmetricSpace.uniformity_edist
#align uniformity_edist uniformity_edist

section Pi

open Finset

variable {π : β → Type _} [Fintype β]

/-- The product of a finite number of emetric spaces, with the max distance, is still
an emetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces. -/
instance emetricSpacePi [∀ b, EmetricSpace (π b)] : EmetricSpace (∀ b, π b) :=
  { pseudoEmetricSpacePi with
    eq_of_edist_eq_zero := fun f g eq0 =>
      by
      have eq1 : (sup univ fun b : β => edist (f b) (g b)) ≤ 0 := le_of_eq eq0
      simp only [Finset.sup_le_iff] at eq1
      exact funext fun b => edist_le_zero.1 <| eq1 b <| mem_univ b }
#align emetric_space_pi emetricSpacePi

end Pi

namespace Emetric

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
/-- A compact set in an emetric space is separable, i.e., it is the closure of a countable set. -/
theorem countable_closure_of_compact {s : Set γ} (hs : IsCompact s) :
    ∃ (t : _)(_ : t ⊆ s), t.Countable ∧ s = closure t :=
  by
  rcases subset_countable_closure_of_compact hs with ⟨t, hts, htc, hsub⟩
  exact ⟨t, hts, htc, subset.antisymm hsub (closure_minimal hts hs.is_closed)⟩
#align emetric.countable_closure_of_compact Emetric.countable_closure_of_compact

section Diam

variable {s : Set γ}

theorem diam_eq_zero_iff : diam s = 0 ↔ s.Subsingleton :=
  ⟨fun h x hx y hy => edist_le_zero.1 <| h ▸ edist_le_diam_of_mem hx hy, diam_subsingleton⟩
#align emetric.diam_eq_zero_iff Emetric.diam_eq_zero_iff

theorem diam_pos_iff : 0 < diam s ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y := by
  simp only [pos_iff_ne_zero, Ne.def, diam_eq_zero_iff, Set.Subsingleton, not_forall]
#align emetric.diam_pos_iff Emetric.diam_pos_iff

end Diam

end Emetric

/-!
### Separation quotient
-/


instance [PseudoEmetricSpace X] : HasEdist (UniformSpace.SeparationQuotient X) :=
  ⟨fun x y =>
    Quotient.liftOn₂' x y edist fun x y x' y' hx hy =>
      calc
        edist x y = edist x' y :=
          edist_congr_right <| Emetric.inseparable_iff.1 <| separationRel_iff_inseparable.1 hx
        _ = edist x' y' :=
          edist_congr_left <| Emetric.inseparable_iff.1 <| separationRel_iff_inseparable.1 hy
        ⟩

@[simp]
theorem UniformSpace.SeparationQuotient.edist_mk [PseudoEmetricSpace X] (x y : X) :
    @edist (UniformSpace.SeparationQuotient X) _ (Quot.mk _ x) (Quot.mk _ y) = edist x y :=
  rfl
#align uniform_space.separation_quotient.edist_mk UniformSpace.SeparationQuotient.edist_mk

instance [PseudoEmetricSpace X] : EmetricSpace (UniformSpace.SeparationQuotient X) :=
  @EmetricSpace.ofT0PseudoEmetricSpace (UniformSpace.SeparationQuotient X)
    { edist_self := fun x => Quotient.inductionOn' x edist_self
      edist_comm := fun x y => Quotient.inductionOn₂' x y edist_comm
      edist_triangle := fun x y z => Quotient.inductionOn₃' x y z edist_triangle
      toUniformSpace := inferInstance
      uniformity_edist :=
        (uniformity_basis_edist.map _).eq_binfᵢ.trans <|
          infᵢ_congr fun ε =>
            infᵢ_congr fun hε =>
              congr_arg 𝓟
                (by
                  ext ⟨⟨x⟩, ⟨y⟩⟩
                  refine' ⟨_, fun h => ⟨(x, y), h, rfl⟩⟩
                  rintro ⟨⟨x', y'⟩, h', h⟩
                  simp only [Prod.ext_iff] at h
                  rwa [← h.1, ← h.2]) }
    _

/-!
### `additive`, `multiplicative`

The distance on those type synonyms is inherited without change.
-/


open Additive Multiplicative

section

variable [HasEdist X]

instance : HasEdist (Additive X) :=
  ‹HasEdist X›

instance : HasEdist (Multiplicative X) :=
  ‹HasEdist X›

@[simp]
theorem edist_ofMul (a b : X) : edist (ofMul a) (ofMul b) = edist a b :=
  rfl
#align edist_of_mul edist_ofMul

@[simp]
theorem edist_ofAdd (a b : X) : edist (ofAdd a) (ofAdd b) = edist a b :=
  rfl
#align edist_of_add edist_ofAdd

@[simp]
theorem edist_toMul (a b : Additive X) : edist (toMul a) (toMul b) = edist a b :=
  rfl
#align edist_to_mul edist_toMul

@[simp]
theorem edist_toAdd (a b : Multiplicative X) : edist (toAdd a) (toAdd b) = edist a b :=
  rfl
#align edist_to_add edist_toAdd

end

instance [PseudoEmetricSpace X] : PseudoEmetricSpace (Additive X) :=
  ‹PseudoEmetricSpace X›

instance [PseudoEmetricSpace X] : PseudoEmetricSpace (Multiplicative X) :=
  ‹PseudoEmetricSpace X›

instance [EmetricSpace X] : EmetricSpace (Additive X) :=
  ‹EmetricSpace X›

instance [EmetricSpace X] : EmetricSpace (Multiplicative X) :=
  ‹EmetricSpace X›

/-!
### Order dual

The distance on this type synonym is inherited without change.
-/


open OrderDual

section

variable [HasEdist X]

instance : HasEdist Xᵒᵈ :=
  ‹HasEdist X›

@[simp]
theorem edist_toDual (a b : X) : edist (toDual a) (toDual b) = edist a b :=
  rfl
#align edist_to_dual edist_toDual

@[simp]
theorem edist_ofDual (a b : Xᵒᵈ) : edist (ofDual a) (ofDual b) = edist a b :=
  rfl
#align edist_of_dual edist_ofDual

end

instance [PseudoEmetricSpace X] : PseudoEmetricSpace Xᵒᵈ :=
  ‹PseudoEmetricSpace X›

instance [EmetricSpace X] : EmetricSpace Xᵒᵈ :=
  ‹EmetricSpace X›

