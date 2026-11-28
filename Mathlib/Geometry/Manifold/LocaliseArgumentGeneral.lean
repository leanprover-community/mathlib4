module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Topology.Sets.OpenCover

-- Experiments: localisation arguments in differential geometry
-- in Utrecht (June 11), Christian Merten, Edward van de Meent, Michael Rothgang
-- version support manifolds with boundary: seems promising,
-- requires further clean-up and exploration

@[expose] section

open NormedSpace ContinuousLinearMap
open scoped Manifold

set_option warn.sorry false
set_option linter.style.longLine false

inductive ImBad {𝕜 : Type} [NontriviallyNormedField 𝕜] :
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type} [TopologicalSpace H]
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners 𝕜 E H)
    {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {H' : Type} [TopologicalSpace H']
    (N : Type) [TopologicalSpace N] [ChartedSpace H' N]
    (J : ModelWithCorners 𝕜 F H'), Prop where
  | refl {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
      {H : Type} [TopologicalSpace H]
      {M : Type} [TopologicalSpace M] [ChartedSpace H M]
      {I : ModelWithCorners 𝕜 E H} : ImBad M I M I

lemma _root_.Set.restrict_surjective {α β : Type*} {s : Set α} [Nonempty β] :
    (s.restrict (π := fun _ ↦ β)).Surjective := by
  sorry

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
  {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {N : Type} [TopologicalSpace N] [ChartedSpace H' N]
  {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H'' : Type} [TopologicalSpace H'']
  {I₀ : ModelWithCorners 𝕜 F H''} {M₀ : Type} [TopologicalSpace M₀] [ChartedSpace H'' M₀]

@[ext]
structure NiceSubset (I : ModelWithCorners 𝕜 E H) : Type _  where
  carrier : Set E
  isOpen_preimage_carrier : IsOpen <| I ⁻¹' carrier
  foo : carrier ⊆ Set.range I

open TopologicalSpace Set

-- missing lemma, TODO clean up!
lemma ModelWithCorners.image_preimage (I : ModelWithCorners 𝕜 E H)
    (s : Set E) (hs : s ⊆ I.target) : I '' (I ⁻¹' s) = s := by
  rw [I.image_eq]
  rw [← Set.preimage_comp]
  rw [Set.inter_comm]
  let a := I.rightInvOn.eqOn
  let a' := EqOn.inter_preimage_eq a
  rw [a']
  simp
  erw [I.range_eq_target]; exact hs

def niceSubsetEquiv : NiceSubset I ≃ Opens H where
  toFun s := ⟨_, s.isOpen_preimage_carrier⟩
  invFun t := {
    carrier := I '' t.1
    isOpen_preimage_carrier := by simp [I.preimage_image, t.isOpen] -- why not simp?
    foo := by simp
  }
  left_inv t := by
    ext1
    dsimp
    rw [I.image_preimage]
    simpa [I.image_preimage] using t.foo
  right_inv s := by ext; simp [I.preimage_image]
-- future: define NiceSubset.open to yield an Open

lemma restrict_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {f : M → 𝕜} {g : M → V} (U : Set M) :
  (Set.restrict U f • Set.restrict U g) = U.restrict (f • g) := sorry

lemma restrict_smul_apply
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {f : M → 𝕜} {g : M → V} (U : Set M) {x : U} :
  (Set.restrict U f • Set.restrict U g) x = U.restrict (f • g) x := sorry

open scoped ContDiff
variable {n : ℕ∞ω}

-- better name OpenSmoothEmbedding!
-- open question: do we want n as regularity parameter?
-- the inclusion of U into M is true for any n...
variable (I J n) in
def IsOpenImmersion (f : M → N) : Prop :=
  ∃ U : Opens N, ∃ φ : Diffeomorph I J M U n, (Subtype.val ∘ φ) = f
-- lemma: is a smooth embedding with open range, yada yada (and conversely...)
-- is antitone in the regularity

def IsOpenImmersion.isOpen_range {f : M → N} (hf : IsOpenImmersion I J n f) : IsOpen (Set.range f) := by
  sorry

def IsOpenImmersion.range {f : M → N} (_hf : IsOpenImmersion I J n f) : Opens N :=
  ⟨Set.range f, _hf.isOpen_range⟩

-- now it's true!
variable (I n) in
lemma baz (z : M) :
    ∃ (U : Opens H) (f : U → M) (hf : IsOpenImmersion I I n f),
    z ∈ Set.range f := by
  let φ := chartAt H z
  use ⟨φ.target, φ.open_target⟩ -- now true
  use Set.restrict φ.target φ.symm
  refine ⟨sorry /- charts are open immersions-/, ?_⟩
  simp only [mem_range, Set.restrict_apply, Subtype.exists, Opens.mem_mk, exists_prop]
  refine ⟨φ z, mem_chart_target H z, ?_⟩
  exact φ.left_inv <| mem_chart_source H z

lemma mychainrule {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {f : M → V} {φ : M₀ → M} {z : M₀} {hφ : MDiffAt φ z} (v : TangentSpace I₀ z) :
    d% f (φ z) (mfderiv% φ z v) = d% (f ∘ φ) z v := by
  /-rw [mvfderiv_comp_left (I := I)]
  · simp
  · assumption -/
  sorry -- other file
open Function
lemma mvfderiv_smul' {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {f : M → 𝕜} {g : M → V} {x : M}
    (hf : MDiffAt f x) (hg : MDiffAt g x) :
    d% (f • g) x = f x • d% g x + (d% f x).smulRight (g x) := by
  wlog h : ∃ (s : NiceSubset I), ImBad M I (niceSubsetEquiv s) I
  · obtain ⟨U, φ, hφ, hz⟩ := baz I (M := M) 2/- XXX! -/ x
    obtain ⟨s, rfl⟩ := (niceSubsetEquiv (I := I)).surjective U
    obtain ⟨hz, rfl⟩ := hz
    ext v
    have aux : Surjective (mfderiv% φ hz) := sorry
    obtain ⟨v, rfl⟩ := aux v
    rw [mychainrule]
    simp only [add_apply, smul_apply]--, smulRight_apply]
    rw [mychainrule]
    --rw [mychainrule]
    --change (d% ((f ∘ φ) • (g ∘ φ)) hz) v = f (φ hz) • (d% (g ∘ φ) hz) v + (d% (f ∘ φ) hz) v • g (φ hz) -- lemma: commute smul and comp
    --apply this
    --rw [Function.smul_comp]
    -- d% (φ z)
    sorry
    sorry
    sorry

  obtain ⟨s, ⟨⟩⟩ := h
  clear! M
  have : ∃ f' : E → 𝕜, Set.restrict (niceSubsetEquiv s) (f' ∘ I) = f := by
    obtain ⟨myf, rfl⟩ := Set.restrict_surjective (β := 𝕜) (s := (niceSubsetEquiv s).carrier) f
    use myf ∘ I.symm
    ext
    simp
  obtain ⟨f', rfl⟩ := this
  have : ∃ g' : E → V, Set.restrict (niceSubsetEquiv s) (g' ∘ I) = g := by
    sorry -- like previous one
  obtain ⟨g', rfl⟩ := this
  obtain ⟨x, hx⟩ := x
  have : ∃ x' : E, x' ∈ s.carrier ∧ I.symm x' = x := by
    use I x
    constructor
    · simpa [niceSubsetEquiv] using hx
    · apply I.left_inv'
      simp
  obtain ⟨x', hx', rfl⟩ := this
  rw [restrict_smul]
  -- mdiff lemmas, like yesterday
  sorry

end
