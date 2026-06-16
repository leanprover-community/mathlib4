module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.OpenSmoothEmbedding
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

lemma _root_.Set.restrict_surjective {α β : Type*} (s : Set α) [Nonempty β] :
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
  rw [← Set.preimage_comp, Set.inter_comm,
    I.rightInvOn.eqOn.inter_preimage_eq]
  simp only [preimage_id_eq, id_eq, inter_eq_right]
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

-- Now, this lemma is true!
variable (I n) in
lemma baz (z : M) :
    ∃ (U : Opens H) (f : U → M) (hf : IsOpenSmoothEmbedding I I n f),
    z ∈ Set.range f := by
  let φ := chartAt H z
  use ⟨φ.target, φ.open_target⟩, Set.restrict φ.target φ.symm
  refine ⟨?_ /- charts are open smooth embeddings -/, ?_⟩
  · sorry
  simpa using ⟨φ z, mem_chart_target H z, φ.left_inv <| mem_chart_source H z⟩

-- missing API lemma, exercise for Christian (Merten)
lemma mvfderiv_comp_left {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] {f : M → V}
    {z : M₀} (φ : M₀ → M) (hφ : MDiffAt φ z) :
    d% (f ∘ φ) z = d% f (φ z) ∘SL (mfderiv% φ z) := by
  sorry

lemma mychainrule {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {f : M → V} {φ : M₀ → M} {z : M₀} (hφ : MDiffAt φ z) (v : TangentSpace I₀ z) :
    d% f (φ z) (mfderiv% φ z v) = d% (f ∘ φ) z v := by
  rw [mvfderiv_comp_left (I := I)]
  · simp
  · assumption

-- another missing lemma, I think!
lemma mvfderiv_restrict_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {f' : M → V} {U : Opens M} {x : M} (hx : x ∈ U) :
    d% (Set.restrict U f' : U → V) ⟨x, hx⟩ =
      d% f' x ∘SL (mfderiv% (Subtype.val : U → _) ⟨x, hx⟩):= by
  sorry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

lemma mvfderiv_eq_fderiv {f : E → V} {x : E} :
  d% f x = (fderiv 𝕜 f x) ∘L (NormedSpace.fromTangentSpace x).toContinuousLinearMap := by
  sorry

open Function
lemma mvfderiv_smul' {f : M → 𝕜} {g : M → V} {x : M}
    (hf : MDiffAt f x) (hg : MDiffAt g x) :
    d% (f • g) x = f x • d% g x + (d% f x).smulRight (g x) := by
  wlog h : ∃ (s : NiceSubset I), ImBad M I (niceSubsetEquiv s) I
  · -- TODO: think about which regularity I can assume. For now, will C¹ do?
    obtain ⟨U, φ, hφ, hz⟩ := baz I (M := M) 1 x
    obtain ⟨s, rfl⟩ := (niceSubsetEquiv (I := I)).surjective U
    obtain ⟨z, rfl⟩ := hz
    ext v
    obtain ⟨v, rfl⟩ := hφ.surjective_mfderiv z v
    have hφ' := hφ.contMDiff.mdifferentiableAt (x := z) (by simp)
    rw [mychainrule hφ']
    simp only [add_apply, smul_apply, smulRight_apply]
    rw [mychainrule hφ', mychainrule hφ']
    -- one more lemma about commuting smul and composition,
    -- then should be the chain rule for d% again
    -- rw [Function.smul_comp]
      --change (d% ((f ∘ φ) • (g ∘ φ)) hz) v = f (φ hz) • (d% (g ∘ φ) hz) v + (d% (f ∘ φ) hz) v • g (φ hz) -- lemma: commute smul and comp
    sorry
  obtain ⟨s, ⟨⟩⟩ := h
  clear! M
  have : ∃ f' : E → 𝕜, Set.restrict (niceSubsetEquiv s) (f' ∘ I) = f := by
    obtain ⟨f₀, rfl⟩ := Set.restrict_surjective (niceSubsetEquiv s).carrier f
    use f₀ ∘ I.symm
    ext
    simp
  obtain ⟨f', rfl⟩ := this
  have : ∃ g' : E → V, Set.restrict (niceSubsetEquiv s) (g' ∘ I) = g := by
    obtain ⟨g₀, rfl⟩ := Set.restrict_surjective (niceSubsetEquiv s).carrier g
    use g₀ ∘ I.symm
    ext
    simp
  obtain ⟨g', rfl⟩ := this
  obtain ⟨x, hx⟩ := x
  have : ∃ x' : E, x' ∈ s.carrier ∧ I.symm x' = x :=
    ⟨I x, by simpa [niceSubsetEquiv] using hx, I.left_inv' (by simp)⟩
  obtain ⟨x', hx', rfl⟩ := this
  rw [restrict_smul]
  -- mdiff lemmas, like yesterday
  -- missing mathlib lemmas: relate MDiff terms to normed space world
  -- should be global simp lemmas or a simp set
  replace hf : DifferentiableWithinAt 𝕜 f' s.carrier x' := sorry
  replace hg : DifferentiableWithinAt 𝕜 g' s.carrier x' := sorry
  -- xxx doesn't apply! rw [mvfderiv_eq_fderiv]
  simp_rw [mvfderiv_restrict_apply]
  dsimp
  have : I (I.symm x') = x' := by
    rw [← Function.comp_apply (f := I) (g := I.symm)]
    apply I.right_inv'
    grw [s.foo] at hx'
    rw [← I.range_eq_target]
    simpa
  rw [this]
  ext X
  dsimp
  sorry

end
