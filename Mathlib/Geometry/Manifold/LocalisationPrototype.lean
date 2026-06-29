module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.OpenSmoothEmbedding
public import Mathlib.Topology.Sets.OpenCover
import Mathlib.Tactic.ClickSuggestions

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
#check' ImBad.refl
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

-- should IsOpenMap be namespaced? was this just missed when `IsEmbedding` got namespaced?

open TopologicalSpace Set

-- copied from #41045; review and merge that one!
/-- A partial homeomorphism whose source is all of `X` defines an embedding of `X` into
`Y`. The converse is also true; see `IsEmbedding.toPartialHomeomorph`. -/
theorem PartialHomeomorph.isEmbedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : PartialHomeomorph X Y} (h : e.source = Set.univ) :
    Topology.IsEmbedding e :=
  sorry

-- TODO: redefine ModelWithCorners instead; this is a temporary solution only
@[simps toPartialEquiv]
def ModelWithCorners.toPartialHomeomorph (I : ModelWithCorners 𝕜 E H) : PartialHomeomorph H E where
  toPartialEquiv := I.toPartialEquiv
  continuousOn_toFun := I.continuous_toFun.continuousOn
  continuousOn_invFun := I.continuous_invFun.continuousOn

lemma ModelWithCorners.isEmbedding : Topology.IsEmbedding I :=
  I.toPartialHomeomorph.isEmbedding (by simp)

-- missing lemma, TODO clean up!
lemma ModelWithCorners.image_preimage (I : ModelWithCorners 𝕜 E H)
    (s : Set E) (hs : s ⊆ I.target) : I '' (I ⁻¹' s) = s := by
  rw [I.image_eq]
  rw [← Set.preimage_comp, Set.inter_comm,
    I.rightInvOn.eqOn.inter_preimage_eq]
  simp only [preimage_id_eq, id_eq, inter_eq_right]
  erw [I.range_eq_target]; exact hs

lemma NiceSubset.uniqueDiffOn (s : NiceSubset I) : UniqueDiffOn 𝕜 s.carrier := by
  have : ∃ t, IsOpen t ∧ s.carrier = (range I) ∩ t := by
    obtain ⟨c, hc, hc'⟩ := I.isEmbedding.image_eq_isOpen_inter_range s.2
    use c, hc
    rw [inter_comm, ← hc', I.image_preimage]
    simpa using s.3
  obtain ⟨t, ht, ht'⟩ := this
  rw [ht']
  exact I.uniqueDiffOn.inter ht

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
    {z : M₀} (φ : M₀ → M) (hf : MDiffAt f (φ z)) (hφ : MDiffAt φ z) :
    d% (f ∘ φ) z = d% f (φ z) ∘SL (mfderiv% φ z) := by
  sorry

lemma mychainrule {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {f : M → V} {φ : M₀ → M} {z : M₀} (hf : MDiffAt f (φ z)) (hφ : MDiffAt φ z) (v : TangentSpace I₀ z) :
    d% f (φ z) (mfderiv% φ z v) = d% (f ∘ φ) z v := by
  rw [mvfderiv_comp_left (I := I)]
  · simp
  · sorry
  · assumption

-- another missing lemma, I think!
lemma mvfderiv_restrict_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {f' : M → V} {U : Opens M} {x : M} (hx : x ∈ U) :
    d% (Set.restrict U f' : U → V) ⟨x, hx⟩ =
      d% f' x ∘SL (mfderiv% (Subtype.val : U → _) ⟨x, hx⟩):= by
  sorry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

-- This is true, but may not be what we want in general!
lemma mvfderiv_eq_fderiv {f : E → V} {x : E} :
    d% f x = (fderiv 𝕜 f x) ∘L (NormedSpace.fromTangentSpace x).toContinuousLinearMap := by
  simp only [mvfderiv, mfderiv_eq_fderiv]
  rfl

-- TODO: investigate why these are missing!
attribute [simp] mdifferentiableWithinAt_univ differentiableWithinAt_univ continuousWithinAt_univ
  mdifferentiableWithinAt_iff_differentiableWithinAt

lemma mvfderivWithin_of_isOpen {f : M → V} {s : Set M} (hs : IsOpen s) {x : M} (hx : x ∈ s) :
    d[s] f x = d% f x := by
  simp [mvfderiv, mvfderivWithin, mfderivWithin_of_isOpen hs hx]

-- we want automation to compute d% (f ∘ I), so we want a specialized version of mfderivWithin_comp
lemma mvfderiv_comp_modelWithCorners_v2 (s : NiceSubset I) {f : E → V} {x : H} (hx : I x ∈ s.carrier)
    (hf : DifferentiableWithinAt 𝕜 f s.carrier (I x)) :
    d% (f ∘ I) x = (fderivWithin 𝕜 f s.carrier (I x)) ∘L (d% I x) := by
  -- TODO fix elaborator bug in the following statement
  have unused : mvfderiv I (f ∘ I) x = mvfderivWithin I (f ∘ I) (I ⁻¹' s.carrier) x := by
    simp [mvfderiv, mvfderivWithin, mfderivWithin_of_isOpen s.2 hx]
  rw [← mfderivWithin_eq_fderivWithin, ← mvfderivWithin_of_isOpen s.2 hx]
  simp only [mvfderiv, mvfderivWithin]
  rw [mfderivWithin_comp (I' := (𝓘(𝕜, E))) (u := s.carrier) (s := I ⁻¹' s.carrier)]
  rotate_left
  · simpa
  · apply I.contMDiff.mdifferentiableWithinAt one_ne_zero
    -- apply I.contMDiff.mdifferentiableAt one_ne_zero -- missing API lemma?
  · simp
  · exact s.2.uniqueMDiffWithinAt hx
  simp only [Function.comp_apply, mfderivWithin_eq_fderivWithin]
  rw [mfderivWithin_of_isOpen s.2 hx]
  rfl

-- should we have ModelWithCorners.isNiceSubset?

-- don't want, also false in general
-- lemma mvfderiv_eq_fderivWithin' (s : NiceSubset I) {f : E → V} {x : E} (hx : x ∈ s.carrier) :
--     d% f x = (fderivWithin 𝕜 f s.carrier x) ∘L (NormedSpace.fromTangentSpace x).toContinuousLinearMap := by
--   -- note!
--   have : fderivWithin 𝕜 f s.carrier x = fderivWithin 𝕜 f (range I) x := by
--     apply fderivWithin_subset s.3 (s.uniqueDiffOn _ hx) ?_
--     sorry -- easy or missing lemma
--   rw [mvfderiv_eq_fderiv]
--   rw [fderivWithin_eq_fderiv]
--   · apply s.uniqueDiffOn.uniqueDiffWithinAt hx
--   sorry -- TODO: not true in general!

theorem Function.smul_comp {𝕜 X Y Z : Type*} [SMul 𝕜 Z] (f : Y → 𝕜) (g : Y → Z) (φ : X → Y) :
  (f • g) ∘ φ = f ∘ φ • g ∘ φ := rfl

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
    rw [mychainrule _ hφ']; swap; · exact hf.smul hg
    simp only [add_apply, smul_apply, smulRight_apply]
    rw [mychainrule hf hφ', mychainrule hg hφ']
    rw [Function.smul_comp, ← Function.comp_apply (f := f) (g := φ),
      ← Function.comp_apply (f := g) (g := φ)]
    have hf' : MDiffAt (f ∘ φ) z := hf.comp _ hφ'
    have hg' : MDiffAt (g ∘ φ) z := hg.comp _ hφ'
    specialize this hf' hg' ⟨_, .refl⟩
    exact congr($this v)
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
  -- ideally, everything is `simp` now!
  rw [restrict_smul]
  -- mdiff lemmas, like yesterday
  -- missing mathlib lemmas: relate MDiff terms to normed space world
  -- should be global simp lemmas or a simp set
  replace hf : DifferentiableWithinAt 𝕜 f' s.carrier x' := sorry
  replace hg : DifferentiableWithinAt 𝕜 g' s.carrier x' := sorry
  simp_rw [mvfderiv_restrict_apply]
  rw [← Function.smul_comp]
  -- cleanup "unmanifoldify" tactic does all of these steps; applies this conditional simp lemma
  -- and generates side goals as necessary
  rw [mvfderiv_comp_modelWithCorners_v2 s (by simpa) (by simpa [s.3 hx'] using! hf.smul hg)]
  rw [mvfderiv_comp_modelWithCorners_v2 s  (by simpa) (by simpa [s.3 hx'] using hg)]
  rw [mvfderiv_comp_modelWithCorners_v2 s (by simpa) (by simpa [s.3 hx'])]

  --set A := mfderiv I (𝓘(𝕜, E)) I (I.symm x') -- TODO: elaborators failure, fix!
  --set B := mfderiv I I Subtype.val ⟨I.symm x', hx⟩
  ext X
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply,
    smulRight_apply]
  -- This is the mathematics
  rw [fderivWithin_smul]
  · simp
  · exact s.uniqueDiffOn.uniqueDiffWithinAt hx -- missing API lemma!
  · simpa [s.3 hx'] using hf
  · simpa [s.3 hx'] using hg

  /- old proof was
  -- guess: specialized to I should be simp?
  rw [mvfderiv_comp_left (I₀ := I) I I.mdifferentiableAt (z := I.symm x') (I := 𝓘(𝕜, E))]
  rw [mvfderiv_comp_left (I₀ := I) I I.mdifferentiableAt (z := I.symm x') (I := 𝓘(𝕜, E))]
  rw [mvfderiv_comp_left (I₀ := I) I I.mdifferentiableAt (z := I.symm x') (I := 𝓘(𝕜, E))]
  have : I (I.symm x') = x' := by
    rw [← Function.comp_apply (f := I) (g := I.symm)]
    apply I.right_inv'
    grw [s.foo] at hx'
    rw [← I.range_eq_target]
    simpa
  dsimp [this]
  simp only [this]
  -- Trouble: if we rewrite by this, we cannot apply the chain rule to the fderiv
  -- as f' and g' are only differentiable on s.
  -- simp_rw [mvfderiv_eq_fderiv]
  rw [mvfderiv_comp_modelWithCorners]
  simp_rw [mvfderiv_eq_fderivWithin' s (I := I) hx]
  simp only [this]
  set A := mfderiv I (𝓘(𝕜, E)) I (I.symm x') -- TODO: elaborators failure, fix!
  set B := mfderiv I I Subtype.val ⟨I.symm x', hx⟩
  ext X
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, add_apply, smul_apply,
    smulRight_apply]
  -- This is the mathematics
  rw [fderivWithin_smul]
  · simp
  · exact s.uniqueDiffOn.uniqueDiffWithinAt hx' -- missing API lemma!
  · exact hf
  · exact hg
  -/

end
