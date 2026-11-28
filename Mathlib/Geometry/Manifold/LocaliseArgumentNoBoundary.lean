module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Topology.Sets.OpenCover

-- Experiments: localisation arguments in differential geometry
-- in Utrecht (June 10), Christian Merten, Edward van de Meent, Michael Rothgang
-- more polished version: seems to work for manifolds without boundary

@[expose] section

open NormedSpace ContinuousLinearMap
open scoped Manifold

set_option warn.sorry false
set_option linter.style.longLine false


-- TODO: make 𝕜 configurable!

-- science fiction: everything is in Type
-- cannot do this because universes!
-- given two manifolds, models with corners between them and a map, Prop sth

-- should this be an abbrev?
def ManifoldFunctionProperty : Type 1 :=
  ∀ {𝕜 : Type} [NontriviallyNormedField 𝕜]
    {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {H' : Type} [TopologicalSpace H']
    {N : Type} [TopologicalSpace N] [ChartedSpace H' N]
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F H')
    (f : M → N),
    Prop

open scoped ContDiff
variable {n : ℕ∞ω}

namespace ManifoldFunctionProperty

structure RespectsDiffeo (P : ManifoldFunctionProperty) where
  pre : ∀
    {𝕜 : Type} [NontriviallyNormedField 𝕜]
    {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {HM : Type} [TopologicalSpace HM]
    {M₁ : Type} [TopologicalSpace M₁] [ChartedSpace HM M₁]
    {E' : Type} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {HM' : Type} [TopologicalSpace HM']
    {M₂ : Type} [TopologicalSpace M₂] [ChartedSpace HM' M₂]
    {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {HN : Type} [TopologicalSpace HN]
    {N : Type} [TopologicalSpace N] [ChartedSpace HN N]
    (I : ModelWithCorners 𝕜 E HM) (I' : ModelWithCorners 𝕜 E' HM') (J : ModelWithCorners 𝕜 F HN)
    (φ : Diffeomorph I I' M₁ M₂ n) (f : M₂ → N),
    P I J (f ∘ φ) ↔ P I' J f
  post : ∀
    {𝕜 : Type} [NontriviallyNormedField 𝕜]
    {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {HM : Type} [TopologicalSpace HM]
    {M₁ : Type} [TopologicalSpace M₁] [ChartedSpace HM M₁]
    {E' : Type} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {HM' : Type} [TopologicalSpace HM']
    {M₂ : Type} [TopologicalSpace M₂] [ChartedSpace HM' M₂]
    {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {HN : Type} [TopologicalSpace HN]
    -- XXX: rename to M, N₁ and N₂
    {N : Type} [TopologicalSpace N] [ChartedSpace HN N]
    (I : ModelWithCorners 𝕜 E HM) (I' : ModelWithCorners 𝕜 E' HM') (J : ModelWithCorners 𝕜 F HN)
    (f : M₁ → M₂) (φ : Diffeomorph I' J M₂ N n),
    P I J (φ ∘ f) ↔ P I I' f

variable (P : ManifoldFunctionProperty)

-- VS Code snippets for all the boilerplate to copy-paste?
open TopologicalSpace

structure IsLocalOnSource extends RespectsDiffeo (n := n) P where
  -- If `P` holds for `f : M → N`, it also holds for any restriction to an open subset of `V`
  restr :
    ∀ {𝕜 : Type} [NontriviallyNormedField 𝕜]
    {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {H' : Type} [TopologicalSpace H']
    {N : Type} [TopologicalSpace N] [ChartedSpace H' N]
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F H')
    (f : M → N),
    P I J f ↔
      ∀ (V : Opens M),
      P I J (f ∘ (Subtype.val : V → M))
  of_isOpenCover : -- additional universe parameter, which we take from M
    ∀ {𝕜 : Type} [NontriviallyNormedField 𝕜]
    {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {H' : Type} [TopologicalSpace H']
    {N : Type} [TopologicalSpace N] [ChartedSpace H' N]
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F H')
    {ι : Type} -- of M
    {U : ι → Opens M} -- FIXME: make `U` is TopologicalSpace.isOpenCover
    (_hU : IsOpenCover U)
    (f : M → N) (_hf : ∀ i, P I J (f ∘ (Subtype.val : U i → M))),
    P I J f

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
  {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {N : Type} [TopologicalSpace N] [ChartedSpace H' N]
  {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H'' : Type} [TopologicalSpace H'']
  {I₀ : ModelWithCorners 𝕜 F H''} {M₀ : Type} [TopologicalSpace M₀] [ChartedSpace H'' M₀]

-- open question: do we want n as regularity parameter?
-- the inclusion of U into M is true for any n...
variable (I J n) in
def IsOpenImmersion (f : M → N) : Prop :=
  ∃ U : Opens N, ∃ φ : Diffeomorph I J M U n, (Subtype.val ∘ φ) = f
-- lemma: is a smooth embedding with open range, yada yada (and conversely...)
-- is antitone in the regularity

def IsOpenImmersion.isOpen_range {f : M → N} (hf : IsOpenImmersion n I J f) : IsOpen (Set.range f) := by
  sorry

def IsOpenImmersion.range {f : M → N} (_hf : IsOpenImmersion n I J f) : Opens N :=
  ⟨Set.range f, _hf.isOpen_range⟩

-- noncomputable def IsOpenImmersion.toPartialEquiv {φ : M₀ → M} (hφ : IsOpenImmersion n I₀ I φ) :
--     PartialEquiv M₀ M := by
--   choose U ψ hψ using hφ
--   exact {
--     toFun := φ
--     invFun :=
--       --#check Function.extend
--       --let ψ' : M → U := sorry
--       --let sdf := (Subtype.val : U → M) ∘ ψ.toFun
--       sorry--sdf
--     source := Set.univ
--     target := U
--     map_source' := sorry
--     map_target' := sorry
--     left_inv' := sorry
--     right_inv' := sorry
--   }

-- #exit
-- noncomputable def IsOpenImmersion.toPartialDiffeomorph {φ : M₀ → M} (hφ : IsOpenImmersion n I₀ I φ) :
--     PartialDiffeomorph I₀ I M₀ M n := by

--   exact ⟨
--     toOpenPartialHomeomorph := φ.to


--   sorry --where--:= by

-- #exit
/-- The inclusion `U ↪ M` of any open subset is an open immersion. -/
lemma isOpenImmersion_subtypeVal (U : Opens M) : IsOpenImmersion n I I (Subtype.val : U → M) :=
  ⟨U, Diffeomorph.refl I U n, by simp⟩

-- given any open immersion, pre-composing with that open immersion preserves P
lemma foo {f : M → N} {ι : M₀ → M} (hP : IsLocalOnSource P (n := n))
    (hf : IsOpenImmersion n I₀ I ι) (hf' : P I J f) :
    P I₀ J (f ∘ ι) := by
  obtain ⟨U, φ, rfl⟩ := hf
  rw [← Function.comp_assoc, hP.pre]
  rw [hP.restr] at hf'
  apply hf'

section practice1

-- Question. If I really want to do this local business, do I need to switch to MfldCat
-- in the middle of the proof, perform my reduction to some normed space, and continue
-- in the unbundled style?
variable (hP : IsLocalOnSource P (n := n))
    {ι : Type}
    {E : ι → Type} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    {H : ι → Type} [∀ i, TopologicalSpace (H i)]
    {M : ι → Type} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
    {I : (i : ι) → ModelWithCorners 𝕜 (E i) (H i)}
    {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {H' : Type} [TopologicalSpace H']
    {N : Type} [TopologicalSpace N] [ChartedSpace H' N]
    {G : Type} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {H'' : Type} [TopologicalSpace H'']
    {N' : Type} [TopologicalSpace N'] [ChartedSpace H'' N']
    {J : ModelWithCorners 𝕜 F H'} {J' : ModelWithCorners 𝕜 G H''}
    -- family of open immersions Mᵢ → N
    {φ : (i : ι) → (M i) → N} (hφ : ∀ i, IsOpenImmersion n (I i) J (φ i))
    -- family is jointly surjective
    (H : ⋃ i, Set.range (φ i) = Set.univ)
    (f : N → N')
    (hfφ : ∀ i, P (I i) J' (f ∘ φ i))

-- define IsOpenImmersion.range : Opens N, show the underlying set is the Set.range
-- show the API lemma below

-- practice for Michael: prove the Sum.elim thing with it

include hφ hfφ hP H in
lemma bar : P J J' f := by
  -- construct open cover of N (via the images of φ i)
  -- add lemma above: range of each φ i is open
  -- or choose...
  choose U σ hσ using hφ
  have : IsOpenCover U := sorry -- easy, use H
  apply hP.of_isOpenCover (U := U)
  · apply this
  · intro i
    rw [← hP.pre _ _ _ (σ i)]
    rw [Function.comp_assoc]
    rw [hσ]
    exact hfφ i

  -- at some point, bundle into an open cover structure?
  -- with nice constructors, refining things
-- N and P also manifolds

-- perhaps have a binary version for convenience?
-- is is ![] convenient enough, with Fin 2 as index type?

end practice1

-- next example to practice
lemma mvfderiv_add' {f g : M → 𝕜} {z : M} (hf : MDiffAt f z) (hg : MDiffAt g z) :
    d% (f + g) z = d% f z + d% g z := sorry

-- but perhaps let's do this one first
lemma mvfderiv_smul' {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {f : M → 𝕜} {g : M → V} {x : M}
    (hf : MDiffAt f x) (hg : MDiffAt g x) :
    d% (f • g) x = f x • d% g x + (d% f x).smulRight (g x) := by
  /-refine HasMFDerivAt.mfderiv ⟨hf.continuousAt.smul hg.continuousAt, ?_⟩
  convert hf.hasMFDerivAt.2.smul hg.hasMFDerivAt.2
  simp
  rfl -- about `fromTangentSpace` only-/
  sorry

/-
Def. md is *local* if md_x f = md_x (f ∘ ι) for any manifold `V` and smooth open embedding `ι : V → M` (i.e., smooth embedding with open range)
-/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] {f : M → V}

-- also missing
def IsOpenImmersion.isLocalDiffeomorph {φ : M₀ → M} (hφ : IsOpenImmersion n I₀ I φ) :
    IsLocalDiffeomorph I₀ I n φ := by
  -- better proof: use composition properties of LocalDiffeomorph
  -- and add those in the process
  sorry

noncomputable def IsOpenImmersion.mfderivToCLE {φ : M₀ → M} (hφ : IsOpenImmersion n I₀ I φ) (z : M₀) (hn : n ≠ 0) :
  TangentSpace I₀ z ≃L[𝕜] TangentSpace I (φ z) := (hφ.isLocalDiffeomorph z).mfderivToContinuousLinearEquiv hn

-- missing API lemma, exercise for Christian
lemma mvfderiv_comp_left {z : M₀} (φ : M₀ → M) (hφ : MDiffAt φ z) :
    d% (f ∘ φ) z = d% f (φ z) ∘SL (mfderiv% φ z) := by
  sorry

-- step 1: reduce to local neighbourhoods
/-
lemma baz {φ : M₀ → M} {hφ : IsOpenImmersion n I₀ I φ} {z : M₀} (v : TangentSpace I₀ z) (hn : n ≠ 0) :
    d% f (φ z) (mfderiv% φ z v) = d% (f ∘ φ) z v := by
  obtain ⟨U, ψ, rfl⟩ := hφ
  have missing1 : MDiffAt (Subtype.val : U → M) (ψ z) :=
    contMDiff_subtype_val.mdifferentiable hn .. -- missing lemma
  rw [mfderiv_comp (I' := I)]
  rotate_left
  · exact missing1
  · exact ψ.mdifferentiable hn _
  rw [← Function.comp_assoc]
  rw [mvfderiv_comp_left (I := I)]; rotate_left
  · exact ψ.mdifferentiable hn _
  rw [mvfderiv_comp_left (I := I)]
  · simp only [Function.comp_apply, coe_comp']; rfl
  · exact contMDiff_subtype_val.mdifferentiable hn .. -/

-- XXX also add unapplied version... well, we kinda have
lemma baz' {φ : M₀ → M} {z : M₀} {hφ : MDiffAt φ z} (v : TangentSpace I₀ z) :
    d% f (φ z) (mfderiv% φ z v) = d% (f ∘ φ) z v := by
  rw [mvfderiv_comp_left (I := I)]
  · simp
  · assumption

-- TODO: put n in a sensible position in IsOpenImmersion: want it to be I J n f

-- TODO: this is false for manifolds with boundary! (is true without)
lemma baz'' {z : M} :
    ∃ (U : Opens E) (f : U → M) (hf : IsOpenImmersion n 𝓘(𝕜, E) I f),
    z ∈ Set.range f := by
  let φ := extChartAt I z
  use ⟨φ.target, sorry⟩ -- is false in general!
  --let f : φ.target → M := fun ⟨z, hz⟩ ↦ sorry
  --use φ.symm.toFun
  sorry -- by definition of a manifold, just use

-- instead, should we define "PartialDiffeomorph'" (without the openness constraint)
-- and work with that? differentials are still invertible either way
----> define PartialDiffeomorph' and prove all the necessary lemmas
-- let's do a sci-fi proof for now, working with baz''

-- WLOG, ∃ U : Opens E s.t. M = U --- cannot say this because things are unbundled
--   MfldCat would really help here
-- Christian's vision
-- easy tactic to write: take the goal and "bundle everything",
-- i.e. turn the goal into sth about MfldCat
-- then do local reduction, obtain on the equality (only have some Open E left)
-- then "unbundle everything"
-- the simp (to reduce the goal from sth `mvfderiv` in normed space to `fderiv`)

-- M is bad if it is equal to itself
-- but now we can do bad things :-)
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

/- elaborators test case; can we support this?
lemma mvfderiv_restrict_apply {f' : E → 𝕜} {U : Opens E} {x : E} (hx : x ∈ U) :
    d% (U.restrict f') ⟨x, hx⟩ = d% f' x := sorry
-/

lemma mvfderiv_restrict_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {f' : M → V} {U : Opens M} {x : M} (hx : x ∈ U) :
    d% (Set.restrict U f' : U → V) ⟨x, hx⟩ =
      d% f' x ∘SL (mfderiv% (Subtype.val : U → _) ⟨x, hx⟩):= by
  sorry

lemma restrict_smul {f : M → 𝕜} {g : M → V} (U : Set M) :
  (Set.restrict U f • Set.restrict U g) = U.restrict (f • g) := sorry

lemma restrict_smul_apply {f : M → 𝕜} {g : M → V} (U : Set M) {x : U} :
  (Set.restrict U f • Set.restrict U g) x = U.restrict (f • g) x := sorry

lemma mvfderiv_eq_fderiv {f : E → V} {x : E} :
  d% f x = (fderiv 𝕜 f x) ∘L (NormedSpace.fromTangentSpace x).toContinuousLinearMap := by
  sorry

lemma mvfderiv_smul'' {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {f : M → 𝕜} {g : M → V} {x : M}
    (hf : MDiffAt f x) (hg : MDiffAt g x) :
    d% (f • g) x = f x • d% g x + (d% f x).smulRight (g x) := by
  wlog h : ∃ (U : Opens E), ImBad M I U 𝓘(𝕜, E)
  · -- simp lemma where `this` is simplified with conclusion of `ImBad` might be nice
    -- all proofs of ImBad will be `⟨⟨⟩, rfl⟩`
    sorry -- easy for a human to mechanically fill in, but annoying to write a tactic for
  -- the "un-subtypifying" is very automatable?
  obtain ⟨U, ⟨⟩⟩ := h
  -- there's no M in the goal any more! (but everything is about a function U → 𝕜)
  clear! M
  clear! H
  -- step two: "unsubtypify tactic", extensible
  obtain ⟨f', rfl⟩ := Set.restrict_surjective f
  -- should be in mathlib; I believe this is true but haven't checked very carefully
  replace hf : MDiffAt[U.1] f' x := sorry
  obtain ⟨g', rfl⟩ := Set.restrict_surjective g
  replace hg : MDiffAt[U.1] g' x := sorry
  obtain ⟨x, hx⟩ := x
  -- careful: dsimp will dsimp in some places now; model with corners needs an Opens... don't do this!
  -- missing mathlib lemmas: relate MDiff terms to normed space world
  -- should be global simp lemmas or a simp set
  replace hf : DifferentiableWithinAt 𝕜 f' U x := sorry
  replace hg : DifferentiableWithinAt 𝕜 g' U x := sorry
  dsimp
  rw [restrict_smul]
  simp_rw [mvfderiv_restrict_apply, mvfderiv_eq_fderiv]
  ext X
  rw [fderiv_smul]
  · simp
  · sorry -- true given U open
  · sorry -- true given U open
  -- argue: every property that held globally on M now holds on s

end ManifoldFunctionProperty

end
