import Mathlib.Tactic.Functoriality.Attr
import Mathlib.Tactic.SolveByElim
import Mathlib.GroupTheory.Submonoid.Operations
import Mathlib.Topology.SubsetProperties

attribute [functor] Submonoid.map Submonoid.comap

open Lean Meta Elab Tactic
open Mathlib Tactic LabelAttr

def solveUsingFunctors (g : MVarId) : MetaM Unit := do
  let cfg : SolveByElim.Config :=
    { maxDepth := 5, exfalso := false, symm := true, allowSynthFailures := true }
  let cfg := cfg.synthInstance
  let [] ← SolveByElim.solveByElim.processSyntax cfg false false [] [] #[mkIdent `functor] [g]
    | throwError "solve_by_elim returned subgoals: this should be impossible!"

elab "functoriality" : tactic => do
  liftMetaFinishingTactic solveUsingFunctors

example [Monoid M] [Monoid N] (f : M →* N) : Submonoid M → Submonoid N := by
  apply (config := {allowSynthFailures := true}) Submonoid.map
  swap
  exact f
  infer_instance

set_option trace.Meta.Tactic.solveByElim true in
example [Monoid M] [Monoid N] (f : M →* N) : Submonoid M → Submonoid N := by
  functoriality

example [Monoid M] [Monoid N] (f : M →* N) : Submonoid N → Submonoid M := by
  functoriality

section compact

-- Minimal contrasting examples: compactness vs sequential compactness

def MyCompact (X : Type) [TopologicalSpace X] :=
  ∀ {ι : Type} {U : ι → Set X} (_ : ∀ i, IsOpen (U i)) (_ : Set.univ ⊆ ⋃ i, U i),
  ∃ t : Finset ι, Set.univ ⊆ ⋃ i ∈ t, U i

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]


-- attribute [simp] IsOpen.preimage
attribute [aesop safe apply] IsOpen.preimage
example (f : X → Y) (hf : f.Surjective) (hf_cont : Continuous f) (hX : MyCompact X) :
  MyCompact Y := by
. --
  intro ι
  specialize @hX ι
  --
  intro U
  specialize @hX (λ i ↦ f ⁻¹' (U i)) -- surjectivity (preimages of sets)
  --
  intro hU_open
  specialize hX ?_
  . --
    intro i
    specialize hU_open i
    --
    aesop -- required: attribute [aesop safe apply] IsOpen.preimage. or attribute [simp]
    -- simp [*]
    -- exact IsOpen.preimage hf_cont hU_open -- found by library_search
  --
  intro hU_cover
  specialize hX ?_
  --
  intro x
  specialize @hU_cover (f x) -- mapped (x : X) to (f x : Y)
  --
  convert _ ∘ hU_cover ∘ _ <;>
  clear hU_cover
  . --rw? -- rw? causes a PANIC
    -- this works:
      -- intro _
      -- simp [*] at *
      -- assumption
    -- this works:
      -- rintro ⟨_, ⟨⟨i, rfl⟩, hx⟩⟩
      -- refine ⟨_, ⟨⟨i, rfl⟩, hx⟩⟩
    -- this works:
    aesop
  --
  . aesop
    -- exact id
  --
  . obtain ⟨t, ht⟩ := hX
    use t
    --
    intro y
    obtain ⟨x, rfl⟩ := hf y -- choose preimage of y
    specialize @ht x
    --
    aesop
    -- aesop works starting here
    -- intro hy
    -- specialize ht hy -- or something (this is very trivial)
    -- --
    -- -- specialize @ht (hf y).choose
    -- -- intros y hy
    -- -- set x := (hf y).choose
    -- -- have hx : f x = y := (hf y).choose_spec
    -- -- clear_value x
    -- -- subst hx
    -- -- specialize @ht x trivial -- surjectivity (elementwise)
    -- --
    -- rw [Set.mem_iUnion] at ht ⊢ -- annoying
    -- obtain ⟨i, ht⟩ := ht
    -- use i
    -- --
    -- rw [Set.mem_iUnion] at ht ⊢ -- annoying
    -- obtain ⟨hi, ht⟩ := ht
    -- use hi
    -- --
    -- exact ht

@[simp] lemma image_of_exists (f : X → Y) (w : ∃ a, f a = y) : f (Exists.choose w) = y :=
  Exists.choose_spec w

def MySeqCompact (X : Type) [TopologicalSpace X] :=
  ∀ (α : ℕ → X),
  ∃ (β : ℕ → ℕ) (x : X),
  ∀ (U : Set X) (_ : IsOpen U) (_ : x ∈ U),
  ∃ (N : ℕ),
  ∀ (n : ℕ) (_ : n ≥ N), α (β n) ∈ U

example (f : X → Y) (hf : f.Surjective) (hf_cont : Continuous f) (hX : MySeqCompact X) :
  MySeqCompact Y := by
  set g : Y → X := (Classical.axiomOfChoice hf).choose
  have hg : ∀ y, f (g y) = y := (Classical.axiomOfChoice hf).choose_spec
  clear_value g
  -- clear hf
  --
  intro α
  specialize hX ?_
  . clear g hg
    intro n
    specialize α n
    exact (hf α).choose
  -- specialize hX (g ∘ α)
  --
  obtain ⟨β, hβ⟩ := hX
  use β
  --
  obtain ⟨x, hx⟩ := hβ
  use f x
  --
  intro U
  specialize hx (U.preimage f) -- use preimage "f.comap U"
  --
  intro hU
  specialize hx (by aesop)
  -- specialize hx (hU.preimage hf_cont)
  --
  intro hxU
  specialize hx hxU
  --
  obtain ⟨N, hN⟩ := hx
  use N
  --
  intro n
  specialize hN n
  --
  intro hnN
  specialize hN hnN
  --
  aesop

#check IsCompact
example (f : X → Y) (hf : f.Surjective) (hf_cont : Continuous f) (hX : CompactSpace X) :
  CompactSpace Y := by
. constructor
  rcases hX with ⟨hX⟩
  --
  intro s
  specialize @hX (s.comap f)
  --
  intro hs
  specialize @hX ?_
  . exact Filter.NeBot.comap_of_surj hs hf -- needs to be found by functoriality
  convert _ ∘ hX ∘ _ <;> clear hX <;> intro h
  . obtain ⟨x, hx⟩ := h
    use f x
    constructor
    . replace hx := hx.1
      aesop
    . replace hx := hx.2
      sorry


end compact
