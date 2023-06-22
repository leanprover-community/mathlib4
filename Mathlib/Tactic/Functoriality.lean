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
  -- set g : Y → X := (Classical.axiomOfChoice hf).choose
  -- have hg : ∀ y, f (g y) = y := (Classical.axiomOfChoice hf).choose_spec
  -- clear_value g
  -- clear hf
  -- clear g hg
  --
  intro α
  specialize hX ?_
  . intro n
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

--   convert_to IsCompact (f '' Set.univ)
--   . sorry
  -- exact IsCompact.image hX hf_cont
example (f : X → Y) (hf : f.Surjective) (hf_cont : Continuous f) (hX : CompactSpace X) :
  CompactSpace Y := by
  constructor
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
  sorry

end compact

-- structure TransportCtx where
--   term : Expr
--   goal : MVarId

def Transporter : Type := Expr → MVarId → MetaM (List (Expr × MVarId))

-- This is never actually used: it exists so we can write `partial` definitions.
instance : Inhabited Transporter where
  default _ _ := pure []

def Lean.Expr.forallE? : Expr → Option (Name × Expr × Expr × BinderInfo)
  | .forallE n t b bi => some (n, t, b, bi)
  | _ => none

def Lean.Expr.lam? : Expr → Option (Name × Expr × Expr × BinderInfo)
  | .lam n t b bi => some (n, t, b, bi)
  | _ => none

def transportForall (_f : Expr) (_cont : Transporter) : Transporter := fun t g => do
  let (h, g) ← g.intro1P
  g.withContext do
    -- We need to get the `Expr` corresponding to `h` (which is just an `FVarId`)
    let h := (← h.getDecl).toExpr -- FIXME what is the colloquialism here?
    -- TODO we need to transport `h` along `f` to whatever the type of the first argument of `t` is!
    -- FIXME cleanup!!
    trace[Tactic.transport] t
    let .some (_, t_arg_type, _, _) := (← inferType t).forallE? | throwError "foo"
    let synthetic_goal ← mkFreshExprMVar t_arg_type
    let [] ← _cont h synthetic_goal.mvarId! | throwError "transporting the argument failed"
    let t' ← mkAppM' t #[synthetic_goal]
    return [(t', g)]

def transport1 (f : Expr) (cont : Transporter) : Transporter := fun t g => do
  let ty ← g.getType
  if ← isDefEq ty (← inferType t) then
    g.assign t
    return []
  if let .some t' ← try? (mkAppM' f #[t]) then
    -- code smell: this is just doing the first branch now, can we refactor?
    if ← isDefEq ty (← inferType t') then
      g.assign t'
      return []
  if ty.isForall then
    return ← transportForall f cont t g
  throwError "transport doesn't know what to do yet!"

-- FIXME probably better to use fuel rather than a `partial` def.
partial def transportMany (f : Expr) : Transporter := fun t g => do
  -- TODO call transport1 repeatedly not just once
  transport1 f (transportMany f) t g

def transport (f t : Expr) (g : MVarId) : MetaM (List MVarId) := do
  (← transportMany f t g).mapM fun ⟨t', g'⟩ => do
    -- FIXME don't use a hardcoded name `w
    let (_, g'') ← g'.note `w t'
    pure g''

syntax "transport" ppSpace term:max "along" ppSpace term:max : tactic

/-- A user-facing tactic that just calls the plumbing. -/
-- To see how to do this, look for examples of `macro`, `elab`,
-- or `syntax` and `elab_rules`.
elab_rules : tactic
  | `(tactic| transport $t:term along $f:term) => do
    -- Let's hand off to a "plumbing" function in `MetaM` right away.
    -- This means we need to 1) change `f` and `t` from ``TSyntax `term`` to `Expr`,
    -- and we need to 2) get the main goal, and afterwards reset the user's goals.
    -- For 1), we need `elabTerm`:
    let t ← Term.elabTerm t none
    let f ← Term.elabTerm f none
    -- For 2):
    -- let g ← getMainGoal
    -- let gs ← ourAwesomeTactic g t f
    -- replaceMainGoal gs
    liftMetaTactic (transport f t)

set_option trace.Tactic.transport true

example (w : ∀ n : Nat, n > 1) : ∀ n : Nat, n > 1 := by
  transport w along id

example (w : α) (f : α → β) : β := by
  transport w along f

example (w : ∀ n : Nat, n > 1) : ∀ n : Nat, n > 0 := by
  transport w along id

example (w : ∀ n : Int, n > 1) : ∀ n : Nat, n > 0 := by
  transport w along Int.ofNat

example (w : ∀ n : Int, n > 0) : ∀ n : Nat, n > 0 := by
  transport w along Int.ofNat

example : (by transport (0 : ℕ) along (fun (n : ℕ) => (n+1, n+2)) : ℕ × ℕ) = (1, 2) := rfl
