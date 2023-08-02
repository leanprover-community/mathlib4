import Mathlib.Tactic.Functoriality.Attr
import Mathlib.Tactic.SolveByElim
import Mathlib.GroupTheory.Submonoid.Operations
import Mathlib.Topology.SubsetProperties

attribute [functor] Submonoid.map Submonoid.comap

open Lean Meta Elab Tactic
open Mathlib Tactic LabelAttr

def Lean.MVarId.solveUsingFunctors (g : MVarId) : MetaM Unit := do
  let cfg : SolveByElim.Config :=
    { maxDepth := 5, exfalso := false, symm := true, allowSynthFailures := true }
  let cfg := cfg.synthInstance
  let [] ← SolveByElim.solveByElim.processSyntax cfg false false [] [] #[mkIdent `functor] [g]
    | throwError "solve_by_elim returned subgoals: this should be impossible!"

elab "functoriality" : tactic => do
  liftMetaFinishingTactic Lean.MVarId.solveUsingFunctors

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

attribute [functor] Set.preimage

example (f : X → Y) : Set Y → Set X := by
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

def Transporter : Type := Expr → MVarId → MetaM (List (Expr × MVarId) × List (Expr × MVarId))

-- This is never actually used: it exists so we can write `partial` definitions.
instance : Inhabited Transporter where
  default _ _ := pure ([], [])

def Lean.Expr.forallE? : Expr → Option (Name × Expr × Expr × BinderInfo)
  | .forallE n t b bi => some (n, t, b, bi)
  | _ => none

def Lean.Expr.lam? : Expr → Option (Name × Expr × Expr × BinderInfo)
  | .lam n t b bi => some (n, t, b, bi)
  | _ => none

/--
This step applies when both the term `t` to transport, and the goal `g`, are for all statements.
It introduces the argument `h` of `g`, and tries to transport it, using `cont`,
to the argument of `t`, producing `h'`.
If that succeeds, evaluate `t` at that value to obtain `t'`
-/
def transportForall (cont : Transporter) : Transporter := fun t g => do
  let (h, g') ← g.intro1P
  -- withTraceNode `Tactic.transport (return m!"{·.emoji} introduced hypothesis {Expr.fvar h}") do
  -- withTraceNode `Tactic.transport (return m!"{·.emoji} remaining goal is {g'}") do
  g'.withContext do
    -- we transport `h` along `f` to whatever the type of the first argument of `t` is!
    -- withTraceNode `Tactic.transport (return m!"{·.emoji} term type is {← inferType t}") do
    let .some (_, t_arg_type, _, _) := (← whnf (← inferType t)).forallE?
      | throwError "transport failed, expected {t} to be a pi type!"
    let h' ← mkFreshExprMVar t_arg_type
    let (todo, suspended) ← cont (.fvar h) h'.mvarId!
    let t' := mkApp t h'
    return ((t', g') :: todo, suspended)

def applyTheConstructor' (mvarId : MVarId) :
    MetaM (Name × List MVarId × List MVarId × List MVarId) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `constructor
    let target ← mvarId.getType'
    matchConstInduct target.getAppFn
      (fun _ => throwTacticEx `constructor mvarId
                  m!"target is not an inductive datatype{indentExpr target}")
      fun ival us => do
        match ival.ctors with
        | [ctor] =>
          let cinfo ← getConstInfoCtor ctor
          let ctorConst := Lean.mkConst ctor us
          let (args, binderInfos, _) ← forallMetaTelescopeReducing (← inferType ctorConst)
          let mut explicit := #[]
          let mut implicit := #[]
          let mut insts := #[]
          for arg in args, binderInfo in binderInfos, i in [0:args.size] do
            if cinfo.numParams ≤ i ∧ binderInfo.isExplicit then
              explicit := explicit.push arg.mvarId!
            else
              implicit := implicit.push arg.mvarId!
              if binderInfo.isInstImplicit then
                insts := insts.push arg.mvarId!
          let e := mkAppN ctorConst args
          let eType ← inferType e
          unless (← withAssignableSyntheticOpaque <| isDefEq eType target) do
            throwError m!"type mismatch{indentExpr e}\n{← mkHasTypeButIsExpectedMsg eType target}"
          mvarId.assign e
          return (ctor, explicit.toList, implicit.toList, insts.toList)
        | _ => throwTacticEx `constructor mvarId
                m!"target inductive type does not have exactly one constructor{indentExpr target}"

/--
Looks at the head symbol of `e`,
and tries to solve the goal using that symbol applied to fresh metavariables.
If that succeeds, call `k` on each matching argument of `e` and fresh metavariable.
-/
def foo (e : Expr) (mvarId : MVarId) (k : Expr → MVarId → MetaM α) : MetaM (List α) := do
  withTraceNode `Tactic.transport (return m!"{·.emoji} note") do
  let (h, g') ← mvarId.note `h e
  withTraceNode `Tactic.transport (return m!"{·.emoji} cases") do
  let #[c] ← g'.cases h | throwTacticEx `constructor mvarId "oops, too many constructors"
  c.mvarId.withContext do
    let (ctor, explicit, _, _) ← applyTheConstructor' c.mvarId
    guard (c.ctorName = ctor)
    -- withTraceNode `Tactic.transport (return m!"{·.emoji} assign") do
    -- c.mvarId.assign e
    withTraceNode `Tactic.transport (return m!"{·.emoji} continue: {c.fields} {explicit}") do
    c.fields.toList.zip explicit |>.mapM fun ⟨e, m⟩ => k e m


def transportCongr (cont : Transporter) : Transporter := fun t g => do
  let r ← foo t g cont
  return (r.map (·.1) |>.join, r.map (·.2) |>.join)

def aesop (terminal : Bool) : Transporter := fun t g => do
  guard (← isProp (← g.getType))
  let (_, g') ← g.note `w t
  let (gs, _) ← Aesop.search g' (options := { warnOnNonterminal := false, terminal := terminal })
  return ([], gs.toList.map fun g => (t, g))

def transport1 (f : Expr) (cont : Transporter) : Transporter := fun t g => g.withContext do
  withTraceNode `Tactic.transport (return m!"{·.emoji} transport1") do
  let g_ty ← g.getType
  let t_ty ← inferType t
  withTraceNode `Tactic.transport (return m!"{·.emoji} transporting {t} from{indentExpr t_ty}\nto{indentExpr g_ty}") do
  -- TODO factor this out into a separate function.
  if ← isDefEq g_ty t_ty then do
    withTraceNode `Tactic.transport ((return m!"{·.emoji} assigning {t}")) do
      g.assign t
    return ([], [])
  -- TODO factor this out into a separate function.
  if let .some t' ← try? (mkAppM' f #[t]) then
    -- code smell: this is just doing the first branch now, can we refactor?
    if ← isDefEq g_ty (← inferType t') then
      withTraceNode `Tactic.transport ((return m!"{·.emoji} assigning {t'}")) do
        g.assign t'
      return ([], [])
  if let .some _ ← (observing? do
    withTraceNode `Tactic.transport (return m!"{·.emoji} trying aesop") do
    aesop true t g)
  then return ([], [])
  if let .some _ ← (observing? do
    -- TODO don't use hardcoded name!
    -- TODO don't duplicate `f` if it is already a hypothesis!
    -- TODO maybe better to pass `f` as an argument rather than dumping it back as a hypothesis?
    withTraceNode `Tactic.transport ((return m!"{·.emoji} attempting functoriality")) do
    let (_, g') ← g.note `f f
    g'.solveUsingFunctors) then return ([], [])
  if (← whnf g_ty).isForall then
    return ← transportForall cont t g
  if let .some r ← (observing? do transportCongr cont t g) then
    return r
  -- try
  return ([], [(t, g)])
  -- catch _ =>
  --   withTraceNode `Tactic.transport (fun _ => return m!"{crossEmoji} giving up") do
  --   return ([], [(t, g)])

def transportMany (f : Expr) : ℕ → Transporter
  | 0, _, _ => throwError "out of fuel"
  | (n+1), t, g => do
    let (todo, suspended) ← transport1 f (transportMany f n) t g
    let recursing ← todo.mapM fun ⟨t', g'⟩ => transportMany f n t' g'
    return (recursing.map (·.1) |>.join, suspended :: recursing.map (·.2) |>.join)

def transport (f t : Expr) (g : MVarId) : MetaM (List MVarId) := do
  let ([], suspended) ← transportMany f 100 t g
    | throwError "transport finished, but there were still active subtasks!"
  suspended.mapM fun ⟨t', g'⟩ => do
    -- FIXME don't use a hardcoded name (if `t` was a local hypothesis, replace it?)
    let (_, g'') ← g'.note `w t'
    pure g''

syntax "transport" ppSpace term:max "along" ppSpace term:max : tactic

/-- A user-facing tactic that just calls the plumbing. -/
-- To see how to do this, look for examples of `macro`, `elab`,
-- or `syntax` and `elab_rules`.
elab_rules : tactic
  | `(tactic| transport $t:term along $f:term) => do
    let t ← elabTermForApply t
    let f ← Term.elabTerm f none
    liftMetaTactic (transport f t)

set_option trace.Tactic.transport true

example (w : ∀ n : Nat, n > 1) : ∀ n : Nat, n > 1 := by
  transport w along id

example (w : α) (f : α → β) : β := by
  transport w along f

example (w : ∀ n : Nat, n > 1) : ∀ n : Nat, n > 0 := by
  transport w along id
  guard_hyp w : n > 1
  guard_target = n > 0
  admit

example (w : ∀ n : Int, n > 1) : ∀ n : Nat, n > 0 := by
  transport w along Int.ofNat
  guard_hyp w : Int.ofNat n > 1
  guard_target = n > 0
  admit

example (w : ∀ n : Int, n > 0) : ∀ n : Nat, n > 0 := by
  transport w along Int.ofNat

example : (by transport (0 : ℕ) along (fun (n : ℕ) => (n+1, n+2)) : ℕ × ℕ) = (1, 2) := rfl

example (f : X → Y) (s : Set Y) : Set X := by
  transport s along f

example (f : X → Y) : (fun s => by transport s along f : Set Y → Set X) = fun s => f ⁻¹' s := rfl

example (f : X → Y) (t : (ι : Type) → (ι → Set Y)) : (ι : Type) → (ι → Set X) :=
  by transport t along f

example (f : X → Y) (t : {ι : Type} → (ι → Set Y)) : {ι : Type} → (ι → Set X) :=
  by transport t along f

example (f : X → Y) (t : X × X) : (by transport t along f : Y × Y) = (f t.1, f t.2) := rfl

noncomputable def Function.Surjective.choose {f : X → Y} (hf : f.Surjective) (y : Y) :=
  (hf y).choose

@[simp]
theorem Function.Surjective.choose_spec {f : X → Y} (hf : f.Surjective) (y : Y) :
    f (hf.choose y) = y :=
  (hf y).choose_spec

attribute [functor] Function.Surjective.choose

example (f : X → Y) (hf : f.Surjective) (y : Y) : (by transport y along f : X) = hf.choose y := rfl
example (f : X → Y) (hf : f.Surjective) (y : Y) : f (by transport y along f : X) = y := by simp


variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] in
example (f : X → Y) (hf : f.Surjective) (hf_cont : Continuous f) (hX : MyCompact X) :
    MyCompact Y := by
  transport hX along f
