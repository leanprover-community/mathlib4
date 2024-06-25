import Mathlib.Tactic

/-example : False := by
  have a : 1 = 1 := by rfl
  sorry
axiom f : Nat → Nat
#check 1 + f 2
axiom F : List Nat → List Nat → List Nat
#check [1] ++ F [2] [2]-/

open Std Tactic Lint Lean Meta Elab Tactic
deriving instance Repr for StructureInfo

class A (T : Type) where
  a : Nat

class B (T : Type) [A T] : Prop where
  hb : 0 < a

class C (T : Type) [A T] : Prop where
  hc : a < 7

class BC (T : Type) [A T] extends B T, C T -- bad

class BC' (T : Type) [A T] extends B T, C T -- good
instance (T : Type) [A T] [B T] [C T] : BC' T where

class FO (T S : Type) where
  hh : 1 = 1
class BC'hard (T : Type) [A T] extends FO T ℕ,  B T, C T -- bad
variable (T : Type) [A T]
-- #synth BC' T -- no loop
class BCD (T : Type) [A T] extends B T, C T where
  hd : a = 1

def canSynth (name : Name) : MetaM Bool :=
do
  -- let e ← getEnv
  let en ← getEnv
  let some _ := getStructureInfo? en name | return false
    -- if (a.fieldInfo.filter (fun fi : StructureFieldInfo => fi.subobject? = none)).size ≠ 0 then
  dbg_trace (repr <| getAllParentStructures en name)
  let d ← getConstInfoInduct name
  -- let m ← (mkFreshExprMVar)
  -- TODO use getStructureCtor
  -- mkFresheExprMVar -- TODO typo in core
  dbg_trace  d.type
  dbg_trace  d.numParams
  let e : Expr := d.type
  let .mvar m ← mkFreshExprMVar e | return false -- TODO fail here
  -- let _ ← Tactic.run m do
  let (_, m') ← m.introNP d.numParams
  m'.withContext do
    let g ← getLCtx
    -- let .some t := g.decls[0]! | failure
    -- let (t : FVarId) := t.fvarId
    withLocalDeclsD ((getAllParentStructures en name).map
        (fun ps : Name => (`a, fun _ : Array Expr => do mkAppOptM ps <| g.decls.toArray.map (Option.map <| fun d => .fvar d.fvarId)))) -- TODO universes
      fun _ => do
      -- let g' ← getLCtx
      -- TODO surely a better way to slice?
      -- toArray.extract 0 d.numParams |>.
      let g ← getLCtx
      dbg_trace (repr <| g.decls.toArray.map (Option.map <| fun d => d.type))
      let ins ← mkAppOptM name <| g.decls.toArray.extract 0 d.numParams |>.map (Option.map <| fun d => .fvar d.fvarId)
      dbg_trace ins

      -- let e := .app (mkConst `B) (.fvar t)
      -- dbg_trace e
      let si ← synthInstance ins
      dbg_trace si
  return true

--#eval canSynth `BC'


@[std_linter] def freeInstances : Lint.Linter where
  noErrorsFound := "There are \"free\" instance that should be added."
  errorsFound := "UNUSED ARGUMENTS."
  test declName := do
    if ← isAutoDecl declName then return none
    -- Skip anything not classes
    let e ← getEnv
    -- TODO consider non-structure classes also? likely pointless
    let some a := getStructureInfo? e declName | return none
    if !isClass e declName then return none
    -- if ← isProjectionFn declName then return none
    -- let info ← getConstInfo declName
    -- let ty := info.type
    -- TODO decidable array ne
    if (a.fieldInfo.filter (fun fi : StructureFieldInfo => fi.subobject? = none)).size ≠ 0 then
      return none
    if ← canSynth declName then return none
    return ((toString (repr a)) ++ (toString <| repr (getAllParentStructures e declName)))
    --findField?
    -- let some val := info.value? | return none
    -- return "Class has a possible free instance that does not exist"
    -- forallTelescope ty fun args ty => do
    --   let mut e := (mkAppN val args).headBeta
    --   e := mkApp e ty
    --   for arg in args do
    --     let ldecl ← getFVarLocalDecl arg
    --     e := mkApp e ldecl.type
    --     if let some val := ldecl.value? then
    --       e := mkApp e val
    --   let unused := args.zip (.range args.size) |>.filter fun (arg, _) =>
    --     !e.containsFVar arg.fvarId!
    --   if unused.isEmpty then return none
    --   addMessageContextFull <| .joinSep (← unused.toList.mapM fun (arg, i) =>
    --       return m!"argument {i+1} {arg} : {← inferType arg}") m!", "

-- instance (T : Type) [hA : A T] [hB : B T] [hC : C T] : BC T  :=
-- { hA, hB, hC with }

--#lint only freeInstances
-- #lint only freeInstances in Std
-- #lint freeInstances in Mathlib
