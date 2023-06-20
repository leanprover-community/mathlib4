import Mathlib.Data.Vector
import Mathlib.Data.Vector.MapNorm
import Mathlib.Data.Bitvec.Ruleset
import Mathlib.Data.Fintype.Card
import Qq

namespace Vector

  /-
    TODO: this should probably go to a separate file
  -/
  namespace Tactic
    open Lean Meta Elab.Tactic Qq

    variable  {α : Q(Type u)}
              {β : Q(Type v)}
              {γ : Q(Type w)}
              {σ₁ : Q(Type q)}
              {σ₂ : Q(Type r)}

    #check inferInstance
    #check QQ
    #check synthInstanceQ


    protected partial def enumerate (α : Q(Type u)) : MetaM <| List (Q($α)) := do
      return []
    --   let inst ← synthInstanceQ (q(Fintype $α) : Q(Type u))
    --   withTransparency (mode := TransparencyMode.all) do
    --     let n : Q(ℕ) ← reduceAll <| q(@Fintype.card $α $inst)

    --     if ←isDefEq n q(Nat.zero) then
    --       return []
    --     let n ← match n with
    --       | ~q(Nat.succ $n) => pure n
    --       | _ => throwError "Failed to reduce `{n}`"

    --     let f : Q(Fin ($n+1) → $α) ← reduce' <| q((@Fintype.equivFin $α $inst).invFun)
    --     go f n
    -- where
    --   go {n : Q(Nat)} (f : Q(Fin ($n+1) → $α)) : Q(Nat) → MetaM (List Q($α))
    --     -- | ~q(Nat.succ $i) => do
    --     --     -- let x ← reduceAll <| q($f (Fin.ofNat $i))
    --     --     let x : Q($α) := q($f (Fin.ofNat $i))
    --     --     let xs ← go f i
    --     --     return x :: xs
    --     | ~q(Nat.zero) => do
    --         let x : Q($α) := q($f 0)
    --         let x ← reduce' x
    --         pure [x]
    --     | _ => pure []

    -- #eval Tactic.enumerate q(Empty)
    -- #eval Tactic.enumerate q(Unit)

    protected partial def get_bisim_relation
                              (s₁ : Q($σ₁)) (s₂ : Q($σ₂))
                              (next_states : Q($σ₁) → Q($σ₂) → MetaM (List (Q($σ₁) × Q($σ₂))))
    : MetaM <| Array (Q($σ₁) × Q($σ₂)) := do
      let mut new_states : Array (Q($σ₁) × Q($σ₂)) := #[(s₁, s₂)]
      let mut R : Array (Q($σ₁) × Q($σ₂)) := #[]

      while !new_states.isEmpty do
        let cur := new_states.back
        new_states := new_states.pop

        R := R.push cur
        let ⟨s₁, s₂⟩ := cur;

        for next in (←next_states s₁ s₂) do
          if !R.contains next && !new_states.contains next then
            new_states := new_states.push next

      return R

    protected def get_bisim_relation_unary  (f : Q($α → $σ₁ → $σ₁ × $β))
                                            (g : Q($α → $σ₂ → $σ₂ × $β))
                                            (s₁ : Q($σ₁)) (s₂ : Q($σ₂))
          : MetaM (Array (Q($σ₁) × Q($σ₂))) := do
      let enumerate_inputs ← Tactic.enumerate α
      Tactic.get_bisim_relation s₁ s₂ fun s₁ s₂ =>
        enumerate_inputs.mapM fun (input_bit : Q($α)) => do
          let o₁ : Q($σ₁ × $β) ← reduce q($f $input_bit $s₁)
          let o₂ : Q($σ₂ × $β) ← reduce q($g $input_bit $s₂)

          if !(←isDefEq q(($o₁).snd) q(($o₂).snd)) then
            -- TODO: improve this error
            throwError "Failed to show that `{f} {input_bit} {s₁}` and `{g} {input_bit} {s₂}` agree on the output bit (`{o₁}` vs `{o₂}`)"

          let q₁ ← reduce q(($o₁).fst)
          let q₂ ← reduce q(($o₂).fst)
          return (q₁, q₂)



    -- #check Tactic.bisim_unary

    -- @[aesop safe tactic (rule_sets [Mathlib.Data.Bitvec])]
    def bisim : TacticM Unit := do
      withMainContext do
        evalTactic <|<- `(tactic| simp only [map_to_mapAccumr, map₂_to_mapAccumr₂])
        let (goal : Q(Prop)) ← getMainTarget
        goal.check
        go goal
      where go : Q(Prop) → TacticM Unit
          | ~q(@Vector.mapAccumr $α $γ _ $σ₁ $f $xs $s₁ = Vector.mapAccumr $g $xs' $s₂) => do
              if !(←isDefEq xs xs') then
                throwError "Failed to unify\n\t{xs}\nand\n\t{xs'}"
              let R ← Tactic.get_bisim_relation_unary f g s₁ s₂
              dbg_trace "{R}"
          | ~q((@Vector.mapAccumr $α $γ _ $σ₁ $f $xs $s₁).snd = (Vector.mapAccumr $g $xs' $s₂).snd) => do
              if !(←isDefEq xs xs') then
                throwError "Failed to unify\n\t{xs}\nand\n\t{xs'}"
              let R ← Tactic.get_bisim_relation_unary f g s₁ s₂
              dbg_trace "{R}"
          | ~q((@Vector.mapAccumr₂ $α $β $γ _ $σ₁ $f $xs $ys $s₁).snd = (Vector.mapAccumr $g $xs' $s₂).snd) => do
              if !(←isDefEq xs xs') then
                throwError "Failed to unify\n\t{xs}\nand\n\t{xs'}"
              let R ← Tactic.get_bisim_relation_unary f g s₁ s₂
              dbg_trace "{R}"
          | goal => throwError
"Expected goal of form
  mapAccumr ?f ?xs ?s = mapAccumr ?g ?xs ?s'
Found:
  {goal}
"


    elab "bisim" : tactic => bisim

  end Tactic
end Vector
