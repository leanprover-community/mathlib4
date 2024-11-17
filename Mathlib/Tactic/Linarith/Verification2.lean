import Mathlib.Tactic.Linarith.Verification

open Lean Elab Tactic Meta

namespace Linarith

/-! ### Auxiliary functions for assembling proofs -/

def addNegEqProofs2 : List (Syntax.Term × Expr) → MetaM (List ((Bool × Syntax.Term) × Expr))
  | [] => return []
  | (stx, pf) :: tl => do
    let l := (← addNegEqProof pf).map (fun (pos, pf) ↦ ((pos, stx), pf))
    return l ++ (← addNegEqProofs2 tl)

/-! #### The main method -/

instance : Quote ℤ where quote
  | .ofNat n => quote n
  | .negSucc n => Unhygienic.run `(-$(quote (n + 1)))

instance : Quote ℚ where
  quote q :=
    if q.den = 1 then quote q.num
    else Unhygienic.run `($(quote q.num) / $(quote q.den))

def mkLinearCombinationTerm (d : ℕ) : List ((Bool × Syntax.Term) × ℕ) → TermElabM Syntax.Term
  | [] => failure
  | ((pos, hyp), n) :: l => do
    let q : ℚ := _root_.mkRat n d
    match l with
    | [] =>
      if q == 1 then
        if pos then
          pure hyp
        else
          ``(-$hyp)
      else
        let a : Syntax.Term := quote (if pos then q else -q)
        ``($a * $hyp)
    | _ => do
      let a : Syntax.Term := quote q
      let stx ← if q == 1 then pure hyp else ``($a * $hyp)
      let l ← mkLinearCombinationTerm d l
      if pos then
        ``($l + $stx)
      else
        ``($l - $stx)

def findLinearCombination (transparency : TransparencyMode) (oracle : CertificateOracle)
    (phantomHypType : Expr) (type : Expr) (l : List (Syntax.Term × Expr)) :
    TermElabM Syntax.Term := do
  trace[linarith.detail] "Beginning work in `findLinearCombination`."
  -- for the elimination to work properly, we must add a proof of `-1 < 0` to the list,
  -- along with negated equality proofs.
  let l' ← addNegEqProofs2 l
  let inputsAux := l'.reverse
  let inputtpsAux ← ((inputsAux.map Prod.snd).mapM (m := MetaM) inferType)
  trace[linarith.detail] "... finished `addNegEqProofs`."
  let oneLtZero := ← mkNegOneLtZeroProof type
  let oneLtZeroPfTyp ← inferType oneLtZero
  trace[linarith.detail] "... finished `mkNegOneLtZeroProof`."
  let (comps, max_var) ←
    linearFormsAndMaxVar transparency (phantomHypType :: oneLtZeroPfTyp :: inputtpsAux)
  trace[linarith.detail] "... finished `linearFormsAndMaxVar`."
  trace[linarith.detail] "{comps}"
  -- perform the elimination and fail if no contradiction is found.
  let certificate : Batteries.HashMap Nat Nat ← try
    oracle.produceCertificate comps max_var
  catch e =>
    trace[linarith] e.toMessageData
    throwError "linarith? failed to find a contradiction"
  trace[linarith] "linarith? has found a contradiction: {certificate.toList}"
  match certificate[0]? with
  | none => throwError "no need to use linear_combination: hypotheses are mutually contradictory"
  | some denom =>
  let enum_inputsAux := inputsAux.enum
  -- construct a list pairing nonzero coeffs with the proof of their corresponding comparison
  let zip : List ((Bool × Term) × ℕ) :=
    enum_inputsAux.filterMap fun ⟨n, e⟩ => certificate[n+2]?.map (e.1, ·)
  mkLinearCombinationTerm denom zip.reverse

end Linarith
