/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.V2.PrattLemmas
import Batteries.Tactic.NoMatch
import Mathlib.Lean.Message
import Mathlib.Tactic.NormNum.Prime
import Mathlib.V2.PowMod

open Nat

namespace Tactic.Prime

inductive MPrattCertificate : Type
  | small (n : ℕ)
  | big (n : ℕ) (root : ℕ) (factors : List MPrattCertificate)
  deriving Repr, BEq, Lean.ToExpr

inductive PrattEntry : Type
  | small (n : ℕ)
  | big (n : ℕ) (root : ℕ) (factors : List ℕ)
  deriving Repr, BEq, Lean.ToExpr, Lean.FromJson

def PrattCertificate : Type := List PrattEntry
  deriving Repr, BEq, Lean.ToExpr, Lean.FromJson

def PrattEntry.out : PrattEntry → ℕ
  | .small n => n
  | .big n _ _ => n

def testPratt : PrattCertificate := [.small 2, .big 3 2 [2], .big 37 2 [2, 3]]

def MPrattCertificate.out : MPrattCertificate → ℕ
  | .small n => n
  | .big n _ _ => n

def reformatAux : MPrattCertificate → Std.TreeMap ℕ PrattEntry
  | .small n => {(n, .small n)}
  | .big n root factors =>
      if n ≤ 11 then {(n, .small n)} else
      (factors.map reformatAux).foldl (.mergeWith (fun _ a _ => a))
      {(n, .big n root (factors.map (·.out)))}

def reformat : MPrattCertificate → PrattCertificate := Std.TreeMap.values ∘ reformatAux

section

open Lean Elab

declare_syntax_cat pratt_certificate
declare_syntax_cat mpratt_certificate
declare_syntax_cat bpratt_certificate
declare_syntax_cat bpratt_entry

syntax mpratt_certificate : pratt_certificate
syntax num : mpratt_certificate
syntax "{" num "," ppSpace num "," ppSpace "{" mpratt_certificate,+ "}" "}" : mpratt_certificate

syntax bpratt_certificate : pratt_certificate
syntax "[" bpratt_entry,* "]" : bpratt_certificate
syntax num : bpratt_entry
syntax "(" num "," ppSpace num "," ppSpace "[" num,* "]" ")" : bpratt_entry

partial def MPrattCertificate.ofSyntax : TSyntax `mpratt_certificate → MetaM MPrattCertificate
  | `(mpratt_certificate| $n:num) => return small n.getNat
  | `(mpratt_certificate| {$n:num, $root:num, { $[$factors],* }}) => do
    let n := n.getNat
    if n < 100 then return small n
    let root := root.getNat
    let factors ← factors.mapM ofSyntax
    return big n root factors.toList
  | e => throwError "Invalid mathematica Pratt certificate syntax {e}"

partial def PrattEntry.ofSyntax : TSyntax `bpratt_entry → MetaM PrattEntry
  | `(bpratt_entry| $n:num) => return .small n.getNat
  | `(bpratt_entry| ( $n:num, $root:num, [ $[$nums],* ] )) => do
      let n := n.getNat
      let root := root.getNat
      let nums := nums.map (·.getNat)
      return .big n root nums.toList
  | e => throwError "Invalid builder Pratt entry syntax {e}"

partial def PrattCertificate.ofSyntaxAux : TSyntax `bpratt_certificate → MetaM PrattCertificate
  | `(bpratt_certificate| [ $[$entries],* ] ) => do
    let entries ← entries.mapM PrattEntry.ofSyntax
    return entries.toList
  | e => throwError "Invalid builder Pratt certificate syntax {e}"

partial def PrattCertificate.ofSyntax : TSyntax `pratt_certificate → MetaM PrattCertificate
  | `(pratt_certificate| $n:mpratt_certificate) => do
      let i ← MPrattCertificate.ofSyntax n
      return reformat i
  | `(pratt_certificate| $n:bpratt_certificate) => PrattCertificate.ofSyntaxAux n
  | e => throwError "Invalid Pratt certificate syntax {e}"

partial def PrattEntry.toSyntax : PrattEntry → MetaM (TSyntax `bpratt_entry)
  | .small n => do
      let n := Lean.Syntax.mkNatLit n
      `(bpratt_entry| $n:num)
  | .big n root factors => do
      let n := Lean.Syntax.mkNatLit n
      let root := Lean.Syntax.mkNatLit root
      let factors := factors.toArray.map Lean.Syntax.mkNatLit
      `(bpratt_entry| ($n:num, $root:num, [ $[$factors],* ]))

partial def PrattCertificate.toSyntax (i : PrattCertificate) :
    MetaM (TSyntax `bpratt_certificate) := do
  let j ← i.toArray.mapM (·.toSyntax)
  `(bpratt_certificate| [ $[$j],* ] )

partial def MPrattCertificate.toSyntaxAux : MPrattCertificate → MetaM (TSyntax `mpratt_certificate)
  | .small n => do
      let n := Lean.Syntax.mkNatLit n
      `(mpratt_certificate| $n:num)
  | .big n root factors => do
      let n := Lean.Syntax.mkNatLit n
      let root := Lean.Syntax.mkNatLit root
      let factors ← factors.toArray.mapM toSyntaxAux
      `(mpratt_certificate| {$n:num, $root:num, { $[$factors],* }})

partial def MPrattCertificate.toSyntax
    (c : MPrattCertificate) : MetaM (TSyntax `pratt_certificate) := do
  let cert ← c.toSyntaxAux
  `(pratt_certificate| $cert:mpratt_certificate)

end

section test

def testInput : String :=
  "{7919, 7, {2, {37, 2, {2, {3, 2, {2}}}}, \
  {107, 2, {2, {53, 2, {2, {13, 2, {2, {3, 2, {2}}}}}}}}}}"

def testMyInput : String :=
  "[2, (3, 2, [2]), 7, (127, 3, [2, 3, 7])]"

open Lean

/--
info: {7919, 7, {2, {37, 2, {2, {3, 2, {2}}}}, {107, 2, {2, {53, 2, {2, {13, 2, {2, {3, 2, {2}}}}}}}}}}
-/
#guard_msgs in
#eval show MetaM _ from do
  let i ← IO.ofExcept (Parser.runParserCategory (← getEnv) `mpratt_certificate testInput)
  Lean.PrettyPrinter.ppTerm ⟨i⟩

/-- info: [2, (3, 2, [2]), 7, (127, 3, [2, 3, 7])] -/
#guard_msgs in
#eval show MetaM _ from do
  let i ← IO.ofExcept (Parser.runParserCategory (← getEnv) `bpratt_certificate testMyInput)
  Lean.PrettyPrinter.ppCategory `bpratt_certificate i

end test

section

open Lean Elab Meta Tactic Qq

def extractFactor.acc (p q i : ℕ) (hq : 1 < q) : ℕ × ℕ :=
  if hp₀ : p = 0 then (0, i)
  else if p % q = 0 then
    have : p / q < p := Nat.div_lt_self (by omega) hq
    acc (p / q) q (i + 1) hq
  else (p, i)
  -- partial_fixpoint

/--
Given `p q : ℕ`, find the unique `r k : ℕ` such that `r * q ^ k = p` and `r` is not divisible by `q`
-/
def extractFactor (p q : ℕ) : ℕ × ℕ :=
  if hq : q ≤ 1 then (p, 0) else extractFactor.acc p q 0 (lt_of_not_le hq)

def processEntryAux (m : Std.TreeMap ℕ (Expr × Expr)) (p p' root : ℕ) (pE rootE : Expr)
    (factors : List ℕ) :
    MetaM (ℕ × Expr) := do
  let mut t : ℕ := 1
  let mut res : ℕ := p'
  -- cur * res = p'
  let mut pf ← mkAppM ``pratt_axiom #[pE, rootE]
  -- pf will be a proof of `pratt_predicate p root t`
  for q in factors do
    let (spare, k) := extractFactor res q -- r * q ^ k = res
    if k = 0 then logWarning m!"unused factor {q} in factorization {factors} of {p - 1}"
    let r := t
    t := t * q ^ k
    res := spare
    let tE : Expr := mkNatLit t
    let qE : Expr := mkNatLit q
    let o : ℕ := (p - 1) / q
    let oE : Expr := mkNatLit o
    let some ((hq : Expr), _) := m.get? q | throwError s!"purported prime {q} not in certificate"
    let hpow ← Tactic.powMod.provePowModNe root o p 1 rootE oE pE (mkNatLit 1)
    pf ← mkAppM ``prove_prime_step #[pE, rootE, qE, oE, tE, mkNatLit r, mkNatLit k,
      ← mkEqRefl oE, hq, ← mkEqRefl tE, hpow, pf]
  return (t, pf)

lemma Nat.prime_2 : Nat.Prime 2 := by norm_num
lemma Nat.prime_3 : Nat.Prime 3 := by norm_num
lemma Nat.prime_5 : Nat.Prime 5 := by norm_num
lemma Nat.prime_7 : Nat.Prime 7 := by norm_num
lemma Nat.prime_11 : Nat.Prime 11 := by norm_num
lemma Nat.prime_13 : Nat.Prime 13 := by norm_num
lemma Nat.prime_17 : Nat.Prime 17 := by norm_num
lemma Nat.prime_19 : Nat.Prime 19 := by norm_num
lemma Nat.prime_23 : Nat.Prime 23 := by norm_num
lemma Nat.prime_29 : Nat.Prime 29 := by norm_num
lemma Nat.prime_31 : Nat.Prime 31 := by norm_num
lemma Nat.prime_37 : Nat.Prime 37 := by norm_num
lemma Nat.prime_41 : Nat.Prime 41 := by norm_num
lemma Nat.prime_43 : Nat.Prime 43 := by norm_num
lemma Nat.prime_47 : Nat.Prime 47 := by norm_num
lemma Nat.prime_53 : Nat.Prime 53 := by norm_num
lemma Nat.prime_59 : Nat.Prime 59 := by norm_num
lemma Nat.prime_61 : Nat.Prime 61 := by norm_num
lemma Nat.prime_67 : Nat.Prime 67 := by norm_num
lemma Nat.prime_71 : Nat.Prime 71 := by norm_num
lemma Nat.prime_73 : Nat.Prime 73 := by norm_num
lemma Nat.prime_79 : Nat.Prime 79 := by norm_num
lemma Nat.prime_83 : Nat.Prime 83 := by norm_num
lemma Nat.prime_89 : Nat.Prime 89 := by norm_num
lemma Nat.prime_97 : Nat.Prime 97 := by norm_num

def processEntry (m : Std.TreeMap ℕ (Expr × Expr)) :
    PrattEntry → MetaM (Std.TreeMap ℕ (Expr × Expr))
  | .small p => do
    let mv ← mkFreshExprMVar
      (some (← mkAppM ``Nat.Prime #[mkNatLit p]))
      (userName := .mkSimple s!"prime_{p}")
    let pf := mkConst (.str `Tactic.Prime.Nat s!"prime_{p}")
    return insert (p, (mv, pf)) m
  | .big p root factors => do
    unless p ≥ 2 do
      throwError "error 4"
    let p' : ℕ := p - 1
    let pE : Expr := mkNatLit p
    let p'E : Expr := mkNatLit p'
    let rootE : Expr := mkNatLit root
    let (last, pf) ← processEntryAux m p (p - 1) root pE rootE factors
    unless last = p - 1 do
      throwError "bad factorization {factors} of {p - 1} (missing {(p - 1) / last})"
    let hpow ← Tactic.powMod.provePowModEq root p' p 1 rootE p'E pE
    let pf ← mkAppM ``prove_prime_end #[p'E, rootE, ← mkEqRefl pE, hpow, pf]
    let i ← mkFreshExprMVar
      (some (← mkAppM ``Nat.Prime #[pE]))
      (userName := .mkSimple s!"prime_{p}")
    return insert (p, (i, pf)) m

def prove_prime (cert : PrattCertificate) (n : ℕ) : MetaM Expr := do
  let data ← cert.foldlM processEntry ∅
  trace[debug] "{data.toArray}"
  let some (pf, _) := data.get? n | throwError "the certificate doesn't prove {n} is prime"
  data.foldrM (init := pf) fun _ (hmq, hpq) pf =>
    mkLetFun hmq hpq pf

elab "pratt" ppSpace certificate:pratt_certificate : tactic => liftMetaFinishingTactic fun goal ↦ do
  match certificate with
  | `(pratt_certificate| $cert:pratt_certificate) =>
    let cert ← PrattCertificate.ofSyntax cert
    let t := (← goal.getType'').consumeMData
    let some nE := t.app1? ``Nat.Prime | throwError "goal for `pratt` not a primality test"
    let some n := nE.nat? | throwError "not a numeral"
    let pf ← prove_prime cert n
    goal.assign pf

inductive Primality.Generator
  | sage | mathematica | native

structure Primality.Config where
  generator : Primality.Generator := .sage

declare_config_elab elabPrimeConfig Primality.Config

def sageScript (n : ℕ) : String :=
  (include_str "prime_sage_helper.py") ++ "\n" ++ s!"main({n})"

def mathematicaScript (n : ℕ) : String :=
  s!"Needs[\"PrimalityProving`\"];\n\
  p = {n};\n\
  PrimalityProving`PrimeQCertificate[p, \"SmallPrime\" -> p + 1]"

/-- The result of a sage call in the success case. -/
structure SageSuccess where
  /-- The main result of the function call is an array of polynomials
  parallel to the input list of hypotheses and an exponent for the goal. -/
  data : String
  deriving FromJson, Repr

/-- The result of a sage call in the failure case. -/
structure SageError where
  /-- The error kind -/
  name : String
  /-- The error message -/
  value : String
  deriving FromJson

/-- The result of a sage call. -/
def SageResult := Except SageError SageSuccess

/-- Parse a `SageResult` from the raw SageMath API output. -/
instance : FromJson SageResult where fromJson? j := do
  -- we expect the output has either "success": true and contains "stdout",
  -- or has "success": false and error information under "execute_reply"
  if let .ok true := j.getObjValAs? Bool "success" then
    -- parse SageSuccess from stdout, which is formatted as SageCoeffAndPower
    -- (see sageCreateQuery for the format of stdout)
    let stdout ← j.getObjValAs? String "stdout"
    let coeffAndPower ← Json.parse stdout >>= fromJson?
    let sageSuccess := { data := coeffAndPower }
    return .ok sageSuccess
  else
    -- parse SageError from execute_reply
    let executeReply ← j.getObjVal? "execute_reply"
    let errorName ← executeReply.getObjValAs? String "ename"
    let errorValue ← executeReply.getObjValAs? String "evalue"
    return .error { name := errorName, value := errorValue }

def extractCertificate (env : Environment) (out : String) : Except String Syntax := do
  let out ← Json.parse out
  if let .ok true := out.getObjValAs? Bool "success" then
    let stdout ← out.getObjValAs? String "stdout"
    Parser.runParserCategory env `bpratt_certificate stdout
  else
    -- parse SageError from execute_reply
    let executeReply ← out.getObjVal? "execute_reply"
    let errorName ← executeReply.getObjValAs? String "ename"
    let errorValue ← executeReply.getObjValAs? String "evalue"
    .error s!"SageMath error: {errorName}: {errorValue}"

def makeCertificate (n : ℕ) (gen : Primality.Generator) : MetaM PrattCertificate := do
  match gen with
  | .sage =>
    let data := s!"code={System.Uri.escapeUri (sageScript n)}"
    let apiUrl := "https://sagecell.sagemath.org/service"
    let curlArgs := #["-X", "POST", "--data-raw", data, apiUrl]
    let out ← IO.Process.output {cmd := "curl", args := curlArgs}
    if out.exitCode ≠ 0 then
      IO.throwServerError <|
        "Could not send API request to SageMath. " ++
        s!"curl exited with code {out.exitCode}:\n{out.stderr}"
    match extractCertificate (← getEnv) out.stdout with
    | .error e =>
      IO.throwServerError <|
        s!"Could not parse SageMath output (error: {e})\nSageMath output:\n{out.stdout}\n\
        The most likely reason for this is that the input {n} was not prime."
    | .ok certStx =>
      let certStx : TSyntax `bpratt_certificate := .mk certStx
      let certStx ← `(pratt_certificate| $certStx:bpratt_certificate)
      PrattCertificate.ofSyntax certStx

  | .native => throwError "native computation not implemented"
  | .mathematica =>
    let code := mathematicaScript n
    let out ← IO.Process.output {cmd := "wolframscript", args := #["-code", code]}
    if out.exitCode != 0 then
      IO.throwServerError <|
        "Could not make call request to wolframscript. " ++
        s!"curl exited with code {out.exitCode}:\n{out.stderr}"
    let out := out.stdout
    match Parser.runParserCategory (← getEnv) `mpratt_certificate out with
      | .error e =>
        throwError s!"failed to parse mathematica certificate output\n\
          The most likely reason for this is that the input {n} was not prime.\n\
          parser error: {e}\noutput: {out}"
      | .ok certStx =>
        let certStx : TSyntax `mpratt_certificate := .mk certStx
        let certStx ← `(pratt_certificate| $certStx:mpratt_certificate)
        PrattCertificate.ofSyntax certStx

syntax "prime" Parser.Tactic.optConfig ppSpace : tactic

elab_rules : tactic
  | `(tactic| prime%$tk $cfg:optConfig) => do
    let config ← elabPrimeConfig cfg
    liftMetaFinishingTactic fun goal ↦ do
      let t := (← goal.getType'').consumeMData
      let some nE := t.app1? ``Nat.Prime | throwError "goal for `prime` not a primality test"
      let some n := nE.nat? | throwError "not a numeral"
      let cert ←
        if n < 100 then pure [.small n]
        else makeCertificate n config.generator
      let pf ← prove_prime cert n
      let stx ← PrattCertificate.toSyntax cert
      let _ ← TryThis.addSuggestion tk (origSpan? := ← getRef)
        (← `(tactic| pratt $stx:bpratt_certificate))
      goal.assign pf

end

end Tactic.Prime

example : Nat.Prime 47867742232066880047611079 := by pratt
    [2, 3, 5, 7, 11, 17, 23, 29, 31, 37, 47, 67, 83, (167, 5, [2, 83]), (283, 3, [2, 3, 47]),
      (4663, 3, [2, 3, 7, 37]), (5011, 2, [2, 3, 5, 167]), (62311, 6, [2, 3, 5, 31, 67]),
      (214499, 2, [2, 23, 4663]), (1123145497, 7, [2, 3, 11, 283, 5011]),
      (90101681149415123, 2, [2, 11, 17, 214499, 1123145497]),
      (47867742232066880047611079, 3, [2, 3, 7, 29, 62311, 90101681149415123])]

-- set_option exponentiation.threshold 3913 in
-- example : Nat.Prime (3 * 2 ^ 3912 + 1) := by
--   simp only [reducePow, reduceMul, reduceAdd]
--   pratt builder [2, 3, (127780414391497973212171930170926986757577048484820926201064729783485263494817422495127775983679039078116803697168137524940219819335799478153348592755198599590903607242050230924443865709697486743641039970666450337071378658828331722728467720393963808366917988956767802913905167890490075236068196363700359481304279948916896583006686025357237170212018946813663108217900835975808683160984117514866915965161953626338070145596982334808959718966160701183250747572515090867613655044807172211728519357721287835503689517292364425608325467094686443862517374850243698013720305871319056887431952190952721719757200172695537054790570648290887720009455171821568413052107356003828041937567129362866696549587422369864562815134637684140271767482353107080370450890024342225936273158281477009232714640818424893445193089479459814572594522258577931514012256573162006292678354475638319009668319255772179069845291474717503333030909793536116894869761453687330048252587304656806182949368202671739705463406846852567720022377005763291104588535681445561286808586673846016527511475331939430139687698419185010117348285933672139833826832898565919546377321517928825162277951756632134321102813522053716838646284289
-- , 11, [2, 3])]
