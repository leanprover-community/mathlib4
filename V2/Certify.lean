import MetaCompute.V2.PrattLemmas
import Batteries.Tactic.NoMatch
import Mathlib.Lean.Message
import Mathlib.Tactic.NormNum.Prime
import MetaCompute.V2.PowMod

open Nat

inductive MPrattCertificate : Type
  | small (n : ℕ)
  | big (n : ℕ) (root : ℕ) (factors : List MPrattCertificate)
  deriving Repr, BEq, Lean.ToExpr

inductive PrattEntry : Type
  | small (n : ℕ)
  | big (n : ℕ) (root : ℕ) (factors : List ℕ)
  deriving Repr, BEq, Lean.ToExpr

def PrattCertificate : Type := List PrattEntry
  deriving Repr, BEq, Lean.ToExpr

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

syntax "mathematica" ppSpace mpratt_certificate : pratt_certificate
syntax num : mpratt_certificate
syntax "{" num "," ppSpace num "," ppSpace "{" mpratt_certificate,+ "}" "}" : mpratt_certificate

syntax "builder" ppSpace bpratt_certificate : pratt_certificate
syntax "[" bpratt_entry,* "]" : bpratt_certificate
syntax num : bpratt_entry
syntax "(" num "," num "," "[" num,* "]" ")" : bpratt_entry

partial def MPrattCertificate.ofSyntax : TSyntax `mpratt_certificate → MetaM MPrattCertificate
  | `(mpratt_certificate| $n:num) => return small n.getNat
  | `(mpratt_certificate| {$n:num, $root:num, { $[$factors],* }}) => do
    let n := n.getNat
    if n < 100 then return small n
    let root := root.getNat
    let factors ← factors.mapM ofSyntax
    return big n root factors.toList
  | _ => throwError "Invalid Pratt certificate syntax"

partial def PrattCertificate.ofSyntax : TSyntax `pratt_certificate → MetaM MPrattCertificate
  | `(pratt_certificate| mathematica $n:mpratt_certificate) => MPrattCertificate.ofSyntax n
  | _ => throwUnsupportedSyntax

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
  `(pratt_certificate| mathematica $cert)

end

def testInput : String :=
  "{7919, 7, {2, {37, 2, {2, {3, 2, {2}}}}, {107, 2, {2, {53, 2, {2, {13, 2, {2, {3, 2, {2}}}}}}}}}}"
def testMyInput : String :=
  "[2, (3, 2, [2]), 7, (127, 3, [2, 3, 7])]"

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

def processEntryAux (m : Std.TreeMap ℕ Expr) (p p' root : ℕ) (pE rootE : Expr)
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
    let some (hq : Expr) := m.get? q | throwError "error 6"
    let hpow ← Tactic.powMod.provePowModNe root o p 1 rootE oE pE (mkNatLit 1)
    pf ← mkAppM ``prove_prime_step #[pE, rootE, qE, oE, tE, mkNatLit r, mkNatLit k,
      ← mkEqRefl oE, hq, ← mkEqRefl tE, hpow, pf]
  return (t, pf)

lemma Nat.prime_thirteen : Nat.Prime 13 := by norm_num
lemma Nat.prime_seventeen : Nat.Prime 17 := by norm_num
lemma Nat.prime_nineteen : Nat.Prime 19 := by norm_num
lemma Nat.prime_twentyThree : Nat.Prime 23 := by norm_num
lemma Nat.prime_twentyNine : Nat.Prime 29 := by norm_num
lemma Nat.prime_thirtyOne : Nat.Prime 31 := by norm_num
lemma Nat.prime_thirtySeven : Nat.Prime 37 := by norm_num
lemma Nat.prime_fortyOne : Nat.Prime 41 := by norm_num
lemma Nat.prime_fortyThree : Nat.Prime 43 := by norm_num
lemma Nat.prime_fortySeven : Nat.Prime 47 := by norm_num
lemma Nat.prime_fiftyThree : Nat.Prime 53 := by norm_num
lemma Nat.prime_fiftyNine : Nat.Prime 59 := by norm_num
lemma Nat.prime_sixtyOne : Nat.Prime 61 := by norm_num
lemma Nat.prime_sixtySeven : Nat.Prime 67 := by norm_num
lemma Nat.prime_seventyOne : Nat.Prime 71 := by norm_num
lemma Nat.prime_seventyThree : Nat.Prime 73 := by norm_num
lemma Nat.prime_seventyNine : Nat.Prime 79 := by norm_num
lemma Nat.prime_eightyThree : Nat.Prime 83 := by norm_num
lemma Nat.prime_eightyNine : Nat.Prime 89 := by norm_num
lemma Nat.prime_ninetySeven : Nat.Prime 97 := by norm_num

def processEntry (m : Std.TreeMap ℕ Expr) : PrattEntry → MetaM (Std.TreeMap ℕ Expr)
  | .small 2 => return insert (2, mkConst ``Nat.prime_two) m
  | .small 3 => return insert (3, mkConst ``Nat.prime_three) m
  | .small 5 => return insert (5, mkConst ``Nat.prime_five) m
  | .small 7 => return insert (7, mkConst ``Nat.prime_seven) m
  | .small 11 => return insert (11, mkConst ``Nat.prime_eleven) m
  | .small 13 => return insert (13, mkConst ``Nat.prime_thirteen) m
  | .small 17 => return insert (17, mkConst ``Nat.prime_seventeen) m
  | .small 19 => return insert (19, mkConst ``Nat.prime_nineteen) m
  | .small 23 => return insert (23, mkConst ``Nat.prime_twentyThree) m
  | .small 29 => return insert (29, mkConst ``Nat.prime_twentyNine) m
  | .small 31 => return insert (31, mkConst ``Nat.prime_thirtyOne) m
  | .small 37 => return insert (37, mkConst ``Nat.prime_thirtySeven) m
  | .small 41 => return insert (41, mkConst ``Nat.prime_fortyOne) m
  | .small 43 => return insert (43, mkConst ``Nat.prime_fortyThree) m
  | .small 47 => return insert (47, mkConst ``Nat.prime_fortySeven) m
  | .small 53 => return insert (53, mkConst ``Nat.prime_fiftyThree) m
  | .small 59 => return insert (59, mkConst ``Nat.prime_fiftyNine) m
  | .small 61 => return insert (61, mkConst ``Nat.prime_sixtyOne) m
  | .small 67 => return insert (67, mkConst ``Nat.prime_sixtySeven) m
  | .small 71 => return insert (71, mkConst ``Nat.prime_seventyOne) m
  | .small 73 => return insert (73, mkConst ``Nat.prime_seventyThree) m
  | .small 79 => return insert (79, mkConst ``Nat.prime_seventyNine) m
  | .small 83 => return insert (83, mkConst ``Nat.prime_eightyThree) m
  | .small 89 => return insert (89, mkConst ``Nat.prime_eightyNine) m
  | .small 97 => return insert (97, mkConst ``Nat.prime_ninetySeven) m
  | .small _ => throwError "bad small prime"
  | .big p root factors => do
    for q in factors do unless (m.get? q).isSome do throwError "error 5"
    unless p ≥ 12 do throwError "error 4"
    let p' : ℕ := p - 1
    let pE : Expr := mkNatLit p
    let p'E : Expr := mkNatLit p'
    let rootE : Expr := mkNatLit root
    let (last, pf) ← processEntryAux m p (p - 1) root pE rootE factors
    unless last = p - 1 do throwError "bad factorization {factors} of {p - 1} (missing {(p - 1) / last})"
    let hpow ← Tactic.powMod.provePowModEq root p' p 1 rootE p'E pE
    let pf ← mkAppM ``prove_prime_end #[pE, p'E, mkNatLit root, ← mkEqRefl (mkNatLit p), hpow, pf]
    return insert (p, pf) m

def prove_prime (cert : PrattCertificate) (goal : MVarId) : MetaM Expr := do
  let t ← goal.getType
  let some nE := (← whnfR t).app1? ``Nat.Prime | throwError "goal not a primality test"
  let some n := nE.nat? | throwError "not a numeral"
  let data ← cert.foldlM processEntry ∅
  trace[debug] "{data.toArray}"
  let some pf := data.get? n | throwError "the certificate doesn't prove this prime"
  return pf

elab "pratt " certificate:pratt_certificate : tactic => liftMetaFinishingTactic fun goal ↦ do
  match certificate with
  | `(pratt_certificate| mathematica $cert:mpratt_certificate) =>
    let cert := reformat (← MPrattCertificate.ofSyntax cert)
    let pf ← prove_prime cert goal
    goal.assign pf
  | _ => throwUnsupportedSyntax -- TODO: ADD OTHER THINGS!!!!!!

syntax "prime " : tactic

elab_rules : tactic
  | `(tactic| prime%$tk) => liftMetaFinishingTactic fun goal ↦ do
    let t ← goal.getType
    let some nE := t.app1? ``Nat.Prime | throwError "goal not a primality test"
    let some n := nE.nat? | throwError "not a numeral"
    let code := s!"Needs[\"PrimalityProving`\"]; p = {n}; PrimalityProving`PrimeQCertificate[p, \"SmallPrime\" -> p + 1]"
    let out ← IO.Process.output {cmd := "wolframscript", args := #["-code", code]}
    let out := out.stdout
    match Parser.runParserCategory (← getEnv) `mpratt_certificate out with
    | .error e =>
      throwError s!"failed to parse mathematica output\nparser error: {e}\noutput: {out}"
    | .ok certStx =>
      let certStx : TSyntax `mpratt_certificate := .mk certStx
      let certM ← MPrattCertificate.ofSyntax certStx
      let cert := reformat certM
      let pf ← prove_prime cert goal
      let stx ← MPrattCertificate.toSyntax certM
      let _ ← TryThis.addSuggestion tk (← `(tactic| pratt $stx))
      goal.assign pf

end
