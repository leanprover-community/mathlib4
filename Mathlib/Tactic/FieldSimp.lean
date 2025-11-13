/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, David Renshaw, Heather Macbeth, Arend Mellendijk, Michael Rothgang
-/
import Mathlib.Data.Ineq
import Mathlib.Tactic.FieldSimp.Attr
import Mathlib.Tactic.FieldSimp.Discharger
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Util.AtLocation
import Mathlib.Util.AtomM.Recurse
import Mathlib.Util.SynthesizeUsing

/-!
# `field_simp` tactic

Tactic to clear denominators in algebraic expressions.
-/

open Lean Meta Qq

namespace Mathlib.Tactic.FieldSimp

initialize registerTraceClass `Tactic.field_simp

variable {v : Level} {M : Q(Type v)}

section DischargeM

inductive ProofKind : Type
  | nonzero : ProofKind
  | positive : ProofKind
deriving BEq, Hashable

structure Discharge.Context where
  discharger : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type)

abbrev DischargeM :=
  ReaderT Discharge.Context <| CacheAtomM (Std.HashMap (Nat × ProofKind) (Option Expr))

def DischargeM.disch {u : Level} (i : ℕ) (kind : ProofKind) (type : Q(Sort u)) :
    DischargeM Q($type) := do
  let ⟨discharger⟩ ← read
  let c ← CacheAtomM.get (σ := Std.HashMap (Nat × ProofKind) (Option Expr))
  match c.get? ⟨i, kind⟩  with
  | none =>
    try
      -- logInfo m!"Running discharger on goal {type}"
      let pf ← discharger type
      CacheAtomM.set (c.insert (i, kind) (some pf))
      return pf
    catch | _ => CacheAtomM.set (c.insert (i, kind) none); failure
  | some none => failure
  | some (some pf) => return pf

def DischargeM.run {α : Type} (m : DischargeM α)
  (disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type)) : AtomM α := (m ⟨disch⟩).run' ∅

end DischargeM

open DischargeM

/-! ### Lists of expressions representing exponents and atoms, and operations on such lists -/

/-- Basic meta-code "normal form" object of the `field_simp` tactic: a type synonym
for a list of ordered triples comprising an expression representing a term of a type `M` (where
typically `M` is a field), together with an integer "power" and a natural number "index".

The natural number represents the index of the `M` term in the `AtomM` monad: this is not enforced,
but is sometimes assumed in operations.  Thus when items `((a₁, x₁), k)` and `((a₂, x₂), k)`
appear in two different `FieldSimp.qNF` objects (i.e. with the same `ℕ`-index `k`), it is expected
that the expressions `x₁` and `x₂` are the same.  It is also expected that the items in a
`FieldSimp.qNF` list are in strictly decreasing order by natural-number index.

By forgetting the natural number indices, an expression representing a `Mathlib.Tactic.FieldSimp.NF`
object can be built from a `FieldSimp.qNF` object; this construction is provided as
`Mathlib.Tactic.FieldSimp.qNF.toNF`. -/
abbrev qNF (M : Q(Type v)) := List ((ℤ × Q($M)) × ℕ)

namespace qNF

/-- Given `l` of type `qNF M`, i.e. a list of `(ℤ × Q($M)) × ℕ`s (two `Expr`s and a natural
number), build an `Expr` representing an object of type `NF M` (i.e. `List (ℤ × M)`) in the
in the obvious way: by forgetting the natural numbers and gluing together the integers and `Expr`s.
-/
def toNF (l : qNF q($M)) : Q(NF $M) :=
  let l' : List Q(ℤ × $M) := (l.map Prod.fst).map (fun (a, x) ↦ q(($a, $x)))
  let qt : List Q(ℤ × $M) → Q(List (ℤ × $M)) := List.rec q([]) (fun e _ l ↦ q($e ::ᵣ $l))
  qt l'

/-- Given `l` of type `qNF M`, i.e. a list of `(ℤ × Q($M)) × ℕ`s (two `Expr`s and a natural
number), apply an expression representing a function with domain `ℤ` to each of the `ℤ`
components. -/
def onExponent (l : qNF M) (f : ℤ → ℤ) : qNF M :=
  l.map fun ((a, x), k) ↦ ((f a, x), k)

/-- Build a transparent expression for the product of powers represented by `l : qNF M`. -/
def evalPrettyMonomial (iM : Q(GroupWithZero $M)) (r : ℤ) (x : Q($M)) :
    MetaM (Σ e : Q($M), Q(zpow' $x $r = $e)) := do
  match r with
  | 0 => /- If an exponent is zero then we must not have been able to prove that x is nonzero.  -/
    return ⟨q($x / $x), q(zpow'_zero_eq_div ..)⟩
  | 1 => return ⟨x, q(zpow'_one $x)⟩
  | .ofNat r => do
    let pf ← mkDecideProofQ q($r ≠ 0)
    return ⟨q($x ^ $r), q(zpow'_ofNat $x $pf)⟩
  | r => do
    let pf ← mkDecideProofQ q($r ≠ 0)
    return ⟨q($x ^ $r), q(zpow'_of_ne_zero_right _ _ $pf)⟩

/-- Try to drop an expression `zpow' x r` from the beginning of a product. If `r ≠ 0` this of course
can't be done. If `r = 0`, then `zpow' x r` is equal to `x / x`, so it can be simplified to 1 (hence
dropped from the beginning of the product) if we can find a proof that `x ≠ 0`. -/
def tryClearZero
    (iM : Q(CommGroupWithZero $M))
    (r : ℤ) (x : Q($M)) (i : ℕ) (l : qNF M) :
    DischargeM <| Σ l' : qNF M, Q(NF.eval $(qNF.toNF (((r, x), i) :: l)) = NF.eval $(l'.toNF)) := do
  if r != 0 then
    return ⟨((r, x), i) :: l, q(rfl)⟩
  try
    let pf' : Q($x ≠ 0) ← disch i .nonzero q($x ≠ 0)
    have pf_r : Q($r = 0) := ← mkDecideProofQ q($r = 0)
    return ⟨l, (q(NF.eval_cons_of_pow_eq_zero $pf_r $pf' $(l.toNF)):)⟩
  catch _=>
    return ⟨((r, x), i) :: l, q(rfl)⟩

/-- Given `l : qNF M`, obtain `l' : qNF M` by removing all `l`'s exponent-zero entries where the
corresponding atom can be proved nonzero, and construct a proof that their associated expressions
are equal. -/
def removeZeros
    (iM : Q(CommGroupWithZero $M))
    (l : qNF M) :
    DischargeM <| Σ l' : qNF M, Q(NF.eval $(l.toNF) = NF.eval $(l'.toNF)) :=
  match l with
  | [] => return ⟨[], q(rfl)⟩
  | ((r, x), i) :: t => do
    let ⟨t', pf⟩ ← removeZeros iM t
    let ⟨l', pf'⟩ ← tryClearZero iM r x i t'
    let pf' : Q(NF.eval (($r, $x) ::ᵣ $(qNF.toNF t')) = NF.eval $(qNF.toNF l')) := pf'
    let pf'' : Q(NF.eval (($r, $x) ::ᵣ $(qNF.toNF t)) = NF.eval $(qNF.toNF l')) :=
      q(NF.eval_cons_eq_eval_of_eq_of_eq $r $x $pf $pf')
    return ⟨l', pf''⟩

/-- Given a product of powers, split as a quotient: the positive powers divided by (the negations
of) the negative powers. -/
def split (iM : Q(CommGroupWithZero $M)) (l : qNF M) :
    MetaM (Σ l_n l_d : qNF M, Q(NF.eval $(l.toNF)
      = NF.eval $(l_n.toNF) / NF.eval $(l_d.toNF))) := do
  match l with
  | [] => return ⟨[], [], q(Eq.symm (div_one (1:$M)))⟩
  | ((r, x), i) :: t =>
    let ⟨t_n, t_d, pf⟩ ← split iM t
    if r > 0 then
      return ⟨((r, x), i) :: t_n, t_d, (q(NF.cons_eq_div_of_eq_div $r $x $pf):)⟩
    else if r = 0 then
      return ⟨((1, x), i) :: t_n, ((1, x), i) :: t_d, (q(NF.cons_zero_eq_div_of_eq_div $x $pf):)⟩
    else
      let r' : ℤ := -r
      return ⟨t_n, ((r', x), i) :: t_d, (q(NF.cons_eq_div_of_eq_div' $r' $x $pf):)⟩

private def evalPrettyAux (iM : Q(CommGroupWithZero $M)) (l : qNF M) :
    MetaM (Σ e : Q($M), Q(NF.eval $(l.toNF) = $e)) := do
  match l with
  | [] => return ⟨q(1), q(rfl)⟩
  | [((r, x), _)] =>
    let ⟨e, pf⟩ ← evalPrettyMonomial q(inferInstance) r x
    return ⟨e, q(by rw [NF.eval_cons]; exact Eq.trans (one_mul _) $pf)⟩
  | ((r, x), k) :: t =>
    let ⟨e, pf_e⟩ ← evalPrettyMonomial q(inferInstance) r x
    let ⟨t', pf⟩ ← evalPrettyAux iM t
    have pf'' : Q(NF.eval $(qNF.toNF (((r, x), k) :: t)) = (NF.eval $(qNF.toNF t)) * zpow' $x $r) :=
      (q(NF.eval_cons ($r, $x) $(qNF.toNF t)):)
    return ⟨q($t' * $e), q(Eq.trans $pf'' (congr_arg₂ HMul.hMul $pf $pf_e))⟩

/-- Build a transparent expression for the product of powers represented by `l : qNF M`. -/
def evalPretty (iM : Q(CommGroupWithZero $M)) (l : qNF M) :
    MetaM (Σ e : Q($M), Q(NF.eval $(l.toNF) = $e)) := do
  let ⟨l_n, l_d, pf⟩ ← split iM l
  let ⟨num, pf_n⟩ ← evalPrettyAux q(inferInstance) l_n
  let ⟨den, pf_d⟩ ← evalPrettyAux q(inferInstance) l_d
  match l_d with
  | [] => return ⟨num, q(eq_div_of_eq_one_of_subst $pf $pf_n)⟩
  | _ =>
    let pf_n : Q(NF.eval $(l_n.toNF) = $num) := pf_n
    let pf_d : Q(NF.eval $(l_d.toNF) = $den) := pf_d
    let pf : Q(NF.eval $(l.toNF) = NF.eval $(l_n.toNF) / NF.eval $(l_d.toNF)) := pf
    let pf_tot := q(eq_div_of_subst $pf $pf_n $pf_d)
    return ⟨q($num / $den), pf_tot⟩

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(ℤ × Q($M)) × ℕ`s (an integer, an
`Expr` and a natural number), construct another such term `l`, which will have the property that in
the field `$M`, the product of the "multiplicative linear combinations" represented by `l₁` and
`l₂` is the multiplicative linear combination represented by `l`.

The construction assumes, to be valid, that the lists `l₁` and `l₂` are in strictly decreasing order
by `ℕ`-component, and that if pairs `(a₁, x₁)` and `(a₂, x₂)` appear in `l₁`, `l₂` respectively with
the same `ℕ`-component `k`, then the expressions `x₁` and `x₂` are equal.

The construction is as follows: merge the two lists, except that if pairs `(a₁, x₁)` and `(a₂, x₂)`
appear in `l₁`, `l₂` respectively with the same `ℕ`-component `k`, then contribute a term
`(a₁ + a₂, x₁)` to the output list with `ℕ`-component `k`. -/
def mul : qNF q($M) → qNF q($M) → qNF q($M)
  | [], l => l
  | l, [] => l
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      ((a₁, x₁), k₁) :: mul t₁ (((a₂, x₂), k₂) :: t₂)
    else if k₁ = k₂ then
      /- If we can prove that the atom is nonzero then we could remove it from this list,
      but this will be done at a later stage. -/
      ((a₁ + a₂, x₁), k₁) :: mul t₁ t₂
    else
      ((a₂, x₂), k₂) :: mul (((a₁, x₁), k₁) :: t₁) t₂

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(ℤ × Q($M)) × ℕ`s (an integer, an
`Expr` and a natural number), recursively construct a proof that in the field `$M`, the product of
the "multiplicative linear combinations" represented by `l₁` and `l₂` is the multiplicative linear
combination represented by `FieldSimp.qNF.mul l₁ l₁`. -/
def mkMulProof (iM : Q(CommGroupWithZero $M)) (l₁ l₂ : qNF M) :
    Q((NF.eval $(l₁.toNF)) * NF.eval $(l₂.toNF) = NF.eval $((qNF.mul l₁ l₂).toNF)) :=
  match l₁, l₂ with
  | [], l => (q(one_mul (NF.eval $(l.toNF))):)
  | l, [] => (q(mul_one (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      let pf := mkMulProof iM t₁ (((a₂, x₂), k₂) :: t₂)
      (q(NF.mul_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkMulProof iM t₁ t₂
      (q(NF.mul_eq_eval₂ $a₁ $a₂ $x₁ $pf):)
    else
      let pf := mkMulProof iM (((a₁, x₁), k₁) :: t₁) t₂
      (q(NF.mul_eq_eval₃ ($a₂, $x₂) $pf):)

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(ℤ × Q($M)) × ℕ`s (an integer, an
`Expr` and a natural number), construct another such term `l`, which will have the property that in
the field `$M`, the quotient of the "multiplicative linear combinations" represented by `l₁` and
`l₂` is the multiplicative linear combination represented by `l`.

The construction assumes, to be valid, that the lists `l₁` and `l₂` are in strictly decreasing order
by `ℕ`-component, and that if pairs `(a₁, x₁)` and `(a₂, x₂)` appear in `l₁`, `l₂` respectively with
the same `ℕ`-component `k`, then the expressions `x₁` and `x₂` are equal.

The construction is as follows: merge the first list and the negation of the second list, except
that if pairs `(a₁, x₁)` and `(a₂, x₂)` appear in `l₁`, `l₂` respectively with the same
`ℕ`-component `k`, then contribute a term `(a₁ - a₂, x₁)` to the output list with `ℕ`-component `k`.
-/
def div : qNF M → qNF M → qNF M
  | [], l => l.onExponent Neg.neg
  | l, [] => l
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      ((a₁, x₁), k₁) :: div t₁ (((a₂, x₂), k₂) :: t₂)
    else if k₁ = k₂ then
      ((a₁ - a₂, x₁), k₁) :: div t₁ t₂
    else
      ((-a₂, x₂), k₂) :: div (((a₁, x₁), k₁) :: t₁) t₂

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(ℤ × Q($M)) × ℕ`s (an integer, an
`Expr` and a natural number), recursively construct a proof that in the field `$M`, the quotient
of the "multiplicative linear combinations" represented by `l₁` and `l₂` is the multiplicative
linear combination represented by `FieldSimp.qNF.div l₁ l₁`. -/
def mkDivProof (iM : Q(CommGroupWithZero $M)) (l₁ l₂ : qNF M) :
    Q(NF.eval $(l₁.toNF) / NF.eval $(l₂.toNF) = NF.eval $((qNF.div l₁ l₂).toNF)) :=
  match l₁, l₂ with
  | [], l => (q(NF.one_div_eq_eval $(l.toNF)):)
  | l, [] => (q(div_one (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      let pf := mkDivProof iM t₁ (((a₂, x₂), k₂) :: t₂)
      (q(NF.div_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkDivProof iM t₁ t₂
      (q(NF.div_eq_eval₂ $a₁ $a₂ $x₁ $pf):)
    else
      let pf := mkDivProof iM (((a₁, x₁), k₁) :: t₁) t₂
      (q(NF.div_eq_eval₃ ($a₂, $x₂) $pf):)

end qNF

/-- Constraints on denominators which may need to be considered in `field_simp`: no condition,
nonzeroness, or strict positivity. -/
inductive DenomCondition (iM : Q(GroupWithZero $M))
  | none
  | nonzero
  | positive (iM' : Q(PartialOrder $M)) (iM'' : Q(PosMulStrictMono $M))
      (iM''' : Q(PosMulReflectLT $M)) (iM'''' : Q(ZeroLEOneClass $M))

namespace DenomCondition

/-- Given a field-simp-normal-form expression `L` (a product of powers of atoms), a proof (according
to the value of `DenomCondition`) of that expression's nonzeroness, strict positivity, etc. -/
def proof {iM : Q(GroupWithZero $M)} (L : qNF M) : DenomCondition iM → Type
  | .none => Unit
  | .nonzero => Q(NF.eval $(qNF.toNF L) ≠ 0)
  | .positive _ _ _ _ => Q(0 < NF.eval $(qNF.toNF L))

/-- The empty field-simp-normal-form expression `[]` (representing `1` as an empty product of powers
of atoms) can be proved to be nonzero, strict positivity, etc., as needed, as specified by the
value of `DenomCondition`. -/
def proofZero {iM : Q(CommGroupWithZero $M)} :
    ∀ cond : DenomCondition (M := M) q(inferInstance), cond.proof []
  | .none => Unit.unit
  | .nonzero => q(one_ne_zero (α := $M))
  | .positive _ _ _ _ => q(zero_lt_one (α := $M))

end DenomCondition

/-- Given a proof of the nonzeroness, strict positivity, etc. (as specified by the value of
`DenomCondition`) of a field-simp-normal-form expression `L` (a product of powers of atoms),
construct a corresponding proof for `((r, e), i) :: L`.

In this version we also expose the proof of nonzeroness of `e`. -/
def mkDenomConditionProofSucc {iM : Q(CommGroupWithZero $M)}
    {cond : DenomCondition (M := M) q(inferInstance)}
    {L : qNF M} (hL : cond.proof L) (e : Q($M)) (r : ℤ) (i : ℕ) :
    DischargeM (Q($e ≠ 0) × cond.proof (((r, e), i) :: L)) := do
  match cond with
  | .none => return (← disch i .nonzero q($e ≠ 0), Unit.unit)
  | .nonzero =>
    let pf ← disch i .nonzero q($e ≠ 0)
    let pf₀ : Q(NF.eval $(qNF.toNF L) ≠ 0) := hL
    return (pf, q(NF.cons_ne_zero $r $pf $pf₀))
  | .positive _ _ _ _ =>
    let pf ← disch i .positive q(0 < $e)
    let pf₀ : Q(0 < NF.eval $(qNF.toNF L)) := hL
    let pf' := q(NF.cons_pos $r (x := $e) $pf $pf₀)
    return (q(LT.lt.ne' $pf), pf')

/-- Given a proof of the nonzeroness, strict positivity, etc. (as specified by the value of
`DenomCondition`) of a field-simp-normal-form expression `L` (a product of powers of atoms),
construct a corresponding proof for `((r, e), i) :: L`. -/
def mkDenomConditionProofSucc' {iM : Q(CommGroupWithZero $M)}
    {cond : DenomCondition (M := M) q(inferInstance)}
    {L : qNF M} (hL : cond.proof L) (e : Q($M)) (r : ℤ) (i : ℕ) :
    DischargeM (cond.proof (((r, e), i) :: L)) := do
  match cond with
  | .none => return Unit.unit
  | .nonzero =>
    let pf ← disch i .nonzero q($e ≠ 0)
    let pf₀ : Q(NF.eval $(qNF.toNF L) ≠ 0) := hL
    return q(NF.cons_ne_zero $r $pf $pf₀)
  | .positive _ _ _ _ =>
    let pf ← disch i .positive q(0 < $e)
    let pf₀ : Q(0 < NF.eval $(qNF.toNF L)) := hL
    return q(NF.cons_pos $r (x := $e) $pf $pf₀)

namespace qNF

/-- Extract a common factor `L` of two products-of-powers `l₁` and `l₂` in `M`, in the sense that
both `l₁` and `l₂` are quotients by `L` of products of *positive* powers.

The variable `cond` specifies whether we extract a *certified nonzero[/positive]* (and therefore
potentially smaller) common factor. If so, the metaprogram returns a "proof" that this common factor
is nonzero/positive, i.e. an expression `Q(NF.eval $(L.toNF) ≠ 0)` / `Q(0 < NF.eval $(L.toNF))`. -/
partial def gcd (iM : Q(CommGroupWithZero $M)) (l₁ l₂ : qNF M)
    (cond : DenomCondition (M := M) q(inferInstance)) :
  DischargeM <| Σ (L l₁' l₂' : qNF M),
    Q((NF.eval $(L.toNF)) * NF.eval $(l₁'.toNF) = NF.eval $(l₁.toNF)) ×
    Q((NF.eval $(L.toNF)) * NF.eval $(l₂'.toNF) = NF.eval $(l₂.toNF)) ×
    cond.proof L :=

  /- Handle the case where atom `i` is present in the first list but not the second. -/
  let absent (l₁ l₂ : qNF M) (n : ℤ) (e : Q($M)) (i : ℕ) :
      DischargeM <| Σ (L l₁' l₂' : qNF M),
        Q((NF.eval $(L.toNF)) * NF.eval $(l₁'.toNF) = NF.eval $(qNF.toNF (((n, e), i) :: l₁))) ×
        Q((NF.eval $(L.toNF)) * NF.eval $(l₂'.toNF) = NF.eval $(l₂.toNF)) ×
        cond.proof L := do
    let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← gcd iM l₁ l₂ cond
    if 0 < n then
      -- Don't pull anything out
      return ⟨L, ((n, e), i) :: l₁', l₂', (q(NF.eval_mul_eval_cons $n $e $pf₁):), q($pf₂), pf₀⟩
    else if n = 0 then
      -- Don't pull anything out, but eliminate the term if it is a cancellable zero
      let ⟨l₁'', pf''⟩ ← tryClearZero iM 0 e i l₁'
      let pf'' : Q(NF.eval ((0, $e) ::ᵣ $(l₁'.toNF)) = NF.eval $(l₁''.toNF)) := pf''
      return ⟨L, l₁'', l₂', (q(NF.eval_mul_eval_cons_zero $pf₁ $pf''):), q($pf₂), pf₀⟩
    try
      let (pf, b) ← mkDenomConditionProofSucc pf₀ e n i
      -- if nonzeroness proof succeeds
      return ⟨((n, e), i) :: L, l₁', ((-n, e), i) :: l₂', (q(NF.eval_cons_mul_eval $n $e $pf₁):),
        (q(NF.eval_cons_mul_eval_cons_neg $n $pf $pf₂):), b⟩
    catch _ =>
      -- if we can't prove nonzeroness, don't pull out e.
      return ⟨L, ((n, e), i) :: l₁', l₂', (q(NF.eval_mul_eval_cons $n $e $pf₁):), q($pf₂), pf₀⟩

  /- Handle the case where atom `i` is present in both lists. -/
  let bothPresent (t₁ t₂ : qNF M) (n₁ n₂ : ℤ) (e : Q($M)) (i : ℕ) :
      DischargeM <| Σ (L l₁' l₂' : qNF M),
        Q((NF.eval $(L.toNF)) * NF.eval $(l₁'.toNF) = NF.eval $(qNF.toNF (((n₁, e), i) :: t₁))) ×
        Q((NF.eval $(L.toNF)) * NF.eval $(l₂'.toNF) = NF.eval $(qNF.toNF (((n₂, e), i) :: t₂))) ×
        cond.proof L := do
    let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← gcd iM t₁ t₂ cond
    if n₁ < n₂ then
      let N : ℤ := n₂ - n₁
      return ⟨((n₁, e), i) :: L, l₁', ((n₂ - n₁, e), i) :: l₂',
        (q(NF.eval_cons_mul_eval $n₁ $e $pf₁):), (q(NF.mul_eq_eval₂ $n₁ $N $e $pf₂):),
        ← mkDenomConditionProofSucc' pf₀ e n₁ i⟩
    else if n₁ = n₂ then
      return ⟨((n₁, e), i) :: L, l₁', l₂', (q(NF.eval_cons_mul_eval $n₁ $e $pf₁):),
        (q(NF.eval_cons_mul_eval $n₂ $e $pf₂):), ← mkDenomConditionProofSucc' pf₀ e n₁ i⟩
    else
      let N : ℤ := n₁ - n₂
      return ⟨((n₂, e), i) :: L, ((n₁ - n₂, e), i) :: l₁', l₂',
        (q(NF.mul_eq_eval₂ $n₂ $N $e $pf₁):), (q(NF.eval_cons_mul_eval $n₂ $e $pf₂):),
        ← mkDenomConditionProofSucc' pf₀ e n₂ i⟩

  match l₁, l₂ with
  | [], [] => pure ⟨[], [], [],
    (q(one_mul (NF.eval $(qNF.toNF (M := M) []))):),
    (q(one_mul (NF.eval $(qNF.toNF (M := M) []))):), cond.proofZero⟩
  | ((n, e), i) :: t, [] => do
    let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← absent t [] n e i
    return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩
  | [], ((n, e), i) :: t => do
    let ⟨L, l₂', l₁', pf₂, pf₁, pf₀⟩ ← absent t [] n e i
    return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩
  | ((n₁, e₁), i₁) :: t₁, ((n₂, e₂), i₂) :: t₂ => do
    if i₁ > i₂ then
      let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← absent t₁ (((n₂, e₂), i₂) :: t₂) n₁ e₁ i₁
      return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩
    else if i₁ == i₂ then
      try
        bothPresent t₁ t₂ n₁ n₂ e₁ i₁
      catch _ =>
        -- if `bothPresent` fails, don't pull out `e`
        -- the failure case of `bothPresent` should be:
        -- * `.none` case: never
        -- * `.nonzero` case: if `e` can't be proved nonzero
        -- * `.positive _` case: if `e` can't be proved positive
        let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← gcd iM t₁ t₂ cond
        return ⟨L, ((n₁, e₁), i₁) :: l₁', ((n₂, e₂), i₂) :: l₂',
          (q(NF.eval_mul_eval_cons $n₁ $e₁ $pf₁):), (q(NF.eval_mul_eval_cons $n₂ $e₂ $pf₂):), pf₀⟩
    else
      let ⟨L, l₂', l₁', pf₂, pf₁, pf₀⟩ ← absent t₂ (((n₁, e₁), i₁) :: t₁) n₂ e₂ i₂
      return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩

end qNF

/-! ### Core of the `field_simp` tactic -/

/-- The main algorithm behind the `field_simp` tactic: partially-normalizing an
expression in a field `M` into the form x1 ^ c1 * x2 ^ c2 * ... x_k ^ c_k,
where x1, x2, ... are distinct atoms in `M`, and c1, c2, ... are integers. -/
partial def normalize
    (iM : Q(CommGroupWithZero $M)) (x : Q($M)) :
    DischargeM (Σ y : Q($M), (Σ g : Sign M, Q($x = $(g.expr y))) ×
      Σ l : qNF M, Q($y = NF.eval $(l.toNF))) := do
  let baseCase (y : Q($M)) (normalize? : Bool) :
      AtomM (Σ (l : qNF M), Q($y = NF.eval $(l.toNF))) := do
    if normalize? then
      let r ← (← read).evalAtom y
      have y' : Q($M) := r.expr
      have pf : Q($y = $y') := ← r.getProof
      let (k, ⟨x', _⟩) ← AtomM.addAtomQ y'
      pure ⟨[((1, x'), k)], q(Eq.trans $pf (NF.atom_eq_eval $x'))⟩
    else
      let (k, ⟨x', _⟩) ← AtomM.addAtomQ y
      pure ⟨[((1, x'), k)], q(NF.atom_eq_eval $x')⟩
  match x with
  /- normalize a multiplication: `x₁ * x₂` -/
  | ~q($x₁ * $x₂) =>
    let ⟨y₁, ⟨g₁, pf₁_sgn⟩, l₁, pf₁⟩ ← normalize iM x₁
    let ⟨y₂, ⟨g₂, pf₂_sgn⟩, l₂, pf₂⟩ ← normalize iM x₂
    -- build the new list and proof
    have pf := qNF.mkMulProof iM l₁ l₂
    let ⟨G, pf_y⟩ := ← Sign.mul iM y₁ y₂ g₁ g₂
    pure ⟨q($y₁ * $y₂), ⟨G, q(Eq.trans (congr_arg₂ HMul.hMul $pf₁_sgn $pf₂_sgn) $pf_y)⟩,
      qNF.mul l₁ l₂, q(NF.mul_eq_eval $pf₁ $pf₂ $pf)⟩
  /- normalize a division: `x₁ / x₂` -/
  | ~q($x₁ / $x₂) =>
    let ⟨y₁, ⟨g₁, pf₁_sgn⟩, l₁, pf₁⟩ ← normalize iM x₁
    let ⟨y₂, ⟨g₂, pf₂_sgn⟩, l₂, pf₂⟩ ← normalize iM x₂
    -- build the new list and proof
    let pf := qNF.mkDivProof iM l₁ l₂
    let ⟨G, pf_y⟩ := ← Sign.div iM y₁ y₂ g₁ g₂
    pure ⟨q($y₁ / $y₂), ⟨G, q(Eq.trans (congr_arg₂ HDiv.hDiv $pf₁_sgn $pf₂_sgn) $pf_y)⟩,
      qNF.div l₁ l₂, q(NF.div_eq_eval $pf₁ $pf₂ $pf)⟩
  /- normalize a inversion: `y⁻¹` -/
  | ~q($y⁻¹) =>
    let ⟨y', ⟨g, pf_sgn⟩, l, pf⟩ ← normalize iM y
    let pf_y ← Sign.inv iM y' g
    -- build the new list and proof, casing according to the sign of `x`
    pure ⟨q($y'⁻¹), ⟨g, q(Eq.trans (congr_arg Inv.inv $pf_sgn) $pf_y)⟩,
      l.onExponent Neg.neg, (q(NF.inv_eq_eval $pf):)⟩
  /- normalize an integer exponentiation: `y ^ (s : ℤ)` -/
  | ~q($y ^ ($s : ℤ)) =>
    let some s := Expr.int? s | pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
    if s = 0 then
      pure ⟨q(1), ⟨Sign.plus, (q(zpow_zero $y):)⟩, [], q(NF.one_eq_eval $M)⟩
    else
      let ⟨y', ⟨g, pf_sgn⟩, l, pf⟩ ← normalize iM y
      let pf_s ← mkDecideProofQ q($s ≠ 0)
      let ⟨G, pf_y⟩ ← Sign.zpow iM y' g s
      let pf_y' := q(Eq.trans (congr_arg (· ^ $s) $pf_sgn) $pf_y)
      pure ⟨q($y' ^ $s), ⟨G, pf_y'⟩, l.onExponent (HMul.hMul s), (q(NF.zpow_eq_eval $pf_s $pf):)⟩
  /- normalize a natural number exponentiation: `y ^ (s : ℕ)` -/
  | ~q($y ^ ($s : ℕ)) =>
    let some s := Expr.nat? s | pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
    if s = 0 then
      pure ⟨q(1), ⟨Sign.plus, (q(pow_zero $y):)⟩, [], q(NF.one_eq_eval $M)⟩
    else
      let ⟨y', ⟨g, pf_sgn⟩, l, pf⟩ ← normalize iM y
      let pf_s ← mkDecideProofQ q($s ≠ 0)
      let ⟨G, pf_y⟩ ← Sign.pow iM y' g s
      let pf_y' := q(Eq.trans (congr_arg (· ^ $s) $pf_sgn) $pf_y)
      pure ⟨q($y' ^ $s), ⟨G, pf_y'⟩, l.onExponent (HSMul.hSMul s), (q(NF.pow_eq_eval $pf_s $pf):)⟩
  /- normalize a `(1:M)` -/
  | ~q(1) => pure ⟨q(1), ⟨Sign.plus,  q(rfl)⟩, [], q(NF.one_eq_eval $M)⟩
  /- normalize an addition: `a + b` -/
  | ~q(HAdd.hAdd (self := @instHAdd _ $i) $a $b) =>
    try
      let _i ← synthInstanceQ q(Semifield $M)
      assumeInstancesCommute
      let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf₁⟩ ← normalize iM a
      let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf₂⟩ ← normalize iM b
      let ⟨L, l₁', l₂', pf₁', pf₂', _⟩ ← l₁.gcd iM l₂ .none
      let ⟨e₁, pf₁''⟩ ← qNF.evalPretty iM l₁'
      let ⟨e₂, pf₂''⟩ ← qNF.evalPretty iM l₂'
      have pf_a := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf₁ (Eq.symm $pf₁')) pf₁''
      have pf_b := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf₂ (Eq.symm $pf₂')) pf₂''
      let e : Q($M) := q($(g₁.expr e₁) + $(g₂.expr e₂))
      let ⟨sum, pf_atom⟩ ← baseCase e false
      let L' := qNF.mul L sum
      let pf_mul : Q((NF.eval $(L.toNF)) * NF.eval $(sum.toNF) = NF.eval $(L'.toNF)) :=
        qNF.mkMulProof iM L sum
      pure ⟨x, ⟨Sign.plus, q(rfl)⟩, L', q(subst_add $pf_a $pf_b $pf_atom $pf_mul)⟩
    catch _ => pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
  /- normalize a subtraction: `a - b` -/
  | ~q(HSub.hSub (self := @instHSub _ $i) $a $b) =>
    try
      let _i ← synthInstanceQ q(Field $M)
      assumeInstancesCommute
      let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf₁⟩ ← normalize iM a
      let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf₂⟩ ← normalize iM b
      let ⟨L, l₁', l₂', pf₁', pf₂', _⟩ ← l₁.gcd iM l₂ .none
      let ⟨e₁, pf₁''⟩ ← qNF.evalPretty iM l₁'
      let ⟨e₂, pf₂''⟩ ← qNF.evalPretty iM l₂'
      have pf_a := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf₁ (Eq.symm $pf₁')) pf₁''
      have pf_b := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf₂ (Eq.symm $pf₂')) pf₂''
      let e : Q($M) := q($(g₁.expr e₁) - $(g₂.expr e₂))
      let ⟨sum, pf_atom⟩ ← baseCase e false
      let L' := qNF.mul L sum
      let pf_mul : Q((NF.eval $(L.toNF)) * NF.eval $(sum.toNF) = NF.eval $(L'.toNF)) :=
        qNF.mkMulProof iM L sum
      pure ⟨x, ⟨Sign.plus, q(rfl)⟩, L', q(subst_sub $pf_a $pf_b $pf_atom $pf_mul)⟩
    catch _ => pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
  /- normalize a negation: `-a` -/
  | ~q(Neg.neg (self := $i) $a) =>
    try
      let iM' ← synthInstanceQ q(Field $M)
      assumeInstancesCommute
      let ⟨y, ⟨g, pf_sgn⟩, l, pf⟩ ← normalize iM a
      let ⟨G, pf_y⟩ ← Sign.neg iM' y g
      pure ⟨y, ⟨G, q(Eq.trans (congr_arg Neg.neg $pf_sgn) $pf_y)⟩, l, pf⟩
    catch _ => pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
  -- TODO special-case handling of zero? maybe not necessary
  /- anything else should be treated as an atom -/
  | _ => pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩

/-- Given `x` in a commutative group-with-zero, construct a new expression in the standard form
*** / *** (all denominators at the end) which is equal to `x`. -/
def reduceExprQ (iM : Q(CommGroupWithZero $M)) (x : Q($M)) :
    DischargeM (Σ x' : Q($M), Q($x = $x')) := do
  let ⟨y, ⟨g, pf_sgn⟩, l, pf⟩ ← normalize iM x
  let ⟨l', pf'⟩ ← qNF.removeZeros iM l
  let ⟨x', pf''⟩ ← qNF.evalPretty iM l'
  let pf_yx : Q($y = $x') := q(Eq.trans (Eq.trans $pf $pf') $pf'')
  return ⟨g.expr x', q(Eq.trans $pf_sgn $(g.congr pf_yx))⟩

/-- Given `e₁` and `e₂`, cancel nonzero factors to construct a new equality which is logically
equivalent to `e₁ = e₂`. -/
def reduceEqQ (iM : Q(CommGroupWithZero $M)) (e₁ e₂ : Q($M)) :
    DischargeM (Σ f₁ f₂ : Q($M), Q(($e₁ = $e₂) = ($f₁ = $f₂))) := do
  let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf_l₁⟩ ← normalize iM e₁
  let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf_l₂⟩ ← normalize iM e₂
  let ⟨L, l₁', l₂', pf_lhs, pf_rhs, pf₀⟩ ← l₁.gcd iM l₂ .nonzero
  let pf₀ : Q(NF.eval $(qNF.toNF L) ≠ 0) := pf₀
  let ⟨f₁', pf_l₁'⟩ ← l₁'.evalPretty iM
  let ⟨f₂', pf_l₂'⟩ ← l₂'.evalPretty iM
  have pf_ef₁ := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf_l₁ (Eq.symm $pf_lhs)) pf_l₁'
  have pf_ef₂ := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf_l₂ (Eq.symm $pf_rhs)) pf_l₂'
  return ⟨g₁.expr f₁', g₂.expr f₂', q(eq_eq_cancel_eq $pf_ef₁ $pf_ef₂ $pf₀)⟩

/-- Given `e₁` and `e₂`, cancel positive factors to construct a new inequality which is logically
equivalent to `e₁ ≤ e₂`. -/
def reduceLeQ (iM : Q(CommGroupWithZero $M)) (iM' : Q(PartialOrder $M))
    (iM'' : Q(PosMulStrictMono $M)) (iM''' : Q(PosMulReflectLE $M)) (iM'''' : Q(ZeroLEOneClass $M))
    (e₁ e₂ : Q($M)) :
    DischargeM (Σ f₁ f₂ : Q($M), Q(($e₁ ≤ $e₂) = ($f₁ ≤ $f₂))) := do
  let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf_l₁⟩ ← normalize iM e₁
  let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf_l₂⟩ ← normalize iM e₂
  let ⟨L, l₁', l₂', pf_lhs, pf_rhs, pf₀⟩
    ← l₁.gcd iM l₂ (.positive iM' iM'' q(inferInstance) iM'''')
  let pf₀ : Q(0 <  NF.eval $(qNF.toNF L)) := pf₀
  let ⟨f₁', pf_l₁'⟩ ← l₁'.evalPretty iM
  let ⟨f₂', pf_l₂'⟩ ← l₂'.evalPretty iM
  have pf_ef₁ := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf_l₁ (Eq.symm $pf_lhs)) pf_l₁'
  have pf_ef₂ := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf_l₂ (Eq.symm $pf_rhs)) pf_l₂'
  return ⟨g₁.expr f₁', g₂.expr f₂', q(le_eq_cancel_le $pf_ef₁ $pf_ef₂ $pf₀)⟩

/-- Given `e₁` and `e₂`, cancel positive factors to construct a new inequality which is logically
equivalent to `e₁ < e₂`. -/
def reduceLtQ (iM : Q(CommGroupWithZero $M)) (iM' : Q(PartialOrder $M))
    (iM'' : Q(PosMulStrictMono $M)) (iM''' : Q(PosMulReflectLT $M)) (iM'''' : Q(ZeroLEOneClass $M))
    (e₁ e₂ : Q($M)) :
    DischargeM (Σ f₁ f₂ : Q($M), Q(($e₁ < $e₂) = ($f₁ < $f₂))) := do
  let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf_l₁⟩ ← normalize iM e₁
  let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf_l₂⟩ ← normalize iM e₂
  let ⟨L, l₁', l₂', pf_lhs, pf_rhs, pf₀⟩
    ← l₁.gcd iM l₂ (.positive iM' iM'' iM''' iM'''')
  let pf₀ : Q(0 <  NF.eval $(qNF.toNF L)) := pf₀
  let ⟨f₁', pf_l₁'⟩ ← l₁'.evalPretty iM
  let ⟨f₂', pf_l₂'⟩ ← l₂'.evalPretty iM
  have pf_ef₁ := ← Sign.mkEqMul iM pf_sgn₁ q(Eq.trans $pf_l₁ (Eq.symm $pf_lhs)) pf_l₁'
  have pf_ef₂ := ← Sign.mkEqMul iM pf_sgn₂ q(Eq.trans $pf_l₂ (Eq.symm $pf_rhs)) pf_l₂'
  return ⟨g₁.expr f₁', g₂.expr f₂', q(lt_eq_cancel_lt $pf_ef₁ $pf_ef₂ $pf₀)⟩

/-- Given `x` in a commutative group-with-zero, construct a new expression in the standard form
*** / *** (all denominators at the end) which is equal to `x`. -/
def reduceExpr (x : Expr) :
    DischargeM Simp.Result := do
  -- for `field_simp` to work with the recursive infrastructure in `AtomM.recurse`, we need to fail
  -- on things `field_simp` would treat as atoms
  guard x.isApp
  let ⟨f, _⟩ := x.getAppFnArgs
  guard <|
    f ∈ [``HMul.hMul, ``HDiv.hDiv, ``Inv.inv, ``HPow.hPow, ``HAdd.hAdd, ``HSub.hSub, ``Neg.neg]
  -- infer `u` and `K : Q(Type u)` such that `x : Q($K)`
  let ⟨u, K, _⟩ ← inferTypeQ' x
  -- find a `CommGroupWithZero` instance on `K`
  let iK : Q(CommGroupWithZero $K) ← synthInstanceQ q(CommGroupWithZero $K)
  -- run the core normalization function `normalizePretty` on `x`
  trace[Tactic.field_simp] "putting {x} in \"field_simp\"-normal-form"
  let ⟨e, pf⟩ ← reduceExprQ iK x
  return { expr := e, proof? := some pf }

/-- Given an (in)equality `a = b` (respectively, `a ≤ b`, `a < b`), cancel nonzero (resp. positive)
factors to construct a new (in)equality which is logically equivalent to `a = b` (respectively,
`a ≤ b`, `a < b`). -/
def reduceProp (t : Expr) :
    DischargeM Simp.Result := do
  let ⟨i, _, a, b⟩ ← t.ineq?
  -- infer `u` and `K : Q(Type u)` such that `x : Q($K)`
  let ⟨u, K, a⟩ ← inferTypeQ' a
  -- find a `CommGroupWithZero` instance on `K`
  let iK : Q(CommGroupWithZero $K) ← synthInstanceQ q(CommGroupWithZero $K)
  trace[Tactic.field_simp] "clearing denominators in {a} ~ {b}"
  -- run the core (in)equality-transforming mechanism on `a =/≤/< b`
  match i with
  | .eq =>
    let ⟨a', b', pf⟩ ← reduceEqQ iK a b
    let t' ← mkAppM `Eq #[a', b']
    return { expr := t', proof? := pf }
  | .le =>
    let iK' : Q(PartialOrder $K) ← synthInstanceQ q(PartialOrder $K)
    let iK'' : Q(PosMulStrictMono $K) ← synthInstanceQ q(PosMulStrictMono $K)
    let iK''' : Q(PosMulReflectLE $K) ← synthInstanceQ q(PosMulReflectLE $K)
    let iK'''' : Q(ZeroLEOneClass $K) ← synthInstanceQ q(ZeroLEOneClass $K)
    let ⟨a', b', pf⟩ ← reduceLeQ iK iK' iK'' iK''' iK'''' a b
    let t' ← mkAppM `LE.le #[a', b']
    return { expr := t', proof? := pf }
  | _ =>
    let iK' : Q(PartialOrder $K) ← synthInstanceQ q(PartialOrder $K)
    let iK'' : Q(PosMulStrictMono $K) ← synthInstanceQ q(PosMulStrictMono $K)
    let iK''' : Q(PosMulReflectLT $K) ← synthInstanceQ q(PosMulReflectLT $K)
    let iK'''' : Q(ZeroLEOneClass $K) ← synthInstanceQ q(ZeroLEOneClass $K)
    let ⟨a', b', pf⟩ ← reduceLtQ iK iK' iK'' iK''' iK'''' a b
    let t' ← mkAppM `LT.lt #[a', b']
    return { expr := t', proof? := pf }

/-! ### Frontend -/

open Elab Tactic Lean.Parser.Tactic

/-- If the user provided a discharger, elaborate it. If not, we will use the `field_simp` default
discharger, which (among other things) includes a simp-run for the specified argument list, so we
elaborate those arguments. -/
def parseDischarger (d : Option (TSyntax ``discharger)) (args : Option (TSyntax ``simpArgs)) :
    TacticM (∀ {u : Level} (type : Q(Sort u)), MetaM Q($type)) := do
  match d with
  | none =>
    let ctx ← Simp.Context.ofArgs (args.getD ⟨.missing⟩) { contextual := true }
    return fun e ↦ Prod.fst <$> (FieldSimp.discharge e).run ctx >>= Option.getM
  | some d =>
    if args.isSome then
      logWarningAt args.get!
        "Custom `field_simp` dischargers do not make use of the `field_simp` arguments list"
    match d with
    | `(discharger| (discharger := $tac)) =>
      let tac := (evalTactic (← `(tactic| ($tac))) *> pruneSolvedGoals)
      return (synthesizeUsing' · tac)
    | _ => throwError "could not parse the provided discharger {d}"

/--
The goal of `field_simp` is to bring expressions in (semi-)fields over a common denominator, i.e. to
reduce them to expressions of the form `n / d` where neither `n` nor `d` contains any division
symbol. For example, `x / (1 - y) / (1 + y / (1 - y))` is reduced to `x / (1 - y + y)`:
```
example (x y z : ℚ) (hy : 1 - y ≠ 0) :
    ⌊x / (1 - y) / (1 + y / (1 - y))⌋ < 3 := by
  field_simp
  -- new goal: `⊢ ⌊x / (1 - y + y)⌋ < 3`
```

The `field_simp` tactic will also clear denominators in field *(in)equalities*, by
cross-multiplying. For example, `field_simp` will clear the `x` denominators in the following
equation:
```
example {K : Type*} [Field K] {x : K} (hx0 : x ≠ 0) :
    (x + 1 / x) ^ 2 + (x + 1 / x) = 1 := by
  field_simp
  -- new goal: `⊢ (x ^ 2 + 1) * (x ^ 2 + 1 + x) = x ^ 2`
```

A very common pattern is `field_simp; ring` (clear denominators, then the resulting goal is
solvable by the axioms of a commutative ring). The finishing tactic `field` is a shorthand for this
pattern.

Cancelling and combining denominators will generally require checking "nonzeroness"/"positivity"
side conditions. The `field_simp` tactic attempts to discharge these, and will omit such steps if it
cannot discharge the corresponding side conditions. The discharger will try, among other things,
`positivity` and `norm_num`, and will also use any nonzeroness/positivity proofs included explicitly
(e.g. `field_simp [hx]`). If your expression is not completely reduced by `field_simp`, check the
denominators of the resulting expression and provide proofs that they are nonzero/positive to enable
further progress.
-/
elab (name := fieldSimp) "field_simp"tk:"!"?  d:(discharger)? args:(simpArgs)? loc:(location)? :
    tactic => withMainContext do
  let disch ← parseDischarger d args
  let disch {u : Level} (type : Q(Sort u)) : MetaM Q($type) :=
    if tk.isSome then do
      try disch type
      catch | _ => return ← mkFreshExprMVarQ type
    else disch type
  let cs ← IO.mkRef {}
  let s ← IO.mkRef {}
  let cleanup r := do r.mkEqTrans (← simpOnlyNames [] r.expr) -- convert e.g. `x = x` to `True`
  let m := CacheAtomM.recurse cs s {}
    ((fun e ↦ (reduceProp e <|> reduceExpr e) ⟨disch⟩)) cleanup
  let numGoals := (← getGoals).length
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  transformAtLocation (m ·) "field_simp" (failIfUnchanged := true) (mayCloseGoalFromHyp := true) loc
  if tk.isSome then
    let mut goals : List MVarId := []
    for ⟨⟨i, kind⟩, pf⟩ in ← cs.get do
      let some pf := pf | unreachable!
      if pf.isMVar then
        goals := pf.mvarId! :: goals
    let currGoals ← getGoals
    if currGoals.length < numGoals then
      setGoals (goals ++ currGoals)
    else
      let g :: l := currGoals | unreachable!
      setGoals (g :: goals ++ l)

/--
The goal of the `field_simp` conv tactic is to bring an expression in a (semi-)field over a common
denominator, i.e. to reduce it to an expression of the form `n / d` where neither `n` nor `d`
contains any division symbol. For example, `x / (1 - y) / (1 + y / (1 - y))` is reduced to
`x / (1 - y + y)`:
```
example (x y z : ℚ) (hy : 1 - y ≠ 0) :
    ⌊x / (1 - y) / (1 + y / (1 - y))⌋ < 3 := by
  conv => enter [1, 1]; field_simp
  -- new goal: `⊢ ⌊x / (1 - y + y)⌋ < 3`
```

As in this example, cancelling and combining denominators will generally require checking
"nonzeroness" side conditions. The `field_simp` tactic attempts to discharge these, and will omit
such steps if it cannot discharge the corresponding side conditions. The discharger will try, among
other things, `positivity` and `norm_num`, and will also use any nonzeroness proofs included
explicitly (e.g. `field_simp [hx]`). If your expression is not completely reduced by `field_simp`,
check the denominators of the resulting expression and provide proofs that they are nonzero to
enable further progress.

The `field_simp` conv tactic is a variant of the main (i.e., not conv) `field_simp` tactic. The
latter operates recursively on subexpressions, bringing *every* field-expression encountered to the
form `n / d`.
-/
elab "field_simp" d:(discharger)? args:(simpArgs)? : conv => do
  -- find the expression `x` to `conv` on
  let x ← Conv.getLhs
  let disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type) ← parseDischarger d args
  -- bring into field_simp standard form
  let r ← AtomM.run .reducible <| ((reduceExpr x).run disch)
  -- convert `x` to the output of the normalization
  Conv.applySimpResult r

/--
The goal of the simprocs grouped under the `field` attribute is to clear denominators in
(semi-)field (in)equalities, by bringing LHS and RHS each over a common denominator and then
cross-multiplying. For example, the `field` simproc will clear the `x` denominators in the following
equation:
```
example {K : Type*} [Field K] {x : K} (hx0 : x ≠ 0) :
    (x + 1 / x) ^ 2 + (x + 1 / x) = 1 := by
  simp only [field]
  -- new goal: `⊢ (x ^ 2 + 1) * (x ^ 2 + 1 + x) = x ^ 2`
```

The `field` simproc-set's functionality is a variant of the more general `field_simp` tactic, which
not only clears denominators in field (in)equalities but also brings isolated field expressions into
the normal form `n / d` (where neither `n` nor `d` contains any division symbol). (For confluence
reasons, the `field` simprocs also have a slightly different normal form from `field_simp`'s.)

Cancelling and combining denominators will generally require checking "nonzeroness"/"positivity"
side conditions. The `field` simproc-set attempts to discharge these, and will omit such steps if it
cannot discharge the corresponding side conditions. The discharger will try, among other things,
`positivity` and `norm_num`, and will also use any nonzeroness/positivity proofs included explicitly
in the simp call (e.g. `simp [field, hx]`). If your (in)equality is not completely reduced by the
`field` simproc-set, check the denominators of the resulting (in)equality and provide proofs that
they are nonzero/positive to enable further progress.
-/
def proc : Simp.Simproc := fun (t : Expr) ↦ do
  let ctx ← Simp.getContext
  let disch e : MetaM Expr := Prod.fst <$> (FieldSimp.discharge e).run ctx >>= Option.getM
  try
    let r ← AtomM.run .reducible <| (FieldSimp.reduceProp t).run disch
    -- the `field_simp`-normal form is in opposition to the `simp`-lemmas `one_div` and `mul_inv`,
    -- so we need to undo any such lemma applications, otherwise we can get infinite loops
    return .visit <| ← r.mkEqTrans (← simpOnlyNames [``one_div, ``mul_inv] r.expr)
  catch _ =>
    return .continue

end Mathlib.Tactic.FieldSimp

open Mathlib.Tactic

simproc_decl fieldEq (Eq _ _) := FieldSimp.proc
simproc_decl fieldLe (LE.le _ _) := FieldSimp.proc
simproc_decl fieldLt (LT.lt _ _) := FieldSimp.proc

attribute [field, inherit_doc FieldSimp.proc] fieldEq fieldLe fieldLt

/-!
 We register `field_simp` with the `hint` tactic.
 -/
register_hint field_simp
