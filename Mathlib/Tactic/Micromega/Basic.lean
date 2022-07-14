namespace Micromega

/-- A type of polynomial expressions. -/
-- coq: pExpr
inductive PolyExpr (α : Type) : Type
| const : α → PolyExpr α
| var : UInt32 → PolyExpr α
| add : PolyExpr α → PolyExpr α → PolyExpr α
| sub : PolyExpr α → PolyExpr α → PolyExpr α
| mul : PolyExpr α → PolyExpr α → PolyExpr α
| neg : PolyExpr α → PolyExpr α
| pow : PolyExpr α → Nat → PolyExpr α
deriving Repr

namespace PolyExpr

instance : Coe α (PolyExpr α) := ⟨const⟩
instance : Add (PolyExpr α) := ⟨add⟩
instance : Sub (PolyExpr α) := ⟨sub⟩
instance : Mul (PolyExpr α) := ⟨mul⟩
instance : Neg (PolyExpr α) := ⟨neg⟩
instance : Pow (PolyExpr α) Nat := ⟨pow⟩

-- coq: map_PExpr
variable (f : α → β) in
def map : PolyExpr α → PolyExpr β
| const a => const (f a)
| var i => var i
| add a b => add a.map b.map
| sub a b => sub a.map b.map
| mul a b => mul a.map b.map
| neg a => neg a.map
| pow a i => pow a.map i

-- coq: zeval_const
@[specialize]
def eval [Add α] [Sub α] [Mul α] [Neg α] [Pow α Nat] : PolyExpr α → Option α
| const c => some c
| var _ => none
| add e₁ e₂ => do some $ (← e₁.eval) + (← e₂.eval)
| sub e₁ e₂ => do some $ (← e₁.eval) - (← e₂.eval)
| mul e₁ e₂ => do some $ (← e₁.eval) * (← e₂.eval)
| neg e => do some $ -(← e.eval)
| pow e n => do some $ (← e.eval) ^ n

end PolyExpr

inductive Poly (α : Type) : Type
| /-- The polynomial `c : α` -/
  const : α → Poly α
| /-- Lift a polynomial by incrementing all variable indexes by `j > 0` -/
  inj (j : UInt32) : Poly α → Poly α
| /-- The polynomial `p * x_0^i + inj 1 q`, where `i > 0` -/
  var : Poly α → (i : Nat) → Poly α → Poly α
deriving BEq, Repr

namespace Poly

-- coq: xdenorm, denorm
def denorm : Poly α → (x : UInt32 := 0) → PolyExpr α
| const c, _ => PolyExpr.const c
| inj j p, x => p.denorm (x + j)
| var p j q, x => p.denorm x * PolyExpr.var x ^ j + q.denorm (x + 1)

-- coq: max_var
def maxVar : Poly α → (x : UInt32 := 0) → UInt32
| const _, x => x
| inj j p, x => p.maxVar (x + j)
| var p _ q, x => max (p.maxVar x) (q.maxVar (x + 1))

instance (n) [OfNat α n] : OfNat (Poly α) n := ⟨const (OfNat.ofNat n)⟩

-- coq: is_pol_Z0
@[specialize]
def isZero [OfNat α (nat_lit 0)] [BEq α] : Poly α → Bool
| const z => z == 0
| _ => false

def inj₀ (j : UInt32) (p : Poly α) : Poly α := if j == 0 then p else inj j p

-- coq: mkPinj
def mkInj (j : UInt32) : Poly α → Poly α
| p@(const _) => p
| inj j' q₀ => inj (j + j') q₀
| p => inj₀ j p

-- coq: mkPinj_pred
/-- requires: j ≠ 0 -/
def mkInjPred (j : UInt32) (p : Poly α) : Poly α := inj₀ (j-1) p

-- coq: mkPX
/-- requires: i ≠ 0 -/
def mkVar [BEq α] [OfNat α (nat_lit 0)] (p : Poly α) (i : Nat) (q₀ : Poly α) : Poly α :=
  match p with
  | const c => if c == 0 then q₀.mkInj 1 else var p i q₀
  | inj _ _ => var p i q₀
  | var p' i' q' => if q' == 0 then var p' (i' + i) q₀ else var p i q₀

-- coq: mkXi
/-- The polynomial `x₀^i`. -/
def x0Pow [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] (i : Nat) : Poly α :=
  if i == 0 then 1 else var 1 i 0

-- coq: mkX
/-- The polynomial `x₀`. -/
def x0 [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] : Poly α := x0Pow 1

-- coq: mk_X
/-- The polynomial `x_i`. -/
def xi [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] (j : UInt32) : Poly α := inj₀ j x0

@[specialize]
def map (f : α → α) : Poly α → Poly α
| const c => const (f c)
| inj j q => inj j (map f q)
| var p i q => var (map f p) i (map f q)

-- coq: paddC
def addConst [Add α] : Poly α → α → Poly α
| const c1, c => const (c1 + c)
| inj j q, c => inj j (addConst q c)
| var p i q, c => var p i (addConst q c)
instance [Add α] : HAdd (Poly α) α (Poly α) := ⟨addConst⟩

-- coq: psubC
def subConst [Add α] [Neg α] : Poly α → α → Poly α
| const c1, c => const (c1 + -c)
| inj j q, c => inj j (subConst q c)
| var p i q, c => var p i (subConst q c)
instance [Add α] [Neg α] : HSub (Poly α) α (Poly α) := ⟨subConst⟩

@[specialize]
instance [Neg α] : Neg (Poly α) := ⟨map Neg.neg⟩

-- coq: padd
@[specialize]
partial def add [OfNat α (nat_lit 0)] [BEq α] [Add α] : Poly α → Poly α → Poly α
| p, const c' => p + c'
| const c, inj j q₀ => inj j (q₀ + c)
| inj j' q', inj j q₀ =>
  if j ≤ j' then mkInj j (add (inj₀ (j'-j) q') q₀) else mkInj j' (add q' (inj (j-j') q₀))
| var p i q', inj j q₀ => if j == 1 then var p i (add q' q₀) else var p i (add q' (inj (j-1) q₀))
| p, var p' i' q' =>
  let rec addX (i' : Nat) : Poly α → Poly α
  | p@(const _) => var p' i' p
  | inj j' q' => var p' i' (mkInjPred j' q')
  | var p₂ i q' =>
    match compare i i' with
    | Ordering.eq => mkVar (add p₂ p') i q'
    | Ordering.gt => mkVar (add (var p₂ (i-i') 0) p') i' q'
    | Ordering.lt => mkVar (addX (i'-i) p₂) i q'
  match p with
  | const c => var p' i' (q' + c)
  | inj j₀ q₀ => var p' i' (add (mkInjPred j₀ q₀) q')
  | var p₂ i q₀ =>
    match compare i i' with
    | Ordering.eq => mkVar (add p₂ p') i (add q₀ q')
    | Ordering.gt => mkVar (add (var p₂ (i-i') 0) p') i' (add q₀ q')
    | Ordering.lt => mkVar (addX (i'-i) p₂) i (add q₀ q')

@[specialize]
instance [OfNat α (nat_lit 0)] [BEq α] [Add α] : Add (Poly α) := ⟨add⟩

-- coq: psub, psub0, psub1
@[specialize]
partial def sub [OfNat α (nat_lit 0)] [BEq α] [Add α] [Neg α] : Poly α → Poly α → Poly α
| p, const c' => p - c'
| const c, inj j q₀ => inj j (q₀ + -c)
| inj j' q', inj j q₀ =>
  if j ≤ j' then mkInj j (sub (inj₀ (j'-j) q') q₀) else mkInj j' (sub q' (inj (j-j') q₀))
| var p i q', inj j q₀ => if j == 1 then var p i (sub q' q₀) else var p i (sub q' (inj (j-1) q₀))
| p, var p' i' q' =>
  let rec subX (i' : Nat) : Poly α → Poly α
  | p@(const _) => var (-p') i' p
  | inj j' q' => var (-p') i' (mkInjPred j' q')
  | var p₂ i q' =>
    match compare i i' with
    | Ordering.eq => mkVar (sub p₂ p') i q'
    | Ordering.gt => mkVar (sub (var p₂ (i-i') 0) p') i' q'
    | Ordering.lt => mkVar (subX (i'-i) p₂) i q'
  match p with
  | const c => var (-p') i' (q' - c)
  | inj j₀ q₀ => var (-p') i' (sub (mkInjPred j₀ q₀) q')
  | var p₂ i q₀ =>
    match compare i i' with
    | Ordering.eq => mkVar (sub p₂ p') i (sub q₀ q')
    | Ordering.gt => mkVar (sub (var p₂ (i-i') 0) p') i' (sub q₀ q')
    | Ordering.lt => mkVar (subX (i'-i) p₂) i (sub q₀ q')

@[specialize]
instance [OfNat α (nat_lit 0)] [BEq α] [Add α] [Neg α] : Sub (Poly α) := ⟨sub⟩

-- coq: pmulC
def mulConst [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] [Mul α] [BEq α]
  (p : Poly α) (c : α) : Poly α :=
  if c == 0 then 0 else if c == 1 then p else
  let rec aux : Poly α → Poly α
  | const c' => const (c' * c)
  | inj j c' => inj j (aux c')
  | var p₂ i q₀ => mkVar (aux p₂) i (aux q₀)
  aux p
instance [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] [Mul α] [BEq α] :
  HMul (Poly α) α (Poly α) := ⟨mulConst⟩

-- coq: pmul
partial def mul [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] [Add α] [Mul α] [BEq α] :
  Poly α → Poly α → Poly α
| p, const c => p * c
| const c, inj j q₀ => mkInj j (q₀ * c)
| inj j' q', inj j q₀ =>
  if j ≤ j' then mkInj j (mul (inj₀ (j'-j) q') q₀) else mkInj j' (mul q' (inj (j-j') q₀))
| var _ i' q', inj j q₀  =>
  mkVar (mul q' (inj j q₀)) i' $ if j == 1 then mul q' q₀ else mul q' (inj (j-1) q₀)
| const c, p'' => p'' * c
| p@(inj j q₀), var p' i' q' => mkVar (mul p p') i' (mul (mkInjPred j q₀) q')
| var p₂ i q₀, var p' i' q' =>
  mkVar (mkVar (mul p₂ p') i 0 + (mul (mkInj 1 q₀) p')) i' 0 +
  mkVar (mul p₂ (inj 1 q')) i (mul q₀ q')
instance [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] [Add α] [Mul α] [BEq α] :
  Mul (Poly α) := ⟨mul⟩

-- coq: psquare
def square [∀ n, OfNat α n] [Add α] [Mul α] [BEq α] :
  Poly α → Poly α
| const c => const (c * c)
| inj j q₀ => inj j (square q₀)
| var p₂ i q₀ => mkVar (mkVar (square p₂) i 0 + p₂ * mkInj 1 (q₀ * 2)) i (square q₀)

-- coq: ppow_pos, ppow_N
variable (subst : Poly α → Poly α) in
partial def powAux [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] [Add α] [Mul α] [BEq α]
  (res p : Poly α) : (n : Nat) → Poly α
| 0 => 1
| 1 => subst (res * p)
| n =>
  let n' := n >>> 1; let a := powAux (powAux res p n') p n'
  if n &&& 1 = 0 then subst (a * p) else a

instance [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] [Add α] [Mul α] [BEq α] :
  Pow (Poly α) Nat := ⟨powAux id 1⟩

end Poly

-- coq: norm_aux, norm, normZ, normQ
@[specialize]
def PolyExpr.norm [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] [Add α] [Mul α] [Neg α] [BEq α] :
  PolyExpr α → Poly α
| const c => Poly.const c
| var j => Poly.xi j
| add (neg e₁) e₂ => norm e₂ - norm e₁
| add e₁ (neg e₂) => norm e₁ - norm e₂
| add e₁ e₂ => norm e₁ + norm e₂
| sub e₁ e₂ => norm e₁ - norm e₂
| mul e₁ e₂ => norm e₁ * norm e₂
| neg e₁ => -norm e₁
| pow e₁ n => norm e₁ ^ n

-- coq: kind
inductive Kind | prop | bool
deriving Repr

def Kind.isProp
| prop => true
| _ => false

-- coq: gFormula
variable (α ξ β φ : Type) in
inductive GFormula
| protected true : Kind → GFormula
| protected false : Kind → GFormula
| X : Kind → ξ → GFormula
| A : Kind → α → β → GFormula
| and : Kind → GFormula → GFormula → GFormula
| or : Kind → GFormula → GFormula → GFormula
| not : Kind → GFormula → GFormula
| imp : Kind → GFormula → Option φ → GFormula → GFormula
| iff : Kind → GFormula → GFormula → GFormula
| eq : GFormula → GFormula → GFormula
deriving Repr

namespace GFormula

-- coq: mapX
variable (f : Kind → ξ → ξ') in
def mapX : GFormula α ξ β φ → GFormula α ξ' β φ
| GFormula.true k => GFormula.true k
| GFormula.false k => GFormula.false k
| X k x => X k (f k x)
| A k a b => A k a b
| and k f₁ f₂ => and k (mapX f₁) (mapX f₂)
| or k f₁ f₂ => or k (mapX f₁) (mapX f₂)
| not k f => not k (mapX f)
| imp k f₁ o f₂ => imp k (mapX f₁) o (mapX f₂)
| iff k f₁ f₂ => iff k (mapX f₁) (mapX f₂)
| eq f₁ f₂ => eq (mapX f₁) (mapX f₂)

variable (f : α → α') in
def mapA : GFormula α ξ β φ → GFormula α' ξ β φ
| GFormula.true k => GFormula.true k
| GFormula.false k => GFormula.false k
| X k x => X k x
| A k a b => A k (f a) b
| and k f₁ f₂ => and k (mapA f₁) (mapA f₂)
| or k f₁ f₂ => or k (mapA f₁) (mapA f₂)
| not k f => not k (mapA f)
| imp k f₁ o f₂ => imp k (mapA f₁) o (mapA f₂)
| iff k f₁ f₂ => iff k (mapA f₁) (mapA f₂)
| eq f₁ f₂ => eq (mapA f₁) (mapA f₂)

-- coq: foldA
variable (f : β → γ → γ) in
def foldB : GFormula α ξ β φ → γ → γ
| A _ _ an => f an
| and _ f₁ f₂ => foldB f₁ ∘ foldB f₂
| or _ f₁ f₂ => foldB f₁ ∘ foldB f₂
| not _ f => foldB f
| imp _ f₁ _ f₂ => foldB f₁ ∘ foldB f₂
| iff _ f₁ f₂ => foldB f₁ ∘ foldB f₂
| eq f₁ f₂ => foldB f₁ ∘ foldB f₂
| _ => id

-- coq: ids_of_formula
def ids : GFormula α ξ β φ → (arr : Array φ := #[]) → Array φ
| imp _ _ none f', arr => ids f' arr
| imp _ _ (some a) f', arr => ids f' $ arr.push a
| _, arr => arr

-- coq: collect_annot
def annots : GFormula α ξ β φ → (arr : Array β := #[]) → Array β := foldB fun a arr => arr.push a

end GFormula

-- coq: clause
def Clause (σ α : Type) := Array (σ × α)
-- coq: cnf
def CNF (σ α) := Array (Clause σ α)

instance : ForIn m (Clause σ α) (σ × α) := Array.instForInArray
instance : ForIn m (CNF σ α) (Clause σ α) := Array.instForInArray
instance : Append (CNF σ α) := Array.instAppendArray

-- coq: cnf_tt
protected def CNF.true : CNF σ α := #[]
-- coq: cnf_ff
protected def CNF.false : CNF σ α := #[#[]]

instance : Inhabited (CNF σ α) := ⟨CNF.false⟩

def Clause.isFalse (f : Clause σ α) := f.isEmpty

-- coq: is_cnf_tt
def CNF.isTrue (f : CNF σ α) := f.isEmpty

-- coq: is_cnf_ff
def CNF.isFalse : CNF σ α → Bool
  | #[#[]] => true
  | _ => false

class Deduce (σ) := (unsat : σ → Bool) (deduce : σ → σ → Option σ)

-- coq: add_term
def Clause.addTerm [Deduce σ] (t₀ : σ × α) (cl : Clause σ α) : Option (Clause σ α) := do
  let check (t' : σ × α) : Option Unit := do
    if let some u := Deduce.deduce t₀.1 t'.1 then
      if Deduce.unsat u then none
  for lit in cl do check lit
  check t₀
  some $ cl.push t₀

-- coq: or_clause
def Clause.or [Deduce σ] (cl₁ cl₂ : Clause σ α) : Option (Clause σ α) := do
  let mut out := cl₂
  for lit in cl₁ do
    out ← out.addTerm lit
  out

-- coq: or_clause_cnf
def CNF.or₁ [Deduce σ] (f : CNF σ α) (cl : Clause σ α) : CNF σ α :=
  if cl.isFalse then f else f.filterMap cl.or

-- coq: and_cnf_opt
def CNF.and (f f' : CNF σ α) : CNF σ α :=
  if f.isFalse || f'.isFalse then CNF.false else
  if f'.isTrue then f else if f.isTrue then f' else f ++ f'
instance : AndOp (CNF σ α) := ⟨CNF.and⟩

-- coq: or_cnf_opt
def CNF.or [Deduce σ] (f f' : CNF σ α) : CNF σ α :=
  if f.isTrue || f'.isTrue then CNF.true else
  if f'.isFalse then f else if f.isFalse then f' else
  f.foldl (init := CNF.true) fun acc cl => acc ++ f'.or₁ cl
instance [Deduce σ] : OrOp (CNF σ α) := ⟨CNF.or⟩

class Normalize (α σ β) where
  norm : α → β → CNF σ β
  negate : α → β → CNF σ β

namespace GFormula

-- coq: is_bool
def isBool : GFormula α ξ β φ → Option Bool
| GFormula.true _ => some true
| GFormula.false _ => some false
| _ => none

-- coq: xcnf
def xcnf [Deduce σ] [Normalize α σ β] : (negate : Bool := true) → GFormula α ξ β φ → CNF σ β
| _, X _ _ => panic! "xcnf X"
| true, GFormula.true _ => CNF.true
| false, GFormula.true _ => CNF.false
| true, GFormula.false _ => CNF.false
| false, GFormula.false _ => CNF.true
| true, A _ a b => Normalize.negate a b
| false, A _ a b => Normalize.norm a b
| true, and _ e₁ e₂ => xcnf true e₁ &&& xcnf true e₂
| false, and _ e₁ e₂ => xcnf false e₁ ||| xcnf false e₂
| true, or _ e₁ e₂ => xcnf true e₁ ||| xcnf true e₂
| false, or _ e₁ e₂ => xcnf false e₁ &&& xcnf false e₂
| true, imp _ e₁ _ e₂ => xcnf false e₁ ||| xcnf true e₂
| false, imp _ e₁ _ e₂ => xcnf true e₁ &&& xcnf false e₂
| p, not _ e => xcnf (!p) e
| p, iff _ e₁ e₂ =>
  match e₂.isBool with
  | some b => xcnf (b == p) e₁
  | none => xcnf (!p) e₁ &&& xcnf false e₂ ||| xcnf p e₁ &&& xcnf true e₂
| p, eq e₁ e₂ =>
  match e₂.isBool with
  | some b => xcnf (b == p) e₁
  | none => xcnf (!p) e₁ &&& xcnf false e₂ ||| xcnf p e₁ &&& xcnf true e₂

end GFormula

-- coq: trace
inductive Trace (α : Type)
| null
| push : α → Trace α → Trace α
| merge : Trace α → Trace α → Trace α
deriving Inhabited

instance : EmptyCollection (Trace α) := ⟨Trace.null⟩
instance : Add (Trace α) := ⟨Trace.merge⟩
instance : Coe α (Trace α) := ⟨fun a => Trace.null.push a⟩

-- coq: radd_term
def Clause.addTermT [Deduce σ] (t₀ : σ × α) (cl : Clause σ α) : Except (Trace α) (Clause σ α) := do
  let check (t' : σ × α) : Except (Trace α) Unit := do
    if let some u := Deduce.deduce t₀.1 t'.1 then
      if Deduce.unsat u then throw ↑t'.2
  for lit in cl do check lit
  check t₀
  pure $ cl.push t₀

-- coq: ror_clause
def Clause.orT [Deduce σ] (cl₁ cl₂ : Clause σ α) : Except (Trace α) (Clause σ α) := do
  let mut out := cl₂
  for lit in cl₁ do
    out ← out.addTermT lit
  pure out

-- coq: ror_clause_cnf
def CNF.orT₁ [Deduce σ] (f : CNF σ α) (cl : Clause σ α) : CNF σ α × Trace α :=
  if cl.isFalse then (f, ∅) else
    f.foldl (init := (#[], ∅)) fun (acc, tr) cl' =>
      match cl.orT cl' with
      | Except.ok cl => (acc.push cl, tr)
      | Except.error tr' => (acc, tr + tr')

-- coq: ror_cnf
def CNF.orT [Deduce σ] (f f' : CNF σ α) : CNF σ α × Trace α :=
  if f.isTrue || f'.isTrue then (CNF.true, ∅) else
  if f'.isFalse then (f, ∅) else if f.isFalse then (f', ∅) else
  f.foldl (init := (CNF.true, ∅)) fun (acc, tr) cl =>
    let (acc', tr') := f'.orT₁ cl; (acc ++ acc', tr + tr')

-- coq: ratom
def atomT (f : CNF σ α) (a : α) : CNF σ α × Trace α :=
  if f.isTrue || f.isFalse then (f, a) else (f, ∅)

instance : AndOp (CNF σ α × Trace α) where
  and := fun (f, tr) (f', tr') => (f.and f', tr + tr')

instance [Deduce σ] : OrOp (CNF σ α × Trace α) where
  or := fun (f, tr) (f', tr') =>
    let (f'', tr'') := f.orT f'; (f'', tr + tr' + tr'')

-- coq: rxcnf, cnfQ
variable (normalize negate : α → β → CNF σ β) in
def GFormula.xcnfT [Deduce σ] [Normalize α σ β] :
  (negate : Bool := true) → GFormula α ξ β φ → CNF σ β × Trace β
| _, X _ _ => panic! "xcnf X"
| true, GFormula.true _ => (CNF.true, ∅)
| false, GFormula.true _ => (CNF.false, ∅)
| true, GFormula.false _ => (CNF.false, ∅)
| false, GFormula.false _ => (CNF.true, ∅)
| true, A _ a b => atomT (Normalize.negate a b) b
| false, A _ a b => atomT (Normalize.norm a b) b
| true, and _ e₁ e₂ => xcnfT true e₁ &&& xcnfT true e₂
| false, and _ e₁ e₂ => xcnfT false e₁ ||| xcnfT false e₂
| true, or _ e₁ e₂ => xcnfT true e₁ ||| xcnfT true e₂
| false, or _ e₁ e₂ => xcnfT false e₁ &&& xcnfT false e₂
| true, imp _ e₁ _ e₂ => xcnfT false e₁ ||| xcnfT true e₂
| false, imp _ e₁ _ e₂ => xcnfT true e₁ &&& xcnfT false e₂
| p, not _ e => xcnfT (!p) e
| p, iff _ e₁ e₂ =>
  match e₂.isBool with
  | some b => xcnfT (b == p) e₁
  | none => xcnfT (!p) e₁ &&& xcnfT false e₂ ||| xcnfT p e₁ &&& xcnfT true e₂
| p, eq e₁ e₂ =>
  match e₂.isBool with
  | some b => xcnfT (b == p) e₁
  | none => xcnfT (!p) e₁ &&& xcnfT false e₂ ||| xcnfT p e₁ &&& xcnfT true e₂

-- coq: to_constrT
class ToConstr (α β ξ) where
  protected true : Kind → ξ
  protected false : Kind → ξ
  A : Kind → α → β → ξ
  and : Kind → ξ → ξ → ξ
  or : Kind → ξ → ξ → ξ
  imp : Kind → ξ → ξ → ξ
  iff : Kind → ξ → ξ → ξ
  not : Kind → ξ → ξ
  eq : ξ → ξ → ξ

-- coq: aformula
def GFormula.toConstr [ToConstr α β ξ] : GFormula α ξ β φ → ξ
| GFormula.true k => ToConstr.true α β k
| GFormula.false k => ToConstr.false α β k
| X _ x => x
| A k a b => ToConstr.A k a b
| and k f₁ f₂ => ToConstr.and α β k (toConstr f₁) (toConstr f₂)
| or k f₁ f₂ => ToConstr.or α β k (toConstr f₁) (toConstr f₂)
| not k f => ToConstr.not α β k (toConstr f)
| imp k f₁ _ f₂ => ToConstr.imp α β k (toConstr f₁) (toConstr f₂)
| iff k f₁ f₂ => ToConstr.iff α β k (toConstr f₁) (toConstr f₂)
| eq f₁ f₂ => ToConstr.eq α β (toConstr f₁) (toConstr f₂)

-- coq: is_X
def GFormula.isX : GFormula α ξ β φ → Option ξ
| X _ p => some p
| _ => none

-- coq: abst_simpl
variable [ToConstr α β ξ] (needA : β → Bool) in
def GFormula.abstS : GFormula α ξ β φ → GFormula α ξ β φ
| f@(A k a b) => if needA b then f else X k (ToConstr.A k a b)
| and k e₁ e₂ => abstS e₁ |>.and k <| abstS e₂
| or k e₁ e₂ => abstS e₁ |>.or k <| abstS e₂
| not k e => abstS e |>.not k
| imp k e₁ o e₂ => abstS e₁ |>.imp k o <| abstS e₂
| iff k e₁ e₂ => abstS e₁ |>.iff k <| abstS e₂
| eq e₁ e₂ => abstS e₁ |>.eq <| abstS e₂
| x => x

-- coq: abs_and
variable [ToConstr α β ξ] (F : Kind → (f₁ f₂ : GFormula α ξ β φ) → GFormula α ξ β φ) in
def GFormula.absAnd (k : Kind) (f₁ f₂ : GFormula α ξ β φ) : GFormula α ξ β φ :=
  let F := F k f₁ f₂; if f₁.isX.isSome || f₂.isX.isSome then X k F.toConstr else F

-- coq: abs_or
variable [ToConstr α β ξ] (F : Kind → (f₁ f₂ : GFormula α ξ β φ) → GFormula α ξ β φ) in
def GFormula.absOr (k : Kind) (f₁ f₂ : GFormula α ξ β φ) : GFormula α ξ β φ :=
  let F := F k f₁ f₂; if f₁.isX.isSome && f₂.isX.isSome then X k F.toConstr else F

-- coq: abs_not
variable [ToConstr α β ξ] (F : Kind → GFormula α ξ β φ → GFormula α ξ β φ) in
def GFormula.absNot (k : Kind) (f : GFormula α ξ β φ) : GFormula α ξ β φ :=
  let F := F k f; if f.isX.isSome then X k F.toConstr else F

-- coq: mk_arrow
def GFormula.mkArrow (o : Option φ) (k : Kind) (f₁ f₂ : GFormula α ξ β φ) : GFormula α ξ β φ :=
  if o.isSome && f₁.isX.isSome then f₂ else imp k f₁ o f₂

variable [ToConstr α β ξ] (needA : β → Bool) in
mutual
partial def GFormula.absIff (F : (f₁ f₂ : GFormula α ξ β φ) → GFormula α ξ β φ)
  (p : Bool) (k : Kind) (e₁ e₂ : GFormula α ξ β φ) : GFormula α ξ β φ :=
  let F := F (abstS needA e₁) (abstS needA e₂)
  if ((abst (!p) e₁).isX.isSome || (abst false e₂).isX.isSome) &&
     ((abst p e₁).isX.isSome || (abst true e₂).isX.isSome)
  then X k F.toConstr else F

-- coq: abst_form
partial def GFormula.abst : Bool → GFormula α ξ β φ → GFormula α ξ β φ
| true, f@(GFormula.true _) => f
| false, GFormula.true k => X k (ToConstr.true α β k)
| true, GFormula.false k => X k (ToConstr.false α β k)
| false, f@(GFormula.false _) => f
| _, X k p => X k p
| _, f@(A k a b) => if needA b then f else X k (ToConstr.A k a b)
| true, and k e₁ e₂ => absAnd and k (abst true e₁) (abst true e₂)
| false, and k e₁ e₂ => absOr and k (abst false e₁) (abst false e₂)
| true, or k e₁ e₂ => absOr or k (abst true e₁) (abst true e₂)
| false, or k e₁ e₂ => absAnd or k (abst false e₁) (abst false e₂)
| true, imp k e₁ o e₂ => absOr (mkArrow o) k (abst false e₁) (abst true e₂)
| false, imp k e₁ o e₂ => absOr (mkArrow o) k (abst true e₁) (abst false e₂)
| p, not k e => let f := abst (!p) e; if f.isX.isSome then X k (not k f).toConstr else not k f
| p, iff k e₁ e₂ => absIff (iff k) p k e₁ e₂
| p, eq e₁ e₂ => absIff eq p Kind.bool e₁ e₂
end

-- coq: cnf_checker
partial def CNF.check
  (checker : Clause σ α → β → Option Unit) (f : CNF σ α) (l : Array β) : Option Unit :=
  let rec loop (i : Nat) : Option Unit := do
    if h : i < f.size then
      if h' : i < l.size then
        checker (f.get ⟨i, h⟩) (l.get ⟨i, h'⟩); loop (i+1)
      else none
  loop 0

-- coq: tauto_checker
def tautoChecker [Deduce σ] [Normalize α σ β]
  (checker : Clause σ β → γ → Option Unit) (f : GFormula α ξ β φ) (w : Array γ) : Option Unit :=
  f.xcnf true |>.check checker w

-- coq: op1
inductive Ord | zero | nonzero | pos | nonneg deriving Repr

-- coq: nFormula
def Atom (α) := Poly α × Ord
instance [Repr α] : Repr (Atom α) := inferInstanceAs (Repr (_×_))

instance [OfNat α (nat_lit 0)] : Inhabited (Atom α) := ⟨(0, Ord.zero)⟩

-- coq: opMult
def Ord.mul : Ord → Ord → Option Ord
| Ord.zero, _ => some Ord.zero
| _, Ord.zero => some Ord.zero
| Ord.nonzero, Ord.nonzero => some Ord.nonzero
| Ord.nonzero, _ => none
| _, Ord.nonzero => none
| Ord.pos, Ord.pos => some Ord.pos
| _, _ => some Ord.nonneg

-- coq: opAdd
def Ord.add : Ord → Ord → Option Ord
| Ord.zero, o => some o
| o, Ord.zero => some o
| Ord.nonzero, _ => none
| _, Ord.nonzero => none
| Ord.nonneg, Ord.nonneg => some Ord.nonneg
| _, _ => some Ord.pos

-- coq: psatz, qWitness, rWitness
inductive PSatz (α)
| /-- `0 = 0` -/
  zero
| /-- `c > 0`, for a positive constant `c` -/
  const : α → PSatz α
| /-- hypothesis `n` -/
  hyp : Nat → PSatz α
| /-- `p * p ≥ 0` -/
  square : Poly α → PSatz α
| /-- if `q = 0` then `p * q = 0` -/
  smul : Poly α → PSatz α → PSatz α
| /--
  if `p ≻₁ 0` and `q ≻₂ 0` then `p * q ≻₃ 0`, where `≻₁` is determined from `≻₁`, `≻₂`:
  * If `p = 0` then `p * q = 0` and similarly for `q`
  * If `p ≠ 0` and `q ≠ 0` then `p * q ≠ 0`
  * If `p > 0` and `q > 0` then `p * q > 0`
  * If `p ≥ 0` and `q > 0` then `p * q ≥ 0` and similarly for `q`
  -/
  mul : PSatz α → PSatz α → PSatz α
| /--
  if `p ≻₁ 0` and `q ≻₂ 0` then `p + q ≻₃ 0`, where `≻₁` is determined from `≻₁`, `≻₂`:
  * If `p = 0` or `q ≻₂ 0` then `p + q ≻₂ 0` and similarly for `q`
  * If `p ≥ 0` and `q ≥ 0` then `p + q ≥ 0`
  * If `p ≥ 0` and `q > 0` then `p + q > 0` and similarly for `q`
  -/
  add : PSatz α → PSatz α → PSatz α
deriving Inhabited, Repr

-- coq: pexpr_times_nformula
def Atom.smul [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] [Add α] [Mul α] [BEq α] :
  Poly α → Atom α → Option (Atom α)
| p, (ef, Ord.zero) => some (p * ef, Ord.zero)
| _, _ => none

-- coq: nformula_times_nformula
def Atom.mul [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] [Add α] [Mul α] [BEq α] :
  Atom α → Atom α → Option (Atom α)
| (e₁, o₁), (e₂, o₂) => return (e₁ * e₂, ← o₁.mul o₂)

-- coq: nformula_plus_nformula, zdeduce, qdeduce, rdeduce
@[specialize]
def Atom.add [OfNat α (nat_lit 0)] [BEq α] [Add α] : Atom α → Atom α → Option (Atom α)
| (e₁, o₁), (e₂, o₂) => return (e₁ + e₂, ← o₁.add o₂)

-- coq: eval_Psatz, eval_Psatz0
variable [∀ n, OfNat α n] [Add α] [Mul α] [BEq α] [LT α] [DecidableRel (@LT.lt α _)]
  (l : Array (Atom α)) in
@[specialize]
def PSatz.eval : PSatz α → Option (Atom α)
| hyp n => l[n]?
| square e => some (e.square, Ord.nonneg)
| smul re e => do (← e.eval).smul re
| mul e₁ e₂ => do (← e₁.eval).mul (← e₂.eval)
| add e₁ e₂ => do (← e₁.eval).add (← e₂.eval)
| const c => if 0 < c then some (Poly.const c, Ord.pos) else none
| zero => some (0, Ord.zero)

-- coq: check_inconsistent, zunsat, qunsat, runsat
@[specialize]
def Atom.inconsistent [OfNat α (nat_lit 0)] [BEq α] [LT α] [DecidableRel (@LT.lt α _)] :
  Atom α → Bool
| (Poly.const c, o) =>
  match o with
  | Ord.zero => c != 0
  | Ord.nonzero => c == 0
  | Ord.pos => !(0 < c)
  | Ord.nonneg => c < 0
| _ => false

@[specialize]
instance [OfNat α (nat_lit 0)] [BEq α] [Add α] [LT α] [DecidableRel (@LT.lt α _)] :
  Deduce (Atom α) := ⟨Atom.inconsistent, Atom.add⟩

-- coq: check_normalized_formulas, zWeakChecker, qWeakChecker, rWeakChecker
@[specialize]
def PSatz.check [∀ n, OfNat α n] [Add α] [Mul α] [BEq α] [LT α] [DecidableRel (@LT.lt α _)]
  (l : Array (Atom α)) (cm : PSatz α) : Option Unit :=
  match cm.eval l with
  | some f => guard f.inconsistent
  | none => none

-- coq: op2
inductive Ineq | eq | ne | le | ge | lt | gt deriving Repr

-- coq: formula
structure AtomExpr (α) where
  lhs : PolyExpr α
  op : Ineq
  rhs : PolyExpr α
  deriving Repr

-- coq: normalise, xnnormalise
@[specialize]
def AtomExpr.norm [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] [Add α] [Mul α] [Neg α] [BEq α] :
  AtomExpr α → Atom α
| ⟨lhs, Ineq.eq, rhs⟩ => (lhs.norm - rhs.norm, Ord.zero)
| ⟨lhs, Ineq.ne, rhs⟩ => (lhs.norm - rhs.norm, Ord.nonzero)
| ⟨lhs, Ineq.le, rhs⟩ => (rhs.norm - lhs.norm, Ord.nonneg)
| ⟨lhs, Ineq.ge, rhs⟩ => (lhs.norm - rhs.norm, Ord.nonneg)
| ⟨lhs, Ineq.lt, rhs⟩ => (rhs.norm - lhs.norm, Ord.pos)
| ⟨lhs, Ineq.gt, rhs⟩ => (lhs.norm - rhs.norm, Ord.pos)

-- coq: xnormalise
def Atom.strictNegate [Neg α] : Atom α → Array (Atom α)
| (e, Ord.zero) => #[(e, Ord.pos), (-e, Ord.pos)]
| (e, Ord.nonzero) => #[(e, Ord.zero)]
| (e, Ord.pos) => #[(-e, Ord.nonneg)]
| (e, Ord.nonneg) => #[(-e, Ord.pos)]

-- coq: xnegate
def Atom.strictNorm [Neg α] : Atom α → Array (Atom α)
| (e, Ord.nonzero) => #[(e, Ord.pos), (-e, Ord.pos)]
| p => #[p]

-- coq: cnf_of_list, cnf_of_list0
@[specialize]
def Atom.cnfOfList [OfNat α (nat_lit 0)] [BEq α] [LT α] [DecidableRel (@LT.lt α _)]
  (ats : Array (Atom α)) (tag : β) : CNF (Atom α) β :=
  ats.filterMap fun a => if a.inconsistent then none else some #[(a, tag)]

@[specialize]
instance [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)]
  [Add α] [Mul α] [Neg α] [BEq α] [LT α] [DecidableRel (@LT.lt α _)] :
  Normalize (AtomExpr α) (Atom α) β where
  -- coq: cnf_negate, qnegate, rnegate
  norm e tag := let f := e.norm
    if f.inconsistent then CNF.true else Atom.cnfOfList f.strictNorm tag
  -- coq: cnf_normalise, qnormalise, rnormalise
  negate e tag := let f := e.norm
    if f.inconsistent then CNF.false else Atom.cnfOfList f.strictNegate tag

-- coq: map_Formula
def AtomExpr.map (f : α → β) : AtomExpr α → AtomExpr β
| ⟨lhs, o, rhs⟩ => ⟨lhs.map f, o, rhs.map f⟩

-- coq: simpl_cone
def PSatz.simpCone [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] [Mul α] [BEq α] : PSatz α → PSatz α
| square (Poly.const c) => if c == 0 then zero else const (c * c)
| mul zero _ => zero
| mul _ zero => zero
| add zero e => e
| add e zero => e
| mul (mul (const c) x) (const c') => mul (const (c * c')) x
| mul (mul x (const c)) (const c') => mul (const (c * c')) x
| mul (const c) (mul (const c') x) => mul (const (c * c')) x
| mul (const c) (mul x (const c')) => mul (const (c * c')) x
  -- TODO: should there be a symmetric version?
| mul (const c) (add x y) => add (mul (const c) x) (mul (const c) y)
| mul (const c) (const c') => const (c * c')
| e@(mul (const c) x) => if c == 1 then x else e
| e@(mul x (const c)) => if c == 1 then x else e
| e => e

-- coq: q
structure Rat where
  num : Int
  denom : Nat

instance : BEq Rat := ⟨fun ⟨xn, xd⟩ ⟨yn, yd⟩ => xn * yd == yn * xd⟩
instance : LE Rat := ⟨fun ⟨xn, xd⟩ ⟨yn, yd⟩ => xn * yd ≤ yn * xd⟩
instance : DecidableRel (@LE.le Rat _) :=
  fun ⟨_,_⟩ ⟨_,_⟩ => inferInstanceAs (Decidable ((_:Int) ≤ _))
instance : LT Rat := ⟨fun ⟨xn, xd⟩ ⟨yn, yd⟩ => xn * yd < yn * xd⟩
instance : DecidableRel (@LT.lt Rat _) :=
  fun ⟨_,_⟩ ⟨_,_⟩ => inferInstanceAs (Decidable ((_:Int) < _))
instance : Add Rat := ⟨fun ⟨xn, xd⟩ ⟨yn, yd⟩ => ⟨xn * yd + yn * xd, xd * yd⟩⟩
instance : Mul Rat := ⟨fun ⟨xn, xd⟩ ⟨yn, yd⟩ => ⟨xn * yn, xd * yd⟩⟩
instance : Neg Rat := ⟨fun ⟨n, d⟩ => ⟨-n, d⟩⟩
instance : Sub Rat := ⟨fun a b => a + -b⟩
def Rat.ofInt (n : Int) : Rat := ⟨n, 1⟩
instance : OfNat Rat n := ⟨Rat.ofInt n⟩

-- coq: qinv
def Rat.inv : Rat → Rat
| ⟨0, _⟩ => 0
| ⟨Int.ofNat n, d⟩ => ⟨d, n⟩
| ⟨Int.negSucc n, d⟩ => ⟨d, n+1⟩

partial def powNat [OfNat α (nat_lit 1)] [Mul α] (r : α) : Nat → α
| 0 => 1
| 1 => r
| n => let n' := n >>> 1; let a := powNat r n'; if n &&& 1 = 0 then a * a * r else a * a

instance : Pow Int Nat := ⟨powNat⟩
instance : Pow Rat Nat := ⟨powNat⟩

-- coq: qpower
def Rat.pow (r : Rat) : Int → Rat
| Int.ofNat n => r ^ n
| Int.negSucc n => (r ^ (n+1)).inv

instance : Pow Rat Int := ⟨Rat.pow⟩

instance : Repr Rat := ⟨fun ⟨n, d⟩ _ => if d == 1 then repr n else s!"{n}/{d}"⟩

-- coq: xnormalise0
def Atom.negateInt : Atom Int → Array (Atom Int)
| (e, Ord.zero) => #[(e - 1, Ord.nonneg), (-1 - e, Ord.nonneg)]
| (e, Ord.nonzero) => #[(e, Ord.zero)]
| (e, Ord.pos) => #[(-e, Ord.nonneg)]
| (e, Ord.nonneg) => #[(-1 - e, Ord.nonneg)]

-- coq: xnegate0
def Atom.normInt : Atom Int → Array (Atom Int)
| (e, Ord.nonzero) => #[(e - 1, Ord.nonneg), (-1 - e, Ord.nonneg)]
| (e, Ord.pos) => #[(e - 1, Ord.nonneg)]
| p => #[p]

instance : Normalize (AtomExpr Int) (Atom Int) β where
  -- coq: negate
  norm e tag := let f := e.norm
    if f.inconsistent then CNF.true else Atom.cnfOfList f.normInt tag
  -- coq: normalise0
  negate e tag := let f := e.norm
    if f.inconsistent then CNF.false else Atom.cnfOfList f.negateInt tag

-- E-rounding: This pair satisfies 0 ≤ mod x y < nat_abs y for y ≠ 0
def Int.divEuclid : Int → Int → Int
| Int.ofNat m, Int.ofNat n => Int.ofNat (m / n)
| Int.ofNat m, Int.negSucc n => -Int.ofNat (m / Nat.succ n)
| Int.negSucc _, 0 => 0
| Int.negSucc m, Int.ofNat (n+1) => Int.negSucc (m / Nat.succ n)
| Int.negSucc m, Int.negSucc n => Int.ofNat (Nat.succ (m / Nat.succ n))

def Int.modEuclid : Int → Int → Int
| Int.ofNat m, n => Int.ofNat (m % Int.natAbs n)
| Int.negSucc m, n => Int.subNatNat (Int.natAbs n) (Nat.succ (m % Int.natAbs n))

-- coq: ceiling
def divCeil (a b : Int) : Int := if a % b == 0 then a / b else Int.divEuclid a b + 1

-- coq: zArithProof
inductive ZArithProof
| done
| rat : PSatz Int → ZArithProof → ZArithProof
| cut : PSatz Int → ZArithProof → ZArithProof
| split : Poly Int → ZArithProof → ZArithProof → ZArithProof
| enum : PSatz Int → PSatz Int → Array ZArithProof → ZArithProof
| ex : UInt32 → ZArithProof → ZArithProof
deriving Repr

-- coq: Z.gcd
def Int.gcd (x y : Int) : Int := (Int.natAbs x).gcd (Int.natAbs y)
-- coq: zgcdM
def gcdM (x y : Int) : Int := max (Int.gcd x y) 1

-- coq: zgcd_pol
def Poly.gcdInt : Poly Int → Int × Int
| const c => (0, c)
| inj _ p => p.gcdInt
| var p _ q => let (g₁, c₁) := p.gcdInt; let (g₂, c₂) := q.gcdInt; (gcdM (gcdM g₁ c₁) g₂, c₂)

-- coq: zdiv_pol
def Poly.divInt (p : Poly Int) (x : Int) : Poly Int := map (Int.divEuclid · x) p

-- coq: makeCuttingPlane
def Poly.cuttingPlane (p : Poly Int) : Poly Int × Int :=
  let (g, c) := p.gcdInt
  if g > 0 then ((p - c).map (Int.divEuclid · g), -divCeil (-c) g) else (p, 0)

-- coq: genCuttingPlane
def Atom.cuttingPlane : Atom Int → Option ((Poly Int × Int) × Ord)
| (e, Ord.zero) =>
  let (g, c) := e.gcdInt
  if g > 0 && c != 0 && Int.gcd g c == g then none else (e.cuttingPlane, Ord.zero)
| (e, Ord.nonzero) => some ((e, 0), Ord.nonzero)
| (e, Ord.pos) => some ((e - 1).cuttingPlane, Ord.nonzero)
| (e, Ord.nonneg) => some (e.cuttingPlane, Ord.nonzero)

-- coq: nformula_of_cutting_plane
def Atom.ofCuttingPlane : (Poly Int × Int) × Ord → Atom Int
| ((e, z), o) => (e + Poly.const z, o)

-- coq: valid_cut_sign
def Ord.validCutSign : Ord → Bool
| Ord.zero => true
| Ord.nonneg => true
| _ => false

-- coq: bound_var
def AtomExpr.varNonneg (v : UInt32) : AtomExpr Int :=
  ⟨PolyExpr.var v, Ineq.ge, PolyExpr.const 0⟩

-- coq: mk_eq_pos
def AtomExpr.eqSub (x y t : UInt32) : AtomExpr Int :=
  ⟨PolyExpr.var x, Ineq.eq, PolyExpr.var y - PolyExpr.var t⟩

-- coq: max_var_nformulae
def Atom.listMaxVar (l : Array (Atom α)) : UInt32 := l.foldl (fun m a => a.1.maxVar m) 0

-- coq: zChecker
partial def ZArithProof.check (l : Array (Atom Int)) : ZArithProof → Option Unit
| done => none
| rat w pf => do
  let f ← w.eval l
  if !f.inconsistent then pf.check (l.push f)
| cut w pf => do
  if let some cp := (← w.eval l).cuttingPlane then
    pf.check $ l.push (Atom.ofCuttingPlane cp)
| split p pf₁ pf₂ => do
  let cp₁ ← Atom.cuttingPlane (p, Ord.nonneg)
  let cp₂ ← Atom.cuttingPlane (-p, Ord.nonneg)
  pf₁.check $ l.push (Atom.ofCuttingPlane cp₁)
  pf₂.check $ l.push (Atom.ofCuttingPlane cp₂)
| enum w₁ w₂ pfs => do
  let f₁ ← w₁.eval l; let f₂ ← w₂.eval l
  if let some ((e₁, z₁), o₁) := f₁.cuttingPlane then
    if let some ((e₂, z₂), o₂) := f₂.cuttingPlane then
      guard $ o₁.validCutSign && o₂.validCutSign && (e₁ + e₂).isZero
      let mut i := -z₁
      for pf in pfs do
        pf.check $ l.push (e₁ - Poly.const i, Ord.zero)
        i := i + 1
      guard $ i > z₂
| ex x pf => do
  let fr := Atom.listMaxVar l
  guard $ x ≤ fr
  let z := fr + 1; let t := z + 1
  pf.check $ l
    |>.push (AtomExpr.eqSub x z t).norm
    |>.push (AtomExpr.varNonneg z).norm
    |>.push (AtomExpr.varNonneg t).norm

-- coq: bFormula
def BFormula (α ξ) := GFormula α ξ Unit Unit

def BFormula.map (f : α → β) : BFormula α ξ → BFormula β ξ := GFormula.mapA f

-- coq: qTautoChecker
def tautoCheckerAtom
  [∀ n, OfNat α n] [Add α] [Mul α] [Neg α] [BEq α] [LT α] [DecidableRel (@LT.lt α _)]
  (l : BFormula (AtomExpr α) ξ) (pfs : Array (PSatz α)) : Option Unit :=
tautoChecker (fun cl => PSatz.check (cl.map (·.1))) l pfs

-- coq: zTautoChecker
def tautoCheckerInt
  (l : BFormula (AtomExpr Int) ξ) (pfs : Array ZArithProof) : Option Unit :=
tautoChecker (fun cl => ZArithProof.check (cl.map (·.1))) l pfs

-- coq: rcst
inductive RConst
| zero
| one
| rat : Rat → RConst
| int : Int → RConst
| add : RConst → RConst → RConst
| sub : RConst → RConst → RConst
| mul : RConst → RConst → RConst
| pow : RConst → Int ⊕ Nat → RConst
| inv : RConst → RConst
| neg : RConst → RConst
deriving Repr

-- coq: q_of_Rcst
def RConst.eval : RConst → Rat
| zero => 0
| one => 1
| rat r => r
| int z => ⟨z, 1⟩
| add a b => a.eval + b.eval
| sub a b => a.eval - b.eval
| mul a b => a.eval * b.eval
| pow a (Sum.inl n) => a.eval ^ n
| pow a (Sum.inr n) => a.eval ^ n
| inv a => a.eval.inv
| neg a => -a.eval

-- coq: rTautoChecker
def tautoCheckerR (l : BFormula (AtomExpr RConst) ξ) (pfs : Array (PSatz Rat)) : Option Unit :=
tautoCheckerAtom (l.map (·.map (·.eval))) pfs
