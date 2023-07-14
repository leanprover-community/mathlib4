/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Expr
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Vector
import Mathlib.Control.Monad.Cont

/-! # Automatically generated lemmas for working with concrete matrices

This file contains "magic" lemmas which autogenerate to the correct size of matrix. For instance,
`Matrix.of_mul_of_fin` can be used as:
```lean
example {α} [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
  !![a₁₁, a₁₂;
     a₂₁, a₂₂] ⬝ !![b₁₁, b₁₂;
                    b₂₁, b₂₂] = !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;
                                   a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂] := by
  rw [of_mul_of_fin% 2 2 2]
```

## Main results

* `Matrix.fin_eta.elab`: the elaborator `fin_eta% m n A` which expands a matrix into coefficients
* `Matrix.of_mul_of_fin.elab`: the elaborator `of_mul_of_fin% l m n` which produces a lemma
  about matrix multiplication.

-/

open Lean Lean.Meta Elab Qq

/-- Like `List.mapM` but for a tuple. -/
def PiFin.mapM {α : Type u} {n : ℕ} {m : Type u → Type v} [Monad m] (f : Fin n → m α) :
    m (Fin n → α) :=
  Vector.get <$> Vector.mmap f ⟨List.finRange n, List.length_finRange _⟩

/-- Convert a vector of Exprs to the Expr constructing that vector.-/
def PiFin.toExprQ {u : Level} {α : Q(Type u)} :
    ∀ {n : ℕ}, (Fin n → Q($α)) → Q(Fin $n → $α)
  | 0, _v => q(![])
  | _n + 1, v => q(Matrix.vecCons $(v 0) $(PiFin.toExprQ <| Matrix.vecTail v))


namespace Matrix

/-- Like `PiFin.mapM` but for a matrix. -/
def mapM {α : Type u} {n o : ℕ} {m : Type u → Type v} [Monad m]
    (f : Matrix (Fin n) (Fin o) (m α)) :
    m (Matrix (Fin n) (Fin o) α) :=
  Matrix.of <$> (PiFin.mapM <| fun i => PiFin.mapM <| fun j => f i j)

/-- `PiFin.toExprQ` but for matrices -/
def toExprQ {u : Level} {m n : ℕ} {α : Q(Type u)} (A : Matrix (Fin m) (Fin n) Q($α)) :
  Q(Matrix (Fin $m) (Fin $n) $α) :=
q(Matrix.of $(PiFin.toExprQ (u := u) fun i : Fin m => PiFin.toExprQ fun j : Fin n => A i j))

namespace fin_eta


/-- Prove a statement of the form `∀ {α} A : Matrix m n α, A = !![A 0 0, ...]`.
Returns an assigned metavariable whose type is this statement. -/
def prove (m n : ℕ) : MetaM Expr := do
  let u ← mkFreshLevelMVar
  -- Note: Qq seems to need type ascriptions on `fun` binders even though
  -- the type is easily inferred. Is there a metavariable instantiation bug?
  withLocalDeclQ `α .implicit q(Type u) fun (α : Q(Type u)) =>
  withLocalDeclDQ `A q(Matrix (Fin $m) (Fin $n) $α) fun A => do
    let entry_vals : Q(Fin $m → Fin $n → $α) :=
      PiFin.toExprQ (u := u) (fun i : Fin m => PiFin.toExprQ (fun j : Fin n => q($A $i $j)))
    let A_eta : Q(Matrix (Fin $m) (Fin $n) $α) := q(Matrix.of $entry_vals)
    let forall_A_eq : Q(Prop) ← mkForallFVars #[α, A] q($A = $A_eta)
    let heq : Q(Matrix.etaExpand $A = $A_eta) := (q(Eq.refl $A_eta) : Expr)
    let some pf ← checkTypeQ (ty := forall_A_eq) <| ← mkLambdaFVars #[α, A]
                                                        q((Matrix.etaExpand_eq $A).symm.trans $heq)
          | throwError "(internal error) fin_eta% generated proof with incorrect type."
    mkExpectedTypeHint pf forall_A_eq

/-- `fin_eta% m n` for `m` and `n` natural number literals generates an eta expansion theorem,
for example
```lean
fin_eta% 2 3 : ∀ {α : Type u_1} (A : Matrix (Fin 2) (Fin 3) α),
                  A = ↑of ![![A 0 0, A 0 1, A 0 2],
                            ![A 1 0, A 1 1, A 1 2]]
``` -/
elab:max (name := «elab») "fin_eta% " mStx:term:max nStx:term:max A?:(term)? : term => do
  let m : Q(Nat) ← Term.elabTermEnsuringType mStx (mkConst ``Nat)
  let n : Q(Nat) ← Term.elabTermEnsuringType nStx (mkConst ``Nat)
  let A? ←
    match A? with
    | some A => do
      let u ← mkFreshLevelMVar
      let α : Q(Type u) ← mkFreshExprMVarQ q(Type u)
      some <$> Term.elabTermEnsuringType A q(Matrix (Fin $m) (Fin $n) $α)
    | none => pure none
  let some m ← (evalNat m).run
    | throwErrorAt mStx "Expecting a natural number, have{indentD m}"
  let some n ← (evalNat n).run
    | throwErrorAt nStx "Expecting a natural number, have{indentD n}"
  let pf ← prove m n
  if let some A := A? then
    Term.elabAppArgs pf #[] #[.expr A] none false false
  else
    return pf

-- /-- Helper tactic used as an `auto_param` for `matrix.fin_eta` -/
-- meta def fin_eta.derive : tactic unit :=
-- do
--   target@`(%%A' = %%A_eta) ← tactic.target,
--   (expr.const `matrix ls, [`(fin %%m), `(fin %%n), α])
--     ← expr.get_app_fn_args <$> tactic.infer_type A',
--   some (m, n) ← pure (prod.mk <$> m.to_nat <*> n.to_nat) |
--     fail!"Dimensions {m} {n} are not numerals",
--   (t,pr) ← matrix.fin_eta.prove m n,

--   tactic.unify target (t.instantiate_pis [α, A']),
--   tactic.exact (pr α A')

-- /-- This lemma expands `A` into `!![A 0 0, ...]`. -/
-- theorem fin_eta {α} {m n : ℕ}
--   (A : matrix (fin m) (fin n) α) {«!![A 0 0, ...]» : matrix (fin m) (fin n) α}
--   (h : A = «!![A 0 0, ...]» . matrix.fin_eta.derive) : A = «!![A 0 0, ...]» := h

-- example : true :=
-- begin
--   let B : matrix (fin 20) (fin 20) ℕ := 0,
--   have := matrix.fin_eta B,  -- 400 coefficients, but very fast
--   have : B = B, by rw this,
--   trivial,
-- end

end fin_eta

section of_mul_of_fin

/-- Choose a name suffix for a matrix index -/
private def nameSuffix {m n : ℕ} : Fin m → Fin n → String :=
  let chars := "₀₁₂₃₄₅₆₇₈₉".data
  if h : m ≤ 10 ∧ n ≤ 10
  then (fun i j => [chars.get <| i.castLE (i.prop.trans_le h.1),
                    chars.get <| j.castLE (j.prop.trans_le h.2)].asString)
  else (fun i j => "_" ++ toString i ++ "_" ++ toString j)

/-- Prove a statement of the form
```
∀ α [has_mul α] [add_comm_monoid α] (a₁₁ ... aₗₘ b₁₁ ... bₘₙ : α),
   !![a₁₁ ⋱ aₗₘ] ⬝ !![b₁₁ ⋱ bₘₙ] = !![⋱]
```
Returns the type of this statement and its proof. -/
def prove (l m n : ℕ) : MetaM Expr :=
do
  let u ← mkFreshLevelMVar
  -- Note: Qq seems to need type ascriptions on `fun` binders even though
  -- the type is easily inferred. Is there a metavariable instantiation bug?
  withLocalDeclQ `α .implicit q(Type u) fun (α : Q(Type u)) => do
  withLocalDeclQ `inst_1 .instImplicit q(Mul $α) fun (instMulα : Q(Mul $α)) => do
  withLocalDeclQ `inst_2 .instImplicit q(AddCommMonoid $α) fun (instAddCommMonoidα : Q(AddCommMonoid $α)) => do
    -- trick: create algebraic instances on `Expr` so that we can use `Matrix.mul` or
    -- `Matrix.mulᵣ` to build the expression we want to end up with. It doesn't matter which we
    -- pick but the typeclasses are easier to create for the latter.
    let _zero := Expr.instZero α (←synthInstanceQ q(Zero $α))
    let _add := Expr.instAdd α (←synthInstanceQ q(Add $α))
    let _mul := Expr.instMul α (←synthInstanceQ q(Mul $α))

    -- moving to `ContT` lets us use `withLocalDeclDQ` with `Matrix.mapM`
    (ContT.run · pure) do
      -- introduce variables for each coefficient
      let a : Matrix (Fin l) (Fin m) Q($α) ← Matrix.mapM <| fun i j =>
          withLocalDeclDQ ((`a).appendAfter (nameSuffix i j)) _
      let b : Matrix (Fin m) (Fin n) Q($α) ← Matrix.mapM <| fun i j =>
          withLocalDeclDQ ((`b).appendAfter (nameSuffix i j)) _
      let a_flat := (List.finRange l).bind <| fun i => (List.finRange m).map <| fun j => a i j
      let b_flat := (List.finRange m).bind <| fun i => (List.finRange n).map <| fun j => b i j
      let args := (#[α, instMulα, instAddCommMonoidα] : Array Expr) ++
        (show Array Expr from a_flat.toArray ++ b_flat.toArray : Array Expr)

      -- build the matrices out of the coefficients
      let A := Matrix.toExprQ a
      let B := Matrix.toExprQ b
      let AB := Matrix.toExprQ (Matrix.mulᵣ a b)

      -- State and prove the equality, noting the RHS is defeq to `mulᵣ A B`.
      let forall_A_eq : Q(Prop) ← mkForallFVars args q($A ⬝ $B = $AB)
      let pf' ← mkLambdaFVars args <|
        (show Q($A ⬝ $B = $AB) from (q((Matrix.mulᵣ_eq $A $B).symm) : Expr))
      let some pf ← checkTypeQ (ty := forall_A_eq) <| pf'
            | throwError "(internal error) of_mul_of_fin% generated proof with incorrect type."
      mkExpectedTypeHint pf forall_A_eq

elab:max (name := of_mul_of_fin_elab)
    "of_mul_of_fin% " lStx:term:max mStx:term:max nStx:term:max : term => do
  let l : Q(Nat) ← Term.elabTermEnsuringType mStx (mkConst ``Nat)
  let m : Q(Nat) ← Term.elabTermEnsuringType mStx (mkConst ``Nat)
  let n : Q(Nat) ← Term.elabTermEnsuringType nStx (mkConst ``Nat)
  let some l ← (evalNat l).run
    | throwErrorAt lStx "Expecting a natural number, have{indentD l}"
  let some m ← (evalNat m).run
    | throwErrorAt mStx "Expecting a natural number, have{indentD m}"
  let some n ← (evalNat n).run
    | throwErrorAt nStx "Expecting a natural number, have{indentD n}"
  prove l m n

-- /-- Helper tactic used as an `auto_param` for `matrix.of_mul_of_fin` -/
-- meta def of_mul_of_fin.derive : tactic unit :=
-- do
--   target@`(@matrix.mul (fin %%l) (fin %%m) (fin %%n) %%α %%_ %%i1 %%i2 %%A %%B = %%AB)
--     ← tactic.target,
--   some (l, m, n) ← pure (prod.mk <$> l.to_nat <*> (prod.mk <$> m.to_nat <*> n.to_nat)) |
--     fail!"Dimensions {l}, {m} {n} are not numerals",
--   (t,pr) ← of_mul_of_fin.prove l m n,
--   tactic.apply (pr α i1 i2) {},
--   tactic.done
--   -- TODO: should we be extracting the coefficients manually so we can do a full invocation as
--   -- something like:
--   --   tactic.unify target (t.instantiate_pis [α, A']),
--   --   tactic.exact (pr α A')

-- /-- This lemma assumes that `a_coeffs` and `b_coeffs` refer to expressions of the form
-- `![![x₀₀, x₀₁], ![x₁₀, x₁₁]]`. It then uses an `auto_param` to populate `ab_coeffs` with an
-- expression of the same form, containing the appropriate expressions in terms of `+`, `*`, `aᵢⱼ`,
-- and `bⱼₖ`. -/
-- theorem of_mul_of_fin {α} [has_mul α] [add_comm_monoid α] {l m n : ℕ}
--   {a_coeffs : fin l → fin m → α}
--   {b_coeffs : fin m → fin n → α}
--   {ab_coeffs : fin l → fin n → α}
--   (h : of a_coeffs ⬝ of b_coeffs = of ab_coeffs . of_mul_of_fin.derive) :
--     of a_coeffs ⬝ of b_coeffs = of ab_coeffs := h

end of_mul_of_fin

end Matrix
