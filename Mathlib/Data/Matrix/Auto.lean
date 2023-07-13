/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Expr
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Vector

/-! # Automatically generated lemmas for working with concrete matrices

This file contains "magic" lemmas which autogenerate to the correct size of matrix. For instance,
`Matrix.of_mul_of_fin` can be used as:
```lean
example {α} [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
  !![a₁₁, a₁₂;
     a₂₁, a₂₂] ⬝ !![b₁₁, b₁₂;
                    b₂₁, b₂₂] = !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;
                                   a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂] := by
  rw of_mul_of_fin
```

## Main results

* `Matrix.fin_eta`
* `Matrix.of_mul_of_fin`

-/

/-- Like `List.mapM` but for a vector. -/
def Fin.mapM {α : Type u} {n : ℕ} {m : Type u → Type v} [Monad m] (f : Fin n → m α) :
    m (Fin n → α) :=
  Vector.get <$> Vector.mmap f ⟨List.finRange n, List.length_finRange _⟩

open Lean Lean.Meta Elab Qq

namespace Matrix

namespace fin_eta


/-- Convert a vector of Exprs to the Expr constructing that vector.-/
def _root_.PiFin.toExprQ {u : Level} {α : Q(Type u)} :
    ∀ {n : ℕ}, (Fin n → Q($α)) → Q(Fin $n → $α)
  | 0, _v => q(![])
  | _n + 1, v => q(Matrix.vecCons $(v 0) $(PiFin.toExprQ <| Matrix.vecTail v))

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
elab:max "fin_eta% " mStx:term:max nStx:term:max A?:(term)? : term => do
  let m : Q(Nat) ← Term.elabTermEnsuringType mStx (mkConst ``Nat)
  let n : Q(Nat) ← Term.elabTermEnsuringType nStx (mkConst ``Nat)
  let A? ←
    match A? with
    | some A => do
      let u ← mkFreshLevelMVar
      let α : Q(Type u) ← mkFreshExprMVarQ q(Type u)
      some <$> Term.elabTermEnsuringType A q(Fin $m → Fin $n → $α)
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

variable (α : Type u) (A : Matrix (Fin _) (Fin _) α) in
#check (fin_eta% 2 3 A : A = of ![![A 0 0, A 0 1, A 0 2], ![A 1 0, A 1 1, A 1 2]])

variable (α : Type u) (A : Matrix (Fin _) (Fin _) α) in
#check (fin_eta% _ _ A : A = of ![![A 0 0, A 0 1, A 0 2], ![A 1 0, A 1 1, A 1 2]])

example (A : Matrix (Fin 2) (Fin 3) ℕ) : A = 0 := by
  rw [fin_eta% _ _ A]
  dsimp

example : true := by
  let B : Matrix (Fin 20) (Fin 20) ℕ := 0
  have := fin_eta% _ _ B
  have : B = B := by rw [this]
  trivial


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
then (fun i j => [
  chars.get <| i.castLE (i.prop.trans_le h.1), chars.get <| j.castLE (j.prop.trans_le h.2)].asString)
else (fun i j => "_" ++ toString i ++ "_" ++ toString j)

/-- `pi_fin.to_pexpr` but for matrices -/
def fin_to_pexpr {u : Level} {m n : ℕ} {α : Q(Type u)} (A : Matrix (Fin m) (Fin n) Q($α)) :
  Q(Matrix (Fin $m) (Fin $n) $α) :=
q(Matrix.of $(PiFin.toExprQ (u := u) fun i : Fin m => PiFin.toExprQ fun j : Fin n => A i j))

/-- This statement is defeq to `of_mul_of_fin`, but syntactically worse-/
theorem of_mul_of_fin_aux (l m n : ℕ) ⦃α⦄ [Mul α] [AddCommMonoid α] :
  Forall $ fun A : Matrix (Fin l) (Fin m) α =>
    Forall $ fun B : Matrix (Fin m) (Fin n) α =>
      A.mul B = A.mulᵣ B :=
by simp_rw [forall_iff, mulᵣ_eq, eq_self_iff_true, forall_const]

/-- Prove a statement of the form
```
∀ α [has_mul α] [add_comm_monoid α] (a₁₁ ... aₗₘ b₁₁ ... bₘₙ : α),
   !![a₁₁ ⋱ aₗₘ] ⬝ !![b₁₁ ⋱ bₘₙ] = !![⋱]
```
Returns the type of this statement and its proof. -/
def of_mul_of_fin.prove (l m n : ℕ) : MetaM Expr :=
do
  let u ← mkFreshLevelMVar
  -- Note: Qq seems to need type ascriptions on `fun` binders even though
  -- the type is easily inferred. Is there a metavariable instantiation bug?
  withLocalDeclQ `α .implicit q(Type u) fun (α : Q(Type u)) => do
  withLocalDeclQ `inst_1 .instImplicit q(Mul $α) fun (instMulα : Q(Mul $α)) => do
  withLocalDeclQ `inst_2 .instImplicit q(Mul $α) fun (instAddCommMonoidα : Q(AddCommMonoid $α)) => do
    -- todo: convert CPS into a monad?
    let a : Fin l → Fin m → Q($α) ← (Fin.mapM $ fun i : Fin l => Fin.mapM $ fun j : Fin m =>
        tactic.mk_local' ((`a).append_suffix (nameSuffix i j)) binder_info.default α)
    let b : Fin m → Fin n → Q($α)  ← (Fin.mapM $ fun i : Fin m => Fin.mapM $ fun j : Fin n =>
        tactic.mk_local' ((`b).append_suffix (nameSuffix i j)) binder_info.default α)
    let a_flat := (List.finRange l).bind (fun i => (List.finRange m).map $ fun j => a i j)
    let b_flat := (List.finRange m).bind (fun i=> (List.finRange n).map $ fun j => b i j)
    let args := (#[α, instMulα, instAddCommMonoidα] : Array Expr) ++
      (show Array Expr from a_flat.toArray) ++ (show Array Expr from b_flat.toArray)

    -- build the matrices out of the coefficients
    let A := Matrix.fin_to_pexpr a
    let B := Matrix.fin_to_pexpr b
    -- -- get an instance cache holding all the instances needed for matrix multiplication. There must
    -- -- be a better way to do this.
    -- t ← tactic.mk_instance_cache α,
    -- has_add_α ← tactic.mk_app `has_add [α] >>= (λ t, prod.snd <$> @tactic.solve_aux unit t (do
    -- { tmp2 ← tactic.pose `_inst_2' none add_comm_monoid_α,
    --   tactic.reset_instance_cache,
    --   tactic.apply_instance })),
    -- has_zero_α ← tactic.mk_app `has_zero [α] >>= (λ t, prod.snd <$> @tactic.solve_aux unit t (do
    -- { tmp2 ← tactic.pose `_inst_2' none add_comm_monoid_α,
    --   tactic.reset_instance_cache,
    --   tactic.apply_instance })),
    -- let t := {inst := [
    --   (`has_mul, has_mul_α),
    --   (`has_add, has_add_α),
    --   (`has_zero, has_zero_α),
    --   (`add_comm_monoid, add_comm_monoid_α)].foldl (λ n x, n.insert x.1 x.2) t.inst,
    --   ..t},

    -- -- clever trick: create algebraic instances on `expr` so that we can use `matrix.mul` or
    -- -- `matrix.mulᵣ` to build the expression we want to end up with. It doesn't matter which we pick,
    -- -- but the typeclasses are easier to create for the latter.
    -- (t, has_mul_αe) ← expr.has_mul t,
    -- (t, has_add_αe) ← expr.has_add t,
    -- (t, has_zero_αe) ← expr.has_zero t,
    -- let ab := @matrix.mulᵣ _ _ _ _ has_mul_αe has_add_αe has_zero_αe a b,
    -- let AB := matrix.fin_to_pexpr (matrix.map ab to_pexpr),

    -- -- State and prove the equality, noting the RHS is defeq to `mulᵣ A B`.
    -- A_eq ← tactic.to_expr ``(@matrix.mul _ _ _ _ _ %%has_mul_α %%add_comm_monoid_α %%A %%B = %%AB),
    -- t ← tactic.pis args A_eq,
    -- let pr := (expr.const `matrix.of_mul_of_fin_aux [u]).mk_app [`(l), `(m), `(n)],
    -- -- This seems to create a metavariable then assign it, which ensures `pr` carries the right type.
    -- ((), pr) ← tactic.solve_aux t $ tactic.exact pr,

    -- pure (t, pr)
    sorry

open scoped Matrix

#exit


/-- Helper tactic used as an `auto_param` for `matrix.of_mul_of_fin` -/
meta def of_mul_of_fin.derive : tactic unit :=
do
  target@`(@matrix.mul (fin %%l) (fin %%m) (fin %%n) %%α %%_ %%i1 %%i2 %%A %%B = %%AB)
    ← tactic.target,
  some (l, m, n) ← pure (prod.mk <$> l.to_nat <*> (prod.mk <$> m.to_nat <*> n.to_nat)) |
    fail!"Dimensions {l}, {m} {n} are not numerals",
  (t,pr) ← of_mul_of_fin.prove l m n,
  tactic.apply (pr α i1 i2) {},
  tactic.done
  -- TODO: should we be extracting the coefficients manually so we can do a full invocation as
  -- something like:
  --   tactic.unify target (t.instantiate_pis [α, A']),
  --   tactic.exact (pr α A')

/-- This lemma assumes that `a_coeffs` and `b_coeffs` refer to expressions of the form
`![![x₀₀, x₀₁], ![x₁₀, x₁₁]]`. It then uses an `auto_param` to populate `ab_coeffs` with an
expression of the same form, containing the appropriate expressions in terms of `+`, `*`, `aᵢⱼ`,
and `bⱼₖ`. -/
theorem of_mul_of_fin {α} [has_mul α] [add_comm_monoid α] {l m n : ℕ}
  {a_coeffs : fin l → fin m → α}
  {b_coeffs : fin m → fin n → α}
  {ab_coeffs : fin l → fin n → α}
  (h : of a_coeffs ⬝ of b_coeffs = of ab_coeffs . of_mul_of_fin.derive) :
    of a_coeffs ⬝ of b_coeffs = of ab_coeffs := h

end of_mul_of_fin

end matrix
