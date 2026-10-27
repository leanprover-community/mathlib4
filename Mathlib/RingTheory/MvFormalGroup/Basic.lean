/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.Data.Matrix.Diagonal

/-!
# Multidimensional formal group laws

A formal group law over `R` has an arbitrary coordinate index `σ`, which may be infinite.
Variables are indexed by `Fin 2 × σ`: `(0, i)` denotes `Xᵢ` and `(1, i)` denotes `Yᵢ`.
The linear part is `X + Y`, and the law is associative. In addition, each monomial
occurs in only finitely many coordinate series (`coeff_zero`).

The identity equations are deduced using order estimates valid for arbitrary variables.
Commutativity is a separate property `MvFormalGroup.IsComm`. Finite-index convenience lemmas and
the `truncTotal` API retain their `[Finite σ]` hypotheses.
-/

@[expose] public section

noncomputable section

open MvPowerSeries Finsupp Function

/-- A formal group law over a commutative ring `R` with (possibly infinite) coordinate
index `σ`. -/
@[ext]
structure MvFormalGroup (σ : Type*) (R : Type*) [CommRing R] [DecidableEq σ] where
  /-- The coordinate power series `F(i)(X, Y)`. -/
  toPowerSeries : σ → MvPowerSeries (Fin 2 × σ) R
  /-- Every coordinate has zero constant term. -/
  zero_constantCoeff i : constantCoeff (toPowerSeries i) = 0
  /-- The coefficient of `Xⱼ` in `F(i)` is the Kronecker delta. -/
  lin_coeff_X i j : coeff (single (0, j) 1) (toPowerSeries i) = (1 : Matrix σ σ R) j i
  /-- The coefficient of `Yⱼ` in `F(i)` is the Kronecker delta. -/
  lin_coeff_Y i j : coeff (single (1, j) 1) (toPowerSeries i) = (1 : Matrix σ σ R) j i
  /-- Every monomial `XᵐYⁿ` occurs in only finitely many `F(i)`. -/
  coeff_zero d : {i | coeff d (toPowerSeries i) ≠ 0}.Finite
  /-- Associativity condition: `F(F(X, Y), Z) = F(X, F(Y, Z))`, coordinate by coordinate. -/
  assoc i :
    let V : Fin 3 → σ → MvPowerSeries (Fin 3 × σ) R := curry X
    (toPowerSeries i).subst (uncurry
      ![fun j ↦ (toPowerSeries j).subst (uncurry ![V 0, V 1]), V 2]) =
    (toPowerSeries i).subst (uncurry
      ![V 0, fun j ↦ (toPowerSeries j).subst (uncurry ![V 1, V 2])])

namespace MvFormalGroup

variable {R : Type*} [CommRing R] {σ τ υ : Type*} [DecidableEq σ]

/-- Commutativity condition: `F(X, Y) = F(Y, X)`. -/
class IsComm (F : MvFormalGroup σ R) : Prop where
  comm i : F.toPowerSeries i = (F.toPowerSeries i).subst (uncurry ![curry X 1, curry X 0])

section Basic

variable (F : MvFormalGroup σ R) {S : Type*} [CommRing S] [Algebra R S]
  {x y z : σ → MvPowerSeries τ S}

@[simp]
lemma lin_coeff_X_eq_ite {i j : σ} :
    (F.toPowerSeries i).coeff (single (0, j) 1) = if j = i then 1 else 0 := by
  rw [lin_coeff_X, Matrix.one_apply]

@[simp]
lemma lin_coeff_Y_eq_ite {i j : σ} :
    (F.toPowerSeries i).coeff (single (1, j) 1) = if j = i then 1 else 0 := by
  rw [lin_coeff_Y, Matrix.one_apply]

/-- `F(i)(X, Y) ≡ Xᵢ + Yᵢ` modulo terms of total degree at least two. -/
theorem coeff_eq_of_degree_lt_two (i : σ) {d : Fin 2 × σ →₀ ℕ} (hd : d.degree < 2) :
    coeff d (F.toPowerSeries i) = coeff d (X (0, i) + X (1, i)) := by
  obtain h0 | h1 : d.degree = 0 ∨ d.degree = 1 := by omega
  · have : d = 0 := d.degree_eq_zero_iff.mp h0
    simp [this, F.zero_constantCoeff]
  · obtain ⟨⟨b, j⟩, rfl⟩ := (Finsupp.sum_eq_one_iff d).mp h1
    fin_cases b <;> simp [F.lin_coeff_X, F.lin_coeff_Y, coeff_X,
      Finsupp.single_left_inj, eq_comm, Matrix.one_apply]

/-- The coefficient axioms give exactly the prescribed truncation modulo degree two. -/
theorem truncTotal_two [Finite σ] (F : MvFormalGroup σ R) (i : σ) :
    (F.toPowerSeries i).truncTotal 2 = MvPolynomial.X (0, i) + MvPolynomial.X (1, i) := by
  ext d
  rw [coeff_truncTotal_eq_ite, ← MvPolynomial.coeff_coe]
  split_ifs with hd
  · simpa using F.coeff_eq_of_degree_lt_two i hd
  · have (s : Fin 2 × σ) : d ≠ single s 1 := by intro rfl; simp at hd
    simp [coeff_X, this]

theorem hasSubst : HasSubst F.toPowerSeries where
  const_coeff i := by simp [F.zero_constantCoeff]
  coeff_zero := F.coeff_zero

omit [DecidableEq σ] in
/-- Substituting `a` into `f(x, y)` is the same as substituting `(x(a), y(a))` into `f`. -/
theorem subst_pair_subst {T : Type*} [CommRing T]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] (f : MvPowerSeries (Fin 2 × σ) R)
    {a : τ → MvPowerSeries υ T}
    (hx : HasSubst x) (hy : HasSubst y) (ha : HasSubst a) :
    (f.subst (uncurry ![x, y])).subst a =
      f.subst (uncurry ![fun i ↦ (x i).subst a, fun i ↦ (y i).subst a]) := by
  rw [subst_comp_subst_apply (HasSubst.uncurry (by simp [hx, hy])) ha f]
  congr! 2 with ⟨b, i⟩
  fin_cases b <;> rfl

/-- `F(x, y)` is substitutable whenever `x` and `y` are. -/
theorem hasSubst_subst_pair (hx : HasSubst x) (hy : HasSubst y) :
    HasSubst fun j ↦ (F.toPowerSeries j).subst (uncurry ![x, y]) := by
  simpa using F.hasSubst.comp (hx.pair hy)

/-- Associativity after substituting three substitutable families. -/
theorem assoc_subst (hx : HasSubst x) (hy : HasSubst y) (hz : HasSubst z) (i : σ) :
    (F.toPowerSeries i).subst (uncurry ![fun j ↦ (F.toPowerSeries j).subst (uncurry ![x, y]), z]) =
      (F.toPowerSeries i).subst
        (uncurry ![x, fun j ↦ (F.toPowerSeries j).subst (uncurry ![y, z])]) := by
  have ha : HasSubst (uncurry ![x, y, z]) := .uncurry fun b ↦ by fin_cases b <;> assumption
  have hF (b c : Fin 3) :
      HasSubst fun j ↦ (F.toPowerSeries j).subst (uncurry ![curry (X (R := R)) b, curry X c]) := by
    simpa using F.hasSubst.comp (.uncurry fun d ↦ by fin_cases d <;> exact HasSubst.X.curry _)
  simpa [subst_pair_subst, HasSubst.X.curry, hF, ha, subst_X] using
    congrArg (subst (uncurry ![x, y, z])) (F.assoc i)

/-! ### The identity -/

omit [DecidableEq σ] in
/-- Substituting `(x, y)` into `Xᵢ + Yᵢ` gives `xᵢ + yᵢ`. -/
private theorem subst_X_add_X (hx : HasSubst x) (hy : HasSubst y) (i : σ) :
    (X (0, i) + X (1, i) : MvPowerSeries (Fin 2 × σ) R).subst (uncurry ![x, y]) = x i + y i := by
  simp [subst_add (hx.pair hy), subst_X (hx.pair hy)]

/-- `F(x, y) ≡ x + y` modulo terms of total degree at least two. -/
theorem two_le_order_subst_sub
    (hx : HasSubst x) (hy : HasSubst y) (hx0 : ∀ i, constantCoeff (x i) = 0)
    (hy0 : ∀ i, constantCoeff (y i) = 0) (i : σ) :
    2 ≤ ((F.toPowerSeries i).subst (uncurry ![x, y]) - (x i + y i)).order := by
  have hp0 : ∀ s, constantCoeff (uncurry ![x, y] s) = 0 := by
    simp [Prod.forall, Fin.forall_fin_two, hx0, hy0]
  rw [← subst_X_add_X (R := R) hx hy, ← subst_sub (hx.pair hy), ← one_mul 2]
  refine .trans (mul_le_mul ?_ ?_ zero_le zero_le) (le_order_subst (hx.pair hy) _)
  · exact le_iInf <| by simp [one_le_order_iff_constCoeff_eq_zero, hx0, hy0]
  · refine le_order fun d hd => ?_
    rw [map_sub, coeff_eq_of_degree_lt_two _ _ (mod_cast hd), ← map_sub]
    simp

/-- The family of series `F(X, 0)`. -/
abbrev Xzero : σ → MvPowerSeries σ R := fun i ↦ (F.toPowerSeries i).subst (uncurry ![X, 0])

/-- The family of series `F(0, X)`. -/
abbrev zeroX : σ → MvPowerSeries σ R := fun i ↦ (F.toPowerSeries i).subst (uncurry ![0, X])

@[simp]
theorem constantCoeff_Xzero (i : σ) : constantCoeff (F.Xzero i) = 0 :=
  constantCoeff_subst_eq_zero (.uncurry <| Fin.forall_fin_two.mpr ⟨.X, .zero⟩)
    (by simp [Fin.forall_fin_two]) (F.zero_constantCoeff i)

@[simp]
theorem constantCoeff_zeroX (i : σ) : constantCoeff (F.zeroX i) = 0 :=
  constantCoeff_subst_eq_zero (.uncurry <| Fin.forall_fin_two.mpr ⟨.zero, .X⟩)
    (by simp [Fin.forall_fin_two]) (F.zero_constantCoeff i)

theorem Xzero_subst_Xzero (i : σ) : (F.Xzero i).subst F.Xzero = F.Xzero i := by
  have hs : HasSubst F.Xzero := F.hasSubst_subst_pair .X .zero
  rw [Xzero, subst_pair_subst _ (x := X) (y := 0) .X .zero hs]
  have h00 : uncurry ![(0 : σ → MvPowerSeries σ R), 0] = 0 := by
    funext ⟨b, j⟩; fin_cases b <;> rfl
  simpa only [h00, subst_zero_of_constantCoeff_zero (F.zero_constantCoeff _),
    Pi.zero_apply, ← substAlgHom_apply hs, map_zero, substAlgHom_X,
    Xzero, ← Pi.zero_def] using F.assoc_subst .X .zero .zero i (S := R)

theorem zeroX_subst_zeroX (i : σ) : (F.zeroX i).subst F.zeroX = F.zeroX i := by
  have hs : HasSubst F.zeroX := F.hasSubst_subst_pair .zero .X
  rw [zeroX, subst_pair_subst _ (x := 0) (y := X) .zero .X hs]
  have h00 : uncurry ![(0 : σ → MvPowerSeries σ R), 0] = 0 := by
    funext ⟨b, j⟩; fin_cases b <;> rfl
  simpa only [h00, subst_zero_of_constantCoeff_zero (F.zero_constantCoeff _),
    Pi.zero_apply, ← substAlgHom_apply hs, map_zero, substAlgHom_X,
    zeroX, ← Pi.zero_def] using (F.assoc_subst .zero .zero .X i (S := R)).symm

omit [DecidableEq σ] in
/-- An idempotent family congruent to `X` modulo degree two is `X`. -/
private theorem eq_X_of_idempotent (g : σ → MvPowerSeries σ R) (hg : HasSubst g)
    (hg0 : ∀ i, constantCoeff (g i) = 0) (hlin : ∀ i, 2 ≤ (g i - X i).order)
    (hgg : ∀ i, (g i).subst g = g i) : g = X := by
  -- one factor `c x.1` for each of the `d s` occurrences of the variable `s`
  have hprod (c : σ → MvPowerSeries σ R) (d : σ →₀ ℕ) :
      d.prod (fun s k ↦ c s ^ k) = ∏ x ∈ d.support.sigma fun s ↦ Finset.range (d s), c x.1 := by
    simp [Finsupp.prod, Finset.prod_sigma]
  have h (n : ℕ) (i : σ) : (n : ℕ∞) ≤ (g i - X i).order := by
    induction n generalizing i with
    | zero => simp
    | succ n ih =>
      -- by idempotency, `g i - X i` is the difference of its substitutions of `X` and `g`
      have hsub : g i - X i = -((g i - X i).subst g - (g i - X i).subst X) := by
        rw [subst_sub hg, hgg, subst_X hg, sub_self, subst_self, id_eq, zero_sub, neg_neg]
      rw [hsub, order_neg]
      refine nat_le_order fun e he ↦ ?_
      rw [map_sub, sub_eq_zero, coeff_subst hg, coeff_subst HasSubst.X]
      refine finsum_congr fun d ↦ ?_
      obtain hd | hd : d.degree < 2 ∨ 2 ≤ d.degree := by omega
      · -- `g i - X i` has no terms of degree less than two
        simp [coeff_of_lt_order (.trans_le (mod_cast hd) (hlin i))]
      congr 1
      have hd : 2 ≤ (d.support.sigma fun s ↦ Finset.range (d s)).card := by
        simpa [Finset.card_sigma, Finsupp.degree_apply] using hd
      rw [hprod, hprod]
      refine coeff_eq_of_lt_order_sub (lt_of_lt_of_le ?_ (add_nsmul_le_order_prod_sub_prod
        (fun x _ ↦ one_le_order_iff_constCoeff_eq_zero.mpr (hg0 x.1))
        (fun x _ ↦ one_le_order_iff_constCoeff_eq_zero.mpr (constantCoeff_X x.1)) fun x _ ↦ ih x.1))
      rw [nsmul_one]
      norm_cast
      omega
  exact funext fun i ↦ sub_eq_zero.mp (order_eq_top_iff.mp (ENat.eq_top_iff_forall_ge.mpr (h · i)))

/-- `0 : σ → MvPowerSeries σ R` is a right identity: `F(X, 0) = X`. -/
@[simp]
theorem Xzero_eq_X : F.Xzero = X := by
  refine eq_X_of_idempotent F.Xzero (F.hasSubst_subst_pair .X .zero)
    F.constantCoeff_Xzero (fun j ↦ ?_) F.Xzero_subst_Xzero
  simpa using F.two_le_order_subst_sub (x := X) (y := 0) .X .zero (S := R)
    constantCoeff_X (by simp) j

/-- `0 : σ → MvPowerSeries σ R` is a left identity: `F(0, X) = X`. -/
@[simp]
theorem zeroX_eq_X : F.zeroX = X := by
  refine eq_X_of_idempotent F.zeroX (F.hasSubst_subst_pair .zero .X)
    F.constantCoeff_zeroX (fun j ↦ ?_) F.zeroX_subst_zeroX
  simpa using F.two_le_order_subst_sub (x := 0) (y := X) .zero .X (S := R)
    (by simp) constantCoeff_X j

/-- `0 : σ → MvPowerSeries τ S` is a right identity after any admissible substitution. -/
@[simp]
theorem add_zero (hx : HasSubst x) (i : σ) :
    (F.toPowerSeries i).subst (uncurry ![x, 0]) = x i := by
  have h := congrArg (subst x) (congrFun F.Xzero_eq_X i)
  rw [Xzero, subst_pair_subst _ (x := X) (y := 0) .X .zero hx] at h
  simpa only [Pi.zero_apply, ← substAlgHom_apply hx, map_zero, substAlgHom_X,
    ← Pi.zero_def] using h

/-- `0 : σ → MvPowerSeries τ S` is a left identity after any admissible substitution. -/
@[simp]
theorem zero_add (hx : HasSubst x) (i : σ) :
    (F.toPowerSeries i).subst (uncurry ![0, x]) = x i := by
  have h := congrArg (subst x) (congrFun F.zeroX_eq_X i)
  rw [zeroX, subst_pair_subst _ (x := 0) (y := X) .zero .X hx] at h
  simpa only [Pi.zero_apply, ← substAlgHom_apply hx, map_zero, substAlgHom_X,
    ← Pi.zero_def] using h

end Basic

/-- The additive formal group law `F(i)(X, Y) = Xᵢ + Yᵢ`. -/
def additive (σ : Type*) (R : Type*) [CommRing R] [DecidableEq σ] : MvFormalGroup σ R where
  toPowerSeries i := X (0, i) + X (1, i)
  zero_constantCoeff _ := by simp
  lin_coeff_X i j := by simp [coeff_index_single_X, Matrix.one_apply]
  lin_coeff_Y i j := by simp [coeff_index_single_X, Matrix.one_apply]
  coeff_zero := ((HasSubst.X.curry 0).add (HasSubst.X.curry 1)).coeff_zero
  assoc i := by
    have hv (b : Fin 3) := HasSubst.X.curry (R := R) (σ := σ) b
    simp only [subst_X_add_X (hv _) (hv _)]
    rw [subst_X_add_X _ (hv 2), subst_X_add_X (hv 0), add_assoc]
    · exact (hv 1).add (hv 2)
    · exact (hv 0).add (hv 1)

instance : (additive σ R).IsComm where
  comm i := by
    change X (0, i) + X (1, i) = (X (0, i) + X (1, i) : MvPowerSeries (Fin 2 × σ) R).subst _
    rw [subst_X_add_X (HasSubst.X.curry 1) (HasSubst.X.curry 0)]
    simp [add_comm]

end MvFormalGroup
