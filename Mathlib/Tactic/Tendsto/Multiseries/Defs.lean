/-
Copyright (c) 2024 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Data.Seq.Seq
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Main definitions

* `PreMS basis` is the type of lazy formal multiseries, where `basis` is the list of basis
functions. It is defined recursively as `PreMS [] = ℝ` (constants), and
`PreMS (b₁ :: tl) = Seq (ℝ × PreMS tl)`. This is lazy possibly infinite list of pairs, where each
pair `(exp, coef)` represents the monomial `b₁^exp * coef`. The type is isomorphic to the type
of trees of finite fixed depth with possibly infinite branching and `ℝ`-valued labels in vertexes.
* `WellOrdered ms` is the predicate meaning that at each level of `ms` as a nested tree all
exponents are Pairwise by TODO (убывание).
* `Approximates ms f` is the predicate meaning that the multiseries `ms` can be used to obtain
an asymptotical approximations of the real function `f`.
For details see the docs for `Approximates`.

# Definition used inside the theory
* `leadingExp ms` is the value of leading exponent of `ms`. Is `ms = []` then it is `⊥`.


-/


namespace TendstoTactic

open Filter Asymptotics Stream' Seq

abbrev Basis := List (ℝ → ℝ)

/-- TODO -/
abbrev PreMS (basis : Basis) : Type :=
  match basis with
  | [] => ℝ
  | .cons _ tl => Seq (ℝ × PreMS tl)

namespace PreMS

universe v in
/-- Recursion principle for multiseries with non-empty basis. It is equivalent to
`Stream'.Seq.recOn` but provides some convenience. For example one can write
`cases' ms with exp coef tl` while cannot `cases' ms with (exp, coef) tl` (`cases` tactic does
not support argument deconstruction). -/
@[cases_eliminator]
def recOn {basis_hd} {basis_tl} {motive : PreMS (basis_hd :: basis_tl) → Sort v}
    (ms : PreMS (basis_hd :: basis_tl)) (nil : motive nil)
    (cons : ∀ exp coef (tl : PreMS (basis_hd :: basis_tl)), motive (cons (exp, coef) tl)) :
    motive ms := by
  cases' ms using Stream'.Seq.recOn with hd tl
  · exact nil
  · exact cons hd.1 hd.2 tl

instance (basis : Basis) : Inhabited (PreMS basis) where
  default := match basis with
  | [] => default
  | .cons _ _ => default

section leadingExp

variable {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}

/-- The leading exponent of multiseries with non-empty basis. For `ms = []` it is `⊥`. -/
def leadingExp (ms : PreMS (basis_hd :: basis_tl)) : WithBot ℝ :=
  match head ms with
  | none => ⊥
  | some (exp, _) => exp

@[simp]
theorem leadingExp_nil : @leadingExp basis_hd basis_tl .nil = ⊥ := by
  simp [leadingExp]

@[simp]
theorem leadingExp_cons {hd : ℝ × PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} :
    @leadingExp basis_hd basis_tl (Seq.cons hd tl) = hd.1 := by
  simp [leadingExp]

theorem leadingExp_of_head :
    ms.leadingExp = ms.head.elim ⊥ (fun (exp, _) ↦ exp) := by
  cases ms <;> simp

/-- If `ms.leadingExp = ⊥` then `ms = []`. -/
theorem leadingExp_eq_bot :
    ms = .nil ↔ ms.leadingExp = ⊥ := by
  cases ms <;> simp

/-- If `ms.leadingExp` is real number `exp` then `ms = cons (exp, coef) tl` for some `coef` and
`tl`. -/
theorem leadingExp_eq_coe {exp : ℝ} (h : ms.leadingExp = ↑exp) :
    ∃ (a : PreMS basis_tl × PreMS (basis_hd :: basis_tl)), ms = .cons (exp, a.1) a.2 := by
  cases' ms with exp' coef tl
  · simp at h
  · simp at h
    subst h
    use (coef, tl)

end leadingExp

section WellOrdered

/-- Auxilary instance for order on pairs `(exp, coef)` used below to define `WellOrdered` in terms
of `Stream'.Seq.Pairwise`. `(exp₁, coef₁) ≤ (exp₂, coef₂)` iff `exp₁ ≤ exp₂`. -/
scoped instance {basis} : Preorder (ℝ × PreMS basis) where
  le := fun x y ↦ x.1 ≤ y.1
  le_refl := by simp
  le_trans := by
    intro x y z hxy hyz
    simp at *
    trans y.1 <;> assumption

-- TODO: can be simpler??
private theorem lt_iff_lt {basis} {exp1 exp2 : ℝ} {coef1 coef2 : PreMS basis} :
    (exp1, coef1) < (exp2, coef2) ↔ exp1 < exp2 := by
  constructor
  · intro h
    rw [lt_iff_le_not_le] at h ⊢
    exact h
  · intro h
    rw [lt_iff_le_not_le] at h ⊢
    exact h

/-- Multiseries `ms` is `WellOrdered` when at each its level exponents are Pairwise by TODO. -/
inductive WellOrdered : {basis : Basis} → (PreMS basis) → Prop
| const (ms : PreMS []) : WellOrdered ms
| seq {hd} {tl} (ms : PreMS (hd :: tl))
    (h_coef : ∀ i x, ms.get? i = .some x → x.2.WellOrdered)
    (h_Pairwise : Seq.Pairwise (· > ·) ms) : ms.WellOrdered

variable {basis_hd : ℝ → ℝ} {basis_tl : Basis}

/-- `[]` is `WellOrdered`. -/
theorem WellOrdered.nil : @WellOrdered (basis_hd :: basis_tl) .nil := by
  constructor
  · intro i x
    intro h
    simp at h
  · unfold Seq.Pairwise
    intro i j x y _ h
    simp at h

/-- `[(exp, coef)]` is `WellOrdered` when `coef` is `WellOrdered`. -/
theorem WellOrdered.cons_nil {exp : ℝ} {coef : PreMS basis_tl} (h_coef : coef.WellOrdered) :
    @WellOrdered (basis_hd :: basis_tl) (.cons (exp, coef) .nil) := by
  constructor
  · intro i x h
    cases i with
    | zero =>
      simp at h
      rw [← h]
      simpa
    | succ j =>
      simp at h
  · unfold Seq.Pairwise
    intro i j x y h_lt _ hj
    cases j with
    | zero => simp at h_lt
    | succ k => simp at hj

/-- `cons (exp, coef) tl` is `WellOrdered` when `coef` and `tl` are `WellOrdered` and leading
exponent of `tl` is less than `exp`. -/
theorem WellOrdered.cons {exp : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h_coef : coef.WellOrdered)
    (h_comp : tl.leadingExp < exp)
    (h_tl : tl.WellOrdered) :
    @WellOrdered (basis_hd :: basis_tl) (.cons (exp, coef) tl) := by
  cases h_tl with | seq _ h_tl_coef h_tl_tl =>
  constructor
  · intro i x h
    cases i with
    | zero =>
      simp at h
      rw [← h]
      simpa
    | succ j =>
      simp at h
      simp at h_tl_coef
      solve_by_elim
  · cases tl
    · exact Pairwise_cons_nil
    apply Seq.Pairwise.cons_cons_of_trans _ h_tl_tl
    simpa [lt_iff_lt] using h_comp

/-- The fact `WellOrdered (cons (exp, coef) tl)` implies that `coef` and `tl` are `WellOrdered`, and
leading exponent of `tl` is less than `exp`. -/
theorem WellOrdered_cons {exp : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : @WellOrdered (basis_hd :: basis_tl) (.cons (exp, coef) tl)) :
    coef.WellOrdered ∧ tl.leadingExp < exp ∧ tl.WellOrdered := by
  cases h with | seq _ h_coef h_Pairwise =>
  constructor
  · specialize h_coef 0 (exp, coef)
    simpa using h_coef
  cases' tl with tl_exp tl_coef tl_tl
  · simp [WellOrdered.nil]
  apply Pairwise.cons_cons_elim_of_trans at h_Pairwise
  constructor
  · simp [lt_iff_lt] at h_Pairwise
    simp
    exact h_Pairwise.left
  · constructor
    · intro i x hx
      specialize h_coef (i + 1) x
      simp at h_coef hx
      exact h_coef hx
    · exact h_Pairwise.right

-- TODO : ∨ -> → at h_step
/-- Coinduction principle for proving `WellOrdered`. For some predicate `motive` on multiseries,
if `motive ms` (base case) and the predicate "survives" destruction of its argument, then `ms` is
`WellOrdered`. Here "survive" means that if `x = cons (exp, coef) tl` than `motive x` must imply
`coef.wellOrdered`, `tl.leadingExp < exp` and `motive tl`. -/
theorem WellOrdered.coind {ms : PreMS (basis_hd :: basis_tl)}
    (motive : (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (h_base : motive ms)
    (h_step : ∀ ms, motive ms →
      (ms = .nil) ∨
      (
        ∃ exp coef, ∃ (tl : PreMS (basis_hd :: basis_tl)), ms = .cons (exp, coef) tl ∧
        coef.WellOrdered ∧
        tl.leadingExp < exp ∧
        motive tl
      )
    )
    : ms.WellOrdered := by
  have h_all : ∀ n, motive (ms.drop n) := by
    intro n
    induction n with
    | zero => simpa
    | succ m ih =>
      simp only [Seq.drop]
      specialize h_step _ ih
      cases h_step with
      | inl h_ms_eq =>
        rw [h_ms_eq] at ih ⊢
        simpa
      | inr h =>
        obtain ⟨exp, coef, tl, h_ms_eq, _, _, h_tl⟩ := h
        rw [h_ms_eq]
        simp
        exact h_tl
  constructor
  · intro i x hx
    simp [← head_dropn] at hx
    specialize h_step _ (h_all i)
    cases h_step with
    | inl h_ms_eq =>
      rw [h_ms_eq] at hx
      simp at hx
    | inr h =>
      obtain ⟨exp, coef, tl, h_ms_eq, h_coef, h_comp, h_tl⟩ := h
      rw [h_ms_eq] at hx
      simp at hx
      simpa [← hx]
  · apply Seq.Pairwise.coind_trans motive h_base
    intro hd tl ih
    specialize h_step _ ih
    simp [Seq.cons_eq_cons] at h_step
    obtain ⟨exp, coef, tl, ⟨h_hd_eq, h_tl_eq⟩, _, h_comp, h_tl⟩ := h_step
    subst h_hd_eq h_tl_eq
    constructor
    · cases tl
      · simp
      simp at h_comp ⊢
      rwa [lt_iff_lt]
    · exact h_tl

end WellOrdered

section Approximates

section Majorated

/-- `majorated f g exp` for real functions `f` and `g` means that for any `exp' < exp`,
`f =o[atTop] g^exp'`. -/
def majorated (f basis_hd : ℝ → ℝ) (exp : ℝ) : Prop :=
  ∀ exp', exp < exp' → f =o[atTop] (fun t ↦ (basis_hd t)^exp')

/-- One can change the argument of `majorated` with the function that eventually equals to it. -/
theorem majorated_of_EventuallyEq {f g basis_hd : ℝ → ℝ} {exp : ℝ} (h_eq : g =ᶠ[atTop] f)
    (h : majorated f basis_hd exp) : majorated g basis_hd exp := by
  simp only [majorated] at *
  intro exp' h_exp
  specialize h exp' h_exp
  exact EventuallyEq.trans_isLittleO h_eq h

-- TODO: to upstream?
/-- For any function `f`, `f^exp` is majorated with `f` with exponent `exp`. -/
theorem majorated_self {f : ℝ → ℝ} {exp : ℝ}
    (h : Tendsto f atTop atTop) :
    majorated (fun t ↦ (f t)^exp) f exp := by
  simp only [majorated]
  intro exp' h_exp
  apply (isLittleO_iff_tendsto' _).mpr
  · have : (fun t ↦ f t ^ exp / f t ^ exp') =ᶠ[atTop] fun t ↦ (f t)^(exp - exp') := by
      apply Eventually.mono <| Tendsto.eventually_gt_atTop h 0
      intro t h
      simp only
      rw [← Real.rpow_sub h]
    apply Tendsto.congr' this.symm
    conv =>
      arg 1
      rw [show (fun t ↦ f t ^ (exp - exp')) = ((fun t ↦ t^(-(exp' - exp))) ∘ f) by ext; simp]
    apply Tendsto.comp _ h
    apply tendsto_rpow_neg_atTop
    linarith
  · apply Eventually.mono <| Tendsto.eventually_gt_atTop h 0
    intro t h1 h2
    absurd h2
    exact (Real.rpow_pos_of_pos h1 _).ne.symm

/-- If one can majorate `f` with `exp1`, then it can be majorated with any `exp2 > exp1`. -/
theorem majorated_of_lt {f basis_hd : ℝ → ℝ} {exp1 exp2 : ℝ}
    (h_lt : exp1 < exp2) (h : majorated f basis_hd exp1) :
    majorated f basis_hd exp2 := by
  simp [majorated] at *
  intro exp' h_exp
  apply h _ (by linarith)

/-- If `f` is majorated with negative exponent, then it tends to zero. -/
theorem majorated_tendsto_zero_of_neg {f basis_hd : ℝ → ℝ} {exp : ℝ}
    (h_lt : exp < 0) (h : majorated f basis_hd exp) :
    Tendsto f atTop (nhds 0) := by
  simp [majorated] at h
  specialize h 0 (by linarith)
  simpa using h

/-- Constants can be majorated with `exp = 0`. -/
theorem const_majorated {basis_hd : ℝ → ℝ} (h_tendsto : Tendsto basis_hd atTop atTop)
    {c : ℝ}
    : majorated (fun _ ↦ c) basis_hd 0 := by
  intro exp h_exp
  apply Asymptotics.isLittleO_const_left.mpr
  right
  apply Tendsto.comp tendsto_norm_atTop_atTop
  apply Tendsto.comp (tendsto_rpow_atTop h_exp)
  exact h_tendsto

/-- Zero can be majorated with any exponent. -/
theorem zero_majorated {basis_hd : ℝ → ℝ} {exp : ℝ}
    : majorated (fun _ ↦ 0) basis_hd exp := by
  intro exp h_exp
  apply Asymptotics.isLittleO_zero

/-- `f * c` can be majorated with the same exponent as `f` for any constant `c`. -/
theorem mul_const_majorated {f basis_hd : ℝ → ℝ} {exp : ℝ} (h : majorated f basis_hd exp)
    {c : ℝ}
    : majorated (fun t ↦ (f t) * c) basis_hd exp := by
  intro exp h_exp
  simp_rw [mul_comm]
  apply IsLittleO.const_mul_left (h exp h_exp)

/-- Sum of two function, that can be majorated with exponents `f_exp` and `g_exp`, can be
majorated with exponent `f_exp ⊔ g_exp`. -/
theorem add_majorated {f g basis_hd : ℝ → ℝ} {f_exp g_exp : ℝ} (hf : majorated f basis_hd f_exp)
    (hg : majorated g basis_hd g_exp)
    : majorated (f + g) basis_hd (f_exp ⊔ g_exp) := by
  simp only [majorated] at *
  intro exp h_exp
  simp at h_exp
  apply IsLittleO.add
  · exact hf _ h_exp.left
  · exact hg _ h_exp.right

/-- Product of two function, that can be majorated with exponents `f_exp` and `g_exp`, can be
majorated with exponent `f_exp + g_exp`. -/
theorem mul_majorated {f g basis_hd : ℝ → ℝ} {f_exp g_exp : ℝ} (hf : majorated f basis_hd f_exp)
    (hg : majorated g basis_hd g_exp) (h_pos : ∀ᶠ t in atTop, 0 < basis_hd t)
    : majorated (f * g) basis_hd (f_exp + g_exp) := by
  simp only [majorated] at *
  intro exp h_exp
  let ε := (exp - f_exp - g_exp) / 2
  specialize hf (f_exp + ε) (by dsimp [ε]; linarith)
  specialize hg (g_exp + ε) (by dsimp [ε]; linarith)
  apply IsLittleO.trans_eventuallyEq
    (g₁ := fun t ↦ basis_hd t ^ (f_exp + ε) * basis_hd t ^ (g_exp + ε))
  · exact IsLittleO.mul hf hg
  · simp only [EventuallyEq]
    apply Eventually.mono h_pos
    intro t hx
    conv =>
      rhs
      rw [show exp = (f_exp + ε) + (g_exp + ε) by dsimp [ε]; ring_nf]
      rw [Real.rpow_add hx]

end Majorated

section PartialSums

noncomputable def partialSumsFrom (Cs : Seq (ℝ → ℝ)) (exps : Seq ℝ) (basis_fun : ℝ → ℝ)
    (init : ℝ → ℝ) : Seq (ℝ → ℝ) :=
  Cs.zip exps |>.fold init fun acc (fC, exp) =>
    fun t ↦ acc t + (basis_fun t)^exp * (fC t)

noncomputable def partialSums (Cs : Seq (ℝ → ℝ)) (exps : Seq ℝ) (basis_fun : ℝ → ℝ) :
    Seq (ℝ → ℝ) :=
  partialSumsFrom Cs exps basis_fun 0

theorem partialSumsFrom_nil {exps : Seq ℝ} {basis_fun : ℝ → ℝ} {init : ℝ → ℝ} :
    partialSumsFrom .nil exps basis_fun init = .cons init .nil := by
  simp [partialSumsFrom]

theorem partialSumsFrom_cons {Cs_hd : ℝ → ℝ} {Cs_tl : Seq (ℝ → ℝ)} {exps_hd : ℝ}
    {exps_tl : Seq ℝ} {basis_fun : ℝ → ℝ} {init : ℝ → ℝ} :
    partialSumsFrom (.cons Cs_hd Cs_tl) (.cons exps_hd exps_tl) basis_fun init =
    (.cons init <| partialSumsFrom Cs_tl exps_tl basis_fun
      (fun t ↦ init t + (basis_fun t)^exps_hd * (Cs_hd t))) := by
  simp [partialSumsFrom]

theorem partialSumsFrom_eq_map {Cs : Seq (ℝ → ℝ)} {exps : Seq ℝ} {basis_fun : ℝ → ℝ}
    {init : ℝ → ℝ} (h : Cs.AtLeastAsLongAs exps) :
    partialSumsFrom Cs exps basis_fun init =
      (partialSums Cs exps basis_fun).map fun fG => init + fG := by

  let motive : Seq (ℝ → ℝ) → Seq (ℝ → ℝ) → Prop := fun x y =>
    ∃ Cs exps init fD,
      Cs.AtLeastAsLongAs exps ∧
      (
        (x = partialSumsFrom Cs exps basis_fun (fD + init)) ∧
        (y = (partialSumsFrom Cs exps basis_fun init).map fun fG => fD + fG)
      ) ∨
      (x = .nil ∧ y = .nil)
  apply eq_of_bisim' motive
  · simp [motive]
    use Cs, exps, 0, init
    left
    constructor
    · assumption
    constructor
    · simp
    · simp [partialSums]
  · intro x y ih
    simp [motive] at ih
    obtain ⟨Cs', exps', init', fD, ih⟩ := ih
    cases' ih with ih ih
    · left
      obtain ⟨h_alal, h_x_eq, h_y_eq⟩ := ih
      cases' exps' with exps_hd exps_tl
      · simp [partialSums, partialSumsFrom] at h_x_eq h_y_eq
        use fD + init', .nil
        constructor
        constructor
        · assumption
        constructor
        · assumption
        simp [motive]
      · obtain ⟨Cs_hd, Cs_tl, h_Cs⟩ := Seq.AtLeastAsLongAs.cons_elim h_alal
        subst h_Cs
        simp [partialSums, partialSumsFrom_cons] at h_x_eq h_y_eq
        use fD + init',
          partialSumsFrom Cs_tl exps_tl basis_fun fun t ↦ fD t + init' t +
            basis_fun t ^ exps_hd * Cs_hd t,
          Seq.map (fun fG ↦ fD + fG) (partialSumsFrom Cs_tl exps_tl basis_fun fun t ↦ init' t +
            basis_fun t ^ exps_hd * Cs_hd t)
        constructor
        · assumption
        constructor
        · assumption
        simp [motive]
        simp at h_alal
        use Cs_tl, exps_tl, fun t ↦ init' t + basis_fun t ^ exps_hd * Cs_hd t, fD
        left
        constructor
        · assumption
        constructor
        · congr
          eta_expand
          simp
          ext
          ring_nf
        rfl
    · right
      exact ih

end PartialSums

def Approximates {basis : Basis} (ms : PreMS basis) (f : ℝ → ℝ)   : Prop :=
  match basis with
  | [] => f =ᶠ[atTop] fun _ ↦ ms
  | List.cons basis_hd _ =>
    ∃ Cs : Seq (ℝ → ℝ),
    Cs.AtLeastAsLongAs ms ∧
    ((Cs.zip ms).All fun (fC, (_, coef)) => coef.Approximates fC) ∧
    (
      let exps := ms.map fun t => t.1;
      let exps' : Seq (Option ℝ) := (exps.map .some).append (.cons .none .nil);
      (partialSums Cs exps basis_hd).zip exps' |>.All fun (ps, exp?) =>
        match exp? with
        | .some exp =>
          majorated (fun t ↦ f t - ps t) basis_hd exp
        | .none => (fun t ↦ f t - ps t) =ᶠ[atTop] 0
    )

variable {f basis_hd : ℝ → ℝ} {basis_tl : Basis}

/-- `[]` approximates zero function. -/
theorem Approximates.nil (h : f =ᶠ[atTop] 0) :
    @Approximates (basis_hd :: basis_tl) .nil f := by
  simp [Approximates]
  use .nil
  simpa [partialSums, partialSumsFrom]

/-- `cons (exp, coef) tl` approximates `f` when `f` can be majorated with exponent `exp`, and
there exists some function `fC` such that `coef` approximates `fC` and `tl` approximates
`f - fC * basis_hd ^ exp`. -/
theorem Approximates.cons {exp : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (fC : ℝ → ℝ) (h_coef : coef.Approximates fC)
    (h_maj : majorated f basis_hd exp)
    (h_tl : tl.Approximates (fun t ↦ f t - (basis_hd t)^exp * (fC t))) :
    @Approximates (basis_hd :: basis_tl) (.cons (exp, coef) tl) f := by
  simp [Approximates] at h_tl ⊢
  obtain ⟨Cs, h_tl_alal, h_tl_coef, h_tl_maj⟩ := h_tl
  use .cons fC Cs
  constructor
  · simpa
  constructor
  · simp
    constructor
    · exact h_coef
    · exact h_tl_coef
  · unfold partialSums at h_tl_maj ⊢
    simp [partialSumsFrom_cons]
    constructor
    · exact h_maj
    -- copypaste from `Approximates_cons`
    · rw [partialSumsFrom_eq_map (Seq.AtLeastAsLongAs_map h_tl_alal)]
      rw [Seq.zip_map_left]
      apply Seq.map_All_iff.mpr
      apply Seq.All_mp _ h_tl_maj
      intro (fC', exp?)
      simp
      intro h
      ring_nf at h
      ring_nf
      exact h

/-- Auxilary type used in `Approximates.coind` proof. -/
private structure Approximates.coind.AuxT {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (motive : (f : ℝ → ℝ) → (ms : PreMS (basis_hd :: basis_tl)) → Prop) where
  val : PreMS (basis_hd :: basis_tl)
  f : ℝ → ℝ
  h : motive f val

theorem Approximates.coind {ms : PreMS (basis_hd :: basis_tl)}
    (motive : (f : ℝ → ℝ) → (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (h_base : motive f ms)
    (h_step : ∀ f ms, motive f ms →
      (ms = .nil ∧ f =ᶠ[atTop] 0) ∨
      (
        ∃ exp coef tl fC, ms = .cons (exp, coef) tl ∧
        (coef.Approximates fC) ∧
        majorated f basis_hd exp ∧
        (motive (fun t ↦ f t - (basis_hd t)^exp * (fC t)) tl)
      )
    )
    : ms.Approximates f := by
  simp [Approximates]
  let T := Approximates.coind.AuxT motive
  let g : T → Option ((ℝ → ℝ) × T) := fun ⟨val, f, h⟩ =>
    match h_val : destruct val with
    | none => .none
    | some ((exp, coef), tl) =>
        have spec : ∃ fC,
            coef.Approximates fC ∧
            majorated f basis_hd exp ∧
            motive (fun t ↦ f t - basis_hd t ^ exp * fC t) tl := by
          apply destruct_eq_cons at h_val
          specialize h_step _ _ h
          simp [h_val, Seq.cons_eq_cons] at h_step
          obtain ⟨exp_1, coef_1, tl_1, ⟨⟨h_exp, h_coef⟩, h_tl⟩, h_step⟩ := h_step
          subst h_exp
          subst h_coef
          subst h_tl
          exact h_step
        let fC := spec.choose
        .some (fC, ⟨tl, fun t ↦ f t - (basis_hd t)^exp * (fC t), spec.choose_spec.right.right⟩)
  let Cs : Seq (ℝ → ℝ) := Seq.corec g ⟨ms, f, h_base⟩
  use Cs
  constructor
  · let motive' : Seq (ℝ → ℝ) → Seq (ℝ × PreMS basis_tl) → Prop := fun Cs ms =>
      ∃ f h, Cs = (Seq.corec g ⟨ms, f, h⟩)
    apply Seq.AtLeastAsLongAs.coind motive'
    · simp only [motive']
      use f, h_base
    · intro Cs ms ih (exp, coef) tl h_ms_eq
      simp only [motive'] at ih
      obtain ⟨f, h, h_Cs_eq⟩ := ih
      subst h_ms_eq
      rw [Seq.corec_cons] at h_Cs_eq
      pick_goal 2
      · simp [g]
        constructor
      use ?_, ?_
      constructor
      · exact h_Cs_eq
      simp only [motive']
      generalize_proofs p1 p2
      use fun t ↦ f t - basis_hd t ^ exp * p1.choose t, p2
      simp
  · constructor
    · let motive' : Seq ((ℝ → ℝ) × ℝ × PreMS basis_tl) → Prop := fun li =>
        ∃ (ms : PreMS (basis_hd :: basis_tl)), ∃ f h,
          li = (Seq.corec g ⟨ms, f, h⟩).zip ms
      apply Seq.All.coind motive'
      · simp only [motive']
        use ms, f, h_base
      · intro (fC, (exp, coef)) tl ih
        simp only
        simp only [motive'] at ih
        obtain ⟨ms, f, h, h_eq⟩ := ih
        specialize h_step _ _ h
        cases' ms with ms_exp ms_coef ms_tl
        · simp at h_eq
        · rw [Seq.corec_cons] at h_eq
          pick_goal 2
          · simp [g]
            constructor
          simp [Seq.cons_eq_cons] at h_eq
          obtain ⟨⟨h1, ⟨h2, h3⟩⟩, h_eq⟩ := h_eq
          constructor
          · subst h1
            subst h2
            subst h3
            generalize_proofs p
            exact p.choose_spec.left
          · simp only [motive']
            use ?_, ?_, ?_
    · simp [partialSums]
      let motive' : Seq ((ℝ → ℝ) × Option ℝ) → Prop := fun li =>
        li = .nil ∨ ∃ (ms : Seq (ℝ × PreMS basis_tl)), ∃ fG h init,
          li = ((partialSumsFrom (Seq.corec g ⟨ms, fG, h⟩)
            (Seq.map (fun x ↦ x.1) ms) basis_hd init).zip
              ((Seq.map some (Seq.map (fun x ↦ x.1) ms)).append (Seq.cons none Seq.nil))) ∧
      fG + init =ᶠ[atTop] f
      apply Seq.All.coind motive'
      · simp only [motive']
        right
        use ms, f, h_base, 0
        constructor
        · rfl
        simp
      · intro (f', exp?) li_tl ih
        simp only [motive'] at ih
        cases ih with
        | inl ih => simp at ih
        | inr ih =>
        obtain ⟨(ms : PreMS (basis_hd :: basis_tl)), fG, h_mot, init, h_eq, hF_eq⟩ := ih
        · simp
          cases' ms with exp coef tl
          · rw [Seq.corec_nil] at h_eq
            pick_goal 2
            · simp [g]
            simp [Seq.cons_eq_cons, partialSumsFrom_nil] at h_eq
            obtain ⟨⟨h1, h2⟩, h3⟩ := h_eq
            subst h1 h2 h3
            simp
            specialize h_step _ _ h_mot
            cases h_step with
            | inr h_step => simp at h_step
            | inl h_step =>
              simp at h_step
              constructor
              · apply eventuallyEq_iff_sub.mp
                trans
                · exact hF_eq.symm
                conv => rhs; ext t; rw [← zero_add (f' t)]
                apply EventuallyEq.add h_step
                rfl
              · simp [motive']
          · rw [Seq.corec_cons] at h_eq
            swap
            · simp [g]
              rfl
            simp [Seq.cons_eq_cons, partialSumsFrom_cons] at h_eq
            obtain ⟨⟨h1, h2⟩, h3⟩ := h_eq
            subst h1 h2 h3
            simp
            constructor
            · intro exp' h_exp
              apply EventuallyEq.trans_isLittleO (f₂ := fG)
              · apply eventuallyEq_iff_sub.mpr
                replace hF_eq := eventuallyEq_iff_sub.mp hF_eq.symm
                trans f - (fG + f')
                · apply eventuallyEq_iff_sub.mpr
                  eta_expand
                  simp
                  ring_nf!
                  rfl
                · exact hF_eq
              · generalize_proofs h at h_eq
                obtain ⟨_, _, h_maj, _⟩ := h
                apply h_maj _ h_exp
            · simp [motive']
              right
              generalize_proofs h1 h2
              use tl, fun t ↦ fG t - basis_hd t ^ exp * h1.choose t,
                h2, fun t ↦ f' t + basis_hd t ^ exp * h1.choose t
              constructor
              · rfl
              apply eventuallyEq_iff_sub.mpr
              eta_expand
              simp
              ring_nf!
              conv =>
                lhs; ext t; rw [show fG t + (f' t - f t) = (fG t + f' t) - f t by ring]
              apply eventuallyEq_iff_sub.mp
              exact hF_eq

/-- If `[]` approximates `f`, then `f = 0` eventually. -/
theorem Approximates_nil (h : @Approximates (basis_hd :: basis_tl) Seq.nil f) :
    f =ᶠ[atTop] 0 := by
  unfold Approximates at h
  obtain ⟨Cs, _, _, h_maj⟩ := h
  simp at h_maj
  apply Seq.All_get at h_maj
  simp [partialSums, partialSumsFrom] at h_maj
  -- unfold Seq.All at h_maj
  specialize h_maj (n := 0) 0 none
  simpa using h_maj

/-- If `cons (exp, coef) tl` approximates `f`, then `f` can be majorated with exponent `exp`, and
there exists function `fC` such that `coef` approximates `fC` and `tl` approximates
`f - fC * basis_hd ^ exp`. -/
theorem Approximates_cons {exp : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : @Approximates (basis_hd :: basis_tl) (.cons (exp, coef) tl) f) :
    ∃ fC,
      coef.Approximates fC ∧
      majorated f basis_hd exp ∧
      tl.Approximates (fun t ↦ f t - (basis_hd t)^exp * (fC t)) := by
  unfold Approximates at h
  obtain ⟨Cs, h_alal, h_coef, h_maj⟩ := h
  obtain ⟨fC, Cs_tl, h_alal⟩ := Seq.AtLeastAsLongAs.cons_elim h_alal
  subst h_alal
  use fC
  simp at h_coef
  constructor
  · exact h_coef.left
  · constructor
    · simp [partialSums, partialSumsFrom] at h_maj
      exact h_maj.left
    · simp at h_alal
      unfold Approximates
      use Cs_tl
      constructor
      · assumption
      · constructor
        · exact h_coef.right
        · simp [partialSums, partialSumsFrom_cons] at h_maj
          apply And.right at h_maj
          rw [partialSumsFrom_eq_map (Seq.AtLeastAsLongAs_map h_alal)] at h_maj
          rw [Seq.zip_map_left] at h_maj
          apply Seq.All_mp _ (Seq.map_All_iff.mp h_maj)
          intro (fC', exp?)
          simp
          intro h
          ring_nf at h
          ring_nf
          exact h

/-- One can replace `f` in `Approximates` with the funcion that eventually equals `f`. -/
theorem Approximates_of_EventuallyEq {basis : Basis} {ms : PreMS basis} {f f' : ℝ → ℝ}
     (h_equiv : f =ᶠ[atTop] f') (h_approx : ms.Approximates f) :
    ms.Approximates f' :=
  match basis with
  | [] => by
    simp [Approximates] at h_approx
    exact EventuallyEq.trans h_equiv.symm h_approx
  | List.cons basis_hd basis_tl => by
    let motive : (f : ℝ → ℝ) → (ms : PreMS (basis_hd :: basis_tl)) → Prop :=
      fun f' ms =>
        ∃ f, f =ᶠ[atTop] f' ∧ ms.Approximates f
    apply Approximates.coind motive
    · simp only [motive]
      use f
    · intro f' ms ih
      cases' ms with exp coef tl
      · left
        simp [motive] at ih
        obtain ⟨f, h_equiv, hF⟩ := ih
        apply Approximates_nil at hF
        constructor
        · rfl
        · exact EventuallyEq.trans h_equiv.symm hF
      · right
        use exp, coef, tl
        simp
        simp [motive] at ih
        obtain ⟨f, h_equiv, hF⟩ := ih
        obtain ⟨fC, h_coef, h_maj, h_tl⟩ := Approximates_cons hF
        use fC
        constructor
        · exact h_coef
        constructor
        · intro exp' h
          apply EventuallyEq.trans_isLittleO h_equiv.symm
          apply h_maj _ h
        · simp [motive]
          use fun t ↦ f t - basis_hd t ^ exp * (fC t)
          constructor
          · apply EventuallyEq.sub h_equiv
            apply EventuallyEq.rfl
          · exact h_tl

end Approximates

end PreMS

end TendstoTactic
