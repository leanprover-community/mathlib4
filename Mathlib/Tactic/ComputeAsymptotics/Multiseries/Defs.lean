/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Seq.Basic

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


namespace ComputeAsymptotics

open Filter Asymptotics Topology Stream' Seq

/-- List of functions used to construct monomials in multiseries. -/
abbrev Basis := List (ℝ → ℝ)

/-- TODO -/
def PreMS (basis : Basis) : Type :=
  match basis with
  | [] => ℝ
  | .cons _ tl => Seq (ℝ × PreMS tl)

namespace PreMS

section Seq

open Stream'.Seq

abbrev toReal (ms : PreMS []) : ℝ := ms

abbrev toSeq {basis_hd basis_tl} (ms : PreMS (basis_hd :: basis_tl)) :
    Stream'.Seq (ℝ × PreMS basis_tl) :=
  ms

def nil {basis_hd basis_tl} : PreMS (basis_hd :: basis_tl) := Seq.nil

def cons {basis_hd basis_tl} (exp : ℝ) (coef : PreMS basis_tl) (tl : PreMS (basis_hd :: basis_tl)) :
    PreMS (basis_hd :: basis_tl) :=
  Seq.cons (exp, coef) tl

/-- Recursion principle for multiseries with non-empty basis. It is equivalent to
`Stream'.Seq.recOn` but provides some convenience. For example one can write
`cases' ms with exp coef tl` while cannot `cases' ms with (exp, coef) tl` (`cases` tactic does
not support argument deconstruction). -/
@[cases_eliminator]
def recOn {basis_hd} {basis_tl} {motive : PreMS (basis_hd :: basis_tl) → Sort*}
    (ms : PreMS (basis_hd :: basis_tl)) (nil : motive nil)
    (cons : ∀ exp coef (tl : PreMS (basis_hd :: basis_tl)), motive (cons exp coef tl)) :
    motive ms := by
  cases ms using Stream'.Seq.recOn with
  | nil => exact nil
  | cons hd tl => exact cons hd.1 hd.2 tl

def corec {β : Type*} {basis_hd} {basis_tl} (f : β → Option (ℝ × PreMS basis_tl × β)) (b : β) :
    PreMS (basis_hd :: basis_tl) :=
  Stream'.Seq.corec (fun a => (f a).map (fun (exp, coef, next) => ((exp, coef), next))) b

def destruct {basis_hd basis_tl} (ms : PreMS (basis_hd :: basis_tl)) :
    Option (ℝ × PreMS basis_tl × PreMS (basis_hd :: basis_tl)) :=
  (Seq.destruct ms).map (fun ((exp, coef), tl) => (exp, coef, tl))

def head {basis_hd basis_tl} (ms : PreMS (basis_hd :: basis_tl)) : Option (ℝ × PreMS basis_tl) :=
  Seq.head ms

def map {basis_hd basis_tl basis_hd' basis_tl'} (f : ℝ → PreMS basis_tl → ℝ)
    (g : ℝ → PreMS basis_tl → PreMS basis_tl')
    (ms : PreMS (basis_hd :: basis_tl)) :
    PreMS (basis_hd' :: basis_tl') :=
  Seq.map (fun (exp, coef) ↦ (f exp coef, g exp coef)) ms

instance (basis : Basis) : Inhabited (PreMS basis) where
  default := match basis with
  | [] => (default : ℝ)
  | .cons _ _ => (default : Stream'.Seq _)

instance {basis_hd basis_tl} : Membership (ℝ × PreMS basis_tl) (PreMS (basis_hd :: basis_tl)) where
  mem ms x := x ∈ ms.toSeq

theorem eq_of_bisim {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x y : PreMS (basis_hd :: basis_tl)}
    (motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop)
    (base : motive x y)
    (step : ∀ x y, motive x y → (x = .nil ∧ y = .nil) ∨ ∃ exp coef,
      ∃ (x' y' : PreMS (basis_hd :: basis_tl)),
      x = cons exp coef x' ∧ y = cons exp coef y' ∧ motive x' y') :
    x = y := Seq.eq_of_bisim' motive base (by grind [nil, cons])

theorem eq_of_bisim_strong {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {x y : PreMS (basis_hd :: basis_tl)}
    (motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop)
    (base : motive x y)
    (step : ∀ x y, motive x y → (x = y) ∨ ∃ exp coef,
      ∃ (x' y' : PreMS (basis_hd :: basis_tl)),
      x = cons exp coef x' ∧ y = cons exp coef y' ∧ motive x' y') :
    x = y := Seq.eq_of_bisim_strong motive base (by grind [nil, cons])

section simp

@[simp]
theorem cons_ne_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)} :
    cons exp coef tl ≠ .nil := by
  intro h
  simp [cons, nil] at h
  apply Seq.cons_ne_nil h

@[simp]
theorem nil_ne_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)} :
    .nil ≠ cons exp coef tl := cons_ne_nil.symm

@[simp]
theorem cons_eq_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp1 exp2 : ℝ}
    {coef1 coef2 : PreMS basis_tl} {tl1 tl2 : PreMS (basis_hd :: basis_tl)} :
    cons exp1 coef1 tl1 = cons exp2 coef2 tl2 ↔ exp1 = exp2 ∧ coef1 = coef2 ∧ tl1 = tl2 := by
  rw [cons, cons, Seq.cons_eq_cons]
  grind

#check Stream'.Seq.corec_nil

#check Stream'.Seq.corec_cons

theorem corec_nil {β : Type*} {basis_hd} {basis_tl}
    {f : β → Option (ℝ × PreMS basis_tl × β)} {b : β} (h : f b = none) :
    corec f b = (nil : PreMS (basis_hd :: basis_tl)) := by
  simp [corec, nil]
  rw [Seq.corec_nil]
  simpa

theorem corec_cons {β : Type*} {basis_hd} {basis_tl} {exp : ℝ} {coef : PreMS basis_tl} {next : β}
    {f : β → Option (ℝ × PreMS basis_tl × β)} {b : β}
    (h : f b = some (exp, coef, next)) :
    (corec f b : PreMS (basis_hd :: basis_tl)) = cons exp coef (corec f next) := by
  simp [corec, cons]
  rw [Seq.corec_cons]
  simpa

@[simp]
theorem destruct_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    destruct (nil : PreMS (basis_hd :: basis_tl)) = none := by
  simp [destruct, nil]

@[simp]
theorem destruct_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)} :
    destruct (cons exp coef tl) = some (exp, coef, tl) := by
  simp [destruct, cons]

@[simp]
theorem head_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    head (nil : PreMS (basis_hd :: basis_tl)) = none := by
  simp [head, nil]

@[simp]
theorem head_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)} :
    head (cons exp coef tl) = some (exp, coef) := by
  simp [head, cons]

@[simp]
theorem map_nil {basis_hd basis_tl basis_hd' basis_tl'} (f : ℝ → PreMS basis_tl → ℝ)
    (g : ℝ → PreMS basis_tl → PreMS basis_tl') :
    map f g (nil : PreMS (basis_hd :: basis_tl)) = (nil : PreMS (basis_hd' :: basis_tl')) := by
  simp [map, nil]

@[simp]
theorem map_cons {basis_hd basis_tl basis_hd' basis_tl'} (f : ℝ → PreMS basis_tl → ℝ)
    (g : ℝ → PreMS basis_tl → PreMS basis_tl') {exp : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} :
    map f g (cons exp coef tl) = cons (basis_hd := basis_hd')
      (f exp coef) (g exp coef) (map f g tl) := by
  simp [map, cons]

@[simp]
theorem map_id {basis_hd basis_tl} (ms : PreMS (basis_hd :: basis_tl)) :
    ms.map (fun exp _ => exp) (fun _ coef => coef) = ms :=
  Stream'.Seq.map_id ms

-- #check Stream'.Seq.map_comp

-- @[simp]
-- theorem map_comp {b₁ b₂ b₃ bs₁ bs₂ bs₃} (f₁ : ℝ → PreMS b₁ → ℝ)
--     (g₁ : ℝ → PreMS b₁ → PreMS b₂) (f₂ : ℝ → PreMS b₂ → ℝ) (g₂ : ℝ → PreMS b₂ → PreMS b₃)
--     (ms : PreMS (b₁ :: bs₁)) :
--     ms.map () := by
--   simp [map, Stream'.Seq.map_comp]

@[simp]
theorem notMem_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x : ℝ × PreMS basis_tl} :
    x ∉ (nil : PreMS (basis_hd :: basis_tl)) :=
  Seq.notMem_nil _

@[simp]
theorem mem_cons_iff {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)} {x : ℝ × PreMS basis_tl} :
    x ∈ cons exp coef tl ↔ x = (exp, coef) ∨ x ∈ tl :=
  Seq.mem_cons_iff

@[simp]
theorem Pairwise_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {R} :
    Seq.Pairwise R (nil : PreMS (basis_hd :: basis_tl)) := by
  simp [nil]

@[simp]
theorem Pairwise_cons_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {R exp coef} :
    Seq.Pairwise R (cons exp coef (nil : PreMS (basis_hd :: basis_tl))) := by
  simp [cons, nil]

end simp

end Seq

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
theorem leadingExp_cons {exp : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} :
    @leadingExp basis_hd basis_tl (cons exp coef tl) = exp := by
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
    ∃ coef tl, ms = cons exp coef tl := by
  cases ms with
  | nil => simp at h
  | cons exp coef tl =>
    simp only [leadingExp_cons, WithBot.coe_inj] at h
    subst h
    use coef, tl

end leadingExp

section WellOrdered

/-- Auxilary instance for order on pairs `(exp, coef)` used below to define `WellOrdered` in terms
of `Stream'.Seq.Pairwise`. `(exp₁, coef₁) ≤ (exp₂, coef₂)` iff `exp₁ ≤ exp₂`. -/
scoped instance {basis} : Preorder (ℝ × PreMS basis) := Preorder.lift Prod.fst

private theorem lt_iff_lt {basis} {exp1 exp2 : ℝ} {coef1 coef2 : PreMS basis} :
    (exp1, coef1) < (exp2, coef2) ↔ exp1 < exp2 := by
  rfl

/-- Multiseries `ms` is `WellOrdered` when at each its level exponents are Pairwise by TODO. -/
inductive WellOrdered : {basis : Basis} → (PreMS basis) → Prop
| const (ms : PreMS []) : WellOrdered ms
| seq {hd} {tl} (ms : PreMS (hd :: tl))
    (h_coef : ∀ x ∈ ms, x.2.WellOrdered)
    (h_Pairwise : Seq.Pairwise (· > ·) ms) : ms.WellOrdered

variable {basis_hd : ℝ → ℝ} {basis_tl : Basis}

/-- `[]` is `WellOrdered`. -/
theorem WellOrdered.nil : @WellOrdered (basis_hd :: basis_tl) .nil := by
  constructor <;> simp

/-- `[(exp, coef)]` is `WellOrdered` when `coef` is `WellOrdered`. -/
theorem WellOrdered.cons_nil {exp : ℝ} {coef : PreMS basis_tl} (h_coef : coef.WellOrdered) :
    @WellOrdered (basis_hd :: basis_tl) (cons exp coef .nil) := by
  constructor
  · simpa
  · simp

/-- `cons (exp, coef) tl` is `WellOrdered` when `coef` and `tl` are `WellOrdered` and leading
exponent of `tl` is less than `exp`. -/
theorem WellOrdered.cons {exp : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h_coef : coef.WellOrdered)
    (h_comp : tl.leadingExp < exp)
    (h_tl : tl.WellOrdered) :
    @WellOrdered (basis_hd :: basis_tl) (cons exp coef tl) := by
  cases h_tl with | seq _ h_tl_coef h_tl_tl =>
  constructor
  · grind [mem_cons_iff]
  · cases tl
    · exact Pairwise_cons_nil
    apply Seq.Pairwise.cons_cons_of_trans _ h_tl_tl
    simpa [lt_iff_lt] using h_comp

/-- The fact `WellOrdered (cons (exp, coef) tl)` implies that `coef` and `tl` are `WellOrdered`, and
leading exponent of `tl` is less than `exp`. -/
theorem WellOrdered_cons {exp : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : @WellOrdered (basis_hd :: basis_tl) (cons exp coef tl)) :
    coef.WellOrdered ∧ tl.leadingExp < exp ∧ tl.WellOrdered := by
  cases h with | seq _ h_coef h_Pairwise =>
  constructor
  · specialize h_coef (exp, coef) (by simp)
    simpa using h_coef
  cases tl with
  | nil => simp [WellOrdered.nil]
  | cons tl_exp tl_coef tl_tl =>
  obtain ⟨h_all, h_Pairwise⟩ := Pairwise.cons_elim h_Pairwise
  constructor
  · simp
    apply h_all (tl_exp, tl_coef) (by simp [cons])
  constructor
  · intro x hx
    apply h_coef
    simp [hx]
  · assumption

/-- Coinduction principle for proving `WellOrdered`. For some predicate `motive` on multiseries,
if `motive ms` (base case) and the predicate "survives" destruction of its argument, then `ms` is
`WellOrdered`. Here "survive" means that if `x = cons (exp, coef) tl` than `motive x` must imply
`coef.wellOrdered`, `tl.leadingExp < exp` and `motive tl`. -/
theorem WellOrdered.coind {ms : PreMS (basis_hd :: basis_tl)}
    (motive : (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (h_base : motive ms)
    (h_step : ∀ exp coef tl, motive (PreMS.cons exp coef tl) →
        coef.WellOrdered ∧
        tl.leadingExp < exp ∧
        motive tl) :
    ms.WellOrdered := by
  constructor
  · apply all_coind
    · exact h_base
    · intro (exp, coef) tl h
      specialize h_step exp coef tl h
      grind
  · apply Pairwise.coind_trans
    · exact h_base
    · intro (exp, coef) tl h
      constructor
      · intro (tl_exp, tl_coef) h_tl
        simp
        change tl_exp < exp
        replace h_step := (h_step exp coef tl h).right.left
        cases tl <;> simp [leadingExp, head] at h_tl h_step; grind
      · specialize h_step exp coef tl h
        grind

end WellOrdered

section Approximates

section Majorated

/-- `majorated f g exp` for real functions `f` and `g` means that for any `exp' < exp`,
`f =o[atTop] g^exp'`. -/
def majorated (f basis_hd : ℝ → ℝ) (exp : ℝ) : Prop :=
  ∀ exp', exp < exp' → f =o[atTop] (fun t ↦ (basis_hd t) ^ exp')

/-- One can change the argument of `majorated` with the function that eventually equals to it. -/
theorem majorated_of_EventuallyEq {f g basis_hd : ℝ → ℝ} {exp : ℝ} (h_eq : g =ᶠ[atTop] f)
    (h : majorated f basis_hd exp) : majorated g basis_hd exp := by
  simp only [majorated] at *
  intro exp' h_exp
  specialize h exp' h_exp
  exact EventuallyEq.trans_isLittleO h_eq h

-- TODO: upstream?
/-- For any function `f`, `f^exp` is majorated with `f` with exponent `exp`. -/
theorem majorated_self {f : ℝ → ℝ} {exp : ℝ}
    (h : Tendsto f atTop atTop) :
    majorated (fun t ↦ (f t)^exp) f exp := by
  simp only [majorated]
  intro exp' h_exp
  apply (isLittleO_iff_tendsto' _).mpr
  · have : (fun t ↦ f t ^ exp / f t ^ exp') =ᶠ[atTop] fun t ↦ (f t)^(exp - exp') := by
      apply (Tendsto.eventually_gt_atTop h 0).mono
      intro t h
      simp only [← Real.rpow_sub h]
    apply Tendsto.congr' this.symm
    conv =>
      arg 1
      rw [show (fun t ↦ f t ^ (exp - exp')) = ((fun t ↦ t^(-(exp' - exp))) ∘ f) by ext; simp]
    apply Tendsto.comp _ h
    apply tendsto_rpow_neg_atTop
    linarith
  · apply (Tendsto.eventually_gt_atTop h 0).mono
    intro t h1 h2
    absurd h2
    exact (Real.rpow_pos_of_pos h1 _).ne.symm

/-- If one can majorate `f` with `exp1`, then it can be majorated with any `exp2 > exp1`. -/
theorem majorated_of_lt {f basis_hd : ℝ → ℝ} {exp1 exp2 : ℝ}
    (h_lt : exp1 < exp2) (h : majorated f basis_hd exp1) :
    majorated f basis_hd exp2 := by
  simp only [majorated] at *
  intro exp' h_exp
  apply h _ (by linarith)

/-- If `f` is majorated with negative exponent, then it tends to zero. -/
theorem majorated_tendsto_zero_of_neg {f basis_hd : ℝ → ℝ} {exp : ℝ}
    (h_lt : exp < 0) (h : majorated f basis_hd exp) :
    Tendsto f atTop (𝓝 0) := by
  simp only [majorated] at h
  specialize h 0 (by linarith)
  simpa using h

/-- Constants can be majorated with `exp = 0`. -/
theorem const_majorated {basis_hd : ℝ → ℝ} (h_tendsto : Tendsto basis_hd atTop atTop)
    {c : ℝ} : majorated (fun _ ↦ c) basis_hd 0 := by
  intro exp h_exp
  apply Asymptotics.isLittleO_const_left.mpr
  right
  apply Tendsto.comp tendsto_norm_atTop_atTop
  apply Tendsto.comp (tendsto_rpow_atTop h_exp)
  exact h_tendsto

/-- Zero can be majorated with any exponent. -/
theorem zero_majorated {basis_hd : ℝ → ℝ} {exp : ℝ} : majorated (fun _ ↦ 0) basis_hd exp := by
  intro exp h_exp
  apply Asymptotics.isLittleO_zero

/-- `f * c` can be majorated with the same exponent as `f` for any constant `c`. -/
theorem mul_const_majorated {f basis_hd : ℝ → ℝ} {exp : ℝ} (h : majorated f basis_hd exp)
    {c : ℝ} : majorated (fun t ↦ (f t) * c) basis_hd exp := by
  intro exp h_exp
  simp_rw [mul_comm]
  apply IsLittleO.const_mul_left (h exp h_exp)

/-- Sum of two function, that can be majorated with exponents `f_exp` and `g_exp`, can be
majorated with exponent `f_exp ⊔ g_exp`. -/
theorem add_majorated {f g basis_hd : ℝ → ℝ} {f_exp g_exp : ℝ} (hf : majorated f basis_hd f_exp)
    (hg : majorated g basis_hd g_exp) : majorated (f + g) basis_hd (f_exp ⊔ g_exp) := by
  simp only [majorated] at *
  intro exp h_exp
  simp only [sup_lt_iff] at h_exp
  apply IsLittleO.add
  · exact hf _ h_exp.left
  · exact hg _ h_exp.right

/-- Product of two function, that can be majorated with exponents `f_exp` and `g_exp`, can be
majorated with exponent `f_exp + g_exp`. -/
theorem mul_majorated {f g basis_hd : ℝ → ℝ} {f_exp g_exp : ℝ} (hf : majorated f basis_hd f_exp)
    (hg : majorated g basis_hd g_exp) (h_pos : ∀ᶠ t in atTop, 0 < basis_hd t) :
    majorated (f * g) basis_hd (f_exp + g_exp) := by
  simp only [majorated] at *
  intro exp h_exp
  let ε := (exp - f_exp - g_exp) / 2
  specialize hf (f_exp + ε) (by dsimp [ε]; linarith)
  specialize hg (g_exp + ε) (by dsimp [ε]; linarith)
  apply IsLittleO.trans_eventuallyEq
    (g₁ := fun t ↦ basis_hd t ^ (f_exp + ε) * basis_hd t ^ (g_exp + ε))
  · exact IsLittleO.mul hf hg
  · simp only [EventuallyEq]
    apply h_pos.mono
    intro t hx
    conv =>
      rhs
      rw [show exp = (f_exp + ε) + (g_exp + ε) by dsimp [ε]; ring_nf]
      rw [Real.rpow_add hx]

end Majorated

mutual
  def Approximates.T (basis : Basis) : (PreMS basis → (ℝ → ℝ) → Prop) →o
      (PreMS basis → (ℝ → ℝ) → Prop) :=
    match (generalizing := true) basis with
    | [] => {
      toFun := fun P ms f => (f =ᶠ[atTop] (fun _ ↦ ms))
      monotone' P Q hPQ ms f hP := hP
    }
    | .cons basis_hd basis_tl => {
      toFun := fun P ms f =>
        (ms = .nil ∧ f =ᶠ[atTop] 0) ∨
        (∃ (exp : ℝ) (coef : PreMS basis_tl) (tl : PreMS (basis_hd :: basis_tl)) (fC : ℝ → ℝ),
          ms = cons exp coef tl ∧ coef.Approximates fC ∧
          majorated f basis_hd exp ∧ P tl (fun t ↦ f t - (basis_hd t)^exp * fC t))
      monotone' := by
        intro P Q hPQ ms f hP
        generalize Approximates = A at *
        change ∀ ms f, P ms f → Q ms f at hPQ
        grind
    }

  def Approximates {basis} (ms : PreMS basis) (f : ℝ → ℝ) : Prop :=
    (Approximates.T basis).gfp ms f
end

variable {f basis_hd : ℝ → ℝ} {basis_tl : Basis}

private theorem Approximates.step {basis} {ms : PreMS basis} {f : ℝ → ℝ} :
    ms.Approximates f ↔ (Approximates.T basis Approximates ms f) := by
  conv_lhs => unfold Approximates; rw [← OrderHom.isFixedPt_gfp]
  conv_rhs => arg 2; eta_expand; unfold Approximates; change OrderHom.gfp _

theorem Approximates.const {c : ℝ} (h : f =ᶠ[atTop] fun _ ↦ c) : @Approximates [] c f := by
  rw [Approximates.step]
  simpa [T]

/-- `[]` approximates zero function. -/
theorem Approximates.nil (h : f =ᶠ[atTop] 0) :
    @Approximates (basis_hd :: basis_tl) .nil f := by
  rw [Approximates.step]
  simpa [T]

/-- `cons (exp, coef) tl` approximates `f` when `f` can be majorated with exponent `exp`, and
there exists some function `fC` such that `coef` approximates `fC` and `tl` approximates
`f - fC * basis_hd ^ exp`. -/
theorem Approximates.cons {exp : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (fC : ℝ → ℝ) (h_coef : coef.Approximates fC)
    (h_maj : majorated f basis_hd exp)
    (h_tl : tl.Approximates (fun t ↦ f t - (basis_hd t) ^ exp * (fC t))) :
    @Approximates (basis_hd :: basis_tl) (cons exp coef tl) f := by
  rw [Approximates.step]
  simp [T]
  grind

theorem Approximates.coind {ms : PreMS (basis_hd :: basis_tl)}
    (motive : (ms : PreMS (basis_hd :: basis_tl)) → (f : ℝ → ℝ) → Prop)
    (h_base : motive ms f)
    (h_step : ∀ ms f, motive ms f →
      (ms = .nil ∧ f =ᶠ[atTop] 0) ∨
      (∃ exp coef tl fC, ms = PreMS.cons exp coef tl ∧
        (coef.Approximates fC) ∧
        majorated f basis_hd exp ∧
        (motive tl (fun t ↦ f t - (basis_hd t) ^ exp * (fC t))))) :
    ms.Approximates f := by
  have : motive ≤ T _ motive := by
    intro ms f h
    simp [T]
    grind
  have := OrderHom.le_gfp _ this
  unfold Approximates
  aesop

@[simp]
theorem Approximates_const_iff {ms : PreMS []} {f : ℝ → ℝ} :
    ms.Approximates f ↔ f =ᶠ[atTop] (fun _ ↦ ms) where
  mp h := by
    rw [Approximates.step] at h
    simpa [Approximates.T] using h
  mpr h := Approximates.const h

/-- If `[]` approximates `f`, then `f = 0` eventually. -/
theorem Approximates_nil (h : @Approximates (basis_hd :: basis_tl) nil f) :
    f =ᶠ[atTop] 0 := by
  rw [Approximates.step] at h
  simpa [Approximates.T] using h

/-- If `cons (exp, coef) tl` approximates `f`, then `f` can be majorated with exponent `exp`, and
there exists function `fC` such that `coef` approximates `fC` and `tl` approximates
`f - fC * basis_hd ^ exp`. -/
theorem Approximates_cons {exp : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : @Approximates (basis_hd :: basis_tl) (cons exp coef tl) f) :
    ∃ fC,
      coef.Approximates fC ∧
      majorated f basis_hd exp ∧
      tl.Approximates (fun t ↦ f t - (basis_hd t)^exp * (fC t)) := by
  rw [Approximates.step] at h
  simp [Approximates.T] at h
  grind

/-- One can replace `f` in `Approximates` with the funcion that eventually equals `f`. -/
theorem Approximates_of_EventuallyEq {basis : Basis} {ms : PreMS basis} {f f' : ℝ → ℝ}
    (h_equiv : f =ᶠ[atTop] f') (h_approx : ms.Approximates f) :
    ms.Approximates f' := by
  cases basis with
  | nil => exact Approximates.const <| h_equiv.symm.trans (Approximates_const_iff.mp h_approx)
  | cons basis_hd basis_tl =>
    let motive (ms : PreMS (basis_hd :: basis_tl)) (f' : ℝ → ℝ) : Prop :=
        ∃ f, f =ᶠ[atTop] f' ∧ ms.Approximates f
    apply Approximates.coind motive
    · simp only [motive]
      use f
    · intro ms f' ih
      cases ms with
      | nil =>
        left
        simp only [motive] at ih
        obtain ⟨f, h_equiv, hF⟩ := ih
        apply Approximates_nil at hF
        constructor
        · rfl
        · exact EventuallyEq.trans h_equiv.symm hF
      | cons exp coef tl =>
        right
        use exp, coef, tl
        simp only [true_and]
        simp only [motive] at ih
        obtain ⟨f, h_equiv, hF⟩ := ih
        obtain ⟨fC, h_coef, h_maj, h_tl⟩ := Approximates_cons hF
        use fC
        constructor
        · exact h_coef
        constructor
        · intro exp' h
          apply EventuallyEq.trans_isLittleO h_equiv.symm
          apply h_maj _ h
        · simp only [motive]
          use fun t ↦ f t - basis_hd t ^ exp * (fC t)
          constructor
          · apply EventuallyEq.sub h_equiv
            apply EventuallyEq.rfl
          · exact h_tl

end Approximates

end PreMS

end ComputeAsymptotics
