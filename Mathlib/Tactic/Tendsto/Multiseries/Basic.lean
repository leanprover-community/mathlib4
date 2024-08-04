import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Tactic

namespace TendstoTactic

inductive PreMS where
| const : ℝ → PreMS
| nil : PreMS
| cons (deg : ℝ) (coef : PreMS) (tl : Thunk PreMS) : PreMS

abbrev Basis := List (ℝ → ℝ)

universe u in
def PreMS.rec' {motive : PreMS → Sort u} (const : ∀ c, motive (.const c)) (nil : motive .nil)
    (cons : (deg : ℝ) → (coef : PreMS) → (tl : Thunk PreMS) → motive coef → motive tl.get → motive (.cons deg coef tl)) (ms : PreMS) :
    motive ms :=
  match ms with
  | .const c => const c
  | .nil => nil
  | .cons deg coef tl =>
    let coef_ih := PreMS.rec' const nil cons coef
    let tl_ih := PreMS.rec' const nil cons tl.get
    cons deg coef tl coef_ih tl_ih

-- code generator does not support recursor 'TendstoTactic.PreMS.rec' yet
-- universe u in
-- def PreMS.rec'' {motive : PreMS → Sort u} (const : ∀ c, motive (.const c)) (nil : motive .nil)
--     (cons : (deg : ℝ) → (coef : PreMS) → (tl : Thunk PreMS) → motive coef → motive tl.get → motive (.cons deg coef tl)) (ms : PreMS) :
--     motive ms := by
--   induction ms using PreMS.rec with
--   | const => apply const
--   | nil => apply nil
--   | cons deg coef tl coef_ih tl_ih =>
--     have tl_ih : motive tl.get := tl_ih
--     apply cons
--     exacts [coef_ih, tl_ih]
--   | mk _ ih => apply ih

instance : Inhabited PreMS := ⟨.nil⟩

inductive PreMS.hasDepth : PreMS → ℕ → Prop where
| const (c : ℝ) : PreMS.hasDepth (PreMS.const c) 0
| nil (n : ℕ) : PreMS.hasDepth PreMS.nil n
| cons (m : ℕ) (deg : ℝ) (coef : PreMS) (tl : Thunk PreMS) (h_coef : PreMS.hasDepth coef m)
  (h_tl : PreMS.hasDepth tl.get (m + 1)) : PreMS.hasDepth (PreMS.cons deg coef tl) (m + 1)


-- todo: redefine as isApproximation
-- def PreMS.hasDepth (ms : PreMS) (n : ℕ) : Prop :=
--   match n, ms with
--   | n, .const _ => n = 0
--   | _, .nil => True
--   | 0, .cons _ _ _ => False
--   | m + 1, .cons _ coef tl => coef.hasDepth m ∧ tl.get.hasDepth n

-- inductive PreMS.wellOrdered : PreMS → Prop where
-- | const (c : ℝ) : PreMS.wellOrdered (PreMS.const c)
-- | nil : PreMS.wellOrdered PreMS.nil
-- | cons (deg : ℝ) (coef : PreMS) (tl : Thunk PreMS) (h_coef : PreMS.hasDepth coef m)
--   (h_tl : PreMS.hasDepth tl.get (m + 1)) : PreMS.hasDepth (PreMS.cons deg coef tl) (m + 1)

-- todo: redefine as isApproximation
def PreMS.wellOrdered (ms : PreMS) : Prop :=
  match ms with
  | cons deg coef tl => coef.wellOrdered ∧ tl.get.wellOrdered ∧
    match tl.get with
    | cons tl_deg _ _ => tl_deg < deg
    | _ => True
  | _ => True

inductive PreMS.isApproximation : PreMS → (ℝ → ℝ) → Basis → Prop where
| nil (basis : List (ℝ → ℝ)) (F : ℝ → ℝ) (h : F =ᶠ[Filter.atTop] 0) : PreMS.isApproximation .nil F basis
| const (c : ℝ) (F : ℝ → ℝ) (h : F =ᶠ[Filter.atTop] fun _ ↦ c) : PreMS.isApproximation (.const c) F []
| cons (deg : ℝ) (coef : PreMS) (tl : Thunk PreMS) (F C basis_hd : ℝ → ℝ)
    (basis_tl : Basis) (h_coef : coef.isApproximation C basis_tl)
    (h_tl : tl.get.isApproximation (fun x ↦ (F x) - (basis_hd x)^deg * (C x)) (basis_hd :: basis_tl))
    (h : (∀ deg', deg < deg' → F =o[Filter.atTop] (fun x => (basis_hd x)^deg'))) :
    PreMS.isApproximation (.cons deg coef tl) F (basis_hd :: basis_tl)

structure MS where
  val : PreMS
  basis : Basis
  F : ℝ → ℝ
  h_depth : val.hasDepth basis.length
  h_wo : val.wellOrdered
  h_approx : val.isApproximation F basis

def MS.const (c : ℝ) : MS where
  val := .const c
  basis := []
  F _ := c
  h_depth := PreMS.hasDepth.const _
  h_wo := by simp [PreMS.wellOrdered]
  h_approx := .const c (fun _ ↦ c) (by rfl)

def MS.zero : MS := MS.const 0
def MS.one : MS := MS.const 1

def MS.nil (basis : Basis) : MS where
  val := .nil
  basis := basis
  F _ := 0
  h_depth := PreMS.hasDepth.nil _
  h_wo := by simp [PreMS.wellOrdered]
  h_approx := .nil basis (fun _ ↦ 0) (by rfl)

--!!- IDK about this:

-- /-- Creates `cons deg coef .nil`. -/
-- def MS.monomial {n : ℕ} (deg : ℝ) (coef : MS n) : MS (n + 1) :=
--   ⟨PreMS.cons deg coef.val PreMS.nil, by
--     simp [PreMS.hasDepth, PreMS.wellOrdered]
--     exact coef.property.left
--   ⟩

-- -- useful?
-- def MS.lift {n m} (ms : MS n) (h : n ≤ m) : MS m :=
--   if hif : n = m then
--     hif ▸ ms
--   else
--     MS.lift (n := n + 1) (m := m) ⟨PreMS.cons 0 ms.val PreMS.nil, by
--       constructor
--       · simp [PreMS.hasDepth]; exact ms.property.left
--       · simp [PreMS.wellOrdered]
--     ⟩ (by omega)

-- example : (MS.lift (m := 2) (MS.const 1) (by decide)).val =
--   PreMS.cons 0
--     (PreMS.cons 0 (PreMS.const 1) PreMS.nil)
--   PreMS.nil := by rfl


-- def MS.baseFun {n : ℕ} (h : 0 < n) : MS n :=
--   match n with
--   | 0 => by omega
--   | m + 1 =>
--     let pre : MS m := MS.lift MS.one (by omega)
--     MS.monomial 1 pre

--!!- Maybe to Trimming.lean?

def PreMS.isFlatZero (ms : PreMS) : Prop :=
  match ms with
  | .const c => c = 0
  | .nil => True
  | _ => False


def PreMS.isTrimmed (ms : PreMS) : Prop :=
  match ms with
  | .cons _ coef _ => coef.isTrimmed ∧ ¬ coef.isFlatZero
  | _ => True

-- def PreMS.isTrimmed (ms : PreMS) : Prop :=
--   match ms with
--   | .cons _ coef _ => coef.isTrimmed
--   | .const c => c ≠ 0
--   | .nil => False

def MS.isTrimmed (ms : MS) : Prop :=
  ms.val.isTrimmed

end TendstoTactic
