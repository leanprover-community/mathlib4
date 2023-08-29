/-
Copyright (c) 2018 Violeta Hernández Palacios, Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Mario Carneiro
-/
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential

#align_import set_theory.ordinal.fixed_point from "leanprover-community/mathlib"@"0dd4319a17376eda5763cd0a7e0d35bbaaa50e83"

/-!
# Fixed points of normal functions

We prove various statements about the fixed points of normal ordinal functions. We state them in
three forms: as statements about type-indexed families of normal functions, as statements about
ordinal-indexed families of normal functions, and as statements about a single normal function. For
the most part, the first case encompasses the others.

Moreover, we prove some lemmas about the fixed points of specific normal functions.

## Main definitions and results

* `nfpFamily`, `nfpBFamily`, `nfp`: the next fixed point of a (family of) normal function(s).
* `fp_family_unbounded`, `fp_bfamily_unbounded`, `fp_unbounded`: the (common) fixed points of a
  (family of) normal function(s) are unbounded in the ordinals.
* `deriv_add_eq_mul_omega_add`: a characterization of the derivative of addition.
* `deriv_mul_eq_opow_omega_mul`: a characterization of the derivative of multiplication.
-/


noncomputable section

universe u v

open Function Order

namespace Ordinal

/-! ### Fixed points of type-indexed families of ordinals -/


section

variable {ι : Type u} {f : ι → Ordinal.{max u v} → Ordinal.{max u v}}

/-- The next common fixed point, at least `a`, for a family of normal functions.

This is defined for any family of functions, as the supremum of all values reachable by applying
finitely many functions in the family to `a`.

`Ordinal.nfpFamily_fp` shows this is a fixed point, `Ordinal.le_nfpFamily` shows it's at
least `a`, and `Ordinal.nfpFamily_le_fp` shows this is the least ordinal with these properties. -/
def nfpFamily (f : ι → Ordinal → Ordinal) (a : Ordinal) : Ordinal :=
  sup (List.foldr f a)
#align ordinal.nfp_family Ordinal.nfpFamily

theorem nfpFamily_eq_sup (f : ι → Ordinal.{max u v} → Ordinal.{max u v}) (a : Ordinal.{max u v}) :
    nfpFamily.{u, v} f a = sup.{u, v} (List.foldr f a) :=
  rfl
#align ordinal.nfp_family_eq_sup Ordinal.nfpFamily_eq_sup

theorem foldr_le_nfpFamily (f : ι → Ordinal → Ordinal)
    (a l) : List.foldr f a l ≤ nfpFamily.{u, v} f a :=
  le_sup.{u, v} _ _
#align ordinal.foldr_le_nfp_family Ordinal.foldr_le_nfpFamily

theorem le_nfpFamily (f : ι → Ordinal → Ordinal) (a) : a ≤ nfpFamily f a :=
  le_sup _ []
#align ordinal.le_nfp_family Ordinal.le_nfpFamily

theorem lt_nfpFamily {a b} : a < nfpFamily.{u, v} f b ↔ ∃ l, a < List.foldr f b l :=
  lt_sup.{u, v}
#align ordinal.lt_nfp_family Ordinal.lt_nfpFamily

theorem nfpFamily_le_iff {a b} : nfpFamily.{u, v} f a ≤ b ↔ ∀ l, List.foldr f a l ≤ b :=
  sup_le_iff
#align ordinal.nfp_family_le_iff Ordinal.nfpFamily_le_iff

theorem nfpFamily_le {a b} : (∀ l, List.foldr f a l ≤ b) → nfpFamily.{u, v} f a ≤ b :=
  sup_le.{u, v}
#align ordinal.nfp_family_le Ordinal.nfpFamily_le

theorem nfpFamily_monotone (hf : ∀ i, Monotone (f i)) : Monotone (nfpFamily.{u, v} f) :=
  fun _ _ h => sup_le.{u, v} fun l => (List.foldr_monotone hf l h).trans (le_sup.{u, v} _ l)
#align ordinal.nfp_family_monotone Ordinal.nfpFamily_monotone

theorem apply_lt_nfpFamily (H : ∀ i, IsNormal (f i)) {a b} (hb : b < nfpFamily.{u, v} f a) (i) :
    f i b < nfpFamily.{u, v} f a :=
  let ⟨l, hl⟩ := lt_nfpFamily.1 hb
  lt_sup.2 ⟨i::l, (H i).strictMono hl⟩
#align ordinal.apply_lt_nfp_family Ordinal.apply_lt_nfpFamily

theorem apply_lt_nfpFamily_iff [Nonempty ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∀ i, f i b < nfpFamily.{u, v} f a) ↔ b < nfpFamily.{u, v} f a :=
  ⟨fun h =>
    lt_nfpFamily.2 <|
      let ⟨l, hl⟩ := lt_sup.1 <| h <| Classical.arbitrary ι
      ⟨l, ((H _).self_le b).trans_lt hl⟩,
    apply_lt_nfpFamily H⟩
#align ordinal.apply_lt_nfp_family_iff Ordinal.apply_lt_nfpFamily_iff

theorem nfpFamily_le_apply [Nonempty ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∃ i, nfpFamily.{u, v} f a ≤ f i b) ↔ nfpFamily.{u, v} f a ≤ b := by
  rw [← not_iff_not]
  -- ⊢ (¬∃ i, nfpFamily f a ≤ f i b) ↔ ¬nfpFamily f a ≤ b
  push_neg
  -- ⊢ (∀ (i : ι), f i b < nfpFamily f a) ↔ b < nfpFamily f a
  exact apply_lt_nfpFamily_iff H
  -- 🎉 no goals
#align ordinal.nfp_family_le_apply Ordinal.nfpFamily_le_apply

theorem nfpFamily_le_fp (H : ∀ i, Monotone (f i)) {a b} (ab : a ≤ b) (h : ∀ i, f i b ≤ b) :
    nfpFamily.{u, v} f a ≤ b :=
  sup_le fun l => by
    by_cases hι : IsEmpty ι
    -- ⊢ List.foldr f a l ≤ b
    · rwa [Unique.eq_default l]
      -- 🎉 no goals
    · induction' l with i l IH generalizing a
      -- ⊢ List.foldr f a [] ≤ b
      · exact ab
        -- 🎉 no goals
      exact (H i (IH ab)).trans (h i)
      -- 🎉 no goals
#align ordinal.nfp_family_le_fp Ordinal.nfpFamily_le_fp

theorem nfpFamily_fp {i} (H : IsNormal (f i)) (a) :
    f i (nfpFamily.{u, v} f a) = nfpFamily.{u, v} f a := by
  unfold nfpFamily
  -- ⊢ f i (sup (List.foldr f a)) = sup (List.foldr f a)
  rw [@IsNormal.sup.{u, v, v} _ H _ _ ⟨[]⟩]
  -- ⊢ sup (f i ∘ List.foldr f a) = sup (List.foldr f a)
  apply le_antisymm <;> refine' Ordinal.sup_le fun l => _
  -- ⊢ sup (f i ∘ List.foldr f a) ≤ sup (List.foldr f a)
                        -- ⊢ (f i ∘ List.foldr f a) l ≤ sup (List.foldr f a)
                        -- ⊢ List.foldr f a l ≤ sup (f i ∘ List.foldr f a)
  · exact le_sup _ (i::l)
    -- 🎉 no goals
  · exact (H.self_le _).trans (le_sup _ _)
    -- 🎉 no goals
#align ordinal.nfp_family_fp Ordinal.nfpFamily_fp

theorem apply_le_nfpFamily [hι : Nonempty ι] {f : ι → Ordinal → Ordinal} (H : ∀ i, IsNormal (f i))
    {a b} : (∀ i, f i b ≤ nfpFamily.{u, v} f a) ↔ b ≤ nfpFamily.{u, v} f a := by
  refine' ⟨fun h => _, fun h i => _⟩
  -- ⊢ b ≤ nfpFamily f a
  · cases' hι with i
    -- ⊢ b ≤ nfpFamily f a
    exact ((H i).self_le b).trans (h i)
    -- 🎉 no goals
  rw [← nfpFamily_fp (H i)]
  -- ⊢ f i b ≤ f i (nfpFamily f a)
  exact (H i).monotone h
  -- 🎉 no goals
#align ordinal.apply_le_nfp_family Ordinal.apply_le_nfpFamily

theorem nfpFamily_eq_self {f : ι → Ordinal → Ordinal} {a} (h : ∀ i, f i a = a) :
    nfpFamily f a = a :=
  le_antisymm (sup_le fun l => by rw [List.foldr_fixed' h l]) <| le_nfpFamily f a
                                  -- 🎉 no goals
#align ordinal.nfp_family_eq_self Ordinal.nfpFamily_eq_self

-- Todo: This is actually a special case of the fact the intersection of club sets is a club set.
/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
theorem fp_family_unbounded (H : ∀ i, IsNormal (f i)) :
    (⋂ i, Function.fixedPoints (f i)).Unbounded (· < ·) := fun a =>
  ⟨nfpFamily.{u, v} f a, fun s ⟨i, hi⟩ => by
    rw [← hi, mem_fixedPoints_iff]
    -- ⊢ f i (nfpFamily f a) = nfpFamily f a
    exact nfpFamily_fp.{u, v} (H i) a, (le_nfpFamily f a).not_lt⟩
    -- 🎉 no goals
#align ordinal.fp_family_unbounded Ordinal.fp_family_unbounded

/-- The derivative of a family of normal functions is the sequence of their common fixed points.

This is defined for all functions such that `Ordinal.derivFamily_zero`,
`Ordinal.derivFamily_succ`, and `Ordinal.derivFamily_limit` are satisfied. -/
def derivFamily (f : ι → Ordinal → Ordinal) (o : Ordinal) : Ordinal :=
  limitRecOn o (nfpFamily.{u, v} f 0) (fun _ IH => nfpFamily.{u, v} f (succ IH))
    fun a _ => bsup.{max u v, u} a
#align ordinal.deriv_family Ordinal.derivFamily

@[simp]
theorem derivFamily_zero (f : ι → Ordinal → Ordinal) :
    derivFamily.{u, v} f 0 = nfpFamily.{u, v} f 0 :=
  limitRecOn_zero _ _ _
#align ordinal.deriv_family_zero Ordinal.derivFamily_zero

@[simp]
theorem derivFamily_succ (f : ι → Ordinal → Ordinal) (o) :
    derivFamily.{u, v} f (succ o) = nfpFamily.{u, v} f (succ (derivFamily.{u, v} f o)) :=
  limitRecOn_succ _ _ _ _
#align ordinal.deriv_family_succ Ordinal.derivFamily_succ

theorem derivFamily_limit (f : ι → Ordinal → Ordinal) {o} :
    IsLimit o → derivFamily.{u, v} f o = bsup.{max u v, u} o fun a _ => derivFamily.{u, v} f a :=
  limitRecOn_limit _ _ _ _
#align ordinal.deriv_family_limit Ordinal.derivFamily_limit

theorem derivFamily_isNormal (f : ι → Ordinal → Ordinal) : IsNormal (derivFamily f) :=
  ⟨fun o => by rw [derivFamily_succ, ← succ_le_iff]; apply le_nfpFamily, fun o l a => by
               -- ⊢ succ (derivFamily f o) ≤ nfpFamily f (succ (derivFamily f o))
                                                     -- 🎉 no goals
    rw [derivFamily_limit _ l, bsup_le_iff]⟩
    -- 🎉 no goals
#align ordinal.deriv_family_is_normal Ordinal.derivFamily_isNormal

theorem derivFamily_fp {i} (H : IsNormal (f i)) (o : Ordinal.{max u v}) :
    f i (derivFamily.{u, v} f o) = derivFamily.{u, v} f o := by
  induction' o using limitRecOn with o _ o l IH
  · rw [derivFamily_zero]
    -- ⊢ f i (nfpFamily f 0) = nfpFamily f 0
    exact nfpFamily_fp H 0
    -- 🎉 no goals
  · rw [derivFamily_succ]
    -- ⊢ f i (nfpFamily f (succ (derivFamily f o))) = nfpFamily f (succ (derivFamily  …
    exact nfpFamily_fp H _
    -- 🎉 no goals
  · rw [derivFamily_limit _ l,
      IsNormal.bsup.{max u v, u, max u v} H (fun a _ => derivFamily f a) l.1]
    refine' eq_of_forall_ge_iff fun c => _
    -- ⊢ (bsup o fun a h => f i (derivFamily f a)) ≤ c ↔ (bsup o fun a x => derivFami …
    simp (config := { contextual := true }) only [bsup_le_iff, IH]
    -- 🎉 no goals
#align ordinal.deriv_family_fp Ordinal.derivFamily_fp

theorem le_iff_derivFamily (H : ∀ i, IsNormal (f i)) {a} :
    (∀ i, f i a ≤ a) ↔ ∃ o, derivFamily.{u, v} f o = a :=
  ⟨fun ha => by
    suffices : ∀ (o) (_ : a ≤ derivFamily.{u, v} f o), ∃ o, derivFamily.{u, v} f o = a
    -- ⊢ ∃ o, derivFamily f o = a
    exact this a ((derivFamily_isNormal _).self_le _)
    -- ⊢ ∀ (o : Ordinal.{max u v}), a ≤ derivFamily f o → ∃ o, derivFamily f o = a
    intro o
    -- ⊢ a ≤ derivFamily f o → ∃ o, derivFamily f o = a
    induction' o using limitRecOn with o IH o l IH
    · intro h₁
      -- ⊢ ∃ o, derivFamily f o = a
      refine' ⟨0, le_antisymm _ h₁⟩
      -- ⊢ derivFamily f 0 ≤ a
      rw [derivFamily_zero]
      -- ⊢ nfpFamily f 0 ≤ a
      exact nfpFamily_le_fp (fun i => (H i).monotone) (Ordinal.zero_le _) ha
      -- 🎉 no goals
    · intro h₁
      -- ⊢ ∃ o, derivFamily f o = a
      cases' le_or_lt a (derivFamily.{u, v} f o) with h h
      -- ⊢ ∃ o, derivFamily f o = a
      · exact IH h
        -- 🎉 no goals
      refine' ⟨succ o, le_antisymm _ h₁⟩
      -- ⊢ derivFamily f (succ o) ≤ a
      rw [derivFamily_succ]
      -- ⊢ nfpFamily f (succ (derivFamily f o)) ≤ a
      exact nfpFamily_le_fp (fun i => (H i).monotone) (succ_le_of_lt h) ha
      -- 🎉 no goals
    · intro h₁
      -- ⊢ ∃ o, derivFamily f o = a
      cases' eq_or_lt_of_le h₁ with h h
      -- ⊢ ∃ o, derivFamily f o = a
      · exact ⟨_, h.symm⟩
        -- 🎉 no goals
      rw [derivFamily_limit _ l, ← not_le, bsup_le_iff, not_ball] at h
      -- ⊢ ∃ o, derivFamily f o = a
      exact
        let ⟨o', h, hl⟩ := h
        IH o' h (le_of_not_le hl),
    fun ⟨o, e⟩ i => e ▸ (derivFamily_fp (H i) _).le⟩
#align ordinal.le_iff_deriv_family Ordinal.le_iff_derivFamily

theorem fp_iff_derivFamily (H : ∀ i, IsNormal (f i)) {a} :
    (∀ i, f i a = a) ↔ ∃ o, derivFamily.{u, v} f o = a :=
  Iff.trans ⟨fun h i => le_of_eq (h i), fun h i => (H i).le_iff_eq.1 (h i)⟩ (le_iff_derivFamily H)
#align ordinal.fp_iff_deriv_family Ordinal.fp_iff_derivFamily

/-- For a family of normal functions, `Ordinal.derivFamily` enumerates the common fixed points. -/
theorem derivFamily_eq_enumOrd (H : ∀ i, IsNormal (f i)) :
    derivFamily.{u, v} f = enumOrd (⋂ i, Function.fixedPoints (f i)) := by
  rw [← eq_enumOrd _ (fp_family_unbounded.{u, v} H)]
  -- ⊢ StrictMono (derivFamily f) ∧ Set.range (derivFamily f) = ⋂ (i : ι), fixedPoi …
  use (derivFamily_isNormal f).strictMono
  -- ⊢ Set.range (derivFamily f) = ⋂ (i : ι), fixedPoints (f i)
  rw [Set.range_eq_iff]
  -- ⊢ (∀ (a : Ordinal.{max u v}), derivFamily f a ∈ ⋂ (i : ι), fixedPoints (f i))  …
  refine' ⟨_, fun a ha => _⟩
  -- ⊢ ∀ (a : Ordinal.{max u v}), derivFamily f a ∈ ⋂ (i : ι), fixedPoints (f i)
  · rintro a S ⟨i, hi⟩
    -- ⊢ derivFamily f a ∈ S
    rw [← hi]
    -- ⊢ derivFamily f a ∈ (fun i => fixedPoints (f i)) i
    exact derivFamily_fp (H i) a
    -- 🎉 no goals
  rw [Set.mem_iInter] at ha
  -- ⊢ ∃ a_1, derivFamily f a_1 = a
  rwa [← fp_iff_derivFamily H]
  -- 🎉 no goals
#align ordinal.deriv_family_eq_enum_ord Ordinal.derivFamily_eq_enumOrd

end

/-! ### Fixed points of ordinal-indexed families of ordinals -/


section

variable {o : Ordinal.{u}} {f : ∀ b < o, Ordinal.{max u v} → Ordinal.{max u v}}

/-- The next common fixed point, at least `a`, for a family of normal functions indexed by ordinals.

This is defined as `Ordinal.nfpFamily` of the type-indexed family associated to `f`. -/
def nfpBFamily (o : Ordinal) (f : ∀ b < o, Ordinal → Ordinal) : Ordinal → Ordinal :=
  nfpFamily (familyOfBFamily o f)
#align ordinal.nfp_bfamily Ordinal.nfpBFamily

theorem nfpBFamily_eq_nfpFamily {o : Ordinal} (f : ∀ b < o, Ordinal → Ordinal) :
    nfpBFamily.{u, v} o f = nfpFamily.{u, v} (familyOfBFamily o f) :=
  rfl
#align ordinal.nfp_bfamily_eq_nfp_family Ordinal.nfpBFamily_eq_nfpFamily

theorem foldr_le_nfpBFamily {o : Ordinal}
    (f : ∀ b < o, Ordinal → Ordinal) (a l) :
    List.foldr (familyOfBFamily o f) a l ≤ nfpBFamily.{u, v} o f a :=
  le_sup.{u, v} _ _
#align ordinal.foldr_le_nfp_bfamily Ordinal.foldr_le_nfpBFamily

theorem le_nfpBFamily {o : Ordinal} (f : ∀ b < o, Ordinal → Ordinal) (a) :
    a ≤ nfpBFamily.{u, v} o f a :=
  le_sup.{u, v} _ []
#align ordinal.le_nfp_bfamily Ordinal.le_nfpBFamily

theorem lt_nfpBFamily {a b} :
    a < nfpBFamily.{u, v} o f b ↔ ∃ l, a < List.foldr (familyOfBFamily o f) b l :=
  lt_sup.{u, v}
#align ordinal.lt_nfp_bfamily Ordinal.lt_nfpBFamily

theorem nfpBFamily_le_iff {o : Ordinal} {f : ∀ b < o, Ordinal → Ordinal} {a b} :
    nfpBFamily.{u, v} o f a ≤ b ↔ ∀ l, List.foldr (familyOfBFamily o f) a l ≤ b :=
  sup_le_iff.{u, v}
#align ordinal.nfp_bfamily_le_iff Ordinal.nfpBFamily_le_iff

theorem nfpBFamily_le {o : Ordinal} {f : ∀ b < o, Ordinal → Ordinal} {a b} :
    (∀ l, List.foldr (familyOfBFamily o f) a l ≤ b) → nfpBFamily.{u, v} o f a ≤ b :=
  sup_le.{u, v}
#align ordinal.nfp_bfamily_le Ordinal.nfpBFamily_le

theorem nfpBFamily_monotone (hf : ∀ i hi, Monotone (f i hi)) : Monotone (nfpBFamily.{u, v} o f) :=
  nfpFamily_monotone fun _ => hf _ _
#align ordinal.nfp_bfamily_monotone Ordinal.nfpBFamily_monotone

theorem apply_lt_nfpBFamily (H : ∀ i hi, IsNormal (f i hi)) {a b} (hb : b < nfpBFamily.{u, v} o f a)
    (i hi) : f i hi b < nfpBFamily.{u, v} o f a := by
  rw [←familyOfBFamily_enum o f]
  -- ⊢ familyOfBFamily o f (enum (fun x x_1 => x < x_1) i (_ : i < type fun x x_1 = …
  apply apply_lt_nfpFamily (fun _ => H _ _) hb
  -- 🎉 no goals
#align ordinal.apply_lt_nfp_bfamily Ordinal.apply_lt_nfpBFamily

theorem apply_lt_nfpBFamily_iff (ho : o ≠ 0) (H : ∀ i hi, IsNormal (f i hi)) {a b} :
    (∀ i hi, f i hi b < nfpBFamily.{u, v} o f a) ↔ b < nfpBFamily.{u, v} o f a :=
  ⟨fun h => by
    haveI := out_nonempty_iff_ne_zero.2 ho
    -- ⊢ b < nfpBFamily o f a
    refine' (apply_lt_nfpFamily_iff.{u, v} _).1 fun _ => h _ _
    -- ⊢ ∀ (i : (Quotient.out o).α), IsNormal (familyOfBFamily o f i)
    exact fun _ => H _ _, apply_lt_nfpBFamily H⟩
    -- 🎉 no goals
#align ordinal.apply_lt_nfp_bfamily_iff Ordinal.apply_lt_nfpBFamily_iff

theorem nfpBFamily_le_apply (ho : o ≠ 0) (H : ∀ i hi, IsNormal (f i hi)) {a b} :
    (∃ i hi, nfpBFamily.{u, v} o f a ≤ f i hi b) ↔ nfpBFamily.{u, v} o f a ≤ b := by
  rw [← not_iff_not]
  -- ⊢ (¬∃ i hi, nfpBFamily o f a ≤ f i hi b) ↔ ¬nfpBFamily o f a ≤ b
  push_neg
  -- ⊢ (∀ (i : Ordinal.{u}) (hi : i < o), f i hi b < nfpBFamily o f a) ↔ b < nfpBFa …
  exact apply_lt_nfpBFamily_iff.{u, v} ho H
  -- 🎉 no goals
#align ordinal.nfp_bfamily_le_apply Ordinal.nfpBFamily_le_apply

theorem nfpBFamily_le_fp (H : ∀ i hi, Monotone (f i hi)) {a b} (ab : a ≤ b)
    (h : ∀ i hi, f i hi b ≤ b) : nfpBFamily.{u, v} o f a ≤ b :=
  nfpFamily_le_fp (fun _ => H _ _) ab fun _ => h _ _
#align ordinal.nfp_bfamily_le_fp Ordinal.nfpBFamily_le_fp

theorem nfpBFamily_fp {i hi} (H : IsNormal (f i hi)) (a) :
    f i hi (nfpBFamily.{u, v} o f a) = nfpBFamily.{u, v} o f a := by
  rw [← familyOfBFamily_enum o f]
  -- ⊢ familyOfBFamily o f (enum (fun x x_1 => x < x_1) i (_ : i < type fun x x_1 = …
  apply nfpFamily_fp
  -- ⊢ IsNormal (familyOfBFamily o f (enum (fun x x_1 => x < x_1) i (_ : i < type f …
  rw [familyOfBFamily_enum]
  -- ⊢ IsNormal (f i ?H.hi)
  exact H
  -- 🎉 no goals
#align ordinal.nfp_bfamily_fp Ordinal.nfpBFamily_fp

theorem apply_le_nfpBFamily (ho : o ≠ 0) (H : ∀ i hi, IsNormal (f i hi)) {a b} :
    (∀ i hi, f i hi b ≤ nfpBFamily.{u, v} o f a) ↔ b ≤ nfpBFamily.{u, v} o f a := by
  refine' ⟨fun h => _, fun h i hi => _⟩
  -- ⊢ b ≤ nfpBFamily o f a
  · have ho' : 0 < o := Ordinal.pos_iff_ne_zero.2 ho
    -- ⊢ b ≤ nfpBFamily o f a
    exact ((H 0 ho').self_le b).trans (h 0 ho')
    -- 🎉 no goals
  · rw [← nfpBFamily_fp (H i hi)]
    -- ⊢ f i hi b ≤ f i hi (nfpBFamily o f a)
    exact (H i hi).monotone h
    -- 🎉 no goals
#align ordinal.apply_le_nfp_bfamily Ordinal.apply_le_nfpBFamily

theorem nfpBFamily_eq_self {a} (h : ∀ i hi, f i hi a = a) : nfpBFamily.{u, v} o f a = a :=
  nfpFamily_eq_self fun _ => h _ _
#align ordinal.nfp_bfamily_eq_self Ordinal.nfpBFamily_eq_self

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
theorem fp_bfamily_unbounded (H : ∀ i hi, IsNormal (f i hi)) :
    (⋂ (i) (hi), Function.fixedPoints (f i hi)).Unbounded (· < ·) := fun a =>
  ⟨nfpBFamily.{u, v} _ f a, by
    rw [Set.mem_iInter₂]
    -- ⊢ ∀ (i : Ordinal.{u}) (j : i < o), nfpBFamily o f a ∈ fixedPoints (f i j)
    exact fun i hi => nfpBFamily_fp (H i hi) _, (le_nfpBFamily f a).not_lt⟩
    -- 🎉 no goals
#align ordinal.fp_bfamily_unbounded Ordinal.fp_bfamily_unbounded

/-- The derivative of a family of normal functions is the sequence of their common fixed points.

This is defined as `Ordinal.derivFamily` of the type-indexed family associated to `f`. -/
def derivBFamily (o : Ordinal) (f : ∀ b < o, Ordinal → Ordinal) : Ordinal → Ordinal :=
  derivFamily (familyOfBFamily o f)
#align ordinal.deriv_bfamily Ordinal.derivBFamily

theorem derivBFamily_eq_derivFamily {o : Ordinal} (f : ∀ b < o, Ordinal → Ordinal) :
    derivBFamily.{u, v} o f = derivFamily.{u, v} (familyOfBFamily o f) :=
  rfl
#align ordinal.deriv_bfamily_eq_deriv_family Ordinal.derivBFamily_eq_derivFamily

theorem derivBFamily_isNormal {o : Ordinal} (f : ∀ b < o, Ordinal → Ordinal) :
    IsNormal (derivBFamily o f) :=
  derivFamily_isNormal _
#align ordinal.deriv_bfamily_is_normal Ordinal.derivBFamily_isNormal

theorem derivBFamily_fp {i hi} (H : IsNormal (f i hi)) (a : Ordinal) :
    f i hi (derivBFamily.{u, v} o f a) = derivBFamily.{u, v} o f a := by
  rw [← familyOfBFamily_enum o f]
  -- ⊢ familyOfBFamily o f (enum (fun x x_1 => x < x_1) i (_ : i < type fun x x_1 = …
  apply derivFamily_fp
  -- ⊢ IsNormal (familyOfBFamily o f (enum (fun x x_1 => x < x_1) i (_ : i < type f …
  rw [familyOfBFamily_enum]
  -- ⊢ IsNormal (f i ?H.hi)
  exact H
  -- 🎉 no goals
#align ordinal.deriv_bfamily_fp Ordinal.derivBFamily_fp

theorem le_iff_derivBFamily (H : ∀ i hi, IsNormal (f i hi)) {a} :
    (∀ i hi, f i hi a ≤ a) ↔ ∃ b, derivBFamily.{u, v} o f b = a := by
  unfold derivBFamily
  -- ⊢ (∀ (i : Ordinal.{u}) (hi : i < o), f i hi a ≤ a) ↔ ∃ b, derivFamily (familyO …
  rw [← le_iff_derivFamily]
  -- ⊢ (∀ (i : Ordinal.{u}) (hi : i < o), f i hi a ≤ a) ↔ ∀ (i : (Quotient.out o).α …
  · refine' ⟨fun h i => h _ _, fun h i hi => _⟩
    -- ⊢ f i hi a ≤ a
    rw [← familyOfBFamily_enum o f]
    -- ⊢ familyOfBFamily o f (enum (fun x x_1 => x < x_1) i (_ : i < type fun x x_1 = …
    apply h
    -- 🎉 no goals
  · exact fun _ => H _ _
    -- 🎉 no goals
#align ordinal.le_iff_deriv_bfamily Ordinal.le_iff_derivBFamily

theorem fp_iff_derivBFamily (H : ∀ i hi, IsNormal (f i hi)) {a} :
    (∀ i hi, f i hi a = a) ↔ ∃ b, derivBFamily.{u, v} o f b = a := by
  rw [← le_iff_derivBFamily H]
  -- ⊢ (∀ (i : Ordinal.{u}) (hi : i < o), f i hi a = a) ↔ ∀ (i : Ordinal.{u}) (hi : …
  refine' ⟨fun h i hi => le_of_eq (h i hi), fun h i hi => _⟩
  -- ⊢ f i hi a = a
  rw [← (H i hi).le_iff_eq]
  -- ⊢ f i hi a ≤ a
  exact h i hi
  -- 🎉 no goals
#align ordinal.fp_iff_deriv_bfamily Ordinal.fp_iff_derivBFamily

/-- For a family of normal functions, `Ordinal.derivBFamily` enumerates the common fixed points. -/
theorem derivBFamily_eq_enumOrd (H : ∀ i hi, IsNormal (f i hi)) :
    derivBFamily.{u, v} o f = enumOrd (⋂ (i) (hi), Function.fixedPoints (f i hi)) := by
  rw [← eq_enumOrd _ (fp_bfamily_unbounded.{u, v} H)]
  -- ⊢ StrictMono (derivBFamily o f) ∧ Set.range (derivBFamily o f) = ⋂ (i : Ordina …
  use (derivBFamily_isNormal f).strictMono
  -- ⊢ Set.range (derivBFamily o f) = ⋂ (i : Ordinal.{u}) (hi : i < o), fixedPoints …
  rw [Set.range_eq_iff]
  -- ⊢ (∀ (a : Ordinal.{max u v}), derivBFamily o f a ∈ ⋂ (i : Ordinal.{u}) (hi : i …
  refine' ⟨fun a => Set.mem_iInter₂.2 fun i hi => derivBFamily_fp (H i hi) a, fun a ha => _⟩
  -- ⊢ ∃ a_1, derivBFamily o f a_1 = a
  rw [Set.mem_iInter₂] at ha
  -- ⊢ ∃ a_1, derivBFamily o f a_1 = a
  rwa [← fp_iff_derivBFamily H]
  -- 🎉 no goals
#align ordinal.deriv_bfamily_eq_enum_ord Ordinal.derivBFamily_eq_enumOrd

end

/-! ### Fixed points of a single function -/


section

variable {f : Ordinal.{u} → Ordinal.{u}}

/-- The next fixed point function, the least fixed point of the normal function `f`, at least `a`.

This is defined as `ordinal.nfpFamily` applied to a family consisting only of `f`. -/
def nfp (f : Ordinal → Ordinal) : Ordinal → Ordinal :=
  nfpFamily fun _ : Unit => f
#align ordinal.nfp Ordinal.nfp

theorem nfp_eq_nfpFamily (f : Ordinal → Ordinal) : nfp f = nfpFamily fun _ : Unit => f :=
  rfl
#align ordinal.nfp_eq_nfp_family Ordinal.nfp_eq_nfpFamily

@[simp]
theorem sup_iterate_eq_nfp (f : Ordinal.{u} → Ordinal.{u}) :
    (fun a => sup fun n : ℕ => f^[n] a) = nfp f := by
  refine' funext fun a => le_antisymm _ (sup_le fun l => _)
  -- ⊢ (sup fun n => f^[n] a) ≤ nfp f a
  · rw [sup_le_iff]
    -- ⊢ ∀ (i : ℕ), f^[i] a ≤ nfp f a
    intro n
    -- ⊢ f^[n] a ≤ nfp f a
    rw [← List.length_replicate n Unit.unit, ← List.foldr_const f a]
    -- ⊢ List.foldr (fun x => f) a (List.replicate n ()) ≤ nfp f a
    apply le_sup
    -- 🎉 no goals
  · rw [List.foldr_const f a l]
    -- ⊢ f^[List.length l] a ≤ sup fun n => f^[n] a
    exact le_sup _ _
    -- 🎉 no goals
#align ordinal.sup_iterate_eq_nfp Ordinal.sup_iterate_eq_nfp

theorem iterate_le_nfp (f a n) : f^[n] a ≤ nfp f a := by
  rw [← sup_iterate_eq_nfp]
  -- ⊢ f^[n] a ≤ (fun a => sup fun n => f^[n] a) a
  exact le_sup _ n
  -- 🎉 no goals
#align ordinal.iterate_le_nfp Ordinal.iterate_le_nfp

theorem le_nfp (f a) : a ≤ nfp f a :=
  iterate_le_nfp f a 0
#align ordinal.le_nfp Ordinal.le_nfp

theorem lt_nfp {a b} : a < nfp f b ↔ ∃ n, a < f^[n] b := by
  rw [← sup_iterate_eq_nfp]
  -- ⊢ a < (fun a => sup fun n => f^[n] a) b ↔ ∃ n, a < f^[n] b
  exact lt_sup
  -- 🎉 no goals
#align ordinal.lt_nfp Ordinal.lt_nfp

theorem nfp_le_iff {a b} : nfp f a ≤ b ↔ ∀ n, f^[n] a ≤ b := by
  rw [← sup_iterate_eq_nfp]
  -- ⊢ (fun a => sup fun n => f^[n] a) a ≤ b ↔ ∀ (n : ℕ), f^[n] a ≤ b
  exact sup_le_iff
  -- 🎉 no goals
#align ordinal.nfp_le_iff Ordinal.nfp_le_iff

theorem nfp_le {a b} : (∀ n, f^[n] a ≤ b) → nfp f a ≤ b :=
  nfp_le_iff.2
#align ordinal.nfp_le Ordinal.nfp_le

@[simp]
theorem nfp_id : nfp id = id :=
  funext fun a => by
    simp_rw [← sup_iterate_eq_nfp, iterate_id]
    -- ⊢ (sup fun n => id a) = id a
    exact sup_const a
    -- 🎉 no goals
#align ordinal.nfp_id Ordinal.nfp_id

theorem nfp_monotone (hf : Monotone f) : Monotone (nfp f) :=
  nfpFamily_monotone fun _ => hf
#align ordinal.nfp_monotone Ordinal.nfp_monotone

theorem IsNormal.apply_lt_nfp {f} (H : IsNormal f) {a b} : f b < nfp f a ↔ b < nfp f a := by
  unfold nfp
  -- ⊢ f b < nfpFamily (fun x => f) a ↔ b < nfpFamily (fun x => f) a
  rw [← @apply_lt_nfpFamily_iff Unit (fun _ => f) _ (fun _ => H) a b]
  -- ⊢ f b < nfpFamily (fun x => f) a ↔ Unit → f b < nfpFamily (fun x => f) a
  exact ⟨fun h _ => h, fun h => h Unit.unit⟩
  -- 🎉 no goals
#align ordinal.is_normal.apply_lt_nfp Ordinal.IsNormal.apply_lt_nfp

theorem IsNormal.nfp_le_apply {f} (H : IsNormal f) {a b} : nfp f a ≤ f b ↔ nfp f a ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 H.apply_lt_nfp
#align ordinal.is_normal.nfp_le_apply Ordinal.IsNormal.nfp_le_apply

theorem nfp_le_fp {f} (H : Monotone f) {a b} (ab : a ≤ b) (h : f b ≤ b) : nfp f a ≤ b :=
  nfpFamily_le_fp (fun _ => H) ab fun _ => h
#align ordinal.nfp_le_fp Ordinal.nfp_le_fp

theorem IsNormal.nfp_fp {f} (H : IsNormal f) : ∀ a, f (nfp f a) = nfp f a :=
  @nfpFamily_fp Unit (fun _ => f) Unit.unit H
#align ordinal.is_normal.nfp_fp Ordinal.IsNormal.nfp_fp

theorem IsNormal.apply_le_nfp {f} (H : IsNormal f) {a b} : f b ≤ nfp f a ↔ b ≤ nfp f a :=
  ⟨le_trans (H.self_le _), fun h => by simpa only [H.nfp_fp] using H.le_iff.2 h⟩
                                       -- 🎉 no goals
#align ordinal.is_normal.apply_le_nfp Ordinal.IsNormal.apply_le_nfp

theorem nfp_eq_self {f : Ordinal → Ordinal} {a} (h : f a = a) : nfp f a = a :=
  nfpFamily_eq_self fun _ => h
#align ordinal.nfp_eq_self Ordinal.nfp_eq_self

/-- The fixed point lemma for normal functions: any normal function has an unbounded set of
fixed points. -/
theorem fp_unbounded (H : IsNormal f) : (Function.fixedPoints f).Unbounded (· < ·) := by
  convert fp_family_unbounded fun _ : Unit => H
  -- ⊢ fixedPoints f = ⋂ (i : Unit), fixedPoints f
  exact (Set.iInter_const _).symm
  -- 🎉 no goals
#align ordinal.fp_unbounded Ordinal.fp_unbounded

/-- The derivative of a normal function `f` is the sequence of fixed points of `f`.

This is defined as `Ordinal.derivFamily` applied to a trivial family consisting only of `f`. -/
def deriv (f : Ordinal → Ordinal) : Ordinal → Ordinal :=
  derivFamily fun _ : Unit => f
#align ordinal.deriv Ordinal.deriv

theorem deriv_eq_derivFamily (f : Ordinal → Ordinal) : deriv f = derivFamily fun _ : Unit => f :=
  rfl
#align ordinal.deriv_eq_deriv_family Ordinal.deriv_eq_derivFamily

@[simp]
theorem deriv_zero (f) : deriv f 0 = nfp f 0 :=
  derivFamily_zero _
#align ordinal.deriv_zero Ordinal.deriv_zero

@[simp]
theorem deriv_succ (f o) : deriv f (succ o) = nfp f (succ (deriv f o)) :=
  derivFamily_succ _ _
#align ordinal.deriv_succ Ordinal.deriv_succ

theorem deriv_limit (f) {o} : IsLimit o → deriv f o = bsup.{u, 0} o fun a _ => deriv f a :=
  derivFamily_limit _
#align ordinal.deriv_limit Ordinal.deriv_limit

theorem deriv_isNormal (f) : IsNormal (deriv f) :=
  derivFamily_isNormal _
#align ordinal.deriv_is_normal Ordinal.deriv_isNormal

theorem deriv_id_of_nfp_id {f : Ordinal → Ordinal} (h : nfp f = id) : deriv f = id :=
  ((deriv_isNormal _).eq_iff_zero_and_succ IsNormal.refl).2 (by simp [h])
                                                                -- 🎉 no goals
#align ordinal.deriv_id_of_nfp_id Ordinal.deriv_id_of_nfp_id

theorem IsNormal.deriv_fp {f} (H : IsNormal f) : ∀ o, f (deriv f o) = deriv f o :=
  @derivFamily_fp Unit (fun _ => f) Unit.unit H
#align ordinal.is_normal.deriv_fp Ordinal.IsNormal.deriv_fp

theorem IsNormal.le_iff_deriv {f} (H : IsNormal f) {a} : f a ≤ a ↔ ∃ o, deriv f o = a := by
  unfold deriv
  -- ⊢ f a ≤ a ↔ ∃ o, derivFamily (fun x => f) o = a
  rw [← le_iff_derivFamily fun _ : Unit => H]
  -- ⊢ f a ≤ a ↔ Unit → f a ≤ a
  exact ⟨fun h _ => h, fun h => h Unit.unit⟩
  -- 🎉 no goals
#align ordinal.is_normal.le_iff_deriv Ordinal.IsNormal.le_iff_deriv

theorem IsNormal.fp_iff_deriv {f} (H : IsNormal f) {a} : f a = a ↔ ∃ o, deriv f o = a := by
  rw [← H.le_iff_eq, H.le_iff_deriv]
  -- 🎉 no goals
#align ordinal.is_normal.fp_iff_deriv Ordinal.IsNormal.fp_iff_deriv

/-- `Ordinal.deriv` enumerates the fixed points of a normal function. -/
theorem deriv_eq_enumOrd (H : IsNormal f) : deriv f = enumOrd (Function.fixedPoints f) := by
  convert derivFamily_eq_enumOrd fun _ : Unit => H
  -- ⊢ fixedPoints f = ⋂ (i : Unit), fixedPoints f
  exact (Set.iInter_const _).symm
  -- 🎉 no goals
#align ordinal.deriv_eq_enum_ord Ordinal.deriv_eq_enumOrd

theorem deriv_eq_id_of_nfp_eq_id {f : Ordinal → Ordinal} (h : nfp f = id) : deriv f = id :=
  (IsNormal.eq_iff_zero_and_succ (deriv_isNormal _) IsNormal.refl).2 <| by simp [h]
                                                                           -- 🎉 no goals
#align ordinal.deriv_eq_id_of_nfp_eq_id Ordinal.deriv_eq_id_of_nfp_eq_id

end

/-! ### Fixed points of addition -/


@[simp]
theorem nfp_add_zero (a) : nfp (a + ·) 0 = a * omega := by
  simp_rw [← sup_iterate_eq_nfp, ← sup_mul_nat]
  -- ⊢ (sup fun n => (fun x => a + x)^[n] 0) = sup fun n => a * ↑n
  congr; funext n
  -- ⊢ (fun n => (fun x => a + x)^[n] 0) = fun n => a * ↑n
         -- ⊢ (fun x => a + x)^[n] 0 = a * ↑n
  induction' n with n hn
  -- ⊢ (fun x => a + x)^[Nat.zero] 0 = a * ↑Nat.zero
  · rw [Nat.cast_zero, mul_zero, iterate_zero_apply]
    -- 🎉 no goals
  · nth_rw 2 [Nat.succ_eq_one_add]
    -- ⊢ (fun x => a + x)^[Nat.succ n] 0 = a * ↑(1 + n)
    rw [Nat.cast_add, Nat.cast_one, mul_one_add, iterate_succ_apply', hn]
    -- 🎉 no goals
#align ordinal.nfp_add_zero Ordinal.nfp_add_zero

theorem nfp_add_eq_mul_omega {a b} (hba : b ≤ a * omega) : nfp (a + ·) b = a * omega := by
  apply le_antisymm (nfp_le_fp (add_isNormal a).monotone hba _)
  -- ⊢ a * ω ≤ nfp ((fun x x_1 => x + x_1) a) b
  · rw [← nfp_add_zero]
    -- ⊢ nfp (fun x => a + x) 0 ≤ nfp ((fun x x_1 => x + x_1) a) b
    exact nfp_monotone (add_isNormal a).monotone (Ordinal.zero_le b)
    -- 🎉 no goals
  · dsimp; rw [← mul_one_add, one_add_omega]
    -- ⊢ a + a * ω ≤ a * ω
           -- 🎉 no goals
#align ordinal.nfp_add_eq_mul_omega Ordinal.nfp_add_eq_mul_omega

theorem add_eq_right_iff_mul_omega_le {a b : Ordinal} : a + b = b ↔ a * omega ≤ b := by
  refine' ⟨fun h => _, fun h => _⟩
  -- ⊢ a * ω ≤ b
  · rw [← nfp_add_zero a, ← deriv_zero]
    -- ⊢ deriv (fun x => a + x) 0 ≤ b
    cases' (add_isNormal a).fp_iff_deriv.1 h with c hc
    -- ⊢ deriv (fun x => a + x) 0 ≤ b
    rw [← hc]
    -- ⊢ deriv (fun x => a + x) 0 ≤ deriv ((fun x x_1 => x + x_1) a) c
    exact (deriv_isNormal _).monotone (Ordinal.zero_le _)
    -- 🎉 no goals
  · have := Ordinal.add_sub_cancel_of_le h
    -- ⊢ a + b = b
    nth_rw 1 [← this]
    -- ⊢ a + (a * ω + (b - a * ω)) = b
    rwa [← add_assoc, ← mul_one_add, one_add_omega]
    -- 🎉 no goals
#align ordinal.add_eq_right_iff_mul_omega_le Ordinal.add_eq_right_iff_mul_omega_le

theorem add_le_right_iff_mul_omega_le {a b : Ordinal} : a + b ≤ b ↔ a * omega ≤ b := by
  rw [← add_eq_right_iff_mul_omega_le]
  -- ⊢ a + b ≤ b ↔ a + b = b
  exact (add_isNormal a).le_iff_eq
  -- 🎉 no goals
#align ordinal.add_le_right_iff_mul_omega_le Ordinal.add_le_right_iff_mul_omega_le

theorem deriv_add_eq_mul_omega_add (a b : Ordinal.{u}) : deriv (a + ·) b = a * omega + b := by
  revert b
  -- ⊢ ∀ (b : Ordinal.{u}), deriv (fun x => a + x) b = a * ω + b
  rw [← funext_iff, IsNormal.eq_iff_zero_and_succ (deriv_isNormal _) (add_isNormal _)]
  -- ⊢ deriv (fun x => a + x) 0 = (fun x x_1 => x + x_1) (a * ω) 0 ∧ ∀ (a_1 : Ordin …
  refine' ⟨_, fun a h => _⟩
  -- ⊢ deriv (fun x => a + x) 0 = (fun x x_1 => x + x_1) (a * ω) 0
  · dsimp; rw [deriv_zero, add_zero]
    -- ⊢ deriv (fun x => a + x) 0 = a * ω + 0
           -- ⊢ nfp (fun x => a + x) 0 = a * ω
    exact nfp_add_zero a
    -- 🎉 no goals
  · dsimp; rw [deriv_succ, h, add_succ]
    -- ⊢ deriv (fun x => a✝ + x) (succ a) = a✝ * ω + succ a
           -- ⊢ nfp (fun x => a✝ + x) (succ ((fun x x_1 => x + x_1) (a✝ * ω) a)) = succ (a✝  …
    exact nfp_eq_self (add_eq_right_iff_mul_omega_le.2 ((le_add_right _ _).trans (le_succ _)))
    -- 🎉 no goals
#align ordinal.deriv_add_eq_mul_omega_add Ordinal.deriv_add_eq_mul_omega_add

/-! ### Fixed points of multiplication -/

--Porting note: commented out, doesn't seem necessary
-- local infixr:0 "^" => @Pow.pow Ordinal Ordinal Ordinal.hasPow

@[simp]
theorem nfp_mul_one {a : Ordinal} (ha : 0 < a) : nfp (a * ·) 1 = (a^omega) := by
  rw [← sup_iterate_eq_nfp, ← sup_opow_nat]
  -- ⊢ (fun a_1 => sup fun n => (fun x => a * x)^[n] a_1) 1 = sup fun n => a ^ ↑n
  · dsimp
    -- ⊢ (sup fun n => (fun x => a * x)^[n] 1) = sup fun n => a ^ ↑n
    congr
    -- ⊢ (fun n => (fun x => a * x)^[n] 1) = fun n => a ^ ↑n
    funext n
    -- ⊢ (fun x => a * x)^[n] 1 = a ^ ↑n
    induction' n with n hn
    -- ⊢ (fun x => a * x)^[Nat.zero] 1 = a ^ ↑Nat.zero
    · rw [Nat.cast_zero, opow_zero, iterate_zero_apply]
      -- 🎉 no goals
    nth_rw 2 [Nat.succ_eq_one_add]
    -- ⊢ (fun x => a * x)^[Nat.succ n] 1 = a ^ ↑(1 + n)
    rw [Nat.cast_add, Nat.cast_one, opow_add, opow_one, iterate_succ_apply', hn]
    -- 🎉 no goals
  · exact ha
    -- 🎉 no goals
#align ordinal.nfp_mul_one Ordinal.nfp_mul_one

@[simp]
theorem nfp_mul_zero (a : Ordinal) : nfp (a * ·) 0 = 0 := by
  rw [← Ordinal.le_zero, nfp_le_iff]
  -- ⊢ ∀ (n : ℕ), (fun x => a * x)^[n] 0 ≤ 0
  intro n
  -- ⊢ (fun x => a * x)^[n] 0 ≤ 0
  induction' n with n hn; · rfl
  -- ⊢ (fun x => a * x)^[Nat.zero] 0 ≤ 0
                            -- 🎉 no goals
  dsimp only; rwa [iterate_succ_apply, mul_zero]
  -- ⊢ (fun x => a * x)^[Nat.succ n] 0 ≤ 0
              -- 🎉 no goals
#align ordinal.nfp_mul_zero Ordinal.nfp_mul_zero

@[simp]
theorem nfp_zero_mul : nfp (HMul.hMul 0) = id := by
  rw [← sup_iterate_eq_nfp]
  -- ⊢ (fun a => sup fun n => (HMul.hMul 0)^[n] a) = id
  refine' funext fun a => (sup_le fun n => _).antisymm (le_sup (fun n => (0 * ·)^[n] a) 0)
  -- ⊢ (HMul.hMul 0)^[n] a ≤ id a
  induction' n with n _
  -- ⊢ (HMul.hMul 0)^[Nat.zero] a ≤ id a
  · rfl
    -- 🎉 no goals
  rw [Function.iterate_succ']
  -- ⊢ (HMul.hMul 0 ∘ (HMul.hMul 0)^[n]) a ≤ id a
  change 0 * _ ≤ a
  -- ⊢ 0 * (HMul.hMul 0)^[n] a ≤ a
  rw [zero_mul]
  -- ⊢ 0 ≤ a
  exact Ordinal.zero_le a
  -- 🎉 no goals
#align ordinal.nfp_zero_mul Ordinal.nfp_zero_mul

@[simp]
theorem deriv_mul_zero : deriv (HMul.hMul 0) = id :=
  deriv_eq_id_of_nfp_eq_id nfp_zero_mul
#align ordinal.deriv_mul_zero Ordinal.deriv_mul_zero

theorem nfp_mul_eq_opow_omega {a b : Ordinal} (hb : 0 < b) (hba : b ≤ (a^omega)) :
    nfp (a * ·) b = (a^omega.{u}) := by
  cases' eq_zero_or_pos a with ha ha
  -- ⊢ nfp (fun x => a * x) b = a ^ ω
  · rw [ha, zero_opow omega_ne_zero] at hba ⊢
    -- ⊢ nfp (fun x => 0 * x) b = 0
    rw [Ordinal.le_zero.1 hba, nfp_zero_mul]
    -- ⊢ id 0 = 0
    rfl
    -- 🎉 no goals
  apply le_antisymm
  -- ⊢ nfp (fun x => a * x) b ≤ a ^ ω
  · apply nfp_le_fp (mul_isNormal ha).monotone hba
    -- ⊢ (fun x x_1 => x * x_1) a (a ^ ω) ≤ a ^ ω
    dsimp only; rw [← opow_one_add, one_add_omega]
    -- ⊢ a * a ^ ω ≤ a ^ ω
                -- 🎉 no goals
  rw [← nfp_mul_one ha]
  -- ⊢ nfp (fun x => a * x) 1 ≤ nfp (fun x => a * x) b
  exact nfp_monotone (mul_isNormal ha).monotone (one_le_iff_pos.2 hb)
  -- 🎉 no goals
#align ordinal.nfp_mul_eq_opow_omega Ordinal.nfp_mul_eq_opow_omega

theorem eq_zero_or_opow_omega_le_of_mul_eq_right {a b : Ordinal} (hab : a * b = b) :
    b = 0 ∨ (a^omega.{u}) ≤ b := by
  cases' eq_zero_or_pos a with ha ha
  -- ⊢ b = 0 ∨ a ^ ω ≤ b
  · rw [ha, zero_opow omega_ne_zero]
    -- ⊢ b = 0 ∨ 0 ≤ b
    exact Or.inr (Ordinal.zero_le b)
    -- 🎉 no goals
  rw [or_iff_not_imp_left]
  -- ⊢ ¬b = 0 → a ^ ω ≤ b
  intro hb
  -- ⊢ a ^ ω ≤ b
  rw [← nfp_mul_one ha]
  -- ⊢ nfp (fun x => a * x) 1 ≤ b
  rw [← Ne.def, ← one_le_iff_ne_zero] at hb
  -- ⊢ nfp (fun x => a * x) 1 ≤ b
  exact nfp_le_fp (mul_isNormal ha).monotone hb (le_of_eq hab)
  -- 🎉 no goals
#align ordinal.eq_zero_or_opow_omega_le_of_mul_eq_right Ordinal.eq_zero_or_opow_omega_le_of_mul_eq_right

theorem mul_eq_right_iff_opow_omega_dvd {a b : Ordinal} : a * b = b ↔ (a^omega) ∣ b := by
  cases' eq_zero_or_pos a with ha ha
  -- ⊢ a * b = b ↔ a ^ ω ∣ b
  · rw [ha, zero_mul, zero_opow omega_ne_zero, zero_dvd_iff]
    -- ⊢ 0 = b ↔ b = 0
    exact eq_comm
    -- 🎉 no goals
  refine' ⟨fun hab => _, fun h => _⟩
  -- ⊢ a ^ ω ∣ b
  · rw [dvd_iff_mod_eq_zero]
    -- ⊢ b % a ^ ω = 0
    rw [← div_add_mod b (a^omega), mul_add, ← mul_assoc, ← opow_one_add, one_add_omega,
      add_left_cancel] at hab
    cases' eq_zero_or_opow_omega_le_of_mul_eq_right hab with hab hab
    -- ⊢ b % a ^ ω = 0
    · exact hab
      -- 🎉 no goals
    refine' (not_lt_of_le hab (mod_lt b (opow_ne_zero omega _))).elim
    -- ⊢ a ≠ 0
    rwa [← Ordinal.pos_iff_ne_zero]
    -- 🎉 no goals
  cases' h with c hc
  -- ⊢ a * b = b
  rw [hc, ← mul_assoc, ← opow_one_add, one_add_omega]
  -- 🎉 no goals
#align ordinal.mul_eq_right_iff_opow_omega_dvd Ordinal.mul_eq_right_iff_opow_omega_dvd

theorem mul_le_right_iff_opow_omega_dvd {a b : Ordinal} (ha : 0 < a) :
    a * b ≤ b ↔ (a^omega) ∣ b := by
  rw [← mul_eq_right_iff_opow_omega_dvd]
  -- ⊢ a * b ≤ b ↔ a * b = b
  exact (mul_isNormal ha).le_iff_eq
  -- 🎉 no goals
#align ordinal.mul_le_right_iff_opow_omega_dvd Ordinal.mul_le_right_iff_opow_omega_dvd

theorem nfp_mul_opow_omega_add {a c : Ordinal} (b) (ha : 0 < a) (hc : 0 < c) (hca : c ≤ (a^omega)) :
    nfp (a * ·) ((a^omega) * b + c) = (a^omega.{u}) * succ b := by
  apply le_antisymm
  -- ⊢ nfp (fun x => a * x) (a ^ ω * b + c) ≤ a ^ ω * succ b
  · apply nfp_le_fp (mul_isNormal ha).monotone
    -- ⊢ a ^ ω * b + c ≤ a ^ ω * succ b
    · rw [mul_succ]
      -- ⊢ a ^ ω * b + c ≤ a ^ ω * b + a ^ ω
      apply add_le_add_left hca
      -- 🎉 no goals
    · dsimp only; rw [← mul_assoc, ← opow_one_add, one_add_omega]
      -- ⊢ a * (a ^ ω * succ b) ≤ a ^ ω * succ b
                  -- 🎉 no goals
  · cases' mul_eq_right_iff_opow_omega_dvd.1 ((mul_isNormal ha).nfp_fp ((a^omega) * b + c)) with
      d hd
    rw [hd]
    -- ⊢ a ^ ω * succ b ≤ a ^ ω * d
    apply mul_le_mul_left'
    -- ⊢ succ b ≤ d
    have := le_nfp (Mul.mul a) ((a^omega) * b + c)
    -- ⊢ succ b ≤ d
    erw [hd] at this
    -- ⊢ succ b ≤ d
    have := (add_lt_add_left hc ((a^omega) * b)).trans_le this
    -- ⊢ succ b ≤ d
    rw [add_zero, mul_lt_mul_iff_left (opow_pos omega ha)] at this
    -- ⊢ succ b ≤ d
    rwa [succ_le_iff]
    -- 🎉 no goals
#align ordinal.nfp_mul_opow_omega_add Ordinal.nfp_mul_opow_omega_add

theorem deriv_mul_eq_opow_omega_mul {a : Ordinal.{u}} (ha : 0 < a) (b) :
    deriv (a * ·) b = (a^omega) * b := by
  revert b
  -- ⊢ ∀ (b : Ordinal.{u}), deriv (fun x => a * x) b = a ^ ω * b
  rw [← funext_iff,
    IsNormal.eq_iff_zero_and_succ (deriv_isNormal _) (mul_isNormal (opow_pos omega ha))]
  refine' ⟨_, fun c h => _⟩
  -- ⊢ deriv (fun x => a * x) 0 = (fun x x_1 => x * x_1) (a ^ ω) 0
  · dsimp only; rw [deriv_zero, nfp_mul_zero, mul_zero]
    -- ⊢ deriv (fun x => a * x) 0 = a ^ ω * 0
                -- 🎉 no goals
  · rw [deriv_succ, h]
    -- ⊢ nfp (fun x => a * x) (succ ((fun x x_1 => x * x_1) (a ^ ω) c)) = (fun x x_1  …
    exact nfp_mul_opow_omega_add c ha zero_lt_one (one_le_iff_pos.2 (opow_pos _ ha))
    -- 🎉 no goals
#align ordinal.deriv_mul_eq_opow_omega_mul Ordinal.deriv_mul_eq_opow_omega_mul

end Ordinal
