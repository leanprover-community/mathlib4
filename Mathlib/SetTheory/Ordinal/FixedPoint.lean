/-
Copyright (c) 2018 Violeta Hernández Palacios, Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Mario Carneiro
-/
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential

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

theorem nfpFamily_eq_sup (f : ι → Ordinal.{max u v} → Ordinal.{max u v}) (a : Ordinal.{max u v}) :
    nfpFamily.{u, v} f a = sup.{u, v} (List.foldr f a) :=
  rfl

theorem foldr_le_nfpFamily (f : ι → Ordinal → Ordinal)
    (a l) : List.foldr f a l ≤ nfpFamily.{u, v} f a :=
  le_sup.{u, v} _ _

theorem le_nfpFamily (f : ι → Ordinal → Ordinal) (a) : a ≤ nfpFamily f a :=
  le_sup _ []

theorem lt_nfpFamily {a b} : a < nfpFamily.{u, v} f b ↔ ∃ l, a < List.foldr f b l :=
  lt_sup.{u, v}

theorem nfpFamily_le_iff {a b} : nfpFamily.{u, v} f a ≤ b ↔ ∀ l, List.foldr f a l ≤ b :=
  sup_le_iff

theorem nfpFamily_le {a b} : (∀ l, List.foldr f a l ≤ b) → nfpFamily.{u, v} f a ≤ b :=
  sup_le.{u, v}

theorem nfpFamily_monotone (hf : ∀ i, Monotone (f i)) : Monotone (nfpFamily.{u, v} f) :=
  fun _ _ h => sup_le.{u, v} fun l => (List.foldr_monotone hf l h).trans (le_sup.{u, v} _ l)

theorem apply_lt_nfpFamily (H : ∀ i, IsNormal (f i)) {a b} (hb : b < nfpFamily.{u, v} f a) (i) :
    f i b < nfpFamily.{u, v} f a :=
  let ⟨l, hl⟩ := lt_nfpFamily.1 hb
  lt_sup.2 ⟨i::l, (H i).strictMono hl⟩

theorem apply_lt_nfpFamily_iff [Nonempty ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∀ i, f i b < nfpFamily.{u, v} f a) ↔ b < nfpFamily.{u, v} f a :=
  ⟨fun h =>
    lt_nfpFamily.2 <|
      let ⟨l, hl⟩ := lt_sup.1 <| h <| Classical.arbitrary ι
      ⟨l, ((H _).self_le b).trans_lt hl⟩,
    apply_lt_nfpFamily H⟩

theorem nfpFamily_le_apply [Nonempty ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∃ i, nfpFamily.{u, v} f a ≤ f i b) ↔ nfpFamily.{u, v} f a ≤ b := by
  rw [← not_iff_not]
  push_neg
  exact apply_lt_nfpFamily_iff H

theorem nfpFamily_le_fp (H : ∀ i, Monotone (f i)) {a b} (ab : a ≤ b) (h : ∀ i, f i b ≤ b) :
    nfpFamily.{u, v} f a ≤ b :=
  sup_le fun l => by
    by_cases hι : IsEmpty ι
    · rwa [Unique.eq_default l]
    · induction' l with i l IH generalizing a
      · exact ab
      exact (H i (IH ab)).trans (h i)

theorem nfpFamily_fp {i} (H : IsNormal (f i)) (a) :
    f i (nfpFamily.{u, v} f a) = nfpFamily.{u, v} f a := by
  unfold nfpFamily
  rw [@IsNormal.sup.{u, v, v} _ H _ _ ⟨[]⟩]
  apply le_antisymm <;> refine Ordinal.sup_le fun l => ?_
  · exact le_sup _ (i::l)
  · exact (H.self_le _).trans (le_sup _ _)

theorem apply_le_nfpFamily [hι : Nonempty ι] {f : ι → Ordinal → Ordinal} (H : ∀ i, IsNormal (f i))
    {a b} : (∀ i, f i b ≤ nfpFamily.{u, v} f a) ↔ b ≤ nfpFamily.{u, v} f a := by
  refine ⟨fun h => ?_, fun h i => ?_⟩
  · cases' hι with i
    exact ((H i).self_le b).trans (h i)
  rw [← nfpFamily_fp (H i)]
  exact (H i).monotone h

theorem nfpFamily_eq_self {f : ι → Ordinal → Ordinal} {a} (h : ∀ i, f i a = a) :
    nfpFamily f a = a :=
  le_antisymm (sup_le fun l => by rw [List.foldr_fixed' h l]) <| le_nfpFamily f a

-- Todo: This is actually a special case of the fact the intersection of club sets is a club set.
/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
theorem fp_family_unbounded (H : ∀ i, IsNormal (f i)) :
    (⋂ i, Function.fixedPoints (f i)).Unbounded (· < ·) := fun a =>
  ⟨nfpFamily.{u, v} f a, fun s ⟨i, hi⟩ => by
    rw [← hi, mem_fixedPoints_iff]
    exact nfpFamily_fp.{u, v} (H i) a, (le_nfpFamily f a).not_lt⟩

/-- The derivative of a family of normal functions is the sequence of their common fixed points.

This is defined for all functions such that `Ordinal.derivFamily_zero`,
`Ordinal.derivFamily_succ`, and `Ordinal.derivFamily_limit` are satisfied. -/
def derivFamily (f : ι → Ordinal → Ordinal) (o : Ordinal) : Ordinal :=
  limitRecOn o (nfpFamily.{u, v} f 0) (fun _ IH => nfpFamily.{u, v} f (succ IH))
    fun a _ => bsup.{max u v, u} a

@[simp]
theorem derivFamily_zero (f : ι → Ordinal → Ordinal) :
    derivFamily.{u, v} f 0 = nfpFamily.{u, v} f 0 :=
  limitRecOn_zero _ _ _

@[simp]
theorem derivFamily_succ (f : ι → Ordinal → Ordinal) (o) :
    derivFamily.{u, v} f (succ o) = nfpFamily.{u, v} f (succ (derivFamily.{u, v} f o)) :=
  limitRecOn_succ _ _ _ _

theorem derivFamily_limit (f : ι → Ordinal → Ordinal) {o} :
    IsLimit o → derivFamily.{u, v} f o = bsup.{max u v, u} o fun a _ => derivFamily.{u, v} f a :=
  limitRecOn_limit _ _ _ _

theorem derivFamily_isNormal (f : ι → Ordinal → Ordinal) : IsNormal (derivFamily f) :=
  ⟨fun o => by rw [derivFamily_succ, ← succ_le_iff]; apply le_nfpFamily, fun o l a => by
    rw [derivFamily_limit _ l, bsup_le_iff]⟩

theorem derivFamily_fp {i} (H : IsNormal (f i)) (o : Ordinal.{max u v}) :
    f i (derivFamily.{u, v} f o) = derivFamily.{u, v} f o := by
  induction' o using limitRecOn with o _ o l IH
  · rw [derivFamily_zero]
    exact nfpFamily_fp H 0
  · rw [derivFamily_succ]
    exact nfpFamily_fp H _
  · rw [derivFamily_limit _ l,
      IsNormal.bsup.{max u v, u, max u v} H (fun a _ => derivFamily f a) l.1]
    refine eq_of_forall_ge_iff fun c => ?_
    simp (config := { contextual := true }) only [bsup_le_iff, IH]

theorem le_iff_derivFamily (H : ∀ i, IsNormal (f i)) {a} :
    (∀ i, f i a ≤ a) ↔ ∃ o, derivFamily.{u, v} f o = a :=
  ⟨fun ha => by
    suffices ∀ (o) (_ : a ≤ derivFamily.{u, v} f o), ∃ o, derivFamily.{u, v} f o = a from
      this a ((derivFamily_isNormal _).self_le _)
    intro o
    induction' o using limitRecOn with o IH o l IH
    · intro h₁
      refine ⟨0, le_antisymm ?_ h₁⟩
      rw [derivFamily_zero]
      exact nfpFamily_le_fp (fun i => (H i).monotone) (Ordinal.zero_le _) ha
    · intro h₁
      rcases le_or_lt a (derivFamily.{u, v} f o) with h | h
      · exact IH h
      refine ⟨succ o, le_antisymm ?_ h₁⟩
      rw [derivFamily_succ]
      exact nfpFamily_le_fp (fun i => (H i).monotone) (succ_le_of_lt h) ha
    · intro h₁
      cases' eq_or_lt_of_le h₁ with h h
      · exact ⟨_, h.symm⟩
      rw [derivFamily_limit _ l, ← not_le, bsup_le_iff, not_forall₂] at h
      exact
        let ⟨o', h, hl⟩ := h
        IH o' h (le_of_not_le hl),
    fun ⟨o, e⟩ i => e ▸ (derivFamily_fp (H i) _).le⟩

theorem fp_iff_derivFamily (H : ∀ i, IsNormal (f i)) {a} :
    (∀ i, f i a = a) ↔ ∃ o, derivFamily.{u, v} f o = a :=
  Iff.trans ⟨fun h i => le_of_eq (h i), fun h i => (H i).le_iff_eq.1 (h i)⟩ (le_iff_derivFamily H)

/-- For a family of normal functions, `Ordinal.derivFamily` enumerates the common fixed points. -/
theorem derivFamily_eq_enumOrd (H : ∀ i, IsNormal (f i)) :
    derivFamily.{u, v} f = enumOrd (⋂ i, Function.fixedPoints (f i)) := by
  rw [← eq_enumOrd _ (fp_family_unbounded.{u, v} H)]
  use (derivFamily_isNormal f).strictMono
  rw [Set.range_eq_iff]
  refine ⟨?_, fun a ha => ?_⟩
  · rintro a S ⟨i, hi⟩
    rw [← hi]
    exact derivFamily_fp (H i) a
  rw [Set.mem_iInter] at ha
  rwa [← fp_iff_derivFamily H]

end

/-! ### Fixed points of ordinal-indexed families of ordinals -/


section

variable {o : Ordinal.{u}} {f : ∀ b < o, Ordinal.{max u v} → Ordinal.{max u v}}

/-- The next common fixed point, at least `a`, for a family of normal functions indexed by ordinals.

This is defined as `Ordinal.nfpFamily` of the type-indexed family associated to `f`. -/
def nfpBFamily (o : Ordinal) (f : ∀ b < o, Ordinal → Ordinal) : Ordinal → Ordinal :=
  nfpFamily (familyOfBFamily o f)

theorem nfpBFamily_eq_nfpFamily {o : Ordinal} (f : ∀ b < o, Ordinal → Ordinal) :
    nfpBFamily.{u, v} o f = nfpFamily.{u, v} (familyOfBFamily o f) :=
  rfl

theorem foldr_le_nfpBFamily {o : Ordinal}
    (f : ∀ b < o, Ordinal → Ordinal) (a l) :
    List.foldr (familyOfBFamily o f) a l ≤ nfpBFamily.{u, v} o f a :=
  le_sup.{u, v} _ _

theorem le_nfpBFamily {o : Ordinal} (f : ∀ b < o, Ordinal → Ordinal) (a) :
    a ≤ nfpBFamily.{u, v} o f a :=
  le_sup.{u, v} _ []

theorem lt_nfpBFamily {a b} :
    a < nfpBFamily.{u, v} o f b ↔ ∃ l, a < List.foldr (familyOfBFamily o f) b l :=
  lt_sup.{u, v}

theorem nfpBFamily_le_iff {o : Ordinal} {f : ∀ b < o, Ordinal → Ordinal} {a b} :
    nfpBFamily.{u, v} o f a ≤ b ↔ ∀ l, List.foldr (familyOfBFamily o f) a l ≤ b :=
  sup_le_iff.{u, v}

theorem nfpBFamily_le {o : Ordinal} {f : ∀ b < o, Ordinal → Ordinal} {a b} :
    (∀ l, List.foldr (familyOfBFamily o f) a l ≤ b) → nfpBFamily.{u, v} o f a ≤ b :=
  sup_le.{u, v}

theorem nfpBFamily_monotone (hf : ∀ i hi, Monotone (f i hi)) : Monotone (nfpBFamily.{u, v} o f) :=
  nfpFamily_monotone fun _ => hf _ _

theorem apply_lt_nfpBFamily (H : ∀ i hi, IsNormal (f i hi)) {a b} (hb : b < nfpBFamily.{u, v} o f a)
    (i hi) : f i hi b < nfpBFamily.{u, v} o f a := by
  rw [← familyOfBFamily_enum o f]
  apply apply_lt_nfpFamily (fun _ => H _ _) hb

theorem apply_lt_nfpBFamily_iff (ho : o ≠ 0) (H : ∀ i hi, IsNormal (f i hi)) {a b} :
    (∀ i hi, f i hi b < nfpBFamily.{u, v} o f a) ↔ b < nfpBFamily.{u, v} o f a :=
  ⟨fun h => by
    haveI := out_nonempty_iff_ne_zero.2 ho
    refine (apply_lt_nfpFamily_iff.{u, v} ?_).1 fun _ => h _ _
    exact fun _ => H _ _, apply_lt_nfpBFamily H⟩

theorem nfpBFamily_le_apply (ho : o ≠ 0) (H : ∀ i hi, IsNormal (f i hi)) {a b} :
    (∃ i hi, nfpBFamily.{u, v} o f a ≤ f i hi b) ↔ nfpBFamily.{u, v} o f a ≤ b := by
  rw [← not_iff_not]
  push_neg
  exact apply_lt_nfpBFamily_iff.{u, v} ho H

theorem nfpBFamily_le_fp (H : ∀ i hi, Monotone (f i hi)) {a b} (ab : a ≤ b)
    (h : ∀ i hi, f i hi b ≤ b) : nfpBFamily.{u, v} o f a ≤ b :=
  nfpFamily_le_fp (fun _ => H _ _) ab fun _ => h _ _

theorem nfpBFamily_fp {i hi} (H : IsNormal (f i hi)) (a) :
    f i hi (nfpBFamily.{u, v} o f a) = nfpBFamily.{u, v} o f a := by
  rw [← familyOfBFamily_enum o f]
  apply nfpFamily_fp
  rw [familyOfBFamily_enum]
  exact H

theorem apply_le_nfpBFamily (ho : o ≠ 0) (H : ∀ i hi, IsNormal (f i hi)) {a b} :
    (∀ i hi, f i hi b ≤ nfpBFamily.{u, v} o f a) ↔ b ≤ nfpBFamily.{u, v} o f a := by
  refine ⟨fun h => ?_, fun h i hi => ?_⟩
  · have ho' : 0 < o := Ordinal.pos_iff_ne_zero.2 ho
    exact ((H 0 ho').self_le b).trans (h 0 ho')
  · rw [← nfpBFamily_fp (H i hi)]
    exact (H i hi).monotone h

theorem nfpBFamily_eq_self {a} (h : ∀ i hi, f i hi a = a) : nfpBFamily.{u, v} o f a = a :=
  nfpFamily_eq_self fun _ => h _ _

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
theorem fp_bfamily_unbounded (H : ∀ i hi, IsNormal (f i hi)) :
    (⋂ (i) (hi), Function.fixedPoints (f i hi)).Unbounded (· < ·) := fun a =>
  ⟨nfpBFamily.{u, v} _ f a, by
    rw [Set.mem_iInter₂]
    exact fun i hi => nfpBFamily_fp (H i hi) _, (le_nfpBFamily f a).not_lt⟩

/-- The derivative of a family of normal functions is the sequence of their common fixed points.

This is defined as `Ordinal.derivFamily` of the type-indexed family associated to `f`. -/
def derivBFamily (o : Ordinal) (f : ∀ b < o, Ordinal → Ordinal) : Ordinal → Ordinal :=
  derivFamily (familyOfBFamily o f)

theorem derivBFamily_eq_derivFamily {o : Ordinal} (f : ∀ b < o, Ordinal → Ordinal) :
    derivBFamily.{u, v} o f = derivFamily.{u, v} (familyOfBFamily o f) :=
  rfl

theorem derivBFamily_isNormal {o : Ordinal} (f : ∀ b < o, Ordinal → Ordinal) :
    IsNormal (derivBFamily o f) :=
  derivFamily_isNormal _

theorem derivBFamily_fp {i hi} (H : IsNormal (f i hi)) (a : Ordinal) :
    f i hi (derivBFamily.{u, v} o f a) = derivBFamily.{u, v} o f a := by
  rw [← familyOfBFamily_enum o f]
  apply derivFamily_fp
  rw [familyOfBFamily_enum]
  exact H

theorem le_iff_derivBFamily (H : ∀ i hi, IsNormal (f i hi)) {a} :
    (∀ i hi, f i hi a ≤ a) ↔ ∃ b, derivBFamily.{u, v} o f b = a := by
  unfold derivBFamily
  rw [← le_iff_derivFamily]
  · refine ⟨fun h i => h _ _, fun h i hi => ?_⟩
    rw [← familyOfBFamily_enum o f]
    apply h
  · exact fun _ => H _ _

theorem fp_iff_derivBFamily (H : ∀ i hi, IsNormal (f i hi)) {a} :
    (∀ i hi, f i hi a = a) ↔ ∃ b, derivBFamily.{u, v} o f b = a := by
  rw [← le_iff_derivBFamily H]
  refine ⟨fun h i hi => le_of_eq (h i hi), fun h i hi => ?_⟩
  rw [← (H i hi).le_iff_eq]
  exact h i hi

/-- For a family of normal functions, `Ordinal.derivBFamily` enumerates the common fixed points. -/
theorem derivBFamily_eq_enumOrd (H : ∀ i hi, IsNormal (f i hi)) :
    derivBFamily.{u, v} o f = enumOrd (⋂ (i) (hi), Function.fixedPoints (f i hi)) := by
  rw [← eq_enumOrd _ (fp_bfamily_unbounded.{u, v} H)]
  use (derivBFamily_isNormal f).strictMono
  rw [Set.range_eq_iff]
  refine ⟨fun a => Set.mem_iInter₂.2 fun i hi => derivBFamily_fp (H i hi) a, fun a ha => ?_⟩
  rw [Set.mem_iInter₂] at ha
  rwa [← fp_iff_derivBFamily H]

end

/-! ### Fixed points of a single function -/


section

variable {f : Ordinal.{u} → Ordinal.{u}}

/-- The next fixed point function, the least fixed point of the normal function `f`, at least `a`.

This is defined as `ordinal.nfpFamily` applied to a family consisting only of `f`. -/
def nfp (f : Ordinal → Ordinal) : Ordinal → Ordinal :=
  nfpFamily fun _ : Unit => f

theorem nfp_eq_nfpFamily (f : Ordinal → Ordinal) : nfp f = nfpFamily fun _ : Unit => f :=
  rfl

@[simp]
theorem sup_iterate_eq_nfp (f : Ordinal.{u} → Ordinal.{u}) :
    (fun a => sup fun n : ℕ => f^[n] a) = nfp f := by
  refine funext fun a => le_antisymm ?_ (sup_le fun l => ?_)
  · rw [sup_le_iff]
    intro n
    rw [← List.length_replicate n Unit.unit, ← List.foldr_const f a]
    apply le_sup
  · rw [List.foldr_const f a l]
    exact le_sup _ _

theorem iterate_le_nfp (f a n) : f^[n] a ≤ nfp f a := by
  rw [← sup_iterate_eq_nfp]
  exact le_sup _ n

theorem le_nfp (f a) : a ≤ nfp f a :=
  iterate_le_nfp f a 0

theorem lt_nfp {a b} : a < nfp f b ↔ ∃ n, a < f^[n] b := by
  rw [← sup_iterate_eq_nfp]
  exact lt_sup

theorem nfp_le_iff {a b} : nfp f a ≤ b ↔ ∀ n, f^[n] a ≤ b := by
  rw [← sup_iterate_eq_nfp]
  exact sup_le_iff

theorem nfp_le {a b} : (∀ n, f^[n] a ≤ b) → nfp f a ≤ b :=
  nfp_le_iff.2

@[simp]
theorem nfp_id : nfp id = id :=
  funext fun a => by
    simp_rw [← sup_iterate_eq_nfp, iterate_id]
    exact sup_const a

theorem nfp_monotone (hf : Monotone f) : Monotone (nfp f) :=
  nfpFamily_monotone fun _ => hf

theorem IsNormal.apply_lt_nfp {f} (H : IsNormal f) {a b} : f b < nfp f a ↔ b < nfp f a := by
  unfold nfp
  rw [← @apply_lt_nfpFamily_iff Unit (fun _ => f) _ (fun _ => H) a b]
  exact ⟨fun h _ => h, fun h => h Unit.unit⟩

theorem IsNormal.nfp_le_apply {f} (H : IsNormal f) {a b} : nfp f a ≤ f b ↔ nfp f a ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 H.apply_lt_nfp

theorem nfp_le_fp {f} (H : Monotone f) {a b} (ab : a ≤ b) (h : f b ≤ b) : nfp f a ≤ b :=
  nfpFamily_le_fp (fun _ => H) ab fun _ => h

theorem IsNormal.nfp_fp {f} (H : IsNormal f) : ∀ a, f (nfp f a) = nfp f a :=
  @nfpFamily_fp Unit (fun _ => f) Unit.unit H

theorem IsNormal.apply_le_nfp {f} (H : IsNormal f) {a b} : f b ≤ nfp f a ↔ b ≤ nfp f a :=
  ⟨le_trans (H.self_le _), fun h => by simpa only [H.nfp_fp] using H.le_iff.2 h⟩

theorem nfp_eq_self {f : Ordinal → Ordinal} {a} (h : f a = a) : nfp f a = a :=
  nfpFamily_eq_self fun _ => h

/-- The fixed point lemma for normal functions: any normal function has an unbounded set of
fixed points. -/
theorem fp_unbounded (H : IsNormal f) : (Function.fixedPoints f).Unbounded (· < ·) := by
  convert fp_family_unbounded fun _ : Unit => H
  exact (Set.iInter_const _).symm

/-- The derivative of a normal function `f` is the sequence of fixed points of `f`.

This is defined as `Ordinal.derivFamily` applied to a trivial family consisting only of `f`. -/
def deriv (f : Ordinal → Ordinal) : Ordinal → Ordinal :=
  derivFamily fun _ : Unit => f

theorem deriv_eq_derivFamily (f : Ordinal → Ordinal) : deriv f = derivFamily fun _ : Unit => f :=
  rfl

@[simp]
theorem deriv_zero (f) : deriv f 0 = nfp f 0 :=
  derivFamily_zero _

@[simp]
theorem deriv_succ (f o) : deriv f (succ o) = nfp f (succ (deriv f o)) :=
  derivFamily_succ _ _

theorem deriv_limit (f) {o} : IsLimit o → deriv f o = bsup.{u, 0} o fun a _ => deriv f a :=
  derivFamily_limit _

theorem deriv_isNormal (f) : IsNormal (deriv f) :=
  derivFamily_isNormal _

theorem deriv_id_of_nfp_id {f : Ordinal → Ordinal} (h : nfp f = id) : deriv f = id :=
  ((deriv_isNormal _).eq_iff_zero_and_succ IsNormal.refl).2 (by simp [h])

theorem IsNormal.deriv_fp {f} (H : IsNormal f) : ∀ o, f (deriv f o) = deriv f o :=
  @derivFamily_fp Unit (fun _ => f) Unit.unit H

theorem IsNormal.le_iff_deriv {f} (H : IsNormal f) {a} : f a ≤ a ↔ ∃ o, deriv f o = a := by
  unfold deriv
  rw [← le_iff_derivFamily fun _ : Unit => H]
  exact ⟨fun h _ => h, fun h => h Unit.unit⟩

theorem IsNormal.fp_iff_deriv {f} (H : IsNormal f) {a} : f a = a ↔ ∃ o, deriv f o = a := by
  rw [← H.le_iff_eq, H.le_iff_deriv]

/-- `Ordinal.deriv` enumerates the fixed points of a normal function. -/
theorem deriv_eq_enumOrd (H : IsNormal f) : deriv f = enumOrd (Function.fixedPoints f) := by
  convert derivFamily_eq_enumOrd fun _ : Unit => H
  exact (Set.iInter_const _).symm

theorem deriv_eq_id_of_nfp_eq_id {f : Ordinal → Ordinal} (h : nfp f = id) : deriv f = id :=
  (IsNormal.eq_iff_zero_and_succ (deriv_isNormal _) IsNormal.refl).2 <| by simp [h]

end

/-! ### Fixed points of addition -/


@[simp]
theorem nfp_add_zero (a) : nfp (a + ·) 0 = a * omega := by
  simp_rw [← sup_iterate_eq_nfp, ← sup_mul_nat]
  congr; funext n
  induction' n with n hn
  · rw [Nat.cast_zero, mul_zero, iterate_zero_apply]
  · rw [iterate_succ_apply', Nat.add_comm, Nat.cast_add, Nat.cast_one, mul_one_add, hn]

theorem nfp_add_eq_mul_omega {a b} (hba : b ≤ a * omega) : nfp (a + ·) b = a * omega := by
  apply le_antisymm (nfp_le_fp (add_isNormal a).monotone hba _)
  · rw [← nfp_add_zero]
    exact nfp_monotone (add_isNormal a).monotone (Ordinal.zero_le b)
  · dsimp; rw [← mul_one_add, one_add_omega]

theorem add_eq_right_iff_mul_omega_le {a b : Ordinal} : a + b = b ↔ a * omega ≤ b := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← nfp_add_zero a, ← deriv_zero]
    cases' (add_isNormal a).fp_iff_deriv.1 h with c hc
    rw [← hc]
    exact (deriv_isNormal _).monotone (Ordinal.zero_le _)
  · have := Ordinal.add_sub_cancel_of_le h
    nth_rw 1 [← this]
    rwa [← add_assoc, ← mul_one_add, one_add_omega]

theorem add_le_right_iff_mul_omega_le {a b : Ordinal} : a + b ≤ b ↔ a * omega ≤ b := by
  rw [← add_eq_right_iff_mul_omega_le]
  exact (add_isNormal a).le_iff_eq

theorem deriv_add_eq_mul_omega_add (a b : Ordinal.{u}) : deriv (a + ·) b = a * omega + b := by
  revert b
  rw [← funext_iff, IsNormal.eq_iff_zero_and_succ (deriv_isNormal _) (add_isNormal _)]
  refine ⟨?_, fun a h => ?_⟩
  · rw [deriv_zero, add_zero]
    exact nfp_add_zero a
  · rw [deriv_succ, h, add_succ]
    exact nfp_eq_self (add_eq_right_iff_mul_omega_le.2 ((le_add_right _ _).trans (le_succ _)))

/-! ### Fixed points of multiplication -/

-- Porting note: commented out, doesn't seem necessary
-- local infixr:0 "^" => @Pow.pow Ordinal Ordinal Ordinal.hasPow

@[simp]
theorem nfp_mul_one {a : Ordinal} (ha : 0 < a) : nfp (a * ·) 1 = (a^omega) := by
  rw [← sup_iterate_eq_nfp, ← sup_opow_nat]
  · dsimp
    congr
    funext n
    induction' n with n hn
    · rw [Nat.cast_zero, opow_zero, iterate_zero_apply]
    rw [iterate_succ_apply', Nat.add_comm, Nat.cast_add, Nat.cast_one, opow_add, opow_one, hn]
  · exact ha

@[simp]
theorem nfp_mul_zero (a : Ordinal) : nfp (a * ·) 0 = 0 := by
  rw [← Ordinal.le_zero, nfp_le_iff]
  intro n
  induction' n with n hn; · rfl
  dsimp only; rwa [iterate_succ_apply, mul_zero]

@[simp]
theorem nfp_zero_mul : nfp (HMul.hMul 0) = id := by
  rw [← sup_iterate_eq_nfp]
  refine funext fun a => (sup_le fun n => ?_).antisymm (le_sup (fun n => (0 * ·)^[n] a) 0)
  induction' n with n _
  · rfl
  rw [Function.iterate_succ']
  change 0 * _ ≤ a
  rw [zero_mul]
  exact Ordinal.zero_le a

@[simp]
theorem deriv_mul_zero : deriv (HMul.hMul 0) = id :=
  deriv_eq_id_of_nfp_eq_id nfp_zero_mul

theorem nfp_mul_eq_opow_omega {a b : Ordinal} (hb : 0 < b) (hba : b ≤ (a^omega)) :
    nfp (a * ·) b = (a^omega.{u}) := by
  rcases eq_zero_or_pos a with ha | ha
  · rw [ha, zero_opow omega_ne_zero] at hba ⊢
    rw [Ordinal.le_zero.1 hba, nfp_zero_mul]
    rfl
  apply le_antisymm
  · apply nfp_le_fp (mul_isNormal ha).monotone hba
    rw [← opow_one_add, one_add_omega]
  rw [← nfp_mul_one ha]
  exact nfp_monotone (mul_isNormal ha).monotone (one_le_iff_pos.2 hb)

theorem eq_zero_or_opow_omega_le_of_mul_eq_right {a b : Ordinal} (hab : a * b = b) :
    b = 0 ∨ (a^omega.{u}) ≤ b := by
  rcases eq_zero_or_pos a with ha | ha
  · rw [ha, zero_opow omega_ne_zero]
    exact Or.inr (Ordinal.zero_le b)
  rw [or_iff_not_imp_left]
  intro hb
  rw [← nfp_mul_one ha]
  rw [← Ne, ← one_le_iff_ne_zero] at hb
  exact nfp_le_fp (mul_isNormal ha).monotone hb (le_of_eq hab)

theorem mul_eq_right_iff_opow_omega_dvd {a b : Ordinal} : a * b = b ↔ (a^omega) ∣ b := by
  rcases eq_zero_or_pos a with ha | ha
  · rw [ha, zero_mul, zero_opow omega_ne_zero, zero_dvd_iff]
    exact eq_comm
  refine ⟨fun hab => ?_, fun h => ?_⟩
  · rw [dvd_iff_mod_eq_zero]
    rw [← div_add_mod b (a^omega), mul_add, ← mul_assoc, ← opow_one_add, one_add_omega,
      add_left_cancel] at hab
    cases' eq_zero_or_opow_omega_le_of_mul_eq_right hab with hab hab
    · exact hab
    refine (not_lt_of_le hab (mod_lt b (opow_ne_zero omega ?_))).elim
    rwa [← Ordinal.pos_iff_ne_zero]
  cases' h with c hc
  rw [hc, ← mul_assoc, ← opow_one_add, one_add_omega]

theorem mul_le_right_iff_opow_omega_dvd {a b : Ordinal} (ha : 0 < a) :
    a * b ≤ b ↔ (a^omega) ∣ b := by
  rw [← mul_eq_right_iff_opow_omega_dvd]
  exact (mul_isNormal ha).le_iff_eq

theorem nfp_mul_opow_omega_add {a c : Ordinal} (b) (ha : 0 < a) (hc : 0 < c) (hca : c ≤ (a^omega)) :
    nfp (a * ·) ((a^omega) * b + c) = (a^omega.{u}) * succ b := by
  apply le_antisymm
  · apply nfp_le_fp (mul_isNormal ha).monotone
    · rw [mul_succ]
      apply add_le_add_left hca
    · dsimp only; rw [← mul_assoc, ← opow_one_add, one_add_omega]
  · cases' mul_eq_right_iff_opow_omega_dvd.1 ((mul_isNormal ha).nfp_fp ((a^omega) * b + c)) with
      d hd
    rw [hd]
    apply mul_le_mul_left'
    have := le_nfp (Mul.mul a) ((a^omega) * b + c)
    erw [hd] at this
    have := (add_lt_add_left hc ((a^omega) * b)).trans_le this
    rw [add_zero, mul_lt_mul_iff_left (opow_pos omega ha)] at this
    rwa [succ_le_iff]

theorem deriv_mul_eq_opow_omega_mul {a : Ordinal.{u}} (ha : 0 < a) (b) :
    deriv (a * ·) b = (a^omega) * b := by
  revert b
  rw [← funext_iff,
    IsNormal.eq_iff_zero_and_succ (deriv_isNormal _) (mul_isNormal (opow_pos omega ha))]
  refine ⟨?_, fun c h => ?_⟩
  · dsimp only; rw [deriv_zero, nfp_mul_zero, mul_zero]
  · rw [deriv_succ, h]
    exact nfp_mul_opow_omega_add c ha zero_lt_one (one_le_iff_pos.2 (opow_pos _ ha))

end Ordinal
