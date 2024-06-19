/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Set.Subsingleton

#align_import computability.halting from "leanprover-community/mathlib"@"a50170a88a47570ed186b809ca754110590f9476"

/-!
# Computability theory and the halting problem

A universal partial recursive function, Rice's theorem, and the halting problem.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/


open Encodable Denumerable

namespace Nat.Partrec

open Computable Part

theorem merge' {f g} (hf : Nat.Partrec f) (hg : Nat.Partrec g) :
    ∃ h, Nat.Partrec h ∧
      ∀ a, (∀ x ∈ h a, x ∈ f a ∨ x ∈ g a) ∧ ((h a).Dom ↔ (f a).Dom ∨ (g a).Dom) := by
  obtain ⟨cf, rfl⟩ := Code.exists_code.1 hf
  obtain ⟨cg, rfl⟩ := Code.exists_code.1 hg
  have : Nat.Partrec fun n => Nat.rfindOpt fun k => cf.evaln k n <|> cg.evaln k n :=
    Partrec.nat_iff.1
      (Partrec.rfindOpt <|
        Primrec.option_orElse.to_comp.comp
          (Code.evaln_prim.to_comp.comp <| (snd.pair (const cf)).pair fst)
          (Code.evaln_prim.to_comp.comp <| (snd.pair (const cg)).pair fst))
  refine ⟨_, this, fun n => ?_⟩
  have : ∀ x ∈ rfindOpt fun k ↦ HOrElse.hOrElse (Code.evaln k cf n) fun _x ↦ Code.evaln k cg n,
      x ∈ Code.eval cf n ∨ x ∈ Code.eval cg n := by
    intro x h
    obtain ⟨k, e⟩ := Nat.rfindOpt_spec h
    revert e
    simp only [Option.mem_def]
    cases' e' : cf.evaln k n with y <;> simp <;> intro e
    · exact Or.inr (Code.evaln_sound e)
    · subst y
      exact Or.inl (Code.evaln_sound e')
  refine ⟨this, ⟨fun h => (this _ ⟨h, rfl⟩).imp Exists.fst Exists.fst, ?_⟩⟩
  intro h
  rw [Nat.rfindOpt_dom]
  simp only [dom_iff_mem, Code.evaln_complete, Option.mem_def] at h
  obtain ⟨x, k, e⟩ | ⟨x, k, e⟩ := h
  · refine ⟨k, x, ?_⟩
    simp only [e, Option.some_orElse, Option.mem_def]
  · refine ⟨k, ?_⟩
    cases' cf.evaln k n with y
    · exact ⟨x, by simp only [e, Option.mem_def, Option.none_orElse]⟩
    · exact ⟨y, by simp only [Option.some_orElse, Option.mem_def]⟩

#align nat.partrec.merge' Nat.Partrec.merge'

end Nat.Partrec

namespace Partrec

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

open Computable Part

open Nat.Partrec (Code)

open Nat.Partrec.Code

theorem merge' {f g : α →. σ} (hf : Partrec f) (hg : Partrec g) :
    ∃ k : α →. σ,
      Partrec k ∧ ∀ a, (∀ x ∈ k a, x ∈ f a ∨ x ∈ g a) ∧ ((k a).Dom ↔ (f a).Dom ∨ (g a).Dom) := by
  let ⟨k, hk, H⟩ := Nat.Partrec.merge' (bind_decode₂_iff.1 hf) (bind_decode₂_iff.1 hg)
  let k' (a : α) := (k (encode a)).bind fun n => (decode (α := σ) n : Part σ)
  refine
    ⟨k', ((nat_iff.2 hk).comp Computable.encode).bind (Computable.decode.ofOption.comp snd).to₂,
      fun a => ?_⟩
  have : ∀ x ∈ k' a, x ∈ f a ∨ x ∈ g a := by
    intro x h'
    simp only [k', exists_prop, mem_coe, mem_bind_iff, Option.mem_def] at h'
    obtain ⟨n, hn, hx⟩ := h'
    have := (H _).1 _ hn
    simp [mem_decode₂, encode_injective.eq_iff] at this
    obtain ⟨a', ha, rfl⟩ | ⟨a', ha, rfl⟩ := this <;> simp only [encodek, Option.some_inj] at hx <;>
      rw [hx] at ha
    · exact Or.inl ha
    · exact Or.inr ha
  refine ⟨this, ⟨fun h => (this _ ⟨h, rfl⟩).imp Exists.fst Exists.fst, ?_⟩⟩
  intro h
  rw [bind_dom]
  have hk : (k (encode a)).Dom :=
    (H _).2.2 (by simpa only [encodek₂, bind_some, coe_some] using h)
  exists hk
  simp only [exists_prop, mem_map_iff, mem_coe, mem_bind_iff, Option.mem_def] at H
  obtain ⟨a', _, y, _, e⟩ | ⟨a', _, y, _, e⟩ := (H _).1 _ ⟨hk, rfl⟩ <;>
    simp only [e.symm, encodek, coe_some, some_dom]
#align partrec.merge' Partrec.merge'

theorem merge {f g : α →. σ} (hf : Partrec f) (hg : Partrec g)
    (H : ∀ (a), ∀ x ∈ f a, ∀ y ∈ g a, x = y) :
    ∃ k : α →. σ, Partrec k ∧ ∀ a x, x ∈ k a ↔ x ∈ f a ∨ x ∈ g a :=
  let ⟨k, hk, K⟩ := merge' hf hg
  ⟨k, hk, fun a x =>
    ⟨(K _).1 _, fun h => by
      have : (k a).Dom := (K _).2.2 (h.imp Exists.fst Exists.fst)
      refine ⟨this, ?_⟩
      cases' h with h h <;> cases' (K _).1 _ ⟨this, rfl⟩ with h' h'
      · exact mem_unique h' h
      · exact (H _ _ h _ h').symm
      · exact H _ _ h' _ h
      · exact mem_unique h' h⟩⟩
#align partrec.merge Partrec.merge

theorem cond {c : α → Bool} {f : α →. σ} {g : α →. σ} (hc : Computable c) (hf : Partrec f)
    (hg : Partrec g) : Partrec fun a => cond (c a) (f a) (g a) :=
  let ⟨cf, ef⟩ := exists_code.1 hf
  let ⟨cg, eg⟩ := exists_code.1 hg
  ((eval_part.comp (Computable.cond hc (const cf) (const cg)) Computable.encode).bind
    ((@Computable.decode σ _).comp snd).ofOption.to₂).of_eq
    fun a => by cases c a <;> simp [ef, eg, encodek]
#align partrec.cond Partrec.cond

nonrec theorem sum_casesOn {f : α → Sum β γ} {g : α → β →. σ} {h : α → γ →. σ} (hf : Computable f)
    (hg : Partrec₂ g) (hh : Partrec₂ h) : @Partrec _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) :=
  option_some_iff.1 <|
    (cond (sum_casesOn hf (const true).to₂ (const false).to₂)
          (sum_casesOn_left hf (option_some_iff.2 hg).to₂ (const Option.none).to₂)
          (sum_casesOn_right hf (const Option.none).to₂ (option_some_iff.2 hh).to₂)).of_eq
      fun a => by cases f a <;> simp only [Bool.cond_true, Bool.cond_false]
#align partrec.sum_cases Partrec.sum_casesOn

end Partrec

/-- A computable predicate is one whose indicator function is computable. -/
def ComputablePred {α} [Primcodable α] (p : α → Prop) :=
  ∃ _ : DecidablePred p, Computable fun a => decide (p a)
#align computable_pred ComputablePred

/-- A recursively enumerable predicate is one which is the domain of a computable partial function.
 -/
def RePred {α} [Primcodable α] (p : α → Prop) :=
  Partrec fun a => Part.assert (p a) fun _ => Part.some ()
#align re_pred RePred

theorem RePred.of_eq {α} [Primcodable α] {p q : α → Prop} (hp : RePred p) (H : ∀ a, p a ↔ q a) :
    RePred q :=
  (funext fun a => propext (H a) : p = q) ▸ hp
#align re_pred.of_eq RePred.of_eq

theorem Partrec.dom_re {α β} [Primcodable α] [Primcodable β] {f : α →. β} (h : Partrec f) :
    RePred fun a => (f a).Dom :=
  (h.map (Computable.const ()).to₂).of_eq fun n => Part.ext fun _ => by simp [Part.dom_iff_mem]
#align partrec.dom_re Partrec.dom_re

theorem ComputablePred.of_eq {α} [Primcodable α] {p q : α → Prop} (hp : ComputablePred p)
    (H : ∀ a, p a ↔ q a) : ComputablePred q :=
  (funext fun a => propext (H a) : p = q) ▸ hp
#align computable_pred.of_eq ComputablePred.of_eq

namespace ComputablePred

variable {α : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable σ]

open Nat.Partrec (Code)

open Nat.Partrec.Code Computable

theorem computable_iff {p : α → Prop} :
    ComputablePred p ↔ ∃ f : α → Bool, Computable f ∧ p = fun a => (f a : Prop) :=
  ⟨fun ⟨D, h⟩ => ⟨_, h, funext fun a => propext (Bool.decide_iff _).symm⟩, by
    rintro ⟨f, h, rfl⟩; exact ⟨by infer_instance, by simpa using h⟩⟩
#align computable_pred.computable_iff ComputablePred.computable_iff

protected theorem not {p : α → Prop} (hp : ComputablePred p) : ComputablePred fun a => ¬p a := by
  obtain ⟨f, hf, rfl⟩ := computable_iff.1 hp
  exact
    ⟨by infer_instance,
      (cond hf (const false) (const true)).of_eq fun n => by
        simp only [Bool.not_eq_true]
        cases f n <;> rfl⟩
#align computable_pred.not ComputablePred.not

theorem to_re {p : α → Prop} (hp : ComputablePred p) : RePred p := by
  obtain ⟨f, hf, rfl⟩ := computable_iff.1 hp
  unfold RePred
  dsimp only []
  refine
    (Partrec.cond hf (Decidable.Partrec.const' (Part.some ())) Partrec.none).of_eq fun n =>
      Part.ext fun a => ?_
  cases a; cases f n <;> simp
#align computable_pred.to_re ComputablePred.to_re

/-- **Rice's Theorem** -/
theorem rice (C : Set (ℕ →. ℕ)) (h : ComputablePred fun c => eval c ∈ C) {f g} (hf : Nat.Partrec f)
    (hg : Nat.Partrec g) (fC : f ∈ C) : g ∈ C := by
  cases' h with _ h
  obtain ⟨c, e⟩ :=
    fixed_point₂
      (Partrec.cond (h.comp fst) ((Partrec.nat_iff.2 hg).comp snd).to₂
          ((Partrec.nat_iff.2 hf).comp snd).to₂).to₂
  simp only [Bool.cond_decide] at e
  by_cases H : eval c ∈ C
  · simp only [H, if_true] at e
    change (fun b => g b) ∈ C
    rwa [← e]
  · simp only [H, if_false] at e
    rw [e] at H
    contradiction
#align computable_pred.rice ComputablePred.rice

theorem rice₂ (C : Set Code) (H : ∀ cf cg, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C)) :
    (ComputablePred fun c => c ∈ C) ↔ C = ∅ ∨ C = Set.univ := by
  classical exact
      have hC : ∀ f, f ∈ C ↔ eval f ∈ eval '' C := fun f =>
        ⟨Set.mem_image_of_mem _, fun ⟨g, hg, e⟩ => (H _ _ e).1 hg⟩
      ⟨fun h =>
        or_iff_not_imp_left.2 fun C0 =>
          Set.eq_univ_of_forall fun cg =>
            let ⟨cf, fC⟩ := Set.nonempty_iff_ne_empty.2 C0
            (hC _).2 <|
              rice (eval '' C) (h.of_eq hC)
                (Partrec.nat_iff.1 <| eval_part.comp (const cf) Computable.id)
                (Partrec.nat_iff.1 <| eval_part.comp (const cg) Computable.id) ((hC _).1 fC),
        fun h => by {
          obtain rfl | rfl := h <;> simp [ComputablePred, Set.mem_empty_iff_false] <;>
            exact ⟨by infer_instance, Computable.const _⟩ }⟩
#align computable_pred.rice₂ ComputablePred.rice₂

/-- The Halting problem is recursively enumerable -/
theorem halting_problem_re (n) : RePred fun c => (eval c n).Dom :=
  (eval_part.comp Computable.id (Computable.const _)).dom_re
#align computable_pred.halting_problem_re ComputablePred.halting_problem_re

/-- The **Halting problem** is not computable -/
theorem halting_problem (n) : ¬ComputablePred fun c => (eval c n).Dom
  | h => rice { f | (f n).Dom } h Nat.Partrec.zero Nat.Partrec.none trivial
#align computable_pred.halting_problem ComputablePred.halting_problem

-- Post's theorem on the equivalence of r.e., co-r.e. sets and
-- computable sets. The assumption that p is decidable is required
-- unless we assume Markov's principle or LEM.
-- @[nolint decidable_classical]
theorem computable_iff_re_compl_re {p : α → Prop} [DecidablePred p] :
    ComputablePred p ↔ RePred p ∧ RePred fun a => ¬p a :=
  ⟨fun h => ⟨h.to_re, h.not.to_re⟩, fun ⟨h₁, h₂⟩ =>
    ⟨‹_›, by
      obtain ⟨k, pk, hk⟩ :=
        Partrec.merge (h₁.map (Computable.const true).to₂) (h₂.map (Computable.const false).to₂)
        (by
          intro a x hx y hy
          simp only [Part.mem_map_iff, Part.mem_assert_iff, Part.mem_some_iff, exists_prop,
            and_true, exists_const] at hx hy
          cases hy.1 hx.1)
      refine Partrec.of_eq pk fun n => Part.eq_some_iff.2 ?_
      rw [hk]
      simp only [Part.mem_map_iff, Part.mem_assert_iff, Part.mem_some_iff, exists_prop, and_true,
        true_eq_decide_iff, and_self, exists_const, false_eq_decide_iff]
      apply Decidable.em⟩⟩
#align computable_pred.computable_iff_re_compl_re ComputablePred.computable_iff_re_compl_re

theorem computable_iff_re_compl_re' {p : α → Prop} :
    ComputablePred p ↔ RePred p ∧ RePred fun a => ¬p a := by
  classical exact computable_iff_re_compl_re
#align computable_pred.computable_iff_re_compl_re' ComputablePred.computable_iff_re_compl_re'

theorem halting_problem_not_re (n) : ¬RePred fun c => ¬(eval c n).Dom
  | h => halting_problem _ <| computable_iff_re_compl_re'.2 ⟨halting_problem_re _, h⟩
#align computable_pred.halting_problem_not_re ComputablePred.halting_problem_not_re

end ComputablePred

namespace Nat

open Vector Part

/-- A simplified basis for `Partrec`. -/
inductive Partrec' : ∀ {n}, (Vector ℕ n →. ℕ) → Prop
  | prim {n f} : @Primrec' n f → @Partrec' n f
  | comp {m n f} (g : Fin n → Vector ℕ m →. ℕ) :
    Partrec' f → (∀ i, Partrec' (g i)) → Partrec' fun v => (mOfFn fun i => g i v) >>= f
  | rfind {n} {f : Vector ℕ (n + 1) → ℕ} :
    @Partrec' (n + 1) f → Partrec' fun v => rfind fun n => some (f (n ::ᵥ v) = 0)
#align nat.partrec' Nat.Partrec'

end Nat

namespace Nat.Partrec'

open Vector Partrec Computable

open Nat (Partrec')

open Nat.Partrec'

theorem to_part {n f} (pf : @Partrec' n f) : _root_.Partrec f := by
  induction pf with
  | prim hf => exact hf.to_prim.to_comp
  | comp _ _ _ hf hg => exact (Partrec.vector_mOfFn hg).bind (hf.comp snd)
  | rfind _ hf =>
    have := hf.comp (vector_cons.comp snd fst)
    have :=
      ((Primrec.eq.comp _root_.Primrec.id (_root_.Primrec.const 0)).to_comp.comp
        this).to₂.partrec₂
    exact _root_.Partrec.rfind this
#align nat.partrec'.to_part Nat.Partrec'.to_part

theorem of_eq {n} {f g : Vector ℕ n →. ℕ} (hf : Partrec' f) (H : ∀ i, f i = g i) : Partrec' g :=
  (funext H : f = g) ▸ hf
#align nat.partrec'.of_eq Nat.Partrec'.of_eq

theorem of_prim {n} {f : Vector ℕ n → ℕ} (hf : Primrec f) : @Partrec' n f :=
  prim (Nat.Primrec'.of_prim hf)
#align nat.partrec'.of_prim Nat.Partrec'.of_prim

theorem head {n : ℕ} : @Partrec' n.succ (@head ℕ n) :=
  prim Nat.Primrec'.head
#align nat.partrec'.head Nat.Partrec'.head

theorem tail {n f} (hf : @Partrec' n f) : @Partrec' n.succ fun v => f v.tail :=
  (hf.comp _ fun i => @prim _ _ <| Nat.Primrec'.get i.succ).of_eq fun v => by
    simp; rw [← ofFn_get v.tail]; congr; funext i; simp
#align nat.partrec'.tail Nat.Partrec'.tail

protected theorem bind {n f g} (hf : @Partrec' n f) (hg : @Partrec' (n + 1) g) :
    @Partrec' n fun v => (f v).bind fun a => g (a ::ᵥ v) :=
  (@comp n (n + 1) g (fun i => Fin.cases f (fun i v => some (v.get i)) i) hg fun i => by
        refine Fin.cases ?_ (fun i => ?_) i <;> simp [*]
        exact prim (Nat.Primrec'.get _)).of_eq
    fun v => by simp [mOfFn, Part.bind_assoc, pure]
#align nat.partrec'.bind Nat.Partrec'.bind

protected theorem map {n f} {g : Vector ℕ (n + 1) → ℕ} (hf : @Partrec' n f)
    (hg : @Partrec' (n + 1) g) : @Partrec' n fun v => (f v).map fun a => g (a ::ᵥ v) := by
  simp [(Part.bind_some_eq_map _ _).symm]; exact hf.bind hg
#align nat.partrec'.map Nat.Partrec'.map

/-- Analogous to `Nat.Partrec'` for `ℕ`-valued functions, a predicate for partial recursive
  vector-valued functions. -/
def Vec {n m} (f : Vector ℕ n → Vector ℕ m) :=
  ∀ i, Partrec' fun v => (f v).get i
#align nat.partrec'.vec Nat.Partrec'.Vec

nonrec theorem Vec.prim {n m f} (hf : @Nat.Primrec'.Vec n m f) : Vec f := fun i => prim <| hf i
#align nat.partrec'.vec.prim Nat.Partrec'.Vec.prim

protected theorem nil {n} : @Vec n 0 fun _ => nil := fun i => i.elim0
#align nat.partrec'.nil Nat.Partrec'.nil

protected theorem cons {n m} {f : Vector ℕ n → ℕ} {g} (hf : @Partrec' n f) (hg : @Vec n m g) :
    Vec fun v => f v ::ᵥ g v := fun i =>
  Fin.cases (by simpa using hf) (fun i => by simp only [hg i, get_cons_succ]) i
#align nat.partrec'.cons Nat.Partrec'.cons

theorem idv {n} : @Vec n n id :=
  Vec.prim Nat.Primrec'.idv
#align nat.partrec'.idv Nat.Partrec'.idv

theorem comp' {n m f g} (hf : @Partrec' m f) (hg : @Vec n m g) : Partrec' fun v => f (g v) :=
  (hf.comp _ hg).of_eq fun v => by simp
#align nat.partrec'.comp' Nat.Partrec'.comp'

theorem comp₁ {n} (f : ℕ →. ℕ) {g : Vector ℕ n → ℕ} (hf : @Partrec' 1 fun v => f v.head)
    (hg : @Partrec' n g) : @Partrec' n fun v => f (g v) := by
  simpa using hf.comp' (Partrec'.cons hg Partrec'.nil)
#align nat.partrec'.comp₁ Nat.Partrec'.comp₁

theorem rfindOpt {n} {f : Vector ℕ (n + 1) → ℕ} (hf : @Partrec' (n + 1) f) :
    @Partrec' n fun v => Nat.rfindOpt fun a => ofNat (Option ℕ) (f (a ::ᵥ v)) :=
  ((rfind <|
        (of_prim (Primrec.nat_sub.comp (_root_.Primrec.const 1) Primrec.vector_head)).comp₁
          (fun n => Part.some (1 - n)) hf).bind
    ((prim Nat.Primrec'.pred).comp₁ Nat.pred hf)).of_eq
    fun v =>
    Part.ext fun b => by
      simp only [Nat.rfindOpt, exists_prop, tsub_eq_zero_iff_le, PFun.coe_val, Part.mem_bind_iff,
        Part.mem_some_iff, Option.mem_def, Part.mem_coe]
      refine
        exists_congr fun a => (and_congr (iff_of_eq ?_) Iff.rfl).trans (and_congr_right fun h => ?_)
      · congr
        funext n
        cases f (n ::ᵥ v) <;> simp [Nat.succ_le_succ] <;> rfl
      · have := Nat.rfind_spec h
        simp only [Part.coe_some, Part.mem_some_iff] at this
        revert this; cases' f (a ::ᵥ v) with c <;> intro this
        · cases this
        rw [← Option.some_inj, eq_comm]
        rfl
#align nat.partrec'.rfind_opt Nat.Partrec'.rfindOpt

open Nat.Partrec.Code

theorem of_part : ∀ {n f}, _root_.Partrec f → @Partrec' n f :=
  @(suffices ∀ f, Nat.Partrec f → @Partrec' 1 fun v => f v.head from fun {n f} hf => by
      let g := fun n₁ =>
        (Part.ofOption (decode (α := Vector ℕ n) n₁)).bind (fun a => Part.map encode (f a))
      exact
        (comp₁ g (this g hf) (prim Nat.Primrec'.encode)).of_eq fun i => by
          dsimp only [g]; simp [encodek, Part.map_id']
    fun f hf => by
    obtain ⟨c, rfl⟩ := exists_code.1 hf
    simpa [eval_eq_rfindOpt] using
      rfindOpt <|
        of_prim <|
          Primrec.encode_iff.2 <|
            evaln_prim.comp <|
              (Primrec.vector_head.pair (_root_.Primrec.const c)).pair <|
                Primrec.vector_head.comp Primrec.vector_tail)
#align nat.partrec'.of_part Nat.Partrec'.of_part

theorem part_iff {n f} : @Partrec' n f ↔ _root_.Partrec f :=
  ⟨to_part, of_part⟩
#align nat.partrec'.part_iff Nat.Partrec'.part_iff

theorem part_iff₁ {f : ℕ →. ℕ} : (@Partrec' 1 fun v => f v.head) ↔ _root_.Partrec f :=
  part_iff.trans
    ⟨fun h =>
      (h.comp <| (Primrec.vector_ofFn fun _ => _root_.Primrec.id).to_comp).of_eq fun v => by
        simp only [id, head_ofFn],
      fun h => h.comp vector_head⟩
#align nat.partrec'.part_iff₁ Nat.Partrec'.part_iff₁

theorem part_iff₂ {f : ℕ → ℕ →. ℕ} : (@Partrec' 2 fun v => f v.head v.tail.head) ↔ Partrec₂ f :=
  part_iff.trans
    ⟨fun h =>
      (h.comp <| vector_cons.comp fst <| vector_cons.comp snd (const nil)).of_eq fun v => by
        simp only [head_cons, tail_cons],
      fun h => h.comp vector_head (vector_head.comp vector_tail)⟩
#align nat.partrec'.part_iff₂ Nat.Partrec'.part_iff₂

theorem vec_iff {m n f} : @Vec m n f ↔ Computable f :=
  ⟨fun h => by simpa only [ofFn_get] using vector_ofFn fun i => to_part (h i), fun h i =>
    of_part <| vector_get.comp h (const i)⟩
#align nat.partrec'.vec_iff Nat.Partrec'.vec_iff

end Nat.Partrec'
