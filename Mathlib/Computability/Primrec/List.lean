/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Logic.Encodable.Pi

/-!
# Primitive recursive functions on Lists

The primitive recursive functions are defined in `Mathlib.Computability.Primrec.Basic`.
This file contains definitions and theorems about primitive recursive functions that
relate to operation on lists.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

@[expose] public section

open List (Vector)
open Denumerable Encodable Function


section

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]
variable (H : Nat.Primrec fun n => Encodable.encode (@decode (List β) _ n))

open Primrec

set_option backward.privateInPublic true in
private def prim : Primcodable (List β) := ⟨H⟩

private theorem list_casesOn' {f : α → List β} {g : α → σ} {h : α → β × List β → σ}
    (hf : haveI := prim H; Primrec f) (hg : Primrec g) (hh : haveI := prim H; Primrec₂ h) :
    @Primrec _ σ _ _ fun a => List.casesOn (f a) (g a) fun b l => h a (b, l) :=
  letI := prim H
  have :
    @Primrec _ (Option σ) _ _ fun a =>
      (@decode (Option (β × List β)) _ (encode (f a))).map fun o => Option.casesOn o (g a) (h a) :=
    ((@map_decode_iff _ (Option (β × List β)) _ _ _ _ _).2 <|
      to₂ <|
        option_casesOn snd (hg.comp fst) (hh.comp₂ (fst.comp₂ Primrec₂.left) Primrec₂.right)).comp
      .id (encode_iff.2 hf)
  option_some_iff.1 <| this.of_eq fun a => by rcases f a with - | ⟨b, l⟩ <;> simp [encodek]

set_option backward.privateInPublic true in
private theorem list_foldl' {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : haveI := prim H; Primrec f) (hg : Primrec g) (hh : haveI := prim H; Primrec₂ h) :
    Primrec fun a => (f a).foldl (fun s b => h a (s, b)) (g a) := by
  letI := prim H
  let G (a : α) (IH : σ × List β) : σ × List β := List.casesOn IH.2 IH fun b l => (h a (IH.1, b), l)
  have hG : Primrec₂ G := list_casesOn' H (snd.comp snd) snd <|
    to₂ <|
    pair (hh.comp (fst.comp fst) <| pair ((fst.comp snd).comp fst) (fst.comp snd))
      (snd.comp snd)
  let F := fun (a : α) (n : ℕ) => (G a)^[n] (g a, f a)
  have hF : Primrec fun a => (F a (encode (f a))).1 :=
    (fst.comp <|
      nat_iterate (encode_iff.2 hf) (pair hg hf) <|
      hG)
  suffices ∀ a n, F a n = (((f a).take n).foldl (fun s b => h a (s, b)) (g a), (f a).drop n) by
    refine hF.of_eq fun a => ?_
    rw [this, List.take_of_length_le (length_le_encode _)]
  introv
  dsimp only [F]
  generalize f a = l
  generalize g a = x
  induction n generalizing l x with
  | zero => rfl
  | succ n IH =>
    simp only [iterate_succ, comp_apply]
    rcases l with - | ⟨b, l⟩ <;> simp [G, IH]

set_option backward.privateInPublic true in
private theorem list_cons' : (haveI := prim H; Primrec₂ (@List.cons β)) :=
  letI := prim H
  encode_iff.1 (succ.comp <| Primrec₂.natPair.comp (encode_iff.2 fst) (encode_iff.2 snd))

set_option backward.privateInPublic true in
private theorem list_reverse' :
    haveI := prim H
    Primrec (@List.reverse β) :=
  letI := prim H
  (list_foldl' H .id (const []) <| to₂ <| ((list_cons' H).comp snd fst).comp snd).of_eq
    (suffices ∀ l r, List.foldl (fun (s : List β) (b : β) => b :: s) r l = List.reverseAux l r from
      fun l => this l []
    fun l => by induction l <;> simp [*, List.reverseAux])

end

namespace Primcodable

variable {α : Type*} {β : Type*}
variable [Primcodable α] [Primcodable β]

open Primrec

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
instance list : Primcodable (List α) :=
  ⟨letI H := Primcodable.prim (List ℕ)
    have : Primrec₂ fun (a : α) (o : Option (List ℕ)) => o.map (List.cons (encode a)) :=
      option_map snd <| (list_cons' H).comp ((@Primrec.encode α _).comp (fst.comp fst)) snd
    have :
      Primrec fun n =>
        (ofNat (List ℕ) n).reverse.foldl
          (fun o m => (@decode α _ m).bind fun a => o.map (List.cons (encode a))) (some []) :=
      list_foldl' H ((list_reverse' H).comp (.ofNat (List ℕ))) (const (some []))
        (Primrec.comp₂ (bind_decode_iff.2 <| .swap this) Primrec₂.right)
    nat_iff.1 <|
      (encode_iff.2 this).of_eq fun n => by
        rw [List.foldl_reverse]
        apply Nat.case_strong_induction_on n; · simp
        intro n IH; simp
        rcases @decode α _ n.unpair.1 with - | a; · rfl
        simp only [Option.bind_some, Option.map_some]
        suffices ∀ (o : Option (List ℕ)) (p), encode o = encode p →
            encode (Option.map (List.cons (encode a)) o) = encode (Option.map (List.cons a) p) from
          this _ _ (IH _ (Nat.unpair_right_le n))
        intro o p IH
        cases o <;> cases p
        · rfl
        · injection IH
        · injection IH
        · exact congr_arg (fun k => (Nat.pair (encode a) k).succ.succ) (Nat.succ.inj IH)⟩
end Primcodable

namespace Primrec

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

theorem list_cons : Primrec₂ (@List.cons α) :=
  list_cons' (Primcodable.prim _)

theorem list_casesOn {f : α → List β} {g : α → σ} {h : α → β × List β → σ} :
    Primrec f →
      Primrec g →
        Primrec₂ h → @Primrec _ σ _ _ fun a => List.casesOn (f a) (g a) fun b l => h a (b, l) :=
  list_casesOn' (Primcodable.prim _)

theorem list_foldl {f : α → List β} {g : α → σ} {h : α → σ × β → σ} :
    Primrec f →
      Primrec g → Primrec₂ h → Primrec fun a => (f a).foldl (fun s b => h a (s, b)) (g a) :=
  list_foldl' (Primcodable.prim _)

theorem list_reverse : Primrec (@List.reverse α) :=
  list_reverse' (Primcodable.prim _)

theorem list_foldr {f : α → List β} {g : α → σ} {h : α → β × σ → σ} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec fun a => (f a).foldr (fun b s => h a (b, s)) (g a) :=
  (list_foldl (list_reverse.comp hf) hg <| to₂ <| hh.comp fst <| (pair snd fst).comp snd).of_eq
    fun a => by simp [List.foldl_reverse]

theorem list_head? : Primrec (@List.head? α) :=
  (list_casesOn .id (const none) (option_some_iff.2 <| fst.comp snd).to₂).of_eq fun l => by
    cases l <;> rfl

theorem list_headI [Inhabited α] : Primrec (@List.headI α _) :=
  (option_getD_default.comp list_head?).of_eq fun l => l.head!_eq_head?_getD.symm

theorem list_tail : Primrec (@List.tail α) :=
  (list_casesOn .id (const []) (snd.comp snd).to₂).of_eq fun l => by cases l <;> rfl

theorem list_rec {f : α → List β} {g : α → σ} {h : α → β × List β × σ → σ} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec₂ h) :
    @Primrec _ σ _ _ fun a => List.recOn (f a) (g a) fun b l IH => h a (b, l, IH) :=
  let F (a : α) := (f a).foldr (fun (b : β) (s : List β × σ) => (b :: s.1, h a (b, s))) ([], g a)
  have : Primrec F :=
    list_foldr hf (pair (const []) hg) <|
      to₂ <| pair ((list_cons.comp fst (fst.comp snd)).comp snd) hh
  (snd.comp this).of_eq fun a => by
    suffices F a = (f a, List.recOn (f a) (g a) fun b l IH => h a (b, l, IH)) by rw [this]
    dsimp [F]
    induction f a <;> simp [*]

theorem list_getElem? : Primrec₂ ((·[·]? : List α → ℕ → Option α)) :=
  let F (l : List α) (n : ℕ) :=
    l.foldl
      (fun (s : ℕ ⊕ α) (a : α) =>
        Sum.casesOn s (@Nat.casesOn (fun _ => ℕ ⊕ α) · (Sum.inr a) Sum.inl) Sum.inr)
      (Sum.inl n)
  have hF : Primrec₂ F :=
    (list_foldl fst (sumInl.comp snd)
      ((sumCasesOn fst (nat_casesOn snd (sumInr.comp <| snd.comp fst) (sumInl.comp snd).to₂).to₂
              (sumInr.comp snd).to₂).comp
          snd).to₂).to₂
  have :
    @Primrec _ (Option α) _ _ fun p : List α × ℕ => Sum.casesOn (F p.1 p.2) (fun _ => none) some :=
    sumCasesOn hF (const none).to₂ (option_some.comp snd).to₂
  this.to₂.of_eq fun l n => by
    dsimp; symm
    induction l generalizing n with
    | nil => rfl
    | cons a l IH =>
      rcases n with - | n
      · dsimp [F]
        clear IH
        induction l <;> simp_all
      · simpa using IH ..

theorem list_getD (d : α) : Primrec₂ fun l n => List.getD l n d := by
  simp only [List.getD_eq_getElem?_getD]
  exact option_getD.comp₂ list_getElem? (const _)

theorem list_getI [Inhabited α] : Primrec₂ (@List.getI α _) :=
  list_getD _

theorem list_append : Primrec₂ ((· ++ ·) : List α → List α → List α) :=
  (list_foldr fst snd <| to₂ <| comp (@list_cons α _) snd).to₂.of_eq fun l₁ l₂ => by
    induction l₁ <;> simp [*]

theorem list_concat : Primrec₂ fun l (a : α) => l ++ [a] :=
  list_append.comp fst (list_cons.comp snd (const []))

theorem list_map {f : α → List β} {g : α → β → σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).map (g a) :=
  (list_foldr hf (const []) <|
        to₂ <| list_cons.comp (hg.comp fst (fst.comp snd)) (snd.comp snd)).of_eq
    fun a => by induction f a <;> simp [*]

theorem list_range : Primrec List.range :=
  (nat_rec' .id (const []) ((list_concat.comp snd fst).comp snd).to₂).of_eq fun n => by
    simp; induction n <;> simp [*, List.range_succ]

theorem list_flatten : Primrec (@List.flatten α) :=
  (list_foldr .id (const []) <| to₂ <| comp (@list_append α _) snd).of_eq fun l => by
    dsimp; induction l <;> simp [*]

theorem list_flatMap {f : α → List β} {g : α → β → List σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).flatMap (g a)) := list_flatten.comp (list_map hf hg)

theorem optionToList : Primrec (Option.toList : Option α → List α) :=
  (option_casesOn Primrec.id (const [])
    ((list_cons.comp Primrec.id (const [])).comp₂ Primrec₂.right)).of_eq
  (fun o => by rcases o <;> simp)

theorem listFilterMap {f : α → List β} {g : α → β → Option σ}
    (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).filterMap (g a) :=
  (list_flatMap hf (comp₂ optionToList hg)).of_eq
    fun _ ↦ Eq.symm <| List.filterMap_eq_flatMap_toList _ _

variable {p : α → Prop} [DecidablePred p]

theorem list_length : Primrec (@List.length α) :=
  (list_foldr (@Primrec.id (List α) _) (const 0) <| to₂ <| (succ.comp <| snd.comp snd).to₂).of_eq
    fun l => by dsimp; induction l <;> simp [*]

/-- Filtering a list for elements that satisfy a decidable predicate is primitive recursive. -/
theorem listFilter (hf : PrimrecPred p) : Primrec fun L ↦ List.filter (p ·) L := by
  rw [← List.filterMap_eq_filter]
  apply listFilterMap .id
  simp only [Primrec₂, Option.guard, decide_eq_true_eq]
  exact ite (hf.comp snd) (option_some_iff.mpr snd) (const none)

theorem list_findIdx {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec fun a => (f a).findIdx (p a) :=
  (list_foldr hf (const 0) <|
        to₂ <| cond (hp.comp fst <| fst.comp snd) (const 0) (succ.comp <| snd.comp snd)).of_eq
    fun a => by dsimp; induction f a <;> simp [List.findIdx_cons, *]

theorem list_idxOf [DecidableEq α] : Primrec₂ (@List.idxOf α _) :=
  to₂ <| list_findIdx snd <| Primrec.beq.comp₂ snd.to₂ (fst.comp fst).to₂

theorem nat_strong_rec (f : α → ℕ → σ) {g : α → List σ → Option σ} (hg : Primrec₂ g)
    (H : ∀ a n, g a ((List.range n).map (f a)) = some (f a n)) : Primrec₂ f :=
  suffices Primrec₂ fun a n => (List.range n).map (f a) from
    Primrec₂.option_some_iff.1 <|
      (list_getElem?.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq fun a n => by
        simp
  Primrec₂.option_some_iff.1 <|
    (nat_rec (const (some []))
          (to₂ <|
            option_bind (snd.comp snd) <|
              to₂ <|
                option_map (hg.comp (fst.comp fst) snd)
                  (to₂ <| list_concat.comp (snd.comp fst) snd))).of_eq
      fun a n => by
      induction n with
      | zero => rfl
      | succ n IH => simp [IH, H, List.range_succ]

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
theorem listLookup [DecidableEq α] : Primrec₂ (List.lookup : α → List (α × β) → Option β) :=
  (to₂ <| list_rec snd (const none) <|
    to₂ <|
      cond (Primrec.beq.comp (fst.comp fst) (fst.comp <| fst.comp snd))
        (option_some.comp <| snd.comp <| fst.comp snd)
        (snd.comp <| snd.comp snd)).of_eq
  fun a ps => by
  induction ps with simp [List.lookup, *]
  | cons p ps ih => cases ha : a == p.1 <;> simp

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
theorem nat_omega_rec' (f : β → σ) {m : β → ℕ} {l : β → List β} {g : β → List σ → Option σ}
    (hm : Primrec m) (hl : Primrec l) (hg : Primrec₂ g)
    (Ord : ∀ b, ∀ b' ∈ l b, m b' < m b)
    (H : ∀ b, g b ((l b).map f) = some (f b)) : Primrec f := by
  haveI : DecidableEq β := Encodable.decidableEqOfEncodable β
  let mapGraph (M : List (β × σ)) (bs : List β) : List σ := bs.flatMap (Option.toList <| M.lookup ·)
  let bindList (b : β) : ℕ → List β := fun n ↦ n.rec [b] fun _ bs ↦ bs.flatMap l
  let graph (b : β) : ℕ → List (β × σ) := fun i ↦ i.rec [] fun i ih ↦
    (bindList b (m b - i)).filterMap fun b' ↦ (g b' <| mapGraph ih (l b')).map (b', ·)
  have mapGraph_primrec : Primrec₂ mapGraph :=
    to₂ <| list_flatMap snd <| optionToList.comp₂ <| listLookup.comp₂ .right (fst.comp₂ .left)
  have bindList_primrec : Primrec₂ (bindList) :=
    nat_rec' snd
      (list_cons.comp fst (const []))
      (to₂ <| list_flatMap (snd.comp snd) (hl.comp₂ .right))
  have graph_primrec : Primrec₂ (graph) :=
    to₂ <| nat_rec' snd (const []) <|
      to₂ <| listFilterMap
        (bindList_primrec.comp
          (fst.comp fst)
          (nat_sub.comp (hm.comp <| fst.comp fst) (fst.comp snd))) <|
            to₂ <| option_map
              (hg.comp snd (mapGraph_primrec.comp (snd.comp <| snd.comp fst) (hl.comp snd)))
              (Primrec₂.pair.comp₂ (snd.comp₂ .left) .right)
  have : Primrec (fun b => (graph b (m b + 1))[0]?.map Prod.snd) :=
    option_map (list_getElem?.comp (graph_primrec.comp Primrec.id (succ.comp hm)) (const 0))
      (snd.comp₂ Primrec₂.right)
  exact option_some_iff.mp <| this.of_eq <| fun b ↦ by
    have graph_eq_map_bindList (i : ℕ) (hi : i ≤ m b + 1) :
        graph b i = (bindList b (m b + 1 - i)).map fun x ↦ (x, f x) := by
      have bindList_eq_nil : bindList b (m b + 1) = [] :=
        have bindList_m_lt (k : ℕ) : ∀ b' ∈ bindList b k, m b' < m b + 1 - k := by
          induction k with simp [bindList]
          | succ k ih =>
            grind
        List.eq_nil_iff_forall_not_mem.mpr
          (by intro b' ha'; by_contra; simpa using bindList_m_lt (m b + 1) b' ha')
      have mapGraph_graph {bs bs' : List β} (has : bs' ⊆ bs) :
          mapGraph (bs.map <| fun x => (x, f x)) bs' = bs'.map f := by
        induction bs' with simp [mapGraph]
        | cons b bs' ih =>
          have : b ∈ bs ∧ bs' ⊆ bs := by simpa using has
          rcases this with ⟨ha, has'⟩
          simpa [List.lookup_graph f ha] using ih has'
      have graph_succ : ∀ i, graph b (i + 1) =
        (bindList b (m b - i)).filterMap fun b' =>
          (g b' <| mapGraph (graph b i) (l b')).map (b', ·) := fun _ => rfl
      have bindList_succ : ∀ i, bindList b (i + 1) = (bindList b i).flatMap l := fun _ => rfl
      induction i with
      | zero => symm; simpa [graph] using bindList_eq_nil
      | succ i ih =>
        simp only [graph_succ, ih (Nat.le_of_lt hi), Nat.succ_sub (Nat.le_of_lt_succ hi),
          Nat.succ_eq_add_one, bindList_succ, Nat.reduceSubDiff]
        apply List.filterMap_eq_map_iff_forall_eq_some.mpr
        intro b' ha'; simp; rw [mapGraph_graph]
        · exact H b'
        · exact (List.infix_flatMap_of_mem ha' l).subset
    simp [graph_eq_map_bindList (m b + 1) (Nat.le_refl _), bindList]

theorem nat_omega_rec (f : α → β → σ) {m : α → β → ℕ}
    {l : α → β → List β} {g : α → β × List σ → Option σ}
    (hm : Primrec₂ m) (hl : Primrec₂ l) (hg : Primrec₂ g)
    (Ord : ∀ a b, ∀ b' ∈ l a b, m a b' < m a b)
    (H : ∀ a b, g a (b, (l a b).map (f a)) = some (f a b)) : Primrec₂ f :=
  Primrec₂.uncurry.mp <|
    nat_omega_rec' (Function.uncurry f)
      (Primrec₂.uncurry.mpr hm)
      (list_map (hl.comp fst snd) (Primrec₂.pair.comp₂ (fst.comp₂ .left) .right))
      (hg.comp₂ (fst.comp₂ .left) (Primrec₂.pair.comp₂ (snd.comp₂ .left) .right))
      (by simpa using Ord) (by simpa [Function.comp] using H)

end Primrec

namespace PrimrecPred

open List Primrec

variable {α β : Type*} {p : α → Prop} {L : List α} {b : β}

variable [Primcodable α] [Primcodable β]

/-- Checking if any element of a list satisfies a decidable predicate is primitive recursive. -/
theorem exists_mem_list : (hf : PrimrecPred p) → PrimrecPred fun L : List α ↦ ∃ a ∈ L, p a
  | ⟨_, hf⟩ => .of_eq
      (.not <| Primrec.eq.comp (list_length.comp <| listFilter hf.primrecPred) (const 0)) <| by simp

/-- Checking if every element of a list satisfies a decidable predicate is primitive recursive. -/
theorem forall_mem_list : (hf : PrimrecPred p) → PrimrecPred fun L : List α ↦ ∀ a ∈ L, p a
  | ⟨_, hf⟩ => .of_eq
      (Primrec.eq.comp (list_length.comp <| listFilter hf.primrecPred) (list_length)) <| by simp

variable {p : ℕ → Prop}

/-- Bounded existential quantifiers are primitive recursive. -/
theorem exists_lt (hf : PrimrecPred p) : PrimrecPred fun n ↦ ∃ x < n, p x :=
  of_eq (hf.exists_mem_list.comp list_range) (by simp)

/-- Bounded universal quantifiers are primitive recursive. -/
theorem forall_lt (hf : PrimrecPred p) : PrimrecPred fun n ↦ ∀ x < n, p x :=
  of_eq (hf.forall_mem_list.comp list_range) (by simp)

/-- A helper lemma for proofs about bounded quantifiers on decidable relations. -/
theorem listFilter_listRange {R : ℕ → ℕ → Prop} (s : ℕ) [DecidableRel R] (hf : PrimrecRel R) :
    Primrec fun n ↦ (range s).filter (fun y ↦ R y n) := by
  simp only [← filterMap_eq_filter]
  refine listFilterMap (.const (range s)) ?_
  refine ite (Primrec.eq.comp ?_ (const true)) (option_some_iff.mpr snd) (.const Option.none)
  exact hf.decide.comp snd fst

end PrimrecPred

namespace PrimrecRel

open Primrec List PrimrecPred

variable {α β : Type*} {R : α → β → Prop} {L : List α} {b : β}

variable [Primcodable α] [Primcodable β]

/-- If `R a b` is decidable, then given `L : List α` and `b : β`, it is primitive recursive
to filter `L` for elements `a` with `R a b` -/
theorem listFilter (hf : PrimrecRel R) [DecidableRel R] :
    Primrec₂ fun (L : List α) b ↦ L.filter (fun a ↦ R a b) := by
  simp only [← List.filterMap_eq_filter]
  refine listFilterMap fst (Primrec.ite ?_ ?_ (Primrec.const Option.none))
  · exact Primrec.eq.comp (hf.decide.comp snd (snd.comp fst)) (.const true)
  · exact (option_some).comp snd

/-- If `R a b` is decidable, then given `L : List α` and `b : β`, `g L b ↔ ∃ a L, R a b`
is a primitive recursive relation. -/
theorem exists_mem_list (hf : PrimrecRel R) : PrimrecRel fun (L : List α) b ↦ ∃ a ∈ L, R a b := by
  classical
  have h (L) (b) : (List.filter (R · b) L).length ≠ 0 ↔ ∃ a ∈ L, R a b := by simp
  refine .of_eq (.not ?_) h
  exact Primrec.eq.comp (list_length.comp hf.listFilter) (const 0)

/-- If `R a b` is decidable, then given `L : List α` and `b : β`, `g L b ↔ ∀ a L, R a b`
is a primitive recursive relation. -/
theorem forall_mem_list (hf : PrimrecRel R) : PrimrecRel fun (L : List α) b ↦ ∀ a ∈ L, R a b := by
  classical
  have h (L) (b) : (List.filter (R · b) L).length = L.length ↔ ∀ a ∈ L, R a b := by simp
  apply PrimrecRel.of_eq ?_ h
  exact (Primrec.eq.comp (list_length.comp <| PrimrecRel.listFilter hf) (.comp list_length fst))

variable {R : ℕ → ℕ → Prop}

/-- If `R a b` is decidable, then for any fixed `n` and `y`, `g n y ↔ ∃ x < n, R x y` is a
primitive recursive relation. -/
theorem exists_lt (hf : PrimrecRel R) : PrimrecRel fun n y ↦ ∃ x < n, R x y :=
  (hf.exists_mem_list.comp (list_range.comp fst) snd).of_eq (by simp)

/-- If `R a b` is decidable, then for any fixed `n` and `y`, `g n y ↔ ∀ x < n, R x y` is a
primitive recursive relation. -/
theorem forall_lt (hf : PrimrecRel R) : PrimrecRel fun n y ↦ ∀ x < n, R x y :=
  (hf.forall_mem_list.comp (list_range.comp fst) snd).of_eq (by simp)

end PrimrecRel

namespace Primcodable

variable {α : Type*} [Primcodable α]

open Primrec

instance vector {n} : Primcodable (List.Vector α n) :=
  subtype ((@Primrec.eq ℕ _).comp list_length (const _))

instance finArrow {n} : Primcodable (Fin n → α) :=
  ofEquiv _ (Equiv.vectorEquivFin _ _).symm

end Primcodable

namespace Primrec

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

theorem vector_toList {n} : Primrec (@List.Vector.toList α n) :=
  subtype_val

theorem vector_toList_iff {n} {f : α → List.Vector β n} :
    (Primrec fun a => (f a).toList) ↔ Primrec f :=
  subtype_val_iff

theorem vector_cons {n} : Primrec₂ (@List.Vector.cons α n) :=
  vector_toList_iff.1 <| by simpa using list_cons.comp fst (vector_toList_iff.2 snd)

theorem vector_length {n} : Primrec (@List.Vector.length α n) :=
  const _

theorem vector_head {n} : Primrec (@List.Vector.head α n) :=
  option_some_iff.1 <| (list_head?.comp vector_toList).of_eq fun ⟨_ :: _, _⟩ => rfl

theorem vector_tail {n} : Primrec (@List.Vector.tail α n) :=
  vector_toList_iff.1 <| (list_tail.comp vector_toList).of_eq fun ⟨l, h⟩ => by cases l <;> rfl

theorem vector_get {n} : Primrec₂ (@List.Vector.get α n) :=
  option_some_iff.1 <|
    (list_getElem?.comp (vector_toList.comp fst) (fin_val.comp snd)).of_eq fun a => by
      simp [Vector.get_eq_get_toList]

theorem list_ofFn :
    ∀ {n} {f : Fin n → α → σ}, (∀ i, Primrec (f i)) → Primrec fun a => List.ofFn fun i => f i a
  | 0, _, _ => by simp only [List.ofFn_zero]; exact const []
  | n + 1, f, hf => by
    simpa using list_cons.comp (hf 0) (list_ofFn fun i => hf i.succ)

theorem vector_ofFn {n} {f : Fin n → α → σ} (hf : ∀ i, Primrec (f i)) :
    Primrec fun a => List.Vector.ofFn fun i => f i a :=
  vector_toList_iff.1 <| by simp [list_ofFn hf]

theorem vector_get' {n} : Primrec (@List.Vector.get α n) :=
  of_equiv_symm

theorem vector_ofFn' {n} : Primrec (@List.Vector.ofFn α n) :=
  of_equiv

theorem fin_app {n} : Primrec₂ (@id (Fin n → σ)) :=
  (vector_get.comp (vector_ofFn'.comp fst) snd).of_eq fun ⟨v, i⟩ => by simp

theorem fin_curry₁ {n} {f : Fin n → α → σ} : Primrec₂ f ↔ ∀ i, Primrec (f i) :=
  ⟨fun h i => h.comp (const i) .id, fun h =>
    (vector_get.comp ((vector_ofFn h).comp snd) fst).of_eq fun a => by simp⟩

theorem fin_curry {n} {f : α → Fin n → σ} : Primrec f ↔ Primrec₂ f :=
  ⟨fun h => fin_app.comp (h.comp fst) snd, fun h =>
    (vector_get'.comp
          (vector_ofFn fun i => show Primrec fun a => f a i from h.comp .id (const i))).of_eq
      fun a => by funext i; simp⟩

end Primrec

namespace Nat

open List.Vector

/-- An alternative inductive definition of `Primrec` which
  does not use the pairing function on ℕ, and so has to
  work with n-ary functions on ℕ instead of unary functions.
  We prove that this is equivalent to the regular notion
  in `to_prim` and `of_prim`. -/
inductive Primrec' : ∀ {n}, (List.Vector ℕ n → ℕ) → Prop
  | zero : @Primrec' 0 fun _ => 0
  | succ : @Primrec' 1 fun v => succ v.head
  | get {n} (i : Fin n) : Primrec' fun v => v.get i
  | comp {m n f} (g : Fin n → List.Vector ℕ m → ℕ) :
      Primrec' f → (∀ i, Primrec' (g i)) → Primrec' fun a => f (List.Vector.ofFn fun i => g i a)
  | prec {n f g} :
      @Primrec' n f →
        @Primrec' (n + 2) g →
          Primrec' fun v : List.Vector ℕ (n + 1) =>
            v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)

end Nat

namespace Nat.Primrec'

open List.Vector Primrec

theorem to_prim {n f} (pf : @Nat.Primrec' n f) : Primrec f := by
  induction pf with
  | zero => exact .const 0
  | succ => exact _root_.Primrec.succ.comp .vector_head
  | get i => exact Primrec.vector_get.comp .id (.const i)
  | comp _ _ _ hf hg => exact hf.comp (.vector_ofFn fun i => hg i)
  | @prec n f g _ _ hf hg =>
    exact
      .nat_rec' .vector_head (hf.comp Primrec.vector_tail)
        (hg.comp <|
          Primrec.vector_cons.comp (Primrec.fst.comp .snd) <|
          Primrec.vector_cons.comp (Primrec.snd.comp .snd) <|
            (@Primrec.vector_tail _ _ (n + 1)).comp .fst).to₂

theorem of_eq {n} {f g : List.Vector ℕ n → ℕ} (hf : Primrec' f) (H : ∀ i, f i = g i) :
    Primrec' g :=
  (funext H : f = g) ▸ hf

theorem const {n} : ∀ m, @Primrec' n fun _ => m
  | 0 => zero.comp Fin.elim0 fun i => i.elim0
  | m + 1 => succ.comp _ fun _ => const m

theorem head {n : ℕ} : @Primrec' n.succ head :=
  (get 0).of_eq fun v => by simp [get_zero]

theorem tail {n f} (hf : @Primrec' n f) : @Primrec' n.succ fun v => f v.tail :=
  (hf.comp _ fun i => @get _ i.succ).of_eq fun v => by
    rw [← ofFn_get v.tail]; congr; funext i; simp

/-- A function from vectors to vectors is primitive recursive when all of its projections are. -/
def Vec {n m} (f : List.Vector ℕ n → List.Vector ℕ m) : Prop :=
  ∀ i, Primrec' fun v => (f v).get i

protected theorem nil {n} : @Vec n 0 fun _ => nil := fun i => i.elim0

protected theorem cons {n m f g} (hf : @Primrec' n f) (hg : @Vec n m g) :
    Vec fun v => f v ::ᵥ g v := fun i => Fin.cases (by simp [*]) (fun i => by simp [hg i]) i

theorem idv {n} : @Vec n n id :=
  get

theorem comp' {n m f g} (hf : @Primrec' m f) (hg : @Vec n m g) : Primrec' fun v => f (g v) :=
  (hf.comp _ hg).of_eq fun v => by simp

theorem comp₁ (f : ℕ → ℕ) (hf : @Primrec' 1 fun v => f v.head) {n g} (hg : @Primrec' n g) :
    Primrec' fun v => f (g v) :=
  hf.comp _ fun _ => hg

theorem comp₂ (f : ℕ → ℕ → ℕ) (hf : @Primrec' 2 fun v => f v.head v.tail.head) {n g h}
    (hg : @Primrec' n g) (hh : @Primrec' n h) : Primrec' fun v => f (g v) (h v) := by
  simpa using hf.comp' (hg.cons <| hh.cons Primrec'.nil)

theorem prec' {n f g h} (hf : @Primrec' n f) (hg : @Primrec' n g) (hh : @Primrec' (n + 2) h) :
    @Primrec' n fun v => (f v).rec (g v) fun y IH : ℕ => h (y ::ᵥ IH ::ᵥ v) := by
  simpa using comp' (prec hg hh) (hf.cons idv)

theorem pred : @Primrec' 1 fun v => v.head.pred :=
  (prec' head (const 0) head).of_eq fun v => by simp; cases v.head <;> rfl

theorem add : @Primrec' 2 fun v => v.head + v.tail.head :=
  (prec head (succ.comp₁ _ (tail head))).of_eq fun v => by
    simp; induction v.head <;> simp [*, Nat.succ_add]

theorem sub : @Primrec' 2 fun v => v.head - v.tail.head := by
  have : @Primrec' 2 fun v ↦ (fun a b ↦ b - a) v.head v.tail.head := by
    refine (prec head (pred.comp₁ _ (tail head))).of_eq fun v => ?_
    simp; induction v.head <;> simp [*, Nat.sub_add_eq]
  simpa using comp₂ (fun a b => b - a) this (tail head) head

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
theorem mul : @Primrec' 2 fun v => v.head * v.tail.head :=
  (prec (const 0) (tail (add.comp₂ _ (tail head) head))).of_eq fun v => by
    simp; induction v.head <;> simp [*, Nat.succ_mul]; rw [add_comm]

theorem if_lt {n a b f g} (ha : @Primrec' n a) (hb : @Primrec' n b) (hf : @Primrec' n f)
    (hg : @Primrec' n g) : @Primrec' n fun v => if a v < b v then f v else g v :=
  (prec' (sub.comp₂ _ hb ha) hg (tail <| tail hf)).of_eq fun v => by
    cases e : b v - a v
    · simp [not_lt.2 (Nat.sub_eq_zero_iff_le.mp e)]
    · simp [Nat.lt_of_sub_eq_succ e]

theorem natPair : @Primrec' 2 fun v => v.head.pair v.tail.head :=
  if_lt head (tail head) (add.comp₂ _ (tail <| mul.comp₂ _ head head) head)
    (add.comp₂ _ (add.comp₂ _ (mul.comp₂ _ head head) head) (tail head))

protected theorem encode : ∀ {n}, @Primrec' n encode
  | 0 => (const 0).of_eq fun v => by rw [v.eq_nil]; rfl
  | _ + 1 =>
    (succ.comp₁ _ (natPair.comp₂ _ head (tail Primrec'.encode))).of_eq fun ⟨_ :: _, _⟩ => rfl

theorem sqrt : @Primrec' 1 fun v => v.head.sqrt := by
  suffices H : ∀ n : ℕ, n.sqrt =
      n.rec 0 fun x y => if x.succ < y.succ * y.succ then y else y.succ by
    simp only [H, succ_eq_add_one]
    have :=
      @prec' 1 _ _
        (fun v => by
          have x := v.head; have y := v.tail.head
          exact if x.succ < y.succ * y.succ then y else y.succ)
        head (const 0) ?_
    · exact this
    have x1 : @Primrec' 3 fun v => v.head.succ := succ.comp₁ _ head
    have y1 : @Primrec' 3 fun v => v.tail.head.succ := succ.comp₁ _ (tail head)
    exact if_lt x1 (mul.comp₂ _ y1 y1) (tail head) y1
  introv; symm
  induction n with
  | zero => simp
  | succ n IH =>
    dsimp; rw [IH]; split_ifs with h
    · exact le_antisymm (Nat.sqrt_le_sqrt (Nat.le_succ _)) (Nat.lt_succ_iff.1 <| Nat.sqrt_lt.2 h)
    · exact Nat.eq_sqrt.2
        ⟨not_lt.1 h, Nat.sqrt_lt.1 <| Nat.lt_succ_iff.2 <| Nat.sqrt_succ_le_succ_sqrt _⟩

theorem unpair₁ {n f} (hf : @Primrec' n f) : @Primrec' n fun v => (f v).unpair.1 := by
  have s := sqrt.comp₁ _ hf
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
  refine (if_lt fss s fss s).of_eq fun v => ?_
  simp [Nat.unpair]; split_ifs <;> rfl

theorem unpair₂ {n f} (hf : @Primrec' n f) : @Primrec' n fun v => (f v).unpair.2 := by
  have s := sqrt.comp₁ _ hf
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
  refine (if_lt fss s s (sub.comp₂ _ fss s)).of_eq fun v => ?_
  simp [Nat.unpair]; split_ifs <;> rfl

theorem of_prim {n f} : Primrec f → @Primrec' n f :=
  suffices ∀ f, Nat.Primrec f → @Primrec' 1 fun v => f v.head from fun hf =>
    (pred.comp₁ _ <|
          (this _ hf).comp₁ (fun m => Encodable.encode <| (@decode (List.Vector ℕ n) _ m).map f)
            Primrec'.encode).of_eq
      fun i => by simp [encodek]
  fun f hf => by
  induction hf with
  | zero => exact const 0
  | succ => exact succ
  | left => exact unpair₁ head
  | right => exact unpair₂ head
  | pair _ _ hf hg => exact natPair.comp₂ _ hf hg
  | comp _ _ hf hg => exact hf.comp₁ _ hg
  | prec _ _ hf hg =>
    simpa using
      prec' (unpair₂ head) (hf.comp₁ _ (unpair₁ head))
        (hg.comp₁ _ <|
          natPair.comp₂ _ (unpair₁ <| tail <| tail head) (natPair.comp₂ _ head (tail head)))

theorem prim_iff {n f} : @Primrec' n f ↔ Primrec f :=
  ⟨to_prim, of_prim⟩

theorem prim_iff₁ {f : ℕ → ℕ} : (@Primrec' 1 fun v => f v.head) ↔ Primrec f :=
  prim_iff.trans
    ⟨fun h => (h.comp <| .vector_ofFn fun _ => .id).of_eq fun v => by simp, fun h =>
      h.comp .vector_head⟩

theorem prim_iff₂ {f : ℕ → ℕ → ℕ} : (@Primrec' 2 fun v => f v.head v.tail.head) ↔ Primrec₂ f :=
  prim_iff.trans
    ⟨fun h => (h.comp <| Primrec.vector_cons.comp .fst <|
      Primrec.vector_cons.comp .snd (.const nil)).of_eq fun v => by simp,
    fun h => h.comp .vector_head (Primrec.vector_head.comp .vector_tail)⟩

theorem vec_iff {m n f} : @Vec m n f ↔ Primrec f :=
  ⟨fun h => by simpa using Primrec.vector_ofFn fun i => to_prim (h i), fun h i =>
    of_prim <| Primrec.vector_get.comp h (.const i)⟩

end Nat.Primrec'

theorem Primrec.nat_sqrt : Primrec Nat.sqrt :=
  Nat.Primrec'.prim_iff₁.1 Nat.Primrec'.sqrt
