/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Finite.Basic

/-!
# Fintype instances for pi types
-/

assert_not_exists OrderedRing MonoidWithZero

open Finset Function

variable {α β : Type*}

namespace Fintype

variable [DecidableEq α] [Fintype α] {γ δ : α → Type*} {s : ∀ a, Finset (γ a)}

/-- Given for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `Fintype.piFinset t` of all functions taking values in `t a` for all `a`. This is the
analogue of `Finset.pi` where the base finset is `univ` (but formally they are not the same, as
there is an additional condition `i ∈ Finset.univ` in the `Finset.pi` definition). -/
def piFinset (t : ∀ a, Finset (δ a)) : Finset (∀ a, δ a) :=
  (Finset.univ.pi t).map ⟨fun f a => f a (mem_univ a), fun _ _ =>
    by simp +contextual [funext_iff]⟩

@[simp]
theorem mem_piFinset {t : ∀ a, Finset (δ a)} {f : ∀ a, δ a} : f ∈ piFinset t ↔ ∀ a, f a ∈ t a := by
  constructor
  · simp only [piFinset, mem_map, and_imp, forall_prop_of_true, exists_prop, mem_univ, exists_imp,
      mem_pi]
    rintro g hg hgf a
    rw [← hgf]
    exact hg a
  · simp only [piFinset, mem_map, forall_prop_of_true, exists_prop, mem_univ, mem_pi]
    exact fun hf => ⟨fun a _ => f a, hf, rfl⟩

@[simp]
theorem coe_piFinset (t : ∀ a, Finset (δ a)) :
    (piFinset t : Set (∀ a, δ a)) = Set.pi Set.univ fun a => t a :=
  Set.ext fun x => by
    rw [Set.mem_univ_pi]
    exact Fintype.mem_piFinset

theorem piFinset_subset (t₁ t₂ : ∀ a, Finset (δ a)) (h : ∀ a, t₁ a ⊆ t₂ a) :
    piFinset t₁ ⊆ piFinset t₂ := fun _ hg => mem_piFinset.2 fun a => h a <| mem_piFinset.1 hg a

@[simp]
theorem piFinset_eq_empty : piFinset s = ∅ ↔ ∃ i, s i = ∅ := by simp [piFinset]

@[simp]
theorem piFinset_empty [Nonempty α] : piFinset (fun _ => ∅ : ∀ i, Finset (δ i)) = ∅ := by simp

@[simp]
lemma piFinset_nonempty : (piFinset s).Nonempty ↔ ∀ a, (s a).Nonempty := by simp [piFinset]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.piFinset_nonempty_of_forall_nonempty⟩ := piFinset_nonempty

lemma _root_.Finset.Nonempty.piFinset_const {ι : Type*} [Fintype ι] [DecidableEq ι] {s : Finset β}
    (hs : s.Nonempty) : (piFinset fun _ : ι ↦ s).Nonempty := piFinset_nonempty.2 fun _ ↦ hs

@[simp]
lemma piFinset_of_isEmpty [IsEmpty α] (s : ∀ a, Finset (γ a)) : piFinset s = univ :=
  eq_univ_of_forall fun _ ↦ by simp

@[simp]
theorem piFinset_singleton (f : ∀ i, δ i) : piFinset (fun i => {f i} : ∀ i, Finset (δ i)) = {f} :=
  ext fun _ => by simp only [funext_iff, Fintype.mem_piFinset, mem_singleton]

theorem piFinset_subsingleton {f : ∀ i, Finset (δ i)} (hf : ∀ i, (f i : Set (δ i)).Subsingleton) :
    (Fintype.piFinset f : Set (∀ i, δ i)).Subsingleton := fun _ ha _ hb =>
  funext fun _ => hf _ (mem_piFinset.1 ha _) (mem_piFinset.1 hb _)

theorem piFinset_disjoint_of_disjoint (t₁ t₂ : ∀ a, Finset (δ a)) {a : α}
    (h : Disjoint (t₁ a) (t₂ a)) : Disjoint (piFinset t₁) (piFinset t₂) :=
  disjoint_iff_ne.2 fun f₁ hf₁ f₂ hf₂ eq₁₂ =>
    disjoint_iff_ne.1 h (f₁ a) (mem_piFinset.1 hf₁ a) (f₂ a) (mem_piFinset.1 hf₂ a)
      (congr_fun eq₁₂ a)

lemma piFinset_image [∀ a, DecidableEq (δ a)] (f : ∀ a, γ a → δ a) (s : ∀ a, Finset (γ a)) :
    piFinset (fun a ↦ (s a).image (f a)) = (piFinset s).image fun b a ↦ f _ (b a) := by
  ext; simp only [mem_piFinset, mem_image, Classical.skolem, forall_and, funext_iff]

lemma eval_image_piFinset_subset (t : ∀ a, Finset (δ a)) (a : α) [DecidableEq (δ a)] :
    ((piFinset t).image fun f ↦ f a) ⊆ t a := image_subset_iff.2 fun _x hx ↦ mem_piFinset.1 hx _

lemma eval_image_piFinset (t : ∀ a, Finset (δ a)) (a : α) [DecidableEq (δ a)]
    (ht : ∀ b, a ≠ b → (t b).Nonempty) : ((piFinset t).image fun f ↦ f a) = t a := by
  refine (eval_image_piFinset_subset _ _).antisymm fun x h ↦ mem_image.2 ?_
  choose f hf using ht
  exact ⟨fun b ↦ if h : a = b then h ▸ x else f _ h, by aesop, by simp⟩

lemma eval_image_piFinset_const {β} [DecidableEq β] (t : Finset β) (a : α) :
    ((piFinset fun _i : α ↦ t).image fun f ↦ f a) = t := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · haveI : Nonempty α := ⟨a⟩
    simp
  · exact eval_image_piFinset (fun _ ↦ t) a fun _ _ ↦ ht

variable [∀ a, DecidableEq (δ a)]

lemma filter_piFinset_of_not_mem (t : ∀ a, Finset (δ a)) (a : α) (x : δ a) (hx : x ∉ t a) :
    {f ∈ piFinset t | f a = x} = ∅ := by
  simp only [filter_eq_empty_iff, mem_piFinset]; rintro f hf rfl; exact hx (hf _)

-- TODO: This proof looks like a good example of something that `aesop` can't do but should
lemma piFinset_update_eq_filter_piFinset_mem (s : ∀ i, Finset (δ i)) (i : α) {t : Finset (δ i)}
    (hts : t ⊆ s i) : piFinset (Function.update s i t) = {f ∈ piFinset s | f i ∈ t} := by
  ext f
  simp only [mem_piFinset, mem_filter]
  refine ⟨fun h ↦ ?_, fun h j ↦ ?_⟩
  · have := by simpa using h i
    refine ⟨fun j ↦ ?_, this⟩
    obtain rfl | hji := eq_or_ne j i
    · exact hts this
    · simpa [hji] using h j
  · obtain rfl | hji := eq_or_ne j i
    · simpa using h.2
    · simpa [hji] using h.1 j

lemma piFinset_update_singleton_eq_filter_piFinset_eq (s : ∀ i, Finset (δ i)) (i : α) {a : δ i}
    (ha : a ∈ s i) :
    piFinset (Function.update s i {a}) = {f ∈ piFinset s | f i = a} := by
  simp [piFinset_update_eq_filter_piFinset_mem, ha]

end Fintype

/-! ### pi -/

/-- A dependent product of fintypes, indexed by a fintype, is a fintype. -/
instance Pi.instFintype {α : Type*} {β : α → Type*} [DecidableEq α] [Fintype α]
    [∀ a, Fintype (β a)] : Fintype (∀ a, β a) :=
  ⟨Fintype.piFinset fun _ => univ, by simp⟩

@[simp]
theorem Fintype.piFinset_univ {α : Type*} {β : α → Type*} [DecidableEq α] [Fintype α]
    [∀ a, Fintype (β a)] :
    (Fintype.piFinset fun a : α => (Finset.univ : Finset (β a))) =
      (Finset.univ : Finset (∀ a, β a)) :=
  rfl

/-- `Fin.snoc` for `r`-ordered tuples. -/
def RelHom.snoc {s : β → β → Prop} {n : ℕ} {r : Fin (n + 1) → Fin (n + 1) → Prop}
  (xs : Fin.castSucc ⁻¹'o r →r s) (x : β)
  (hx : r (Fin.last n) (Fin.last n) → s x x)
  (hxs : ∀ a : Fin n,
    (r a.castSucc (Fin.last n) → s (xs a) x) ∧
    (r (Fin.last n) a.castSucc → s x (xs a))) :
    r →r s where
  toFun := Fin.snoc xs x
  map_rel' {v w} hs := by
    cases v using Fin.lastCases <;> cases w using Fin.lastCases
    · simpa using hx hs
    · simpa using (hxs _).right hs
    · simpa using (hxs _).left hs
    · simpa using xs.map_rel hs

@[simp]
theorem RelHom.coe_snoc
    {s : β → β → Prop} {n : ℕ} {r : Fin (n + 1) → Fin (n + 1) → Prop}
    (xs : Fin.castSucc ⁻¹'o r →r s) (x : β) (hx hxs) :
    ⇑(xs.snoc x hx hxs) = Fin.snoc xs x :=
  rfl

theorem RelHom.snoc_inj
    {s : β → β → Prop} {n : ℕ} {r : Fin (n + 1) → Fin (n + 1) → Prop}
    (xs : Fin.castSucc ⁻¹'o r →r s) (x : β) (hx hxs)
    (ys : Fin.castSucc ⁻¹'o r →r s) (y : β) (hy hys) :
    xs.snoc x hx hxs = ys.snoc y hy hys ↔ xs = ys ∧ x = y := by
  simp_rw [← DFunLike.coe_injective.eq_iff, coe_snoc, Fin.snoc_injective2.eq_iff]

section Fintype

open Option Finset Fin Fintype Equiv Function

-- We show a `Fintype` instance for an abstract hom from `Fin n` to `β`,
-- and then transfer this to arbitrary finite types using
-- `Fintype.truncFinBijection` and `Fintype.truncEquivFin`.

-- For performance reasons, the fintype is constructed inductively
-- instead of simply filtering all homs for valid ones.
private def pairRelFintypeAux {n β} [Fintype β]
    (motive : Fin n → Fin n → β → β → Bool) :
    Fintype { f : Fin n → β // ∀ a b, motive a b (f a) (f b)} :=
  -- induct on the cardinality of the domain
  match n with
  | 0 =>
    -- empty hom
    ⟨{⟨finZeroElim, by simp⟩}, by simp⟩
  | n + 1 =>
    letI ih := { f : Fin n → β // ∀ a b, motive (castSucc a) (castSucc b) (f a) (f b)}
    letI : Fintype ih := pairRelFintypeAux _
    -- pair the valid homs previously obtained with all possible choices for the new target
    { elems := univ.filterMap
        (fun p : ih × β ↦
          if h : motive (last n) (last n) p.snd p.snd ∧
              ∀ (a : Fin n),
                (motive a.castSucc (last n) (p.fst.val a) p.snd) ∧
                (motive (last n) a.castSucc p.snd (p.fst.val a)) then
            some ⟨snoc p.fst.val p.snd, fun a b => by
              cases a using snoc <;> cases b using snoc <;> aesop⟩
          else
            none)
        fun v w _ hbv hbw => by
          simp_rw [Option.mem_def, dite_none_right_eq_some] at hbv hbw
          obtain ⟨_, hv⟩ := hbv
          obtain ⟨_, hw⟩ := hbw
          have hvw := hv.trans hw.symm
          rwa [some_inj, Subtype.ext_iff, snoc_inj, Subtype.val_inj,
            ← Prod.eq_iff_fst_eq_snd_eq] at hvw
      complete C := by
        -- show this map is surjective
        rw [mem_filterMap]
        use (⟨C.val ∘ castSucc, fun a b => C.prop ..⟩, C.val (last n)), @mem_univ ..
        rw [dif_pos ⟨C.prop .., fun _ => ⟨C.prop .., C.prop ..⟩⟩, some_inj]
        ext i
        cases i using snoc <;> simp }

/--
We derive a `Fintype` for functions that satisfy an
arbitrary predicate `motive` between all pairs of arguments.
This is used in `Function.Embedding.fintype`, `RelHom.instFintype` and `RelEmbedding.instFintype`.
Not recommended if your `[DecidableEq α]` is very slow.
-/
def pairRelFintype {α β} [Fintype α] [Fintype β] [DecidableEq α]
    (motive : α → α → (x : β) → (y : β) → [Decidable (x = y)] → Prop)
    -- this is so that typeclass inference will see `inst`
    (_ : ∀ a b x y inst, Decidable (@motive a b x y inst) := by intros; infer_instance) :
    Fintype { f : α → β // ∀ a b inst, @motive a b (f a) (f b) inst } :=
  (truncFinBijection β).recOnSubsingleton fun ⟨b, hb⟩ ↦
    (truncEquivFin α).recOnSubsingleton fun a ↦
      haveI := fun x y => (decidable_of_iff' (x = y) hb.injective.eq_iff)
      letI motive' := fun u v x y => decide (motive (a.symm u) (a.symm v) (b x) (b y))
      (pairRelFintypeAux motive').ofBijective
        (fun f => ⟨b ∘ f.val ∘ a, fun u v inst => by
          rw [Subsingleton.elim inst]
          simpa [motive'] using f.prop (a u) (a v)⟩) <|
      ((a.symm.arrowCongr (.ofBijective b hb)).subtypeEquiv <| fun g => by
        refine ⟨fun h u v inst => ?_, fun h u v => ?_⟩
        · rw [Subsingleton.elim inst]
          simpa [motive'] using h (a u) (a v)
        · simpa [motive'] using h (a.symm u) (a.symm v)).bijective

end Fintype

/-- There are finitely many embeddings between finite types. -/
instance _root_.Function.Embedding.fintype {α β} [Fintype α] [Fintype β] [DecidableEq α] :
    Fintype (α ↪ β) :=
  (pairRelFintype (fun (a b : α) (x y : β) _ => x = y → a = b)).ofEquiv
    (f := (Equiv.subtypeEquivRight (by simp [Injective])).trans
      (Equiv.subtypeInjectiveEquivEmbedding α β))

/--
The type `r →r s` is equivalent to the type of
functions `f` which satisfy `r a b → s (f a) (f b)` for all `a` and `b`.
-/
@[simps]
def RelHom.equivSubtype {α β} {r : α → α → Prop} {s : β → β → Prop} :
    r →r s ≃ { f : α → β // ∀ a b, r a b → s (f a) (f b)} where
  toFun f := ⟨f, @f.map_rel⟩
  invFun f := ⟨f.val, @f.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance RelHom.instFintype {α β} {r : α → α → Prop} {s : β → β → Prop}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableRel r]
    -- this odd typeclass argument is so I can use it in `SimpleGraph.instFintypeColoring`
    [∀ a b [Decidable (a = b)], Decidable (s a b)] : Fintype (r →r s) :=
  (pairRelFintype fun a b x y _ => r a b → s x y).ofEquiv
    (f := (RelHom.equivSubtype.trans (Equiv.subtypeEquivRight (by simp))).symm)

/--
The type `r ↪r s` is equivalent to the type of injective
functions `f` which satisfy `s (f a) (f b) ↔ r a b` for all `a` and `b`.
-/
@[simps]
def RelEmbedding.equivSubtype {α β} {r : α → α → Prop} {s : β → β → Prop} :
    r ↪r s ≃ { f : α ↪ β // ∀ a b, s (f a) (f b) ↔ r a b} where
  toFun f := ⟨f.toEmbedding, @f.map_rel_iff⟩
  invFun f := ⟨⟨f.val, f.val.injective⟩, @f.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance RelEmbedding.instFintype {α β} {r : α → α → Prop} {s : β → β → Prop}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableRel r] [DecidableRel s] : Fintype (r ↪r s) :=
  (pairRelFintype fun a b x y _ => (x = y → a = b) ∧ (s x y ↔ r a b)).ofEquiv
    (f := (RelEmbedding.equivSubtype.trans
      ((Equiv.subtypeEquivOfSubtype' (Equiv.subtypeInjectiveEquivEmbedding ..).symm).trans
        ((Equiv.subtypeSubtypeEquivSubtypeInter Injective fun f =>
            ∀ a b, s (f a) (f b) ↔ r a b).trans
          (Equiv.subtypeEquivRight (fun g => by
            simp [forall_and, Injective]))))).symm)

@[simp]
theorem Finset.univ_pi_univ {α : Type*} {β : α → Type*} [DecidableEq α] [Fintype α]
    [∀ a, Fintype (β a)] :
    (Finset.univ.pi fun a : α => (Finset.univ : Finset (β a))) = Finset.univ := by
  ext; simp

/-! ### Diagonal -/

namespace Finset
variable {ι : Type*} [DecidableEq (ι → α)] {s : Finset α} {f : ι → α}

lemma piFinset_filter_const [DecidableEq ι] [Fintype ι] :
    {f ∈ Fintype.piFinset fun _ : ι ↦ s | ∃ a ∈ s, const ι a = f} = s.piDiag ι := by aesop

lemma piDiag_subset_piFinset [DecidableEq ι] [Fintype ι] :
    s.piDiag ι ⊆ Fintype.piFinset fun _ ↦ s := by simp [← piFinset_filter_const]

end Finset

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the previous section
(or in the `Fintype` module).

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/


section SetFiniteConstructors

section Pi
variable {ι : Type*} [Finite ι] {κ : ι → Type*} {t : ∀ i, Set (κ i)}

/-- Finite product of finite sets is finite -/
theorem Finite.pi (ht : ∀ i, (t i).Finite) : (pi univ t).Finite := by
  cases nonempty_fintype ι
  lift t to ∀ d, Finset (κ d) using ht
  classical
    rw [← Fintype.coe_piFinset]
    apply Finset.finite_toSet

/-- Finite product of finite sets is finite. Note this is a variant of `Set.Finite.pi` without the
extra `i ∈ univ` binder. -/
lemma Finite.pi' (ht : ∀ i, (t i).Finite) : {f : ∀ i, κ i | ∀ i, f i ∈ t i}.Finite := by
  simpa [Set.pi] using Finite.pi ht

end Pi

end SetFiniteConstructors

theorem forall_finite_image_eval_iff {δ : Type*} [Finite δ] {κ : δ → Type*} {s : Set (∀ d, κ d)} :
    (∀ d, (eval d '' s).Finite) ↔ s.Finite :=
  ⟨fun h => (Finite.pi h).subset <| subset_pi_eval_image _ _, fun h _ => h.image _⟩

end Set
