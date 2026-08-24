/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Abhimanyu Pallavi Sudhir
-/
module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Pi
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Order.Filter.Tendsto

/-!
# Germ of a function at a filter

The germ of a function `f : α → β` at a filter `l : Filter α` is the equivalence class of `f`
with respect to the equivalence relation `EventuallyEq l`: `f ≈ g` means `∀ᶠ x in l, f x = g x`.

## Main definitions

We define

* `Filter.Germ l β` to be the space of germs of functions `α → β` at a filter `l : Filter α`;
* coercion from `α → β` to `Germ l β`: `(f : Germ l β)` is the germ of `f : α → β`
  at `l : Filter α`; this coercion is declared as `CoeTC`;
* `(const l c : Germ l β)` is the germ of the constant function `fun x : α ↦ c` at a filter `l`;
* coercion from `β` to `Germ l β`: `(↑c : Germ l β)` is the germ of the constant function
  `fun x : α ↦ c` at a filter `l`; this coercion is declared as `CoeTC`;
* `map (F : β → γ) (f : Germ l β)` to be the composition of a function `F` and a germ `f`;
* `map₂ (F : β → γ → δ) (f : Germ l β) (g : Germ l γ)` to be the germ of `fun x ↦ F (f x) (g x)`
  at `l`;
* `f.Tendsto lb`: we say that a germ `f : Germ l β` tends to a filter `lb` if its representatives
  tend to `lb` along `l`;
* `f.compTendsto g hg` and `f.compTendsto' g hg`: given `f : Germ l β` and a function
  `g : γ → α` (resp., a germ `g : Germ lc α`), if `g` tends to `l` along `lc`, then the composition
  `f ∘ g` is a well-defined germ at `lc`;
* `Germ.liftPred`, `Germ.liftRel`: lift a predicate or a relation to the space of germs:
  `(f : Germ l β).liftPred p` means `∀ᶠ x in l, p (f x)`, and similarly for a relation.

We also define `map (F : β → γ) : Germ l β → Germ l γ` sending each germ `f` to `F ∘ f`.

For each of the following structures we prove that if `β` has this structure, then so does
`Germ l β`:

* one-operation algebraic structures up to `CommGroup`;
* `MulZeroClass`, `Distrib`, `Semiring`, `CommSemiring`, `Ring`, `CommRing`;
* `MulAction`, `DistribMulAction`, `Module`;
* `Preorder`, `PartialOrder`, and `Lattice` structures, as well as `BoundedOrder`;

## Tags

filter, germ
-/

assert_not_exists IsOrderedRing

open scoped Relator
namespace Filter

variable {α β γ δ : Type*} {l : Filter α} {ε : α → Type*}

public theorem const_eventuallyEq' [NeBot l] {a b : β} : (∀ᶠ _ in l, a = b) ↔ a = b :=
  eventually_const

@[simp]
public theorem const_eventuallyEq [NeBot l] {a b : β} : ((fun _ => a) =ᶠ[l] fun _ => b) ↔ a = b :=
  @const_eventuallyEq' _ _ _ _ a b

variable (l) (ε : α → Type*) in
def productSetoid : Setoid ((s : l.sets) × ((x : s.1) → ε x)) where
  r f g := ∀ᶠ x in l, ∀ (hf : x ∈ f.1.1) (hg : x ∈ g.1.1), f.2 ⟨x, hf⟩ = g.2 ⟨x, hg⟩
  iseqv.refl _ := .of_forall fun _ _ _ => rfl
  iseqv.symm h := h.mono fun _ => fun hfg hf hg => (hfg hg hf).symm
  iseqv.trans {_ g _} h₁ h₂ := h₂.mp (h₁.mp (Filter.eventually_of_mem g.1.2
    fun _ hg hfg hgh hf hh => (hfg hf hg).trans (hgh hg hh)))

/-- The filter product of `(x : α) → ε x` at `l`, which consists of partial functions
`(x : s) → ε x` for `s ∈ l`, where two partial functions are identified if they agree on `l`.
This is a dependent version of `Filter.Germ`. -/
public def Product.{u, v} {α : Type u} (l : Filter α) (ε : α → Type v) : Type (max u v) :=
  Quotient (productSetoid l ε)

public section Product
namespace Product

/-- Construct an element of the filter product by giving a set `s ∈ l` and
a partial function `f` defined on `s`. -/
def ofPartialFun (s : Set α) (hs : s ∈ l) (f : (x : α) → x ∈ s → ε x) : Product l ε :=
  Quotient.mk (productSetoid l ε) ⟨⟨s, hs⟩, fun x => f x.1 x.2⟩

theorem ofPartialFun_eq_iff {s t : Set α} {hs : s ∈ l} {ht : t ∈ l}
    {f : (x : α) → x ∈ s → ε x} {g : (x : α) → x ∈ t → ε x} :
    ofPartialFun s hs f = ofPartialFun t ht g ↔ ∀ᶠ x in l, ∀ hxs hxt, f x hxs = g x hxt := by
  unfold ofPartialFun Product productSetoid
  simp [Quotient.eq]

theorem ofPartialFun_eq_of_subset {s t : Set α} (hs : s ∈ l) (hst : s ⊆ t)
    (f : (x : α) → x ∈ t → ε x) :
    ofPartialFun s hs (fun x hx => f x (hst hx)) =
      ofPartialFun t (Filter.mem_of_superset hs hst) f :=
  ofPartialFun_eq_iff.2 (.of_forall fun _ _ _ => rfl)

/-- Construct a function out of the filter product by
specifying what value it should take for each `ofPartialFun s hs f`.
The specified outputs must be equal whenever `ofPartialFun s hs g` and `ofPartialFun t ht g'`
define the same element of `Filter.Product l ε`. -/
def liftOfPartialFun {β : Sort*} (f : (s : Set α) → s ∈ l → ((x : α) → x ∈ s → ε x) → β)
    (hf : ∀ s t hs ht g g', (∀ᶠ x in l, ∀ hxs hxt, g x hxs = g' x hxt) → f s hs g = f t ht g')
    (x : Product l ε) : β :=
  Quotient.lift (fun c => f c.1.1 c.1.2 fun x hx => c.2 ⟨x, hx⟩) (fun u v huv =>
    hf u.1.1 v.1.1 u.1.2 v.1.2 (fun x hx => u.2 ⟨x, hx⟩) (fun x hx => v.2 ⟨x, hx⟩) huv) x

theorem liftOfPartialFun_ofPartialFun {β : Sort*}
    (f : (s : Set α) → s ∈ l → ((x : α) → x ∈ s → ε x) → β)
    (hf : ∀ s t hs ht g g', (∀ᶠ x in l, ∀ hxs hxt, g x hxs = g' x hxt) → f s hs g = f t ht g')
    (s : Set α) (hs : s ∈ l) (g : (x : α) → x ∈ s → ε x) :
    liftOfPartialFun f hf (ofPartialFun s hs g) = f s hs g := (rfl)

@[elab_as_elim]
theorem inductionOnPartialFun {motive : Product l ε → Prop} (t : Product l ε)
    (ofPartialFun : ∀ s hs f, motive (ofPartialFun s hs f)) : motive t :=
  Quotient.inductionOn t fun x => ofPartialFun x.1.1 x.1.2 fun c hc => x.2 ⟨c, hc⟩

/-- Construct an element of the filter product from a global function `f : (x : α) → ε x`
defined on all of `α`. -/
@[expose]
def ofFun (f : (x : α) → ε x) : Product l ε :=
  ofPartialFun .univ l.univ_mem fun x _ => f x

theorem ofFun_def (f : (x : α) → ε x) : ofFun f = ofPartialFun .univ l.univ_mem fun x _ => f x :=
  rfl

theorem ofFun_eq_ofPartialFun (s : Set α) (hs : s ∈ l) (f : (x : α) → ε x) :
    ofFun f = ofPartialFun s hs fun x _ => f x := by
  simp [ofFun_def, ofPartialFun_eq_iff]

/-- Construct a function out of the filter product by
specifying what value it should take for each `ofFun f`.
The specified outputs must be equal whenever `ofFun g` and `ofFun g'`
define the same element of `Filter.Product l ε`. -/
noncomputable def liftOn [Nonempty ((x : α) → ε x)] {β : Sort*} (t : Product l ε)
    (f : ((x : α) → ε x) → β) (h : ∀ g g', (∀ᶠ x in l, g x = g' x) → f g = f g') : β :=
  open scoped Classical in
  liftOfPartialFun (fun s _ g => f fun x =>
      if h : x ∈ s then g x h else Classical.arbitrary ((x : α) → ε x) x)
    (fun _ _ hs ht _ _ hgg =>
      h _ _ (hgg.mp (Filter.eventually_of_mem (Filter.inter_mem hs ht) fun _ hx hgg =>
        ((dite_eq_left hx.1).trans ((hgg hx.1 hx.2).trans (dite_eq_left hx.2).symm))))) t

theorem liftOn_ofFun [Nonempty ((x : α) → ε x)] {β : Sort*} (g : ((x : α) → ε x))
    (f : ((x : α) → ε x) → β) (h : ∀ g g', (∀ᶠ x in l, g x = g' x) → f g = f g') :
    liftOn (ofFun g) f h = f g := by
  unfold liftOn
  simp [ofFun_def, liftOfPartialFun_ofPartialFun]

@[elab_as_elim]
theorem inductionOn [Nonempty ((x : α) → ε x)] {motive : Product l ε → Prop} (t : Product l ε)
    (ofFun : ∀ f, motive (ofFun f)) : motive t := by
  induction t using inductionOnPartialFun with | ofPartialFun s hs f
  obtain ⟨f, rfl⟩ : ∃ g : (x : α) → ε x, (fun x _ => g x) = f := by
    classical
    exact ⟨fun x => if h : x ∈ s then f x h else Classical.arbitrary ((x : α) → ε x) x,
      funext₂ fun x h => dite_eq_left h⟩
  rw [← ofFun_eq_ofPartialFun]
  exact ofFun f

instance coeTC : CoeTC ((x : α) → ε x) (l.Product ε) where
  coe := ofFun

instance instInhabited [(x : α) → Inhabited (ε x)] : Inhabited (l.Product ε) where
  default := ofFun default

instance [(x : α) → Nonempty (ε x)] : Nonempty (l.Product ε) :=
  ⟨ofFun Classical.ofNonempty⟩

theorem nonempty_iff : Nonempty (l.Product ε) ↔ ∀ᶠ x in l, Nonempty (ε x) := by
  constructor
  · refine fun h => h.elim fun f => ?_
    induction f using inductionOnPartialFun with | ofPartialFun s hs f
    exact Filter.eventually_of_mem hs fun x hx => ⟨f x hx⟩
  · intro h
    exact ⟨ofPartialFun {x | Nonempty (ε x)} h fun x hx => Classical.choice hx⟩

theorem isEmpty_iff : IsEmpty (l.Product ε) ↔ ∃ᶠ x in l, IsEmpty (ε x) := by
  rw [← not_nonempty_iff, nonempty_iff]
  simp

theorem subsingleton_iff : Subsingleton (l.Product ε) ↔
    IsEmpty (l.Product ε) ∨ ∀ᶠ x in l, Subsingleton (ε x) := by
  constructor
  · intro h
    rw [← not_nonempty_iff, ← imp_iff_not_or]
    refine fun hne => hne.elim fun f => ?_
    induction f using inductionOnPartialFun with | ofPartialFun s hs f
    classical
    have hf := h.allEq (ofPartialFun s hs fun x hx =>
      if h : Nontrivial (ε x) then (exists_ne (f x hx)).choose else f x hx)
      (ofPartialFun s hs f)
    rw [ofPartialFun_eq_iff] at hf
    refine (hf.and (Filter.eventually_mem_set.2 hs)).mono fun x hx => ?_
    obtain ⟨hx, hxs⟩ := hx
    specialize hx hxs hxs
    contrapose! hx
    rw [dite_eq_left hx]
    exact (exists_ne (f x hxs)).choose_spec
  · intro h
    obtain h | h := h
    · exact ⟨h.elim⟩
    constructor
    intro f g
    induction f using inductionOnPartialFun with | ofPartialFun s hs f
    induction g using inductionOnPartialFun with | ofPartialFun t ht g
    rw [ofPartialFun_eq_iff]
    exact h.mono fun _ h _ _ => h.allEq _ _

theorem nontrivial_iff : Nontrivial (l.Product ε) ↔
    (∀ᶠ x in l, Nonempty (ε x)) ∧ (∃ᶠ x in l, Nontrivial (ε x)) := by
  rw [← not_subsingleton_iff_nontrivial, subsingleton_iff, not_or, isEmpty_iff]
  simp [not_subsingleton_iff_nontrivial]

theorem subsingleton (h : ∀ᶠ x in l, Subsingleton (ε x)) : Subsingleton (l.Product ε) :=
  subsingleton_iff.2 (.inr h)

instance [∀ x, Subsingleton (ε x)] : Subsingleton (l.Product ε) :=
  subsingleton (.of_forall ‹_›)

instance [l.NeBot] [∀ x, Nontrivial (ε x)] : Nontrivial (l.Product ε) :=
  nontrivial_iff.2 ⟨.of_forall fun _ => inferInstance, .of_forall ‹_›⟩

theorem ofFun_eq_iff {f g : (x : α) → ε x} :
    (ofFun f : Product l ε) = ofFun g ↔ ∀ᶠ x in l, f x = g x := by
  simp [ofFun, ofPartialFun_eq_iff]

end Product
end Product

/-- The filter product of `α → β` at `l`, which consists of partial functions
`s → β` for `s ∈ l`, where two partial functions are identified if they agree on `l`.
This is a nondependent version of `Filter.Product`. -/
@[expose]
public def Germ.{u, v} {α : Type u} (l : Filter α) (β : Type v) : Type (max u v) :=
  Product l fun _ => β

public section Germ
namespace Germ
variable {f g h : α → β}

/-- The germ corresponding to a global function. -/
@[expose, coe]
def ofFun : (α → β) → Germ l β := Product.ofFun

instance : CoeTC (α → β) (Germ l β) :=
  ⟨ofFun⟩

@[simp, norm_cast]
theorem coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g := by
  unfold ofFun Germ Filter.EventuallyEq
  rw [Product.ofFun_eq_iff]

alias ⟨_, _root_.Filter.EventuallyEq.germ_eq⟩ := coe_eq

theorem subsingleton_of_bot (h : l = ⊥) : Subsingleton (Germ l β) :=
  Product.subsingleton (h.symm ▸ Filter.eventually_bot)

instance [Subsingleton β] : Subsingleton (Germ l β) :=
  Product.subsingleton (.of_forall fun _ => ‹_›)

instance [l.NeBot] [Nontrivial β] : Nontrivial (Germ l β) :=
  inferInstanceAs (Nontrivial (l.Product fun _ => β))

/-- Germ of the constant function `fun x : α ↦ c` at a filter `l`. -/
@[coe]
abbrev const {l : Filter α} (b : β) : (Germ l β) := ofFun fun _ => b

instance coeTail : CoeTail β (Germ l β) :=
  ⟨const⟩

/-- A germ `P` of functions `α → β` is constant w.r.t. `l`. -/
def IsConstant {l : Filter α} (P : Germ l β) : Prop :=
  P ∈ Set.range const

theorem isConstant_iff_exists {l : Filter α} (P : Germ l β) : P.IsConstant ↔ ∃ b : β, P = b :=
  Set.mem_range.trans (exists_congr fun _ => eq_comm)

theorem isConstant_coe {l : Filter α} {b} (h : ∀ x', f x' = b) : (↑f : Germ l β).IsConstant :=
  Set.mem_range.2 ⟨b, congrArg ofFun (funext h).symm⟩

@[simp]
theorem isConstant_coe_const {l : Filter α} {b : β} : (fun _ : α ↦ b : Germ l β).IsConstant :=
  Set.mem_range_self b

/-- If `f : α → β` is constant w.r.t. `l` and `g : β → γ`, then `g ∘ f : α → γ` also is. -/
lemma isConstant_comp {l : Filter α} {f : α → β} {g : β → γ}
    (h : (f : Germ l β).IsConstant) : ((g ∘ f) : Germ l γ).IsConstant := by
  rw [isConstant_iff_exists] at h ⊢
  obtain ⟨b, hb⟩ := h
  refine ⟨g b, ?_⟩
  rw [coe_eq] at hb ⊢
  exact hb.fun_comp g

@[elab_as_elim]
theorem inductionOn [hl : l.NeBot] (f : Germ l β) {motive : Germ l β → Prop}
    (coe : ∀ f : α → β, motive f) : motive f :=
  have : Nonempty β := Product.inductionOnPartialFun f fun _ hs f =>
    (hl.nonempty_of_mem hs).elim fun x hx => ⟨f x hx⟩
  Product.inductionOn f coe

@[elab_as_elim]
theorem inductionOn₂ [l.NeBot] (f : Germ l β) (g : Germ l γ)
    {motive : Germ l β → Germ l γ → Prop}
    (coe : ∀ (f : α → β) (g : α → γ), motive f g) : motive f g :=
  inductionOn f fun f => inductionOn g (coe f)

@[elab_as_elim]
theorem inductionOn₃ [l.NeBot]
    (f : Germ l β) (g : Germ l γ) (h : Germ l δ)
    {motive : Germ l β → Germ l γ → Germ l δ → Prop}
    (coe : ∀ (f : α → β) (g : α → γ) (h : α → δ), motive f g h) : motive f g h :=
  inductionOn f fun f => inductionOn₂ g h (coe f)

/-- Given a germ `f : Germ l β` and a function `F : (α → β) → γ` sending eventually equal functions
to the same value, returns the value `F` takes on functions having germ `f` at `l`. -/
noncomputable def liftOn [l.NeBot] {γ : Sort*} (f : Germ l β) (F : (α → β) → γ)
    (hF : (l.EventuallyEq ⇒ (· = ·)) F F) : γ :=
  have : Nonempty β := Germ.inductionOn f fun f => (Filter.NeBot.nonempty l).map f
  Product.liftOn f F hF

theorem liftOn_coe [l.NeBot] {γ : Sort*} (F : (α → β) → γ) (hF : (l.EventuallyEq ⇒ (· = ·)) F F)
    (f : α → β) : liftOn f F hF = F f := by
  unfold liftOn ofFun
  extract_lets
  exact Product.liftOn_ofFun f F _

/-- Given a map `F : (α → β) → (γ → δ)` that sends functions eventually equal at `l` to functions
eventually equal at `lc`, returns a map from `Germ l β` to `Germ lc δ`. -/
noncomputable def map' {lc : Filter γ} [l.NeBot] (F : (α → β) → γ → δ)
    (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F) :
    Germ l β → Germ lc δ :=
  fun f => liftOn f (ofFun ∘ F) fun _ _ h => coe_eq.2 (hF h)

@[simp]
theorem map'_coe [l.NeBot] {lc : Filter γ} (F : (α → β) → γ → δ)
    (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F)
    (f : α → β) : map' F hF f = F f := by
  unfold map'
  exact liftOn_coe _ _ f

/-- Lift a function `β → γ` to a function `Germ l β → Germ l γ`. -/
def map (op : β → γ) : Germ l β → Germ l γ :=
  fun f => Product.liftOfPartialFun
    (fun s hs f => Product.ofPartialFun s hs fun x hx => op (f x hx))
    (fun _ _ _ _ _ _ h => Product.ofPartialFun_eq_iff.2
      (h.mono fun _ hx hxs hxt => congrArg op (hx hxs hxt))) f

@[simp]
theorem map_coe (op : β → γ) (f : α → β) : map op (f : Germ l β) = op ∘ f :=
  (rfl)

@[simp]
theorem map_id : map id = (id : Germ l β → Germ l β) := by
  ext ⟨f⟩
  rfl

theorem map_map (op₁ : γ → δ) (op₂ : β → γ) (f : Germ l β) :
    map op₁ (map op₂ f) = map (op₁ ∘ op₂) f :=
  Product.inductionOnPartialFun f fun _ _ _ => rfl

/-- Lift a binary function `β → γ → δ` to a function `Germ l β → Germ l γ → Germ l δ`. -/
def map₂ (op : β → γ → δ) : Germ l β → Germ l γ → Germ l δ :=
  fun f g => Product.liftOfPartialFun
    (fun s hs f =>
      Product.liftOfPartialFun
        (fun t ht g =>
          Product.ofPartialFun (s ∩ t) (Filter.inter_mem hs ht)
            fun x hx => op (f x hx.1) (g x hx.2))
        (fun _ _ _ _ _ _ h => Product.ofPartialFun_eq_iff.2
          (h.mono fun _ hx hxs hxt => congrArg (op _) (hx hxs.2 hxt.2)))
        g)
    (fun _ _ _ _ _ _ h => by
      refine Product.inductionOnPartialFun g fun s hs g => ?_
      unfold Germ
      rw [Product.liftOfPartialFun_ofPartialFun,
        Product.liftOfPartialFun_ofPartialFun,
        Product.ofPartialFun_eq_iff]
      exact h.mono fun x hx hxs hxt => congrFun (congrArg _ (hx hxs.1 hxt.1)) _) f

@[simp]
theorem map₂_coe (op : β → γ → δ) (f : α → β) (g : α → γ) :
    map₂ op (f : Germ l β) g = fun x => op (f x) (g x) := by
  unfold map₂ ofFun Product.ofFun Germ
  erw [Product.liftOfPartialFun_ofPartialFun,
    Product.liftOfPartialFun_ofPartialFun]
  exact Product.ofPartialFun_eq_iff.2 (by simp)

/-- A germ at `l` of maps from `α` to `β` tends to `lb : Filter β` if it is represented by a map
which tends to `lb` along `l`. -/
protected def Tendsto (f : Germ l β) (lb : Filter β) : Prop :=
  ∀ _ : l.NeBot, liftOn f (fun f => Tendsto f l lb) fun _f _g H => propext (tendsto_congr' H)

@[simp, norm_cast]
theorem coe_tendsto {f : α → β} {lb : Filter β} : (f : Germ l β).Tendsto lb ↔ Tendsto f l lb := by
  unfold Germ.Tendsto
  by_cases h : l.NeBot
  · rw [forall_prop_of_true h]
    exact (liftOn_coe _ _ f).to_iff
  · cases not_neBot.1 h
    simp

alias ⟨_, _root_.Filter.Tendsto.germ_tendsto⟩ := coe_tendsto

/-- Given two germs `f : Germ l β`, and `g : Germ lc α`, where `l : Filter α`, if `g` tends to `l`,
then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
noncomputable def compTendsto' (f : Germ l β) {lc : Filter γ} (g : Germ lc α)
    (hg : g.Tendsto l) : Germ lc β :=
  open scoped Classical in
  if hl : l.NeBot then
    liftOn f (fun f => g.map f) <| by
      intro f f' hff
      beta_reduce
      by_cases hlc : lc.NeBot
      · induction g using inductionOn with | coe g
        rw [map_coe, map_coe, coe_eq]
        rw [coe_tendsto] at hg
        exact hff.comp_tendsto hg
      · cases Filter.not_neBot.1 hlc
        exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _
  else Product.ofPartialFun ∅ (Classical.byContradiction fun h => by
    rw [Filter.empty_mem_iff_bot, ← ne_eq, ← Filter.neBot_iff] at h
    induction g using inductionOn with | coe g
    rw [coe_tendsto, Filter.not_neBot.1 hl, tendsto_bot_right_iff] at hg
    exact Filter.neBot_iff.1 h hg) fun x hx => hx.elim

@[simp]
theorem coe_compTendsto' (f : α → β) {lc : Filter γ} {g : Germ lc α} (hg : g.Tendsto l) :
    (f : Germ l β).compTendsto' g hg = g.map f := by
  unfold compTendsto'
  by_cases h : l.NeBot
  · exact (dite_eq_left h).trans (liftOn_coe _ _ f)
  · cases Filter.not_neBot.1 h
    generalize g.map f = u
    induction u using Product.inductionOnPartialFun with | ofPartialFun s hs u
    refine (dite_eq_right h).trans (Product.ofPartialFun_eq_iff.2 ?_)
    simp

/-- Given a germ `f : Germ l β` and a function `g : γ → α`, where `l : Filter α`, if `g` tends
to `l` along `lc : Filter γ`, then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
@[expose]
noncomputable def compTendsto (f : Germ l β) {lc : Filter γ} (g : γ → α) (hg : Tendsto g lc l) :
    Germ lc β :=
  f.compTendsto' _ hg.germ_tendsto

@[simp]
theorem coe_compTendsto (f : α → β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    (f : Germ l β).compTendsto g hg = f ∘ g := by
  unfold compTendsto
  rw [coe_compTendsto', map_coe]

@[simp]
theorem compTendsto'_coe (f : Germ l β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    f.compTendsto' _ hg.germ_tendsto = f.compTendsto g hg :=
  rfl

theorem _root_.Filter.Tendsto.congr_germ {f g : β → γ} {l : Filter α} {l' : Filter β}
    (h : f =ᶠ[l'] g) {φ : α → β} (hφ : Tendsto φ l l') : (f ∘ φ : Germ l γ) = g ∘ φ :=
  EventuallyEq.germ_eq (h.comp_tendsto hφ)

set_option linter.dupNamespace false in
@[deprecated (since := "2026-05-24")] alias Filter.Tendsto.congr_germ := Filter.Tendsto.congr_germ

lemma isConstant_comp_tendsto {lc : Filter γ} {g : γ → α}
    (hf : (f : Germ l β).IsConstant) (hg : Tendsto g lc l) : IsConstant (f ∘ g : Germ lc β) := by
  rcases hf with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  rw [coe_eq] at hb ⊢
  exact hb.comp_tendsto hg

/-- If a germ `f : Germ l β` is constant, where `l : Filter α`,
and a function `g : γ → α` tends to `l` along `lc : Filter γ`,
the germ of the composition `f ∘ g` is also constant. -/
lemma isConstant_compTendsto {f : Germ l β} {lc : Filter γ} {g : γ → α}
    (hf : f.IsConstant) (hg : Tendsto g lc l) : (f.compTendsto g hg).IsConstant := by
  rcases hf with ⟨b, rfl⟩
  rw [coe_compTendsto]
  exact ⟨b, rfl⟩

@[norm_cast]
theorem const_inj [NeBot l] {a b : β} : (↑a : Germ l β) = ↑b ↔ a = b :=
  coe_eq.trans const_eventuallyEq

theorem map_const (l : Filter α) (a : β) (f : β → γ) : (↑a : Germ l β).map f = ↑(f a) :=
  (rfl)

theorem map₂_const (l : Filter α) (b : β) (c : γ) (f : β → γ → δ) :
    map₂ f (↑b : Germ l β) ↑c = ↑(f b c) :=
  map₂_coe f _ _

theorem const_compTendsto {l : Filter α} (b : β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    (↑b : Germ l β).compTendsto g hg = ↑b := by
  rw [coe_compTendsto]
  rfl

theorem const_compTendsto' {l : Filter α} (b : β) {lc : Filter γ} {g : Germ lc α}
    (hg : g.Tendsto l) : (↑b : Germ l β).compTendsto' g hg = ↑b := by
  rw [coe_compTendsto']
  by_cases h : lc.NeBot
  · induction g using inductionOn with | coe g
    rw [map_coe]
    rfl
  · exact (subsingleton_of_bot (Filter.not_neBot.1 h)).allEq _ _

/-- Lift a predicate on `β` to `Germ l β`. -/
def LiftPred (p : β → Prop) (f : Germ l β) : Prop :=
  ∀ _ : l.NeBot, liftOn f (fun f => ∀ᶠ x in l, p (f x)) fun _f _g H =>
    propext <| eventually_congr <| H.mono fun _x hx => hx ▸ Iff.rfl

@[simp]
theorem liftPred_coe {p : β → Prop} {f : α → β} :
    LiftPred p (f : Germ l β) ↔ ∀ᶠ x in l, p (f x) := by
  unfold LiftPred
  by_cases h : l.NeBot
  · rw [forall_prop_of_true h]
    exact (liftOn_coe _ _ f).to_iff
  · cases Filter.not_neBot.1 h
    simp

theorem liftPred_const {p : β → Prop} {x : β} (hx : p x) : LiftPred p (↑x : Germ l β) :=
  liftPred_coe.2 <| Eventually.of_forall fun _y => hx

theorem liftPred_const_iff [NeBot l] {p : β → Prop} {x : β} : LiftPred p (↑x : Germ l β) ↔ p x :=
  liftPred_coe.trans eventually_const

theorem liftPred_iff_map_eq_const_true {p : β → Prop} {f : Germ l β} :
    LiftPred p f ↔ f.map p = True := by
  by_cases h : l.NeBot
  · induction f using inductionOn with | coe f
    rw [liftPred_coe, map_coe, coe_eq, EventuallyEq]
    simp
  · apply iff_of_true
    · unfold LiftPred
      exact fun hl => (h hl).elim
    · exact (subsingleton_of_bot (Filter.not_neBot.1 h)).allEq _ _

/-- Lift a relation `r : β → γ → Prop` to `Germ l β → Germ l γ → Prop`. -/
def LiftRel (r : β → γ → Prop) (f : Germ l β) (g : Germ l γ) : Prop :=
  LiftPred (Function.uncurry r) (map₂ Prod.mk f g)

theorem liftRel_coe {r : β → γ → Prop} {f : α → β} {g : α → γ} :
    LiftRel r (f : Germ l β) g ↔ ∀ᶠ x in l, r (f x) (g x) := by
  unfold LiftRel
  rw [map₂_coe, liftPred_coe]
  rfl

theorem liftRel_const {r : β → γ → Prop} {x : β} {y : γ} (h : r x y) :
    LiftRel r (↑x : Germ l β) ↑y :=
  liftRel_coe.2 <| Eventually.of_forall fun _ => h

@[simp]
theorem liftRel_const_iff [NeBot l] {r : β → γ → Prop} {x : β} {y : γ} :
    LiftRel r (↑x : Germ l β) ↑y ↔ r x y :=
  liftRel_coe.trans eventually_const

theorem liftRel_iff_map₂_eq_const_true {r : β → γ → Prop} {f : Germ l β} {g : Germ l γ} :
    LiftRel r f g ↔ map₂ r f g = True := by
  by_cases h : l.NeBot
  · induction f, g using inductionOn₂ with | coe f g
    rw [liftRel_coe, map₂_coe, coe_eq, EventuallyEq]
    simp
  · apply iff_of_true
    · unfold LiftRel LiftPred
      exact fun hl => (h hl).elim
    · exact (subsingleton_of_bot (Filter.not_neBot.1 h)).allEq _ _

theorem liftRel_eq_iff {f g : Germ l β} : LiftRel (@Eq β) f g ↔ f = g := by
  by_cases h : l.NeBot
  · induction f, g using inductionOn₂ with | coe f g
    rw [liftRel_coe, coe_eq, EventuallyEq]
  · apply iff_of_true
    · unfold LiftRel LiftPred
      exact fun hl => (h hl).elim
    · exact (subsingleton_of_bot (Filter.not_neBot.1 h)).allEq _ _

instance instInhabited [Inhabited β] : Inhabited (Germ l β) := ⟨↑(default : β)⟩

section Monoid

variable {M : Type*} {G : Type*}

@[to_additive] instance instMul [Mul M] : Mul (Germ l M) := ⟨map₂ (· * ·)⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_mul [Mul M] (f g : α → M) : ↑(f * g) = (f * g : Germ l M) :=
  (map₂_coe (· * ·) f g).symm

@[to_additive] instance instOne [One M] : One (Germ l M) := ⟨↑(1 : M)⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_one [One M] : ↑(1 : α → M) = (1 : Germ l M) :=
  rfl

@[to_additive]
instance instSemigroup [Semigroup M] : Semigroup (Germ l M) where
  mul_assoc := by
    intro a b c
    by_cases h : l.NeBot
    · induction a, b, c using inductionOn₃ with | coe a b c
      rw [← coe_mul, ← coe_mul, ← coe_mul, ← coe_mul, mul_assoc]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

@[to_additive]
instance instCommSemigroup [CommSemigroup M] : CommSemigroup (Germ l M) where
  mul_comm := by
    intro a b
    by_cases h : l.NeBot
    · induction a, b using inductionOn₂ with | coe a b
      rw [← coe_mul, ← coe_mul, mul_comm]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

@[to_additive]
instance instIsLeftCancelMul [Mul M] [IsLeftCancelMul M] : IsLeftCancelMul (Germ l M) where
  mul_left_cancel := by
    intro a b c h
    by_cases h : l.NeBot
    · induction a, b, c using inductionOn₃ with | coe a b c
      beta_reduce at h
      rw [← coe_mul, ← coe_mul, coe_eq] at h
      rw [coe_eq]
      exact h.mono fun x hx => mul_left_cancel hx
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

@[to_additive]
instance instIsRightCancelMul [Mul M] [IsRightCancelMul M] : IsRightCancelMul (Germ l M) where
  mul_right_cancel := by
    intro a b c h
    by_cases h : l.NeBot
    · induction a, b, c using inductionOn₃ with | coe a b c
      beta_reduce at h
      rw [← coe_mul, ← coe_mul, coe_eq] at h
      rw [coe_eq]
      exact h.mono fun x hx => mul_right_cancel hx
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

@[to_additive]
instance instIsCancelMul [Mul M] [IsCancelMul M] : IsCancelMul (Germ l M) where

@[to_additive]
instance instLeftCancelSemigroup [LeftCancelSemigroup M] : LeftCancelSemigroup (Germ l M) where
  mul_left_cancel _ _ _ := mul_left_cancel

@[to_additive]
instance instRightCancelSemigroup [RightCancelSemigroup M] : RightCancelSemigroup (Germ l M) where
  mul_right_cancel _ _ _ := mul_right_cancel

@[to_additive]
instance instMulOneClass [MulOneClass M] : MulOneClass (Germ l M) where
  one_mul := by
    intro a
    by_cases h : l.NeBot
    · induction a using inductionOn with | coe a
      rw [← coe_one, ← coe_mul, one_mul]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _
  mul_one := by
    intro a
    by_cases h : l.NeBot
    · induction a using inductionOn with | coe a
      rw [← coe_one, ← coe_mul, mul_one]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

@[to_additive (attr := to_additive) instSMul]
instance instPow [Pow G M] : Pow (Germ l G) M where pow f n := map (· ^ n) f

@[to_additive (attr := simp, norm_cast)]
theorem coe_smul [SMul M G] (n : M) (f : α → G) : ↑(n • f) = n • (f : Germ l G) :=
  (rfl)

@[to_additive (attr := simp, norm_cast)]
theorem const_smul [SMul M G] (n : M) (a : G) : (↑(n • a) : Germ l G) = n • (↑a : Germ l G) :=
  (rfl)

@[to_additive (attr := norm_cast), simp]
theorem coe_pow [Pow G M] (f : α → G) (n : M) : ↑(f ^ n) = (f : Germ l G) ^ n :=
  (rfl)

@[to_additive (attr := norm_cast), simp]
theorem const_pow [Pow G M] (a : G) (n : M) : (↑(a ^ n) : Germ l G) = (↑a : Germ l G) ^ n :=
  (rfl)

@[to_additive]
instance instMonoid [Monoid M] : Monoid (Germ l M) where
  npow_zero := by
    intro x
    by_cases h : l.NeBot
    · induction x using inductionOn with | coe x
      rw [← coe_pow, ← coe_one, pow_zero]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _
  npow_succ := by
    intro n x
    by_cases h : l.NeBot
    · induction x using inductionOn with | coe x
      rw [← coe_pow, ← coe_pow, ← coe_mul, pow_succ]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

/-- Coercion from functions to germs as a monoid homomorphism. -/
@[expose, to_additive /-- Coercion from functions to germs as an additive monoid homomorphism. -/]
def coeMulHom [Monoid M] (l : Filter α) : (α → M) →* Germ l M where
  toFun := ofFun
  map_one' := coe_one
  map_mul' := coe_mul

@[to_additive (attr := simp)]
theorem coe_coeMulHom [Monoid M] : (coeMulHom l : (α → M) → Germ l M) = ofFun :=
  rfl

@[to_additive]
instance instCommMonoid [CommMonoid M] : CommMonoid (Germ l M) where

instance instNatCast [NatCast M] : NatCast (Germ l M) where natCast n := (n : α → M)

@[simp]
theorem natCast_def [NatCast M] (n : ℕ) : ((fun _ ↦ n : α → M) : Germ l M) = n := rfl

@[simp, norm_cast]
theorem const_nat [NatCast M] (n : ℕ) : ((n : M) : Germ l M) = n := rfl

@[simp, norm_cast]
theorem coe_ofNat [NatCast M] (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : α → M) : Germ l M) = OfNat.ofNat n :=
  rfl

@[simp, norm_cast]
theorem const_ofNat [NatCast M] (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : M) : Germ l M) = OfNat.ofNat n :=
  rfl

instance instIntCast [IntCast M] : IntCast (Germ l M) where intCast n := (n : α → M)

@[simp]
theorem intCast_def [IntCast M] (n : ℤ) : ((fun _ ↦ n : α → M) : Germ l M) = n := rfl

instance instAddMonoidWithOne [AddMonoidWithOne M] : AddMonoidWithOne (Germ l M) where
  natCast_zero := (congrArg ofFun Nat.cast_zero).trans coe_zero
  natCast_succ n := (congrArg ofFun (Nat.cast_add_one n)).trans
    ((coe_add _ _).trans (congrArg (_ + ·) coe_one))

instance instAddCommMonoidWithOne [AddCommMonoidWithOne M] : AddCommMonoidWithOne (Germ l M) where
  add_comm := add_comm

@[to_additive] instance instInv [Inv G] : Inv (Germ l G) := ⟨map Inv.inv⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_inv [Inv G] (f : α → G) : ↑f⁻¹ = (f⁻¹ : Germ l G) :=
  (rfl)

@[to_additive (attr := simp, norm_cast)]
theorem const_inv [Inv G] (a : G) : (↑(a⁻¹) : Germ l G) = (↑a)⁻¹ :=
  (rfl)

@[to_additive] instance instDiv [Div M] : Div (Germ l M) := ⟨map₂ (· / ·)⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_div [Div M] (f g : α → M) : ↑(f / g) = (f / g : Germ l M) :=
  (map₂_coe (· / ·) f g).symm

@[to_additive (attr := simp, norm_cast)]
theorem const_div [Div M] (a b : M) : (↑(a / b) : Germ l M) = ↑a / ↑b :=
  coe_div _ _

@[to_additive]
instance instInvolutiveInv [InvolutiveInv G] : InvolutiveInv (Germ l G) where
  inv_inv := by
    intro x
    by_cases h : l.NeBot
    · induction x using inductionOn with | coe x
      rw [← coe_inv, ← coe_inv, inv_inv]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

instance instHasDistribNeg [Mul G] [HasDistribNeg G] : HasDistribNeg (Germ l G) where
  neg_mul := by
    intro x y
    by_cases h : l.NeBot
    · induction x, y using inductionOn₂ with | coe x y
      rw [← coe_neg, ← coe_mul, ← coe_mul, ← coe_neg, neg_mul]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _
  mul_neg := by
    intro x y
    by_cases h : l.NeBot
    · induction x, y using inductionOn₂ with | coe x y
      rw [← coe_neg, ← coe_mul, ← coe_mul, ← coe_neg, mul_neg]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

@[to_additive]
instance instInvOneClass [InvOneClass G] : InvOneClass (Germ l G) where
  inv_one := by rw [← coe_one, ← coe_inv, inv_one]

@[to_additive subNegMonoid]
instance instDivInvMonoid [DivInvMonoid G] : DivInvMonoid (Germ l G) where
  zpow z f := f ^ z
  zpow_zero' := by
    intro x
    by_cases h : l.NeBot
    · induction x using inductionOn with | coe x
      rw [← coe_pow, ← coe_one, zpow_zero]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _
  zpow_succ' := by
    intro n x
    by_cases h : l.NeBot
    · induction x using inductionOn with | coe x
      rw [← coe_pow, ← coe_pow, ← coe_mul, zpow_natCast, zpow_natCast, pow_succ]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _
  zpow_neg' := by
    intro n x
    by_cases h : l.NeBot
    · induction x using inductionOn with | coe x
      rw [← coe_pow, ← coe_pow, ← coe_inv, zpow_negSucc, zpow_natCast]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _
  div_eq_mul_inv := by
    intro x y
    by_cases h : l.NeBot
    · induction x, y using inductionOn₂ with | coe x y
      rw [← coe_div, ← coe_inv, ← coe_mul, div_eq_mul_inv]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

@[to_additive]
instance instDivisionMonoid [DivisionMonoid G] : DivisionMonoid (Germ l G) where
  inv_inv := inv_inv
  mul_inv_rev := by
    intro x y
    by_cases h : l.NeBot
    · induction x, y using inductionOn₂ with | coe x y
      rw [← coe_mul, ← coe_inv, ← coe_inv, ← coe_inv, ← coe_mul, mul_inv_rev]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _
  inv_eq_of_mul := by
    intro x y hxy
    by_cases h : l.NeBot
    · induction x, y using inductionOn₂ with | coe x y
      rw [← coe_mul, ← coe_one, coe_eq] at hxy
      rw [← coe_inv, coe_eq]
      exact hxy.mono fun c hc => inv_eq_of_mul_eq_one_right hc
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

@[to_additive]
instance instGroup [Group G] : Group (Germ l G) where
  inv_mul_cancel := by
    intro x
    by_cases h : l.NeBot
    · induction x using inductionOn with | coe x
      rw [← coe_inv, ← coe_mul, ← coe_one, inv_mul_cancel]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

@[to_additive]
instance instCommGroup [CommGroup G] : CommGroup (Germ l G) where

instance instAddGroupWithOne [AddGroupWithOne G] : AddGroupWithOne (Germ l G) where
  intCast_ofNat n := (congrArg ofFun (Int.cast_natCast n)).trans (natCast_def n)
  intCast_negSucc n := (congrArg ofFun (Int.cast_negSucc n)).trans
    ((coe_neg _).trans (congrArg (-·) (natCast_def _)))

end Monoid

section Ring

variable {R : Type*}

instance instMulZeroClass [MulZeroClass R] : MulZeroClass (Germ l R) where
  zero_mul := by
    intro x
    by_cases h : l.NeBot
    · induction x using inductionOn with | coe x
      rw [← coe_zero, ← coe_mul, zero_mul]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _
  mul_zero := by
    intro x
    by_cases h : l.NeBot
    · induction x using inductionOn with | coe x
      rw [← coe_zero, ← coe_mul, mul_zero]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

instance instMulZeroOneClass [MulZeroOneClass R] : MulZeroOneClass (Germ l R) where
  __ := instMulZeroClass
  __ := instMulOneClass

instance instMonoidWithZero [MonoidWithZero R] : MonoidWithZero (Germ l R) where
  __ := instMonoid
  __ := instMulZeroClass

instance instDistrib [Distrib R] : Distrib (Germ l R) where
  left_distrib := by
    intro a b c
    by_cases h : l.NeBot
    · induction a, b, c using inductionOn₃ with | coe a b c
      rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ← coe_add, mul_add]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _
  right_distrib := by
    intro a b c
    by_cases h : l.NeBot
    · induction a, b, c using inductionOn₃ with | coe a b c
      rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ← coe_add, add_mul]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring (Germ l R) where

instance instNonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring (Germ l R) where

instance instNonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring (Germ l R) where

instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] :
    NonUnitalNonAssocRing (Germ l R) where

instance instNonUnitalRing [NonUnitalRing R] : NonUnitalRing (Germ l R) where

instance instNonAssocRing [NonAssocRing R] : NonAssocRing (Germ l R) where

instance instSemiring [Semiring R] : Semiring (Germ l R) where

instance instRing [Ring R] : Ring (Germ l R) where

instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] :
    NonUnitalCommSemiring (Germ l R) where

instance instCommSemiring [CommSemiring R] : CommSemiring (Germ l R) where

instance instNonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing (Germ l R) where

instance instCommRing [CommRing R] : CommRing (Germ l R) where

/-- Coercion `(α → R) → Germ l R` as a `RingHom`. -/
@[expose]
def coeRingHom [Semiring R] (l : Filter α) : (α → R) →+* Germ l R where
  toFun := ofFun
  __ := coeAddHom l
  __ := coeMulHom l

@[simp]
theorem coe_coeRingHom [Semiring R] : (coeRingHom l : (α → R) → Germ l R) = ofFun :=
  rfl

end Ring

section Module

variable {M N R : Type*}

@[to_additive]
instance instSMul' [SMul M β] : SMul (Germ l M) (Germ l β) :=
  ⟨map₂ (· • ·)⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_smul' [SMul M β] (c : α → M) (f : α → β) : ↑(c • f) = (c : Germ l M) • (f : Germ l β) :=
  (map₂_coe (· • ·) c f).symm

@[to_additive]
instance instMulAction [Monoid M] [MulAction M β] : MulAction M (Germ l β) where
  one_smul := by
    intro f
    by_cases h : l.NeBot
    · induction f using inductionOn with | coe f
      rw [← coe_smul, one_smul]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _
  mul_smul := by
    intro c₁ c₂ f
    by_cases h : l.NeBot
    · induction f using inductionOn with | coe f
      rw [← coe_smul, ← coe_smul, ← coe_smul, mul_smul]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

@[to_additive]
instance instMulAction' [Monoid M] [MulAction M β] : MulAction (Germ l M) (Germ l β) where
  one_smul := by
    intro f
    by_cases h : l.NeBot
    · induction f using inductionOn with | coe f
      rw [← coe_one, ← coe_smul', one_smul]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _
  mul_smul := by
    intro c₁ c₂ f
    by_cases h : l.NeBot
    · induction c₁, c₂, f using inductionOn₃ with | coe c₁ c₂ f
      rw [← coe_mul, ← coe_smul', ← coe_smul', ← coe_smul', mul_smul]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

instance instDistribMulAction [Monoid M] [AddMonoid N] [DistribMulAction M N] :
    DistribMulAction M (Germ l N) where
  smul_add := by
    intro c f g
    by_cases h : l.NeBot
    · induction f, g using inductionOn₂ with | coe f g
      rw [← coe_add, ← coe_smul, ← coe_smul, ← coe_smul, ← coe_add, smul_add]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _
  smul_zero := by
    intro c
    rw [← coe_zero, ← coe_smul, smul_zero]

instance instDistribMulAction' [Monoid M] [AddMonoid N] [DistribMulAction M N] :
    DistribMulAction (Germ l M) (Germ l N) where
  smul_add := by
    intro c f g
    by_cases h : l.NeBot
    · induction c, f, g using inductionOn₃ with | coe c f g
      rw [← coe_add, ← coe_smul', ← coe_smul', ← coe_smul', ← coe_add, smul_add]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _
  smul_zero := by
    intro c
    by_cases h : l.NeBot
    · induction c using inductionOn with | coe c
      rw [← coe_zero, ← coe_smul', smul_zero]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

instance instModule [Semiring R] [AddCommMonoid M] [Module R M] : Module R (Germ l M) where
  add_smul := by
    intro c₁ c₂ f
    by_cases h : l.NeBot
    · induction f using inductionOn with | coe f
      rw [← coe_smul, ← coe_smul, ← coe_smul, ← coe_add, add_smul]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _
  zero_smul := by
    intro f
    by_cases h : l.NeBot
    · induction f using inductionOn with | coe f
      rw [← coe_smul, ← coe_zero, zero_smul]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

instance instModule' [Semiring R] [AddCommMonoid M] [Module R M] :
    Module (Germ l R) (Germ l M) where
  add_smul := by
    intro c₁ c₂ f
    by_cases h : l.NeBot
    · induction c₁, c₂, f using inductionOn₃ with | coe c₁ c₂ f
      rw [← coe_add, ← coe_smul', ← coe_smul', ← coe_smul', ← coe_add, add_smul]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _
  zero_smul := by
    intro f
    by_cases h : l.NeBot
    · induction f using inductionOn with | coe f
      rw [← coe_zero, ← coe_zero, ← coe_smul', zero_smul]
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

end Module

instance instLE [LE β] : LE (Germ l β) := ⟨LiftRel (· ≤ ·)⟩

theorem le_def [LE β] : ((· ≤ ·) : Germ l β → Germ l β → Prop) = LiftRel (· ≤ ·) :=
  rfl

@[simp]
theorem coe_le [LE β] : (f : Germ l β) ≤ g ↔ f ≤ᶠ[l] g :=
  liftRel_coe

theorem coe_nonneg [LE β] [Zero β] {f : α → β} : 0 ≤ (f : Germ l β) ↔ ∀ᶠ x in l, 0 ≤ f x := by
  rw [← coe_zero, coe_le]
  rfl

theorem const_le [LE β] {x y : β} : x ≤ y → (↑x : Germ l β) ≤ ↑y :=
  liftRel_const

@[norm_cast]
theorem const_le_iff [LE β] [NeBot l] {x y : β} : (↑x : Germ l β) ≤ ↑y ↔ x ≤ y :=
  liftRel_const_iff

instance instPreorder [Preorder β] : Preorder (Germ l β) where
  le_refl := by
    intro f
    by_cases h : l.NeBot
    · induction f using inductionOn with | coe f
      rw [coe_le]
    · exact (h.elim ·)
  le_trans := by
    intro u v w huv hvw
    by_cases h : l.NeBot
    · induction u, v, w using inductionOn₃ with | coe u v w
      rw [coe_le] at huv hvw ⊢
      exact huv.trans hvw
    · exact (h.elim ·)

instance instPartialOrder [PartialOrder β] : PartialOrder (Germ l β) where
  le_antisymm := by
    intro u v huv hvu
    by_cases h : l.NeBot
    · induction u, v using inductionOn₂ with | coe u v
      rw [coe_le] at huv hvu
      rw [coe_eq]
      exact huv.antisymm hvu
    · cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

instance instBot [Bot β] : Bot (Germ l β) := ⟨↑(⊥ : β)⟩
instance instTop [Top β] : Top (Germ l β) := ⟨↑(⊤ : β)⟩

@[simp, norm_cast]
theorem const_bot [Bot β] : (↑(⊥ : β) : Germ l β) = ⊥ :=
  rfl

@[simp, norm_cast]
theorem const_top [Top β] : (↑(⊤ : β) : Germ l β) = ⊤ :=
  rfl

instance instOrderBot [LE β] [OrderBot β] : OrderBot (Germ l β) where
  bot_le := by
    intro f
    by_cases h : l.NeBot
    · induction f using inductionOn with | coe f
      rw [← const_bot, coe_le]
      exact .of_forall fun _ => bot_le
    · exact (h.elim ·)

instance instOrderTop [LE β] [OrderTop β] : OrderTop (Germ l β) where
  le_top := by
    intro f
    by_cases h : l.NeBot
    · induction f using inductionOn with | coe f
      rw [← const_top, coe_le]
      exact .of_forall fun _ => le_top
    · exact (h.elim ·)

instance instBoundedOrder [LE β] [BoundedOrder β] : BoundedOrder (Germ l β) where

instance instSup [Max β] : Max (Germ l β) := ⟨map₂ (· ⊔ ·)⟩
instance instInf [Min β] : Min (Germ l β) := ⟨map₂ (· ⊓ ·)⟩

@[simp, norm_cast]
theorem coe_sup [Max β] (a b : α → β) : ↑(a ⊔ b) = (↑a ⊔ ↑b : Germ l β) :=
  (map₂_coe (· ⊔ ·) a b).symm

@[simp, norm_cast]
theorem coe_inf [Min β] (a b : α → β) : ↑(a ⊓ b) = (↑a ⊓ ↑b : Germ l β) :=
  (map₂_coe (· ⊓ ·) a b).symm

@[simp, norm_cast]
theorem const_sup [Max β] (a b : β) : ↑(a ⊔ b) = (↑a ⊔ ↑b : Germ l β) :=
  (map₂_coe (· ⊔ ·) _ _).symm

@[simp, norm_cast]
theorem const_inf [Min β] (a b : β) : ↑(a ⊓ b) = (↑a ⊓ ↑b : Germ l β) :=
  (map₂_coe (· ⊓ ·) _ _).symm

instance instSemilatticeSup [SemilatticeSup β] : SemilatticeSup (Germ l β) where
  sup := max
  le_sup_left := by
    intro u v
    by_cases h : l.NeBot
    · induction u, v using inductionOn₂ with | coe u v
      rw [← coe_sup, coe_le]
      exact .of_forall fun _ => le_sup_left
    · exact (h.elim ·)
  le_sup_right := by
    intro u v
    by_cases h : l.NeBot
    · induction u, v using inductionOn₂ with | coe u v
      rw [← coe_sup, coe_le]
      exact .of_forall fun _ => le_sup_right
    · exact (h.elim ·)
  sup_le := by
    intro u v w huw hvw
    by_cases h : l.NeBot
    · induction u, v, w using inductionOn₃ with | coe u v w
      rw [coe_le] at huw hvw
      rw [← coe_sup, coe_le]
      exact hvw.mp <| huw.mono fun _ => sup_le
    · exact (h.elim ·)

instance instSemilatticeInf [SemilatticeInf β] : SemilatticeInf (Germ l β) where
  inf := min
  inf_le_left := by
    intro u v
    by_cases h : l.NeBot
    · induction u, v using inductionOn₂ with | coe u v
      rw [← coe_inf, coe_le]
      exact .of_forall fun _ => inf_le_left
    · exact (h.elim ·)
  inf_le_right := by
    intro u v
    by_cases h : l.NeBot
    · induction u, v using inductionOn₂ with | coe u v
      rw [← coe_inf, coe_le]
      exact .of_forall fun _ => inf_le_right
    · exact (h.elim ·)
  le_inf := by
    intro u v w huv huw
    by_cases h : l.NeBot
    · induction u, v, w using inductionOn₃ with | coe u v w
      rw [coe_le] at huv huw
      rw [← coe_inf, coe_le]
      exact huw.mp <| huv.mono fun _ => le_inf
    · exact (h.elim ·)

instance instLattice [Lattice β] : Lattice (Germ l β) where

instance instDistribLattice [DistribLattice β] : DistribLattice (Germ l β) where
  le_sup_inf := by
    intro u v w
    by_cases h : l.NeBot
    · induction u, v, w using inductionOn₃ with | coe u v w
      simp only [← coe_inf, ← coe_sup, coe_le]
      exact .of_forall fun _ => le_sup_inf
    · exact (h.elim ·)

@[to_additive]
instance instExistsMulOfLE [Mul β] [LE β] [ExistsMulOfLE β] : ExistsMulOfLE (Germ l β) where
  exists_mul_of_le := by
    intro f g hfg
    by_cases h : l.NeBot
    · induction f, g using inductionOn₂ with | coe f g
      rw [coe_le] at hfg
      choose c hc using fun x (hx : f x ≤ g x) ↦ exists_mul_of_le hx
      classical
      refine ⟨ofFun fun x ↦ if hx : f x ≤ g x then c x hx else f x, ?_⟩
      rw [← coe_mul, coe_eq]
      filter_upwards [hfg] with x hx
      rw [Pi.mul_apply, dite_eq_left hx, hc x hx]
    · refine ⟨f, ?_⟩
      cases Filter.not_neBot.1 h
      exact (Product.subsingleton_iff.2 (.inr Filter.eventually_bot)).allEq _ _

end Germ

end Germ

end Filter
