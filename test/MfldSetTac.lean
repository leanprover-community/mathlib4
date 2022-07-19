import Mathlib.Tactic.MfldSetTac.Tactic

open Lean Meta Elab Tactic

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## Syntax of objects and lemmas needed for testing `MfldSetTac` -/
section stub_lemmas

@[mfld_simps] lemma Set.memSetOfEq {x : α} {p : α → Prop} :
  (x ∈ {y : α | p y}) = p x :=
sorry

@[mfld_simps] lemma Set.interUniv (a : Set α) : a ∩ Set.univ = a := sorry

@[mfld_simps] theorem Set.memInterEq (x : α) (a b : Set α) : (x ∈ a ∩ b) = (x ∈ a ∧ x ∈ b) := sorry

def Set.Preimage (f : α → β) (s : Set β) : Set α := {x | f x ∈ s}

@[mfld_simps] lemma Set.preimage_univ {f : α → β} :
  Set.preimage f Set.univ = Set.univ :=
sorry


@[mfld_simps] theorem Set.memPreimage {f : α → β} {s : Set β} {a : α} :
  (a ∈ Set.Preimage f s) ↔ (f a ∈ s) :=
sorry

@[mfld_simps] theorem Set.preimageInter {f : α → β} {s t : Set β} :
  (Set.Preimage f (s ∩ t)) = Set.Preimage f s ∩ Set.Preimage f t :=
sorry

variable (α) (β)

structure LocalEquiv :=
(toFun      : α → β)
(inv_fun     : β → α)
(source      : Set α)
(target      : Set β)

variable {α} {β}

instance : CoeFun (LocalEquiv α β) fun _ => α → β := ⟨LocalEquiv.toFun⟩

@[mfld_simps] theorem LocalEquiv.map_source (e : LocalEquiv α β) {x : α} (h : x ∈ e.source) :
  e x ∈ e.target :=
sorry

def LocalEquiv.symm (e : LocalEquiv α β) : LocalEquiv β α := sorry

@[mfld_simps] theorem LocalEquiv.symm_source (e : LocalEquiv α β) : e.symm.source = e.target :=
sorry

def LocalEquiv.trans (e : LocalEquiv α β) (e' : LocalEquiv β γ) : LocalEquiv α γ := sorry

@[mfld_simps] theorem LocalEquiv.trans_source (e : LocalEquiv α β) (e' : LocalEquiv β γ) :
  (e.trans e').source = (e.source ∩ Set.Preimage e e'.source) :=
sorry

variable (α) (β)
structure LocalHomeomorph extends LocalEquiv α β
variable {α} {β}

variable (f : LocalHomeomorph α β)

instance LocalHomeomorph.has_coe_to_fun : CoeFun (LocalHomeomorph α β) (λ _ => α → β) :=
⟨λ e => e.toFun⟩

def LocalHomeomorph.symm (e : LocalHomeomorph α β) : LocalHomeomorph β α := sorry

@[mfld_simps] theorem LocalHomeomorph.symm_toLocalEquiv (e : LocalHomeomorph α β) :
  e.symm.toLocalEquiv = e.toLocalEquiv.symm :=
sorry

end stub_lemmas


/-! ## Tests for `MfldSetTac`

Note: before trying these tests, need to make the `MfldSimps` simp attribute and label all the
previous section's lemmas with them.
-/
section tests

/-
Set.memInterEq
Set.memPreimage
Set.preimageInter
and_true
LocalEquiv.map_source
LocalEquiv.trans_source
-/
example  (e : LocalEquiv α β) (e' : LocalEquiv β γ) :
  (e.trans e').source = e.source ∩ Set.Preimage e (e.target ∩ e'.source) := by
mfld_set_tac

/-
and_true
LocalEquiv.map_source
LocalEquiv.symm_source
LocalEquiv.trans_source
Set.memInterEq
Set.memPreimage
-/
example (e : LocalEquiv α β) : (e.trans e.symm).source = e.source := by mfld_set_tac

/-
and_true
LocalEquiv.symm_source
LocalHomeomorph.symm_to_LocalEquiv
Set.memInterEq
Set.memPreimage
-/
example (s : Set α) (f : LocalHomeomorph α β) :
  f.symm.toLocalEquiv.source ∩ (f.toLocalEquiv.target ∩ Set.Preimage f.symm s)
  = f.symm.toLocalEquiv.source ∩ Set.Preimage f.symm s := by mfld_set_tac

end tests
