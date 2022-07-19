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

@[mfld_simps] lemma Set.preimage_univ {f : α → β} : Set.Preimage f Set.univ = Set.univ :=
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

@[mfld_simps] lemma LocalEquiv.leftInv (e : LocalEquiv α β) {x : α} (h : x ∈ e.source) :
  e.symm (e x) = x :=
sorry

def LocalEquiv.trans (e : LocalEquiv α β) (e' : LocalEquiv β γ) : LocalEquiv α γ := sorry

@[mfld_simps] theorem LocalEquiv.trans_source (e : LocalEquiv α β) (e' : LocalEquiv β γ) :
  (e.trans e').source = (e.source ∩ Set.Preimage e e'.source) :=
sorry

@[mfld_simps] lemma LocalEquiv.coeTrans (e : LocalEquiv α β) (e' : LocalEquiv β γ) :
  (e.trans e' : α → γ) = (e' : β → γ) ∘ e :=
sorry

@[mfld_simps] lemma LocalEquiv.coeTransSymm (e : LocalEquiv α β) (e' : LocalEquiv β γ) :
  ((e.trans e').symm : γ → α) = (e.symm : β → α) ∘ e'.symm :=
sorry

variable (α) (β)
structure LocalHomeomorph extends LocalEquiv α β
variable {α} {β}

variable (f : LocalHomeomorph α β)

instance LocalHomeomorph.has_coe_to_fun : CoeFun (LocalHomeomorph α β) (λ _ => α → β) :=
⟨λ e => e.toFun⟩

def LocalHomeomorph.symm (e : LocalHomeomorph α β) : LocalHomeomorph β α := sorry

@[mfld_simps] lemma LocalHomeomorph.leftInv (e : LocalHomeomorph α β) {x : α}
  (h : x ∈ e.toLocalEquiv.source) :
  e.symm (e x) = x :=
sorry

@[mfld_simps] theorem LocalHomeomorph.symmToLocalEquiv (e : LocalHomeomorph α β) :
  e.symm.toLocalEquiv = e.toLocalEquiv.symm :=
sorry

@[mfld_simps] lemma LocalHomeomorph.coe_coe (e : LocalHomeomorph α β) :
  (e.toLocalEquiv : α → β) = e :=
sorry

@[mfld_simps] lemma LocalHomeomorph.coe_coe_symm (e : LocalHomeomorph α β) :
  (e.toLocalEquiv.symm : β → α) = (e.symm : β → α) :=
sorry

structure ModelWithCorners (𝕜 E H : Type u) extends LocalEquiv H E :=
(source_eq : source = Set.univ)

attribute [mfld_simps] ModelWithCorners.source_eq

variables {𝕜 E H : Type u}

def ModelWithCorners.symm (I : ModelWithCorners 𝕜 E H) : LocalEquiv E H := sorry

instance ModelWithCorners.has_coe_to_fun : CoeFun (ModelWithCorners 𝕜 E H) (λ _ => H → E) :=
⟨λ e => e.toFun⟩

@[mfld_simps] lemma ModelWithCorners.leftInv (I : ModelWithCorners 𝕜 E H) (x : H) :
  I.symm (I x) = x :=
sorry

@[mfld_simps] lemma ModelWithCorners.to_local_equiv_coe (I : ModelWithCorners 𝕜 E H) :
  (I.toLocalEquiv : H → E) = I :=
sorry

@[mfld_simps] lemma ModelWithCorners.to_local_equiv_coe_symm (I : ModelWithCorners 𝕜 E H) :
  (I.toLocalEquiv.symm : E → H) = I.symm :=
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


example {𝕜 E H M E' H' M' E'' H'' M'' : Type u}
  {I : ModelWithCorners 𝕜 E H}
  {I' : ModelWithCorners 𝕜 E' H'}
  {I'' : ModelWithCorners 𝕜 E'' H''}
  (e₁: LocalHomeomorph M H)
  (e₂: LocalHomeomorph M' H')
  (e₃: LocalHomeomorph M'' H'')
  {f : M → M'}
  {g : M' → M''} :
  (Set.Preimage (f ∘ ((e₁.toLocalEquiv.trans I.toLocalEquiv).symm))
      (e₂.toLocalEquiv.trans I'.toLocalEquiv).source) ⊆
    {y : E |
    ((e₃.toLocalEquiv.trans I''.toLocalEquiv) ∘
          (g ∘ f) ∘ ((e₁.toLocalEquiv.trans I.toLocalEquiv).symm)) y
    = (((e₃.toLocalEquiv.trans I''.toLocalEquiv : M'' → E'') ∘
             g ∘ ((e₂.toLocalEquiv.trans I'.toLocalEquiv).symm)) ∘
          (e₂.toLocalEquiv.trans I'.toLocalEquiv : M' → E') ∘
            f ∘ ((e₁.toLocalEquiv.trans I.toLocalEquiv).symm)) y} := by
  mfld_set_tac

end tests
