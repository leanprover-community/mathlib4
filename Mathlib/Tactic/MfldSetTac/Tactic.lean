import Mathlib.Tactic.MfldSetTac.Attr
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum

open Lean Meta Elab Tactic

@[ext]
theorem Set.ext {α : Type u} {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) :
a = b := sorry

elab (name := mfldSetTac) "mfld_set_tac" : tactic => withMainContext do
  let g ← getMainGoal
  let goalTy := (← instantiateMVars (← getMVarDecl g).type).getAppFnArgs
  match goalTy with
  | (``Eq, #[_ty, _e₁, _e₂]) =>
    evalTactic (← `(tactic| apply Set.ext;  intro my_y; constructor <;> { intro h_my_y;
                            try { simp only [*, mfld_simps] at h_my_y
                                  simp only [*, mfld_simps] } }))
  | (``Subset.subset, #[_ty, _inst, _e₁, _e₂]) =>
    evalTactic (← `(tactic| intro my_y h_my_y;
                            try { simp only [*, mfld_simps] at h_my_y
                                  simp only [*, mfld_simps] }))
  | _ => throwError "goal should be an equality or an inclusion"

  --match goal with
  --| `(%%e₁ = %%e₂) :=
  --    `[ext my_y,
  --      split;
  --      { assume h_my_y,
  --        try { simp only [*, -h_my_y] with mfld_simps at h_my_y },
  --        simp only [*] with mfld_simps }]
  --| `(%%e₁ ⊆ %%e₂) :=
  --    `[assume my_y h_my_y,
  --      try { simp only [*, -h_my_y] with mfld_simps at h_my_y },
  --      simp only [*] with mfld_simps]
  --| _ := tactic.fail "goal should be an equality or an inclusion"
  --end

--attribute [mfld_simps] mul_one
--
--example (x : Nat) : x * 1 = x := by
--  simp only [mfld_simps]

variable {α : Type u} {β : Type v} {γ : Type w}


/-! ## Syntax of objects and lemmas needed for testing `MfldSetTac` -/
section stub_lemmas

@[mfld_simps] theorem Set.memInterEq (x : α) (a b : Set α) : (x ∈ a ∩ b) = (x ∈ a ∧ x ∈ b) := sorry

def Set.Preimage (f : α → β) (s : Set β) : Set α := {x | f x ∈ s}

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


attribute [mfld_simps] and_true

    -- Set.memInterEq
    -- Set.memPreimage
    -- Set.preimageInter
    -- andTrue
    -- LocalEquiv.map_source
    -- LocalEquiv.trans_source
example  (e : LocalEquiv α β) (e' : LocalEquiv β γ) :
  (e.trans e').source = e.source ∩ Set.Preimage e (e.target ∩ e'.source) := by
mfld_set_tac
--apply Set.ext
--intro my_y
--constructor
--intro h_my_y
--simp only [*, mfld_simps] at h_my_y
--simp only [*, mfld_simps]
--intro h_my_y
--simp only [*, mfld_simps] at h_my_y
--simp only [*, mfld_simps]



/-
andTrue
LocalEquiv.map_source
LocalEquiv.symm_source
LocalEquiv.trans_source
Set.memInterEq
Set.memPreimage
-/
example (e : LocalEquiv α β) : (e.trans e.symm).source = e.source := by mfld_set_tac

/-
andTrue
LocalEquiv.symm_source
LocalHomeomorph.symm_to_LocalEquiv
Set.memInterEq
Set.memPreimage
-/
example (s : Set α) (f : LocalHomeomorph α β) :
  f.symm.toLocalEquiv.source ∩ (f.toLocalEquiv.target ∩ Set.Preimage f.symm s)
  = f.symm.toLocalEquiv.source ∩ Set.Preimage f.symm s := by mfld_set_tac

end tests
