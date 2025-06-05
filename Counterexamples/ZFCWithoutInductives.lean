/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.ZFC.Class

noncomputable section
namespace Counterexample
namespace NoInductives
universe u v

-- inductive types we can't avoid
def allowInductives := [``Subtype, ``False, ``Eq, ``HEq]
axiom mySorry {α} : α

def True : Prop := ∀ C : Prop, C → C
theorem trivial : True := fun _ H => H

def And (a b : Prop) : Prop := ∀ C : Prop, (a → b → C) → C
local infixr:35 (priority := high) " ∧ " => And
def And.mk {a b} (ha : a) (hb : b) : a ∧ b := fun _ H => H ha hb
def And.l {a b} (h : a ∧ b) : a := h _ fun h _ => h
def And.r {a b} (h : a ∧ b) : b := h _ fun _ h => h

local syntax "⟪" term,*,? "⟫" : term

local macro_rules
  | `(⟪$t1, $t2, $t3,*⟫) => `(⟪$t1, ⟪$t2, $t3,*⟫⟫)
  | `(⟪$t1, $t2⟫) => `(.mk $t1 $t2)
  | `(⟪$t1⟫) => `(.mk $t1)
  | `(⟪⟫) => `(.mk)

def Or (a b : Prop) : Prop := ∀ C : Prop, (a → C) → (b → C) → C
local infixr:30 (priority := high) " ∨ " => Or
theorem Or.inl {p q} (h : p) : p ∨ q := fun _ H _ => H h
theorem Or.inr {p q} (h : q) : p ∨ q := fun _ _ H => H h

def Iff (a b : Prop) : Prop := (a → b) ∧ (b → a)
local infix:20 (priority := high) " ↔ " => Iff
theorem Iff.rfl {a} : a ↔ a := ⟪id, id⟫
theorem Iff.symm {a b} (h : a ↔ b) : b ↔ a := ⟪h.r, h.l⟫
theorem Iff.trans {a b c} (h1 : a ↔ b) (h2 : b ↔ c) : a ↔ c := ⟪h2.l ∘ h1.l, h1.r ∘ h2.r⟫

def Exists {α : Sort*} (p : α → Prop) : Prop := ∀ C : Prop, (∀ x, p x → C) → C
open Lean TSyntax.Compat
local macro (priority := high)
  "∃" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``Exists xs b
def Exists.mk {α} {p : α → Prop} (a : α) (h : p a) : ∃ a, p a := fun _ H => H a h

local macro "ex_cases" t:term " with " ids:(ppSpace colGt rcasesPat)+ : tactic => do
  let rec toTerm : TSyntax ``binderIdent → MacroM Term
    | `(binderIdent| _) => `(_)
    | `(binderIdent| $x:ident) => `($x:ident)
    | _ => `(_)
  let rec mkList (p : Ident) (ids : List (TSyntax `rcasesPat)) : MacroM (List (TSyntax `tactic)) :=
    match ids with
    | [] => Macro.throwUnsupported
    | [a] => match a with
      | `(rcasesPat| $a:ident) =>
        return [← `(tactic| have $a:ident := @$p), ← `(tactic| try clear $p)]
      | _ => return [← `(tactic| obtain $a:rcasesPat := @$p), ← `(tactic| try clear $p)]
    | a :: l =>  do
      let x : Ident ← withFreshMacroScope `(x)
      return (← `(tactic| refine @$p _ ?_)) :: (← `(tactic| rintro $a:rcasesPat $x:ident)) ::
        (← `(tactic| try clear $p)) :: (← mkList x l)
  let (x, l) ← if t.raw.isIdent && t.raw.getId.isAtomic then
    pure ((⟨t.raw⟩:Ident), [])
  else
    let x : Ident ← withFreshMacroScope `(x)
    pure (x, [← `(tactic| have $x := $t)])
  `(tactic| ($((l ++ (← mkList x ids.toList)).toArray);*))

def Nonempty (α : Sort*) : Prop := ∀ C : Prop, (α → C) → C

def FunextType := ∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x},
  (∀ (x : α), f x = g x) → f = g

example      : FunextType := funext
axiom funext : FunextType

def PropextType := ∀ {a b : Prop}, (a ↔ b) → a = b

example       : PropextType := fun h => propext ⟨h.l, h.r⟩ ▸ rfl
axiom propext : PropextType

def ChoiceType := ∀ {α}, Nonempty α → α
example      : ChoiceType := fun h => Classical.choice (h _ fun a => ⟨a⟩)
axiom choice : ChoiceType

def indefiniteDescription {α : Sort u} (p : α → Prop) (h : ∃ x, p x) : {x // p x} :=
  choice (h _ fun a h _ f => f ⟨a, h⟩)

def choose {α} {p : α → Prop} (h : ∃ x, p x) : α := (indefiniteDescription _ h).1
theorem choose_spec {α} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription _ h).2

@[elab_as_elim]
def eq_rec {α} {a : α} {C : α → Sort u} {b : α} (t : a = b) (refl : C a) : C b :=
  Eq.rec (motive := fun a _ => C a) refl t

theorem em (p) : p ∨ ¬ p := by
  let U (a x : Prop) : Prop := x = a ∨ p
  have ex a : ∃ x, U a x := ⟪a, .inl rfl⟫
  let u (a : Prop) : Prop := choose (ex a)
  refine choose_spec (ex True) _ (fun hut : u _ = _ => ?_) .inl
  refine choose_spec (ex False) _ (fun hvf : u _ = _ => ?_) .inl
  refine .inr fun hp => ?_
  have : U True = U False := funext fun x => propext ⟪fun _ => .inr hp, fun _ => .inr hp⟫
  have eq : u True = u False :=
    eq_rec this (C := (∀ exV, u True = choose (p := ·) exV)) (fun _ => rfl) (ex _)
  exact (hut ▸ hvf ▸ eq) ▸ trivial

theorem dite_lem {α : Sort u} (c : Prop) (t : c → α) (e : ¬c → α) :
    ∃ a, (∀ h, a = t h) ∧ (∀ h, a = e h) :=
  em c _
    (fun h => ⟪t h, fun _ => rfl, fun h' => h'.elim h⟫)
    (fun h => ⟪e h, (h.elim ·), fun _ => rfl⟫)

def dite {α : Sort u} (c : Prop) (t : c → α) (e : ¬c → α) : α :=
  choose (dite_lem c t e)

theorem dite_pos {α : Sort u} {c : Prop} {t : c → α} {e : ¬c → α} (h : c) : dite c t e = t h :=
  (choose_spec (dite_lem c t e)).l _

theorem dite_neg {α : Sort u} {c : Prop} {t : c → α} {e : ¬c → α} (h : ¬c) : dite c t e = e h :=
  (choose_spec (dite_lem c t e)).r _

local macro_rules
  | `(if $h:ident : $c then $t else $e) => do
    let mvar ← Lean.withRef c `(?m)
    `(let_mvar% ?m := $c; wait_if_type_mvar% ?m;
      dite $mvar (fun $h:ident => $t) (fun $h:ident => $e))
  | `(if _%$h : $c then $t else $e) => do
    let mvar ← Lean.withRef c `(?m)
    `(let_mvar% ?m := $c; wait_if_type_mvar% ?m;
      dite $mvar (fun _%$h => $t) (fun _%$h => $e))

local macro_rules
  | `(if $c then $t else $e) => do
    let mvar ← Lean.withRef c `(?m)
    `(let_mvar% ?m := $c; wait_if_type_mvar% ?m; dite $mvar (fun _ => $t) (fun _ => $e))

def Acc {α} (R : α → α → Prop) (x : α) : Prop :=
  ∀ C : α → Prop, (∀ x, (∀ y, R y x → C y) → C x) → C x

theorem Acc.mk {α} {R : α → α → Prop} {x : α} (h : (y : α) → R y x → Acc R y) : Acc R x :=
  fun _ ih => ih _ fun _ hy => h _ hy _ ih

theorem Acc.inv {α r} {x y : α} (h₁ : Acc r x) (h₂ : r y x) : Acc r y := by
  refine (h₁ (fun z => Acc r z ∧ (r y z → Acc r y)) (fun _ ac => ⟪?_, fun h₂ => ?_⟫)).r h₂
  · refine ⟪fun y hy => (ac y hy).l⟫
  · refine (ac y h₂).l

def WellFounded {α} (R : α → α → Prop) : Prop := ∀ x, Acc R x

section
variable
  {α : Sort u} {C : α → Sort v} {r : α → α → Prop}
  (F : (x : α) → ((y : α) → r y x → C y) → C x)

def FixImage (x : α) (a : C x) : Prop :=
  ∀ D : ∀ x, C x → Prop,
    (∀ x f, (∀ y hy, D y (f y hy)) → D x (F x f)) →
    D x a

theorem FixImage.mk {x : α} (f : ∀ y, r y x → C y)
    (h : ∀ y hy, FixImage F y (f y hy)) : FixImage F x (F x f) :=
  fun _ ih => ih _ _ fun _ hy => h _ hy _ ih

theorem FixImage.inv {x : α} {a} (h₁ : FixImage F x a) :
    ∃ f, a = F x f ∧ ∀ y h, FixImage F y (f y h) := by
  refine (h₁ (fun x a => FixImage F x a ∧ ∃ f, a = F x f ∧ ∀ y h, FixImage F y (f y h)) ?_).r
  refine fun x f IH => ⟪.mk _ _ fun _ _ => (IH _ _).l, ?_⟫
  exact ⟪f, rfl, fun y hy => (IH _ _).l⟫

theorem FixImage.lem (x : α) (acx : Acc r x) : ∃ a : C x, ∀ a', FixImage F x a' ↔ a = a' := by
  refine acx (∃ a, ∀ a', FixImage F · a' ↔ a = a') fun x ih => ?_
  let f y hy := choose (ih y hy)
  have hf y hy : ∀ a', FixImage F y a' ↔ f y hy = a' := choose_spec (ih y hy)
  refine ⟪F _ f, fun a' => ?_⟫
  have : FixImage F x (F x f) := fun D IH => IH _ _ fun y hy => (hf _ hy _).r rfl _ IH
  refine ⟪fun H => ?_, fun eq => eq ▸ this⟫
  refine FixImage.inv _ H _ fun g H => ?_
  have eq : f = g := funext fun _ => funext fun hy => (hf _ hy _).l (H.r _ _)
  exact H.l ▸ eq ▸ rfl

def WellFounded.fixF (x : α) (acx : Acc r x) : C x :=
  choose (FixImage.lem F x acx)

theorem WellFounded.fixF_lem (x : α) (acx : Acc r x) : ∀ a, FixImage F x a ↔ fixF F x acx = a :=
  choose_spec (FixImage.lem F x acx)

theorem WellFounded.fixF_eq (x : α) (acx : Acc r x) :
    fixF F x acx = F x (fun (y : α) (p : r y x) => fixF F y (Acc.inv acx p)) :=
  (WellFounded.fixF_lem _ _ _ _).l <| .mk _ _ fun _ _ => (WellFounded.fixF_lem _ _ _ _).r rfl

def WellFounded.fix (hwf : WellFounded r) (x : α) : C x :=
  WellFounded.fixF F x (hwf x)

theorem WellFounded.fix_eq (hwf : WellFounded r) (x : α) :
    fix F hwf x = F x (fun y _ => fix F hwf y) := fixF_eq F x (hwf x)
end

def PUnit : Type u := False → Sort u
def PUnit.mk : PUnit := (·.elim)
theorem PUnit.eq (x y : PUnit) : x = y := funext (·.elim)

def ULift (α : Type v) : Type max u v := PUnit.{u} → α
def ULift.down {α} (x : ULift α) : α := x ⟪⟫
def ULift.up {α} (x : α) : ULift α := fun _ => x
theorem ULift.up_down {α} (x : ULift α) : .up x.down = x := funext fun h => h.eq ⟪⟫ ▸ rfl
theorem ULift.down_up {α} (x : α) : (ULift.up x).down = x := rfl

def PEmpty : Type u := Subtype fun _ : PUnit => False

def PLift (p : Prop) : Type u := if p then PUnit else PEmpty

def Prod (α : Type u) (β : Type v) : Type max u v :=
  ∀ p : Prop, if p then ULift.{v} α else ULift.{u} β
local infixr:35 (priority := high) " × " => Prod
def Prod.fst {α β} (x : α × β) : α := (cast (dite_pos trivial) (x True)).down
def Prod.snd {α β} (x : α × β) : β := (cast (dite_neg not_false) (x False)).down
def Prod.mk {α β} (a : α) (b : β) : α × β :=
  fun p => if h : p then cast (dite_pos h).symm (.up a) else cast (dite_neg h).symm (.up b)
theorem Prod.mk_fst {α β} (a : α) (b : β) : (Prod.mk a b).fst = a := by
  refine Eq.trans (congrArg ULift.down ?_) (ULift.down_up _)
  dsimp only [mk]
  conv => enter [1, 2]; rw [dite_pos trivial]
  rw [cast_cast]; rfl
theorem Prod.mk_snd {α β} (a : α) (b : β) : (Prod.mk a b).snd = b := by
  refine Eq.trans (congrArg ULift.down ?_) (ULift.down_up _)
  dsimp only [mk]
  conv => enter [1, 2]; rw [dite_neg not_false]
  rw [cast_cast]; rfl

theorem Prod.ext {α β} {x y : α × β} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y := by
  refine funext fun p => em p _ (fun h => ?_) (fun h => ?_)
  · refine propext ⟪fun _ => trivial, fun _ => h⟫ ▸ ?_
    have := (ULift.up_down _).symm.trans <| (congrArg ULift.up h1).trans (ULift.up_down _)
    generalize_proofs p at this; revert p
    generalize x True = a, y True = b; revert a b
    generalize dite .. = c at p
    rintro _ _ rfl h; exact h
  · refine propext (b := False) ⟪h.elim, (·.elim)⟫ ▸ ?_
    have := (ULift.up_down _).symm.trans <| (congrArg ULift.up h2).trans (ULift.up_down _)
    generalize_proofs p at this; revert p
    generalize x False = a, y False = b; revert a b
    generalize dite .. = c at p
    rintro _ _ rfl h; exact h

theorem Prod.fst_snd {α β} (x : α × β) : ⟪x.fst, x.snd⟫ = x :=
  Prod.ext (Prod.mk_fst ..) (Prod.mk_snd ..)

theorem Prod.exists {α β} (x : α × β) : ∃ a b, x = ⟪a, b⟫ := ⟪_, _, (Prod.fst_snd _).symm⟫

@[elab_as_elim]
theorem Prod.casesOn {α β} {C : α → β → α × β → Prop}
    (H : ∀ a b, C a b ⟪a, b⟫) (x : α × β) : C x.fst x.snd x :=
  (Prod.fst_snd x ▸ H x.fst x.snd :)

def Sigma {α : Type u} (β : α → Type v) : Type max u v :=
  { p : α × ∀ x, β x → β x //
    ∀ x, if p.fst = x then ∃ b, ∀ b', p.snd x b' = b else ∀ b, p.snd x b = b }

local macro:35 (priority := high)
  xs:bracketedExplicitBinders " × " b:term:35  : term => expandBrackedBinders ``Sigma xs b
def Sigma.fst {α} {β : α → _} (x : (a : α) × β a) : α := x.1.fst
def Sigma.snd {α} {β : α → _} (x : (a : α) × β a) : β x.fst :=
  x.1.snd x.1.fst (x.1.snd _ (choose (dite_pos rfl ▸ x.2 x.1.fst)))

def Sigma.mk {α} {β : α → _} (a : α) (b : β a) : (a : α) × β a := by
  refine let F := ⟪a, fun x b' => if h : a = x then h ▸ b else b'⟫; ⟨F, fun x => ?_⟩
  have F1 : F.fst = a := Prod.mk_fst ..
  have F2 : F.snd = _ := Prod.mk_snd ..
  refine if h : F.fst = x then ?_ else ?_
  · refine dite_pos h ▸ ?_
    exact ⟪F1.symm.trans h ▸ b, fun b' => F2 ▸ dite_pos (F1 ▸ h)⟫
  · refine dite_neg h ▸ fun b => ?_
    exact F2 ▸ dite_neg (F1 ▸ h)

theorem Sigma.mk_fst {α} {β : α → _} (a : α) (b : β a) : (Sigma.mk a b).fst = a := Prod.mk_fst ..
theorem Sigma.mk_snd {α} {β : α → _} (a : α) (b : β a) :
    (Sigma.mk a b).snd = Sigma.mk_fst .. ▸ b := by
  let F : (x : α) → β x → β x := fun x b' => if h : a = x then h ▸ b else b'
  have := dite_pos rfl ▸ (Sigma.mk a b).2 (Prod.mk a F).fst
  show (Prod.mk a F).snd (Prod.mk a F).fst ((Prod.mk a F).snd _ (choose this)) = _
  suffices ∀ a' F' (h : a' = a), F' = F → ∀ (z : β a'),
      F' a' (F' a' z) = h.symm ▸ b from this _ _ (Prod.mk_fst ..) (Prod.mk_snd ..) _
  rintro a _ rfl rfl z
  dsimp [F]; exact dite_pos rfl ▸ rfl

theorem Sigma.mk_snd_heq {α} {β : α → _} (a : α) (b : β a) :
    HEq (Sigma.mk a b).snd b := by
  refine Sigma.mk_snd .. ▸ ?_
  generalize_proofs p; revert p
  generalize (mk a b).fst = x
  rintro rfl; rfl

@[elab_as_elim]
theorem Sigma.cases_eq {α} {β : α → _} {C : ∀ a, β a → Prop} {a a' : α} {b : β a} {b' : β a'}
    (e : Sigma.mk a b = Sigma.mk a' b') (ih : C a b) : C a' b' := by
  cases Sigma.mk_fst .. ▸ e ▸ Sigma.mk_fst a b
  cases (Sigma.mk_snd_heq a b').symm.trans (e ▸ Sigma.mk_snd_heq a b)
  exact ih

theorem Sigma.ext {α} {β : α → _} {x y : (a : α) × β a}
    (h1 : x.fst = y.fst) (h2 : HEq x.snd y.snd) : x = y := by
  refine Subtype.ext <| Prod.ext h1 <| funext fun a => funext fun b => ?_
  let ⟨x, hx⟩ := x
  let ⟨y, hy⟩ := y
  dsimp [fst, snd] at *
  generalize choose .. = u at h2; generalize choose .. = v at h2
  revert hx hy h1 h2 u v
  refine Prod.casesOn (Prod.casesOn (fun y G x F hx hy h1 u v h2 => ?_) _) _
  subst h1; have h2 := eq_of_heq h2
  refine (dite_pos rfl ▸ hx x) _ fun b1 hxx => ?_
  refine (dite_pos rfl ▸ hy x) _ fun b2 hxy => ?_
  rw [hxx u, hxy v, hxx, hxy] at h2
  subst h2
  refine em (x = a) _ (fun h => ?_) (fun h => ?_)
  · subst h; exact hxy b ▸ hxx b
  · exact ((dite_neg h ▸ hy a) b).symm ▸ (dite_neg h ▸ hx a) b

theorem Sigma.fst_snd {α} {β : α → _} (x : (a : α) × β a) : ⟪x.fst, x.snd⟫ = x :=
  Sigma.ext (Sigma.mk_fst ..) (Sigma.mk_snd_heq ..)

theorem Sigma.exists {α} {β : α → _} (x : (a : α) × β a) : ∃ a b, x = ⟪a, b⟫ :=
  ⟪x.fst, x.snd, (fst_snd _).symm⟫

@[elab_as_elim]
theorem Sigma.casesOn {α} {β : α → _} {C : ((a : α) × β a) → (a : α) → β a → Prop}
    (H : ∀ a b, C ⟪a, b⟫ a b) (x : (a : α) × β a) : C x x.fst x.snd :=
  (Sigma.fst_snd x ▸ H x.fst x.snd :)

@[elab_as_elim]
theorem Sigma.revCasesOn {α} {β : α → _} {C : (a : α) → β a → ((a : α) × β a) → Prop}
    (H : ∀ x, C x.fst x.snd x) (a : α) (b : β a) : C a b ⟪a, b⟫ := by
  have := Sigma.mk_snd .. ▸ H ⟪a, b⟫
  generalize (Sigma.mk a b).fst = x, mk_fst a b = h at this
  subst h; exact this

def Sum (α : Type u) (β : Type v) : Type max u v :=
  (p : Prop) × if p then ULift.{v} α else ULift.{u} β
local infixr:35 (priority := high) " ⊕ " => Sum
def Sum.inl {α β} (x : α) : α ⊕ β := ⟪True, cast (dite_pos trivial).symm (.up x)⟫
def Sum.inr {α β} (x : β) : α ⊕ β := ⟪False, cast (dite_neg not_false).symm (.up x)⟫
def Sum.elim {α β γ} (x : α ⊕ β) (a : α → γ) (b : β → γ) : γ :=
  if h : x.fst then a (cast (dite_pos h) x.snd).down else b (cast (dite_neg h) x.snd).down

theorem Sum.elim_inl {α β γ} (a : α → γ) (b : β → γ) (x : α) : Sum.elim (.inl x) a b = a x := by
  refine (dite_pos (cast (Sigma.mk_fst ..).symm trivial)).trans ?_
  dsimp only [Sum.inl]; rw [Sigma.mk_snd]
  generalize_proofs h1 h2 h3; revert h2 h3
  generalize eq : cast h1 _ = z
  rw [Sigma.mk_fst]; rintro h2 ⟨⟩; show a (cast h2 z).down = _
  generalize dite .. = w at *; subst w z; show a (ULift.up x).down = _
  rw [ULift.down_up]

theorem Sum.elim_inr {α β γ} (a : α → γ) (b : β → γ) (x : β) : Sum.elim (.inr x) a b = b x := by
  refine (dite_neg (mt (cast (Sigma.mk_fst ..)) not_false)).trans ?_
  dsimp only [Sum.inr]; rw [Sigma.mk_snd]
  generalize_proofs h1 h2 h3; revert h2 h3
  generalize eq : cast h1 _ = z
  rw [Sigma.mk_fst]; rintro h2 ⟨⟩; show b (cast h2 z).down = _
  generalize dite .. = w at *; subst w z; show b (ULift.up x).down = _
  rw [ULift.down_up]

theorem Sum.exists {α β} (x : α ⊕ β) : (∃ a, x = .inl a) ∨ ∃ b, x = .inr b := by
  refine x.casesOn fun p q => em p _ (fun h => .inl ?_) (fun h => .inr ?_)
  · cases propext ⟪fun _ => h, fun _ => trivial⟫
    refine ⟪(dite_pos trivial ▸ q :).down, ?_⟫; congr 1
    generalize_proofs h1 h2; revert q
    generalize dite .. = w at *; subst w
    intro q; exact (ULift.up_down _).symm
  · cases propext ⟪(·.elim), h⟫
    refine ⟪(dite_neg not_false ▸ q :).down, ?_⟫; congr 1
    generalize_proofs h1 h2; revert q
    generalize dite .. = w at *; subst w
    intro q; exact (ULift.up_down _).symm

def Option (α : Type u) := Sum α PUnit.{0}
def Option.some {α} (x : α) : Option α := .inl x
def Option.none {α} : Option α := .inr ⟪⟫

def Equivalence {α : Type u} (r : α → α → Prop) : Prop :=
  (∀ x, r x x) ∧
  (∀ {x y}, r x y → r y x) ∧
  (∀ {x y z}, r x y → r y z → r x z)

def EqvGen {α : Type u} (r : α → α → Prop) (x y : α) : Prop :=
  ∀ C : α → α → Prop,
    Equivalence C →
    (∀ {{x y}}, r x y → C x y) →
    C x y

theorem EqvGen.eq_of_rel {α : Type u} {r : α → α → Prop} {x y} (H : EqvGen r x y) :
    EqvGen r x = EqvGen r y :=
  funext fun _ => propext ⟪
    fun h _ c1 c2 => c1.r.r (c1.r.l (H _ c1 c2)) (h _ c1 c2),
    fun h _ c1 c2 => c1.r.r (H _ c1 c2) (h _ c1 c2)⟫

def Quot {α : Type u} (r : α → α → Prop) : Type u :=
  { E : α → Prop // ∃ x, E = EqvGen r x }

def Quot.mk {α : Type u} (r : α → α → Prop) (a : α) : Quot r :=
  ⟨EqvGen r a, ⟪_, rfl⟫⟩

theorem Quot.eq_mk {α : Type u} {r : α → α → Prop}
    (a : α) (q : Quot r) (h : q.1 a) : q = ⟪r, a⟫ :=
  Subtype.ext <| q.2 _ fun _ h' => h'.trans (EqvGen.eq_of_rel (h' ▸ h))

def Quot.out {α : Type u} {r : α → α → Prop} (q : Quot r) : α := choose q.2

theorem Quot.mk_out {α : Type u} {r : α → α → Prop} (q : Quot r) : ⟪_, q.out⟫ = q :=
  Subtype.ext (choose_spec q.2).symm

def Quot.lift {α : Type u} {r : α → α → Prop} {β : Sort v} (f : α → β) (q : Quot r) : β := f q.out

theorem Quot.lift_mk {α : Type u} {r : α → α → Prop} {β : Sort v} (f : α → β)
    (H : ∀ (a b : α), r a b → f a = f b) (a : α) : Quot.lift f ⟪r, a⟫ = f a := by
  suffices ∀ b, EqvGen r a = EqvGen r b → f b = f a from this _ (choose_spec (Quot.mk r a).2)
  intro b h
  refine cast (congrFun h a) (fun _ c1 _ => c1.l a) (f · = f ·) ⟪?_, ?_, ?_⟫ H
  · exact fun _ => rfl
  · exact fun h => h.symm
  · exact fun h1 h2 => h1.trans h2

@[elab_as_elim]
theorem Quot.ind {α : Type u} {r : α → α → Prop} {β : Quot r → Prop}
    (ih : ∀ (a : α), β ⟪r, a⟫) (q : Quot r) : β q :=
  q.2 _ fun x h => (show q = ⟪r, x⟫ from Subtype.ext h) ▸ ih _

theorem Quot.sound {α : Type u} {r : α → α → Prop} {a b : α} (h : r a b) :
    Quot.mk r a = Quot.mk r b :=
  Quot.eq_mk _ _ (fun _ _ c2 => c2 h)

theorem Quot.exact {α : Type u} {r : α → α → Prop} (hr : Equivalence r) {a b : α}
    (h : Quot.mk r a = Quot.mk r b) : r a b :=
  have : (Quot.mk r a).1 b := h ▸ fun _ c1 _ => c1.l _
  this _ hr fun _ _ h => h

def IsWellOrder (α : Type u) (lt : α → α → Prop) : Prop :=
  (∀ a b, lt a b ∨ a = b ∨ lt b a) ∧
  (∀ {a b c}, lt a b → lt b c → lt a c) ∧
  WellFounded lt

def WellOrder : Type (u + 1) :=
  (α : Type u) × { r : α → α → Prop // IsWellOrder α r }

def IsRelEmbedding {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) (f : α → β) :=
  Function.Injective f ∧ ∀ {a b}, s (f a) (f b) ↔ r a b

def IsPrincipalSeg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) (f : α → β) (top : β) :=
  IsRelEmbedding r s f ∧ ∀ b, (∃ y, f y = b) ↔ s b top

def WellOrder.lt' {α β} (r : α → α → Prop) (s : β → β → Prop) : Prop :=
  ∃ f top, IsPrincipalSeg r s f top

theorem WellOrder.lt'.trans {α β γ} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
    (ht : IsWellOrder _ t) (h1 : lt' r s) (h2 : lt' s t) : lt' r t := by
  ex_cases h1 with f a h1; ex_cases h2 with g b h2
  refine ⟪g ∘ f, g a, ⟪?_, ?_⟫, ?_⟫
  · exact Function.Injective.comp h2.l.l h1.l.l
  · exact h2.l.r.trans h1.l.r
  · refine fun c => ⟪fun h => h _ fun x hx => ?_, fun h => ?_⟫
    · exact hx ▸ h2.l.r.r ((h1.r _).l ⟪_, rfl⟫)
    · have := ht.r.l h ((h2.r (g a)).l ⟪_, rfl⟫)
      refine (h2.r _).r this _ fun d hd => hd ▸ ?_
      have := h2.l.r.l (hd ▸ h)
      exact (h1.r _).r this _ fun e he => he ▸ ⟪_, rfl⟫

def WellOrder.lt (a b : WellOrder) : Prop := WellOrder.lt' a.snd.1 b.snd.1

def IsInverse {α β : Type*} (f : α → β) (g : β → α) :=
  (∀ x, f (g x) = x) ∧
  (∀ x, g (f x) = x)

def WellOrder.Equiv {α β} (r : α → α → Prop) (s : β → β → Prop) : Prop :=
  ∃ f g, IsInverse f g ∧ IsRelEmbedding r s f

protected theorem WellOrder.Equiv.rfl {α} {r : α → α → Prop} : Equiv r r :=
  ⟪id, id, ⟪fun _ => rfl, fun _ => rfl⟫, fun _ _ => id, .rfl⟫

theorem LeftInverse.injective {α β} {g : β → α} {f : α → β} :
    Function.LeftInverse g f → Function.Injective f :=
  fun h a b faeqfb => (h a).symm.trans <| .trans (congrArg g faeqfb) (h b)

theorem WellOrder.Equiv.symm {α β} {r : α → α → Prop} {s : β → β → Prop}
    (h : Equiv r s) : Equiv s r := by
  ex_cases h with f g h
  refine ⟪g, f, ⟪h.l.r, h.l.l⟫, LeftInverse.injective h.l.l, fun {a b} => ?_⟫
  exact h.r.r.symm.trans (h.l.l _ ▸ h.l.l _ ▸ .rfl)

theorem WellOrder.Equiv.trans {α β γ} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
    (h1 : Equiv r s) (h2 : Equiv s t) : Equiv r t := by
  ex_cases h1 with f1 g1 h1; ex_cases h2 with f2 g2 h2
  refine ⟪f2 ∘ f1, g1 ∘ g2, ⟪?_, ?_⟫, ?_, ?_⟫
  · exact fun x => show f2 (f1 (g1 (g2 x))) = x from h1.l.l _ ▸ h2.l.l _
  · exact fun x => show g1 (g2 (f2 (f1 x))) = x from h2.l.r _ ▸ h1.l.r _
  · exact Function.Injective.comp h2.r.l h1.r.l
  · exact h2.r.r.trans h1.r.r

def WellOrder.Equiv' (a b : WellOrder) : Prop := WellOrder.Equiv a.snd.1 b.snd.1

theorem WellOrder.Equiv'.mk_iff
    {α} {r : α → α → Prop} {hr : IsWellOrder α r}
    {β} {s : β → β → Prop} {hs : IsWellOrder β s} :
    WellOrder.Equiv' (Sigma.mk α ⟨r, hr⟩) (Sigma.mk β ⟨s, hs⟩) ↔
    WellOrder.Equiv r s := by
  show WellOrder.Equiv .. ↔ _
  refine Sigma.mk_snd .. ▸ Sigma.mk_snd .. ▸ ?_
  generalize_proofs p1 p2; revert p1 p2
  exact Sigma.mk_fst .. ▸ Sigma.mk_fst .. ▸ fun _ _ => .rfl

protected theorem WellOrder.Equiv'.rfl {a : WellOrder} : a.Equiv' a := Equiv.rfl

theorem WellOrder.Equiv'.symm {a b : WellOrder} (h : a.Equiv' b) : b.Equiv' a := Equiv.symm h

theorem WellOrder.Equiv'.trans {a b c : WellOrder}
    (h1 : a.Equiv' b) (h2 : b.Equiv' c) : a.Equiv' c := Equiv.trans h1 h2

theorem WellOrder.equivalence : Equivalence WellOrder.Equiv' :=
  ⟪fun _ => .rfl, (·.symm), (·.trans)⟫

theorem WellOrder.lt_equiv {α β γ} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
    (h1 : lt' r s) (h2 : Equiv s t) : lt' r t := by
  ex_cases h1 with F top hr htop; ex_cases h2 with f g fg inj rel
  refine ⟪f ∘ F, f top, ⟪?_, ?_⟫, fun x => ?_⟫
  · exact Function.Injective.comp inj hr.l
  · exact rel.trans hr.r
  · refine .trans ⟪fun h => ?_, fun h => ?_⟫ <| .trans (htop (g x)) ?_
    · exact h _ fun y h => ⟪y, inj (h.trans (fg.l _).symm)⟫
    · exact h _ fun y h => ⟪y, (congrArg f h).trans (fg.l _)⟫
    · exact rel.symm.trans (fg.l _ ▸ .rfl)

theorem WellOrder.Equiv.lt_r {α β γ} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
    (h : Equiv s t) : lt' r s ↔ lt' r t := ⟪(lt_equiv · h), (lt_equiv · h.symm)⟫

theorem WellOrder.equiv_lt {α β γ} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
    (h1 : Equiv r s) (h2 :  lt' s t) : lt' r t := by
  ex_cases h1 with f g fg inj rel; ex_cases h2 with F top hr htop
  refine ⟪F ∘ f, top, ⟪?_, ?_⟫, fun x => ?_⟫
  · exact Function.Injective.comp hr.l inj
  · exact hr.r.trans rel
  · refine .trans ⟪fun h => ?_, fun h => ?_⟫ (htop x)
    · exact h _ fun y h => ⟪f y, h⟫
    · exact h _ fun y h => ⟪g y, (congrArg F (fg.l _)).trans h⟫

theorem WellOrder.Equiv.lt_l {α β γ} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
    (h : Equiv r s) : lt' r t ↔ lt' s t := ⟪equiv_lt h.symm, equiv_lt h⟫

def Ordinal : Type (u + 1) :=
  Quot WellOrder.Equiv'

nonrec def Ordinal.mk (α) (r : α → α → Prop) (hr : IsWellOrder α r) : Ordinal := ⟪_, α, ⟨r, hr⟩⟫

def Ordinal.Below (o : Ordinal) := o.out.fst
def Ordinal.rel {o : Ordinal} : (x y : o.Below) → Prop := o.out.snd.1
def Ordinal.rel_wo {o : Ordinal} : IsWellOrder o.Below rel := o.out.snd.2

theorem Ordinal.mk_eq_mk
    {α} {r : α → α → Prop} {hr : IsWellOrder α r}
    {β} {s : β → β → Prop} {hs : IsWellOrder β s} :
    mk α r hr = mk β s hs ↔ WellOrder.Equiv r s :=
  .trans ⟪Quot.exact WellOrder.equivalence, Quot.sound⟫ WellOrder.Equiv'.mk_iff

theorem Ordinal.mk_equiv {α r hr} : WellOrder.Equiv (mk α r hr).rel r := by
  have := Quot.exact WellOrder.equivalence (mk α r hr).mk_out
  conv at this =>
    enter [1]; conv => exact (Sigma.fst_snd ..).symm
    enter [2]; exact (Subtype.eta _ (mk α r hr).out.snd.2).symm
  exact WellOrder.Equiv'.mk_iff.l this

def Ordinal.lt (a b : Ordinal) : Prop := WellOrder.lt' a.rel b.rel

def Ordinal.le (a b : Ordinal) : Prop := a.lt b ∨ a = b

theorem Ordinal.mk_lt_mk {α r hr β s hs} : (mk α r hr).lt (mk β s hs) ↔ WellOrder.lt' r s :=
  mk_equiv.lt_l.trans mk_equiv.lt_r

def type.A {α : Type*} (r : α → α → Prop) (y : α) := {z // r z y}
def type.R {α} (r : α → α → Prop) (y : α) (a b : A r y) := r a.1 b.1
theorem type.wo {α} {r : α → α → Prop}
    (H : IsWellOrder α r) (y : α) : IsWellOrder (A r y) (R r y) := by
  refine ⟪?_, H.r.l, ?_⟫
  · exact fun a b => H.l a.1 b.1 _ .inl fun h => .inr <| h _ (.inl ∘ Subtype.ext) .inr
  · refine fun x C ih => H.r.r x.1 (fun y => ∀ h, C ⟨y, h⟩) ?_ _
    exact fun z h1 hz => ih _ fun ⟨w, hw⟩ hr => h1 _ hr _

theorem type.lt {α} {r : α → α → Prop}
    (H : IsWellOrder α r) (y : α) : WellOrder.lt' (type.R r y) r := by
  refine ⟪?_, H.r.l, ?_⟫
  · exact fun a b => H.l a.1 b.1 _ .inl fun h => .inr <| h _ (.inl ∘ Subtype.ext) .inr
  · refine fun x C ih => H.r.r x.1 (fun y => ∀ h, C ⟨y, h⟩) ?_ _
    exact fun z h1 hz => ih _ fun ⟨w, hw⟩ hr => h1 _ hr _

def type (α) (r : α → α → Prop) (H : IsWellOrder α r) (y : α) : Ordinal :=
  .mk (type.A r y) (type.R r y) (type.wo H y)

theorem Ordinal.type_lt_mk (α) (r : α → α → Prop) (H : IsWellOrder α r) (y : α) :
    (type α r H y).lt (mk α r H) :=
  mk_lt_mk.r _

def Ordinal.Below.mk {o : Ordinal} (x : Ordinal) (h : x.lt o) : o.Below := sorry
def Ordinal.Below.fst {o : Ordinal} : o.Below → Ordinal := type o.Below rel rel_wo
def Ordinal.Below.snd {o : Ordinal} (x : o.Below) : x.fst.lt o := sorry
def Ordinal.Below.mk_fst {o : Ordinal} (x : Ordinal) (h : x.lt o) : (mk x h).fst = x := sorry

theorem Ordinal.Below.ext {o : Ordinal} {x y : o.Below} (h1 : x.fst = y.fst) : x = y := by
  sorry

theorem Ordinal.Below.fst_snd {o : Ordinal} (x : o.Below) : ⟪x.fst, x.snd⟫ = x := ext (mk_fst ..)

@[elab_as_elim]
theorem Ordinal.Below.casesOn {o : Ordinal} {C : o.Below → ∀ x : Ordinal, x.lt o → Prop}
    (H : ∀ a b, C ⟪a, b⟫ a b) (x : o.Below) : C x x.fst x.snd :=
  (fst_snd x ▸ H x.fst x.snd :)

@[elab_as_elim]
theorem Ordinal.casesOn {β : Ordinal → Prop}
    (ih : ∀ α r hr, β (.mk α r hr)) (o : Ordinal) : β o :=
  Quot.ind (Sigma.casesOn fun a b => ih a b.1 b.2) o

def Ordinal.succ : (a : Ordinal) → Ordinal := sorry
def Ordinal.lt_succ_self (a : Ordinal) : a.lt a.succ := sorry
def Ordinal.le_of_lt_succ {a b : Ordinal} (h : b.lt a.succ) : b.le a := sorry

nonrec theorem Ordinal.lt.trans {a b c} (h1 : lt a b) (h2 : lt b c) : lt a c := h1.trans c.rel_wo h2
  -- ex_cases h1 with αa ra ha αb rb hb ea eb h1
  -- ex_cases h2 with αb' rb' hb' αc rc hc eb' ec h2; subst ea eb ec
  -- refine ⟪_, _, ha, _, _, hc, rfl, rfl, ?_⟫
  -- have := WellOrder.lt_equiv' h1 <| Ordinal.mk_eq_mk.l eb'
  -- exact this.trans hc h2

theorem Ordinal.le_or_lt (a b : Ordinal) : le a b ∨ lt b a := by
  sorry

theorem Ordinal.lt.trans_le {a b c} (h1 : lt a b) (h2 : le b c) : lt a c :=
  h2 _ h1.trans (· ▸ h1)

theorem Ordinal.le.trans {a b c} (h1 : le a b) (h2 : le b c) : le a c :=
  h1 _ (.inl <| ·.trans_le h2) (· ▸ h2)

def Ordinal.max (a b : Ordinal) : Ordinal := if a.le b then b else a

theorem Ordinal.le_max_left (a b : Ordinal) : a.le (a.max b) := sorry
theorem Ordinal.le_max_right (a b : Ordinal) : b.le (a.max b) := sorry

theorem IsPrincipalSeg.equiv {α β} {r : α → α → Prop} {s : β → β → Prop} {f : α → β} {top : β}
    (hyt : IsPrincipalSeg r s f top) : WellOrder.Equiv (type.R s top) r := by
  refine let F x := choose ((hyt.r _).r x.2); ⟪F, ?_⟫
  have hF (x : {z // s z top}) : f (F _) = _ := choose_spec ((hyt.r _).r x.2)
  refine ⟪fun x => ⟨f x, (hyt.r _).l ⟪_, rfl⟫⟩, ⟪?_, ?_⟫, ?_, ?_⟫
  · exact fun x => hyt.l.l (hF _)
  · exact fun x => Subtype.ext (hF _)
  · exact fun x y h => Subtype.ext <| (hF _).symm.trans <| (congrArg f h).trans (hF _)
  · exact hyt.l.r.symm.trans ((hF _).symm ▸ (hF _).symm ▸ .rfl)

theorem Ordinal.wf : @WellFounded Ordinal Ordinal.lt := by
  intro o C ih; --ex_cases id ih with y αy ry hy αo ro ho rfl - yo yt hyt
  --refine (Ordinal.mk_eq_mk (hr := type.wo ho _)).r hyt.equiv ▸ ?_
  refine Ordinal.rel_wo.r.r yt (fun y => C (type _ _ ho y)) fun x hx => ih _ fun z zx => ?_
  suffices tz : ∃ z', ro z' x ∧ .mk _ _ (type.wo ho z') = z from tz _ fun z' hz => hz.r ▸ hx _ hz.l
  ex_cases zx with αz rz hz αx' rx' hx' rfl zx1 zx2
  ex_cases WellOrder.lt_equiv' zx2 (Ordinal.mk_eq_mk.l zx1).symm with f' ⟨zt, zx⟩ hzt
  refine ⟪zt, zx, Ordinal.mk_eq_mk.r <| .trans ?_ hzt.equiv⟫
  exact ⟪fun ⟨a, ha⟩ => ⟨⟨a, ho.r.l ha zx⟩, ha⟩, fun ⟨a, ha⟩ => ⟨a.1, ha⟩,
    ⟪fun _ => rfl, fun _ => rfl⟫, fun x y h => Subtype.ext (congrArg (·.1.1) h), .rfl⟫

theorem Ordinal.wo : IsWellOrder Ordinal Ordinal.lt :=
  ⟪fun a b => le_or_lt a b _ (fun h => h _ .inl (.inr ∘ .inl)) (.inr ∘ .inr), .trans, wf⟫

def Ordinal.univ : Ordinal.{u+1} := .mk _ _ Ordinal.wo

theorem Ordinal.lt_univ (a : Ordinal.{u}) : a.lt univ.{u} := by
  refine a.casesOn fun α r wo => ?_
  -- refine ⟪_, _, _, _, _, _, rfl, rfl, type α r wo, .mk α r wo, ?_, ?_⟫
  · sorry
  -- · sorry

theorem exists_wellOrder (α : Type u) : ∃ r : α → α → Prop, IsWellOrder α r := by
  refine em (∃ β r f, @IsWellOrder.{u} β r ∧ Function.Injective (f : α → β)) _ ?_ ?_ <;> intro H
  · ex_cases H with β r f wo inj
    sorry
  · let G (x : Ordinal.{u}) (ih : ∀ y : Ordinal, y.lt x → Option α) : Option α :=
      if h : ∃ x : α, ∀ y h, ih y h ≠ .some x then .some (choose h) else .none
    let F : Ordinal → Option α := Ordinal.wf.fix G
    have (b) := by
      refine Ordinal.wf b
        (fun b => ∃ y, F b = .some y ∧ ∀ a, a.lt b → ∃ x, F a = .some x ∧ x ≠ y) ?_
      intro b ih
      suffices hg : ∃ x : α, ∀ y, y.lt b → F y ≠ .some x by
        have := (Ordinal.wf.fix_eq G b).trans (dite_pos hg)
        refine ⟪_, this, fun a ha => ?_⟫
        ex_cases ih a ha with y eq hy
        refine ⟪y, eq, ?_⟫; rintro rfl
        exact choose_spec hg _ ha eq
      refine em _ _ id fun h => (H ?_).elim
      sorry
    sorry

def Ordinal.supr {ι : Type u} (x : ι → Ordinal.{u}) : Ordinal.{u} := sorry

def PSet.F (P : Ordinal.{u} → Prop) (ih : (y : Ordinal) → P y → Type (u + 1)) : Type (u + 1) :=
  (y : {y // P y}) × (ih y.1 y.2 → Prop)

def PElem : Ordinal → Type u := Ordinal.wf.fix fun o ih => (y : o.Below) × (ih y.fst y.snd → Prop)
abbrev PSet o := PElem o → Prop

def PElem.unfold (o) : PElem o = ((y : o.Below) × PSet y.fst) := Ordinal.wf.fix_eq ..

open PElem PSet

def PElem.out {o} (f : PElem o) : (y : o.Below) × PSet y.fst :=
  cast (unfold o) f

def PElem.mk {o} (y) (hy : y.lt o) (s : PSet y) : PElem o :=
  cast (unfold o).symm ⟪⟪y, hy⟫, Ordinal.Below.mk_fst .. ▸ s⟫

theorem PElem.out_mk {o} (y) (hy : y.lt o) (s : PSet y) :
    out (.mk y hy s) = ⟪⟪y, hy⟫, Ordinal.Below.mk_fst .. ▸ s⟫ := by
  unfold mk out; generalize_proofs p q; revert p q
  generalize PElem o = x; rintro rfl _; rfl

theorem PElem.fst_out_mk {o} (y) (hy : y.lt o) (s : PSet y) :
    (mk y hy s).out.fst = ⟪y, hy⟫ := out_mk .. ▸ Sigma.mk_fst ..

theorem PElem.fst_fst_out_mk {o} (y) (hy : y.lt o) (s : PSet y) :
    (mk y hy s).out.fst.fst = y :=
  (congrArg Ordinal.Below.fst (fst_out_mk ..)).trans (Ordinal.Below.mk_fst ..)

theorem PElem.snd_out_mk {o} (y) (hy : y.lt o) (s : PSet y) :
    HEq (mk y hy s).out.snd s := out_mk .. ▸ (Sigma.mk_snd_heq ..).trans (eqRec_heq ..)

theorem PElem.exists {o} (a : PElem o) : ∃ y hy s, a = .mk y hy s := by
  refine ⟪a.out.fst.fst, a.out.fst.snd, a.out.snd, ?_⟫
  unfold mk out; generalize_proofs p1 p2 p3 p4; revert p1 p2 p3 a
  generalize PElem o = x; rintro a rfl ⟨⟩
  refine a.casesOn fun y f h1 h2 => Sigma.ext ?_ ?_
  · refine (Sigma.mk_fst ..).trans <| .trans ?_ (Sigma.mk_fst ..).symm
    exact Ordinal.Below.ext h2
  · refine (Sigma.mk_snd_heq ..).trans <| .trans ?_ (Sigma.mk_snd_heq ..).symm
    exact (eqRec_heq ..).symm

@[elab_as_elim]
theorem PElem.casesOn {o} {C : PElem o → ∀ y, y.lt o → PSet y → Prop}
  (H : ∀ y hy s, C (.mk y hy s) y hy s) (a) : C a a.out.fst.fst a.out.fst.snd a.out.snd := by
  ex_cases PElem.exists a with y hy s ⟨⟩
  generalize_proofs h; revert h
  generalize eq1 : (mk ..).out.fst.fst = x, eq2 : (mk ..).out.snd = y
  cases (PElem.fst_fst_out_mk ..).symm.trans eq1
  cases (PElem.snd_out_mk ..).symm.trans eq2
  exact fun _ => H ..

@[elab_as_elim]
theorem PElem.revCasesOn {o} {C : ∀ y, y.lt o → PSet y → PElem o → Prop}
  (H : ∀ a, C a.out.fst.fst a.out.fst.snd a.out.snd a) (y hy s) : C y hy s (.mk y hy s) := by
  have := H (.mk y hy s); revert this
  generalize_proofs h; revert h
  generalize eq1 : (mk ..).out.fst.fst = x, eq2 : (mk ..).out.snd = y
  cases (PElem.fst_fst_out_mk ..).symm.trans eq1
  cases (PElem.snd_out_mk ..).symm.trans eq2
  exact fun _ => id

@[elab_as_elim]
theorem PElem.cases_eq {o} {C : ∀ y, y.lt o → PSet y → Prop} {y y' hy hy' s s'}
    (e : mk y hy s = mk y' hy' s') (ih : C y hy s) : C y' hy' s' := by
  cases (fst_fst_out_mk ..).symm.trans <| (congr_arg (·.out.fst.fst) e).trans (fst_fst_out_mk ..)
  cases (snd_out_mk ..).symm.trans <| (congr_arg_heq (·.out.snd) e).trans (snd_out_mk ..)
  exact ih

def PElem.embed {a b} (h : a.le b) (f : PElem a) : PElem b :=
  .mk f.out.fst.fst (f.out.fst.snd.trans_le h) f.out.snd

theorem PElem.embed_mk {a b} (h : a.le b) (y) (hy : y.lt a) (s : PSet y) :
    embed h (.mk y hy s) = .mk y (hy.trans_le h) s := by
  unfold embed
  generalize_proofs h; revert h
  generalize eq1 : (mk ..).out.fst.fst = x, eq2 : (mk ..).out.snd = y
  cases (PElem.fst_fst_out_mk ..).symm.trans eq1
  cases (PElem.snd_out_mk ..).symm.trans eq2
  exact fun _ => rfl

theorem PElem.embed_id {a} (x : PElem a) : embed (.inr rfl) x = x :=
  x.casesOn fun _ _ _ => embed_mk ..

theorem PElem.embed_comp {a b c} (x : PElem a) (h₁ : a.le b) (h₂ : b.le c) :
    embed h₂ (embed h₁ x) = embed (h₁.trans h₂) x :=
  x.casesOn fun _ _ _ => embed_mk ..

def PSet.embed {a b} (h : a.le b) (f : PSet a) : PSet b :=
  fun x => ∃ y, f y ∧ y.embed h = x

def onSet {α β} (R : α → β → Prop) (s : α → Prop) (t : β → Prop) : Prop :=
  (∀ x, s x → ∃ y, t y ∧ R x y) ∧ (∀ y, t y → ∃ x, s x ∧ R x y)

def PElem.equivF (P : Ordinal → Prop) (eqv : ∀ y, P y → PElem y → PElem y → Prop)
    {u v : Ordinal} (hu : P u) (hv : P v) (x : PElem u) (y : PElem v) : Prop :=
  (∃ uv : u.le v, eqv _ hv (embed uv x) y) ∨
  (∃ vu : v.lt u, eqv _ hu x (embed (.inl vu) y))

def PElem.Equiv {o} : PElem o → PElem o → Prop := by
  refine Ordinal.wf.fix (C := fun o => PElem o → PElem o → Prop) (fun o eqv a b => ?_) o
  exact ∃ u hu s, a = .mk u hu s ∧ ∃ v hv t, b = .mk v hv t ∧ onSet (PElem.equivF _ eqv hu hv) s t

def PElem.Equiv₂ {u v : Ordinal} : PElem u → PElem v → Prop :=
  equivF (fun _ => True) (fun _ _ => Equiv) trivial trivial

def PSet.Equiv {u v : Ordinal} : PSet u → PSet v → Prop := onSet Equiv₂

def PSet.Subset {u v : Ordinal} (s : PSet u) (t : PSet v) : Prop := ∀ x, s x → ∃ y, t y ∧ x.Equiv₂ y

theorem PElem.Equiv₂.rfl {u} {a : PElem u} : a.Equiv₂ a := sorry

theorem PElem.Equiv₂.symm {u v} {a : PElem u} {b : PElem v}
    (h1 : a.Equiv₂ b) : b.Equiv₂ a := sorry

theorem PElem.Equiv₂.trans {u v w} {a : PElem u} {b : PElem v} {c : PElem w}
    (h1 : a.Equiv₂ b) (h2 : b.Equiv₂ c) : a.Equiv₂ c := sorry

theorem PElem.Equiv₂.embed {u v} {a : PElem u} {h : u.le v} : (embed h a).Equiv₂ a := sorry

theorem PSet.Equiv.embed {u v} {s : PSet u} {h : u.le v} : (embed h s).Equiv s := by
  refine ⟪fun a ha => ?_, fun a ha => ?_⟫
  · ex_cases ha with _ h1 (rfl); exact ⟪_, h1, Equiv₂.embed⟫
  · exact ⟪_, ⟪_, ha, rfl⟫, Equiv₂.embed⟫

theorem PSet.Subset.rfl {u} {a : PSet u} : a.Subset a := fun _ h => ⟪_, h, .rfl⟫

theorem PSet.Subset.trans {u v w} {a : PSet u} {b : PSet v} {c : PSet w}
    (h1 : a.Subset b) (h2 : b.Subset c) : a.Subset c :=
  fun _ h => h1 _ h _ fun _ h1 => h2 _ h1.l _ fun _ h2 => ⟪_, h2.l, h1.r.trans h2.r⟫

theorem PSet.Subset.rev {u v : Ordinal} {s : PSet u} {t : PSet v} :
    s.Subset t ↔ ∀ x, s x → ∃ y, t y ∧ y.Equiv₂ x := by
  apply And.mk <;> exact fun H _ h => H _ h _ fun _ H => ⟪_, H.l, H.r.symm⟫

nonrec theorem PSet.Equiv.mk {u v} {a : PSet u} {b : PSet v}
    (h1 : a.Subset b) (h2 : b.Subset a) : a.Equiv b := ⟪h1, Subset.rev.l h2⟫

theorem PSet.Equiv.sub_l {u v} {a : PSet u} {b : PSet v} (h : a.Equiv b) : a.Subset b := h.l

theorem PSet.Equiv.sub_r {u v} {a : PSet u} {b : PSet v} (h : a.Equiv b) : b.Subset a :=
  Subset.rev.r h.r

theorem PSet.Equiv.rfl {u} {a : PSet u} : a.Equiv a := ⟪.rfl, .rfl⟫

theorem PSet.Equiv.symm {u v} {a : PSet u} {b : PSet v}
    (h1 : a.Equiv b) : b.Equiv a := ⟪h1.sub_r, h1.sub_l⟫

theorem PSet.Equiv.trans {u v w} {a : PSet u} {b : PSet v} {c : PSet w}
    (h1 : a.Equiv b) (h2 : b.Equiv c) : a.Equiv c :=
  ⟪h1.sub_l.trans h2.sub_l, h2.sub_r.trans h1.sub_r⟫

theorem PElem.Equiv.iff {o} (a b : PElem o) :
    Equiv a b ↔ ∃ u hu s, a = .mk u hu s ∧ ∃ v hv t, b = .mk v hv t ∧ s.Equiv t := by
  refine (show @Equiv o = _ from Ordinal.wf.fix_eq ..) ▸ .rfl

theorem PElem.Equiv.mk_iff {o} {u} {hu : u.lt o} {s : PSet u} {v} {hv : v.lt o} {t : PSet v} :
    Equiv (.mk u hu s) (.mk v hv t) ↔ s.Equiv t := by
  refine (Equiv.iff _ _).trans ⟪fun H => ?_, fun H => ?_⟫
  · ex_cases H with u' hu' s' eq1 v' hv' t' eq2 H
    refine cases_eq (C := fun _ _ t => s.Equiv t) eq2.symm ?_
    exact cases_eq (C := fun _ _ s => s.Equiv t') eq1.symm H
  · exact ⟪_, _, _, rfl, _, _, _, rfl, H⟫

theorem PElem.Equiv₂.mk_iff {o o'} {u} {hu : u.lt o} {s : PSet u} {v} {hv : v.lt o'} {t : PSet v} :
    Equiv₂ (.mk u hu s) (.mk v hv t) ↔ s.Equiv t := sorry

def PSet.Equiv' (a b : (o : Ordinal.{u}) × PSet o) : Prop := a.snd.Equiv b.snd

theorem PSet.Equiv'.mk_iff {x} {f : PSet x} {y} {g : PSet y} :
    PSet.Equiv' ⟪x, f⟫ ⟪y, g⟫ ↔ f.Equiv g := by
  dsimp [Equiv']
  refine Sigma.revCasesOn (fun _ => ?_) x f
  refine Sigma.revCasesOn (fun _ => .rfl) y g

theorem PSet.equivalence : Equivalence PSet.Equiv' :=
  sorry

def PSet.powerset {o : Ordinal.{u}} (f : PSet o) : PSet o.succ :=
  fun b => b.out.snd.Subset f

theorem PSet.powerset_mk {o} (f : PSet o) (y hy s) :
    powerset f (.mk y hy s) = s.Subset f := revCasesOn (fun _ => rfl) y hy s

theorem PSet.Subset.exists_equiv {α β} {S : PSet α} {T : PSet β} (H : S.Subset T) :
    ∃ S' : PSet β, S'.Equiv S := by
  let S' : PSet β := fun x => ∃ y, S y ∧ x.Equiv₂ y
  refine ⟪S', fun _ => id, fun a ha => ?_⟫
  ex_cases H _ ha with b - hb
  exact ⟪b, ⟪_, ha, hb.symm⟫, hb⟫

theorem PSet.powerset.resp₁ {α β S T} (H : S.Equiv T) :
    (@powerset α S).Subset (@powerset β T) := by
  intro a h
  ex_cases PElem.exists a with γ hγ A (rfl); rw [powerset_mk] at h
  have := h.trans H.l
  ex_cases this.exists_equiv with A' eq
  exact ⟪.mk _ β.lt_succ_self A', powerset_mk .. ▸ .trans eq.l this, Equiv₂.mk_iff.r eq.symm⟫

def PSet.sep {o} (s : PSet.{u} o) (p : ∀ {{o}}, PSet o → Prop) : PSet o :=
  fun x => s x ∧ p x.out.snd

theorem PSet.sep_mk {o} (s : PSet.{u} o) (p : ∀ {{o}}, PSet o → Prop) (y hy t) :
    sep s p (.mk y hy t) = (s (.mk y hy t) ∧ p t) := PElem.revCasesOn (fun _ => rfl) y hy t

theorem PSet.sep.resp₁ {α β S T p q} (H : S.Equiv T)
    (H2 : ∀ {a b} s t, s.Equiv t → @p a s → @q b t) : (@sep α S p).Subset (@sep β T q) := by
  refine PElem.casesOn fun oa la a ha => ?_
  rw [sep_mk] at ha
  ex_cases H.l _ ha.l with b tb ab
  refine PElem.casesOn (fun ob lb b tb ab => ?_) b tb ab
  exact ⟪.mk ob lb b, sep_mk .. ▸ ⟪tb, H2 _ _ (Equiv₂.mk_iff.l ab) ha.r⟫, ab⟫

def ZFSet := Quot PSet.Equiv'

nonrec def ZFSet.mk {x} (f : PSet x) : ZFSet := ⟪_, x, f⟫

theorem ZFSet.mk_eq_mk {x} {s : PSet x} {y} {t : PSet y} : mk s = mk t ↔ s.Equiv t :=
  .trans ⟪Quot.exact PSet.equivalence, Quot.sound⟫ PSet.Equiv'.mk_iff

def ZFSet.lift {β : Sort v} (f : ∀ x, PSet x → β) : ZFSet → β :=
  Quot.lift fun x => f x.fst x.snd

theorem ZFSet.lift_mk {β : Sort v} (F : ∀ {{x}}, PSet x → β)
    (H : ∀ {o₁ o₂} {s : PSet o₁} {t : PSet o₂}, s.Equiv t → F s = F t)
    {x} (a : PSet x) : lift F ⟪a⟫ = F a :=
  (Quot.lift_mk _ (by exact fun _ _ => H) _).trans (Sigma.revCasesOn (fun _ => rfl) x a)

theorem ZFSet.lift_mk_set {O : Ordinal → Ordinal} (F : ∀ {{x}}, PSet x → PSet (O x))
    (H : ∀ {o₁ o₂} {s : PSet o₁} {t : PSet o₂}, s.Equiv t → (F s).Subset (F t))
    {x} (a : PSet x) : lift (fun _ h => mk (F h)) ⟪a⟫ = ⟪F a⟫ :=
  lift_mk _ (fun h => mk_eq_mk.r ⟪H h, H h.symm⟫) _

theorem ZFSet.lift₂_mk {β : Sort v} (F : ∀ {{x}}, PSet x → ∀ {{y}}, PSet y → β)
    (H : ∀ {oa₁ oa₂ ob₁ ob₂ a₁ a₂ b₁ b₂},
      a₁.Equiv a₂ → b₁.Equiv b₂ → @F oa₁ a₁ ob₁ b₁ = @F oa₂ a₂ ob₂ b₂)
    {x} (a : PSet x) {y} (b : PSet y) : (mk a).lift (fun _ a => (mk b).lift (F a)) = F a b := by
  have {oa a ob b} : lift (F a) (mk b) = @F oa a ob b := lift_mk _ (H .rfl) _
  rw [lift_mk _ fun h => ?_, this]
  rw [this, this]; exact H h .rfl

@[elab_as_elim]
theorem ZFSet.casesOn {C : ZFSet → Prop}
    (H : ∀ {{a}} b, C (.mk (x := a) b)) (x : ZFSet) : C x :=
  Quot.ind (Sigma.casesOn H) x

def ZFSet.mem (a b : ZFSet.{u}) : Prop :=
  ∃ x s, a = .mk (x := x) s ∧ ∃ y t, b = .mk (x := y) t ∧
  ∃ u hu s', t (.mk u hu s') ∧ s.Equiv s'

local notation:50 a:50 " ∈ " b:50 => ZFSet.mem a b

theorem ZFSet.mk_mem {x s y t} :
    mk (x := x) s ∈ mk (x := y) t ↔ ∃ u hu s', t (.mk u hu s') ∧ s.Equiv s' := by
  refine ⟪fun H => ?_, fun H => ?_⟫
  · ex_cases H with x' s' eq1 y' t' eq2 u hu s₂ tu H
    have ss := mk_eq_mk.l eq1
    refine (mk_eq_mk.l eq2).r _ tu _ <| PElem.casesOn fun z hz w hw => ?_
    have := Equiv₂.mk_iff.l hw.r
    refine ⟪_, _, _, hw.l, ss.trans <| H.trans this.symm⟫
  · exact ⟪_, _, rfl, _, _, rfl, H⟫

theorem ZFSet.ext (a b : ZFSet.{u}) : (∀ z, z ∈ a ↔ z ∈ b) → a = b := by
  refine ZFSet.casesOn (ZFSet.casesOn (fun y g x f h => ?_) b) a
  replace h {u} (c : PSet u) := mk_mem.symm.trans <| (h (mk c)).trans mk_mem
  refine mk_eq_mk.r ⟪?_, ?_⟫ <;>
    refine PElem.casesOn fun c hc s fs => ?_ <;>
    [have := (h s).l; have := (h s).r] <;>
  · specialize this ⟪_, _, _, fs, .rfl⟫
    ex_cases this with u hu s' fs' ss
    exact ⟪_, fs', Equiv₂.mk_iff.r ss⟫

def ZFSet.Subset (a b : ZFSet.{u}) := ∀ z, z ∈ a → z ∈ b
local notation:50 a:50 " ⊆ " b:50 => ZFSet.Subset a b

theorem ZFSet.mk_subset {x} {s : PSet x} {y} {t : PSet y} : mk s ⊆ mk t ↔ s.Subset t := by
  refine ⟪fun H => PElem.casesOn fun _ _ a sa => ?_, fun H => ZFSet.casesOn fun _ a h => ?_⟫
  · have := mk_mem.r ⟪_, _, _, sa, .rfl⟫
    ex_cases mk_mem.l (H _ this) with _ _ b tb eq
    exact ⟪_, tb, Equiv₂.mk_iff.r eq⟫
  · ex_cases mk_mem.l h with _ _ b sb ab
    ex_cases H _ sb with c tc bc
    refine PElem.casesOn (fun _ _ c tc bc => ?_) c tc bc
    exact mk_mem.r ⟪_, _, _, tc, ab.trans (Equiv₂.mk_iff.l bc)⟫

def ZFSet.powerset (a : ZFSet.{u}) : ZFSet.{u} :=
  a.lift fun _ s => mk s.powerset

theorem ZFSet.mem_powerset {a b : ZFSet.{u}} : a ∈ b.powerset ↔ a ⊆ b := by
  refine b.casesOn fun ob b => a.casesOn fun oa a => ?_
  rw [powerset, lift_mk_set (H := powerset.resp₁)]
  refine mk_mem.trans <| .trans ⟪fun H => ?_, fun H => ?_⟫ mk_subset.symm
  · ex_cases H with oc _ c bc ac
    exact .trans ac.l (powerset_mk .. ▸ bc)
  · ex_cases H.exists_equiv with c ca
    exact ⟪_, ob.lt_succ_self, c, powerset_mk .. ▸ .trans ca.l H, ca.symm⟫

def ZFSet.sep (a : ZFSet.{u}) (p : ZFSet → Prop) : ZFSet.{u} :=
  a.lift fun o s => mk (x := o) <| s.sep fun _ a => p (mk a)

theorem ZFSet.mem_sep {a b : ZFSet.{u}} {p} : a ∈ b.sep p ↔ a ∈ b ∧ p a := by
  refine a.casesOn fun oa a => b.casesOn fun ob b => ?_
  rw [sep, lift_mk_set]
  · refine mk_mem.trans ⟪fun H => ?_, fun H => ?_⟫
    · ex_cases H with oc hc c bc ac
      rw [sep_mk] at bc
      exact ⟪mk_mem.r ⟪oc, hc, c, bc.l, ac⟫, mk_eq_mk.r ac ▸ bc.r⟫
    · ex_cases mk_mem.l H.l with oc hc c bc ac
      exact ⟪oc, hc, c, sep_mk .. ▸ ⟪⟪bc, mk_eq_mk.r ac ▸ H.r⟫, ac⟫⟫
  · exact fun H => sep.resp₁ H fun _ _ h => mk_eq_mk.r h ▸ id

def ZFSet.union (a b : ZFSet.{u}) : ZFSet.{u} :=
  a.lift fun oa a => b.lift fun ob b => mk (x := oa.max ob) <|
    fun x => a.embed (oa.le_max_left ob) x ∨ b.embed (oa.le_max_right ob) x

theorem ZFSet.mem_union {x a b : ZFSet.{u}} : x ∈ a.union b ↔ x ∈ a ∨ x ∈ b := by
  refine a.casesOn fun oa a => b.casesOn fun ob b => x.casesOn fun ox x => ?_
  rw [union, lift₂_mk]
  · refine mk_mem.trans ⟪fun H => ?_, fun H => ?_⟫
    · ex_cases H with oc hc c H xc
      refine H _ (fun ac => ?_) (fun bc => ?_)
      · ex_cases Equiv.embed.sub_l _ ac with d ad cd
        refine d.casesOn (fun _ _ d ad cd => ?_) ad cd
        exact .inl <| mk_mem.r ⟪_, _, _, ad, xc.trans (Equiv₂.mk_iff.l cd)⟫
      · ex_cases Equiv.embed.sub_l _ bc with d ad cd
        refine d.casesOn (fun _ _ d bd cd => ?_) ad cd
        exact .inr <| mk_mem.r ⟪_, _, _, bd, xc.trans (Equiv₂.mk_iff.l cd)⟫
    · refine H _ (fun ac => ?_) (fun bc => ?_)
      · ex_cases mk_mem.l ac with oc hc c ac xc
        ex_cases (Equiv.embed (h := oa.le_max_left ob)).sub_r _ ac with d ad cd
        refine d.casesOn (fun _ _ d ad cd => ?_) ad cd
        exact ⟪_, _, _, .inl ad, xc.trans (Equiv₂.mk_iff.l cd)⟫
      · ex_cases mk_mem.l bc with oc hc c bc xc
        ex_cases (Equiv.embed (h := oa.le_max_right ob)).sub_r _ bc with d bd cd
        refine d.casesOn (fun _ _ d bd cd => ?_) bd cd
        exact ⟪_, _, _, .inr bd, xc.trans (Equiv₂.mk_iff.l cd)⟫
  · refine fun {oa₁ oa₂ ob₁ ob₂ a₁ a₂ b₁ b₂} Ha Hb => mk_eq_mk.r ?_
    replace Ha := (Equiv.embed (h := oa₁.le_max_left ob₁)).trans <|
      Ha.trans (Equiv.embed (h := oa₂.le_max_left ob₂)).symm
    replace Hb := (Equiv.embed (h := oa₁.le_max_right ob₁)).trans <|
      Hb.trans (Equiv.embed (h := oa₂.le_max_right ob₂)).symm
    refine ⟪?_, ?_⟫
    · refine fun c hc => hc _ (fun hc => ?_) (fun hc => ?_)
      · ex_cases Ha.sub_l _ hc with d ad cd; exact ⟪_, .inl ad, cd⟫
      · ex_cases Hb.sub_l _ hc with d bd cd; exact ⟪_, .inr bd, cd⟫
    · refine fun c hc => hc _ (fun hc => ?_) (fun hc => ?_)
      · ex_cases Ha.sub_r _ hc with d ad cd; exact ⟪_, .inl ad, cd⟫
      · ex_cases Hb.sub_r _ hc with d bd cd; exact ⟪_, .inr bd, cd⟫

def ZFSet.pair (a b : ZFSet.{u}) : ZFSet.{u} :=
  (a.union b).powerset.sep fun x => x = a ∨ x = b

theorem ZFSet.mem_pair {x a b : ZFSet.{u}} : x ∈ a.pair b ↔ x = a ∨ x = b := by
  refine mem_sep.trans ⟪(·.r), fun H => ⟪H _ ?_ ?_, H⟫⟫ <;> rintro rfl <;>
    refine mem_powerset.r fun y h => mem_union.r ?_ <;>
    [exact .inl h; exact .inr h]

def ZFSet.sUnion (a : ZFSet.{u}) : ZFSet.{u} :=
  a.lift fun oa a => mk (x := oa) fun x => ∃ y hy t, a (.mk y hy t) ∧ t.embed (.inl hy) x

theorem ZFSet.mem_sUnion {x a : ZFSet.{u}} : x ∈ a.sUnion ↔ ∃ y, x ∈ y ∧ y ∈ a := by
  refine a.casesOn fun oa a => x.casesOn fun ox x => ?_
  rw [sUnion, lift_mk_set]
  · refine mk_mem.trans ⟪fun H => ?_, fun H => ?_⟫
    · ex_cases H with oc hc c H xc
      ex_cases H with od hd d ad dc
      refine ⟪_, mk_mem.r ⟪_, _, _, dc, xc⟫, ?_⟫
      exact mk_mem.r ⟪_, _, _, ad, Equiv.embed⟫
    · ex_cases H with y xy ya
      refine y.casesOn (fun _ y xy ya => ?_) xy ya
      ex_cases mk_mem.l xy with oc hc c yc xc
      ex_cases mk_mem.l ya with od hd d ad yd
      ex_cases (yd.trans (Equiv.embed (h := .inl hd)).symm).sub_l _ yc with e de ce
      refine e.casesOn (fun oe he e de ce => ?_) de ce
      have xe := xc.trans (Equiv₂.mk_iff.l ce)
      exact ⟪_, _, _, ⟪_, _, _, ad, de⟫, xe⟫
  · refine fun {oa ob a b} H c hc => ?_
    ex_cases hc with od hd d ad dc
    ex_cases H.sub_l _ ad with e be de
    refine e.casesOn (fun oe he e be de => ?_) be de
    have := Equiv₂.mk_iff.l de
    have := (Equiv.embed (h := .inl hd)).trans <| this.trans (Equiv.embed (h := .inl he)).symm
    ex_cases this.sub_l _ dc with f ef cf
    exact ⟪_, ⟪_, _, _, be, ef⟫, cf⟫

def ZFSet.image (f : ZFSet → ZFSet) (a : ZFSet.{u}) : ZFSet.{u} := by
  refine a.lift fun oa a =>
    .mk (x := Ordinal.supr fun i : PElem oa => (f ⟪i.out.snd⟫).out.fst) <|
    fun x => ∃ ob hb b, a (.mk ob hb b) ∧ f ⟪b⟫ = ⟪x.out.snd⟫

section
variable (α : Type*) (ε : α → α → Prop)

set_option hygiene false
set_option quotPrecheck false
local notation:50 (priority := high) a:50 " ∈ " b:50 => ε a b

abbrev subset (a b : α) := ∀ z, z ∈ a → z ∈ b
local notation:50 (priority := high) a:50 " ⊆ " b:50 => subset α ε a b

def ZFC_Model (α : Type*) (ε : α → α → Prop) : Prop :=
  (∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y)                     ∧ -- extensionality
  (∀ x, (∃ a, a ∈ x) → (∃ y, y ∈ x ∧ ¬ ∃ z, z ∈ y ∧ z ∈ x)) ∧ -- regularity
  (∀ p : α → Prop, ∀ z, ∃ y, ∀ x, x ∈ y ↔ x ∈ z ∧ p x)      ∧ -- separation
  (∀ x y, ∃ z, x ∈ z ∧ y ∈ z)                               ∧ -- pairing
  (∀ 𝓕, ∃ A, ∀ x S, x ∈ S ∧ S ∈ 𝓕 → x ∈ A)                  ∧ -- union
  (∀ p : α → Prop, ∀ A, ∃ B, ∀ x, x ∈ A →
    (∃ y, p y) → (∃ y, y ∈ B ∧ p y))                        ∧ -- collection / replacement
  (∃ I, (∃ e, e ∈ I ∧ ∀ y, ¬y ∈ e) ∧
    ∀ x, x ∈ I → ∃ y, y ∈ I ∧ ∀ a, a ∈ y ↔ a ∈ x ∨ a = x)   ∧ -- infinity
  (∀ x, ∃ y, ∀ z, z ⊆ x → z ∈ y)                            ∧ -- powerset
  (∀ X,
    (∀ e, (∀ y, ¬y ∈ e) → ¬e ∈ X) ∧
    (∀ a b, a ∈ X ∧ b ∈ X → (∃ c, c ∈ a ∧ c ∈ b) → a = b) ∧
    ∃ C, ∀ e, e ∈ X → ∃ a, ∀ b, b ∈ e ∧ b ∈ C ↔ a = b)        -- choice
end

theorem ZFC_has_model : ZFC_Model ZFSet ZFSet.mem := by
  refine ⟪?ext, ?reg, ?sep, ?pair, ?union, ?coll, ?infty, ?power, ?choice⟫
  case ext => exact ZFSet.ext
  case reg =>
    sorry
  case sep => exact fun p z => ⟪z.sep p, (·.mem_sep)⟫
  case pair =>
    exact fun x y => ⟪x.pair y, ZFSet.mem_pair.r (.inl rfl), ZFSet.mem_pair.r (.inr rfl)⟫
  case union => exact fun 𝓕 => ⟪𝓕.sUnion, fun a b h => a.mem_sUnion.r ⟪_, h⟫⟫
  case coll =>
    sorry
  case infty =>
    sorry
  case power => exact fun x => ⟪x.powerset, fun _ => ZFSet.mem_powerset.r⟫
  case choice =>
    sorry

end NoInductives

namespace CollectInductives
open Lean Elab Command

structure State where
  visited : NameSet := {}
  inductives : Array Name := #[]

private partial def collect (c : Name) : ReaderT Environment (StateM State) Unit := do
  let s ← get
  if s.visited.contains c then return
  modify fun s => { s with visited := s.visited.insert c }
  let env ← read
  let some ci := env.checked.get.find? c | return
  collectExpr ci.type
  if let some v := ci.value? then collectExpr v
  if ci matches .inductInfo _ || ci.name == ``Quot then
    modify fun s => { s with inductives := s.inductives.push c }
where
  collectExpr (e : Expr) := e.getUsedConstants.forM collect

elab tk:"#print" &"inductives" id:ident* : command => do
  let cs ← liftCoreM <| id.mapM realizeGlobalConstNoOverloadWithInfo
  let env ← getEnv
  let (_, {inductives, ..}) := ((cs.forM collect).run env).run {}
  let inductives := inductives.qsort Name.lt |>.toList
  if inductives ⊆ NoInductives.allowInductives then
    logInfoAt tk m!"{cs} depends on inductives: {inductives}"
  else
    logErrorAt tk m!"{cs} depends on inductives: {inductives}"

end CollectInductives

namespace NoInductives
#print axioms ZFC_has_model
#print inductives ZFC_has_model
end NoInductives

end Counterexample
