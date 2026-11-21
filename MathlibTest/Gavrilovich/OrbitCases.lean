import Mathlib.Tactic.OrbitCases
import Mathlib.Tactic.Gavrilovich
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.FinEnum
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Algebra.Group.Action.Prod

open Gavrilovich CategoryTheory

set_option linter.unreachableTactic false

/-! Goals are checked with `guard_target`/`guard_hyp` rather than `#guard_msgs`: the latter does
not reliably capture messages logged after an `evalExpr` (as `orbit_cases` does). -/

abbrev Z2 := Multiplicative (ZMod 2)
instance : Fintype Z2 := inferInstanceAs (Fintype (Fin 2))
instance : DecidableEq Z2 := inferInstanceAs (DecidableEq (Fin 2))

def swapAB : ⌜a  b⌟ ⟶ ⌜a  b⌟ := relabel[a ↦ b, b ↦ a]

instance : MulAction Z2 (⌜a  b⌟ ⟶ ⌜x  y⌟) where
  smul g f := if g = 1 then f else swapAB ≫ f
  one_smul := by gav_decide
  mul_smul := by gav_decide

/-! The representatives are the first of each orbit, as `Fintype` lists them; hypotheses depending
on the variable are carried along. -/

example (P : (⌜a  b⌟ ⟶ ⌜x  y⌟) → Prop) (f : ⌜a  b⌟ ⟶ ⌜x  y⌟) (hf : P f) : P f := by
  orbit_cases f using Z2
  case inv =>
    guard_target = ∀ (g : Z2) (x : ⌜a  b⌟ ⟶ ⌜x  y⌟), (P x → P x) → P (g • x) → P (g • x)
    exact fun _ _ _ h ↦ h
  case rep_0 =>
    guard_hyp hf : P (⌜a  b⌟ ⇢ ⌜a=b(=x)  y⌟)
    guard_target = P (⌜a  b⌟ ⇢ ⌜a=b(=x)  y⌟)
    exact hf
  case rep_1 =>
    guard_target = P (⌜a  b⌟ ⇢ ⌜a(=x)  b(=y)⌟)
    exact hf
  case rep_2 =>
    guard_target = P (⌜a  b⌟ ⇢ ⌜a=b(=y)  x⌟)
    exact hf

/-! A complete proof: everything is decidable here. -/

example (f : ⌜a  b⌟ ⟶ ⌜x  y⌟) : swapAB ≫ swapAB ≫ f = f := by
  orbit_cases f using Z2 <;> gav_decide

/-! 81 morphisms, 54 orbits. -/

def swp : ⌜a  b  c  d⌟ ⟶ ⌜a  b  c  d⌟ := relabel[a ↦ b, b ↦ a]

instance : MulAction Z2 (⌜a  b  c  d⌟ ⟶ ⌜x  y  z⌟) where
  smul g f := if g = 1 then f else swp ≫ f
  one_smul := by gav_decide
  mul_smul := by gav_decide

example (P : (⌜a  b  c  d⌟ ⟶ ⌜x  y  z⌟) → Prop) (h : ∀ f, P f)
    (f : ⌜a  b  c  d⌟ ⟶ ⌜x  y  z⌟) : P f := by
  orbit_cases f using Z2
  case rep_53 =>
    guard_target = P (⌜a  b  c  d⌟ ⇢ ⌜a=b=c=d(=z)  x  y⌟)
    exact h _
  fail_if_success case rep_54 => exact h _
  all_goals first | exact fun _ _ _ ↦ h _ | exact h _

/-! `Aut` acting by precomposition, as in `Lifting/Separation.lean`. -/

section Aut
variable {C : Type*} [Category* C] (X Y : C)

instance autMulActionLeft : MulAction (Aut X)ᵐᵒᵖ (X ⟶ Y) where
  smul α₁ φ := α₁.unop.asIso.hom ≫ φ
  mul_smul := by simp [HSMul.hSMul]
  one_smul := by simp [HSMul.hSMul]

instance [DecidableEq (X ⟶ X)] : DecidableEq (Aut X) :=
  fun φ ψ ↦ decidable_of_iff (φ.asIso.hom = ψ.asIso.hom) (by simp [Aut.ext_iff, Iso.ext_iff])

instance [FinEnum (X ⟶ X)] : FinEnum (Aut X) :=
  FinEnum.ofSurjective (β := (X ⟶ X) × _)
    (fun (f, g) ↦ if h : f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 X then Aut.of ⟨f, g, h.1, h.2⟩
      else Aut.of (Iso.refl X))
    (fun φ ↦ ⟨(φ.asIso.hom, φ.asIso.inv), by simp⟩)

instance [FinEnum (X ⟶ X)] : FinEnum (Aut X)ᵐᵒᵖ :=
  FinEnum.ofEquiv _ (MulOpposite.opEquiv).symm

instance autMulActionRight : MulAction (Aut Y) (X ⟶ Y) where
  smul α₂ φ := φ ≫ α₂.asIso.hom
  mul_smul := by simp [HSMul.hSMul]
  one_smul := by simp [HSMul.hSMul]

instance : SMulCommClass (Aut X)ᵐᵒᵖ (Aut Y) (X ⟶ Y) where
  smul_comm _ _ _ := (Category.assoc _ _ _).symm

instance autMulAction : MulAction ((Aut X)ᵐᵒᵖ × Aut Y) (X ⟶ Y) := .prodOfSMulCommClass ..

end Aut

/-! Universe-polymorphic, with `generalizing`. -/

universe u in
example (P : (⌜x  y⌟ ⟶ ⌜o₁ → c ← o₂⌟) → Prop) (Q : Prop) (hQ : Q)
    (ι : (⌜x  y⌟ : TopCat.{u}) ⟶ ⌜o₁ → c ← o₂⌟) (h : P ι) : P ι ∧ Q := by
  orbit_cases ι using (Aut (⌜x  y⌟ : TopCat.{u}))ᵐᵒᵖ generalizing hQ
  case inv =>
    guard_target = ∀ (g : (Aut (⌜x  y⌟ : TopCat.{u}))ᵐᵒᵖ) (x : (⌜x  y⌟ : TopCat.{u}) ⟶ _),
      (Q → P x → P x ∧ Q) → Q → P (g • x) → P (g • x) ∧ Q
    exact fun _ _ _ hQ h ↦ ⟨h, hQ⟩
  case rep_1 =>
    guard_hyp hQ : Q
    guard_hyp h : P (⌜x  y⌟ ⇢ ⌜y(=o₁) → x(=c) ← o₂⌟)
    guard_target = P (⌜x  y⌟ ⇢ ⌜y(=o₁) → x(=c) ← o₂⌟) ∧ Q
    exact ⟨h, hQ⟩
  case rep_5 => exact ⟨h, hQ⟩
  fail_if_success case rep_6 => skip
  all_goals exact ⟨h, hQ⟩

/-! Errors. -/

/--
error: failed to synthesize
  SMul Z2 ℕ

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  orbit_cases 1 + 1 using Z2

/--
error: orbit_cases: the action of
  Z2
on
  β → (⌜a  b⌟ ⟶ ⌜x  y⌟)
must not depend on local hypotheses (other than `let` variables) or metavariables
-/
#guard_msgs in
example {β : Type} [Unique β] (f : β → (⌜a  b⌟ ⟶ ⌜x  y⌟)) : f = f := by
  orbit_cases f using Z2

/-! `h : x` keeps a variable `x` with `h : x = r`; `with` alternatives. -/

example (P : (⌜a  b⌟ ⟶ ⌜x  y⌟) → Prop) (h : ∀ f, P f) (f : ⌜a  b⌟ ⟶ ⌜x  y⌟) (hf : P f) :
    P f := by
  orbit_cases hf' : f using Z2 with
  | inv => exact fun _ _ _ _ ↦ h _
  | rep_1 =>
    guard_hyp hf' : f = (⌜a  b⌟ ⇢ ⌜a(=x)  b(=y)⌟)
    guard_hyp hf : P f
    guard_target = P f
    exact hf
  | _ => exact hf

/-- error: orbit_cases: no goal named `rep_7` -/
#guard_msgs in
example (P : (⌜a  b⌟ ⟶ ⌜x  y⌟) → Prop) (f : ⌜a  b⌟ ⟶ ⌜x  y⌟) : P f := by
  orbit_cases f using Z2 with
  | rep_7 => skip

/-- A term, generalized first. -/
example (P : (⌜a  b⌟ ⟶ ⌜x  y⌟) → Prop) (h : ∀ f, P f) (f : ⌜a  b⌟ ⟶ ⌜x  y⌟) :
    P (swapAB ≫ f) := by
  orbit_cases e : swapAB ≫ f using Z2 with
  | inv => exact fun _ _ _ ↦ h _
  | rep_0 =>
    guard_hyp e : x = (⌜a  b⌟ ⇢ ⌜a=b(=x)  y⌟)
    exact h _
  | _ => exact h _

/-- `generalizing` after generalizing a term. -/
example (P : (⌜a  b⌟ ⟶ ⌜x  y⌟) → Prop) (h : ∀ f, P f) (f : ⌜a  b⌟ ⟶ ⌜x  y⌟) (hf : P f) :
    P (swapAB ≫ f) := by
  orbit_cases swapAB ≫ f using Z2 generalizing hf with
  | inv =>
    guard_target = ∀ (g : Z2) (x : ⌜a  b⌟ ⟶ ⌜x  y⌟), (P f → P x) → P f → P (g • x)
    exact fun _ _ _ _ ↦ h _
  | _ => exact h _

/-! The product of both automorphism groups, as in `Lifting/Separation.lean`. -/

universe u in
example (P : (⌜x  y⌟ ⟶ ⌜o₁ → c ← o₂⌟) → Prop) (h : ∀ f, P f)
    (ι : (⌜x  y⌟ : TopCat.{u}) ⟶ ⌜o₁ → c ← o₂⌟) : P ι := by
  orbit_cases hι : ι using (Aut.{u} ⌜x  y⌟)ᵐᵒᵖ × Aut.{u} ⌜o₁ → c ← o₂⌟
  case rep_0 =>
    guard_hyp hι : ι = (⌜x  y⌟ ⇢ ⌜o₁ → x=y(=c) ← o₂⌟)
    exact h _
  fail_if_success case rep_4 => exact h _
  all_goals first | exact fun _ _ _ ↦ h _ | exact h _

/-! `generated_by`: the orbits of the subgroup generated by the given elements, with `inv` only for
those. The kernel never enumerates `G`. -/

example (P : (⌜a  b⌟ ⟶ ⌜x  y⌟) → Prop) (f : ⌜a  b⌟ ⟶ ⌜x  y⌟) (hf : P f) : P f := by
  orbit_cases f using Z2 generated_by [⟨1, by decide⟩]
  case inv =>
    guard_target = ∀ (g : Z2), g ∈ [⟨1, by decide⟩] → ∀ (x : ⌜a  b⌟ ⟶ ⌜x  y⌟),
      (P x → P x) → P (g • x) → P (g • x)
    exact fun _ _ _ _ h ↦ h
  case rep_0 =>
    guard_target = P (⌜a  b⌟ ⇢ ⌜a=b(=x)  y⌟)
    exact hf
  case rep_1 =>
    guard_target = P (⌜a  b⌟ ⇢ ⌜a(=x)  b(=y)⌟)
    exact hf
  case rep_2 =>
    guard_target = P (⌜a  b⌟ ⇢ ⌜a=b(=y)  x⌟)
    exact hf

/-! No generators: every element is its own representative. -/
example (P : (⌜a  b⌟ ⟶ ⌜x  y⌟) → Prop) (h : ∀ f, P f) (f : ⌜a  b⌟ ⟶ ⌜x  y⌟) : P f := by
  orbit_cases f using Z2 generated_by []
  case inv => simp
  case rep_3 => exact h _
  fail_if_success case rep_4 => exact h _
  all_goals exact h _

/-! The generators that `generated_by?` suggests for the product of both automorphism groups. -/
universe u in
example (P : (⌜x  y⌟ ⟶ ⌜o₁ → c ← o₂⌟) → Prop) (h : ∀ f, P f)
    (ι : (⌜x  y⌟ : TopCat.{u}) ⟶ ⌜o₁ → c ← o₂⌟) : P ι := by
  orbit_cases hι : ι using (Aut.{u} ⌜x  y⌟)ᵐᵒᵖ × Aut.{u} ⌜o₁ → c ← o₂⌟
    generated_by [(MulOpposite.op
      ⟨⟨Space.homOfTable [1, 0] (by decide) (by decide),
        Space.homOfTable [1, 0] (by decide) (by decide), by decide, by decide⟩⟩,
      ⟨⟨Space.homOfTable [0, 2, 1] (by decide) (by decide),
        Space.homOfTable [0, 2, 1] (by decide) (by decide), by decide, by decide⟩⟩),
      (MulOpposite.op
      ⟨⟨Space.homOfTable [1, 0] (by decide) (by decide),
        Space.homOfTable [1, 0] (by decide) (by decide), by decide, by decide⟩⟩,
      ⟨⟨(⌜o₁ → c ← o₂⌟ ⇢ ⌜o₁ → c ← o₂⌟), (⌜o₁ → c ← o₂⌟ ⇢ ⌜o₁ → c ← o₂⌟),
        by decide, by decide⟩⟩)]
  case rep_0 =>
    guard_hyp hι : ι = (⌜x  y⌟ ⇢ ⌜o₁ → x=y(=c) ← o₂⌟)
    exact h _
  fail_if_success case rep_4 => exact h _
  all_goals first | exact fun _ _ _ _ ↦ h _ | exact h _

/-! `generated_by?` leaves the same goals as without it (and suggests the generators above). -/
universe u in
example (P : (⌜x  y⌟ ⟶ ⌜o₁ → c ← o₂⌟) → Prop) (h : ∀ f, P f)
    (ι : (⌜x  y⌟ : TopCat.{u}) ⟶ ⌜o₁ → c ← o₂⌟) : P ι := by
  orbit_cases hι : ι using (Aut.{u} ⌜x  y⌟)ᵐᵒᵖ × Aut.{u} ⌜o₁ → c ← o₂⌟ generated_by?
  case rep_0 =>
    guard_hyp hι : ι = (⌜x  y⌟ ⇢ ⌜o₁ → x=y(=c) ← o₂⌟)
    exact h _
  fail_if_success case rep_4 => exact h _
  all_goals first | exact fun _ _ _ ↦ h _ | exact h _

/--
error: orbit_cases: the action of
  Z2
on
  ⌜a  b⌟ ⟶ ⌜x  y⌟
and the generators [g]
must not depend on local hypotheses (other than `let` variables) or metavariables
-/
#guard_msgs in
example (g : Z2) (f : ⌜a  b⌟ ⟶ ⌜x  y⌟) : f = f := by
  orbit_cases f using Z2 generated_by [g]

/-! `rep t` names a representative by its value. -/

example (P : (⌜a  b⌟ ⟶ ⌜x  y⌟) → Prop) (h : ∀ f, P f) (f : ⌜a  b⌟ ⟶ ⌜x  y⌟) : P f := by
  orbit_cases f using Z2 with
  | inv => exact fun _ _ _ ↦ h _
  | rep ⌜a  b⌟ ⇢ ⌜a(=x)  b(=y)⌟ =>
    guard_target = P (⌜a  b⌟ ⇢ ⌜a(=x)  b(=y)⌟)
    exact h _
  | rep ⌜a  b⌟ ⇢ ⌜x  a=b(=y)⌟ => exact h _
  | _ =>
    guard_target = P (⌜a  b⌟ ⇢ ⌜a=b(=x)  y⌟)
    exact h _

universe u in
example (P : (⌜x  y⌟ ⟶ ⌜o₁ → c ← o₂⌟) → Prop) (h : ∀ f, P f)
    (ι : (⌜x  y⌟ : TopCat.{u}) ⟶ ⌜o₁ → c ← o₂⌟) : P ι := by
  orbit_cases hι : ι using (Aut.{u} ⌜x  y⌟)ᵐᵒᵖ × Aut.{u} ⌜o₁ → c ← o₂⌟
    generated_by [(MulOpposite.op
      ⟨⟨Space.homOfTable [1, 0] (by decide) (by decide),
        Space.homOfTable [1, 0] (by decide) (by decide), by decide, by decide⟩⟩,
      ⟨⟨Space.homOfTable [0, 2, 1] (by decide) (by decide),
        Space.homOfTable [0, 2, 1] (by decide) (by decide), by decide, by decide⟩⟩),
      (MulOpposite.op
      ⟨⟨Space.homOfTable [1, 0] (by decide) (by decide),
        Space.homOfTable [1, 0] (by decide) (by decide), by decide, by decide⟩⟩,
      ⟨⟨(⌜o₁ → c ← o₂⌟ ⇢ ⌜o₁ → c ← o₂⌟), (⌜o₁ → c ← o₂⌟ ⇢ ⌜o₁ → c ← o₂⌟),
        by decide, by decide⟩⟩)] with
  | rep ⌜x  y⌟ ⇢ ⌜o₁ → x=y(=c) ← o₂⌟ =>
    guard_hyp hι : ι = (⌜x  y⌟ ⇢ ⌜o₁ → x=y(=c) ← o₂⌟)
    exact h _
  | inv => exact fun _ _ _ _ ↦ h _
  | _ => exact h _

/-- error: orbit_cases: matches none of the representatives -/
#guard_msgs in
example (P : (⌜a  b⌟ ⟶ ⌜x  y⌟) → Prop) (f : ⌜a  b⌟ ⟶ ⌜x  y⌟) : P f := by
  orbit_cases f using Z2 with
  | rep ⌜a  b⌟ ⇢ ⌜b(=x)  a(=y)⌟ => skip

/-- error: orbit_cases: expected `rep` before a term -/
#guard_msgs in
example (P : (⌜a  b⌟ ⟶ ⌜x  y⌟) → Prop) (f : ⌜a  b⌟ ⟶ ⌜x  y⌟) : P f := by
  orbit_cases f using Z2 with
  | foo ⌜a  b⌟ ⇢ ⌜a(=x)  b(=y)⌟ => skip

/-! An alternative can name several goals. -/

example (P : (⌜a  b⌟ ⟶ ⌜x  y⌟) → Prop) (h : ∀ f, P f) (f : ⌜a  b⌟ ⟶ ⌜x  y⌟) : P f := by
  orbit_cases f using Z2 with
  | inv => exact fun _ _ _ ↦ h _
  | rep_0 | rep ⌜a  b⌟ ⇢ ⌜a(=x)  b(=y)⌟ => exact h _
  | rep_2 =>
    guard_target = P (⌜a  b⌟ ⇢ ⌜a=b(=y)  x⌟)
    exact h _

example (P : (⌜a  b⌟ ⟶ ⌜x  y⌟) → Prop) (h : ∀ f, P f) (f : ⌜a  b⌟ ⟶ ⌜x  y⌟) : P f := by
  orbit_cases f using Z2 with
  | rep ⌜a  b⌟ ⇢ ⌜x  a=b(=y)⌟ | rep_1 | rep_2 => exact h _
  | inv | _ => first | exact fun _ _ _ ↦ h _ | exact h _
