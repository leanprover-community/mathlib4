import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Snoc

/-!
## Bisimulations
We can prove two applications of `mapAccumr` equal by providing a bisimulation relation that relates
the initial states.

That is, by providing a relation `R : σ₁ → σ₁ → Prop` such that `R s₁ s₂` implies that `R` also
relates any pair of states reachable by applying `f₁` to `s₁` and `f₂` to `s₂`, with any possible
input values.
-/

namespace Vector



variable (f₁ : α → σ₁ → σ₁ × β) (f₂ : α → σ₂ → σ₂ × β)

def Bisim  : Type _
  := {R : σ₁ → σ₂ → Prop // ∀ {s q} a, R s q → R (f₁ a s).1 (f₂ a q).1 ∧ (f₁ a s).2 = (f₂ a q).2}

instance : CoeFun (Bisim f₁ f₂) (fun _ => σ₁ → σ₂ → Prop) where
  coe R := R.1

theorem mapAccumr_bisim (xs : Vector α n) (f₁ : α → σ₁ → σ₁ × β) (f₂ : α → σ₂ → σ₂ × β) (s₁ : σ₁)
    (s₂ : σ₂) (R : Bisim f₁ f₂) (h₀ : R s₁ s₂):
    (mapAccumr f₁ xs s₁).2 = (mapAccumr f₂ xs s₂).2 := by
  induction xs using Vector.revInductionOn generalizing s₁ s₂
  . rfl
  next xs x ih =>
    simp
    rcases R with ⟨R, hR⟩
    rcases (hR x h₀) with ⟨hR, _⟩
    congr 1
    apply ih _ _ hR



theorem cons.inj {xs ys : Vector α n} {x y : α} :
    x ::ᵥ xs = y ::ᵥ ys → x = y ∧ xs = ys := by
  rcases xs with ⟨xs, hx⟩
  rcases ys with ⟨ys, hy⟩
  simp[cons]
  intro h
  have h : x :: xs = y :: ys := Subtype.mk.inj h
  constructor
  . apply List.head_eq_of_cons_eq h
  . congr
    apply List.tail_eq_of_cons_eq h


theorem snoc.inj {xs ys : Vector α n} {x y : α} :
    xs.snoc x = ys.snoc y → x = y ∧ xs = ys := by
  intro h
  induction xs, ys using Vector.inductionOn₂
  next =>
    simp_all only [snoc_nil, and_true]
    apply (cons.inj h).1
  next x' y' xs ys ih =>
    simp only [snoc_cons] at h
    rcases cons.inj h with ⟨⟨⟩, heq⟩
    rcases ih heq with ⟨⟨⟩, ⟨⟩⟩
    simp


def Bisim.equal : Bisim f₁ f₂ := ⟨
  fun s₁ s₂ => ∀ {n} (xs : Vector α n), (mapAccumr f₁ xs s₁).snd = (mapAccumr f₂ xs s₂).snd,
  by
    intros s q a hEq
    simp only
    constructor
    . intro n xs
      specialize hEq (xs.snoc a)
      simp only [mapAccumr_snoc] at hEq
      exact (snoc.inj hEq).2
    . specialize hEq (nil.snoc a)
      simp only [mapAccumr_snoc] at hEq
      exact (snoc.inj hEq).1



⟩





end Vector
