import Mathlib.Tactic.Gavrilovich
import Mathlib.Topology.Gavrilovich.Sierpinski

universe u

open CategoryTheory Limits CartesianMonoidalCategory TopCat TopologicalSpace
open Gavrilovich Sierpinski

variable {X Y : TopCat.{u}} (f g k : X ⟶ ⌜T → F⌟.{u}) (h : Y ⟶ X) (x : X)

/-! Points: connectives reduce to atoms `a = pt(T)`, `a = pt(F)`; enumerate with `pt_cases`. -/

example (a b : ⌜T → F⌟.{u}) : (a ⊔ bᶜ) ⊓ b = pt(T) ↔ a = pt(T) ∧ b = pt(T) := by
  pt_cases a <;> pt_cases b <;> simp +decide
example (a b : ⌜T → F⌟.{u}) : (a ⊔ bᶜ) ⊓ b = pt(F) ↔ (a = pt(F) ∧ b = pt(T)) ∨ b = pt(F) := by
  simp
example (a : ⌜T → F⌟.{u}) : a ≠ pt(T) ↔ a = pt(F) := ne_T_iff

/-! Values of morphisms: everything reduces to atoms `f x = pt(T)`. -/

example : ((f ⊔ k) ⊓ g) x = pt(F) ↔ (f x = pt(T) → ¬g x = pt(T)) ∧ (k x = pt(T) → ¬g x = pt(T)) := by
  simp; tauto
-- `ᶜ` on morphisms is not pointwise (it is the interior), so it is not unfolded
example : fᶜ x = pt(T) ↔ x ∈ interior {x | ¬f x = pt(T)} := compl_apply_eq_T

/-! Pointwise reading of the lattice operations. -/

example : (f ⊔ g ⊓ k) x = pt(T) ↔ f x = pt(T) ∨ g x = pt(T) ∧ k x = pt(T) := by simp
example (s : ℕ → (X ⟶ ⌜T → F⌟.{u})) :
    (⨆ i, s i ⊓ f) x = pt(T) ↔ ∃ i, s i x = pt(T) ∧ f x = pt(T) := by
  simp
example : f ≤ g ↔ ∀ x, f x = pt(T) → g x = pt(T) := le_def
example : f = ⊤ ↔ ∀ x, f x = pt(T) := eq_top_iff_apply
example : f = ⊥ ↔ ∀ x, ¬f x = pt(T) := eq_bot_iff_apply
example : (f ⊔ g ⊓ k) x = pt(F) ↔ ¬f x = pt(T) ∧ (g x = pt(T) → ¬k x = pt(T)) := by
  simp; tauto

/-! Frame algebra. -/

example : f ⊓ (g ⊔ k) = f ⊓ g ⊔ f ⊓ k := inf_sup_left ..
example (hfg : Disjoint f g) : Disjoint (h ≫ f) (h ≫ g) := by
  rw [disjoint_iff] at hfg ⊢; rw [← comp_inf, hfg, comp_bot]
example (s : ℕ → (X ⟶ ⌜T → F⌟.{u})) : h ≫ (⨆ i, s i ⊓ f) = ⨆ i, h ≫ s i ⊓ h ≫ f := by simp

/-! The `O2C1` equalizer condition and the `O1C2` pullback condition are lattice equations. -/

example : lift f g ≫ Sierpinski.andHom =
    isTerminalTensorUnit.from X ≫ ConcreteCategory.homOfElement pt(F) ↔ Disjoint f g := by
  rw [lift_comp_andHom, from_comp_homOfElement_F, disjoint_iff]
example : lift f g ≫ Sierpinski.orHom =
    isTerminalTensorUnit.from X ≫ ConcreteCategory.homOfElement pt(T) ↔ Codisjoint f g := by
  rw [lift_comp_orHom, from_comp_homOfElement_T, codisjoint_iff]
example : Disjoint f g ↔ ∀ x, ¬(f x = pt(T) ∧ g x = pt(T)) := disjoint_iff_apply
example : Codisjoint f g ↔ ∀ x, f x = pt(T) ∨ g x = pt(T) := codisjoint_iff_apply

/-! Open and closed sets. -/

example (U V : Opens X) : (U ⊔ V).indicatorHom = U.indicatorHom ⊔ V.indicatorHom :=
  indicatorHom_sup U V
example : asOpen (f ⊔ g) = asOpen f ⊔ asOpen g := asOpen_sup
example (U : Opens X) : Opens.functor.homFromElement U = U.indicatorHom := by simp
example (U : Opens X) : h ≫ U.indicatorHom = (Opens.comap h.hom U).indicatorHom := by ext; simp
example (C D : Closeds X) : Codisjoint C.indicatorHom D.indicatorHom ↔ Disjoint (C : Set X) D := by
  simp
-- `T25Space`'s `O1C2` leg: disjoint closures give a map to `O1C2`
example {u v : Set X} (huv : Disjoint (closure u) (closure v)) :
    Codisjoint (isClosed_closure (s := u)).indicatorHom (isClosed_closure (s := v)).indicatorHom :=
  codisjoint_closeds_indicatorHom.mpr huv

/-! Separation axioms via morphisms. -/

example : T2Space X ↔ ∀ x y : X, x ≠ y →
    ∃ f g : X ⟶ ⌜T → F⌟.{u}, f x = pt(T) ∧ g y = pt(T) ∧ Disjoint f g := by
  simp [t2Space_iff, Pairwise, exists_hom, and_comm, and_left_comm, and_assoc]

example : T0Space X ↔ ∀ x y : X, (∀ f : X ⟶ ⌜T → F⌟.{u}, f x = pt(T) ↔ f y = pt(T)) → x = y := by
  simp [t0Space_iff_inseparable, inseparable_iff_forall_isOpen, forall_hom]

/-! The diagram machinery still works on `⌜T → F⌟`. -/

example (a : ⌜T → F⌟.{u}) : a ⊓ aᶜ = pt(F) := by pt_cases a <;> decide
example : ((⌜a → b⌟ ⇢ ⌜a(=T) → b(=F)⌟ : ⌜a → b⌟.{u} ⟶ ⌜T → F⌟) ⊔ ⊥) pt(a) = pt(T) := by
  simp
example : (⌜a → b⌟ ⇢ ⌜a(=T) → b(=F)⌟ : ⌜a → b⌟.{u} ⟶ ⌜T → F⌟) ⊔
    (isTerminalTensorUnit.from _ ≫ ConcreteCategory.homOfElement pt(T)) = ⊤ := by
  simp
