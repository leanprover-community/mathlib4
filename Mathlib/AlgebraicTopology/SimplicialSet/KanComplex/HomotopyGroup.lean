/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.PtSimplexEquiv

/-!
# Homotopy groups of Kan complexes

In this file, we define the homotopy groups `SSet.KanComplex.π n X x`
of a Kan complex `X` where `n : ℕ` and `x : X _⦋n⦌`. For `n = 0`,
this is only a type with a `One` element. In the case of
`SSet.KanComplex.π (n + 1) X x`, we actually get a group structure
for each `i : Fin (n + 1)` (but they should all coindice), and
we use `i := Fin.last n` in order to define the group structure instance.
The multiplication is characterized in terms of `SSet.PtSimplex.MulStruct`
structured, see the lemma `SSet.KanComplex.π.mul_mk_eq_iff`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet.KanComplex

/-- The `n`th homotopy group of a Kan complex `X` relative to a
base point `x : X _⦋0⦌`. It is defined as the homotopy classes
of morphisms `Δ[n] ⟶ X` which are constant with value `x` on `∂Δ[n]`.
(This is a group when `n ≥ 1`.) -/
def π (n : ℕ) (X : SSet.{u}) (x : X _⦋0⦌) : Type u :=
  RelativeMorphism.HomotopyClass ∂Δ[n] (Subcomplex.ofSimplex x)
    (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)

namespace π

variable {n : ℕ} {X : SSet.{u}} {x : X _⦋0⦌}

/-- The surjective map `X.PtSimplex n x → π n X x`. -/
def mk (f : X.PtSimplex n x) : π n X x := f.homotopyClass

lemma mk_surjective : Function.Surjective (π.mk : _ → π n X x) :=
  Quot.mk_surjective

@[elab_as_elim, cases_eliminator, induction_eliminator]
lemma rec {motive : π n X x → Prop}
    (mk : ∀ (f : X.PtSimplex n x), motive (mk f)) (y : π n X x) : motive y := by
  obtain ⟨f, rfl⟩ := y.mk_surjective
  exact mk f

instance : One (π n X x) where
  one := RelativeMorphism.const.homotopyClass

variable [KanComplex X]

lemma mk_eq_mk_iff {p q : X.PtSimplex n x} :
    mk p = mk q ↔ Nonempty (p.RelStruct₀ q) := by
  refine Quot.eq.trans ⟨fun r ↦ ?_, fun ⟨h⟩ ↦ Relation.EqvGen.rel _ _ ⟨h.homotopy⟩⟩
  induction r with
  | rel p q h => exact ⟨PtSimplex.Homotopy.relStruct₀ h.some⟩
  | refl p => exact ⟨.refl _⟩
  | symm _ _ _ h => exact ⟨h.some.symm⟩
  | trans _ _ _ _ _ h₁ h₂ => exact ⟨h₁.some.trans h₂.some⟩

lemma mk_eq_one_iff (p : X.PtSimplex n x) :
    mk p = 1 ↔ Nonempty (p.RelStruct₀ .const) :=
  mk_eq_mk_iff

namespace group

/-- Auxiliary definition for `group.mul`. -/
private noncomputable def mul' (p q : X.PtSimplex (n + 1) x) (i : Fin (n + 1)) :
    X.PtSimplex (n + 1) x :=
  (PtSimplex.MulStruct.nonempty p q i).choose

private noncomputable def mulStruct (p q : X.PtSimplex (n + 1) x) (i : Fin (n + 1)) :
    PtSimplex.MulStruct p q (mul' p q i) i :=
  (PtSimplex.MulStruct.nonempty p q i).choose_spec.some

/-- The multiplication on `π (n + 1) X x`,
which depends a priori on a parameter `i : Fin (n + 1)`. -/
private noncomputable def mul (i : Fin (n + 1)) (g₁ g₂ : π (n + 1) X x) : π (n + 1) X x := by
  refine Quot.lift₂ (fun p q ↦ mk (mul' p q i)) ?_ ?_ g₁ g₂
  · rintro p q q' ⟨h : q.Homotopy q'⟩
    rw [mk_eq_mk_iff]
    exact ⟨PtSimplex.MulStruct.unique (mulStruct p q i) (mulStruct p q' i)
      (.refl p) h.relStruct₀⟩
  · rintro p p' q ⟨h : p.Homotopy p'⟩
    rw [mk_eq_mk_iff]
    exact ⟨PtSimplex.MulStruct.unique (mulStruct p q i) (mulStruct p' q i)
      h.relStruct₀ (.refl q)⟩

private lemma mul_eq_of_mulStruct {g₁ g₂ g₁₂ : X.PtSimplex (n + 1) x} {i : Fin (n + 1)}
    (h : PtSimplex.MulStruct g₁ g₂ g₁₂ i) : mul i (mk g₁) (mk g₂) = mk g₁₂ := by
  change mk _ = mk _
  rw [mk_eq_mk_iff]
  exact ⟨PtSimplex.MulStruct.unique (mulStruct g₁ g₂ i) h (.refl g₁) (.refl g₂)⟩

private lemma mul_mk_eq_iff {g₁ g₂ g₁₂ : X.PtSimplex (n + 1) x} {i : Fin (n + 1)} :
    mul i (mk g₁) (mk g₂) = mk g₁₂ ↔
      Nonempty (PtSimplex.MulStruct g₁ g₂ g₁₂ i) := by
  constructor
  · intro h
    change mk _ = mk _ at h
    rw [mk_eq_mk_iff] at h
    exact ⟨PtSimplex.MulStruct.unique' (mulStruct g₁ g₂ i) h.some⟩
  · rintro ⟨h⟩
    exact mul_eq_of_mulStruct h

private lemma mul_assoc (i : Fin (n + 1)) (g₁ g₂ g₃ : π (n + 1) X x) :
    mul i (mul i g₁ g₂) g₃ = mul i g₁ (mul i g₂ g₃) := by
  induction g₁ with | mk p₁
  induction g₂ with | mk p₂
  induction g₃ with | mk p₃
  exact mul_eq_of_mulStruct
    (PtSimplex.MulStruct.assoc (mulStruct p₁ p₂ i) (mulStruct p₂ p₃ i)
      (mulStruct p₁ (mul' p₂ p₃ i) i))

@[simp]
private lemma one_mul (i : Fin (n + 1)) (g : π (n + 1) X x) :
    mul i 1 g = g := by
  obtain ⟨p, rfl⟩ := g.mk_surjective
  exact mul_eq_of_mulStruct (PtSimplex.MulStruct.oneMul p i)

@[simp]
private lemma mul_one (i : Fin (n + 1)) (g : π (n + 1) X x) :
    mul i g 1 = g := by
  obtain ⟨p, rfl⟩ := g.mk_surjective
  exact mul_eq_of_mulStruct (PtSimplex.MulStruct.mulOne p i)

private lemma exists_left_inverse (i : Fin (n + 1)) (f : π (n + 1) X x) :
    ∃ g, mul i g f = 1 := by
  induction f with | mk p
  obtain ⟨q, ⟨h⟩⟩ := PtSimplex.MulStruct.exists_left_inverse p i
  exact ⟨_, mul_eq_of_mulStruct h⟩

private noncomputable def inv (i : Fin (n + 1)) (f : π (n + 1) X x) : π (n + 1) X x :=
  (exists_left_inverse i f).choose

@[simp]
private lemma inv_mul (i : Fin (n + 1)) (f : π (n + 1) X x) :
    mul i (inv i f) f = 1 := (exists_left_inverse i f).choose_spec

end group

variable (x) in
set_option warn.classDefReducibility false in
/-- If `x : X _⦋0⦌`, this is a group structure on `π (n + 1) X x` which depends
on a parameter `i : Fin (n + 1)`. (Note: they should all agree. The group
instance on `π (n + 1) X x` is defined using `i := Fin.last n`.) -/
@[no_expose]
noncomputable def group' (i : Fin (n + 1)) : Group (π (n + 1) X x) where
  mul := group.mul i
  mul_assoc := group.mul_assoc i
  one_mul := group.one_mul i
  mul_one := group.mul_one i
  inv := group.inv i
  inv_mul_cancel _ := group.inv_mul _ _

lemma mul_eq_of_mulStruct'
    {g₁ g₂ g₁₂ : X.PtSimplex (n + 1) x} {i : Fin (n + 1)}
    (h : PtSimplex.MulStruct g₁ g₂ g₁₂ i) :
    letI := group' x i
    π.mk g₁ * π.mk g₂ = π.mk g₁₂ :=
  group.mul_eq_of_mulStruct h

lemma mul_mk_eq_iff' {g₁ g₂ g₁₂ : X.PtSimplex (n + 1) x} {i : Fin (n + 1)} :
    letI := group' x i
    mk g₁ * mk g₂ = mk g₁₂ ↔
      Nonempty (PtSimplex.MulStruct g₁ g₂ g₁₂ i) :=
  ⟨fun h ↦ ⟨PtSimplex.MulStruct.unique' (group.mulStruct g₁ g₂ i) (mk_eq_mk_iff.1 h).some⟩,
    fun ⟨h⟩ ↦ mul_eq_of_mulStruct' h⟩

noncomputable instance group : Group (π (n + 1) X x) := group' x (Fin.last n)

lemma mul_mk_eq_iff {g₁ g₂ g₁₂ : X.PtSimplex (n + 1) x} :
    mk g₁ * mk g₂ = mk g₁₂ ↔
      Nonempty (PtSimplex.MulStruct g₁ g₂ g₁₂ (Fin.last _)) :=
  mul_mk_eq_iff' ..

end π

end KanComplex

open KanComplex in
lemma PtSimplex.MulStruct.mul_eq {X : SSet.{u}} [KanComplex X] {n : ℕ} {x : X _⦋0⦌}
    {g₁ g₂ g₁₂ : X.PtSimplex (n + 1) x}
    (h : PtSimplex.MulStruct g₁ g₂ g₁₂ (Fin.last _)) :
    π.mk g₁ * π.mk g₂ = π.mk g₁₂ :=
  KanComplex.π.mul_eq_of_mulStruct' h

end SSet
