/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
module

public import Mathlib.Algebra.AddTorsor.Defs
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar

/-!
# Torsors of additive group actions

Further results for torsors, that are not in `Mathlib/Algebra/AddTorsor/Defs.lean` to avoid
increasing imports there.
-/

@[expose] public section

open scoped Pointwise


section General

variable {G : Type*} {P : Type*} [Group G] [T : Torsor G P]

namespace Set

@[to_additive]
theorem singleton_sdiv_self (p : P) : ({p} : Set P) /ₛ {p} = {(1 : G)} := by
  rw [Set.singleton_sdiv_singleton, sdiv_self]

end Set
/-- If dividing two points by the same point produces equal results, those points are equal. -/
@[to_additive /-- If the same point subtracted from two points produces equal
results, those points are equal. -/]
theorem sdiv_left_cancel {p₁ p₂ p : P} (h : p₁ /ₛ p = p₂ /ₛ p) : p₁ = p₂ := by
  rwa [← div_eq_one, sdiv_div_sdiv_cancel_right, sdiv_eq_one_iff_eq] at h

/-- Dividing two points by the same point produces equal results
if and only if those points are equal. -/
@[to_additive (attr := simp) /-- The same point subtracted from two points produces equal results
if and only if those points are equal. -/]
theorem sdiv_left_cancel_iff {p₁ p₂ p : P} : p₁ /ₛ p = p₂ /ₛ p ↔ p₁ = p₂ :=
  ⟨sdiv_left_cancel, fun h => h ▸ rfl⟩

/-- Dividing by the point `p` is an injective function. -/
@[to_additive /-- Subtracting the point `p` is an injective function. -/]
theorem sdiv_left_injective (p : P) : Function.Injective ((· /ₛ p) : P → G) := fun _ _ =>
  sdiv_left_cancel

/-- If dividing the same point by two points produces equal results, those points are equal. -/
@[to_additive /-- If subtracting two points from the same point produces equal
results, those points are equal. -/]
theorem sdiv_right_cancel {p₁ p₂ p : P} (h : p /ₛ p₁ = p /ₛ p₂) : p₁ = p₂ := by
  refine smul_left_cancel (p /ₛ p₂) ?_
  rw [sdiv_smul, ← h, sdiv_smul]

/-- Subtracting two points from the same point produces equal results
if and only if those points are equal. -/
@[to_additive (attr := simp)]
theorem sdiv_right_cancel_iff {p₁ p₂ p : P} : p /ₛ p₁ = p /ₛ p₂ ↔ p₁ = p₂ :=
  ⟨sdiv_right_cancel, fun h => h ▸ rfl⟩

/-- Dividing the point `p` by other points is an injective function. -/
@[to_additive /-- Subtracting a point from the point `p` is an injective function. -/]
theorem sdiv_right_injective (p : P) : Function.Injective ((p /ₛ ·) : P → G) := fun _ _ =>
  sdiv_right_cancel

end General

section comm

variable {G : Type*} {P : Type*} [CommGroup G] [Torsor G P]

/-- Cancellation dividing the results of two divisions. -/
@[to_additive (attr := simp) /-- Cancellation subtracting the results of two subtractions. -/]
theorem sdiv_div_sdiv_cancel_left (p₁ p₂ p₃ : P) : (p₃ /ₛ p₂) / (p₃ /ₛ p₁) = p₁ /ₛ p₂ := by
  rw [div_eq_mul_inv, inv_sdiv_eq_sdiv_rev, mul_comm, sdiv_mul_sdiv_cancel]

@[to_additive (attr := simp)]
theorem smul_sdiv_smul_cancel_left (v : G) (p₁ p₂ : P) : (v • p₁) /ₛ (v • p₂) = p₁ /ₛ p₂ := by
  rw [sdiv_smul_eq_sdiv_div, smul_sdiv_assoc, mul_div_cancel_left]

@[to_additive]
theorem smul_sdiv_smul_comm (v₁ v₂ : G) (p₁ p₂ : P) :
    (v₁ • p₁) /ₛ (v₂ • p₂) = (v₁ / v₂) * (p₁ /ₛ p₂) := by
  rw [sdiv_smul_eq_sdiv_div, smul_sdiv_assoc, mul_div_assoc, ← mul_comm_div]

@[to_additive]
theorem div_mul_sdiv_comm (v₁ v₂ : G) (p₁ p₂ : P) :
    (v₁ / v₂) * (p₁ /ₛ p₂) = (v₁ • p₁) /ₛ (v₂ • p₂) :=
  smul_sdiv_smul_comm _ _ _ _ |>.symm

@[to_additive]
theorem sdiv_smul_comm (p₁ p₂ p₃ : P) : (p₁ /ₛ p₂ : G) • p₃ = (p₃ /ₛ p₂) • p₁ := by
  rw [← @sdiv_eq_one_iff_eq G, smul_sdiv_assoc, sdiv_smul_eq_sdiv_div]
  simp

@[to_additive]
theorem smul_eq_smul_iff_div_eq_sdiv {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ • p₁ = v₂ • p₂ ↔ v₂ / v₁ = p₁ /ₛ p₂ := by
  rw [smul_eq_smul_iff_inv_mul_eq_sdiv, inv_mul_eq_div]

@[to_additive]
theorem sdiv_div_sdiv_comm (p₁ p₂ p₃ p₄ : P) :
    (p₁ /ₛ p₂) / (p₃ /ₛ p₄) = (p₁ /ₛ p₃) / (p₂ /ₛ p₄) := by
  rw [← sdiv_smul_eq_sdiv_div, sdiv_smul_comm, sdiv_smul_eq_sdiv_div]

namespace Set

@[to_additive (attr := simp)]
lemma smul_set_sdiv_smul_set (v : G) (s t : Set P) : (v • s) /ₛ (v • t) = s /ₛ t := by
  ext; simp [mem_sdiv, mem_smul_set]

end Set

end comm

namespace Prod

variable {G G' P P' : Type*} [Group G] [Group G'] [Torsor G P] [Torsor G' P']

@[to_additive]
instance instTorsor : Torsor (G × G') (P × P') where
  smul v p := (v.1 • p.1, v.2 • p.2)
  one_smul _ := Prod.ext (one_smul _ _) (one_smul _ _)
  mul_smul _ _ _ := Prod.ext (mul_smul _ _ _) (mul_smul _ _ _)
  sdiv p₁ p₂ := (p₁.1 /ₛ p₂.1, p₁.2 /ₛ p₂.2)
  sdiv_smul' _ _ := Prod.ext (sdiv_smul _ _) (sdiv_smul _ _)
  smul_sdiv' _ _ := Prod.ext (smul_sdiv _ _) (smul_sdiv _ _)

@[to_additive (attr := simp)]
theorem fst_smul (v : G × G') (p : P × P') : (v • p).1 = v.1 • p.1 :=
  rfl

@[to_additive (attr := simp)]
theorem snd_smul (v : G × G') (p : P × P') : (v • p).2 = v.2 • p.2 :=
  rfl

@[to_additive (attr := simp)]
theorem mk_smul_mk (v : G) (v' : G') (p : P) (p' : P') : (v, v') • (p, p') = (v • p, v' • p') :=
  rfl

@[to_additive (attr := simp)]
theorem fst_sdiv (p₁ p₂ : P × P') : (p₁ /ₛ p₂ : G × G').1 = p₁.1 /ₛ p₂.1 :=
  rfl

@[to_additive (attr := simp)]
theorem snd_sdiv (p₁ p₂ : P × P') : (p₁ /ₛ p₂ : G × G').2 = p₁.2 /ₛ p₂.2 :=
  rfl

@[to_additive (attr := simp)]
theorem mk_sdiv_mk (p₁ p₂ : P) (p₁' p₂' : P') :
    ((p₁, p₁') /ₛ (p₂, p₂') : G × G') = (p₁ /ₛ p₂, p₁' /ₛ p₂') :=
  rfl

end Prod

namespace Pi

universe u v w

variable {I : Type u} {fg : I → Type v} [∀ i, Group (fg i)] {fp : I → Type w}
  [∀ i, Torsor (fg i) (fp i)]

/-- A product of `Torsor`s is a `Torsor`. -/
@[to_additive /-- A product of `AddTorsor`s is an `AddTorsor`. -/]
instance instTorsor : Torsor (∀ i, fg i) (∀ i, fp i) where
  sdiv p₁ p₂ i := p₁ i /ₛ p₂ i
  sdiv_smul' p₁ p₂ := funext fun i => sdiv_smul (p₁ i) (p₂ i)
  smul_sdiv' g p := funext fun i => smul_sdiv (g i) (p i)

@[to_additive (attr := simp)]
theorem sdiv_apply (p q : ∀ i, fp i) (i : I) : (p /ₛ q) i = p i /ₛ q i :=
  rfl

@[to_additive (attr := push ←)]
theorem sdiv_def (p q : ∀ i, fp i) : p /ₛ q = fun i => p i /ₛ q i :=
  rfl

end Pi

namespace Equiv

variable (G : Type*) (P : Type*) [Group G] [Torsor G P]

@[to_additive (attr := simp)]
theorem constSMul_one : constSMul P (1 : G) = 1 :=
  ext <| one_smul G

variable {G}

@[to_additive (attr := simp)]
theorem constSMul_mul (v₁ v₂ : G) : constSMul P (v₁ * v₂) = constSMul P v₁ * constSMul P v₂ :=
  ext <| mul_smul v₁ v₂

/-- `Equiv.constVAdd` as a homomorphism from `Multiplicative G` to `Equiv.perm P` -/
def constVAddHom (G : Type*) (P : Type*) [AddGroup G] [AddTorsor G P] :
    Multiplicative G →* Equiv.Perm P where
  toFun v := constVAdd P (v.toAdd)
  map_one' := constVAdd_zero G P
  map_mul' v v' := constVAdd_add P v.toAdd v'.toAdd

/-- `Equiv.constSMul` as a homomorphism from `G` to `Equiv.perm P` -/
def constSMulHom : G →* Equiv.Perm P where
  toFun v := constSMul P v
  map_one' := constSMul_one G P
  map_mul' := constSMul_mul P

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

open Function

@[simp]
theorem left_vsub_pointReflection (x y : P) : x -ᵥ pointReflection x y = y -ᵥ x :=
  neg_injective <| by simp

@[simp]
theorem right_vsub_pointReflection (x y : P) : y -ᵥ pointReflection x y = 2 • (y -ᵥ x) :=
  neg_injective <| by simp [← neg_nsmul]

/-- `x` is the only fixed point of `pointReflection x`. This lemma requires
`x + x = y + y ↔ x = y`. There is no typeclass to use here, so we add it as an explicit argument. -/
theorem pointReflection_fixed_iff_of_injective_two_nsmul {x y : P} (h : Injective (2 • · : G → G)) :
    pointReflection x y = y ↔ y = x := by
  rw [pointReflection_apply, eq_comm, eq_vadd_iff_vsub_eq, ← neg_vsub_eq_vsub_rev,
    neg_eq_iff_add_eq_zero, ← two_nsmul, ← nsmul_zero 2, h.eq_iff, vsub_eq_zero_iff_eq, eq_comm]

theorem injective_pointReflection_left_of_injective_two_nsmul {G P : Type*} [AddCommGroup G]
    [AddTorsor G P] (h : Injective (2 • · : G → G)) (y : P) :
    Injective fun x : P => pointReflection x y :=
  fun x₁ x₂ (hy : pointReflection x₁ y = pointReflection x₂ y) => by
  rwa [pointReflection_apply, pointReflection_apply, vadd_eq_vadd_iff_sub_eq_vsub,
    vsub_sub_vsub_cancel_right, ← neg_vsub_eq_vsub_rev, neg_eq_iff_add_eq_zero,
    ← two_nsmul, ← nsmul_zero 2, h.eq_iff, vsub_eq_zero_iff_eq] at hy

/-- In the special case of additive commutative groups (as opposed to just additive torsors),
`Equiv.pointReflection x` coincides with `Equiv.subLeft (2 • x)`. -/
lemma pointReflection_eq_subLeft {G : Type*} [AddCommGroup G] (x : G) :
    pointReflection x = Equiv.subLeft (2 • x) := by
  ext; simp [pointReflection, sub_add_eq_add_sub, two_nsmul]

end Equiv

/-- Pullback of an add torsor along an injective map. -/
abbrev Function.Injective.torsor {G P Q : Type*}
    [Group G] [Torsor G P] [SMul G Q] [SDiv G Q] [Nonempty Q] (f : Q → P)
    (hf : Function.Injective f)
    (smul : ∀ (c : G) (x : Q), f (c • x) = c • f x)
    (sdiv : ∀ (x y : Q), x /ₛ y = f x /ₛ f y) : Torsor G Q where
  __ := hf.mulAction f smul
  sdiv_smul' x y := hf <| by simp only [sdiv, smul, sdiv_smul]
  smul_sdiv' c x := by simp [sdiv, smul]

/-- Pushforward of an add torsor along a surjective map. -/
abbrev Function.Surjective.addTorsor {G P Q : Type*}
    [Group G] [Torsor G P] [SMul G Q] [SDiv G Q]
    (f : P → Q) (hf : Surjective f)
    (smul : ∀ (c : G) (x : P), f (c • x) = c • f x)
    (sdiv : ∀ (x y : P), x /ₛ y = f x /ₛ f y) : Torsor G Q where
  __ := hf.mulAction f smul
  nonempty := Torsor.nonempty.map f
  sdiv_smul' := by simp [hf.forall, ← smul, ← sdiv]
  smul_sdiv' := by simp [hf.forall, ← smul, ← sdiv]
