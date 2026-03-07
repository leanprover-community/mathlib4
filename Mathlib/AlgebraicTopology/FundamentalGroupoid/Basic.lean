/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
module

public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Data.Set.Subsingleton

/-!
# Fundamental groupoid of a space

Given a topological space `X`, we can define the fundamental groupoid of `X` to be the category with
objects being points of `X`, and morphisms `x ⟶ y` being paths from `x` to `y`, quotiented by
homotopy equivalence. With this, the fundamental group of `X` based at `x` is just the automorphism
group of `x`.
-/

@[expose] public section

open CategoryTheory

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ x₁ : X}

noncomputable section

open unitInterval

namespace Path

namespace Homotopy

section

/-- Auxiliary function for `reflTransSymm`. -/
def reflTransSymmAux (x : I × I) : ℝ :=
  if (x.2 : ℝ) ≤ 1 / 2 then x.1 * 2 * x.2 else x.1 * (2 - 2 * x.2)

@[continuity, fun_prop]
theorem continuous_reflTransSymmAux : Continuous reflTransSymmAux :=
  continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by grind)

theorem reflTransSymmAux_mem_I (x : I × I) : reflTransSymmAux x ∈ I := by
  dsimp only [reflTransSymmAux]
  split_ifs
  · constructor
    · apply mul_nonneg <;> grind
    · rw [mul_assoc]
      apply mul_le_one₀ <;> grind
  · constructor
    · apply mul_nonneg <;> grind
    · apply mul_le_one₀ <;> grind

set_option backward.isDefEq.respectTransparency false in
/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from the constant path based at `x₀` to
  `p.trans p.symm`. -/
def reflTransSymm (p : Path x₀ x₁) : Homotopy (Path.refl x₀) (p.trans p.symm) where
  toFun x := p ⟨reflTransSymmAux x, reflTransSymmAux_mem_I x⟩
  continuous_toFun := by fun_prop
  map_zero_left := by simp [reflTransSymmAux]
  map_one_left x := by
    simp only [reflTransSymmAux, Path.trans]
    cases le_or_gt (x : ℝ) 2⁻¹ with
    | inl hx => simp [hx, ← extend_apply]
    | inr hx =>
      have : p.extend (2 - 2 * ↑x) = p.extend (1 - (2 * ↑x - 1)) := by ring_nf
      simpa [hx.not_ge, ← extend_apply]
  prop' t := by norm_num [reflTransSymmAux]

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from the constant path based at `x₁` to
  `p.symm.trans p`. -/
def reflSymmTrans (p : Path x₀ x₁) : Homotopy (Path.refl x₁) (p.symm.trans p) :=
  (reflTransSymm p.symm).cast rfl <| congr_arg _ (Path.symm_symm _)

end

section TransRefl

/-- Auxiliary function for `trans_refl_reparam`. -/
def transReflReparamAux (t : I) : ℝ :=
  if (t : ℝ) ≤ 1 / 2 then 2 * t else 1

@[continuity, fun_prop]
theorem continuous_transReflReparamAux : Continuous transReflReparamAux :=
  continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by grind)

theorem transReflReparamAux_mem_I (t : I) : transReflReparamAux t ∈ I := by
  unfold transReflReparamAux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]

theorem transReflReparamAux_zero : transReflReparamAux 0 = 0 := by
  norm_num [transReflReparamAux]

theorem transReflReparamAux_one : transReflReparamAux 1 = 1 := by
  norm_num [transReflReparamAux]

theorem trans_refl_reparam (p : Path x₀ x₁) :
    p.trans (Path.refl x₁) =
      p.reparam (fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩) (by fun_prop)
        (Subtype.ext transReflReparamAux_zero) (Subtype.ext transReflReparamAux_one) := by
  ext
  unfold transReflReparamAux
  simp only [coe_reparam]
  grind

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from `p.trans (Path.refl x₁)` to `p`. -/
def transRefl (p : Path x₀ x₁) : Homotopy (p.trans (Path.refl x₁)) p :=
  ((Homotopy.reparam p (fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩)
          (by fun_prop) (Subtype.ext transReflReparamAux_zero)
          (Subtype.ext transReflReparamAux_one)).cast
      rfl (trans_refl_reparam p).symm).symm

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from `(Path.refl x₀).trans p` to `p`. -/
def reflTrans (p : Path x₀ x₁) : Homotopy ((Path.refl x₀).trans p) p :=
  (transRefl p.symm).symm₂.cast (by simp) (by simp)

end TransRefl

section Assoc

/-- Auxiliary function for `trans_assoc_reparam`. -/
def transAssocReparamAux (t : I) : ℝ :=
  if (t : ℝ) ≤ 1 / 4 then 2 * t else if (t : ℝ) ≤ 1 / 2 then t + 1 / 4 else 1 / 2 * (t + 1)

@[continuity, fun_prop]
theorem continuous_transAssocReparamAux : Continuous transAssocReparamAux :=
  continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop)
    (continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (by grind)).continuousOn (by grind)

theorem transAssocReparamAux_mem_I (t : I) : transAssocReparamAux t ∈ I := by
  unfold transAssocReparamAux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]

theorem transAssocReparamAux_zero : transAssocReparamAux 0 = 0 := by
  norm_num [transAssocReparamAux]

theorem transAssocReparamAux_one : transAssocReparamAux 1 = 1 := by
  norm_num [transAssocReparamAux]

theorem trans_assoc_reparam {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    (p.trans q).trans r =
      (p.trans (q.trans r)).reparam
        (fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩) (by fun_prop)
        (Subtype.ext transAssocReparamAux_zero) (Subtype.ext transAssocReparamAux_one) := by
  ext x
  simp only [transAssocReparamAux, Path.trans_apply, Function.comp_apply, Path.coe_reparam]
  split_ifs
  iterate 12 grind
  · linarith
  · linarith
  · grind

/-- For paths `p q r`, we have a homotopy from `(p.trans q).trans r` to `p.trans (q.trans r)`. -/
def transAssoc {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    Homotopy ((p.trans q).trans r) (p.trans (q.trans r)) :=
  ((Homotopy.reparam (p.trans (q.trans r))
          (fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩) (by fun_prop)
          (Subtype.ext transAssocReparamAux_zero) (Subtype.ext transAssocReparamAux_one)).cast
      rfl (trans_assoc_reparam p q r).symm).symm

end Assoc

end Homotopy

namespace Homotopic

theorem refl_trans (p : Path x₀ x₁) :
    ((Path.refl x₀).trans p).Homotopic p :=
  ⟨Homotopy.reflTrans p⟩

theorem trans_refl (p : Path x₀ x₁) :
    (p.trans (Path.refl x₁)).Homotopic p :=
  ⟨Homotopy.transRefl p⟩

theorem trans_symm (p : Path x₀ x₁) :
    (p.trans p.symm).Homotopic (Path.refl x₀) :=
  ⟨(Homotopy.reflTransSymm p).symm⟩

theorem symm_trans (p : Path x₀ x₁) :
    (p.symm.trans p).Homotopic (Path.refl x₁) :=
  ⟨(Homotopy.reflSymmTrans p).symm⟩

theorem trans_assoc {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    ((p.trans q).trans r).Homotopic (p.trans (q.trans r)) :=
  ⟨Homotopy.transAssoc p q r⟩

namespace Quotient

@[simp, grind =]
theorem refl_trans (γ : Homotopic.Quotient x₀ x₁) :
    trans (refl x₀) γ = γ := by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_refl, eq] using Homotopic.refl_trans γ

@[simp, grind =]
theorem trans_refl (γ : Homotopic.Quotient x₀ x₁) :
    trans γ (refl x₁) = γ := by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_refl, eq] using Homotopic.trans_refl γ

@[simp, grind =]
theorem trans_symm (γ : Homotopic.Quotient x₀ x₁) :
    trans γ (symm γ) = refl x₀ := by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_symm, ← mk_refl, eq] using Homotopic.trans_symm γ

@[simp, grind =]
theorem symm_trans (γ : Homotopic.Quotient x₀ x₁) :
    trans (symm γ) γ = refl x₁ := by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_symm, ← mk_refl, eq] using Homotopic.symm_trans γ

@[simp, grind _=_]
theorem trans_assoc {x₀ x₁ x₂ x₃ : X}
    (γ₀ : Homotopic.Quotient x₀ x₁)
    (γ₁ : Homotopic.Quotient x₁ x₂)
    (γ₂ : Homotopic.Quotient x₂ x₃) :
    trans (trans γ₀ γ₁) γ₂ = trans γ₀ (trans γ₁ γ₂) := by
  induction γ₀ using Quotient.ind with | mk γ₀ =>
  induction γ₁ using Quotient.ind with | mk γ₁ =>
  induction γ₂ using Quotient.ind with | mk γ₂ =>
  simpa [← mk_trans, eq] using Homotopic.trans_assoc γ₀ γ₁ γ₂

end Quotient

end Homotopic

end Path

/-- The fundamental groupoid of a space `X` is defined to be a wrapper around `X`, and we
subsequently put a `CategoryTheory.Groupoid` structure on it. -/
@[ext]
structure FundamentalGroupoid (X : Type*) where
  /-- View a term of `FundamentalGroupoid X` as a term of `X`. -/
  as : X

namespace FundamentalGroupoid

/-- The equivalence between `X` and the underlying type of its fundamental groupoid.
  This is useful for transferring constructions (instances, etc.)
  from `X` to `πₓ X`. -/
@[simps]
def equiv (X : Type*) : FundamentalGroupoid X ≃ X where
  toFun x := x.as
  invFun x := .mk x

@[simp]
lemma isEmpty_iff (X : Type*) :
    IsEmpty (FundamentalGroupoid X) ↔ IsEmpty X :=
  equiv _ |>.isEmpty_congr

instance (X : Type*) [IsEmpty X] :
    IsEmpty (FundamentalGroupoid X) :=
  equiv _ |>.isEmpty

@[simp]
lemma nonempty_iff (X : Type*) :
    Nonempty (FundamentalGroupoid X) ↔ Nonempty X :=
  equiv _ |>.nonempty_congr

instance (X : Type*) [Nonempty X] :
    Nonempty (FundamentalGroupoid X) :=
  equiv _ |>.nonempty

@[simp]
lemma subsingleton_iff (X : Type*) :
    Subsingleton (FundamentalGroupoid X) ↔ Subsingleton X :=
  equiv _ |>.subsingleton_congr

instance (X : Type*) [Subsingleton X] :
    Subsingleton (FundamentalGroupoid X) :=
  equiv _ |>.subsingleton

-- TODO: It seems that `Equiv.nontrivial_congr` doesn't exist.
-- Once it is added, please add the corresponding lemma and instance.

instance {X : Type*} [Inhabited X] : Inhabited (FundamentalGroupoid X) :=
  ⟨⟨default⟩⟩

instance : Groupoid (FundamentalGroupoid X) where
  Hom x y := Path.Homotopic.Quotient x.as y.as
  id x := ⟦Path.refl x.as⟧
  comp := Path.Homotopic.Quotient.trans
  id_comp := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨Path.Homotopy.reflTrans f⟩
  comp_id := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨Path.Homotopy.transRefl f⟩
  assoc := by rintro _ _ _ _ ⟨f⟩ ⟨g⟩ ⟨h⟩; exact Quotient.sound ⟨Path.Homotopy.transAssoc f g h⟩
  inv := Quotient.lift (fun f ↦ ⟦f.symm⟧) (by rintro a b ⟨h⟩; exact Quotient.sound ⟨h.symm₂⟩)
  inv_comp := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨(Path.Homotopy.reflSymmTrans f).symm⟩
  comp_inv := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨(Path.Homotopy.reflTransSymm f).symm⟩

theorem comp_eq (x y z : FundamentalGroupoid X) (p : x ⟶ y) (q : y ⟶ z) : p ≫ q = p.trans q := rfl

theorem id_eq_path_refl (x : FundamentalGroupoid X) : 𝟙 x = ⟦Path.refl x.as⟧ := rfl

/-- The functor on fundamental groupoid induced by a continuous map. -/
@[simps] def map (f : C(X, Y)) : FundamentalGroupoid X ⥤ FundamentalGroupoid Y where
  obj x := ⟨f x.as⟩
  map p := p.map f
  map_id _ := rfl
  map_comp := by rintro _ _ _ ⟨p⟩ ⟨q⟩; exact congr_arg Quotient.mk'' (p.map_trans q f.continuous)

@[simp]
protected theorem map_id : map (.id X) = 𝟭 _ := by
  simp only [map]; congr; ext x y ⟨p⟩; rfl

@[simp]
protected theorem map_comp {Z : Type*} [TopologicalSpace Z] (g : C(Y, Z)) (f : C(X, Y)) :
    map (g.comp f) = map f ⋙ map g := by
  simp only [map]; congr; ext x y ⟨p⟩; rfl

/-- The functor sending a topological space `X` to its fundamental groupoid. -/
def fundamentalGroupoidFunctor : TopCat ⥤ Grpd where
  obj X := { α := FundamentalGroupoid X }
  map f := map f.hom
  map_id _ := FundamentalGroupoid.map_id
  map_comp _ _ := FundamentalGroupoid.map_comp _ _

@[inherit_doc] scoped notation "π" => FundamentalGroupoid.fundamentalGroupoidFunctor

/-- The fundamental groupoid of a topological space. -/
scoped notation "πₓ" => FundamentalGroupoid.fundamentalGroupoidFunctor.obj

/-- The functor between fundamental groupoids induced by a continuous map. -/
scoped notation "πₘ" => FundamentalGroupoid.fundamentalGroupoidFunctor.map

theorem map_eq {X Y : TopCat} {x₀ x₁ : X} (f : C(X, Y)) (p : Path.Homotopic.Quotient x₀ x₁) :
    (πₘ (TopCat.ofHom f)).map p = p.map f := rfl

/-- Help the typechecker by converting a point in a groupoid back to a point in
the underlying topological space. -/
abbrev toTop {X : TopCat} (x : πₓ X) : X := x.as

/-- Help the typechecker by converting a point in a topological space to a
point in the fundamental groupoid of that space. -/
abbrev fromTop {X : TopCat} (x : X) : πₓ X := ⟨x⟩

/-- Help the typechecker by converting an arrow in the fundamental groupoid of
a topological space back to a path in that space (i.e., `Path.Homotopic.Quotient`). -/
abbrev toPath {X : TopCat} {x₀ x₁ : πₓ X} (p : x₀ ⟶ x₁) :
    Path.Homotopic.Quotient x₀.as x₁.as :=
  p

/-- Help the typechecker by converting a path in a topological space to an arrow in the
fundamental groupoid of that space. -/
abbrev fromPath {x₀ x₁ : X} (p : Path.Homotopic.Quotient x₀ x₁) :
    FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x₁ := p

/-- Two paths are equal in the fundamental groupoid if and only if they are homotopic. -/
theorem fromPath_eq_iff_homotopic {x₀ x₁ : X} (f : Path x₀ x₁) (g : Path x₀ x₁) :
    fromPath (Path.Homotopic.Quotient.mk f) = fromPath (Path.Homotopic.Quotient.mk g) ↔
      f.Homotopic g :=
  ⟨fun ih ↦ Quotient.exact ih, fun h ↦ Quotient.sound h⟩

lemma eqToHom_eq {x₀ x₁ : X} (h : x₀ = x₁) :
    eqToHom congr(mk $h) = (Path.Homotopic.Quotient.refl x₁).cast h rfl := by subst h; rfl

@[reassoc]
lemma conj_eqToHom {x y x' y' : X} {p : Path.Homotopic.Quotient x y} (hx : x' = x) (hy : y' = y) :
    eqToHom congr(mk $hx) ≫ p ≫ eqToHom congr(mk $hy.symm) = p.cast hx hy := by
  subst hx hy; simp

end FundamentalGroupoid
