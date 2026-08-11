/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir, Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Order.Ring.StandardPart
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.FilterProduct

/-!
# Construction of the hyperreal numbers as an ultraproduct of real sequences

We define the `Hyperreal` numbers as quotients of sequences `ℕ → ℝ` by an ultrafilter. These form
a field, and we prove some of their basic properties.

Note that most of the machinery that is usually defined for the specific purpose of non-standard
analysis (infinitesimal and infinite elements, standard parts) has been generalized to other
non-archimedean fields. In particular:

- `ArchimedeanClass` can be used to measure whether an element is infinitesimal (`0 < mk x`) or
  infinite (`mk x < 0`).
- `ArchimedeanClass.stdPart` generalizes the standard part function to a general ordered field.

## Todo

Use Łoś's Theorem `FirstOrder.Language.Ultraproduct.sentence_realize` to formalize the transfer
principle on `Hyperreal`.
-/

@[expose] public section

open ArchimedeanClass Filter Germ Topology

noncomputable section

/-- Hyperreal numbers on the ultrafilter extending the cofinite filter. -/
def Hyperreal : Type :=
  Germ (hyperfilter ℕ : Filter ℕ) ℝ
deriving Inhabited

namespace Hyperreal

@[inherit_doc] notation "ℝ*" => Hyperreal

instance : Field ℝ* :=
  inferInstanceAs (Field (Germ _ _))

instance : LinearOrder ℝ* :=
  inferInstanceAs (LinearOrder (Germ _ _))

instance : IsStrictOrderedRing ℝ* :=
  inferInstanceAs (IsStrictOrderedRing (Germ _ _))

/-- Natural embedding `ℝ → ℝ*`. -/
@[coe] def ofReal : ℝ → ℝ* := const

instance : CoeTC ℝ ℝ* := ⟨ofReal⟩

@[simp, norm_cast]
theorem coe_eq_coe {x y : ℝ} : (x : ℝ*) = y ↔ x = y :=
  Germ.const_inj

theorem coe_ne_coe {x y : ℝ} : (x : ℝ*) ≠ y ↔ x ≠ y :=
  coe_eq_coe.not

@[simp, norm_cast]
theorem coe_eq_zero {x : ℝ} : (x : ℝ*) = 0 ↔ x = 0 :=
  coe_eq_coe

@[simp, norm_cast]
theorem coe_eq_one {x : ℝ} : (x : ℝ*) = 1 ↔ x = 1 :=
  coe_eq_coe

@[norm_cast]
theorem coe_ne_zero {x : ℝ} : (x : ℝ*) ≠ 0 ↔ x ≠ 0 :=
  coe_ne_coe

@[norm_cast]
theorem coe_ne_one {x : ℝ} : (x : ℝ*) ≠ 1 ↔ x ≠ 1 :=
  coe_ne_coe

@[simp, norm_cast]
theorem coe_one : ↑(1 : ℝ) = (1 : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ↑(0 : ℝ) = (0 : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_inv (x : ℝ) : ↑x⁻¹ = (x⁻¹ : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_neg (x : ℝ) : ↑(-x) = (-x : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_add (x y : ℝ) : ↑(x + y) = (x + y : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : ℝ) : ℝ*) = OfNat.ofNat n :=
  rfl

@[simp, norm_cast]
theorem coe_mul (x y : ℝ) : ↑(x * y) = (x * y : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_div (x y : ℝ) : ↑(x / y) = (x / y : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_sub (x y : ℝ) : ↑(x - y) = (x - y : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_le_coe {x y : ℝ} : (x : ℝ*) ≤ y ↔ x ≤ y :=
  Germ.const_le_iff

@[simp, norm_cast]
theorem coe_lt_coe {x y : ℝ} : (x : ℝ*) < y ↔ x < y :=
  Germ.const_lt_iff

@[simp, norm_cast]
theorem coe_nonneg {x : ℝ} : 0 ≤ (x : ℝ*) ↔ 0 ≤ x :=
  coe_le_coe

@[simp, norm_cast]
theorem coe_pos {x : ℝ} : 0 < (x : ℝ*) ↔ 0 < x :=
  coe_lt_coe

@[simp, norm_cast]
theorem coe_abs (x : ℝ) : ((|x| : ℝ) : ℝ*) = |↑x| :=
  const_abs x

@[simp, norm_cast]
theorem coe_max (x y : ℝ) : ((max x y : ℝ) : ℝ*) = max ↑x ↑y :=
  Germ.const_max _ _

@[simp, norm_cast]
theorem coe_min (x y : ℝ) : ((min x y : ℝ) : ℝ*) = min ↑x ↑y :=
  Germ.const_min _ _

/-- The canonical map `ℝ → ℝ*` as an `OrderRingHom`. -/
@[simps]
def coeRingHom : ℝ →+*o ℝ* where
  toFun x := x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  monotone' _ _ := coe_le_coe.2

@[simp]
theorem archimedeanClassMk_coe_nonneg (x : ℝ) : 0 ≤ mk (x : ℝ*) :=
  mk_map_nonneg_of_archimedean coeRingHom x

@[simp]
theorem archimdeanClassMk_coe {x : ℝ} (hx : x ≠ 0) : mk (x : ℝ*) = 0 :=
  mk_map_of_archimedean' coeRingHom hx

@[simp]
theorem stdPart_coe (x : ℝ) : stdPart (x : ℝ*) = x :=
  stdPart_map_real coeRingHom x

/-! ### Basic constants -/

/-- Construct a hyperreal number from a sequence of real numbers. -/
def ofSeq (f : ℕ → ℝ) : ℝ* := (↑f : Germ (hyperfilter ℕ : Filter ℕ) ℝ)

theorem ofSeq_surjective : Function.Surjective ofSeq := Quot.exists_rep

theorem ofSeq_lt_ofSeq {f g : ℕ → ℝ} : ofSeq f < ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n < g n :=
  Germ.coe_lt

theorem ofSeq_le_ofSeq {f g : ℕ → ℝ} : ofSeq f ≤ ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n ≤ g n :=
  Germ.coe_le

/-! #### ω -/

/-- A sample infinite hyperreal ω = ⟦(0, 1, 2, 3, ⋯)⟧. -/
def omega : ℝ* := ofSeq Nat.cast

@[inherit_doc] scoped notation "ω" => Hyperreal.omega
recommended_spelling "omega" for "ω" in [omega, «termω»]

theorem coe_lt_omega (r : ℝ) : r < ω := by
  apply ofSeq_lt_ofSeq.2 <| Filter.Eventually.filter_mono Nat.hyperfilter_le_atTop _
  obtain ⟨n, hn⟩ := exists_nat_gt r
  rw [eventually_atTop]
  exact ⟨n, fun m hm ↦ hn.trans_le (mod_cast hm)⟩

theorem omega_pos : 0 < ω :=
  coe_lt_omega 0

@[simp]
theorem omega_ne_zero : ω ≠ 0 :=
  omega_pos.ne'

@[simp]
theorem abs_omega : |ω| = ω :=
  abs_of_pos omega_pos

@[simp]
theorem archimedeanClassMk_omega_neg : mk ω < 0 :=
  fun n ↦ by simpa using! coe_lt_omega n

@[simp]
theorem stdPart_omega : stdPart ω = 0 := by
  rw [stdPart_eq_zero]
  exact archimedeanClassMk_omega_neg.ne

/-! #### ε -/

/-- A sample infinitesimal hyperreal ε = ⟦(0, 1, 1/2, 1/3, ⋯)⟧. -/
def epsilon : ℝ* :=
  ofSeq fun n => n⁻¹

@[inherit_doc] scoped notation "ε" => Hyperreal.epsilon
recommended_spelling "epsilon" for "ε" in [epsilon, «termε»]

@[simp]
theorem inv_omega : ω⁻¹ = ε :=
  rfl

@[simp]
theorem inv_epsilon : ε⁻¹ = ω :=
  @inv_inv _ _ ω

@[simp]
theorem epsilon_pos : 0 < ε :=
  inv_pos_of_pos omega_pos

@[simp]
theorem epsilon_ne_zero : ε ≠ 0 :=
  epsilon_pos.ne'

@[simp]
theorem epsilon_mul_omega : ε * ω = 1 :=
  @inv_mul_cancel₀ _ _ ω omega_ne_zero

@[simp]
theorem archimedeanClassMk_epsilon_pos : 0 < mk ε := by
  simp [← inv_omega]

/-!
### Some facts about `Tendsto`
-/

@[simp]
theorem tendsto_ofSeq {f : ℕ → ℝ} {lb : Filter ℝ} :
    (ofSeq f).Tendsto lb ↔ Tendsto f (hyperfilter ℕ) lb :=
  .rfl

theorem stdPart_map {x : ℝ*} {r : ℝ} {f : ℝ → ℝ} (hf : ContinuousAt f r)
    (hxr : x.Tendsto (𝓝 r)) : (x.map f).Tendsto (𝓝 (f r)) := by
  rcases ofSeq_surjective x with ⟨g, rfl⟩
  exact hf.tendsto.comp hxr

theorem stdPart_map₂ {x y : ℝ*} {r s : ℝ} {f : ℝ → ℝ → ℝ}
    (hxr : x.Tendsto (𝓝 r)) (hys : y.Tendsto (𝓝 s))
    (hf : ContinuousAt (Function.uncurry f) (r, s)) : (x.map₂ f y).Tendsto (𝓝 (f r s)) := by
  rcases ofSeq_surjective x with ⟨x, rfl⟩
  rcases ofSeq_surjective y with ⟨y, rfl⟩
  exact hf.tendsto.comp (hxr.prodMk_nhds hys)

theorem tendsto_iff_forall {x : ℝ*} {r : ℝ} :
    x.Tendsto (𝓝 r) ↔ (∀ s < r, s ≤ x) ∧ (∀ s > r, x ≤ s) := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq, (nhds_basis_Ioo _).tendsto_right_iff]
  simp_rw [Set.mem_Ioo, eventually_and, ← ofSeq_lt_ofSeq]
  refine ⟨fun H ↦ ⟨fun s hs ↦ ?_, fun s hs ↦ ?_⟩, fun H ⟨s, t⟩ ⟨hs, ht⟩ ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨t, ht⟩ := exists_gt r
    exact (H ⟨s, t⟩ ⟨hs, ht⟩).1.le
  · obtain ⟨t, ht⟩ := exists_lt r
    exact (H ⟨t, s⟩ ⟨ht, hs⟩).2.le
  · obtain ⟨u, hu, hu'⟩ := exists_between hs
    exact (coe_lt_coe.2 hu).trans_le (H.1 _ hu')
  · obtain ⟨u, hu, hu'⟩ := exists_between ht
    exact (H.2 _ hu).trans_lt (coe_lt_coe.2 hu')

theorem archimedeanClassMk_nonneg_of_tendsto {x : ℝ*} {r : ℝ} (hx : x.Tendsto (𝓝 r)) :
    0 ≤ mk x := by
  rw [tendsto_iff_forall] at hx
  obtain ⟨s, hs⟩ := exists_lt r
  obtain ⟨t, ht⟩ := exists_gt r
  exact mk_nonneg_of_le_of_le_of_archimedean coeRingHom (hx.1 s hs) (hx.2 t ht)

theorem stdPart_of_tendsto {x : ℝ*} {r : ℝ} (hx : x.Tendsto (𝓝 r)) : stdPart x = r := by
  rw [tendsto_iff_forall] at hx
  exact stdPart_eq coeRingHom hx.1 hx.2

theorem archimedeanClassMk_pos_of_tendsto {x : ℝ*} (hx : x.Tendsto (𝓝 0)) : 0 < mk x := by
  apply (archimedeanClassMk_nonneg_of_tendsto hx).lt_of_ne'
  rw [← stdPart_eq_zero, stdPart_of_tendsto hx]

@[simp]
theorem stdPart_epsilon : stdPart ε = 0 :=
  stdPart_eq_zero.2 <| archimedeanClassMk_epsilon_pos.ne'

theorem epsilon_lt_of_pos {r : ℝ} : 0 < r → ε < r :=
  lt_of_pos_of_archimedean coeRingHom archimedeanClassMk_epsilon_pos

theorem epsilon_lt_of_neg {r : ℝ} : r < 0 → r < ε :=
  lt_of_neg_of_archimedean coeRingHom archimedeanClassMk_epsilon_pos

theorem lt_of_tendsto_atTop {x : ℝ*} (r : ℝ) (hx : x.Tendsto atTop) : r < x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq] at hx
  exact ofSeq_lt_ofSeq.2 <| hx.eventually_mem (Ioi_mem_atTop r)

theorem lt_of_tendsto_atBot {x : ℝ*} (r : ℝ) (hx : x.Tendsto atBot) : x < r := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq] at hx
  exact ofSeq_lt_ofSeq.2 <| hx.eventually_mem (Iio_mem_atBot r)

theorem archimedeanClassMk_neg_of_tendsto_atTop {x : ℝ*} (hx : x.Tendsto atTop) : mk x < 0 := by
  have : 0 < x := lt_of_tendsto_atTop 0 hx
  intro n
  simpa [abs_of_pos this] using! lt_of_tendsto_atTop n hx

theorem archimedeanClassMk_neg_of_tendsto_atBot {x : ℝ*} (hx : x.Tendsto atBot) : mk x < 0 := by
  have : x < 0 := lt_of_tendsto_atBot 0 hx
  intro n
  simpa [abs_of_neg this, lt_neg] using! lt_of_tendsto_atBot (-n) hx

theorem tendsto_atTop_iff {x : ℝ*} : x.Tendsto atTop ↔ 0 < x ∧ mk x < 0 where
  mp h := ⟨lt_of_tendsto_atTop 0 h, archimedeanClassMk_neg_of_tendsto_atTop h⟩
  mpr h := by
    rcases ofSeq_surjective x with ⟨f, rfl⟩
    rw [tendsto_ofSeq, tendsto_atTop]
    exact fun r ↦ ofSeq_le_ofSeq.1 <|
      (lt_of_mk_lt_mk_of_nonneg (h.2.trans_le <| archimedeanClassMk_coe_nonneg r) h.1.le).le

theorem tendsto_atBot_iff {x : ℝ*} : x.Tendsto atBot ↔ x < 0 ∧ mk x < 0 where
  mp h := ⟨lt_of_tendsto_atBot 0 h, archimedeanClassMk_neg_of_tendsto_atBot h⟩
  mpr h := by
    rcases ofSeq_surjective x with ⟨f, rfl⟩
    rw [tendsto_ofSeq, tendsto_atBot]
    exact fun r ↦ ofSeq_le_ofSeq.1 <|
      (lt_of_mk_lt_mk_of_nonpos (h.2.trans_le <| archimedeanClassMk_coe_nonneg r) h.1.le).le

end Hyperreal
end

/-
Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: restore `positivity` plugin

namespace Tactic

open Positivity

private theorem hyperreal_coe_ne_zero {r : ℝ} : r ≠ 0 → (r : ℝ*) ≠ 0 :=
  Hyperreal.coe_ne_zero.2

private theorem hyperreal_coe_nonneg {r : ℝ} : 0 ≤ r → 0 ≤ (r : ℝ*) :=
  Hyperreal.coe_nonneg.2

private theorem hyperreal_coe_pos {r : ℝ} : 0 < r → 0 < (r : ℝ*) :=
  Hyperreal.coe_pos.2

/-- Extension for the `positivity` tactic: cast from `ℝ` to `ℝ*`. -/
@[positivity]
unsafe def positivity_coe_real_hyperreal : expr → tactic strictness
  | q(@coe _ _ $(inst) $(a)) => do
    unify inst q(@coeToLift _ _ Hyperreal.hasCoeT)
    let strictness_a ← core a
    match strictness_a with
      | positive p => positive <$> mk_app `` hyperreal_coe_pos [p]
      | nonnegative p => nonnegative <$> mk_app `` hyperreal_coe_nonneg [p]
      | nonzero p => nonzero <$> mk_app `` hyperreal_coe_ne_zero [p]
  | e =>
    pp e >>= fail ∘ format.bracket "The expression " " is not of the form `(r : ℝ*)` for `r : ℝ`"

end Tactic
-/
