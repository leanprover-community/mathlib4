/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Order.Interval.Finset.Nat

/-!
# Projection of a function

Given a dependent function `f : (i : ι) → α i` and `s : Set ι`, one might want to consider
the restriction of `f` to the variables contained in `s`.
This is defined in this file as `Function.proj s f`.
Similarly, if we have `s t : Set ι`, `hst : s ⊆ t` and `f : (i : ↑t) → α ↑i`,
one might want to restrict it to variables contained in `s`.
This is defined in this file as `Function.proj₂ hst f`.
We also define analoguous functions when `Finset`s are provided.

Having these definitions avoids heavy type ascription when manipulating these functions and allow
some rewriting when composing them (see `Function.proj₂_comp_proj` for instance).

We also define analoguous functions for sets of the form `Set.Iic n` and `Finset.Iic n`, where
`n : ℕ`, see `Function.projNat` for instance.

## Main definitions

* `Function.proj s f`: Restricts the function `f` to the variables contained in `s`.
* `Function.projNat n f`: Restricts the function `f` to the variables indexed by integers `≤ n`.
-/

open Function

section Generality

variable {ι : Type*}

namespace Function

variable {α : ι → Type*}

/-- Given a dependent function, restrict it to a function of variables in `s`. -/
@[simp]
def proj (s : Set ι) (x : (i : ι) → α i) (i : s) : α i := x i

/-- Given a dependent function of variables in `t`, restrict it to a function of variables in `s`
when `s ⊆ t`. -/
@[simp]
def proj₂ {s t : Set ι} (hst : s ⊆ t) (x : (i : t) → α i) (i : s) : α i := x ⟨i.1, hst i.2⟩

/-- Given a dependent function, restrict it to a function of variables in `s`, `Finset` version. -/
@[simp]
def fproj (s : Finset ι) (x : (i : ι) → α i) (i : s) : α i := x i

/-- Given a dependent function of variables in `t`, restrict it to a function of variables in `s`
when `s ⊆ t`, `Finset` version. -/
@[simp]
def fproj₂ {s t : Finset ι} (hst : s ⊆ t) (x : (i : t) → α i) (i : s) : α i := x ⟨i.1, hst i.2⟩

theorem fproj_eq_proj (s : Finset ι) : @fproj ι α s = proj (s : Set ι) := rfl

theorem fproj₂_eq_proj₂ {s t : Finset ι} (hst : s ⊆ t) :
    fproj₂ (α := α) hst = proj₂ (Finset.coe_subset.2 hst) := rfl

theorem proj₂_comp_proj {s t : Set ι} (hst : s ⊆ t) :
    (proj₂ hst) ∘ (@proj ι α t) = proj s := rfl

theorem fproj₂_comp_fproj {s t : Finset ι} (hst : s ⊆ t) :
    (fproj₂ hst) ∘ (@fproj ι α t) = fproj s := rfl

theorem proj₂_comp_proj₂ {s t u : Set ι} (hst : s ⊆ t) (htu : t ⊆ u) :
    (proj₂ (α := α) hst) ∘ (proj₂ htu) = proj₂ (hst.trans htu) := rfl

theorem fproj₂_comp_fproj₂ {s t u : Finset ι} (hst : s ⊆ t) (htu : t ⊆ u) :
    (fproj₂ (α := α) hst) ∘ (fproj₂ htu) = fproj₂ (hst.trans htu) := rfl

end Function

-- variable {X : ι → Type*}

-- section measurability

-- variable [∀ i, MeasurableSpace (X i)]

-- @[measurability, fun_prop]
-- theorem measurable_proj (s : Set ι) : Measurable (@proj ι X s) :=
--   measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

-- @[measurability, fun_prop]
-- theorem measurable_proj₂ {s t : Set ι} (hst : s ⊆ t) :
--     Measurable (proj₂ (α := X) hst) :=
--   measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

-- @[measurability, fun_prop]
-- theorem measurable_fproj (s : Finset ι) : Measurable (@fproj ι X s) :=
--   measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

-- @[measurability, fun_prop]
-- theorem measurable_fproj₂ {s t : Finset ι} (hst : s ⊆ t) :
--     Measurable (fproj₂ (α := X) hst) :=
--   measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

-- end measurability

-- section continuity

-- variable [∀ i, TopologicalSpace (X i)]

-- @[fun_prop]
-- theorem continuous_proj (s : Set ι) : Continuous (@proj ι X s) :=
--   continuous_pi fun _ ↦ continuous_apply _

-- @[fun_prop]
-- theorem continuous_proj₂ {s t : Set ι} (hst : s ⊆ t) :
--     Continuous (proj₂ (α := X) hst) :=
--   continuous_pi fun _ ↦ continuous_apply _

-- @[fun_prop]
-- theorem continuous_fproj (s : Finset ι) : Continuous (@fproj ι X s) :=
--   continuous_pi fun _ ↦ continuous_apply _

-- @[fun_prop]
-- theorem continuous_fproj₂ {s t : Finset ι} (hst : s ⊆ t) :
--     Continuous (fproj₂ (α := X) hst) :=
--   continuous_pi fun _ ↦ continuous_apply _

-- end continuity

end Generality

section Nat

namespace Function

variable {α : ℕ → Type*}

/-- Given a dependent function indexed by `ℕ`, specialize it as a function on `Iic n`.
Contrary to `Function.proj`, this is not `simp` definition to avoid unfolding it
when it's not fully applied. -/
def projNat (n : ℕ) := @proj ℕ α (Set.Iic n)

@[simp]
lemma projNat_def (n : ℕ) (x : Π n, α n) (i : Set.Iic n) : projNat n x i = x i := rfl

/-- Given a dependent function indexed by `Iic n`, specialize it as a function on `Iic m` when
`m ≤ n`.
Contrary to `Function.proj`, this is not `simp` definition to avoid unfolding it
when it's not fully applied. -/
def projNat₂ {m n : ℕ} (hmn : m ≤ n) := proj₂ (α := α) (Set.Iic_subset_Iic.2 hmn)

@[simp]
lemma projNat₂_def {m n : ℕ} (hmn : m ≤ n) (x : Π i : Set.Iic n, α i) (i : Set.Iic m) :
    projNat₂ hmn x i = x ⟨i.1, Set.Iic_subset_Iic.2 hmn i.2⟩ := rfl

/-- Given a dependent function indexed by `ℕ`, specialize it as a function on `Iic n`,
`Finset` version.
Contrary to `Function.proj`, this is not `simp` definition to avoid unfolding it
when it's not fully applied. -/
def fprojNat (n : ℕ) := @fproj ℕ α (Finset.Iic n)

@[simp]
lemma fprojNat_def (n : ℕ) (x : Π n, α n) (i : Finset.Iic n) : fprojNat n x i = x i := rfl

/-- Given a dependent function indexed by `Iic n`, specialize it as a function on `Iic m` when
`m ≤ n`, `Finset` version.
Contrary to `Function.proj`, this is not `simp` definition to avoid unfolding it
when it's not fully applied. -/
def fprojNat₂ {m n : ℕ} (hmn : m ≤ n) := fproj₂ (α := α) (Finset.Iic_subset_Iic.2 hmn)

@[simp]
lemma fprojNat₂_def {m n : ℕ} (hmn : m ≤ n) (x : Π i : Finset.Iic n, α i) (i : Finset.Iic m) :
    fprojNat₂ hmn x i = x ⟨i.1, Finset.Iic_subset_Iic.2 hmn i.2⟩ := rfl

theorem projNat₂_comp_projNat {m n : ℕ} (hmn : m ≤ n) :
    (projNat₂ hmn) ∘ (@projNat α n) = projNat m := rfl

theorem fprojNat₂_comp_fprojNat {m n : ℕ} (hmn : m ≤ n) :
    (fprojNat₂ hmn) ∘ (@fprojNat α n) = fprojNat m := rfl

theorem projNat₂_comp_projNat₂ {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (projNat₂ (α := α) hmn) ∘ (projNat₂ hnk) = projNat₂ (hmn.trans hnk) := rfl

theorem fprojNat₂_comp_fprojNat₂ {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (fprojNat₂ (α := α) hmn) ∘ (fprojNat₂ hnk) = fprojNat₂ (hmn.trans hnk) := rfl

end Function
/-
variable {X : ℕ → Type*}

section measurability

variable [∀ n, MeasurableSpace (X n)]

@[measurability, fun_prop]
theorem measurable_projNat (n : ℕ) : Measurable (@projNat X n) := measurable_proj _

@[measurability, fun_prop]
theorem measurable_projNat₂ {m n : ℕ} (hmn : m ≤ n) : Measurable (projNat₂ (α := X) hmn) :=
  measurable_proj₂ _

@[measurability, fun_prop]
theorem measurable_fprojNat (n : ℕ) : Measurable (@fprojNat X n) := measurable_proj _

@[measurability, fun_prop]
theorem measurable_fprojNat₂ {m n : ℕ} (hmn : m ≤ n) : Measurable (fprojNat₂ (α := X) hmn) :=
  measurable_fproj₂ _

end measurability

section continuity

variable [∀ n, TopologicalSpace (X n)]

@[fun_prop]
theorem continuous_projNat (n : ℕ) : Continuous (@projNat X n) := continuous_proj _

@[fun_prop]
theorem continuous_projNat₂ {m n : ℕ} (hmn : m ≤ n) : Continuous (projNat₂ (α := X) hmn) :=
  continuous_proj₂ _

@[fun_prop]
theorem continuous_fprojNat (n : ℕ) : Continuous (@fprojNat X n) := continuous_proj _

@[fun_prop]
theorem continuous_fprojNat₂ {m n : ℕ} (hmn : m ≤ n) : Continuous (fprojNat₂ (α := X) hmn) :=
  continuous_fproj₂ _

end continuity-/

end Nat
