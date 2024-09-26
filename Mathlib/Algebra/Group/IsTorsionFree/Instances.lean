import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Algebra.Group.IsTorsionFree.Defs
import Mathlib.Algebra.Group.Pi.Basic

@[to_additive prod]
instance Monoid.IsTorsionFree.prod {M N : Type*} [Monoid M] [Monoid N] [IsTorsionFree M]
    [IsTorsionFree N] : IsTorsionFree (M × N) where
  pow_ne_one x n hx hn hxn := by
    rw [Prod.ext_iff] at hxn
    exact hx (Prod.ext ((pow_eq_one_iff_left hn.ne').1 hxn.1)
      ((pow_eq_one_iff_left hn.ne').1 hxn.2))

@[to_additive]
instance Monoid.IsTorsionFree.pi {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]
    [∀ i, IsTorsionFree (M i)] : IsTorsionFree (∀ i, M i) where
  pow_ne_one _x _n hx hn hxn :=
    hx <| funext fun i ↦ (pow_eq_one_iff_left hn.ne').1 (congrFun hxn i)

@[to_additive]
theorem Function.Injective.monoidIsTorsionFree {M N : Type*} [Monoid M] [Monoid N]
    [Monoid.IsTorsionFree N] (f : M →* N) (hf : Function.Injective f) : Monoid.IsTorsionFree M where
  pow_ne_one x n hx hn := ne_of_apply_ne f <| by simpa [hn.ne', map_eq_one_iff f hf]

@[to_additive]
instance Units.instIsTorsionFree {M : Type*} [Monoid M] [Monoid.IsTorsionFree M] :
    Monoid.IsTorsionFree Mˣ :=
  Units.ext.monoidIsTorsionFree (Units.coeHom M)
