module

public import Mathlib.Algebra.ContinuedFractions.Basic

public section

namespace GenContFract

variable {K : Type*} (v : K) [Field K]

variable {g : GenContFract K}

def Euler (h : K) (ρ : Stream'.Seq K) : GenContFract K := ⟨h, ⟨
  fun n => match n with
  | 0 => ρ.get? n |>.map fun ρ => ⟨ρ, 1⟩
  | _ => ρ.get? n |>.map fun ρ => ⟨-ρ, 1 + ρ⟩,
  fun {n} h => match n with
  | 0 => by simp_all
  | n + 1 => by simp at h; simpa using ρ.property h
⟩⟩

private def toEulerAux (g : GenContFract K) : Stream'.Seq K := ⟨
  fun n => match n with
  | 0 => g.s.get? n |>.map fun c => c.a / c.b
  | _ => g.s.get? n |>.map fun c => - c.a * g.dens (n - 1) / g.dens (n + 1),
  fun {n} h => match n with
  | 0 => by simp_all
  | n + 1 => by simp at h; simpa using g.s.property h
⟩

def toEuler (g : GenContFract K) : GenContFract K := Euler g.h <| toEulerAux g

end GenContFract
