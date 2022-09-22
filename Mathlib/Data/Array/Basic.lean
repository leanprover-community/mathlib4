import Std.Tactic.HaveI
import Mathlib.Data.List.Basic

attribute [simp] Array.toArrayAux_eq

alias Array.data_toArray ← List.toArray_data

namespace Array

@[simp] theorem size_mapIdxM_map (as : Array α) (bs : Array β) (f : Fin as.size → α → Id β)
    (i j h) (hj : j = bs.size) : (Array.mapIdxM.map as f i j h bs).size = as.size :=
  (SatisfiesM_Id_eq.1 (SatisfiesM_mapIdxM.go (m := Id) as f _
    (fun _ _ => .trivial) hj (fun _ _ _ => trivial))).1
