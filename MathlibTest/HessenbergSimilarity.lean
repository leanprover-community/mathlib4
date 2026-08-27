module

import Mathlib.LinearAlgebra.Matrix.Hessenberg.Similarity
import Mathlib.LinearAlgebra.Matrix.Notation

example :
    let M : Matrix (Fin 3) (Fin 3) ℚ :=
      !![ 1, 2, 0;
          1, 3, 0;
          0, 3, 1]
    M.IsUpperHessenberg := by decide

example :
    let M : Matrix (Fin 3) (Fin 3) ℚ :=
      !![ 1, 2, 0;
          0, 3, 0;
          1, 0, 1]
    ¬ M.IsUpperHessenberg := by decide

example :
    let M : Matrix (Fin 3) (Fin 3) ℚ :=
      !![ 1, 2, 3;
          4, 5, 6;
          0, 7, 8]
    Hessenberg.Similarity M where
      σ := 1
      L := 1
      H := !![1, 2, 3; 4, 5, 6; 0, 7, 8]
      similarity := by decide +kernel
      L_lowerTriangular := by decide
      L_diag_ne_zero := by decide
      H_hessenberg := by decide

def certShear :
    let M : Matrix (Fin 3) (Fin 3) ℚ :=
      !![ 1, 2, 3;
          1, 1, 1;
          2, 0, 1]
    Hessenberg.Similarity M where
      σ := 1
      L := !![1, 0, 0; 0, 1, 0; 0, 2, 1]
      H := !![1, 8, 3; 1, 3, 1; 0, -4, -1]
      similarity := by decide +kernel
      L_lowerTriangular := by decide
      L_diag_ne_zero := by decide
      H_hessenberg := by decide

example :
    let M : Matrix (Fin 3) (Fin 3) ℚ :=
      !![ 1, 2, 3;
          1, 1, 1;
          2, 0, 1]
    let H : Matrix (Fin 3) (Fin 3) ℚ := !![1, 8, 3; 1, 3, 1; 0, -4, -1]
    M.charpoly = H.charpoly := certShear.charpoly_eq
