import Mathlib.Util.PPBeta
import Mathlib.Data.FunLike.Basic

variable (F α β : Type) [FunLike F α (fun _ => β)] (f : F) (a : α)

set_option pp.beta true in
/--
info: ↑f a : β
-/
#guard_msgs in
#check f a

set_option pp.beta false in
/--
info: ↑f a : (fun x => β) a
-/
#guard_msgs in
#check f a
