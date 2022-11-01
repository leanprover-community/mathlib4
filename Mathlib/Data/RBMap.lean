import Std.Data.RBMap
import Std.Data.HashMap

namespace Std.HashMap

variable [BEq α] [Hashable α]

def keys (m : HashMap α β) : List α :=
m.fold (fun ks k _ => k :: ks) []

def values (m : HashMap α β) : List β :=
m.fold (fun vs _ v => v :: vs) []

def consVal (self : HashMap α (List β)) (a : α) (b : β) :=
match self.find? a with
| none => self.insert a [b]
| some L => self.insert a (b::L)

end Std.HashMap
