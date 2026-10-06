module

import Mathlib.Init
import all Mathlib.Tactic.Linter.Style

namespace Foo

set_option linter.style.missingEnd true

/--
warning: unclosed sections or namespaces; expected: '

end Foo'

Note: This linter can be disabled with `set_option linter.style.missingEnd false`
-/
#guard_msgs in
run_cmd Mathlib.Linter.Style.missingEnd.missingEndLinter.run #[]

set_option linter.style.missingEnd false
