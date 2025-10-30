import Hammer

-- This is only meant to test whether `hammer` was successfully built. `aesopPremises` and `autoPremises` are
-- set to 0 to prevent CI tests from spamming the premise selection server

example : True := by
  hammer {aesopPremises := 0, autoPremises := 0}
