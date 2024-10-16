import SimplcLean
import Batteries

#guard_msgs (drop info) in
simp_lc check in String Char Float USize UInt64 UInt32 UInt16 UInt8 PLift ULift Prod Sum Range
  Subtype ByteArray FloatArray List Option Array Int Nat Bool Id Monad LawfulMonad LawfulSingleton
  Std

set_option maxHeartbeats 0 in
simp_lc check
