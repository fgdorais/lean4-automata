import Batteries
import Extra.Find
import Extra.Fin

structure StateType.{u} where
  State : Type u
  [instEnum : Fin.Enum State]
attribute [instance] StateType.instEnum


namespace Nat
abbrev lg2 (n : Nat) := if n = 0 then 0 else n.log2 + 1
end Nat
