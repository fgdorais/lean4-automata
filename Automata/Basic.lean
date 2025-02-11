import Batteries
import Extra.Find
import Extra.Fin
import Extra.List

structure StateType.{u} where
  State : Type u
  [instEnum : Fin.Enum State]
attribute [instance] StateType.instEnum

/-- Length of the binary representation of `n`. -/
protected abbrev Nat.lg2 (n : Nat) := if n = 0 then 0 else n.log2 + 1

theorem Nat.lt_2_pow_lg2 (x : Nat) : x < 2 ^ x.lg2 := by
  simp only [Nat.lg2]
  split
  · simp [*]
  · exact Nat.lt_log2_self
