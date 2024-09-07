import Batteries
import Extra

structure StateType.{u} where
  State : Type u
  [instFind : Find State]
  [instDecEq : DecidableEq State]
attribute [instance] StateType.instFind StateType.instDecEq
