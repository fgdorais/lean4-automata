import Batteries
import Extra.Find
import Extra.Fin

structure StateType.{u} where
  State : Type u
  [instEnum : Fin.Enum State]
attribute [instance] StateType.instEnum
