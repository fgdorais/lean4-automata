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

def BitVec.dot (a b : BitVec size) : Bool := (a &&& b) != 0

abbrev BitMat (rows cols) := Vector (BitVec cols) rows

namespace BitMat

def row (a : BitMat r c) (i) (h : i < r := by get_elem_tactic) : BitVec c := a[i]

def col (a : BitMat r c) (j) (h : j < c := by get_elem_tactic) : BitVec r :=
  Fin.foldr r (fun i t => t.shiftConcat a[i][j]) 0

def bvMul (a : BitMat r c) (x : BitVec c) : BitVec r :=
  Fin.foldr r (fun i t => t.shiftConcat (a[i].dot x)) 0

def combo (a : BitMat r c) (x : BitVec r) : BitVec c :=
  Fin.foldr r (fun i t => bif x[i] then t ||| a[i] else t) 0

protected def mul (a : BitMat r m) (b  : BitMat m c) : BitMat r c :=
  .ofFn fun i => combo b a[i]
