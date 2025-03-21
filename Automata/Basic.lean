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

namespace BitVec

def dot (a b : BitVec size) : Bool := (a &&& b) != 0

theorem eq_zero_iff_forall_getElem_eq_false {a : BitVec size} :
    a = 0 ↔ ∀ (i) (h : i < size), a[i] = false := by
  simp [BitVec.eq_of_getElem_eq_iff]

theorem ne_zero_iff_exists_getElem_eq_true {a : BitVec size} :
    a ≠ 0 ↔ ∃ (i : Nat) (h : i < size), a[i] = true := by
  constructor
  · intro hz
    by_contra he
    simp only [not_exists, Bool.not_eq_true, ← eq_zero_iff_forall_getElem_eq_false] at he
    contradiction
  · intro ⟨i, hi, ha⟩ hz
    rw [eq_zero_iff_forall_getElem_eq_false] at hz
    rw [hz] at ha
    contradiction

end BitVec

abbrev BitMat (rows cols) := Vector (BitVec cols) rows

namespace BitMat

def ofFn (f : Fin r → Fin c → Bool) : BitMat r c :=
  Vector.ofFn fun i => BitVec.ofFnLE fun j => f i j

def row (a : BitMat r c) (i) (h : i < r := by get_elem_tactic) : BitVec c := a[i]

def col (a : BitMat r c) (j) (h : j < c := by get_elem_tactic) : BitVec r :=
  BitVec.ofFnLE fun i => a[i][j]

def bvMul (a : BitMat r c) (x : BitVec c) : BitVec r :=
  BitVec.ofFnLE fun i => a[i].dot x

def combo (a : BitMat r c) (x : BitVec r) : BitVec c :=
  Fin.foldr r (fun i t => bif x[i] then t ||| a[i] else t) 0

protected def mul (a : BitMat r m) (b  : BitMat m c) : BitMat r c :=
  Vector.ofFn fun i => combo b a[i]
