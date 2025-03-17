import Automata.NFA.Basic
import Automata.NFA.Matrix

namespace NFA
variable (m : NFA α)
open NFA.Matrix

abbrev toMatrix : Matrix α where
  size := m.size
  start := BitVec.ofFnLE fun i => m.start (Fin.Enum.enum i)
  final := BitVec.ofFnLE fun i => m.final (Fin.Enum.enum i)
  trans x := BitMat.ofFnLE fun i j => m.trans x (Fin.Enum.enum j) (Fin.Enum.enum i)

theorem toMFA_run {start : BitVec m.toMatrix.size Bool} :
  (m.toMatrix.run xs start)[i] = Fin.any fun t => start[Fin.find t] && m.run xs t (Fin.Enum.enum i) := by
  induction xs generalizing start with
  | nil =>
    simp only [Function.const_apply]
    rw [Matrix.run_nil]
    constructor
    · intro hstart
      exists Finite.get m.State i
      constructor
      · rw [Finite.find_get]
        exact hstart
      · rw [NFA.run_nil]
    · intro ⟨t, hstart, hrun⟩
      rw [NFA.run_nil] at hrun
      rw [hrun, Finite.find_get] at hstart
      exact hstart
  | cons x xs ih =>
    rw [Matrix.run_cons, ih]
    simp?
    constructor
    · intro ⟨t, hmat, hrun⟩
      unfold Matrix.mulVecBool at hmat
      rw [Vector.get_ofFn] at hmat
      simp? at hmat
      match hmat with
      | ⟨i, htrans, hstart⟩ =>
        rw [Matrix.get_ofFn] at htrans
        rw [Finite.get_find] at htrans
        exists Finite.get m.State i
        constructor
        · rw [Finite.find_get]
          exact hstart
        · rw [NFA.run_cons]
          exists t
    · intro ⟨t, hstart, hrun⟩
      rw [NFA.run_cons] at hrun
      match hrun with
      | ⟨u, htrans, hrun⟩ =>
        exists u
        constructor
        · unfold Matrix.mulVecBool
          rw [Vector.get_ofFn]
          simp?
          exists Finite.find t
          rw [Matrix.get_ofFn]
          rw [Finite.get_find]
          rw [Finite.get_find]
          constructor
          · exact htrans
          · exact hstart
        · exact hrun

theorem toMFA_correct (xs : List α) : m.toMatrix.accept xs = m.accept xs := by
  unfold Matrix.accept NFA.accept BitVec.dot
  simp only [Function.const_apply, BitVec.ofNat_eq_ofNat]
  constructor
  · intro ⟨i, hfinal, hrun⟩
    rw [Vector.get_ofFn] at hfinal
    rw [toMFA_run] at hrun
    simp? at hfinal hrun
    match hrun with
    | ⟨u, hstart, hrun⟩ =>
      rw [Vector.get_ofFn] at hstart
      rw [Finite.get_find] at hstart
      exists (u, Finite.get m.State i)
  · intro ⟨(s,t), hrun, hstart, hfinal⟩
    exists Finite.find t
    constructor
    · rw [Vector.get_ofFn]
      rw [Finite.get_find]
      exact hfinal
    · rw [toMFA_run]
      simp?
      exists s
      rw [Vector.get_ofFn]
      rw [Finite.get_find]
      rw [Finite.get_find]
      constructor
      · exact hstart
      · exact hrun

end NFA
