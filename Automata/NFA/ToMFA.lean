import Automata.NFA.Basic
import Automata.NFA.Matrix

namespace NFA
variable (m : NFA α)
open NFA.Matrix

abbrev toMatrix : Matrix α where
  size := m.size
  start := BitVec.ofFnLE fun i => m.start (Fin.Enum.enum i)
  final := BitVec.ofFnLE fun i => m.final (Fin.Enum.enum i)
  trans x := BitMat.ofFn fun i j => m.trans x (Fin.Enum.enum j) (Fin.Enum.enum i)

theorem toMFA_run {start : BitVec m.toMatrix.size} :
  (m.toMatrix.run xs start)[i] = Find.any fun (t : m.State) => start[Fin.Enum.find t] && m.run xs t (Fin.Enum.enum i) := by
  induction xs generalizing start with
  | nil =>
    rw [Bool.eq_iff_iff]
    simp only [Fin.getElem_fin, Find.any_iff_exists, Bool.and_eq_true, run_nil, exists_eq_right,
      Fin.Enum.find_enum, Bool.coe_iff_coe, Matrix.run_nil]
  | cons x xs ih =>
    rw [Bool.eq_iff_iff]
    simp only [Matrix.run_cons, ih, Fin.getElem_fin, Find.any_iff_exists, Bool.and_eq_true, run_cons]
    constructor
    · intro ⟨t, hmat, hrun⟩
      exists t
      constructor
      ·
        done
      ·
        done
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
      match hrun with
      | ⟨u, htrans, hrun⟩ =>
        exists u
        constructor
        ·
          rw [Finite.get_find]
          rw [Finite.get_find]
          constructor
          · exact htrans
          · exact hstart
        · exact hrun

theorem toMFA_correct (xs : List α) : m.toMatrix.accept xs = m.accept xs := by
  rw [Bool.eq_iff_iff]
  simp only [accept_def, BitVec.dot, BitVec.ofNat_eq_ofNat, bne_iff_ne, ne_eq, accept_eq_true_iff]
  constructor
  ·
    intro ⟨i, hfinal, hrun⟩
    rw [BitVec.ofFn] at hfinal
    rw [toMFA_run] at hrun
    simp? at hfinal hrun
    match hrun with
    | ⟨u, hstart, hrun⟩ =>
      rw [Vector.get_ofFn] at hstart
      rw [Finite.get_find] at hstart
      exists (u, Finite.get m.State i)
  · intro ⟨s, t, hrun, hstart, hfinal⟩
    simp [BitVec.ofFnLE]
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
