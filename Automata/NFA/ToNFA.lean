import Automata.NFA.Basic
import Automata.NFA.Matrix

namespace NFA.Matrix
variable (m : Matrix α)
open NFA

abbrev toNFA : NFA α where
  State := Fin m.size
  start i := m.start[i]
  final i := m.final[i]
  trans x i j := (m.trans x)[j][i]

theorem toNFA_run {start : BitVec m.size} :
  (Find.any fun s => start[s] && m.toNFA.run xs s t) = (m.run xs start)[t] := by
  simp only [Fin.getElem_fin]
  induction xs generalizing start t with
  | nil =>
    rw [Bool.eq_iff_iff]
    constructor
    · simp only [Find.any_iff_exists, Bool.and_eq_true, NFA.run_nil, exists_eq_right]
      rw[Matrix.run_nil]
      intro
      assumption
    · intro hrun
      rw [Matrix.run_nil] at hrun
      simp only [Find.any_iff_exists, Bool.and_eq_true, NFA.run_nil, exists_eq_right]
      exact hrun
  | cons x xs ih =>
    rw [Bool.eq_iff_iff]
    simp only [Find.any_iff_exists, Bool.and_eq_true, NFA.run_cons, Fin.getElem_fin]
    constructor
    · intro ⟨s, hstart, hrun⟩
      match hrun with
      | ⟨u, htrans, hrun⟩ =>
        rw [Matrix.run_cons]
        rw [←ih]
        simp only [Find.any_iff_exists, Bool.and_eq_true]
        exists u
        constructor
        · rw [BitMat.combo]
          simp only [Fin.getElem_fin, BitVec.ofNat_eq_ofNat, BitMat.combo]
          done
        · exact hrun
    · intro hrun
      rw [Matrix.run_cons] at hrun
      rw [←ih] at hrun
      simp only [Find.any_iff_exists, Bool.and_eq_true] at hrun
      match hrun with
      | ⟨i, htrans, hrun⟩ =>
        rw [BitMat.combo] at htrans
        simp at htrans
        match htrans with
        | ⟨j, htrans, hstart⟩ =>
          exists j
          constructor
          · exact hstart
          · rw [NFA.run_cons]
            exists i

theorem toNFA_correct : m.toNFA.accept xs = m.accept xs := by
  simp [NFA.accept, Matrix.accept]
  rw [Bool.eq_iff_iff]
  simp only [Find.any_iff_exists, Bool.and_eq_true, Prod.exists]
  constructor
  · intro ⟨s, t, hrun, hstart, hfinal⟩
    done
  · intro ⟨t, hfinal, hrun⟩
    rw [←toNFA_run] at hrun
    simp at hrun
    match hrun with
    | ⟨s, hstart, hrun⟩ =>
      exists (s,t)

end NFA.Matrix
