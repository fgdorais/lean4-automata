import Automata.NFA.Basic
import Automata.Path

namespace NFA
variable (m : NFA α)
open Path

inductive Trace : {s t : m.State} → List α → Path s t → Prop
  | protected nil {t} : Trace [] (nil t)
  | protected cons {s t u} {p : Path u t} {x xs} : m.trans x s u → Trace xs p → Trace (x :: xs) (Path.cons s p)

protected theorem Trace.append : {s t u : m.State} → {p : Path u t} → {q : Path s u} → {xs ys : List α} → Trace m xs q → Trace m ys p → Trace m (xs ++ ys) (q ++ p)
  | _, _, _, _, nil _, _, _, Trace.nil, hy => hy
  | _, _, _, _, cons _ _, _::_, _, Trace.cons ht hx, hy => Trace.cons ht (Trace.append hx hy)

@[simp] theorem Trace.length_eq_length : {s t : m.State} → {xs : List α} → {p : Path s t} → Trace m xs p → xs.length = p.length
    | _, _, [], nil _, .nil => rfl
    | _, _, _ :: _, cons _ _, .cons _ htail => by
      simp only [List.length_cons]
      rw [Path.length_cons]
      rw [length_eq_length]
      exact htail

@[simp] theorem run_of_trace {p : Path s t} : Trace m xs p → m.run xs s t := by
  intro h
  induction xs generalizing s t with
  | nil =>
    simp only [run_nil]
    cases h
    rfl
  | cons x xs ih =>
    match h with
    | .cons (u := u) htrans htrace =>
    simp only [run_cons]
    exists u
    constructor
    · exact htrans
    · exact ih htrace

@[simp] theorem trace_of_run : m.run xs s t → ∃ (p : Path s t), Trace m xs p := by
  intro hrun
  induction xs generalizing s t with
  | nil =>
    simp only [run_nil] at hrun
    cases hrun
    exists nil s
    exact Trace.nil
  | cons x xs ih =>
    simp only [run_cons] at hrun
    match hrun with
    | ⟨u, htrans, hrun⟩ =>
      match ih hrun with
      | ⟨p, htrace⟩ =>
        exists cons s p
        exact Trace.cons htrans htrace

@[simp] theorem trace_drop {p : Path s t} (n : Nat) : Trace m xs p → Trace m  (xs.drop n) (p.drop n) := by
  intro htrace
  induction htrace generalizing n with
  | nil =>
    match n with
    | 0 =>
      simp only [List.drop_nil]
      rw [Path.drop_nil_zero]
      apply Trace.nil
    | n+1 =>
      simp only [List.drop_nil]
      rw [Path.drop_nil_succ]
      apply Trace.nil
  | cons htrans htrace ih =>
    match n with
    | 0 =>
      simp only [List.drop_zero]
      rw [Path.drop_zero]
      apply Trace.cons
      · rw [val_cons_zero]
        exact htrans
      · exact htrace
    | n+1 =>
      simp only [List.drop_succ_cons]
      rw [Path.drop_cons_succ]
      exact ih n

@[simp] theorem trace_take {p : Path s t} (n : Nat) : Trace m xs p → Trace m  (xs.take n) (p.take n) := by
  intro htrace
  induction htrace generalizing n with
  | nil =>
    match n with
    | 0 =>
      simp only [List.take_nil]
      rw [Path.take_nil_zero]
      apply Trace.nil
    | n+1 =>
    simp only [List.take_nil]
    rw [Path.take_nil_succ]
    apply Trace.nil
  | cons htrans _ ih =>
    match n with
    | 0 =>
      simp only [List.take_zero]
      rw [Path.take_cons_zero]
      apply Trace.nil
    | n+1 =>
      simp only [List.take_succ_cons]
      rw [Path.take_cons_succ]
      apply Trace.cons
      rw [htrans]
      exact ih n

end NFA
