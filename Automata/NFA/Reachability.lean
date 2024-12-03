import Automata.NFA.Basic
import Automata.NFA.Pumping

namespace NFA
variable (m : NFA α)

@[simp] theorem run_unappend : m.run (ys ++ xs) s t → ∃ u, m.run ys s u ∧ m.run xs u t := by
  intro happend
  induction ys generalizing s t with
  | nil =>
    rw [List.nil_append] at happend
    exists s
    constructor
    · simp only [NFA.run]; rfl
    · exact happend
  | cons y ys ih =>
    simp only [List.cons_append, run_cons] at happend
    match happend with
    | ⟨v, htrans, hrun⟩ =>
      match ih hrun with
      | ⟨w, hrunxs, hrunys⟩ =>
        exists w
        constructor
        · simp
          exists v
        · exact hrunys

@[simp] theorem run_append_eq : m.run (ys ++ xs) s t = Find.any (fun u => m.run ys s u ∧ m.run xs u t) := by
  rw [Bool.eq_iff_iff]
  simp
  constructor
  · exact m.run_unappend
  · intro
    | ⟨w, hs, ht⟩ =>
      simp only [run_append]
      exists w

def reachExact [Find α] : (d : Nat) → m.State → m.State → Bool
  | 0, s, t => Find.any fun x => m.trans x s t
  | d+1, s, t => Find.any fun u => reachExact d s u && reachExact d u t

@[simp] theorem run_of_reachExact [Find α] : m.reachExact d s t → ∃ xs, xs.length = 2 ^ d ∧ m.run xs s t := by
  intro hr
  induction d using Nat.recAux generalizing s t with
  | zero =>
    unfold reachExact at hr
    simp only [Find.any_iff_exists] at hr
    match hr with
    | ⟨x, htrans⟩ =>
      exists [x]
      constructor
      · rfl
      · simp
        exact htrans
  | succ d ih =>
    unfold reachExact at hr
    simp only [Find.any_iff_exists, Bool.and_eq_true] at hr
    match hr with
    | ⟨u, hreachsu, hreachut⟩ =>
      match ih hreachsu, ih hreachut with
      | ⟨xs, hlengthxs, hrunxs⟩, ⟨ys, hlengthys, hrunys⟩ =>
        exists xs ++ ys
        constructor
        · simp only [List.length_append, hlengthxs, hlengthys]
          simp only [Nat.pow_succ, Nat.mul_succ, Nat.mul_zero, Nat.zero_add]
        · simp
          exists u

@[simp] theorem reachExact_of_run [Find α] : m.run xs s t → xs.length = 2 ^ d → m.reachExact d s t := by
  intro hrun hxs
  induction d using Nat.recAux generalizing s t xs with
  | zero =>
    match xs with
    | [] => contradiction
    | [x] =>
      unfold reachExact
      simp only [run_cons, run_nil, exists_eq_right, Find.any_iff_exists] at hrun ⊢
      exists x
    | _::_::_ => injection hxs; contradiction
  | succ d ih =>
    unfold reachExact
    simp only [Find.any_iff_exists, Bool.and_eq_true]
    rw [←List.take_append_drop (2 ^ d) xs] at hrun
    match m.run_unappend hrun with
    | ⟨u, hrunsu, hrunut⟩ =>
      exists u
      constructor
      · apply ih hrunsu
        simp only [List.length_take, hxs, Nat.min_def, ite_eq_left_iff, Nat.not_le]
        omega
      · apply ih hrunut
        rw [List.length_drop, hxs, Nat.pow_succ, Nat.mul_succ, Nat.mul_one, Nat.add_sub_cancel]

def reach [Find α] : (d : Nat) → m.State → m.State → Bool
  | 0, s, t => t = s
  | d+1, s, t => reach d s t || Find.any (fun u => m.reachExact d s u && reach d u t)

@[simp] theorem run_of_reach [Find α] : m.reach d s t → ∃ xs, xs.length < 2 ^ d ∧ m.run xs s t := by
  intro hr
  induction d using Nat.recAux generalizing s with
  | zero =>
    unfold reach at hr
    simp only [decide_eq_true_eq] at hr
    exists []
    constructor
    · simp
    · unfold run
      simp
      rw [hr]
  | succ d ih =>
    unfold reach at hr
    simp only [Bool.or_eq_true, Find.any_iff_exists, Bool.and_eq_true] at hr
    cases hr with
    | inl il =>
      match ih il with
      | ⟨ys, hlist, hrun⟩ =>
        exists ys
        constructor
        · trans (2 ^ d)
          · exact hlist
          · rw [Nat.pow_succ, Nat.mul_succ, Nat.mul_one]
            apply Nat.lt_add_of_pos_right
            omega
        · exact hrun
    | inr ir =>
      match ir with
      | ⟨s₁, rexact, r⟩ =>
        match ih r with
        | ⟨ys, hlist, hrun⟩ =>
          match run_of_reachExact m rexact with
          | ⟨zs, hrlist, hrrun⟩ =>
            exists zs ++ ys
            constructor
            · simp only [List.length_append, hrlist]
              rw [Nat.pow_succ, Nat.mul_succ, Nat.mul_one]
              apply Nat.add_lt_add_left
              exact hlist
            · rw [run_append m]
              exists s₁

@[simp] theorem reach_of_run [Find α] : m.run xs s t → xs.length < 2 ^ d → m.reach d s t := by
  intro hrun hxs₁
  induction d using Nat.recAux generalizing s t xs with
  | zero =>
    cases xs with
    | nil =>
      unfold reach
      simp only [run_nil, decide_eq_true_eq] at hrun ⊢
      rw [hrun]
    | cons _ _ => contradiction
  | succ d ih =>
    unfold reach
    simp only [Bool.or_eq_true, Find.any_iff_exists, Bool.and_eq_true]
    if hxs₂: xs.length < 2 ^ d then
      left
      exact ih hrun hxs₂
    else
      have lxs := Nat.le_of_not_gt hxs₂
      right
      rw [←List.take_append_drop (2 ^ d) xs] at hrun
      match m.run_unappend hrun with
      | ⟨u, hrunsu, hrunut⟩ =>
        exists u
        constructor
        · apply m.reachExact_of_run hrunsu
          rw [List.length_take]
          rw [Nat.min_def]
          rw [if_pos lxs]
        · apply ih hrunut
          rw [List.length_drop]
          apply Nat.sub_lt_left_of_lt_add
          · exact lxs
          · rw [Nat.pow_succ, Nat.mul_two] at hxs₁
            exact hxs₁

@[simp] theorem reach_lg2_iff_reachable [Fin.Enum α] (s t : m.State) : m.reach m.size.lg2 s t ↔ ∃ xs, m.run xs s t := by
  constructor
  · intro h
    match m.run_of_reach h with
    | ⟨xs, _, hrun⟩ =>
      exists xs
  · intro h
    match h with
    | ⟨_, hrun⟩ =>
      match m.reachable hrun with
      | ⟨ys, hlength, hrun⟩ =>
        apply reach_of_run
        · exact hrun
        · calc ys.length
            < m.size := hlength
          _ < 2 ^ m.size.lg2 := by
            simp only [Nat.lg2]
            have hsize: (m.size ≠ 0) := by omega
            simp only [hsize, ↓reduceIte, gt_iff_lt]
            rw [←Nat.log2_lt]
            simp
            exact hsize

instance (s t : m.State) [Fin.Enum α] : Decidable (∃ xs, m.run xs s t) :=
  if h : m.reach m.size.lg2 s t then
    isTrue ((m.reach_lg2_iff_reachable s t).mp h)
  else
    isFalse fun f => h ((m.reach_lg2_iff_reachable s t).mpr f)

end NFA
