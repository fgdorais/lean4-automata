import Automata.NFA.Basic

namespace NFA
variable {α} (m : NFA α)

theorem run_unappend {s t : m.State} {xs ys : List α} : m.run (ys ++ xs) s t → ∃ u, m.run ys s u ∧ m.run xs u t := by
  intro happend
  induction ys generalizing s t with
  | nil =>
    rw [List.nil_append] at happend
    exists s
    constr
    · simp only [NFA.run]; rfl
    · exact happend
  | cons y ys ih =>
    rw [List.cons_append] at happend
    unfold run at happend
    dec_lift at happend
    match happend with
    | ⟨v, htrans, hrun⟩ =>
      match ih hrun with
      | ⟨w, hrunxs, hrunys⟩ =>
        exists w
        constr
        · unfold run
          dec_lift
          exists v
        · exact hrunys

theorem run_append_eq {s t : m.State} (ys xs : List α) : m.run (ys ++ xs) s t = Finite.any (λ u => m.run ys s u ∧ m.run xs u t) := by
  dec_lift
  constr
  · exact m.run_unappend
  · intro
    | ⟨w, hs, ht⟩ =>
      rw [run_append]
      exists w

def reachExact [Finite α] : (d : Nat) → m.State → m.State → Bool
| 0, s, t => Finite.any fun x => m.trans x s t
| d+1, s, t => Finite.any fun u => reachExact d s u && reachExact d u t

theorem run_of_reachExact [Finite α] (d : Nat) {s t : m.State} : m.reachExact d s t → ∃ xs, xs.length = 2 ^ d ∧ m.run xs s t := by
  intro hr
  induction d using Nat.recAux generalizing s t with
  | zero =>
    unfold reachExact at hr
    dec_lift at hr
    match hr with
    | ⟨x, htrans⟩ =>
      exists [x]
      constr
      · rfl
      · simp only [NFA.run]
        dec_lift
        exists t
  | succ d ih =>
    unfold reachExact at hr
    dec_lift at hr
    match hr with
    | ⟨u, hreachsu, hreachut⟩ =>
      match ih hreachsu, ih hreachut with
      | ⟨xs, hlengthxs, hrunxs⟩, ⟨ys, hlengthys, hrunys⟩ =>
        exists xs ++ ys
        constr
        · rw [List.length_append]
          rw [hlengthxs]
          rw [hlengthys]
          rw [Nat.pow_succ, Nat.mul_succ, Nat.mul_one]
        · rw [run_append]
          exists u

theorem reachExact_of_run [Finite α] (d : Nat) {s t : m.State} {xs : List α} : m.run xs s t → xs.length = 2 ^ d → m.reachExact d s t := by
  intro hrun hxs
  induction d using Nat.recAux generalizing s t xs with
  | zero =>
    match xs with
    | [] => contradiction
    | [x] =>
      unfold reachExact
      simp only [NFA.run] at hrun
      dec_lift at hrun ⊢
      match hrun with
      | ⟨_, htrans, rfl⟩ => exists x
    | _::_::_ => injection hxs; contradiction
  | succ d ih =>
    unfold reachExact
    dec_lift
    rw [←List.take_append_drop (2 ^ d) xs] at hrun
    match m.run_unappend hrun with
    | ⟨u,hrunsu,hrunut⟩ =>
      exists u
      constr
      · apply ih hrunsu
        rw [List.length_take, Nat.min_def, hxs]
        rw [if_pos (Nat.pow_le_pow_of_le_right (Nat.zero_lt _) (Nat.le_add_right _ 1))]
      · apply ih hrunut
        rw [List.length_drop, hxs, Nat.pow_succ, Nat.mul_succ, Nat.mul_one, Nat.add_sub_cancel]

def reach [Finite α] : (d : Nat) → m.State → m.State → Bool
| 0, s, t => t = s
| d+1, s, t => reach d s t || Finite.any (λ u => m.reachExact d s u && reach d u t)

theorem run_of_reach [Finite α] {d : Nat} {s t : m.State} : m.reach d s t → ∃ xs, xs.length < 2 ^ d ∧ m.run xs s t := by
  intro hr
  induction d using Nat.recAux generalizing s with
  | zero =>
    unfold reach at hr
    dec_lift at hr
    exists []
    constr
    · exact Nat.zero_lt ..
    · unfold run
      dec_lift
      rw [hr]
  | succ d ih =>
    unfold reach at hr
    dec_lift at hr
    cases hr with
    | inl il =>
      match ih il with
      | ⟨ys, hlist, hrun⟩ =>
        exists ys
        constr
        · transitivity (2 ^ d)
          · exact hlist
          · rw [Nat.pow_succ, Nat.mul_succ, Nat.mul_one]
            apply Nat.lt_add_of_pos_right
            exact Nat.zero_lt ..
        · exact hrun
    | inr ir =>
      match ir with
      | ⟨s₁, rexact, r⟩ =>
        match ih r with
        | ⟨ys, hlist, hrun⟩ =>
          match run_of_reachExact m d rexact with
          |⟨zs, hrlist, hrrun⟩ =>
            exists zs++ys
            constr
            · rw [List.length_append]
              rw [hrlist]
              rw [Nat.pow_succ]
              rw [Nat.mul_succ]
              rw [Nat.mul_one]
              apply Nat.add_lt_add_left
              exact hlist
            · rw [run_append m]
              exists s₁

theorem reach_of_run [Finite α] {d : Nat} {s t : m.State} {xs : List α} : m.run xs s t → xs.length < 2 ^ d → m.reach d s t := by
  intro hrun hxs
  induction d using Nat.recAux generalizing s t xs with
  | zero =>
    cases xs with
    | nil =>
      unfold run at hrun
      unfold reach
      dec_lift at hrun ⊢
      rw [hrun]
    | cons _ _ => contradiction
  | succ d ih =>
    unfold reach
    dec_lift
    by_cases xs.length < 2 ^ d with
    | isTrue hxs =>
      left
      exact ih hrun hxs
    | isFalse lxs =>
      have lxs := Nat.le_of_not_gt lxs
      right
      rw [←List.take_append_drop (2 ^ d) xs] at hrun
      match m.run_unappend hrun with
      | ⟨u,hrunsu,hrunut⟩ =>
        exists u
        constr
        · apply m.reachExact_of_run d hrunsu
          rw [List.length_take]
          rw [Nat.min_def]
          rw [if_pos lxs]
        · apply ih hrunut
          rw [List.length_drop]
          apply Nat.sub_lt_left_of_lt_add
          · exact lxs
          · rw [Nat.pow_succ, Nat.mul_two] at hxs
            exact hxs

theorem reach_lg2_iff_reachable [Finite α] (s t : m.State) : m.reach m.size.lg2 s t ↔ ∃ xs, m.run xs s t := by
constr
· intro h
  match m.run_of_reach h with
  | ⟨xs,_,hrun⟩ =>
    exists xs
· intro h
  match h with
  | ⟨_,hrun⟩ =>
    match m.reachable hrun with
    | ⟨ys,hlength,hrun⟩ =>
      apply reach_of_run
      · exact hrun
      · calc ys.length
          < m.size := hlength
        _ < 2 ^ m.size.lg2 := Nat.lt_pow_lg2_self ..

instance (s t : m.State) [Finite α] : Decidable (∃ xs, m.run xs s t) :=
  if h : m.reach m.size.lg2 s t then
    isTrue ((m.reach_lg2_iff_reachable s t).mp h)
  else
    isFalse fun f => h ((m.reach_lg2_iff_reachable s t).mpr f)

end NFA
