import Automata.NFA.Basic
import Automata.NFA.Trace

namespace NFA
variable (m : NFA α)

theorem php [Fin.Enum α] (f : Nat → α) : ∃ i j, i < j ∧ j ≤ Fin.Enum.size α ∧ f i = f j := by sorry

theorem pumping (n : Nat) :
  m.run xs s t → m.run ys t t → m.run zs t u → m.run (xs ++ ys.repeat n ++ zs) s u := by
  induction n using Nat.recAux generalizing xs ys zs with
  | zero =>
    intro hx _ hz
    rw [List.repeat_zero]
    rw [List.append_nil]
    rw [m.run_append]
    exists t
  | succ n ih =>
    intro hx hy hz
    rw [List.repeat_succ]
    rw [List.append_assoc]
    rw [List.append_assoc]
    rw [← List.append_assoc]
    rw [← List.append_assoc]
    apply ih
    · rw [m.run_append]
      exists t
    · exact hy
    · exact hz

@[simp] theorem splitting [Fin.Enum  α] : ws.length ≥ m.size → m.run ws s t → ∃ (u : m.State) (xs ys zs : List α), ws = xs ++ ys ++ zs ∧ ys.length > 0 ∧ m.run xs s u ∧ m.run ys u u ∧ m.run zs u t := by
  intro hw hrun
  match m.trace_of_run hrun with
  | ⟨p, hp⟩ =>
    match php p.val with
    | ⟨i,j,hij,hjs,hval⟩ =>
      let zs := ws.drop j
      let ys := (ws.take j).drop i
      let xs := (ws.take j).take i
      let pz := p.drop j
      let py := (p.take j).drop i
      let px := (p.take j).take i
      have hz : Trace m zs pz := m.trace_drop j hp
      have hy : Trace m ys py := m.trace_drop i (m.trace_take j hp)
      have hx : Trace m xs px := m.trace_take i (m.trace_take j hp)
      have hjp : j ≤ p.length := by
        rw [←Trace.length_eq_length m hp]
        transitivity m.size
        · exact hjs
        · exact hw
      have hpij : p.val i = (p.take j).val i := by rw [Path.val_take hjp (Nat.le_of_lt hij)]
      exists p.val i, xs, ys, zs
      constructor
      · calc
        _ = ws.take j ++ zs := by rw [List.take_append_drop j]
        _ = (xs ++ ys) ++ zs := by rw [List.take_append_drop i]
      · constructor
        · have : j ≤ ws.length := Nat.le_trans hjs hw
          rw [List.length_drop]
          rw [List.length_take]
          rw [Nat.min_eq_left this]
          apply Nat.sub_pos_of_lt hij
        · constructor
          · rw [hpij]
            apply m.run_of_trace hx
          · constructor
            · transitivity (m.run ys (p.val i) (p.val j))
              · rw [hval]
              · rw [hpij]
                apply m.run_of_trace hy
            · rw [hval]
              apply m.run_of_trace hz

@[simp] theorem reachableAux [Fin.Enum α] : ws.length < n → m.run ws s t → ∃ (ws : List α), ws.length < m.size ∧ m.run ws s t := by
  intro hws hrun
  induction n generalizing ws with
  | zero => contradiction
  | succ n ih =>
    if hwslt : ws.length < m.size then
      exists ws
    else
      have hge : ws.length ≥ m.size := Nat.le_of_not_lt hwslt
      match m.splitting hge hrun with
      | ⟨u,xs,ys,zs,heq,hys,hxrun,_,hzrun⟩ =>
        have hrun : m.run (xs ++ zs) s t := by
          rw [run_append]
          exists u
        have hlt : (xs ++ zs).length < n := calc
          _ = xs.length + zs.length := by rw [List.length_append]
          _ < (xs.length + ys.length) + zs.length := by apply Nat.add_lt_add_right; apply Nat.lt_add_of_pos_right; exact hys
          _ = (xs ++ ys).length + zs.length := by rw [List.length_append]
          _ = ((xs ++ ys) ++ zs).length := by rw [List.length_append (as := xs ++ ys)]
          _ = ws.length := by rw [heq]
          _ ≤ n := by apply Nat.le_of_lt_succ hws
        apply ih hlt hrun

@[simp] theorem reachable [Fin.Enum α] : m.run ws s t → ∃ (ws : List α), ws.length < m.size ∧ m.run ws s t :=
  m.reachableAux (Nat.lt_succ_self ws.length)

end NFA
