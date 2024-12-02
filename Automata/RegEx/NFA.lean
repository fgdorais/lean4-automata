import Automata.RegEx.Basic
import Automata.NFA

namespace RegEx

/-- Regular expression language -/
inductive Language : RegEx α → List α → Prop
  | nil : Language nil []
  | lit {x : α} {s : α → Bool} : s x → Language (lit s) [x]
  | altL {a b : RegEx α} {xs : List α} : Language a xs → Language (alt a b) xs
  | altR {a b : RegEx α} {xs : List α} : Language b xs → Language (alt a b) xs
  | cat {a b : RegEx α} {xs ys : List α} : Language a xs → Language b ys → Language (cat a b) (xs ++ ys)
  | starNil {a : RegEx α} : Language (star a) []
  | starCat {a : RegEx α} {xs ys : List α} : Language a xs → Language (star a) ys → Language (star a) (xs ++ ys)

/-- Regular expresion compiler -/
def compile : RegEx α → NFA α
  | empty => NFA.false
  | nil => NFA.eps
  | lit s => NFA.lit s
  | alt a b => compile a ||| compile b
  | cat a b => compile a ++ compile b
  | star a => (compile a).star

theorem soundness (h : Language a xs) : (compile a).accept xs := by
  induction h with
  | nil => exact NFA.eps_sound rfl
  | lit h => exact NFA.lit_sound _ h
  | altL _ ih => exact NFA.alt_sound_left ih
  | altR _ ih => exact NFA.alt_sound_right  ih
  | cat _ _ ih₁ ih₂ => exact NFA.cat_sound ih₁ ih₂
  | starNil => exact NFA.star_sound_nil _
  | starCat _ _ ih₁ ih₂ => exact NFA.star_sound_append _ ih₁ ih₂

theorem completeness (h : (compile a).accept xs) : Language a xs :=
  match a, xs with
  | nil, zs => by
    simp only [compile] at h
    rw [NFA.eps_correct] at h
    split at h
    next => exact Language.nil
    next => contradiction
  | lit s, zs => by
    simp only [compile] at h
    rw [NFA.lit_correct] at h
    split at h
    next x => exact Language.lit h
    next => contradiction
  | alt a b, _ => by
    simp only [compile] at h
    cases NFA.alt_exact h with
    | inl hl =>
      apply Language.altL
      exact completeness hl
    | inr hr =>
      apply Language.altR
      exact completeness hr
  | cat a b, zs => by
    simp only [compile] at h
    match NFA.cat_exact h with
    | ⟨xs, ys, heq, ha, hb⟩ =>
      rw [heq]
      apply Language.cat
      · exact completeness ha
      · exact completeness hb
  | star a, zs => by
    simp only [compile] at h
    if hz: zs = [] then
      rw [hz]
      apply Language.starNil
    else
      match NFA.star_exact (compile a) h hz with
      | ⟨xs, ys, hxs, heq, hx, hy⟩ =>
        have : 1 ≤ xs.length := by
          cases xs with
          | nil => contradiction
          | cons _ _ =>
            rw [List.length_cons]
            apply Nat.succ_le_succ
            exact Nat.zero_le ..
        rw [heq]
        apply Language.starCat
        · exact completeness hx
        · have : 1 + sizeOf a + ys.length < 1 + sizeOf a + zs.length := by
            rw [heq, List.length_append]
            apply Nat.add_lt_add_left
            apply Nat.lt_add_of_pos_left
            assumption
          exact completeness hy
  | empty, _ => by
    simp only [compile] at h
    rw [NFA.false_correct] at h
    contradiction
termination_by sizeOf a + List.length xs

theorem exact (xs : List α) : (compile a).accept xs ↔ Language a xs :=
  ⟨completeness, soundness⟩

instance (xs : List α) : Decidable (Language a xs) :=
  decidable_of_decidable_of_iff (exact xs)

end RegEx
