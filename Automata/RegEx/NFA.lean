import Automata.RegEx.Prelude
import Automata.NFA

namespace RegEx

/-- Regular expression language -/
inductive Language {α} : RegEx α → List α → Prop
| nil : Language nil []
| lit {x : α} {s : α → Bool} : s x → Language (lit s) [x]
| altL {a b : RegEx α} {xs : List α} : Language a xs → Language (alt a b) xs
| altR {a b : RegEx α} {xs : List α} : Language b xs → Language (alt a b) xs
| cat {a b : RegEx α} {xs ys : List α} : Language a xs → Language b ys → Language (cat a b) (xs ++ ys)
| starNil {a : RegEx α} : Language (star a) []
| starCat {a : RegEx α} {xs ys : List α} : Language a xs → Language (star a) ys → Language (star a) (xs ++ ys)

/-- Regular expresion compiler -/
def machine {α} : RegEx α → NFA α
| empty => NFA.false
| nil => NFA.eps
| lit s => NFA.lit s
| alt a b => machine a ||| machine b
| cat a b => machine a ++ machine b
| star a => (machine a).star

theorem soundness {α} {a : RegEx α} {xs : List α} (h : Language a xs) : (machine a).accept xs := by
  induction h with
  | nil => exact NFA.eps_sound rfl
  | lit h => exact NFA.lit_sound _ h
  | altL _ ih => exact NFA.alt_sound_left _ _ ih
  | altR _ ih => exact NFA.alt_sound_right _ _ ih
  | cat _ _ ih₁ ih₂ => exact NFA.cat_sound _ _ ih₁ ih₂
  | starNil => exact NFA.star_sound_nil _
  | starCat _ _ ih₁ ih₂ => exact NFA.star_sound_append _ ih₁ ih₂

theorem completeness {α} {a : RegEx α} {xs : List α} (h : (machine a).accept xs) : Language a xs :=
  match a, xs with
  | nil, zs => by
    unfold machine at h
    rw [NFA.eps_correct] at h
    split at h
    next => exact Language.nil
    next => contradiction
  | lit s, zs => by
    unfold machine at h
    rw [NFA.lit_correct] at h
    split at h
    next x => exact Language.lit h
    next => contradiction
  | alt a b, _ => by
    unfold machine at h
    cases NFA.alt_exact (machine a) (machine b) h with
    | inl hl =>
      apply Language.altL
      exact completeness hl
    | inr hr =>
      apply Language.altR
      exact completeness hr
  | cat a b, zs => by
    unfold machine at h
    match NFA.cat_exact (machine a) (machine b) h with
    | ⟨xs, ys, heq, ha, hb⟩ =>
      rw [heq]
      apply Language.cat
      · exact completeness ha
      · exact completeness hb
  | star a, zs => by
    unfold machine at h
    by_cases zs = [] with
    | isTrue hz =>
      rw [hz]
      apply Language.starNil
    | isFalse hz =>
      match NFA.star_exact (machine a) h hz with
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
    unfold machine at h
    rw [NFA.false_correct] at h
    contradiction
termination_by sizeOf a + List.length xs

theorem exact {α} (a : RegEx α) (xs : List α) : (machine a).accept xs ↔ Language a xs :=
  ⟨completeness, soundness⟩

instance {α} (a : RegEx α) (xs : List α) : Decidable (Language a xs) :=
  decidable_of_decidable_of_iff (exact a xs)

end RegEx
