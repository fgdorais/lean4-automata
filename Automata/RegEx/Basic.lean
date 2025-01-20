import Automata.NFA

/-- Regular expression data type -/
inductive RegEx (α : Type _) : Type _
  | empty : RegEx α
  | nil : RegEx α
  | lit : (α → Bool) → RegEx α
  | alt : RegEx α → RegEx α → RegEx α
  | cat : RegEx α → RegEx α → RegEx α
  | star : RegEx α → RegEx α
  deriving Inhabited

protected class RegEx.SetRepr (α : Type _) where
  toString (s : α → Bool) : String
  ofString : String → α → Bool

def RegEx.toString [RegEx.SetRepr α] : RegEx α → String
  | empty => "[]"
  | nil => ""
  | lit s => "[" ++ SetRepr.toString s ++ "]"
  | alt a b => toString a ++ " | " ++ toString b
  | cat a b =>
    match a with
    | alt _ _ => "(" ++ toString a ++ " " ++ toString b ++ ")"
    | _ => toString a ++ " " ++ toString b
  | star a =>
    match a with
    | alt _ _ => "(" ++ toString a ++ ")*"
    | cat _ _ => "(" ++ toString a ++ ")*"
    | _ => toString a ++ "*"
  instance [RegEx.SetRepr α] : ToString (RegEx α) := ⟨RegEx.toString⟩

/- Regular expression syntax category -/
declare_syntax_cat regex
syntax "." : regex
syntax regex:41 "|" regex:40 : regex
syntax regex regex:arg : regex
syntax regex:max "*" : regex
syntax "(" regex ")" : regex
syntax "[" str "]" : regex

/- Regular expression syntax parser -/
syntax "toRegEx%" regex : term
macro_rules
  | `(toRegEx% .) => `(RegEx.lit fun _ => true)
  | `(toRegEx% $a | $b) => `(RegEx.alt (toRegEx% $a) (toRegEx% $b))
  | `(toRegEx% $a $b) => `(RegEx.cat (toRegEx% $a) (toRegEx% $b))
  | `(toRegEx% $a *) => `(RegEx.star (toRegEx% $a))
  | `(toRegEx% ( $a )) => `(toRegEx% $a)
  | `(toRegEx% [ $s ]) => `(RegEx.lit (RegEx.SetRepr.ofString $s))

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

end RegEx
