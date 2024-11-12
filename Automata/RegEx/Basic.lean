
/-- Regular expression data type -/
inductive RegEx (α : Type _) : Type _
| empty : RegEx α
| nil : RegEx α
| lit : (α → Bool) → RegEx α
| alt : RegEx α → RegEx α → RegEx α
| cat : RegEx α → RegEx α → RegEx α
| star : RegEx α → RegEx α
deriving Inhabited

def RegEx.toString : RegEx α → String
| empty => "()"
| nil => "ε"
| lit _ => "[lit]"
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
instance : ToString (RegEx α) := ⟨RegEx.toString⟩

/- Regular expression syntax category -/
declare_syntax_cat regex
syntax "." : regex
syntax regex:41 "|" regex:40 : regex
syntax regex regex:arg : regex
syntax regex:max "*" : regex
syntax "(" regex ")" : regex
syntax "[" term,* "]" : regex
syntax "{" term "}" : regex

/- Regular expression syntax parser -/
syntax "toRegEx%" regex : term
macro_rules
| `(toRegEx% .) => `(RegEx.lit fun _ => true)
| `(toRegEx% $a | $b) => `(RegEx.alt (toRegEx% $a) (toRegEx% $b))
| `(toRegEx% $a $b) => `(RegEx.cat (toRegEx% $a) (toRegEx% $b))
| `(toRegEx% $a *) => `(RegEx.star (toRegEx% $a))
| `(toRegEx% ( $a )) => `(toRegEx% $a)
| `(toRegEx% [ $t,* ]) => `(RegEx.lit fun x => x ∈ [$t,*])
| `(toRegEx% { $t }) => `(RegEx.lit $t)
