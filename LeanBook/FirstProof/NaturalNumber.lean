/- my impl of the natural number  -/

#version
/- see `M-x show unicode input abbrev` shows the complete list
⊢ goal
← l
→ to
↔ iff
∧ and
∨ or
¬ not
∀ for all
∃ exists
≠ neq
≤ leq
≥ geq
⟨ <
⟩ >
⟦⟧ [[
⟧ ]]
∣ mid
∘ circ
· .
× times
⋄ diamond
∈ in
≈ ~~
∼ sim (similar?)
♥ heartsuit (what is this?)
↑ up arrow
↓ down arrow
₁ 1
₂ 2
ₛ _s (?)
⁻¹ inv
α a (and b, c, ..., z also works)
-/

-- 帰納型 inductive type
inductive MyNat where
  | zero -- a constructor
  | succ (n: MyNat) -- this is also a constructor

--#check MyNat.zero
#check MyNat.succ
-- check if applying MyNat.succ to .zero returns MyNat
#check MyNat.succ .zero
-- #check MyNat.succ .foo

-- toggle InfoView: cmd+shift+enter

def MyNat.one := MyNat.succ .zero
def MyNat.two := MyNat.succ .one

def MyNat.add (m n: MyNat) : MyNat :=
  match n with
  | .zero => m
  -- syntax error if you omit a space before (
  | .succ n => succ (add m n)

-- this Prop is true
#check MyNat.add .one .one = .two
-- this Prop is wrong
#check MyNat.add .one .one = .one

-- customize #reduce command's output
set_option pp.fieldNotation.generalized false

#reduce MyNat.add .one .one
#reduce MyNat.two

-- let's prove 1+1=2 of MyNat
-- example: proof a Prop without naming it
example: MyNat.add .one .one = .two := by
  -- rfl is _tactic_ (following `by`)
  rfl
-- https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_C/tactics/rfl.html

example (n : MyNat) : MyNat.add n .zero = n := by
  rfl
example: MyNat.add .zero .zero = .zero := by
  rfl
