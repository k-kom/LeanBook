-- https://lean-lang.org/theorem_proving_in_lean4/Introduction/#about-lean
-- Lean is based on a version of dependent type theory known as the Calculus of Constructions,
-- with a countable hierarchy of non-cumulative universes and inductive types.
-- By the end of this chapter, you will understand much of what this means.

-- define some constants

def m : Nat := 1
def n : Nat := 0
def b1 : Bool := true
def b2 : Bool := false

/- #check reports type
  auxiliary commands usually start with "#" -/
#check m
#check n
#check n+0
#check m*(n+9)
#check b1&&b2
#check b1||b2
#check true

#eval 5*4
#eval m+2
#eval b1&&b2

#eval 2+2.1
-- #eval m+2.1

def p : Prop := True
def q : Prop := False
#check p∧q

/- if a and b are types, a→b dentoes the type of functions
  from a to b, and a×b denotes tye type of pairs (like <a,b>) -/

#check Nat → Nat
#check Nat × Nat
#check Prod Nat Nat -- cartesian product

#check Nat.succ
#eval Nat.succ (Nat.succ 0)

#check (0, 1.0, true)
#check Nat.add
#eval Nat.add 2 2
#check Nat.add 3
/- partial application -/
#eval (Nat.add 3) 3

#check (5,9).1
#eval (5,9).1 == 9
#eval (5,6).fst == (2,5).snd

#check let t:=(5,9);
t.1
#eval let t:=(5,9); Nat.add t.fst t.snd

/- snd returns `rest` (or `tail`) -/
#eval (5,4,3).snd == (4, 3)

/- → is right associative but IDK how do I check this -/
-- example (f: Nat → Nat → Nat) (g: Nat → (Nat → Nat)): f = g := by rfl

/- 2.2 Types as objects -/
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check F α
#check G α β
#check G α Nat

#check Prod α β
#check Nat × Nat

/- List α is a type -/
#check List α
#check List β

#check Type
#check Type 0
-- #check Type 33
/- you can't do this -/
-- #check Type (Type 1)

-- Some operations, however, need to be polymorphic over type universes.
#check List
#check Prod

universe u
def H (α : Type u) : Type u := Prod α α
-- {u} is universe parameter
#check H
#check H Nat
-- explicitly specifying universe parameters
def I.{u1} (α : Type u1) : Type u1 := Prod α α

/- 2.3. Function Abstraction and Evaluation -/
#check fun (x : Nat) => x + 5
#check λ (x:Nat) => x+5
#eval (λ x:Nat => x+5) 10
#check (λ x:Nat => x+5) 20
#eval let f := λ (x : Nat) => x + 5; f 2

#check λ x : Nat => λ y : Bool => if not y then x + 1 else x+2
/- type inference. Lean knows x is Nat and y is Bool -/
#check λ x y => if !y then x+1 else x+2
/- curried -/
#check (λ x y => if !y then x+1 else x+2.8) 2

def myf1 (n:Nat): String := toString n
def myf2 (s:String) : Bool := s.length > 0

#check λx => myf2 (myf1 x)
#check λ (g : String → Bool) (f : Nat → String) (x : Nat)
=> g (f x)

#check λ (α β γ : Type) (g : β → γ) (f : α → β) (x : α)
=> g (f x)

/- general form of a lambda expression is fun (x:α)=>t
  where the variable x is a "bound variable" -/

-- is eval used in production code?

-- 2.4. Definitions
-- _def_ is one way of declaring new named objects
def double (x:Nat) : Nat := x + x
#eval double 3

def double2 : Nat → Nat := fun x => x + x
def double3 := fun (x:Nat) => x+x
#check double2
#check double3

def pi := 3.141502654
/- linter is furious at not using y -/
def add (x y : Nat) := x+y
#eval add 3 2
#eval add (double 3) (add 3 2)

def greater (x y : Nat) :=
  if x > y then x
  else y

#eval greater 3 3

def doTwice (f: Nat → Nat) (x : Nat) : Nat :=
  f (f x)
#eval doTwice double 3

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
def square := λ(x:Nat) => x*x
#eval compose Nat Nat Nat double square 3

-- 2.5. Local Definitions
#check let y := 2 + 2; y * y

def twice_double (x : Nat) : Nat := let y:=x+x; y*y
#eval twice_double 2

#eval let y:=2+2; let z:=y+y; z*z

def foo := let a := Nat; fun x : a => x + 2
/-
-- failed to check
def bar := (fun a => fun x : a => x+2) Nat
 -/

-- 2.6. Variable and Sections
/- variable command -/
variable (α β γ : Type)
variable (g : β → γ) (f: α → β) (h: α → α)

def compose2 (x:α):= g (f x)
def doTwice2 (x:α):= h (h x)
def doThrice (x:α):= h (h (h x))

#print compose2

/- scope variables with `section` -/
section useful
  variable (α β γ : Type)
  variable (g :β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def my_compose := g (f x)
  def my_doTwice := h (h x)
  def my_doThrice := h (h (h x))
end useful

-- 2.7. Namespaces
namespace Foo
  def a : Nat := 5
  def ff (x : Nat) : Nat := x + 7

  def ffa : Nat := ff a
  def ffffa : Nat := ff (ff a)

  #check a
  #check ff
  #check ffa
  #check ffffa
  #check Foo.ffffa

  /- can be nested -/
  namespace Bar
    def bfa : Nat := ff (ff a)
    def a : Nat := 9

    def bb : Nat := Foo.a + a
  end Bar
end Foo

/- reopen and extend -/
namespace Foo
  def b : Nat := 5
  def c : Nat := a+b
end Foo

#check Foo.a
#check Foo.Bar.bfa
#check Foo.b
#eval Foo.Bar.bb

/- can i close this? -/
open Foo
#check a

#check List.nil
#check List.cons
#check List.map

/- i don't like this. need alias at least -/
/- open List
#check nil
 -/
-- 2.8. What makes dependent type theory dependent?
#check Vector
#check Vector Bool 3
#check List Bool

def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat

#check @List.cons
#check @List.length

/- IDK what's going on -/
/- sigma type = dependant products
   - β take a value of α and returns a type v2
   - and you can create a product of ⟨α, β a⟩ it's called sigma
   - but i can't understand that
    - dependent Cartesian product types (a : α) × β a generalize the Cartesian product α × β
   - is this useful?-/
universe u2 v2
def df (α : Type u2) (β : α → Type v2) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩
def dg (α : Type u2) (β : α → Type v2) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

def dh1 (x : Nat) : Nat :=
  (df Type (fun α => α) Nat x).2
  --
def dh2 (x : Nat) : Nat :=
  (dg Type (fun α => α) Nat x).2

#eval dh1 5
#eval dh2 5
#check (df Type (fun α => α) Nat 4).1

-- 2.9. Implicit Arguments
#eval List.cons 0 List.nil
#eval List.cons 9 []
#check List.nil

def Lst (α : Type u) : Type u := List α
/- implicit argument is defined by {} -/
def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil {α : Type u} : Lst α := List.nil
def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

#check Lst.cons 0 Lst.nil
#eval let as := Lst.nil; let bs := Lst.cons 5 Lst.nil
  Lst.append as bs

def ident {α : Type u} (x : α) := x
#check ident
#check (ident)

#eval (List.nil : List Nat)
#check (List.nil : List Nat)

#check (2 : Float)

#check id
#check @id
#check @id Nat

#check id 3
#check id Nat
#check @id Nat 3
-- #check id Nat 3 -- you can't
#eval id 3
-- #eval id Nat -- you can't
#check List Nat
