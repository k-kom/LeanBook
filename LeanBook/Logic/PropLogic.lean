#check Prop

-- prop
#check (1 + 1 = 3: Prop)
-- function to a prop is not prop it's pred (Nat → Prop is pred? IDK)
-- I think "x is human" is pred so "39 = n + 3" (39 is equal to n+3) is also pred right?
#check (fun n => n + 3 = 39: Nat → Prop)
#check (4 + 3 = 39: Prop)

#check True
#check False

-- `trivial` is tactic
example: True := by trivial -- ⊢ True
--example: False := by trivial

-- 3.1.2 hypothesis
-- ⊢ P
example (P:Prop) (hypothesis:P): P := by exact hypothesis
-- P is prop and h is proof of P then P
-- it looks strange because P is already proved by h
example (P:Prop)(h:P): P := by assumption

-- using ⊥ to prove anything (Fermat's Last Theorem)
-- this proof fails if you omit h from local context
example (h:False) : ∀ x y z n : Nat,
  n ≥ 3 → x^n + y^n = z^n → x * y * z = 0 := by trivial

--- 3.1.3 implication →
example (P Q R:Prop) : (P → Q → R) = (P → (Q → R)) := by rfl
-- you cannot prove
--example (P Q R:Prop) : ((P=Q) = R) = (P = (Q=R)) := by rfl
--example (P Q R:Nat): (P ≤ Q) ∧ (Q≤R) → (P≤R) := by assumption

-- True is ⊤ False is ⊥
-- true and false are Booleans
#eval False → True
#eval True → False

-- apply tactic (implication)
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  -- apply h
  --apply hp
  exact h hp

-- intro tactic
example (P Q : Prop) (hq : Q) : P → Q := by
  intro hp
  -- looks like P is still open 🤔
  exact hq

#eval ¬True
#eval ¬False

-- ¬ P is = P → False (what?)
example (P : Prop) : (¬ P) = (P → False) := by rfl

example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
apply hnp
exact hp

example (P Q : Prop) (h : P → ¬ Q) : Q → ¬ P := by
-- suppose Q
-- what is hq? -> just assuming Q is true
-- but IDKW q comes first not P (from goal?)
intro hq
-- suppose P
intro hp
-- apply hp and hq to h
exact h hp hq

example (P : Prop) (hnp : ¬ P) (hp : P) : False := by contradiction

/- this is invalid. I guess intro will be applied to an assumption
() is like argument -/
-- example (P: Prop) : False := by
-- intro hnp
-- intro hp

example (P Q : Prop) (hnp : ¬ P) (hp : P) :Q := by
exfalso
contradiction

#eval True ↔ True
#eval True ↔ False

example (P Q : Prop) (h1: P→ Q) (h2: Q→ P): P↔Q := by
constructor
· apply h1
· apply h2

-- example (P: Prop) (h: P):= by
-- exact h

example (P Q : Prop) (hq : Q) : (Q→P) ↔ P := by
constructor
-- prove Q→P
--
case mp =>
  intro h
  exact h hq
-- prove P→Q
case mpr =>
  -- hp: P, hq: Q
  -- because trying to prove P→Q→P (look at the goal in infoview)
  intro hp hq
  exact hp

example (P Q :Prop) (hq : Q) : (Q→P) ↔ P := by
constructor <;> intro h
case mp =>
  exact h hq
case mpr =>
  intro hq
  exact h

example (P Q: Prop) (h: P↔Q) (hq: Q) : P := by
-- rewrite goal to ⊢ Q by P↔Q
rw [h]
-- that is exactly hq
exact hq

example (P Q: Prop) (h: P↔Q) (hp: P) :Q := by
-- rewrite goal to ⊢ P by P↔Q
rw [←h]
exact hp

example (P Q:Prop) (h: P↔Q): P=Q := by
rw [h]

example (P Q :Prop) (hp :P) (hq:Q): P∧Q := by
constructor
· exact hp
· exact hq
