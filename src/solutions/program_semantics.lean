/- Program Semantics — Hoare Logic -/

/- This file contains some basic material for the Hoare logic.

This file contains the following concepts:

* `state`: representing the state space of an imperative program (defined as `string → ℕ`)
  * `∅` is the empty state; mapping every variable to `0`
  * `s.update n v` or `s & n ::= v`: replace the name `n` in the state `s` by value `v`
  * `s n` variable `n` of state `s`

* `program` syntax for WHILE programs over `state` as state space.
  Instead of over an arbitrary state space `σ` we
  are now fixed on `state`; and also `assign` only allows changing one variable.

* `(p, s) ⟹ t`: big-step semantics over `program`

It is all under the `hoare_logic` namespace. -/

meta def tactic.dec_trivial := `[exact dec_trivial]

@[simp] lemma not_not_iff (p : Prop) [decidable p] : ¬ (¬ p) ↔ p :=
by by_cases p; simp [h]

@[simp] lemma and_imp2 (p q r : Prop) : ((p ∧ q) → r) ↔ (p → q → r) :=
iff.intro
  (assume h hp hq, h ⟨hp, hq⟩)
  (assume h ⟨hp, hq⟩, h hp hq)

namespace hoare_logic

/- `state` to represent state spaces -/

-- "state" is a mapping from string to N
def state := string → ℕ

def state.update (name : string) (val : ℕ) (s : state) : state :=
λn, if n = name then val else s n

notation s ` & ` n ` ::= ` v := state.update n v s

namespace state

instance : has_emptyc state := ⟨λ_, 0⟩

@[simp] lemma update_apply (name : string) (val : ℕ) (s : state) :
  (s & name ::= val) name = val :=
if_pos rfl

@[simp] lemma update_apply_ne (name name' : string) (val : ℕ) (s : state)
  (h : name' ≠ name . tactic.dec_trivial):
  (s & name ::= val) name' = s name' :=
if_neg h

@[simp] lemma update_override (name : string) (val₁ val₂ : ℕ) (s : state) :
  (s & name ::= val₂ & name ::= val₁) = (s & name ::= val₁) :=
by funext name'; by_cases name' = name; simp [h]

@[simp] lemma update_swap
  (name₁ name₂ : string) (val₁ val₂ : ℕ) (s : state) (h : name₁ ≠ name₂ . tactic.dec_trivial):
  (s & name₂ ::= val₂ & name₁ ::= val₁) = (s & name₁ ::= val₁ & name₂ ::= val₂) :=
by funext name'; by_cases h₁ : name' = name₁; by_cases h₂ : name' = name₂; simp * at *

end state

example (s : state) : (s & "a" ::= 0 & "a" ::= 2) = (s & "a" ::= 2) :=
by simp

example (s : state) : (s & "a" ::= 0 & "b" ::= 2) = (s & "b" ::= 2 & "a" ::= 0) :=
by simp

/- A WHILE programming language -/
-- "program" is an inductive type
-- it defines the generation rules of building a program

inductive program : Type
| skip {} : program
| assign  : string → (state → ℕ) → program
| seq     : program → program → program
| ite     : (state → Prop) → program → program → program
| while   : (state → Prop) → program → program

infixr ` ;; `:90 := program.seq

open program

/- We use the **big step** semantics -/
-- big_step is used in a prop about a program, a state and another state 
-- "big_step (p, s1) s2" means that applying p on s1 outputs s2, and this prop could be built from one of the following rules.

inductive big_step : (program × state) → state → Prop
| skip {s} :
  big_step (skip, s) s
| assign {n f s} :
  big_step (assign n f, s) (s.update n (f s))
| seq {p₁ p₂ s u} (t) (h₁ : big_step (p₁, s) t) (h₂ : big_step (p₂, t) u) :
  big_step (seq p₁ p₂, s) u
| ite_true {c : state → Prop} {p₁ p₀ s t} (hs : c s) (h : big_step (p₁, s) t) :
  big_step (ite c p₁ p₀, s) t
| ite_false {c : state → Prop} {p₁ p₀ s t} (hs : ¬ c s) (h : big_step (p₀, s) t) :
  big_step (ite c p₁ p₀, s) t
| while_true {c : state → Prop} {p s u} (t) (hs : c s) (hp : big_step (p, s) t)
  (hw : big_step (while c p, t) u) :
  big_step (while c p, s) u
| while_false {c : state → Prop} {p s} (hs : ¬ c s) : big_step (while c p, s) s

infix ` ⟹ `:110 := big_step

end hoare_logic
