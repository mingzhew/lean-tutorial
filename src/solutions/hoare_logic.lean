/- Program Semantics — Hoare Logic -/

-- loads big-step semantics `(p, s) ⟹ t` over `state` as state space

--import data.real.basic
import tactic.show_term
import tactic.tauto
import .program_semantics


namespace hoare_logic

open program

variables
  {c : state → Prop} {f : state → ℕ} {n : string}
  {p p₀ p₁ p₂ : program} {s s₀ s₁ s₂ t u : state}
  {P P' P₁ P₂ P₃ Q Q' : state → Prop}


/- Hoare triples `{* P *} p {* Q *}` for partial correctness -/

-- similar to big_step, partial_hoare is used in a Prop about a two specification P,Q and a program p,
-- partial_hoare P p Q means that if a state s has property (P s) and s becomes t after the program p, then t has property (Q t).
-- abbr partial_hoare P p Q => { P } p { Q }

def partial_hoare (P : state → Prop) (p : program) (Q : state → Prop) : Prop :=
∀s t, P s → (p, s) ⟹ t → Q t

notation `{* ` P : 1 ` *} ` p : 1 ` {* ` Q : 1 ` *}` := partial_hoare P p Q


/- Introduction rules for Hoare triples -/

namespace partial_hoare

lemma skip_intro :
  {* P *} skip {* P *} :=
begin
  intros s t hs hst,
  cases hst,
  assumption,
end

lemma assign_intro (P : state → Prop) :
  {* λs, P (s.update n (f s)) *} assign n f {* P *} :=
begin
  intros s t P hst,
  cases hst,
  assumption,
end

lemma seq_intro (h₁ : {* P₁ *} p₁ {* P₂ *}) (h₂ : {* P₂ *} p₂ {* P₃ *}) :
  {* P₁ *} p₁ ;; p₂ {* P₃ *} :=
begin
  intros s t P hst,
  cases hst,
  apply h₂ _ _ _ hst_h₂,
  apply h₁ _ _ _ hst_h₁,
  assumption,
end

lemma ite_intro (h₁ : {* λs, P s ∧ c s *} p₁ {* Q *}) (h₂ : {* λs, P s ∧ ¬ c s *} p₂ {* Q *}) :
  {* P *} ite c p₁ p₂ {* Q *} :=
begin
  intros s t hs hst,
  cases hst,
  { apply h₁ _ _ _ hst_h,
    exact ⟨hs, hst_hs⟩ },
  { apply h₂ _ _ _ hst_h,
    exact ⟨hs, hst_hs⟩ },
end

lemma while_intro (P : state → Prop) (h₁ : {* λs, P s ∧ c s *} p {* P *}) :
  {* P *} while c p {* λs, P s ∧ ¬ c s *} :=
begin
  intros s t hs,
  generalize eq : (while c p, s) = ps,
  intro hst,
  induction hst generalizing s; cases eq,
  { apply hst_ih_hw hst_t _ rfl,
    exact h₁ _ _ ⟨hs, hst_hs⟩ hst_hp },
  { exact ⟨hs, hst_hs⟩ }
end

lemma consequence (h : {* P *} p {* Q *}) (hp : ∀s, P' s → P s) (hq : ∀s, Q s → Q' s) :
  {* P' *} p {* Q' *} :=
assume s t hs hst, hq _ $ h s t (hp s hs) hst

lemma consequence_left (P' : state → Prop) (h : {* P *} p {* Q *}) (hp : ∀s, P' s → P s) :
  {* P' *} p {* Q *} :=
consequence h hp (assume s hs, hs)

lemma consequence_right (Q : state → Prop) (h : {* P *} p {* Q *}) (hq : ∀s, Q s → Q' s) :
  {* P *} p {* Q' *} :=
consequence h (assume s hs, hs) hq

/- Many of the above rules are nonlinear (i.e. their conclusions contain repeated variables). This
makes them inconvenient to apply. We combine some of the previous rules with `consequence` to derive
linear rules. -/

lemma skip_intro' (h : ∀s, P s → Q s):
  {* P *} skip {* Q *} :=
consequence skip_intro h (assume s hs, hs)

lemma assign_intro' (h : ∀s, P s → Q (s.update n (f s))):
  {* P *} assign n f {* Q *} :=
consequence (assign_intro Q) h (assume s hs, hs)

lemma seq_intro' (h₂ : {* P₂ *} p₂ {* P₃ *}) (h₁ : {* P₁ *} p₁ {* P₂ *}) :
  {* P₁ *} p₁ ;; p₂ {* P₃ *} :=
seq_intro h₁ h₂

lemma while_intro_inv (I : state → Prop)
  (h₁ : {* λs, I s ∧ c s *} p {* I *}) (hp : ∀s, P s → I s) (hq : ∀s, ¬ c s → I s → Q s) :
  {* P *} while c p {* Q *} :=
consequence (while_intro I h₁) hp (assume s ⟨hs, hnc⟩, hq s hnc hs)

end partial_hoare


/- Example: `SWAP`

Exchanges the values of variables `a` and `b`. -/

section SWAP

open partial_hoare

def SWAP : program :=
assign "t" (λs, s "a") ;;
assign "a" (λs, s "b") ;;
assign "b" (λs, s "t")


example {P Q R : Prop} (h₁ : Q → P) (h₂ : R) (h₃ : R → Q) : P ∧ R :=
by show_term { tauto }

/-
example (a b : ℕ) : a + b = b + a :=
begin
  unfold add, -- Expand the definition of addition
  change b + a = a + b, -- Change the goal to an equivalent expression
  simp [add_comm], -- Simplify the expression using commutativity of addition
  trace a, -- Print the value of `a`
  refl, -- Prove the goal by reflexivity
end
-/

lemma SWAP_correct (x y : ℕ) :
  {* λs, s "a" = x ∧ s "b" = y *} SWAP {* λs, s "a" = y ∧ s "b" = x *} :=
begin
  have h1 : ∀ (s : state), s "a" = x ∧ s "b" = y → (s & "t" ::= s "a" & "a" ::= (s & "t" ::= s "a") "b" & "b" ::= (s & "t" ::= s "a" & "a" ::= (s & "t" ::= s "a") "b") "t") "a" = y ∧ (s & "t" ::= s "a" & "a" ::= (s & "t" ::= s "a") "b" & "b" ::= (s & "t" ::= s "a" & "a" ::= (s & "t" ::= s "a") "b") "t") "b" = x,
  { simp {contextual := tt} , },


  apply seq_intro',

  /-
  {* ?m_1 *} assign "a" (λ (s : state), s "b") ;; assign "b" (λ (s : state), s "t") {* (λ (s : state), s "a" = y ∧ s "b" = x) *}
  {* (λ (s : state), s "a" = x ∧ s "b" = y) *} assign "t" (λ (s : state), s "a") {* ?m_1 *}
  -/
  apply seq_intro',
  /-
  {* ?m_1 *} assign "b" (λ (s : state), s "t") {* (λ (s : state), s "a" = y ∧ s "b" = x) *}
  {* ?m_1 *} assign "a" (λ (s : state), s "b") {* ?m_2 *}
  {* (λ (s : state), s "a" = x ∧ s "b" = y) *} assign "t" (λ (s : state), s "a") {* ?m_1 *}
  -/
  apply assign_intro,
  /-
  
  -/


  apply assign_intro,
  apply assign_intro',
  /- The remaining goal looks horrible. But `simp` can simplify it dramatically, and with contextual
  rewriting (i.e. using assumptions in the goal as rewrite rules), it can solve it. -/

  simp {contextual := tt},
end

end SWAP


/- Example: `ADD`

Computes `m + n`, leaving the result in `n`, using only these primitive operations: `n + 1`,
`n - 1`, and `n ≠ 0`. -/

section ADD

open partial_hoare

def ADD : program :=
while (λs, s "n" ≠ 0)
( assign "n" (λs, s "n" - 1) ;;
  assign "m" (λs, s "m" + 1) )

def TEST : program :=
while (λs, s "y" < 10)
( assign "x" (λs, s "x" + s "y") ;;
  assign "y" (λs, s "y" + 1))

def TEST2 : program := 
while (λs, s "i" ≤ s "x")
( assign "i" (λs, s "i" + 1) ;; 
  assign "j" (λs, s "j" + s "y") )

#check nat.succ_eq_add_one
#check nat.add_assoc
#print ADD
#print TEST2

lemma ADD_correct (n m : ℕ) :
  {* λs, s "n" = n ∧ s "m" = m *} ADD {* λs, s "m" = n + m *} :=
begin
  -- `refine` is like `exact`, but it lets us specify holes to be filled later
  refine while_intro_inv (λs, s "n" + s "m" = n + m) _ _ _,
  apply seq_intro',
  apply assign_intro,
  apply assign_intro',
  { simp,
    -- puhh this looks much better: `simp` removed all `update`s
    intros s hnm hn0,
    rw ←hnm,
    -- subtracting on `ℕ` is annoying
    cases s "n",
    { contradiction },
    { rw [nat.succ_eq_add_one], simp, 
      rw [nat.add_assoc], 
      have h1 : s "m" + 1 = 1 + s "m",
      { rw nat.add_comm},
      rw h1,
      -- simp [nat.succ_eq_add_one] 
      } },
  { simp {contextual := tt} },
  { simp [not_not_iff, nat.zero_add] {contextual := tt} }
end

end ADD


/- Annotated while loop -/

def program.while_inv (I : state → Prop) (c : state → Prop) (p : program) : program :=
while c p

open program -- makes `program.while_inv` available as `while_inv`

namespace partial_hoare

/- `while_inv` rules use the invariant annotation -/

lemma while_inv_intro {I : state → Prop}
  (h₁ : {* λs, I s ∧ c s *} p {* I *}) (hq : ∀s, ¬ c s → I s → Q s) :
  {* I *} while_inv I c p {* Q *} :=
while_intro_inv I h₁ (assume s hs, hs) hq

lemma while_inv_intro' {I : state → Prop}
  (h₁ : {* λs, I s ∧ c s *} p {* I *}) (hp : ∀s, P s → I s) (hq : ∀s, ¬ c s → I s → Q s) :
  {* P *} while_inv I c p {* Q *} :=
while_intro_inv I h₁ hp hq

end partial_hoare

end hoare_logic

namespace tactic.interactive

open hoare_logic.partial_hoare hoare_logic tactic

meta def is_meta {elab : bool} : expr elab → bool
| (expr.mvar _ _ _) := tt
| _                 := ff


/- Verification condition generator -/

meta def vcg : tactic unit := do
  t ← target,
  match t with
  | `({* %%P *} %%p {* _ *}) :=
    match p with
    | `(program.skip)            := applyc (if is_meta P then ``skip_intro else ``skip_intro')
    | `(program.assign _ _)      := applyc (if is_meta P then ``assign_intro else ``assign_intro')
    | `(program.ite _ _ _)       := do applyc ``ite_intro; vcg
    | `(program.seq _ _)         := do applyc ``seq_intro'; vcg
    | `(program.while_inv _ _ _) :=
      do applyc (if is_meta P then ``while_inv_intro else ``while_inv_intro'); vcg
    | _                          := fail (to_fmt "cannot analyze " ++ to_fmt p)
    end
  | _ := skip  -- do nothing if the goal is not a Hoare triple
  end

end tactic.interactive

namespace hoare_logic
#check nat.zero_add
open program
#print while_inv
example (n m : ℕ) :
  {* λs, s "n" = n ∧ s "m" = m *} ADD {* λs, s "n" = 0 ∧ s "m" = n + m *} :=
begin
  -- use `show` to annotate the while loop with an invariant
  show {* λs, s "n" = n ∧ s "m" = m *}
      while_inv (λs, s "n" + s "m" = n + m) (λs, s "n" ≠ 0)
      ( assign "n" (λs, s "n" - 1) ;;
        assign "m" (λs, s "m" + 1) )
    {* λs, s "n" = 0 ∧ s "m" = n + m *},
  --show_term{vcg},
  vcg;
    simp {contextual := tt},
  intros s hnm hn,
  rw ←hnm,
  cases s "n",
  { contradiction, },
  {rw [nat.succ_eq_add_one], simp, 
      rw [nat.add_assoc], 
      have h1 : s "m" + 1 = 1 + s "m",
      { rw nat.add_comm},
      rw h1,
    -- simp [nat.succ_eq_add_one] 
     },
  intros s h1 h2,
  --intros,
  rw ←h2, simp [nat.zero_add], 
end

lemma add_ge_add_right (a b c : ℕ) (h : a ≥ b) : a + c ≥ b + c := 
begin
 exact nat.add_le_add_right h c,
end

lemma add_ge_add_ge (a b c d : ℕ) (h1 : a ≥ b) (h2 : c ≥ d) : a + c ≥ b + d :=
begin
  intros,
  exact nat.add_le_add h1 h2,
end

open hoare_logic.partial_hoare

/-
def hoare_logic.TEST : program :=
while (λ (s : state), s "y" < 10)
  (assign "x" (λ (s : state), s "x" + s "y") ;; assign "y" (λ (s : state), s "y" + 1))
  x = 1
  y = 0
  while y < 10
    x = x + y
    y = y + 1
  assert(x > y)

Task: given a program; generate a specification; 
      given a while program; generate a loop invariant that leads to a interesting specification. 
-/
set_option pp.all true

#check λ (x:ℕ), x.zero_le
lemma test : 0 ≤ 1:=
begin
/-
Try this: exact 1.zero_le
-/
  show_term{exact nat.zero_le 1},
end

/-
theorem hoare_logic.test : 0 ≤ 1 :=
1.zero_le
-/
/-
theorem hoare_logic.test : @has_le.le.{0} nat nat.has_le (@has_zero.zero.{0} nat nat.has_zero) (@has_one.one.{0} nat nat.has_one) :=
nat.zero_le (@has_one.one.{0} nat nat.has_one)
-/

#print test

/-
invalid field notation, type is not of the form (C ...) where C is a constant
  1
has type
  ?m_1
-/
lemma test1: 0 ≤ 1 := 
nat.zero_le (@has_one.one.{0} nat nat.has_one)

/-
invalid field notation, type is not of the form (C ...) where C is a constant
  1
has type
  ?m_1
state:
⊢ 0 ≤ 1
-/

set_option pp.implicit true
lemma simple_seq1: ∀ (s : state), s "x" = 1 → s "y" = 0 → 1 ≥ 0 ∧ 1 ≥ 1 ∧ 0 ≥ 0:=
begin
  show_term{intros},
  have h1:= λ (s : state) (ᾰ : s "x" = 1) (ᾰ_1 : s "y" = 0), nat.zero_le 1,
  have h2:= λ (s : state) (ᾰ : s "x" = 1) (ᾰ_1 : s "y" = 0), @and.intro (1 ≥ 1) (0 ≥ 0)
       (@le_refl ℕ (@partial_order.to_preorder ℕ (@linear_order.to_partial_order ℕ nat.linear_order)) 1)
       (@le_refl ℕ (@partial_order.to_preorder ℕ (@linear_order.to_partial_order ℕ nat.linear_order)) 0),
  --have h3:= λ (s : state) (ᾰ : s "x" = 1) (ᾰ_1 : s "y" = 0), @and.intro (1 ≥ 0) (1 ≥ 1 ∧ 0 ≥ 0) (h1 s ᾰ ᾰ_1) (h2 s ᾰ ᾰ_1),
  have h3:= λ (s : state) (ᾰ : s "x" = 1) (ᾰ_1 : s "y" = 0), @and.intro (1 ≥ 0) (1 ≥ 1 ∧ 0 ≥ 0) (nat.zero_le 1) (@and.intro (1 ≥ 1) (0 ≥ 0)
       (@le_refl ℕ (@partial_order.to_preorder ℕ (@linear_order.to_partial_order ℕ nat.linear_order)) 1)
       (@le_refl ℕ (@partial_order.to_preorder ℕ (@linear_order.to_partial_order ℕ nat.linear_order)) 0)),
  /-
  Try this: refine @and.intro (1 ≥ 0) (1 ≥ 1 ∧ 0 ≥ 0) _ _
  -/
  show_term{split},
  show_term{exact nat.zero_le 1},
  show_term{split}, exact le_refl 1, exact le_refl 0,
end

/-
theorem hoare_logic.simple_seq1 : ∀ (s : state), s "x" = 1 → s "y" = 0 → 1 ≥ 0 ∧ 1 ≥ 1 ∧ 0 ≥ 0 :=
λ (s : state) (ᾰ : s "x" = 1) (ᾰ_1 : s "y" = 0),
  @and.intro (1 ≥ 0) (1 ≥ 1 ∧ 0 ≥ 0) 1.zero_le
    (@and.intro (1 ≥ 1) (0 ≥ 0)
       (@le_refl ℕ (@partial_order.to_preorder ℕ (@linear_order.to_partial_order ℕ nat.linear_order)) 1)
       (@le_refl ℕ (@partial_order.to_preorder ℕ (@linear_order.to_partial_order ℕ nat.linear_order)) 0))
-/

#print simple_seq1

#print TEST

lemma TEST_loop_inv :
{* λs, s "x" = 1 ∧ s "y" = 0 *} TEST {* λs, s "x" ≥ s "y" *} :=
begin 
  show {* λs, s "x" = 1 ∧ s "y" = 0 *}
      while_inv (λs, s "x" ≥ s "y" ∧ s "x" ≥ 1 ∧ s "y" ≥ 0 ) (λs, s "y" < 10)
      ( assign "x" (λs, s "x" + s "y") ;;
        assign "y" (λs, s "y" + 1) )
    {* λs, s "x" ≥ s "y" *},

  vcg;
    simp {contextual := tt},

  intros s h1 h2 h3 h4,
  
  split, 
  rw (nat.add_comm (s "y") 1),
  refine add_ge_add_right _ _ (s "y") h2,

  split, 
  have h5 : 1 = 1 + 0,
  simp, 
  rw h5, refine (add_ge_add_ge _ _ _ _ h2 h3),
  have h5 : s "y" + 1 ≥ s "y" + 0,
  rw (nat.add_comm (s "y") 1),
  rw (nat.add_comm (s "y") 0),
  apply add_ge_add_right, exact nat.zero_le 1,
  rw (nat.add_zero (s "y")) at h5,
  calc s "y" + 1 ≥ s "y" : h5
  ... ≥ 0 : h3,
  --intros,
  intros s h1 h2,
  /-
  Try this: refine ⟨_, _⟩
  
  -/
  show_term{split},
  exact nat.zero_le 1,
  split, exact le_refl 1, exact le_refl 0,
end

#check while_intro_inv
#check while_inv_intro
#check while_inv_intro'
#print TEST_loop_inv

#check classical.em
/-
def hoare_logic.TEST2 : program :=
while (λ (s : state), s "i" ≤ s "x")
  (assign "i" (λ (s : state), s "i" + 1) ;; assign "j" (λ (s : state), s "j" + s "y"))
-/

/-
def hoare_logic.TEST2 : program :=
while (λ (s : state), s "i" ≤ s "x")
  (assign "i" (λ (s : state), s "i" + 1) ;; assign "j" (λ (s : state), s "j" + s "y"))

  j = 0
  i = 0
  while (i < x)
  {
    i = i + 1
    j = j + y
  }
  assert (y = 1 -> i = j)
-/

#print TEST2

lemma TEST2_loop_inv : 
{* λs, s "j" = 0 ∧ s "i" = 0 *} TEST2 
{* λs, ¬ s "y" = 1 ∨ s "i" = s "j" *} := 
begin
  show {* λs, s "j" = 0 ∧ s "i" = 0 *}
  while_inv (λs, ¬ s "y" = 1 ∨ s "i" = s "j")
  (λs, s "i" ≤ s "x")
  ( assign "i" (λs, s "i" + 1) ;; 
    assign "j" (λs, s "j" + s "y") )
  {* λs, ¬ s "y" = 1 ∨ s "i" = s "j" *},
  vcg; simp {contextual := tt},
  intros s h1 h2,
  have h3 := classical.em (s "y" = 1),
  cases h3, 
  cases h1,
  left, assumption,
  right, 
  rw [h1, h3], 
  left, assumption,
end

/-
theorem hoare_logic.TEST2_loop_inv : {* (λ (s : state), s "j" = 0 ∧ s "i" = 0) *} TEST2 {* (λ (s : state), ¬s "y" = 1 ∨ s "i" = s "j") *} :=
id
  (((assign_intro (λ (s : state), ¬s "y" = 1 ∨ s "i" = s "j")).seq_intro'
      (assign_intro'
         ((id_tag tactic.id_tag.simp
             (forall_congr_eq
                (λ (s : state),
                   (imp_congr_ctx_eq (eq.refl ((¬s "y" = 1 ∨ s "i" = s "j") ∧ s "i" ≤ s "x"))
                      (λ (_h : (¬s "y" = 1 ∨ s "i" = s "j") ∧ s "i" ≤ s "x"),
                         (λ (a a_1 : Prop) (e_1 : a = a_1) (b b_1 : Prop) (e_2 : b = b_1),
                            congr (congr_arg or e_1) e_2)
                           (¬(s & "i" ::= s "i" + 1 &
                                   "j" ::=
                                   (s & "i" ::= s "i" + 1) "j" + (s & "i" ::= s "i" + 1) "y")
                                  "y" =
                                1)
                           (¬s "y" = 1)
                           ((λ (a a_1 : Prop) (e_1 : a = a_1), congr_arg not e_1)
                              ((s & "i" ::= s "i" + 1 &
                                    "j" ::=
                                    (s & "i" ::= s "i" + 1) "j" + (s & "i" ::= s "i" + 1) "y")
                                   "y" =
                                 1)
                              (s "y" = 1)
                              ((λ (a a_1 : ℕ) (e_1 : a = a_1) (ᾰ ᾰ_1 : ℕ) (e_2 : ᾰ = ᾰ_1),
                                  congr (congr_arg eq e_1) e_2)
                                 ((s & "i" ::= s "i" + 1 &
                                     "j" ::=
                                     (s & "i" ::= s "i" + 1) "j" + (s & "i" ::= s "i" + 1) "y")
                                    "y")
                                 (s "y")
                                 ((((λ (name name_1 : string) (e_1 : name = name_1) (val val_1 : ℕ)
                                     (e_2 : val = val_1) (s s_1 : state) (e_3 : s = s_1) (ᾰ ᾰ_1 : string)
                                     (e_4 : ᾰ = ᾰ_1),
                                       congr (congr (congr (congr_arg state.update e_1) e_2) e_3) e_4)
                                      "j"
                                      "j"
                                      (eq.refl "j")
                                      ((s & "i" ::= s "i" + 1) "j" + (s & "i" ::= s "i" + 1) "y")
                                      (s "j" + s "y")
                                      ((λ [self : has_add ℕ] (ᾰ ᾰ_1 : ℕ) (e_2 : ᾰ = ᾰ_1)
                                        (ᾰ_2 ᾰ_3 : ℕ) (e_3 : ᾰ_2 = ᾰ_3),
                                          congr (congr_arg has_add.add e_2) e_3)
                                         ((s & "i" ::= s "i" + 1) "j")
                                         (s "j")
                                         (state.update_apply_ne "i" "j" (s "i" + 1) s (of_as_true trivial))
                                         ((s & "i" ::= s "i" + 1) "y")
                                         (s "y")
                                         (state.update_apply_ne "i" "y" (s "i" + 1) s (of_as_true trivial)))
                                      (s & "i" ::= s "i" + 1)
                                      (s & "i" ::= s "i" + 1)
                                      (eq.refl (s & "i" ::= s "i" + 1))
                                      "y"
                                      "y"
                                      (eq.refl "y")).trans
                                     (state.update_apply_ne "j" "y" (s "j" + s "y") (s & "i" ::= s "i" + 1)
                                        (of_as_true trivial))).trans
                                    (state.update_apply_ne "i" "y" (s "i" + 1) s (of_as_true trivial)))
                                 1
                                 1
                                 (eq.refl 1)))
                           ((s & "i" ::= s "i" + 1 & "j" ::= (s & "i" ::= s "i" + 1) "j" + (s & "i" ::= s "i" + 1) "y")
                                "i" =
                              (s & "i" ::= s "i" + 1 &
                                 "j" ::=
                                 (s & "i" ::= s "i" + 1) "j" + (s & "i" ::= s "i" + 1) "y")
                                "j")
                           (s "i" + 1 = s "j" + s "y")
                           ((λ (a a_1 : ℕ) (e_1 : a = a_1) (ᾰ ᾰ_1 : ℕ) (e_2 : ᾰ = ᾰ_1),
                               congr (congr_arg eq e_1) e_2)
                              ((s & "i" ::= s "i" + 1 &
                                  "j" ::=
                                  (s & "i" ::= s "i" + 1) "j" + (s & "i" ::= s "i" + 1) "y")
                                 "i")
                              (s "i" + 1)
                              ((((λ (name name_1 : string) (e_1 : name = name_1) (val val_1 : ℕ) (e_2 : val = val_1)
                                  (s s_1 : state) (e_3 : s = s_1) (ᾰ ᾰ_1 : string) (e_4 : ᾰ = ᾰ_1),
                                    congr (congr (congr (congr_arg state.update e_1) e_2) e_3) e_4)
                                   "j"
                                   "j"
                                   (eq.refl "j")
                                   ((s & "i" ::= s "i" + 1) "j" + (s & "i" ::= s "i" + 1) "y")
                                   (s "j" + s "y")
                                   ((λ [self : has_add ℕ] (ᾰ ᾰ_1 : ℕ) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : ℕ)
                                     (e_3 : ᾰ_2 = ᾰ_3), congr (congr_arg has_add.add e_2) e_3)
                                      ((s & "i" ::= s "i" + 1) "j")
                                      (s "j")
                                      (state.update_apply_ne "i" "j" (s "i" + 1) s (of_as_true trivial))
                                      ((s & "i" ::= s "i" + 1) "y")
                                      (s "y")
                                      (state.update_apply_ne "i" "y" (s "i" + 1) s (of_as_true trivial)))
                                   (s & "i" ::= s "i" + 1)
                                   (s & "i" ::= s "i" + 1)
                                   (eq.refl (s & "i" ::= s "i" + 1))
                                   "i"
                                   "i"
                                   (eq.refl "i")).trans
                                  (state.update_apply_ne "j" "i" (s "j" + s "y") (s & "i" ::= s "i" + 1)
                                     (of_as_true trivial))).trans
                                 (state.update_apply "i" (s "i" + 1) s))
                              ((s & "i" ::= s "i" + 1 &
                                  "j" ::=
                                  (s & "i" ::= s "i" + 1) "j" + (s & "i" ::= s "i" + 1) "y")
                                 "j")
                              (s "j" + s "y")
                              (((λ (name name_1 : string) (e_1 : name = name_1) (val val_1 : ℕ) (e_2 : val = val_1)
                                 (s s_1 : state) (e_3 : s = s_1) (ᾰ ᾰ_1 : string) (e_4 : ᾰ = ᾰ_1),
                                   congr (congr (congr (congr_arg state.update e_1) e_2) e_3) e_4)
                                  "j"
                                  "j"
                                  (eq.refl "j")
                                  ((s & "i" ::= s "i" + 1) "j" + (s & "i" ::= s "i" + 1) "y")
                                  (s "j" + s "y")
                                  ((λ [self : has_add ℕ] (ᾰ ᾰ_1 : ℕ) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : ℕ)
                                    (e_3 : ᾰ_2 = ᾰ_3), congr (congr_arg has_add.add e_2) e_3)
                                     ((s & "i" ::= s "i" + 1) "j")
                                     (s "j")
                                     (state.update_apply_ne "i" "j" (s "i" + 1) s (of_as_true trivial))
                                     ((s & "i" ::= s "i" + 1) "y")
                                     (s "y")
                                     (state.update_apply_ne "i" "y" (s "i" + 1) s (of_as_true trivial)))
                                  (s & "i" ::= s "i" + 1)
                                  (s & "i" ::= s "i" + 1)
                                  (eq.refl (s & "i" ::= s "i" + 1))
                                  "j"
                                  "j"
                                  (eq.refl "j")).trans
                                 (state.update_apply "j" (s "j" + s "y") (s & "i" ::= s "i" + 1)))))).trans
                     (propext
                        (and_imp (¬s "y" = 1 ∨ s "i" = s "j") (s "i" ≤ s "x")
                           (¬s "y" = 1 ∨ s "i" + 1 = s "j" + s "y")))))).mpr
            (λ (s : state) (h1 : ¬s "y" = 1 ∨ s "i" = s "j") (h2 : s "i" ≤ s "x"),
               (classical.em (s "y" = 1)).dcases_on
                 (λ (h3 : s "y" = 1),
                    h1.dcases_on (λ (h1 : ¬s "y" = 1), or.inl h1)
                      (λ (h1 : s "i" = s "j"),
                         or.inr
                           ((id_tag tactic.id_tag.rw (eq.rec (eq.refl (s "i" + 1 = s "j" + s "y")) h1)).mpr
                              ((id_tag tactic.id_tag.rw (eq.rec (eq.refl (s "j" + 1 = s "j" + s "y")) h3)).mpr
                                 (eq.refl (s "j" + 1))))))
                 (λ (h3 : ¬s "y" = 1), or.inl h3))))).while_inv_intro'
     ((id_tag tactic.id_tag.simp
         ((forall_congr_eq
             (λ (s : state),
                (((imp_congr_ctx_eq (eq.refl (s "j" = 0 ∧ s "i" = 0))
                     (λ (_h : s "j" = 0 ∧ s "i" = 0),
                        ((λ (a a_1 : Prop) (e_1 : a = a_1) (b b_1 : Prop) (e_2 : b = b_1),
                            congr (congr_arg or e_1) e_2)
                           (¬s "y" = 1)
                           (¬s "y" = 1)
                           (eq.refl (¬s "y" = 1))
                           (s "i" = s "j")
                           true
                           (((λ (a a_1 : ℕ) (e_1 : a = a_1) (ᾰ ᾰ_1 : ℕ) (e_2 : ᾰ = ᾰ_1),
                                congr (congr_arg eq e_1) e_2)
                               (s "i")
                               0
                               _h.elim_right
                               (s "j")
                               0
                               _h.elim_left).trans
                              (propext (eq_self_iff_true 0)))).trans
                          (propext (or_true (¬s "y" = 1))))).trans
                    (propext (and_imp (s "j" = 0) (s "i" = 0) true))).trans
                   (imp_congr_ctx_eq (eq.refl (s "j" = 0))
                      (λ (_h : s "j" = 0), propext (implies_true_iff (s "i" = 0))))).trans
                  (propext (implies_true_iff (s "j" = 0))))).trans
            (propext (implies_true_iff state)))).mpr
        trivial)
     ((id_tag tactic.id_tag.simp
         ((forall_congr_eq
             (λ (s : state),
                (imp_congr_ctx_eq (propext not_le)
                   (λ (_h : s "x" < s "i"),
                      (imp_congr_ctx_eq (eq.refl (¬s "y" = 1 ∨ s "i" = s "j"))
                         (λ (_h : ¬s "y" = 1 ∨ s "i" = s "j"), propext (iff_true_intro _h))).trans
                        (propext (implies_true_iff (¬s "y" = 1 ∨ s "i" = s "j"))))).trans
                  (propext (implies_true_iff (s "x" < s "i"))))).trans
            (propext (implies_true_iff state)))).mpr
        trivial))
-/

#print TEST2_loop_inv



end hoare_logic
