import tactic.show_term

open nat (add_assoc add_comm)

theorem hello_world (a b c : ℕ) : a + b + c = a + c + b :=
begin
/-
Try this: exact (id_tag tactic.id_tag.rw (eq.rec (eq.refl (a + b + c = a + c + b)) (add_assoc a b c))).mpr
  ((id_tag tactic.id_tag.rw (eq.rec (eq.refl (a + (b + c) = a + c + b)) (add_comm b c))).mpr
     ((id_tag tactic.id_tag.rw (eq.rec (eq.refl (a + (c + b) = a + c + b)) (add_assoc a c b).symm)).mpr
        (eq.refl (a + c + b))))

-/

show_term{rw [add_assoc, add_comm b, ←add_assoc]},
end
