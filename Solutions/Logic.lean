section propositional

variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :
  P → ¬ ¬ P  := by
  intro hp
  intro hnp
  apply hnp
  exact hp


theorem doubleneg_elim :
  ¬ ¬ P → P  := by
  intro hnp
  by_cases h : P
  exact h

  have hq: False := hnp h -- False needs to be explicit?
  contradiction

theorem doubleneg_law :
  ¬ ¬ P ↔ P  := by
  constructor
  intro hnp
  by_cases hp: P
  -- Left
  exact hp
  -- Right
  contradiction

  intro hp
  intro hnp
  contradiction



------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm :
    (P ∨ Q) → (Q ∨ P)  := by
  intro hpq
  rcases hpq with (hp | hq)
  right
  exact hp

  left
  exact hq

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro hpq
  constructor

  have hq := hpq.right
  exact hq

  have hp := hpq.left
  exact hp



------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :
  (¬ P ∨ Q) → (P → Q)  := by
  intro hip
  intro p
  rcases hip with (negp | q)
  -- Case left
  exfalso
  apply negp
  -- Case right
  exact p
  exact q

theorem disj_as_impl :
  (P ∨ Q) → (¬ P → Q)  := by
  intro horq negp
  rcases horq with (p | q)
  have c: False := negp p
  exfalso
  apply negp
  exact p
  exact q



------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬ Q → ¬ P)  := by
  intro pimpq negq p
  have q: Q := pimpq p
  have c: False := negq q
  exact c

theorem impl_as_contrapositive_converse :
  (¬ Q → ¬ P) → (P → Q)  := by
  intro negqimpnegp p
  by_cases hq: Q
  -- Case left
  exact hq
  have negp: ¬P:= negqimpnegp hq -- Does it need ¬P?
  have c: False := negp p
  exfalso
  exact c


theorem contrapositive_law :
  (P → Q) ↔ (¬ Q → ¬ P)  := by
  constructor
  intro hpq
  intro negq
  by_cases hp: P
  have hq: Q := hpq hp
  have c: False := negq hq
  exfalso
  exact c

  exact hp

  intro negqnegp
  intro p
  by_cases hq: Q

  exact hq
  have negp: ¬P := negqnegp hq
  have c: False := negp p
  exfalso
  exact c



------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

theorem lem_irrefutable :
  ¬ ¬ (P ∨ ¬ P)  := by
  intro npp
  have p1_lem: P ∨ ¬P := by
    right
    intro p
    have p2_lem: P ∨ ¬P := by
      left
      exact p
    have c: False := npp p2_lem
    contradiction
  have f: False := npp p1_lem
  contradiction

------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬ ¬ P  := by
  intro hpqp
  intro neg_p
  have pq: P → Q := by
    intro p
    have c: False := neg_p p
    exfalso
    exact c
  have p: P := hpqp pq
  have c: False := neg_p p
  exact c


------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear :
  (P → Q) ∨ (Q → P)  := by
  by_cases h: P
  right
  intro Q
  exact h

  left
  intro P
  have c: False := h P
  exfalso
  exact c


------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :
  P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by
  intro p_or_q
  intro neg_p_or_neg_q
  rcases p_or_q with (p | q)
  have neg_p : ¬ P := neg_p_or_neg_q.left
  have c: False := neg_p p
  exact c

  have neg_q: ¬Q := neg_p_or_neg_q.right
  have c: False := neg_q q
  exact c


theorem conj_as_negdisj :
  P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by
  intro p_and_q
  intro neg_p_or_neg_q
  rcases neg_p_or_neg_q with (neg_p | neg_q)
  have p: P := p_and_q.left
  have c: False := neg_p p
  exact c

  have q: Q := p_and_q.right
  have c: False := neg_q q
  exact c


------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :
  ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by
  intro neg_porq
  constructor
  intro p
  have p_or_q: P ∨ Q := by
    left
    exact p

  have c: False := neg_porq p_or_q
  exact c

  intro q
  have p_or_q: P ∨ Q := by
    right
    exact q

  have c: False := neg_porq p_or_q
  exact c

theorem demorgan_disj_converse :
  (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by
  intro neg_p_and_neg_p
  intro p_or_q
  rcases p_or_q with (p | q)
  have np: ¬P := neg_p_and_neg_p.left
  have c: False := np p
  exact c

  have nq: ¬Q := neg_p_and_neg_p.right
  have c: False := nq q
  exact c

theorem demorgan_conj :
  ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by
  intro neg_pandq
  by_cases hp: P
  by_cases hq : Q
  have p_and_q: P ∧ Q := by
    constructor
    exact hp
    exact hq
  have c: False := neg_pandq p_and_q
  exfalso
  exact c
  constructor
  exact hq
  right
  exact hp


theorem demorgan_conj_converse :
  (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by
  intro nq_or_np
  intro p_and_q
  rcases p_and_q with ⟨p, q⟩
  rcases nq_or_np with nq | np

  have c: False := nq q
  exact c

  have c: False := np p
  exact c

theorem demorgan_conj_law :
  ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by
  constructor
  intro n_pandq
  by_cases p: P
  by_cases q: Q

  have pandq: P ∧ Q := by
    constructor
    exact p
    exact q
  have c: False := n_pandq pandq
  exfalso
  exact c

  left
  exact q
  right
  exact p

  intro nq_or_np
  intro pandq
  rcases pandq with ⟨p, q⟩
  rcases nq_or_np with nq | np

  have c: False := nq q
  exact c

  have c: False := np p
  exact c


theorem demorgan_disj_law :
  ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
  constructor
  intro n_porq
  constructor
  intro p

  have porq : P ∨ Q := by
    constructor
    exact p

  have c: False := n_porq porq
  exact c

  intro q
  have porq : P ∨ Q := by
    right
    exact q
  have c: False := n_porq porq
  exact c

  intro np_and_nq
  intro porq
  rcases np_and_nq with ⟨np, nq⟩
  rcases porq with p | q
  have c: False := np p
  exact c

  have c: False := nq q
  exact c

------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by
  intro p_and_qorr
  rcases p_and_qorr with ⟨p, qorr⟩
  rcases qorr with q | r

  left
  constructor
  exact p
  exact q

  right
  constructor
  exact p
  exact r

theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
  intro pandq_or_pandr
  rcases pandq_or_pandr with pandq | pandr
  have p: P := pandq.left
  constructor
  exact p
  have q: Q := pandq.right
  left
  exact q

  have p: P := pandr.left
  constructor
  exact p

  have r: R := pandr.right
  right
  exact r

theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
  intro p_or_qandr
  rcases p_or_qandr with p | qandr
  constructor

  left
  exact p

  left
  exact p

  rcases qandr with ⟨q, r⟩
  constructor
  right
  exact q
  right
  exact r

theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by
  intro porq_and_porr
  rcases porq_and_porr with ⟨porq, porr⟩
  rcases porq with p | q

  left
  exact p

  rcases porr with p | r
  left
  exact p
  right
  constructor
  exact q
  exact r


------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  := by
  intro pandq_imp_r
  intro p
  intro q

  have pandq: P ∧ Q := by
    constructor
    exact p
    exact q
  have r := pandq_imp_r pandq
  exact r

theorem uncurry_prop :
  (P → (Q → R)) → ((P ∧ Q) → R)  := by
  intro p_imp_qimpr
  intro pandq
  rcases pandq with ⟨p, q⟩
  have qimpr := p_imp_qimpr p
  have r := qimpr q
  exact r


------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :
  P → P  := by
  intro p
  exact p


------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :
  P → (P ∨ Q)  := by
  intro p
  left
  exact p

theorem weaken_disj_left :
  Q → (P ∨ Q)  := by
  intro q
  right
  exact q

theorem weaken_conj_right :
  (P ∧ Q) → P  := by
  intro pandq
  have p: P := pandq.left
  exact p

theorem weaken_conj_left :
  (P ∧ Q) → Q  := by
  intro pandq
  have q: Q := pandq.right
  exact q


------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
  (P ∨ P) ↔ P  := by
  constructor
  intro porp
  rcases porp with p1 | p2
  exact p1
  exact p2

  intro p
  left
  exact p

theorem conj_idem :
  (P ∧ P) ↔ P := by
  constructor
  intro pandp
  have p: P := pandp.left
  exact p

  intro p
  constructor
  exact p
  exact p


------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
  False → P := by
  intro c
  exfalso
  exact c


theorem true_top :
  P → True  := by
  intro p
  trivial



end propositional

----------------------------------------------------------------

section predicate

variable (U : Type)
variable (P Q : U → Prop)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

theorem demorgan_exists :  -- Proved
  ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
  intro he
  intro a
  intro npa
  have ep : ∃ x, P x := by
    exists a
  have c: False :=  he ep
  exact c

theorem demorgan_exists_converse :  -- Proved
  (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by
  sorry

theorem demorgan_forall :  -- Sorry
  ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_forall_converse :  -- Proved
  (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
  sorry

theorem demorgan_forall_law :  -- Sorry
  ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_law :  -- Proved
  ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :  -- Proved
  (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists :  -- Proved
  (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists_converse :  -- Sorry
  ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by
  sorry

theorem exists_as_neg_forall_converse :  -- Sorry
  ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
  sorry

theorem forall_as_neg_exists_law :  -- Sorry
  (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
  sorry

theorem exists_as_neg_forall_law :  -- Sorry
  (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :  -- Proved
  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists :  -- Proved
  (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists_converse :  -- Proved
  (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
  sorry

theorem forall_conj_as_conj_forall :  -- Proved
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by
  sorry

theorem forall_conj_as_conj_forall_converse :  -- Proved
  (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  sorry

theorem forall_disj_as_disj_forall_converse :  -- Proved
  (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)  := by
  sorry


end predicate

------------------------------------------------

section bonus

------------------------------------------------
--  Drinker's paradox
------------------------------------------------

variable (D : U → Prop)

-- There is a person p such that:
-- if p drinks, then everybody drinks
-- p: «person»
-- D x: «x drinks»
theorem drinker :
  ∃ p, (D p → ∀ x, D x)  := by
  sorry

------------------------------------------------
--  Russell's paradox
------------------------------------------------

variable (S : U → U → Prop)

-- It is impossible to have a barber b such that
-- b shaves exactly those people who do not shave themselves
-- b: «barber»
-- S x y: «x shaves y»
theorem russell :
  ¬ ∃ b, ∀ x, (S b x ↔ ¬ S x x)  := by
  sorry


end bonus


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)  := by
  sorry

theorem exists_conj_as_conj_exists_converse :
  (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)  := by
  sorry

---------------------------------------------- -/
