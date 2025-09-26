section propositional -- LEMBRETE: use git push origin master

variable (P Q R : Prop)

-- LEMBRETE 2: Lembrar de ajeitar os nomes "horríveis"...

------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :
  P → ¬ ¬ P  := by
  intro h1
  intro h2
  apply h2
  apply h1

theorem doubleneg_elim :
  ¬ ¬ P → P  := by
  intro nnp
  by_cases h : P
  exact h
  exact False.elim (nnp h)

theorem doubleneg_law : -- Lembrar de diminuir esse código (sos)
  ¬ ¬ P ↔ P  := by
  constructor
  intro nnp
  by_cases h : P
  exact h
  exfalso
  apply nnp
  assumption
  intro p
  intro nnp1
  apply nnp1
  assumption

------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm : -- JEITO DE SE RESOLVER UMA DISJUNÇÃO
  (P ∨ Q) → (Q ∨ P)  := by
   intro hpq
   rcases hpq with hp | hq
   right
   exact hp
   left
   exact hq


theorem conj_comm : -- JEITO DE SE RESOLVER UMA CONJUNÇÃO
  (P ∧ Q) → (Q ∧ P) := by
  intro hpq
  apply And.intro
  apply hpq.right
  apply hpq.left


------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :
  (¬ P ∨ Q) → (P → Q)  := by
  intro nothpq
  intro p
  cases nothpq with
  | inl np => exact False.elim (np p)
  | inr q => exact q


theorem disj_as_impl :
  (P ∨ Q) → (¬ P → Q)  := by
  intro pvq
  intro np
  cases pvq with
  | inl p => apply False.elim (np p)
  | inr q => exact q

------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬ Q → ¬ P)  := by
  intro hpq
  intro notq
  by_cases h : P
  intro hnotp
  apply notq
  apply hpq
  apply h
  assumption

theorem impl_as_contrapositive_converse :
  (¬ Q → ¬ P) → (P → Q)  := by
  intro notpnotq
  intro p
  by_cases h : Q
  exact h
  exact False.elim ((notpnotq h) p) -- Aplico ¬ Q → ¬ P em ¬Q, que resulta em ¬P, pra no final Aplicar ¬P em P


theorem contrapositive_law :
  (P → Q) ↔ (¬ Q → ¬ P)  := by
  constructor
  -- →
  intro hpq
  intro nq
  intro np
  have hq : Q := by
    apply hpq
    exact np
  apply nq
  exact hq
  -- ←
  intro hqp
  intro p
  by_cases h : P
  sorry

------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------
theorem lem_irrefutable : -- COMMITAR "COM AJUDA VIA ZULLIP"
  ¬ ¬ (P ∨ ¬ P)  := by
  intro h1
  have hp : (P ∨ ¬ P) := by
    right
    intro h2
    apply h1
    have hp : (P ∨ ¬ P) := by
      left
      exact h2
    exact hp
  apply h1
  exact hp
------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬ ¬ P  := by
  intro h1
  intro hnotp
  by_cases h2 : P
  apply hnotp h2 -- Da para você dar apply em mais de um nome :P
  let pq : P → Q := by
    intro p
    exact
  sorry


------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear :
  (P → Q) ∨ (Q → P)  := by
  by_cases h1 : P
  right
  intro q
  assumption
  left
  intro p
  exfalso
  apply h1
  exact p

------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :
  P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by
  intro h1
  intro h2
  cases h1 with
  | inl p => exact h2.left p
  | inr q => exact h2.right q



theorem conj_as_negdisj :
  P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by
  intro h1
  intro h2
  cases h2 with
  | inl hnp => exact hnp h1.left
  | inr qnp => exact qnp h1.right

------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :
  ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by
  intro h1
  constructor
  intro p
  apply h1
  left
  exact p
  intro q
  apply h1
  right
  assumption

theorem demorgan_disj_converse :
  (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by
  intro h1
  intro h2
  cases h2 with
  | inl hip1 => apply h1.left hip1
  | inr hip2 => apply h1.right hip2

theorem demorgan_conj :
  ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by
  intro h1
  have h2 : ¬ Q ∨ ¬ P := by
    by_cases h : Q
    right
    intro p
    apply h1
    constructor
    apply p
    apply h
    left
    apply h
  assumption

theorem demorgan_conj_converse :
  (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by
  intro h1
  intro h2
  cases h1 with
  | inl hip1 => apply hip1 h2.right
  | inr hip2 => apply hip2 h2.left

theorem demorgan_conj_law :
  ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P) := by
  constructor
  -- → (demorgan_conj)
  intro h1
  have h2 : ¬ Q ∨ ¬ P := by
    by_cases h : Q
    right
    intro p
    apply h1
    constructor
    apply p
    apply h
    left
    apply h
  assumption
  -- ← (demorgan_conj_converse)
  intro h1
  intro h2
  cases h1 with
  | inl hip1 => apply hip1 h2.right
  | inr hip2 => apply hip2 h2.left


theorem demorgan_disj_law :
  ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
  constructor
  -- ←
  intro h1
  constructor
  intro p
  apply h1
  left
  exact p
  intro q
  apply h1
  right
  assumption
  -- →
  intro h1
  intro h2
  cases h2 with
  | inl hip1 => apply h1.left hip1
  | inr hip2 => apply h1.right hip2


------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by
  intro h1
  have h2 : P ∧ Q ∨ P ∧ R := by
    left



theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
  sorry

theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
  sorry

theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by
  sorry


------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  := by
  intro h1
  intro p
  intro q
  have h2 : P ∧ Q := by
    constructor
    exact p
    exact q
  apply h1
  exact h2

theorem uncurry_prop :
  (P → (Q → R)) → ((P ∧ Q) → R)  := by
  intro h1
  intro h2
  cases h2 with
  | intro hP hQ
  apply h1
  exact hP
  exact hQ

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
  have hp : (P ∨ Q) := by
    left
    exact p
  exact hp

theorem weaken_disj_left :
  Q → (P ∨ Q)  := by
  intro q
  have hp : (P ∨ Q) := by
    right
    exact q
  exact hp

theorem weaken_conj_right :
  (P ∧ Q) → P  := by
  intro h1
  rcases h1 with ⟨hp , hq⟩
  exact hp

theorem weaken_conj_left :
  (P ∧ Q) → Q  := by
  intro h1
  rcases h1 with ⟨hp , hq⟩
  exact hq

------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
  (P ∨ P) ↔ P  := by
  constructor
  -- →
  intro h
  cases h with
  | inl hp => exact hp
  | inr hp => exact hp
  -- ←
  intro p
  constructor
  exact p

theorem conj_idem :
  (P ∧ P) ↔ P := by
  constructor
  -- →
  intro pp
  rcases pp with ⟨hp , _⟩
  exact hp
  -- ←
  intro p
  constructor
  repeat exact p

------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
  False → P := by
  intro false
  cases false

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

theorem demorgan_exists :
  ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
  intro h1
  intro x
  intro h2
  have h3 : ∃ x, P x := ⟨x, h2⟩
  exact h1 h3


theorem demorgan_exists_converse :
  (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by
  sorry

theorem demorgan_forall :
  ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_forall_converse :
  (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
  sorry

theorem demorgan_forall_law :
  ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_law :
  ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :
  (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists :
  (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists_converse :
  ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by
  sorry

theorem exists_as_neg_forall_converse :
  ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
  sorry

theorem forall_as_neg_exists_law :
  (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
  sorry

theorem exists_as_neg_forall_law :
  (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃ x, Px ∧ Q x) → (∃ x, Px) ∧ (∃ x, Q x)  := by
  intro h1

theorem exists_disj_as_disj_exists :
  (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists_converse :
  (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
  sorry

theorem forall_conj_as_conj_forall :
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by
  sorry

theorem forall_conj_as_conj_forall_converse :
  (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  sorry

theorem forall_disj_as_disj_forall_converse :
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
