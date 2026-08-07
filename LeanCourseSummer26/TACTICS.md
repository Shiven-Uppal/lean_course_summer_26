# Tactics used in the course

References point to occurrences in the lecture example files and exercise
sheets.

## Introducing new objects

- `intro` — Introduces variables or assumptions from an implication or
  universal quantifier into the context. [See](../LectureNotes/lecture1/examples1.lean#L34)

- `ext` — Applies extensionality, reducing equality of structured objects to
  equality of their components or values. [See](../exercises/sheet3.lean#L187)

- `cases` — Splits an inductive object or hypothesis into one goal for each
  possible constructor. [See](../LectureNotes/lecture2/examples2.lean#L60)

- `rcases` — Destructures a hypothesis using patterns; it can unpack
  conjunctions and existentials or split disjunctions. [See](../exercises/sheet1.lean#L19)

- `rintro` — Combines `intro` and `rcases`: it introduces an assumption and
  immediately destructures it with a pattern. [See](../exercises/sheet3.lean#L59)

- `have` — Adds an intermediate fact to the context, either with an explicit
  proof or by inference. [See](../LectureNotes/lecture2/examples2.lean#L72)

- `obtain` — Gives names to, and optionally destructures, the result of an
  expression. [See](../LectureNotes/lecture4/examples4.lean#L144)

- `let` — Introduces a local definition for an expression. [See](../exercises/sheet2.lean#L43)

- `set x := t with hx` — Introduces `x` as a local name for `t` and records the
  defining equality as `hx`. [See](../LectureNotes/lecture7/examples7.lean#L89)

- `induction` — Starts an induction proof, creating a case for each constructor
  and providing the relevant induction hypotheses. [See](../LectureNotes/lecture1/examples1.lean#L17)

- `by_contra` / `by_contra!` — Proves the goal by contradiction. The `!`
  version also simplifies the negated hypothesis. [See `by_contra`](../LectureNotes/lecture2/examples2.lean#L127);
  [see `by_contra!`](../exercises/sheet2.lean#L21)
  
- `by_cases` — Splits into two cases according to whether a proposition is true
  or false. [See](../exercises/sheet1.lean#L12)

- `split_ifs with h` — Splits a goal into cases for the conditions occurring in
  `if ... then ... else ...` expressions, names the condition in each branch
  `h`, and simplifies the corresponding `if` expression.
  [See](../LectureNotes/lecture4/exercise_class.lean#L86)

## Manipulating the tactic state

Many tactics below act on the goal by default. For tactics that support
locations, `at h` applies the tactic to hypothesis `h`, and `at *` applies it
throughout the context and to the goal.

- `exact` — Closes the goal with a proof term of exactly the required type.
  [See](../LectureNotes/lecture1/examples1.lean#L19)

- `exact_mod_cast` — Closes the goal using a proof stated with compatible
  numeric casts inserted or removed. [See](../exercises/sheet5.lean#L21)

- `contradiction` — Closes the goal when the context contains incompatible
  hypotheses, such as both `P` and `¬ P`. [See](../exercises/sheet1.lean#L25)

- `rw` / `rewrite` / `nth_rewrite` — Rewrites using equalities. `rw` is the
  short form of `rewrite`; `nth_rewrite n` rewrites only the chosen occurrence.
  [See `rw`](../LectureNotes/lecture1/examples1.lean#L11);
  [see `nth_rewrite`](../exercises/sheet3.lean#L114)

- `apply` — Matches a theorem's conclusion with the target and creates goals
  for its remaining assumptions. [See](../LectureNotes/lecture2/examples2.lean#L16)

- `specialize` — Instantiates a universally quantified hypothesis with chosen
  arguments, replacing it with the resulting statement. [See](../exercises/sheet5.lean#L101)

- `refine` — Supplies a partial proof term; each `?_` hole becomes a new goal.
  It acts on the goal rather than at a hypothesis. [See](../LectureNotes/lecture3/examples3.lean#L69)

- `use` — Supplies a witness for an existential goal. [See](../exercises/sheet1.lean#L66)

- `constructor` — Applies the goal's constructor; for `P ∧ Q` or `P ↔ Q`, it
  creates two goals. [See](../LectureNotes/lecture2/examples2.lean#L28)

- `left` / `right` — Selects the left or right side of a disjunction.
  The corresponding proof terms are `Or.inl h` and `Or.inr h`.
  [See](../LectureNotes/lecture2/examples2.lean#L45)

- `push Not` — Pushes negations inward through logical expressions.
  [See](../LectureNotes/lecture3/examples3.lean#L121)

- `change` — Replaces the target with a definitionally equal, more convenient
  formulation. [See](../LectureNotes/lecture5/examples5.lean#L172)

- `congrArg f h` — Applies the same function to both sides of an equality. If
  `h : a = b`, then `congrArg f h` proves `f a = f b`. For example,
  `apply congrArg deriv` changes a goal `deriv f = deriv g` to `f = g`.
  This is a proof-producing lemma rather than a tactic.
  [See](../LectureNotes/lecture5/examples5.lean#L184)

- `congrFun h x` — Evaluates both sides of an equality of functions at the same
  argument. If `h : f = g`, then `congrFun h x` proves `f x = g x`. This is a
  proof-producing lemma rather than a tactic.

## Specialized tactics

- `simp` — Rewrites repeatedly using simplification lemmas. Prefer `simp?` when
  developing a proof: it suggests a reproducible `simp only [...]` call.

- `positivity` — Proves positivity, nonnegativity, or nonzeroness from the
  structure of an expression and facts in the context. [See](../exercises/sheet5.lean#L18)

- `linarith` — Solves goals that follow from linear equalities and inequalities
  in the context. 

- `omega` — Decides many goals in linear integer and natural-number arithmetic.

- `group` — Normalizes group-style expressions using associativity, inverses,
  identities, and exponent laws; it does not assume commutativity.

- `ring` / `ring_nf` — Proves polynomial identities by normalization.
  `ring` closes a matching goal; `ring_nf` normalizes polynomial expressions in
  the goal and hypotheses. 

- `calc` — Writes a chain of equalities or relations, with a proof for each
  step. [See](../LectureNotes/lecture3/examples3.lean#L63)
