import LectureNotes.lecture7.examples7

open MyFunctions MySequences

namespace MySequences

/-!
## Lemmas for sequences
-/

/-- The sum of two convergent sequences converges to the sum of their limits. -/
lemma tends_to_add {x y : RealSeq} {a b : ℝ}
    (hx : TendsTo x a) (hy : TendsTo y b) :
    TendsTo ⟨fun n ↦ x n + y n⟩ (a + b) := by
  intro ε hε
  obtain ⟨ N₁, hN₁ ⟩ := hx (ε / 2) (by positivity)
  obtain ⟨ N₂, hN₂ ⟩ := hy (ε / 2) (by positivity)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  calc
    dist (x n + y n) (a + b) ≤ dist (x n) a + dist (y n) b := by
      exact dist_add_add_le (x.x n) (y.x n) a b
    _ < ε / 2 + ε / 2 := by linarith [hN₁ n (le_of_max_le_left hn), hN₂ n (le_of_max_le_right hn)]
    _ = ε := by exact add_halves ε

-- For exercise 2
lemma tends_to_le_of_le {x : RealSeq} {a b : ℝ} (hx : TendsTo x a) (h : ∀ n, x n ≤ b) :
    a ≤ b := by
  by_contra! hba
  let ε := (a - b) / 2
  obtain ⟨N, hN⟩ := hx ε (by positivity)
  specialize hN N (le_refl N)
  apply abs_lt.mp at hN
  have hcon: x N > b + ε := by
    calc
      x N > a - ε := by linarith [hN]
      _ = a - b + b - ε  := by linarith
      _ = b + a - b - (a - b)/2 := by ring
      _ = b + (a - b)/2 := by ring
  linarith [hcon, h N]


-- For exercise 2
lemma tends_to_ge_of_ge {x : RealSeq} {a b : ℝ} (hx : TendsTo x a) (h : ∀ n, x n ≥ b) :
    a ≥ b := by
  by_contra! hba
  let ε := (b - a) / 2
  obtain ⟨N, hN⟩ := hx ε (by positivity)
  specialize hN N (le_refl N)
  apply abs_lt.mp at hN
  have hcon: x N < b - ε := by
    calc _
      x N < a + ε := by linarith [hN]
      _ = a - b + b + ε  := by linarith
      _ = b + a - b + (b - a)/2 := by ring
      _ = b - (b - a)/2 := by ring
  linarith [hcon, h N]


end MySequences

/-!
## Exercise 1: continuous functions
-/
namespace MyFunctions

/-
Use `continuous_at_iff_seq_continuous_at` for the exercise.
You may find `Function.comp_apply` useful when simplifying compositions.
-/
lemma continuous_comp_of_continuous {f g : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousAt f a) (hg : ContinuousAt g (f a)) :
    ContinuousAt (g ∘ f) a := by
  rw [continuous_at_iff_seq_continuous_at] at *
  exact fun x hx => hg  ⟨fun n => f (x n)⟩ (hf x hx)

/-
Use the above lemma to prove that the sum of two continuous functions is continuous.
-/
lemma continuous_sum_of_continuous {f g : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousAt f a) (hg : ContinuousAt g a) :
    ContinuousAt (f + g) a := by
  rw [continuous_at_iff_seq_continuous_at]
  intro x hx
  rw [continuous_at_iff_seq_continuous_at] at hf hg
  exact tends_to_add (hf x hx) (hg x hx)


end MyFunctions

/-!
## Exercise 2: the least-upper-bound property
-/

/-
Do not use `sSup`, `le_csSup`, or `csSup_le` in this exercise. The aim is to
derive the least-upper-bound property from Cauchy completeness.

Use a bisection construction:

1) Choose `l₀ ∈ S` using `hS`, and choose an upper bound `u₀` using `hbdd`.
   Thus `l₀ ≤ u₀`.

2) Recursively bisect the interval `[lₙ, uₙ]`. Let
   `mₙ = (lₙ + uₙ) / 2`.

   * If `mₙ ∈ upperBounds S`, set `lₙ₊₁ = lₙ` and `uₙ₊₁ = mₙ`.
   * Otherwise, there is some `y ∈ S` with `mₙ < y`. Choose such a `y`,
     set `lₙ₊₁ = y`, and keep `uₙ₊₁ = uₙ`.

   You'll need `classical` to make these choices.

3) Prove by induction that:

   * `lₙ ∈ S`;
   * `uₙ ∈ upperBounds S`;
   * the intervals are nested; and
   * `uₙ - lₙ ≤ (u₀ - l₀) / 2^n`.

4) Deduce that `⟨l⟩ : RealSeq` is Cauchy. For sufficiently large `N`,
   every `lₙ` with `n ≥ N` lies in `[l_N, u_N]`, whose length tends to
   zero. The lemmas `exists_pow_lt_of_lt_one` and `one_half_lt_one` may
   help with the powers of `1 / 2`.

5) Apply `MySequences.real_numbers_complete` from last time to obtain a real number `a` to which
   `l` converges. This `a` will be the supremum; do not identify it with
   the library term `sSup S`.

6) Use the two lemmas above about limits to show that `a` satisfied the least-upper-bound property.
Hint: a is also the limit of the sequence `u`.

7) Prove the at least one of the lemmas about limits above.
-/

lemma exists_of_ne_up {S : Set ℝ} (u : ℝ) (hu : ¬ u ∈ upperBounds S) :
    ∃ y ∈ S, u < y := by
  by_contra! h
  exact hu h

open scoped Classical in
noncomputable def pointAbove {S : Set ℝ} (u : ℝ) (hu : ¬ u ∈ upperBounds S) :
    {y : ℝ | y ∈ S ∧ u < y} :=
  ⟨Classical.choose (exists_of_ne_up u hu), Classical.choose_spec (exists_of_ne_up u hu)⟩

-- If you don't want to use Nat.rec, you can also define this function recursively using pattern matching.
open scoped Classical in
noncomputable def boundary {S : Set ℝ} (l : S) (u : upperBounds S) : ℕ → ℝ × ℝ
  | 0 => (l, u)
  | n + 1 =>
    let mid := (boundary l u n).1 + (boundary l u n).2 / 2
    if hmid : mid ∈ upperBounds S then ((boundary l u n).1, mid)
    else ((pointAbove mid hmid).val, (boundary l u n).2)

lemma exercise2 {S : Set ℝ} (hS : S.Nonempty) (v : upperBounds S) :
    ∃ sup : upperBounds S, ∀ b : upperBounds S, sup ≤ b := by
  by_cases hup : v.val ∈ S
  · exact ⟨v, fun b => b.2 hup⟩
  classical
  let ⟨l₀ , hl₀⟩ := hS
  let u₀ := v
  let bdds : ℕ → ℝ × ℝ := Nat.rec (l₀, u₀) fun _ prev =>
    let mid := (prev.1 + prev.2)/2
    if hu : mid ∈ upperBounds S then (prev.1, mid)
    else (pointAbove mid hu, prev.2)
  let l : ℕ → ℝ := fun n => (bdds n).1
  let u : ℕ → ℝ := fun n => (bdds n).2
  have hlmem : ∀ n, l n ∈ S := by
    intro n
    induction n with
    | zero => exact hl₀
    | succ n ih =>
      simp only [l, bdds]
      split_ifs with h
      · exact Set.mem_preimage.mp ih
      exact (pointAbove (((bdds n).1 + (bdds n).2)/2) h).2.1
  have humem : ∀ n, u n ∈ upperBounds S := by
    intro n
    induction n with
    | zero => simp only [Set.mem_setOf_eq, Nat.rec_zero, Subtype.coe_prop, u, bdds]
    | succ n ih =>
      simp only [u, bdds]
      split_ifs with h
      · exact h
      exact ih
  have hneq : u₀ - l₀ > 0 := by
      simp only [gt_iff_lt, sub_pos]
      refine Std.lt_iff_le_and_ne.mpr ⟨v.2 hl₀, ?_⟩
      intro h
      rw[← h] at hup
      exact hup hl₀
  have hdiff : ∀ n, u n - l n ≤ (u₀ - l₀) / 2 ^ n := by
    intro n
    induction n with
    | zero => simp only [Set.mem_setOf_eq, Nat.rec_zero, pow_zero, div_one, Std.le_refl, u, bdds, l]
    | succ n ih =>
      simp only [u, l, bdds]
      split_ifs with h
      · simp only [tsub_le_iff_right]
        refine (div_le_iff₀ ?_).mpr ?_
        · positivity
        calc (bdds n).1 + (bdds n).2 ≤ u n - l n + 2*(bdds n).1 := by simp [u, l]; group; linarith
        _ ≤ (↑u₀ - l₀) / 2 ^ (n) + ((bdds n).1) * 2 := by linarith [ih]
        _ = ((↑u₀ - l₀) / 2 ^ (n+1) + ((bdds n).1)) * 2 := by ring
      simp only [Set.mem_setOf_eq, tsub_le_iff_right]
      calc (bdds n).2 = 1/2*(u n - l n + (((bdds n).1 + (bdds n).2))) := by simp [u, l]; ring
      _ ≤ 1/2 *((↑u₀ - l₀) / 2 ^ (n) + ((bdds n).1 + (bdds n).2)) := by linarith [ih]
      _ = (↑u₀ - l₀) / 2 ^ (n + 1) + (((bdds n).1 + (bdds n).2) / 2) := by ring
      _ ≤ (↑u₀ - l₀) / 2 ^ (n + 1) + ↑(pointAbove (((bdds n).1 + (bdds n).2) / 2) h) :=
        by linarith [((pointAbove (((bdds n).1 + (bdds n).2) / 2) h)).2.2]
  have hdifflim : TendsTo ⟨u - l⟩ 0 := by
    intro ε hε
    obtain ⟨N, hN⟩ := @exists_pow_lt_of_lt_one _ _ _ _ _ (ε/(u₀ - l₀)) (1/2 : ℝ) _ (by positivity)
      (by linarith)
    use N
    intro n hn
    calc dist (u n - l n) 0 = u n - l n := by
          simp only [dist_zero_right, Real.norm_eq_abs, abs_eq_self, sub_nonneg]
          exact humem n (hlmem n)
    _ ≤ (u₀ - l₀) / 2 ^ n := by exact hdiff n
    _ ≤ (u₀ - l₀) / 2 ^ N := by
      apply (div_le_div_iff_of_pos_left hneq (by positivity) (by positivity)).mpr
      exact (pow_le_pow_iff_right₀ (one_lt_two)).mpr hn
    _ < ε := by
      rw[lt_div_iff₀, mul_comm] at hN
      · ring_nf at hN
        simp only [one_div, inv_pow] at hN
        ring_nf
        simp only [inv_pow, hN]
      exact hneq
  have hCauchy : IsCauchyReal ⟨l⟩ := by
    have hmon : Monotone l := by
      refine monotone_nat_of_le_succ ?_
      intro n
      simp only [l, bdds]
      split_ifs with h
      · exact le_of_eq rfl
      calc (bdds n).1 ≤ (((bdds n).1 + (bdds n).1) / 2) := by simp
      _ = (((bdds n).1 + (l n)) / 2) := by rfl
      _ ≤ (((bdds n).1 + (u n)) / 2) := by
        exact div_le_div_of_nonneg_right (by linarith [(humem n (hlmem n))]) (by positivity)
      _ ≤ ↑(pointAbove (((bdds n).1 + (bdds n).2) / 2) h) := by
        linarith [((pointAbove (((bdds n).1 + (bdds n).2) / 2) h)).2.2]
    intro ε hε
    obtain ⟨N, hN⟩ := hdifflim ε hε
    use N
    intro m hm n hn
    calc
      dist (l m) (l n) = |l n - l m| := by exact Metric.mem_sphere'.mp rfl
      _ ≤ u N - l N := by
        exact abs_sub_le_of_le_of_le (hmon hn) (humem N (hlmem n)) (hmon hm) (humem N (hlmem m))
      _ = |(u N - l N) - 0| := by
        simp only [sub_zero]
        exact Eq.symm (abs_of_nonneg (sub_nonneg_of_le (humem N (hlmem N))))
      _ < ε := by exact hN N (le_refl N)
  have ⟨a, ha⟩ := MySequences.real_numbers_complete hCauchy
  use ⟨a, ?_⟩
  · intro b
    apply tends_to_le_of_le ha
    exact fun n => b.2 (hlmem n)
  have ha' : TendsTo ⟨u⟩ a := by
    rw[show u = (u - l) + l by simp only [sub_add_cancel]]
    simpa only [sub_add_cancel, Pi.sub_apply, zero_add] using tends_to_add hdifflim ha
  intro s hs
  apply tends_to_ge_of_ge ha'
  exact fun n => (humem n) hs

/-
Bonus! think about how to prove that every real number has a decimal expansion.
Hint: Use the floor function and look at `Σ'` and `HasSum`.
-/
