import LectureNotes.lecture7.examples7

open MyFunctions MySequences

namespace MySequences

/-!
## Lemmas for sequences
-/

/-- The sum of two convergent sequences converges to the sum of their limits. -/
lemma tends_to_add {x y : RealSeq} {a b : ℝ}
    (hx : tends_to x a) (hy : tends_to y b) :
    tends_to ⟨fun n ↦ x n + y n⟩ (a + b) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx (ε / 2) (half_pos hε)
  obtain ⟨M, hM⟩ := hy (ε / 2) (half_pos hε)
  use max N M
  intro n hn
  calc
    dist (x n + y n) (a + b)
        ≤ dist (x n) a + dist (y n) b := dist_add_add_le _ _ _ _
    _ < ε / 2 + ε / 2 := by
      exact add_lt_add
        (hN n (le_trans (le_max_left N M) hn))
        (hM n (le_trans (le_max_right N M) hn))
    _ = ε := add_halves ε

-- For exercise 2
lemma tends_to_le_of_le {x : RealSeq} {a b : ℝ} (hx : tends_to x a) (h : ∀ n, x n ≤ b) :
    a ≤ b := by
  by_contra hab
  push Not at hab
  obtain ⟨N, hN⟩ := hx ((a - b) / 2) (by linarith)
  have hdist := hN N (le_rfl)
  rw [Real.dist_eq, abs_of_nonpos (by linarith [h N])] at hdist
  linarith [h N]

-- For exercise 2
lemma tends_to_ge_of_ge {x : RealSeq} {a b : ℝ} (hx : tends_to x a) (h : ∀ n, x n ≥ b) :
    a ≥ b := by
  by_contra hab
  push Not at hab
  obtain ⟨N, hN⟩ := hx ((b - a) / 2) (by linarith)
  have hdist := hN N (le_rfl)
  rw [Real.dist_eq, abs_of_nonneg (by linarith [h N])] at hdist
  linarith [h N]

end MySequences

/-!
## Exercise 1: continuous functions
-/
namespace MyFunctions

/-
Use `continuousAt_iff_seqContinuousAt` for the exercise.
You may find `Function.comp_apply` useful when simplifying compositions.
-/
lemma continuous_comp_of_continuous {f g : ℝ → ℝ} {a : ℝ}
    (hf : continuousAt f a) (hg : continuousAt g (f a)) :
    continuousAt (g ∘ f) a := by
  rw [continuousAt_iff_seqContinuousAt] at hf hg ⊢
  intro x hx
  simpa [Function.comp_apply] using
    hg ⟨fun n ↦ f (x n)⟩ (hf x hx)

/-
Use the above lemma to prove that the sum of two continuous functions is continuous.
-/
lemma continuous_sum_of_continuous {f g : ℝ → ℝ} {a : ℝ}
    (hf : continuousAt f a) (hg : continuousAt g a) :
    continuousAt (f + g) a := by
  rw [continuousAt_iff_seqContinuousAt] at hf hg ⊢
  intro x hx
  simpa [Pi.add_apply] using
    tends_to_add (hf x hx) (hg x hx)

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

lemma exercise2 {S : Set ℝ} (hS : S.Nonempty) (u : upperBounds S) :
    ∃ sup : upperBounds S, ∀ b : upperBounds S, sup ≤ b := by
  classical
  obtain ⟨l₀, hl₀⟩ := hS
  have hnot_upper {c : ℝ} (hc : c ∉ upperBounds S) :
      ∃ y : S, c < y := by
    change ¬ ∀ ⦃y : ℝ⦄, y ∈ S → y ≤ c at hc
    push Not at hc
    obtain ⟨y, hyS, hcy⟩ := hc
    exact ⟨⟨y, hyS⟩, hcy⟩
  let I := {p : ℝ × ℝ // p.1 ∈ S ∧ p.2 ∈ upperBounds S}
  let p₀ : I :=
    ⟨(l₀, (u : ℝ)), hl₀, u.2⟩
  let step : I → I := fun p =>
    if hm : (p.1.1 + p.1.2) / 2 ∈ upperBounds S then
      ⟨(p.1.1, (p.1.1 + p.1.2) / 2), p.2.1, hm⟩
    else
      let y : S := Classical.choose (hnot_upper hm)
      ⟨((y : ℝ), p.1.2), y.2, p.2.2⟩
  let p : ℕ → I :=
    fun n ↦ Nat.rec p₀ (fun _ pn ↦ step pn) n
  let l : ℕ → ℝ := fun n ↦ (p n).1.1
  let v : ℕ → ℝ := fun n ↦ (p n).1.2
  have hp_succ (n : ℕ) :
      p (n + 1) = step (p n) := by
    simp [p]
  have hlS (n : ℕ) : l n ∈ S :=
    (p n).2.1
  have hvub (n : ℕ) : v n ∈ upperBounds S :=
    (p n).2.2
  have hlu (n : ℕ) : l n ≤ v n :=
    hvub n (hlS n)
  have hl_step (n : ℕ) : l n ≤ l (n + 1) := by
    change (p n).1.1 ≤ (p (n + 1)).1.1
    rw [hp_succ]
    simp only [step]
    split_ifs with hm
    · exact le_rfl
    · have hmid :
          (p n).1.1 ≤ ((p n).1.1 + (p n).1.2) / 2 := by
        have h := hlu n
        change (p n).1.1 ≤ (p n).1.2 at h
        linarith
      exact hmid.trans (Classical.choose_spec (hnot_upper hm)).le
  have hv_step (n : ℕ) : v (n + 1) ≤ v n := by
    change (p (n + 1)).1.2 ≤ (p n).1.2
    rw [hp_succ]
    simp only [step]
    split_ifs with hm
    · have h := hlu n
      change (p n).1.1 ≤ (p n).1.2 at h
      linarith
    · exact le_rfl
  have hwidth_step (n : ℕ) :
      v (n + 1) - l (n + 1) ≤ (v n - l n) / 2 := by
    change
      (p (n + 1)).1.2 - (p (n + 1)).1.1 ≤
        ((p n).1.2 - (p n).1.1) / 2
    rw [hp_succ]
    simp only [step]
    split_ifs with hm
    · linarith
    · have hy := Classical.choose_spec (hnot_upper hm)
      linarith
  have hl_mono : Monotone l :=
    monotone_nat_of_le_succ hl_step
  have hv_anti : Antitone v :=
    antitone_nat_of_succ_le hv_step
  have hwidth (n : ℕ) :
      v n - l n ≤ ((u : ℝ) - l₀) / (2 : ℝ) ^ n := by
    induction n with
    | zero =>
        simp [l, v, p, p₀]
    | succ n ih =>
        calc
          v (n + 1) - l (n + 1)
              ≤ (v n - l n) / 2 := hwidth_step n
          _ ≤ (((u : ℝ) - l₀) / (2 : ℝ) ^ n) / 2 := by
            linarith
          _ = ((u : ℝ) - l₀) / (2 : ℝ) ^ (n + 1) := by
            rw [pow_succ, div_div]
  have hshrink (ε : ℝ) (hε : 0 < ε) :
      ∃ N, ((u : ℝ) - l₀) / (2 : ℝ) ^ N < ε := by
    by_cases h : (u : ℝ) = l₀
    · exact ⟨0, by simp [h, hε]⟩
    · have hD : 0 < (u : ℝ) - l₀ := by
        exact sub_pos.mpr
          (lt_of_le_of_ne (u.2 hl₀) (Ne.symm h))
      obtain ⟨N, hN⟩ :=
        exists_pow_lt_of_lt_one
          (x := ε / ((u : ℝ) - l₀))
          (y := (1 / 2 : ℝ))
          (div_pos hε hD)
          one_half_lt_one
      refine ⟨N, ?_⟩
      calc
        ((u : ℝ) - l₀) / (2 : ℝ) ^ N
            = ((u : ℝ) - l₀) * (1 / 2 : ℝ) ^ N := by
              simp [div_eq_mul_inv]
        _ < ((u : ℝ) - l₀) *
              (ε / ((u : ℝ) - l₀)) :=
          mul_lt_mul_of_pos_left hN hD
        _ = ε := by
          field_simp [ne_of_gt hD]

  have hl_cauchy : isCauchyReal ⟨l⟩ := by
    intro ε hε
    obtain ⟨N, hN⟩ := hshrink ε hε
    use N
    intro m hm n hn
    have hlNm : l N ≤ l m := hl_mono hm
    have hlNn : l N ≤ l n := hl_mono hn
    have hmV : l m ≤ v N := hvub N (hlS m)
    have hnV : l n ≤ v N := hvub N (hlS n)
    calc
      dist (l m) (l n) = |l m - l n| := rfl
      _ ≤ v N - l N := by
        apply abs_le.mpr
        constructor <;> linarith
      _ ≤ ((u : ℝ) - l₀) / (2 : ℝ) ^ N :=
        hwidth N
      _ < ε := hN
  obtain ⟨a, ha⟩ :=
    real_numbers_complete hl_cauchy
  have hgap :
      tends_to ⟨fun n ↦ v n - l n⟩ 0 := by
    intro ε hε
    obtain ⟨N, hN⟩ := hshrink ε hε
    use N
    intro n hn
    have hvn : v n ≤ v N := hv_anti hn
    have hln : l N ≤ l n := hl_mono hn
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (sub_nonneg.mpr (hlu n))]
    calc
      v n - l n ≤ v N - l N := by
        linarith
      _ ≤ ((u : ℝ) - l₀) / (2 : ℝ) ^ N :=
        hwidth N
      _ < ε := hN
  have hv_tends : tends_to ⟨v⟩ a := by
    simpa using tends_to_add ha hgap
  refine ⟨⟨a, ?_⟩, ?_⟩
  · intro y hy
    exact tends_to_ge_of_ge hv_tends
      (fun n ↦ hvub n hy)
  · intro b
    change a ≤ (b : ℝ)
    exact tends_to_le_of_le ha
      (fun n ↦ b.2 (hlS n))


/-
Bonus! think about how to prove that every real number has a decimal expansion.
Hint: Use the floor function and look at `Σ'` and `HasSum`.
-/
