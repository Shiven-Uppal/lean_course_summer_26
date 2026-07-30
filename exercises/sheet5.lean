import LectureNotes.lecture6.examples6

open MySequences


/-
Hint: Use the above fact about the ceiling of a real number to find a rational number between 0 and ε.
Find a useful theorem below.
-/

example (x : ℝ) : ⌈x⌉ ≥ x := by exact Int.le_ceil x

#check one_div_le

theorem exercise1 {ε : ℝ} (hε : ε > 0) : ∃ δ : ℕ , δ > 0 ∧ (1 / δ) ≤ ε := by
  by_cases h : ε ≤ 1
  · let δ : ℕ := ⌈1 / ε⌉.toNat
    use δ
    have hquotient : 0 < 1 / ε := by
      positivity
    have hceilpos : 0 < ⌈1 / ε⌉ := by
      exact (Int.ceil_pos).mpr hquotient
    have hδeq : (δ : ℤ) = ⌈1 / ε⌉ := by
      exact Int.toNat_of_nonneg (le_of_lt hceilpos)
    have hδpos : 0 < δ := by
      have hδint : (0 : ℤ) < (δ : ℤ) := by
        rw [hδeq]
        exact hceilpos
      exact_mod_cast hδint
    constructor
    · exact hδpos
    · have hδreal : (0 : ℝ) < δ := by
        exact_mod_cast hδpos
      exact (one_div_le hδreal hε).mpr (by
        calc
          1 / ε ≤ (⌈1 / ε⌉ : ℤ) := by
            exact Int.le_ceil (1 / ε)
          _ = (δ : ℝ) := by
            exact_mod_cast hδeq.symm)
  · use 1
    constructor
    · norm_num
    · norm_num
      exact le_of_lt (lt_of_not_ge h)

/-
Show that convergence can be expressed in terms of rational numbers. Use the above exercise.
-/
theorem exericse2 {x : RealSeq} (a : ℝ) (hx : ∀ δ : ℕ, δ > 0 → ∃ N, ∀ n≥ N, dist (x n) a < 1 / δ)
  : tends_toReal x a := by
  intro ε hε
  obtain ⟨δ, hδpos, hδε⟩ := exercise1 hε
  obtain ⟨N, hN⟩ := hx δ hδpos
  use N
  intro n hn
  exact lt_of_lt_of_le (hN n hn) hδε

/-
Show that rational Cauchy sequences are also Cauchy sequences of real numbers and vice versa.
Hint below:
-/
#check Rat.dist_cast

theorem exercise3 {x : RatSeq} : isCauchy x ↔ isCauchyReal x := by
  constructor
  · intro hx ε hε
    obtain ⟨N, hN⟩ := hx ε hε
    use N
    intro m hm n hn
    exact_mod_cast hN m hm n hn
  · intro hx ε hε
    have hεreal : (0 : ℝ) < ε := by
      exact_mod_cast hε
    obtain ⟨N, hN⟩ := hx ε hεreal
    use N
    intro m hm n hn
    exact_mod_cast hN m hm n hn


/-
Finally, show that convergent sequences are Cauchy sequences.
-/
theorem exercise4 {x : RealSeq} (a : ℝ) (hx : tends_toReal x a) : isCauchyReal x := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx (ε / 2) (half_pos hε)
  use N
  intro m hm n hn
  calc
    dist (x m) (x n)
        ≤ dist (x m) a + dist a (x n) := by
          exact dist_triangle (x m) a (x n)
    _ < ε / 2 + ε / 2 := by
          apply add_lt_add
          · exact hN m hm
          · rw [dist_comm]
            exact hN n hn
    _ = ε := by
          ring
/-
Finally, define a sequence of real numbers that does not converge.
-/

def my_diverging_sequence : RealSeq where
  x n := n

theorem exercise5 : ¬ ∃ a : ℝ, tends_toReal my_diverging_sequence a := by
  intro h
  obtain ⟨a, ha⟩ := h
  obtain ⟨N, hN⟩ := ha (1 / 2) (by norm_num)
  have h1 :
      dist (my_diverging_sequence N) a < 1 / 2 := by
    exact hN N (by omega)
  have h2 :
      dist (my_diverging_sequence (N + 1)) a < 1 / 2 := by
    exact hN (N + 1) (by omega)
  have hdist :
      dist (my_diverging_sequence N)
        (my_diverging_sequence (N + 1)) < 1 := by
    calc
      dist (my_diverging_sequence N)
          (my_diverging_sequence (N + 1))
          ≤ dist (my_diverging_sequence N) a +
              dist a (my_diverging_sequence (N + 1)) := by
                exact dist_triangle
                  (my_diverging_sequence N) a
                  (my_diverging_sequence (N + 1))
      _ < 1 / 2 + 1 / 2 := by
            apply add_lt_add
            · exact h1
            · rw [dist_comm]
              exact h2
      _ = 1 := by
            norm_num
  have heq :
      dist (my_diverging_sequence N)
        (my_diverging_sequence (N + 1)) = 1 := by
    simp [my_diverging_sequence, Real.dist_eq]
  rw [heq] at hdist
  exact (lt_self_iff_false 1).mp hdist
