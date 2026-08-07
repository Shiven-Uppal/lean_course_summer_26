import LectureNotes.lecture8.examples8

open MySequences Function

namespace MyFunctions

/-
Exercise 1: Finish the proof of the Leibniz rule, i.e., `deriv_mul`.
Hint: Calc and limit laws and `continuous_at_iff_tends_to`.
-/

/-
Use exercise1 to show compute the derivative of monomial functions.
Hint: Induction on n.
-/
lemma HasDeriv.congr_deriv {f f' f'' : ℝ → ℝ} (hderiv : HasDeriv f f') (heq : f' = f'') :
  HasDeriv f f'' := by
  rw[heq] at hderiv
  exact hderiv

lemma deriv_power (n : ℕ) : HasDeriv (fun x => x ^ n) (fun x : ℝ => n * x ^ (n - 1)) := by
  induction n with
  | zero => simp only [pow_zero, CharP.cast_eq_zero, zero_tsub, mul_one]
            exact deriv_const 1
  | succ n ih =>
  by_cases hn : n = 0
  · rw[hn]
    have hd := deriv_affine 1 0
    simp only [one_mul, add_zero, const_one, zero_add, pow_one, Nat.cast_one, tsub_self, pow_zero,
      mul_one] at *
    exact hd
  have hmul := deriv_mul (⟨fun x => 1, deriv_affine 1 0⟩) (⟨fun x => n * x ^ (n - 1), ih⟩)
  have hprod : (fun x => x ^ (n + 1) : ℝ → ℝ )= (fun x => 1*x + 0) * (fun x => (x ^ n)) :=
    by ext x; rw [Pi.mul_apply]; ring
  rw[← deriv_of_has_deriv ih, ← deriv_of_has_deriv (deriv_affine 1 0), ← hprod] at hmul
  apply hmul.congr_deriv
  ext x
  simp only [const_one, one_mul, add_zero, Pi.add_apply, Pi.mul_apply, Nat.cast_add, Nat.cast_one,
    add_tsub_cancel_right]
  ring_nf
  rw[add_comm, mul_pow_sub_one hn x]

/-
Prove the fact that the derivate vanishes at a local minimum.
Hint: Use the corresponding fact for a local maximum and the fact that `deriv (-f) = -deriv f`.
-/

lemma max_minus_of_min {f : ℝ → ℝ} {x : ℝ} {S : Set ℝ}
    (hf : IsMinOn f S x) : IsMaxOn (-f) S x := by
  intro s hs
  change -(f s) ≤ -(f x)
  exact neg_le_neg_iff.mpr (hf hs)

theorem deriv_at_min_zero {f : ℝ → ℝ} {x ε : ℝ} (hε : ε > 0)
    (hf : IsMinOn f (Set.Ioo (x - ε) (x + ε)) x) : deriv f x = 0 := by
  by_cases h : ∃ f', HasDerivAt f f' x
  · obtain ⟨_, hf'⟩ := h
    rw[deriv_eq_of_has_deriv hf'] at hf'
    have hd' := deriv_eq_of_has_deriv (deriv_mul_at ((deriv_const (-1)) x) hf')
    simp only [const_apply, zero_mul, neg_mul, one_mul, zero_add] at hd'
    calc
      deriv f x = -(-deriv (f) x) := by group
      _ = -(deriv (const ℝ (-1) * f) x) := by rw[hd']
      _ = -(deriv (-f) x) := by
          refine neg_inj.mpr (congrFun (congrArg deriv ?_) x) -- new tactic!
          ext y
          simp only [Pi.mul_apply, const_apply, neg_mul, one_mul, Pi.neg_apply]
      _ = 0 := by rw[deriv_at_max_zero hε (max_minus_of_min hf), neg_zero]
  simp only [deriv, h, ↓reduceDIte]

/-
Use the theorem `deriv_at_max_zero` and the theorems below
to prove Rolle's theorem from the lecture.
-/
theorem max_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ContinuousOn f) :
    ∃ x ∈ Set.Icc a b, IsMaxOn f (Set.Icc a b) x := by
  sorry -- You don't have to prove this! This corresponds to `isCompact_Icc.exists_isMaxOn`.

theorem min_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ContinuousOn f) :
    ∃ x ∈ Set.Icc a b, IsMinOn f (Set.Icc a b) x := by
  sorry -- You don't have to prove this! This corresponds to `isCompact_Icc.exists_isMinOn`.

lemma interval_nbhd {x a b : ℝ} (hx : x ∈ Set.Ioo a b) :
    ∃ ε > 0, Set.Ioo (x - ε) (x + ε) ⊆ Set.Icc a b := by
  obtain ⟨ε, hε, hsub⟩ :=
    Metric.isOpen_iff.mp isOpen_Ioo x hx
  refine ⟨ε, hε, ?_⟩
  rw [← Real.ball_eq_Ioo]
  exact hsub.trans Set.Ioo_subset_Icc_self

lemma deriv_zero_of_max_eq_min {f : ℝ → ℝ} {x a b : ℝ}
    (hf : IsMaxOn f (Set.Icc a b) x) (hg : IsMinOn f (Set.Icc a b) x) :
    ∀ y ∈ Set.Ioo a b, deriv f y = 0 := by
  intro y hy
  have hm : IsMaxOn f (Set.Icc a b) y := by
    have hxy : f y = f x := by
      exact eq_of_ge_of_le (hg (Set.Ioo_subset_Icc_self hy)) (hf (Set.Ioo_subset_Icc_self hy))
    intro z hz
    rw[hxy]
    exact hf hz
  have ⟨ε, hε, hsubset⟩ := interval_nbhd hy
  exact deriv_at_max_zero hε (IsMaxOn.on_subset hm hsubset)

lemma mem_Ioo_of_mem_Icc {a b x : ℝ} (hx : x ∈ Set.Icc a b) (ha : x ≠ a) (hb : x ≠ b) :
    x ∈ Set.Ioo a b := by
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc hx with h1 | h2 | h3
  · contradiction
  · contradiction
  · exact h3

lemma satz_von_rolle {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : Differentiable f) (h : f a = f b) :
    ∃ x ∈ Set.Ioo a b, deriv f x = 0 := by
  have ⟨m, hm, hmax⟩ := max_value_theorem hab (continuous_of_differentiable hf)
  have ⟨n, hn, hmin⟩ := min_value_theorem hab (continuous_of_differentiable hf)
  obtain ⟨y, hy⟩ := Set.nonempty_Ioo.mpr hab -- We use this point if the function is constant.
  by_cases hmn : m = a ∧ n = b ∨ m = b ∧ n = a
  · have hmn' : f m = f n := by
      rcases hmn with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw[ha, hb, h]
      rw[ha, hb, h]
    use y, hy
    refine deriv_zero_of_max_eq_min hmax ?_ _ hy
    intro x hx
    rw[hmn']
    exact hmin hx
  push Not at hmn
  by_cases hma : m = a ∨ m = b
  · rcases hma with ha | hb
    · by_cases hna : n = a
      · rw[ha] at hmax
        rw[hna] at hmin
        use y, hy
        exact deriv_zero_of_max_eq_min hmax hmin _ hy
      have hnioo : n ∈ Set.Ioo a b := mem_Ioo_of_mem_Icc hn hna (hmn.1 ha)
      use n, hnioo
      have ⟨ε, he, hsub⟩ := interval_nbhd hnioo
      exact deriv_at_min_zero he (IsMinOn.on_subset hmin hsub)
    · by_cases hna : n = b
      · rw[hb] at hmax
        rw[hna] at hmin
        use y, hy
        exact deriv_zero_of_max_eq_min hmax hmin _ hy
      have hnioo : n ∈ Set.Ioo a b := mem_Ioo_of_mem_Icc hn (hmn.2 hb) hna
      use n, hnioo
      have ⟨ε, he, hsub⟩ := interval_nbhd hnioo
      exact deriv_at_min_zero he (IsMinOn.on_subset hmin hsub)
  push Not at hma
  have hmioo : m ∈ Set.Ioo a b := mem_Ioo_of_mem_Icc hm hma.1 hma.2
  use m, hmioo
  have ⟨ε, he, hsub⟩ := interval_nbhd hmioo
  exact deriv_at_max_zero he (IsMaxOn.on_subset hmax hsub)

/-
Finally, use the lemma above to prove the main theorem.
-/
theorem mean_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : Differentiable f)
    : ∃ x ∈ Set.Ioo a b, deriv f x = (f b - f a) / (b - a) := by
  let g := f + (const ℝ (-(f b - f a) / (b - a))) * (fun x => 1*x - a)
  have hgend : g a = g b := by
    simp only [neg_sub, one_mul, Pi.add_apply, Pi.mul_apply, const_apply, sub_self, mul_zero,
      add_zero, g]
    rw[div_mul_cancel₀ _ (by linarith)]
    simp only [add_sub_cancel]
  have hdiffg : Differentiable g := by
    use deriv f + deriv ((const ℝ (-(f b - f a) / (b - a))) * (fun x => 1*x - a))
    refine deriv_add (hf) ?_
    exact ⟨_, deriv_mul ⟨const _ 0, deriv_const (-(f b - f a) / (b - a))⟩ ⟨_, deriv_affine 1 (-a)⟩⟩
  obtain ⟨x, hx, hderiv⟩ := satz_von_rolle hab hdiffg hgend
  use x, hx
  calc
    deriv f x = deriv (g + (const ℝ ((f b - f a) / (b - a))) * (fun x => 1*x + (-a))) x := by
      apply congrFun (congrArg deriv ?_) x
      ext x
      simp only [neg_sub, Pi.add_apply, Pi.mul_apply, const_apply, g]
      group
    _ = deriv g x + deriv ((const ℝ ((f b - f a) / (b - a))) * (fun x => 1*x + (-a))) x := by
      rw[← deriv_eq_of_has_deriv (deriv_add (hdiffg) (?_) x)]
      · rfl
      exact ⟨_, deriv_mul ⟨const _ 0, deriv_const ((f b - f a) / (b - a))⟩ ⟨_, deriv_affine 1 (-a)⟩⟩
    _ = (f b - f a) / (b - a) * deriv (fun x ↦ (1*x + (-a))) x := by
      rw[← deriv_eq_of_has_deriv (deriv_mul ⟨_, deriv_const ((f b - f a) / (b - a))⟩
        ⟨_, deriv_affine 1 (-a)⟩ x)]
      rw[← deriv_of_has_deriv (deriv_const ((f b - f a) / (b - a)))]
      simp only [const_zero, zero_mul, Pi.add_apply, Pi.ofNat_apply, Pi.mul_apply,
        const_apply, zero_add, add_eq_right]
      exact hderiv
    _ = (f b - f a) / (b - a) * deriv (fun x ↦ 1*x + (-a)) x := by
      simp
    _ = (f b - f a) / (b - a) := by
      rw[← deriv_of_has_deriv (deriv_affine 1 (-a))]
      simp only [const_apply, mul_one]

end MyFunctions

/-
Bonus exercise:
1) Show that every sequence with values in a closed interval has a convergent subsequence.
2) Prove the max_value_theorem.
-/

-- We've used this many times. You can leave this for last.
lemma limit_of_nested_intervals {a b : ℕ → ℝ} {x : RealSeq} (hx : ∀ n, x n ∈ Set.Icc (a n) (b n))
    (hnset : ∀ n, Set.Icc (a (n + 1)) (b (n + 1)) ⊆ Set.Icc (a n) (b n))
    (hlim : MySequences.TendsTo ⟨(b - a)⟩ 0) :
    ∃ c, TendsTo x c ∧ ∀ n : ℕ, c ∈ Set.Icc (a n) (b n) := by
  sorry

/-
Hint: Try to build a sequence of nested intervals containing a subsequence. Then apply the lemma.
Note a < b is automatic (otherwise you get a contradiction)
-/
theorem convergent_subsequence_of_bounded {x : RealSeq} {a b : ℝ} (hx : ∀ n, x n ∈ Set.Icc a b) :
    ∃ σ : ℕ → ℕ, ∃ c : Set.Icc a b, TendsTo ⟨(x ∘ σ)⟩ c := by
  sorry
