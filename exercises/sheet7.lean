import LectureNotes.lecture8.examples8

open MyFunctions MySequences Function

/-
Exercise 1: Finish the proof of the Leibniz rule, i.e., `deriv_mul`.
Hint: Calc and limit laws and `continuous_at_iff_tends_to`.
-/

/-
Use exercise1 to show compute the derivative of monomial functions.
Hint: Induction on n.
-/
lemma deriv_power (n : ℕ) : deriv (fun x => x ^ n) = fun x : ℝ => n * x ^ (n - 1) := by
  have h :
      HasDeriv (fun x : ℝ => x ^ n)
        (fun x : ℝ => n * x ^ (n - 1)) := by
    induction n with
    | zero =>
        convert deriv_const 1 using 1 <;> ext x <;> simp
    | succ n ih =>
        have hx :
            HasDeriv (fun x : ℝ => x) (const ℝ 1) := by
          simpa using deriv_affine 1 0
        have hmul :=
          deriv_mul
            (f := fun x : ℝ => x ^ n)
            (g := fun x : ℝ => x)
            ⟨_, ih⟩
            ⟨_, hx⟩
        rw [← deriv_of_has_deriv ih,
          ← deriv_of_has_deriv hx] at hmul
        convert hmul using 1
        · ext x
          simp [pow_succ]
        · ext x
          cases n with
          | zero =>
              simp
          | succ n =>
              simp [pow_succ]
              ring
  exact (deriv_of_has_deriv h).symm

/-
Prove the fact that the derivate vanishes at a local minimum.
Hint: Use the corresponding fact for a local maximum and the fact that `deriv (-f) = -deriv f`.
-/
theorem deriv_at_min_zero {f : ℝ → ℝ} {x ε : ℝ} (hε : ε > 0)
  (hf : IsMinOn f (Set.Ioo (x - ε) (x + ε)) x) : deriv f x = 0 := by
  have hmax :
      IsMaxOn (-f) (Set.Ioo (x - ε) (x + ε)) x := by
    intro y hy
    change -f y ≤ -f x
    exact neg_le_neg (show f x ≤ f y from hf hy)
  by_cases h : ∃ f', HasDerivAt f f' x
  · obtain ⟨f', hf'⟩ := h
    have hneg : HasDerivAt (-f) (-f') x := by
      unfold HasDerivAt
      have hlim :=
        tends_to_mul_tends_to
          (const ℝ (-1))
          (fun y => (f y - f x) / (y - x))
          x (-1) f'
          (tends_to_const (-1) x)
          hf'
      convert hlim using 1
      · ext y
        simp only [Pi.neg_apply, const_apply]
        ring
      · ring
    have hzero := deriv_at_max_zero hε hmax
    rw [← deriv_eq_of_has_deriv f f' x hf']
    rw [← deriv_eq_of_has_deriv (-f) (-f') x hneg] at hzero
    linarith
  · simp only [deriv, h, ↓reduceDIte]

/-
Use the theorem `deriv_at_max_zero` and the theorems below
to prove Rolle's theorem from the lecture.
-/
theorem max_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ContinuousOn f) :
    ∃ x ∈ Set.Icc a b, IsMaxOn f (Set.Icc a b) x := by
  exact isCompact_Icc.exists_isMaxOn
    ⟨a, le_rfl, hab.le⟩
    (fun x _ =>
      (Metric.continuousAt_iff.mpr (hf x)).continuousWithinAt)

  -- You don't have to prove this! This corresponds to `isCompact_Icc.exists_isMaxOn`.

theorem min_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ContinuousOn f) :
    ∃ x ∈ Set.Icc a b, IsMinOn f (Set.Icc a b) x := by
  exact isCompact_Icc.exists_isMinOn
    ⟨a, le_rfl, hab.le⟩
    (fun x _ =>
      (Metric.continuousAt_iff.mpr (hf x)).continuousWithinAt)
    -- You don't have to prove this! This corresponds to `isCompact_Icc.exists_isMinOn`.

lemma satz_von_rolle {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : Differentiable f) (h : f a = f b) :
    ∃ x ∈ Set.Ioo a b, deriv f x = 0 := by
  have hlocal {c : ℝ} (hc : c ∈ Set.Ioo a b) :
      ∃ ε > 0,
        Set.Ioo (c - ε) (c + ε) ⊆ Set.Icc a b := by
    refine ⟨min (c - a) (b - c), ?_, ?_⟩
    · exact lt_min
        (sub_pos.mpr hc.1)
        (sub_pos.mpr hc.2)
    · intro y hy
      constructor
      · have hleft :
            a ≤ c - min (c - a) (b - c) := by
          linarith [min_le_left (c - a) (b - c)]
        exact hleft.trans hy.1.le
      · have hright :
            c + min (c - a) (b - c) ≤ b := by
          linarith [min_le_right (c - a) (b - c)]
        exact hy.2.le.trans hright
  obtain ⟨u, hu, humax⟩ :=
    max_value_theorem hab
      (continuous_of_differentiable hf)
  by_cases hu' : u ∈ Set.Ioo a b
  · obtain ⟨ε, hε, hsub⟩ := hlocal hu'
    refine ⟨u, hu', deriv_at_max_zero hε ?_⟩
    intro y hy
    exact humax (hsub hy)
  obtain ⟨v, hv, hvmin⟩ :=
    min_value_theorem hab
      (continuous_of_differentiable hf)
  by_cases hv' : v ∈ Set.Ioo a b
  · obtain ⟨ε, hε, hsub⟩ := hlocal hv'
    refine ⟨v, hv', deriv_at_min_zero hε ?_⟩
    intro y hy
    exact hvmin (hsub hy)
  have hend {c : ℝ} (hc : c ∈ Set.Icc a b)
      (hc' : c ∉ Set.Ioo a b) :
      c = a ∨ c = b := by
    by_cases hca : c = a
    · exact Or.inl hca
    · right
      apply le_antisymm hc.2
      by_contra hbc
      exact hc'
        ⟨lt_of_le_of_ne hc.1 (Ne.symm hca),
          lt_of_not_ge hbc⟩
  have huval : f u = f a := by
    rcases hend hu hu' with rfl | rfl
    · rfl
    · exact h.symm
  have hvval : f v = f a := by
    rcases hend hv hv' with rfl | rfl
    · rfl
    · exact h.symm
  let c := (a + b) / 2
  have hc : c ∈ Set.Ioo a b := by
    dsimp [c]
    constructor <;> linarith
  have hc' : c ∈ Set.Icc a b :=
    ⟨le_of_lt hc.1, le_of_lt hc.2⟩
  obtain ⟨ε, hε, hsub⟩ := hlocal hc
  refine ⟨c, hc, deriv_at_max_zero hε ?_⟩
  intro y hy
  calc
    f y ≤ f u := humax (hsub hy)
    _ = f a := huval
    _ = f v := hvval.symm
    _ ≤ f c := hvmin hc'

/-
Finally, use the lemma above to prove the main theorem.
-/
theorem mean_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : Differentiable f)
    : ∃ x ∈ Set.Ioo a b, deriv f x = (f b - f a) / (b - a) := by
  have hba : b - a ≠ 0 := by
    linarith
  let m := (f b - f a) / (b - a)
  let l : ℝ → ℝ := fun x => -m * x
  have hl' : HasDeriv l (const ℝ (-m)) := by
    simpa [l] using deriv_affine (-m) 0
  have hl : Differentiable l :=
    ⟨_, hl'⟩
  have hadd := deriv_add hf hl
  have hend : (f + l) a = (f + l) b := by
    simp only [Pi.add_apply]
    dsimp [l, m]
    field_simp [hba]
    ring
  obtain ⟨x, hx, hxzero⟩ :=
    satz_von_rolle hab ⟨_, hadd⟩ hend
  refine ⟨x, hx, ?_⟩
  rw [← deriv_of_has_deriv hadd] at hxzero
  rw [← deriv_of_has_deriv hl'] at hxzero
  simp only [Pi.add_apply, const_apply] at hxzero
  dsimp [m] at hxzero ⊢
  linarith

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
  have hnested {m n : ℕ} (hmn : m ≤ n) :
    Set.Icc (a n) (b n) ⊆ Set.Icc (a m) (b m) := by
    sorry
  have hcauchy : IsCauchyReal x := by
    intro ε hε
    obtain ⟨N, hN⟩ := hlim ε hε
    specialize hN N le_rfl
    use N
    intro m hm n hn
    have hxm : x m ∈ Set.Icc (a N) (b N) :=
      hnested hm (hx m)
    have hxn : x n ∈ Set.Icc (a N) (b N) :=
      hnested hn (hx n)
    sorry
  obtain ⟨c, hc⟩ :=
    real_numbers_complete hcauchy
  refine ⟨c, hc, ?_⟩
  intro n
  have htail :
      MySequences.TendsTo ⟨fun k => x (n + k)⟩ c := by
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    use N
    intro k hk
    sorry
  have hmem (k : ℕ) :
      x (n + k) ∈ Set.Icc (a n) (b n) := by
    sorry
  constructor
  · exact tends_to_ge_of_ge htail
      (fun k => (hmem k).1)
  · exact tends_to_le_of_le htail
      (fun k => (hmem k).2)

/-
Hint: Try to build a sequence of nested intervals containing a subsequence. Then apply the lemma.
Note a < b is automatic (otherwise you get a contradiction)
-/
theorem convergent_subsequence_of_bounded {x : RealSeq} {a b : ℝ} (hx : ∀ n, x n ∈ Set.Icc a b) :
    ∃ σ : ℕ → ℕ, ∃ c : Set.Icc a b, TendsTo ⟨(x ∘ σ)⟩ c := by
  sorry
