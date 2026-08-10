import LectureNotes.lecture9.examples9
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

open MySequences Filter


noncomputable section

namespace MyFunctions

def exp_seq (x : ℝ) : RealSeq := ⟨fun n => ∑ k ∈ Finset.range n, (x^k/ k.factorial)⟩

-- We're gonna use the ratio test to show that exp_seq is Cauchy.
#check IsCauSeq.series_ratio_test

-- copied from the complex case :)
theorem IsCauSeq_exp (x : ℝ) : IsCauSeq (abs : ℝ → ℝ) (exp_seq x) := by
  apply IsCauSeq.of_abv
  let ⟨n, hn⟩ := exists_nat_gt |x|
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (abs_nonneg _) hn
  apply IsCauSeq.series_ratio_test n (|x| / n)
    (by positivity)
    ((div_lt_one₀ hn0).mpr hn)
  intro m hm
  rw [abs_abs, abs_abs, Nat.factorial_succ, pow_succ', mul_comm m.succ, Nat.cast_mul,
    ← div_div, mul_div_assoc, mul_div_right_comm, abs_mul, abs_div, Nat.abs_cast]
  gcongr
  exact le_trans hm (Nat.le_succ _)

-- The definiton of the exponential function is the limit of the sequence of partial sums.
def exp (x : ℝ) : ℝ := CauSeq.lim ⟨_, IsCauSeq_exp x⟩

-- Pointwise convergence, holds by definition.
lemma tendsto_exp_seq (x : ℝ) : MySequences.TendsTo (exp_seq x) (exp x) :=
  CauSeq.equiv_lim ⟨_, IsCauSeq_exp x⟩

-- computation of exp 0
lemma exp_zero : exp 0 = 1 := by
  have hpartial : ∀ n ≥ 1, exp_seq 0 n = 1 := by
    intro n hn
    cases n with
    | zero => contradiction
    | succ n =>
        change (∑ k ∈ Finset.range (n + 1), (0 : ℝ) ^ k / k.factorial) = 1
        rw [Finset.sum_eq_single 0]
        · norm_num
        · intro k hk hk0
          simp only [zero_pow hk0, zero_div]
        · simp only [Finset.mem_range, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le,
          not_true_eq_false, pow_zero, Nat.factorial_zero, Nat.cast_one, ne_eq, one_ne_zero,
          not_false_eq_true, div_self, imp_self]
  apply tends_toReal_unique (tendsto_exp_seq 0)
  intro ε hε
  refine ⟨1, fun n hn => ?_⟩
  rw [hpartial n hn, dist_self]
  exact hε

-- uniform convergence with ε-δ-criterion
lemma tendsto_uniformly_iff {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {S : Set ℝ} :
  TendstoUniformlyOn f g atTop S ↔
  ∀ ε > 0, ∃ N, ∀ n≥ N, ∀ x ∈ S, dist (f n x) (g x) < ε := by
  rw [Metric.tendstoUniformlyOn_iff]
  simp only [eventually_atTop, dist_comm]

/-
uniform convergence of the derivates on every ball implies that
differentiation and taking the limit commute. -/
theorem hasDeriv_of_uniform_convergent {f f' : ℕ → ℝ → ℝ} (g g' : ℝ → ℝ)
 (hf' : ∀ r, TendstoUniformlyOn f' g' atTop (Metric.ball 0 r))
 (hf : ∀ n : ℕ, ∀ y, HasDerivAt (f n) (f' n y) y)
 (hfg : ∀ y, MySequences.TendsTo ⟨fun n => f n y⟩ (g y)) :
  HasDeriv g g' := by
  intro x
  rw [HasDerivAt_iff]
  apply _root_.hasDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball (hf' (|x| + 1))
  · exact Filter.Eventually.of_forall fun n y _ => HasDerivAt_iff.mp (hf n y)
  · exact fun y _ => Metric.tendsto_atTop.2 (hfg y)
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    linarith

-- Write exp as a limit of the partial sums (as functions this time).
def exp_partial : ℕ → ℝ → ℝ := fun n x => ∑ k ∈ Finset.range n, (x^k/ k.factorial)

def exp_partial' (n : ℕ) : ℝ → ℝ := fun x => if n = 0 then 0 else exp_partial (n - 1) x

-- Uniform convergence of the partial sums on every ball.
lemma exp_tends_to_uniform {r : ℝ} : TendstoUniformlyOn exp_partial exp atTop (Metric.ball 0 r)
    := by
  have hexp : (fun x : ℝ => ∑' n, x ^ n / n.factorial) = exp := by
    funext x
    exact tendsto_nhds_unique
      (Real.summable_pow_div_factorial x).hasSum.tendsto_sum_nat
      (Metric.tendsto_atTop.2 (tendsto_exp_seq x))
  rw[← hexp]
  apply tendstoUniformlyOn_tsum_nat (Real.summable_pow_div_factorial r)
  intro n x hx
  rw [norm_div, norm_pow, Real.norm_eq_abs, norm_natCast]
  gcongr
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  exact le_of_lt hx

-- simple reindexing of the above result; this is what we actually need
lemma exp_partial_deriv_tends_to_uniform (r : ℝ) :
    TendstoUniformlyOn exp_partial' exp atTop (Metric.ball 0 r) := by
  rw [tendsto_uniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := tendsto_uniformly_iff.mp exp_tends_to_uniform ε hε
  refine ⟨N + 1, fun n hn x hx => ?_⟩
  rw [exp_partial', if_neg (by linarith)]
  exact hN (n - 1) (by omega) x hx
-- derivatives of the partial sums
lemma exp_partial_deriv {n : ℕ} : HasDeriv (exp_partial n) (exp_partial' n) := by
  induction n with
  | zero =>
      convert deriv_const 0 using 1 <;> ext x <;> simp [exp_partial, exp_partial']
  | succ n ih =>
      have hsum : exp_partial (n + 1) =
          exp_partial n + (fun x : ℝ => x ^ n / (n.factorial : ℝ)) := by
        ext x
        simp only [exp_partial, Finset.sum_range_succ, Pi.add_apply]
      have hsum' : exp_partial' n + (fun x : ℝ => n * x ^ (n - 1) / n.factorial) =
          exp_partial' (n + 1) := by
        ext x
        simp only [Pi.add_apply]
        rw [show exp_partial' (n + 1) x = exp_partial n x by simp [exp_partial']]
        unfold exp_partial'
        split_ifs with hn
        · simp only [hn, CharP.cast_eq_zero, zero_tsub, pow_zero, mul_one, Nat.factorial_zero,
            Nat.cast_one, div_one, add_zero, exp_partial, Finset.range_zero, Finset.sum_empty]
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
          have hcoeff : (k + 1 : ℕ) * x ^ k / (k + 1).factorial =
              x ^ k / k.factorial := by
            rw [Nat.factorial_succ, Nat.cast_mul]
            field_simp
          simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
          rw [hcoeff]
          unfold exp_partial
          rw [Finset.sum_range_succ]
      have hmul := deriv_mul ⟨_, deriv_power n⟩ ⟨_, deriv_const (1 / (n.factorial : ℝ))⟩
      rw [← deriv_of_has_deriv (deriv_power n)] at hmul
      rw[← deriv_of_has_deriv (deriv_const (1 / (n.factorial : ℝ)))] at hmul
      have hterm : HasDeriv (fun x : ℝ => x ^ n / n.factorial)
          (fun x => n * x ^ (n - 1) / n.factorial) := by
        convert hmul using 1 <;>
          ext x <;> simp [Pi.mul_apply, Function.const_apply, div_eq_mul_inv]
      have hadd := deriv_add ⟨_, ih⟩ ⟨_, hterm⟩
      rw [← deriv_of_has_deriv ih, ← deriv_of_has_deriv hterm] at hadd
      rw [hsum]
      exact hadd.congr_deriv hsum'

-- apply the convergence theorem to get the derivative of exp.
theorem deriv_exp : HasDeriv exp exp := hasDeriv_of_uniform_convergent exp exp
  (fun r => exp_partial_deriv_tends_to_uniform r)
  (fun n y => exp_partial_deriv (n := n) y)
  tendsto_exp_seq


end MyFunctions
