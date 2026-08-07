import LectureNotes.lecture7.examples7
import Exercises.Sheet5
import Exercises.Sheet6

namespace MyFunctions

open MyFunctions MySequences Function

/-
Convergence of a function `f : ℝ → ℝ` to a limit `a` at a point `x`.
-/
def TendsTo (f : ℝ → ℝ) (x : ℝ) (a : ℝ) : Prop :=
    ∀ ε > 0, ∃ δ > 0, ∀ y ≠ x, |y - x| < δ → |f y - a| < ε


/-
As you can see, there are a few sorry's in the code. Most of these results are similar to things
that we've already proved for sequences. The proofs are completely analogous.
-/
lemma continuous_at_iff_tends_to {f : ℝ → ℝ} {x : ℝ} :
    ContinuousAt f x ↔ TendsTo f x (f x) := by
    constructor
    · intro h ε hε
      obtain ⟨δ, hδ, h'⟩ := h ε hε
      exact ⟨δ, hδ, fun y hy hxy => h' y hxy⟩
    intro h ε hε
    obtain ⟨δ, hδ, h'⟩ := h ε hε
    refine ⟨δ, hδ, fun y hxy => ?_⟩
    by_cases h : y = x
    · rw[h, dist_self]
      exact hε
    exact h' y h hxy

lemma tends_to_of_fun_tends_to {f : ℝ → ℝ} {y : RealSeq} {x a : ℝ} (h : TendsTo f x a)
    (hy : MySequences.TendsTo y x) : MySequences.TendsTo ⟨(fun n => f (y n))⟩ a := by
  sorry

lemma tends_to_const (a : ℝ) (x : ℝ) : TendsTo (const _ a) x a := by
  intro ε hε
  refine ⟨1, by positivity, fun y hy hxy => ?_⟩
  simp only [const_apply, sub_self, abs_zero]
  exact hε

lemma tends_to_of_sub {f : ℝ → ℝ} {x a : ℝ} :
    TendsTo f x a ↔ TendsTo (f - const _ a) x 0 := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, h'⟩ := h ε hε
    refine ⟨δ, hδ, fun y hy hxy => ?_⟩ -- new trick: refine instead of use
    simp only [Pi.sub_apply, const_apply, sub_zero, h' y hy hxy]
  intro h ε hε
  obtain ⟨δ, hδ, h'⟩ := h ε hε
  refine ⟨δ, hδ, fun y hy hxy => ?_⟩
  specialize h' y hy hxy
  simp only [Pi.sub_apply, const_apply, sub_zero] at h'
  exact h'

lemma tends_to_add_tends_to {f g : ℝ → ℝ} {x a b : ℝ} :
    TendsTo f x a → TendsTo g x b → TendsTo (fun y => f y + g y) x (a + b) := by
  sorry

lemma tends_to_mul_tends_to {f g : ℝ → ℝ} {x a b : ℝ} :
    TendsTo f x a → TendsTo g x b → TendsTo (fun y => f y * g y) x (a * b) := by
  sorry

/-
We can define the derivative of a function `f` at a point `x` using the above notion of convergence.
-/
def HasDerivAt (f : ℝ → ℝ) (f' : ℝ) (x : ℝ) : Prop :=
  TendsTo (fun y => (f y - f x) / (y - x)) x f'

-- Follows directly from the fact that limits are unique in ℝ. See lecture 6 `tends_toReal_unique`.
lemma deriv_unique {f : ℝ → ℝ} {x : ℝ} {f' f'' : ℝ}
    (hf' : HasDerivAt f f' x) (hf'' : HasDerivAt f f'' x) : f' = f'' := by
  sorry

/-
Assertion that `f'` is the derivative of `f` at every point `x : ℝ`
-/
def HasDeriv (f : ℝ → ℝ) (f' : ℝ → ℝ) : Prop :=
    ∀ x, HasDerivAt f (f' x) x

/-
We define the derivate of a function to be the value `f'`
from above if it exists, otherwise `0`.
We have to use the axiom of choice here, so we mark this definition as noncomputable.
-/
open scoped Classical in
noncomputable def deriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if h : ∃ f', HasDerivAt f f' x
    then Classical.choose h
  else 0

-- If `f` is differentiable at `x`, then `deriv f x` is the derivative of `f` at `x`.
lemma deriv_eq_of_has_deriv {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} (hf : HasDerivAt f f' x) :
     f' = deriv f x := by
  unfold deriv
  have hex: ∃ f', HasDerivAt f f' x := ⟨f', hf⟩
  simp only [hex, ↓reduceDIte]
  apply deriv_unique (hf) (Classical.choose_spec hex) --access property of choose

-- The same holds globally.
lemma deriv_of_has_deriv {f : ℝ → ℝ} {f' : ℝ → ℝ} (hf : HasDeriv f f') :
    f' = deriv f := by
  ext x --extensionality of functions
  apply deriv_eq_of_has_deriv
  exact hf x

-- Thus, we introduce the notion of a differentiable function.
def Differentiable (f : ℝ → ℝ) : Prop :=
  ∃ f', HasDeriv f f'

-- As a sanity check, we can show that the derivative of a differentiable function is `deriv f`.
lemma has_deriv_of_differentiable {f : ℝ → ℝ} (hf : Differentiable f) :
    HasDeriv f (deriv f) := by
    obtain ⟨f', hf'⟩ := hf
    rw[← deriv_of_has_deriv hf']
    exact hf'

lemma continuous_at_of_deriv_at {f: ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    ContinuousAt f x := by
  rw[continuous_at_iff_tends_to, tends_to_of_sub]
  have h (g : ℝ → ℝ) (hg : g x = 0): g = (fun y => g y / (y - x)) * fun y => y - x := by
      ext y
      by_cases h : y = x
      · simp only [h, hg, Pi.mul_apply, sub_self, div_zero, mul_zero]
      simp only [Pi.mul_apply]
      field_simp -- new tactic!
  rw[h (f - const _ (f x)) (sub_self (f x)), ← mul_zero (f')]
  refine tends_to_mul_tends_to hf ?_
  exact fun ε hε => ⟨ε, hε, fun y hy hxy => by simp only [sub_zero, hxy]⟩


lemma continuous_of_differentiable {f : ℝ → ℝ} (hf : Differentiable f) :
    ContinuousOn f := by
    obtain ⟨f', hf'⟩ := hf
    exact fun x => continuous_at_of_deriv_at (hf' x)

lemma deriv_add {f g : ℝ → ℝ} (hf : Differentiable f) (hg : Differentiable g) :
    HasDeriv (f + g) (deriv f + deriv g) := by
  sorry

lemma deriv_mul_at {f g : ℝ → ℝ} {f' g' : ℝ} {x : ℝ} (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (f * g) (f' * g x + f x * g') x := by
  unfold HasDerivAt at ⊢
  have hexpand : (fun y ↦ ((f * g) y - (f * g) x) / (y - x))
    = (fun y => (f y - f x) / (y - x)) * const _ (g x)  + f *  (fun y => (g y - g x) / (y - x)) := by
    ext y
    simp only [Pi.add_apply, Pi.mul_apply, const_apply]
    calc
      (f y * g y - f x * g x) / (y - x) =
          ((f y - f x) * g x + f y * (g y - g x)) / (y - x) := by ring
      _ = (f y - f x) / (y - x) * g x +
          f y * ((g y - g x) / (y - x)) := by ring
  rw[hexpand]
  apply tends_to_add_tends_to ?_ ?_
  · exact tends_to_mul_tends_to hf (tends_to_const (g x) x)
  refine tends_to_mul_tends_to ?_ hg
  apply continuous_at_iff_tends_to.mp (continuous_at_of_deriv_at hf)


lemma deriv_mul {f g : ℝ → ℝ} (hf : Differentiable f) (hg : Differentiable g) :
    HasDeriv (f * g) (deriv f * g  + f  * deriv g ) := fun x =>
  deriv_mul_at (has_deriv_of_differentiable hf x) (has_deriv_of_differentiable hg x)

lemma deriv_const (c : ℝ) : HasDeriv (const _ c) (const _ 0) := by
    intro x ε hε
    simp only [const_apply, sub_self, zero_div, abs_zero]
    exact ⟨1, by positivity, fun _ _ _ => by positivity⟩

lemma deriv_affine (a b : ℝ) : HasDeriv (fun x => a*x + b) (const _ a) := by
    intro x ε hε
    refine ⟨1, by positivity, fun y hy hxy => ?_⟩
    simp only [add_sub_add_right_eq_sub, const_apply, ← mul_sub a y x]
    field_simp
    rw[sub_self, mul_zero, abs_zero]
    positivity

/-
It is often convenient to restrict functions to intervals.
They are implemented in lean as `Set.Icc a b` for the closed interval `[a, b]`, `Set.Ioo a b` for
the open interval `(a, b)`, and `Set.Ico a b` for the half-open interval `[a, b)`, etc..
-/

#check Set.Ioo _ _ --(a, b) open interval; by defn x ∈ Set.Ioo a b ↔ a < x ∧ x < b.
#check Set.Icc _ _ --[a, b] closed interval
#check Set.Ico _ _ --[a, b) half-open interval

-- The fact that a function has a maximum on a set S is expressed as follows:
#check IsMaxOn

theorem deriv_at_max_zero {f : ℝ → ℝ} {x ε : ℝ} (hε : ε > 0)
    (hf : IsMaxOn f (Set.Ioo (x - ε) (x + ε)) x) : deriv f x = 0 := by
  by_cases h : ∃ f' , HasDerivAt f f' x
  · obtain ⟨f', hf'⟩ := h
    obtain ⟨n, hn, hnle⟩ := nat_one_div_le hε
    have hlt : ∀ m : ℕ, ((↑n + ↑m + 1)⁻¹ : ℝ) < 1/n :=
            fun m => (by exact (lt_one_div (by positivity) (by positivity)).mp (by simp; linarith))
    let yu : ℕ → ℝ := fun m => x + 1 / (n + m + 1 : ℝ)
    have hyu : MySequences.TendsTo ⟨yu⟩ x := by
        sorry -- exericse :)
    let yl : ℕ → ℝ := fun m => x - 1 / (n + m + 1 : ℝ)
    have hyl : MySequences.TendsTo ⟨yl⟩ x := by sorry
    have hf'u : f' ≤ 0 := by
        apply tends_to_le_of_le (tends_to_of_fun_tends_to hf' hyu)
        intro m
        apply div_nonpos_of_nonpos_of_nonneg
        · simp only [sub_nonpos]
          refine le_of_eq_of_le rfl (hf ?_)
          simp only [one_div, Set.mem_Ioo, add_lt_add_iff_left, yu]
          exact ⟨lt_add_of_le_of_pos (by linarith) (by positivity), by linarith [hlt m]⟩
        simp only [one_div, add_sub_cancel_left, inv_nonneg, yu]
        linarith
    have hf'l : f' ≥ 0 := by
        apply tends_to_ge_of_ge (tends_to_of_fun_tends_to hf' hyl)
        intro m
        apply div_nonneg_of_nonpos
        · simp only [sub_nonpos]
          refine le_of_eq_of_le rfl (hf (?_))
          simp only [one_div, Set.mem_Ioo, sub_lt_sub_iff_left, yl]
          refine ⟨ by linarith [hlt m], ?_⟩
          calc
            x - (n + m + 1 : ℝ)⁻¹ < x := by simp only [sub_lt_self_iff, inv_pos]; positivity
            _ < x + ε := by linarith
        simp only [one_div, sub_sub_cancel_left, Left.neg_nonpos_iff, inv_nonneg, yl]
        linarith
    rw[← deriv_eq_of_has_deriv hf']
    linarith
  simp only [deriv, h, ↓reduceDIte]


end MyFunctions
