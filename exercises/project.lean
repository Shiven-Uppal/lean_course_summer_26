import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

open scoped BigOperators
namespace complexnumbers

-- Basic operations
structure cnum where
  re : ℝ
  im : ℝ

def zero : cnum :=
  ⟨0, 0⟩

def one : cnum :=
  ⟨1, 0⟩

def ii : cnum :=
  ⟨0, 1⟩

def add (z w : cnum) : cnum :=
  ⟨z.re + w.re, z.im + w.im⟩

def neg (z : cnum) : cnum :=
  ⟨-z.re, -z.im⟩

def sub (z w : cnum) : cnum :=
  add z (neg w)

def mul (z w : cnum) : cnum :=
  ⟨z.re * w.re - z.im * w.im,
   z.re * w.im + z.im * w.re⟩

def scale (r : ℝ) (z : cnum) : cnum :=
  ⟨r * z.re, r * z.im⟩

def conj (z : cnum) : cnum :=
  ⟨z.re, -z.im⟩

def sqnorm (z : cnum) : ℝ :=
  z.re ^ 2 + z.im ^ 2

def iszero (z : cnum) : Prop :=
  z.re = 0 ∧ z.im = 0

def isreal (z : cnum) : Prop :=
  z.im = 0

def isimag (z : cnum) : Prop :=
  z.re = 0

def oncircle (c : cnum) (r : ℝ) (z : cnum) : Prop :=
  sqnorm (sub z c) = r ^ 2

def turn (z : cnum) : cnum :=
  mul ii z

noncomputable def inv (z : cnum) : cnum :=
  scale ((1 : ℝ) / sqnorm z) (conj z)

@[ext] lemma sameparts {z w : cnum}
    (h1 : z.re = w.re) (h2 : z.im = w.im) : z = w := by
  cases z
  cases w
  simp_all

lemma addzero (z : cnum) :
    add z zero = z := by
  cases z
  simp [add, zero]

lemma zeroadd (z : cnum) :
    add zero z = z := by
  cases z
  simp [add, zero]

lemma addneg (z : cnum) :
    add z (neg z) = zero := by
  cases z
  simp [add, neg, zero]

lemma addcomm (z w : cnum) :
    add z w = add w z := by
  cases z
  cases w
  simp [add, add_comm]

lemma addassoc (z w u : cnum) :
    add (add z w) u = add z (add w u) := by
  cases z
  cases w
  cases u
  simp [add, add_assoc]

lemma scaleone (z : cnum) :
    scale 1 z = z := by
  cases z
  simp [scale]

lemma scalezero (z : cnum) :
    scale 0 z = zero := by
  cases z
  simp [scale, zero]

lemma scaleadd (r : ℝ) (z w : cnum) :
    scale r (add z w) = add (scale r z) (scale r w) := by
  cases z
  cases w
  simp [scale, add, mul_add]

lemma onemul (z : cnum) :
    mul one z = z := by
  cases z
  simp [mul, one]

lemma mulone (z : cnum) :
    mul z one = z := by
  cases z
  simp [mul, one]

lemma zeromul (z : cnum) :
    mul zero z = zero := by
  cases z
  simp [mul, zero]

lemma mulcomm (z w : cnum) :
    mul z w = mul w z := by
  cases z
  cases w
  ext <;> simp [mul] <;> ring

lemma mulassoc (z w u : cnum) :
    mul (mul z w) u = mul z (mul w u) := by
  cases z
  cases w
  cases u
  ext <;> simp [mul] <;> ring

lemma muladd (z w u : cnum) :
    mul z (add w u) = add (mul z w) (mul z u) := by
  cases z
  cases w
  cases u
  ext <;> simp [mul, add] <;> ring

lemma isquared :
    mul ii ii = neg one := by
  simp [mul, ii, neg, one]

lemma ifourth :
    mul (mul ii ii) (mul ii ii) = one := by
  simp [mul, ii, one]

-- Conjugation, norm and inverse
lemma conjconj (z : cnum) :
    conj (conj z) = z := by
  cases z
  simp [conj]

lemma conjreal (z : cnum) :
    conj z = z ↔ isreal z := by
  constructor
  · intro h
    have h1 := congrArg cnum.im h
    change -z.im = z.im at h1
    unfold isreal
    linarith
  · intro h
    unfold isreal at h
    apply sameparts
    · rfl
    · simp [conj, h]

lemma conjimag (z : cnum) :
    conj z = neg z ↔ isimag z := by
  constructor
  · intro h
    have h1 := congrArg cnum.re h
    change z.re = -z.re at h1
    unfold isimag
    linarith
  · intro h
    unfold isimag at h
    apply sameparts
    · simp [conj, neg, h]
    · rfl

lemma axeszero (z : cnum) :
    isreal z ∧ isimag z ↔ iszero z := by
  unfold isreal isimag iszero
  constructor
  · rintro ⟨hi, hr⟩
    exact ⟨hr, hi⟩
  · rintro ⟨hr, hi⟩
    exact ⟨hi, hr⟩

lemma conjadd (z w : cnum) :
    conj (add z w) = add (conj z) (conj w) := by
  cases z
  cases w
  ext <;> simp [conj, add] <;> ring

lemma conjmul (z w : cnum) :
    conj (mul z w) = mul (conj z) (conj w) := by
  cases z
  cases w
  ext <;> simp [conj, mul] <;> ring

lemma normnonneg (z : cnum) :
    0 ≤ sqnorm z := by
  cases z
  unfold sqnorm
  positivity

lemma conjnorm (z : cnum) :
    sqnorm (conj z) = sqnorm z := by
  cases z
  simp [sqnorm, conj]

lemma mulconj (z : cnum) :
    mul z (conj z) = ⟨sqnorm z, 0⟩ := by
  cases z
  ext <;> simp [mul, conj, sqnorm] <;> ring

lemma normzero (z : cnum) :
    sqnorm z = 0 ↔ iszero z := by
  rcases z with ⟨x, y⟩
  constructor
  · intro h
    unfold sqnorm at h
    unfold iszero
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
  · rintro ⟨hx, hy⟩
    change x = 0 at hx
    change y = 0 at hy
    subst x
    subst y
    simp [sqnorm]

lemma invmul (z : cnum) (h : sqnorm z ≠ 0) :
    mul z (inv z) = one := by
  rcases z with ⟨x, y⟩
  simp only [sqnorm] at h
  ext <;>
    simp [inv, scale, conj, mul, sqnorm, one] <;>
    field_simp [h] <;>
    ring

lemma mulinv (z : cnum) (h : sqnorm z ≠ 0) :
    mul (inv z) z = one := by
  rw [mulcomm]
  exact invmul z h

-- Rotations and fourth roots
lemma turncoords (z : cnum) :
    turn z = ⟨-z.im, z.re⟩ := by
  cases z
  simp [turn, mul, ii]

lemma turnnorm (z : cnum) :
    sqnorm (turn z) = sqnorm z := by
  cases z
  simp [sqnorm, turn, mul, ii]
  ring

lemma fourturns (z : cnum) :
    turn (turn (turn (turn z))) = z := by
  cases z
  ext <;> simp [turn, mul, ii]

lemma turncircle (r : ℝ) (z : cnum)
    (h : oncircle zero r z) :
    oncircle zero r (turn z) := by
  rcases z with ⟨x, y⟩
  simp [oncircle, zero, sqnorm, sub, neg, add, turn, mul, ii] at h ⊢
  nlinarith

def root4 (z : cnum) : Prop :=
  mul (mul z z) (mul z z) = one

lemma oneroot :
    root4 one := by
  simp [root4, mul, one]

lemma negoneroot :
    root4 (neg one) := by
  simp [root4, mul, neg, one]

lemma iroot :
    root4 ii := by
  simp [root4, mul, ii, one]

lemma negiroot :
    root4 (neg ii) := by
  simp [root4, mul, neg, ii, one]

lemma rootcycle :
    turn one = ii ∧
    turn ii = neg one ∧
    turn (neg one) = neg ii ∧
    turn (neg ii) = one := by
  constructor
  · simp [turn, mul, ii, one]
  constructor
  · simp [turn, mul, ii, one, neg]
  constructor
  · simp [turn, mul, ii, one, neg]
  · simp [turn, mul, ii, one, neg]

lemma mulnorm (z w : cnum) :
    sqnorm (mul z w) = sqnorm z * sqnorm w := by
  rcases z with ⟨x, y⟩
  rcases w with ⟨u, v⟩
  simp [sqnorm, mul]
  ring

lemma zeroproduct (z w : cnum) :
    mul z w = zero → iszero z ∨ iszero w := by
  intro h
  have h1 : sqnorm (mul z w) = 0 := by
    rw [h]
    simp [sqnorm, zero]
  rw [mulnorm] at h1
  rcases mul_eq_zero.mp h1 with hz | hw
  · left
    exact (normzero z).mp hz
  · right
    exact (normzero w).mp hw

def sq (z : cnum) : cnum :=
  mul z z

def fourth (z : cnum) : cnum :=
  mul (sq z) (sq z)

lemma sqdiff (z : cnum) :
    mul (sub (sq z) one) (add (sq z) one) =
      sub (fourth z) one := by
  rcases z with ⟨x, y⟩
  ext <;>
    simp [mul, sub, neg, add, sq, fourth, one] <;>
    ring

lemma rootsquare (z : cnum) :
    root4 z → sq z = one ∨ sq z = neg one := by
  intro h
  have h1 : fourth z = one := by
    simpa [fourth, sq, root4] using h
  have h2 :
      mul (sub (sq z) one) (add (sq z) one) = zero := by
    rw [sqdiff, h1]
    simp [sub, add, neg, one, zero]
  rcases zeroproduct (sub (sq z) one) (add (sq z) one) h2 with h | h
  · left
    rcases h with ⟨hr, hi⟩
    apply sameparts
    · change (sq z).re = 1
      dsimp [sub, add, neg, one] at hr
      linarith
    · change (sq z).im = 0
      dsimp [sub, add, neg, one] at hi
      simpa using hi
  · right
    rcases h with ⟨hr, hi⟩
    apply sameparts
    · change (sq z).re = -1
      dsimp [add, neg, one] at hr
      linarith
    · simpa [add, neg, one] using hi

lemma sqone (z : cnum) (h : sq z = one) :
    z = one ∨ z = neg one := by
  rcases z with ⟨x, y⟩
  have hr := congrArg cnum.re h
  have hi := congrArg cnum.im h
  simp [sq, mul, one] at hr hi
  have hxy : x * y = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hxy with hx | hy
  · exfalso
    nlinarith [sq_nonneg y]
  · have hx2 : x ^ 2 = 1 := by
      nlinarith
    have hf : (x - 1) * (x + 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hf with h1 | h1
    · left
      apply sameparts
      · simp [one]
        linarith
      · simp [one, hy]
    · right
      apply sameparts
      · simp [neg, one]
        linarith
      · simp [neg, one, hy]

lemma sqnegone (z : cnum) (h : sq z = neg one) :
    z = ii ∨ z = neg ii := by
  rcases z with ⟨x, y⟩
  have hr := congrArg cnum.re h
  have hi := congrArg cnum.im h
  simp [sq, mul, neg, one] at hr hi
  have hxy : x * y = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hxy with hx | hy
  · have hy2 : y ^ 2 = 1 := by
      nlinarith
    have hf : (y - 1) * (y + 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hf with h1 | h1
    · left
      apply sameparts
      · simp [ii, hx]
      · simp [ii]
        linarith
    · right
      apply sameparts
      · simp [neg, ii, hx]
      · simp [neg, ii]
        linarith
  · exfalso
    nlinarith [sq_nonneg x]

theorem fourthroots (z : cnum) :
    root4 z ↔
      z = one ∨ z = neg one ∨ z = ii ∨ z = neg ii := by
  constructor
  · intro h
    rcases rootsquare z h with h | h
    · rcases sqone z h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases sqnegone z h with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  · intro h
    rcases h with h | h | h | h
    · rw [h]
      exact oneroot
    · rw [h]
      exact negoneroot
    · rw [h]
      exact iroot
    · rw [h]
      exact negiroot

-- Connection with Mathlib complex numbers
def ascomplex (z : cnum) : ℂ :=
  ⟨z.re, z.im⟩

lemma ascomplexzero :
    ascomplex zero = 0 := by
  apply Complex.ext
  · simp [ascomplex, zero]
  · simp [ascomplex, zero]

lemma ascomplexone :
    ascomplex one = 1 := by
  apply Complex.ext
  · simp [ascomplex, one]
  · simp [ascomplex, one]

lemma ascomplexi :
    ascomplex ii = Complex.I := by
  apply Complex.ext
  · simp [ascomplex, ii]
  · simp [ascomplex, ii]

lemma ascomplexadd (z w : cnum) :
    ascomplex (add z w) = ascomplex z + ascomplex w := by
  apply Complex.ext
  · simp [ascomplex, add]
  · simp [ascomplex, add]

lemma ascomplexmul (z w : cnum) :
    ascomplex (mul z w) = ascomplex z * ascomplex w := by
  apply Complex.ext
  · simp [ascomplex, mul]
  · simp [ascomplex, mul]

-- Power series, Euler's formula and De Moivre's theorem
noncomputable section
def expseries (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n / (n.factorial : ℂ)

def cosseries (x : ℝ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n * x ^ (2 * n) /
    ((2 * n).factorial : ℝ)

def sinseries (x : ℝ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n * x ^ (2 * n + 1) /
    ((2 * n + 1).factorial : ℝ)

def cis (x : ℝ) : ℂ :=
  (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I

lemma cisreal (x : ℝ) :
    (cis x).re = Real.cos x := by
  rw [cis]
  simp only [Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

lemma cisimag (x : ℝ) :
    (cis x).im = Real.sin x := by
  rw [cis]
  simp only [Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

lemma expeq (z : ℂ) :
    expseries z = Complex.exp z := by
  rw [expseries, Complex.exp_eq_exp_ℂ]
  exact (NormedSpace.expSeries_div_hasSum_exp z).tsum_eq

lemma cosseriesvalue (x : ℝ) :
    cosseries x = Real.cos x := by
  rw [cosseries]
  exact (Real.hasSum_cos x).tsum_eq

lemma sinseriesvalue (x : ℝ) :
    sinseries x = Real.sin x := by
  rw [sinseries]
  exact (Real.hasSum_sin x).tsum_eq

lemma expconj (z : ℂ) :
    Complex.exp (starRingEnd ℂ z) =
      starRingEnd ℂ (Complex.exp z) := by
  exact Complex.exp_conj z

lemma fixedconj (z : ℂ) (h : starRingEnd ℂ z = z) :
    z.im = 0 := by
  exact Complex.conj_eq_iff_im.mp h

lemma realexpimag (x : ℝ) :
    (Complex.exp (x : ℂ)).im = 0 := by
  apply fixedconj
  rw [← expconj (x : ℂ)]
  simp

lemma eulerseries (x : ℝ) :
    expseries ((x : ℂ) * Complex.I) =
      (cosseries x : ℂ) + (sinseries x : ℂ) * Complex.I := by
  have h :
      HasSum
        (fun n : ℕ =>
          ((x : ℂ) * Complex.I) ^ n / (n.factorial : ℂ))
        ((Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I) := by
    apply HasSum.even_add_odd
    · simpa using Complex.hasSum_cos' (x : ℂ)
    · simpa [Complex.I_ne_zero, mul_assoc] using
        (Complex.hasSum_sin' (x : ℂ)).mul_right Complex.I
  rw [expseries, cosseriesvalue, sinseriesvalue]
  exact h.tsum_eq

lemma expfromseries (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) =
      (cosseries x : ℂ) + (sinseries x : ℂ) * Complex.I := by
  calc
    Complex.exp ((x : ℂ) * Complex.I) =
        expseries ((x : ℂ) * Complex.I) :=
      (expeq ((x : ℂ) * Complex.I)).symm
    _ = (cosseries x : ℂ) + (sinseries x : ℂ) * Complex.I :=
      eulerseries x

lemma exprealpart (x : ℝ) :
    (Complex.exp ((x : ℂ) * Complex.I)).re = Real.cos x := by
  have h := congrArg Complex.re (expfromseries x)
  simpa [cosseriesvalue, sinseriesvalue] using h

lemma expimagpart (x : ℝ) :
    (Complex.exp ((x : ℂ) * Complex.I)).im = Real.sin x := by
  have h := congrArg Complex.im (expfromseries x)
  simpa [cosseriesvalue, sinseriesvalue] using h

theorem euler (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) = cis x := by
  apply Complex.ext
  · rw [exprealpart x, cisreal x]
  · rw [expimagpart x, cisimag x]

lemma eulerpi :
    Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := by
  rw [euler]
  simp [cis]

lemma expnat (z : ℂ) (n : ℕ) :
    Complex.exp ((n : ℂ) * z) = Complex.exp z ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul]
      rw [Complex.exp_add, ih, pow_succ]

theorem demoivre (x : ℝ) (n : ℕ) :
    cis x ^ n = cis ((n : ℝ) * x) := by
  calc
    cis x ^ n = Complex.exp ((x : ℂ) * Complex.I) ^ n := by
      rw [euler x]
    _ = Complex.exp ((n : ℂ) * ((x : ℂ) * Complex.I)) :=
      (expnat ((x : ℂ) * Complex.I) n).symm
    _ = Complex.exp ((((n : ℝ) * x : ℝ) : ℂ) * Complex.I) := by
      congr 1
      push_cast
      ring
    _ = cis ((n : ℝ) * x) :=
      euler ((n : ℝ) * x)
end
end complexnumbers
