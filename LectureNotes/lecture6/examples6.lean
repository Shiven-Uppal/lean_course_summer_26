import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.Rat

/-
How to manage a zoo of types, a.k.a. coercions.
-/

section

variable {n m : ℕ} {x : ℚ} {f : ℝ → ℝ}

#check 1/n

#check (1/n : ℚ)

#check (n : ℚ)

#check @Nat.cast ℚ _

#check x + 1/n

#check (x : ℝ) + (1/n : ℝ)

#check ((x + 1/n) : ℝ)

#check (((x : ℚ) + (1/n : ℚ)) : ℝ)

example : (((x : ℚ) + (1/n : ℚ)) : ℝ) = ((x + 1/n) : ℝ) := by
  simp


noncomputable example : ℝ := f (x + 1/n)

/-
What happens in the last example:
1. Since `f` expects a real number, Lean knows that `+` is addition on real
   numbers, so it needs to convert both `x` and `1 / n` to real numbers.
2. Lean knows how to convert rational numbers to real numbers, so it converts
   `x` to a real number.
3. Since Lean expects `1 / n` to be a real number, it converts `n` to a real
   number and then computes `1 / n` as a real number.
-/

/-
Lean is really good at figuring out which coercion to use.
-/
variable (k : Fin n) (l : Fin m)

#check (k : ℕ) + (l : ℕ)

#check (k + l : ℕ)

#check (k : ℕ) + l

#check (k + l: ℝ)

/-
Structures

A term of `HalfPlane` contains two real coordinates together with a proof that
the first coordinate is smaller than the second.
-/

namespace MyStructures

structure HalfPlane where
  x : ℝ
  y : ℝ
  xlty : x < y

/- We construct a point by supplying each field, including the proof field. -/
def p : HalfPlane where
  x := 0
  y := 1
  xlty := by norm_num

-- Trick: use _ to create a skeleton of the structure.
def q : HalfPlane where
  x := sorry
  y := sorry
  xlty := sorry

/- Dot notation accesses the fields of a structure. -/
#check p.x
#check p.y
#check p.xlty

/-
The conversion to `ℝ × ℝ` keeps the two coordinates and forgets the proof.
-/
def HalfPlane.toProd (p : HalfPlane) : ℝ × ℝ := (p.x, p.y)

instance : Coe HalfPlane (ℝ × ℝ) where
  coe := HalfPlane.toProd

-- The expected type causes Lean to insert the coercion.
example (p : HalfPlane) : ℝ × ℝ := p

end MyStructures


/-
Sequences of rational and real numbers.
A sequence of rational numbers is a function from natural numbers to rational
numbers: `x : ℕ → ℚ`.
-/

namespace MySequences

variable {a b : ℝ} {c d : ℚ}

#check |a|

#check |c|

#check dist a b

#check dist c d

example : dist a b = |a - b| := by
  rfl

/-
`structure RatSeq` declares a new type, `RatSeq`, whose terms contain one field:
a function `x : ℕ → ℚ`. Thus, if `s : RatSeq`, then `s.x` is the rational
sequence stored in `s`.
-/
structure RatSeq where
  x : ℕ → ℚ

/-
This instance tells Lean that a `x : RatSeq` may be used as a function `x : ℕ → ℚ`.
Thus, `x n` uses the stored function `f.x`.
-/
instance : CoeFun RatSeq (fun _ => ℕ → ℚ) where
  coe f := f.x

/-
Likewise, `RealSeq` is a type whose terms package functions `ℕ → ℝ`.
Although `RatSeq` and `RealSeq` have the same shape, they are distinct types:
one stores a rational-valued function and the other a real-valued function.
-/
structure RealSeq where
  x : ℕ → ℝ

instance : CoeFun RealSeq (fun _ => ℕ → ℝ) where
  coe f := f.x

/-
We can convert a `RatSeq` to a `RealSeq`. It builds a `RealSeq` from a
`RatSeq` by coercing each rational value `f.x n` to a real value.
-/
abbrev RatSeq.toRealSeq (f : RatSeq) : RealSeq where
  x n := (f.x n : ℝ)

/-
This instance tells Lean to insert `RatSeq.toRealSeq` when it has a `RatSeq`
but the expected type is `RealSeq`.
-/
instance : Coe RatSeq RealSeq where coe x := x.toRealSeq

-- The expected result type causes Lean to insert the registered coercion.
example (x : RatSeq) : RealSeq := x

/-
How to define a sequence of rational numbers.
-/
example : RatSeq where
  x n := 1 / n

example : RatSeq where
  x := fun n ↦ 1 / n

-- Direct wrapper
example : RatSeq := ⟨fun n ↦ 1 / n⟩


/-
We are ready to define Cauchy sequences and limits of sequences.
Note the type coercions in the definitions, including those for `ε`, `n`, `m`,
and `N`.
-/
def IsCauchy (x : RatSeq) := ∀ ε > 0, ∃ N, ∀ m≥ N, ∀ n≥ N, dist (x m) (x n) < ε

def TendsToRat (x : RatSeq) (a : ℚ) := ∀ ε > 0, ∃ N, ∀ n≥ N, dist (x n) a < ε

def IsCauchyReal (x : RealSeq) :=  ∀ ε > 0, ∃ N, ∀ m≥ N, ∀ n≥ N, dist (x m) (x n) < ε

theorem cauchy_real_iff {x : RealSeq} :
  IsCauSeq (abs : ℝ → ℝ) x ↔ IsCauchyReal x  := by
  constructor
  · intro h
    simp only [IsCauchyReal, gt_iff_lt, ge_iff_le, dist]
    exact fun ε a ↦ IsCauSeq.cauchy₂ h a
  intro h ε hε
  obtain ⟨N, hN⟩ := h ε hε
  use N
  intro j hj
  specialize hN N (le_refl N) j hj
  rw[dist_comm] at hN
  exact hN

abbrev TendsTo (x : RealSeq) (a : ℝ) := ∀ ε > 0, ∃ N, ∀ n≥ N, dist (x n) a < ε


example (x : RealSeq) : IsCauSeq (abs : ℝ → ℝ) x:= by sorry

-- We can evaluate `tends_to` on a sequence of rational numbers.
example (x : RatSeq) (a : ℝ) : TendsTo x a := by sorry

-- Find the proof of this on the exercise sheet.
lemma is_cauchy_toReal (x : RatSeq) : IsCauchy x → IsCauchyReal x := by
  sorry

-- This is essentially the definition of the real numbers.
theorem real_numbers_complete {x : RealSeq} (hx : IsCauchyReal x) : ∃ a, TendsTo x a:= by
  exact ⟨(CauSeq.lim  ⟨x, cauchy_real_iff.2 hx⟩), CauSeq.equiv_lim ⟨_, cauchy_real_iff.2 hx⟩⟩

#check ℝ --ctrl + click to see the actual definition!

/-
Uniqueness of the limit of a sequence of real numbers follows from the
following result: two numbers are equal if their distance is less than any
positive number.
-/

#check @eq_of_forall_dist_le _ _ a b

lemma tends_toReal_unique {x : RealSeq} {a b : ℝ} (hx : TendsTo x a) (hy : TendsTo x b) :
  a = b := by
  apply eq_of_forall_dist_le
  intro ε hε
  have ⟨N, hN⟩ := hx (ε/2) (half_pos hε)
  have ⟨M, hM⟩ := hy (ε/2) (half_pos hε)
  let K := max N M
  have hKa : dist (x K) a < ε/2 := by
    exact hN K (le_max_left N M)
  have hKb : dist (x K) b < ε/2 := by
    exact hM K (le_max_right N M)
  calc
    dist a b ≤ dist a (x K) + dist (x K) b := by
      exact dist_triangle a (x K) b
    _ ≤ ε/2 + ε/2 := by
        apply le_of_lt
        exact add_lt_add (Metric.mem_ball'.mp (hN K (le_max_left N M))) hKb
    _ = ε := by
      rw[add_halves]

/-
Bonus: Finally we could use a structure to define the type of Cauchy sequences!
-/

structure RatCauchySeq where
  x : RatSeq
  isCauchy : IsCauchy x

example : RatCauchySeq ≃ {x : RatSeq | IsCauchy x} := by
  exact
    { toFun := fun x ↦ ⟨x.x, x.isCauchy⟩
      invFun := fun x ↦ ⟨x.1, x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

--By using a structure instead of a subtype we get direct access to the fields of the structure.
example (x : RatCauchySeq) : IsCauchy x.x := x.isCauchy


/-
This is roughly how the real numbers are defined in lean: as equivalence classes of Cauchy sequences
of rational numbers. Feel free to explore a bit here and try to define for example addition.
-/

def CauchyRel : RatCauchySeq → RatCauchySeq → Prop :=
  fun x y ↦ ∀ ε > 0, ∃ N, ∀ n≥ N, |(x.x n) - (y.x n)| < ε

theorem CauchyRel_equiv : Equivalence CauchyRel := by
  sorry

def CauchySetoid : Setoid RatCauchySeq where
  r := CauchyRel
  iseqv := CauchyRel_equiv

def Real := Quotient CauchySetoid

def Rat.toReal (x : ℚ) : Real := by
  refine Quotient.mk CauchySetoid ⟨⟨fun n => x⟩, ?_⟩
  sorry


end MySequences

end
