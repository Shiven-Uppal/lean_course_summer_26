import Mathlib.Analysis.BoxIntegral.Basic
import Mathlib.Analysis.BoxIntegral.Partition.Tagged
import Exercises.Sheet7

open BoxIntegral MyFunctions


variable {x : ℝ}

namespace MyRiemannIntegral

/-!
We define the Riemann integral by specializing Mathlib's box integral to one dimension:

* the real interval `[a, b]` is represented as a box indexed by `Fin 1`;
* a function `f : ℝ → ℝ` is evaluated on this one coordinate using `ev`;
* `riemannVolume` computes the length of a 1-dimensional box (i.e. and interval).
* `riemannSum` computes the usual Riemann sum.
* `HasIntegral` uses the library's `IntegrationParams.Riemann`. The theorem
  `hasIntegral_iff` below rewrites this general box-integral definition in the familiar
  ε-δ form using tagged partitions;
* finally, `riemannIntegral` chooses the value whose existence is asserted by `Integrable`
  (and is defined to be `0` when the function is not integrable).
-/

variable (n : ℕ)

#check Fin n → ℝ -- x ∈ R^n as function {0, ..., n-1} → ℝ

-- the identification of `Fin 1 (= {0}) → ℝ` with `ℝ`.
noncomputable abbrev ev := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ

#check Box

abbrev intervalToBox (a b : ℝ) (h : a < b) : Box (Fin 1) :=
  Box.mk (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) (fun _ => h)

-- map: Intervals × ℝ -> ℝ which is additive in the boxes and linear in the real variable.
noncomputable abbrev riemannVolume : (Fin 1 →ᵇᵃ[⊤] ℝ →L[ℝ] ℝ) :=
  BoxAdditiveMap.volume

noncomputable abbrev riemannSum {a b : ℝ} (f : ℝ → ℝ) (hab : a < b)
    (t : TaggedPrepartition (intervalToBox a b hab)) : ℝ :=
  BoxIntegral.integralSum (fun g => f (ev g)) riemannVolume t

-- specialisation of the libary defn
def HasIntegral {a b : ℝ} (f : ℝ → ℝ) (hab : a < b) (α : ℝ) : Prop :=
  BoxIntegral.HasIntegral (intervalToBox a b hab) (IntegrationParams.Riemann)
  (fun g => f (ev g)) (riemannVolume) α

def Integrable {a b : ℝ} (f : ℝ → ℝ) (hab : a < b) : Prop :=
  ∃ α, HasIntegral f hab α

open scoped Classical in
noncomputable def riemannIntegral {a b : ℝ} (f : ℝ → ℝ) (hab : a < b) : ℝ :=
  if h : Integrable f hab then
    Classical.choose h
  else
    0

-- exercise :)
theorem Integrable.hasRiemannIntegral {a b : ℝ} (f : ℝ → ℝ) (hab : a < b) (h : Integrable f hab) :
    HasIntegral f hab (riemannIntegral f hab) := by sorry

 -- the property the the tag is contained in the interval of the corresponding box
#check TaggedPrepartition.IsHenstock

-- the property that the distances between the tag and the corresponding box is less than δ
#check TaggedPrepartition.IsSubordinate

-- special case defn is equivalent to the general defn of HasIntegral
theorem hasIntegral_iff {a b : ℝ} {f : ℝ → ℝ} {hab : a < b} {α : ℝ} :
    HasIntegral f hab α ↔ ∀ ε > 0, ∃ δ : Set.Ioi 0,
    ∀ t : TaggedPrepartition (intervalToBox a b hab),
      t.IsHenstock → t.IsSubordinate (fun _ => δ) → t.IsPartition →
      dist (riemannSum f hab t) α < ε := by
  unfold HasIntegral
  rw [BoxIntegral.hasIntegral_iff]
  constructor
  · intro h ε hε
    obtain ⟨r, hr, hdist⟩ := h (ε / 2) (by linarith)
    let δ : Set.Ioi (0 : ℝ) := r 0 0
    refine ⟨δ, ?_⟩
    intro t hthen htsub htpart
    have hmem : IntegrationParams.Riemann.MemBaseSet
        (intervalToBox a b hab) 0 (r 0) t := by
      refine ⟨?_, fun _ => hthen, ?_, ?_⟩
      · rw [funext (hr 0 (rfl))]
        simpa only [δ] using htsub
      · simp only [IntegrationParams.Riemann, Bool.false_eq_true, nonpos_iff_eq_zero,
        IsEmpty.forall_iff]
      · simp only [IntegrationParams.Riemann, Bool.false_eq_true, nonpos_iff_eq_zero,
        IsEmpty.forall_iff]
    have hle := hdist 0 t hmem htpart
    linarith
  · intro h ε hε
    obtain ⟨δ, hδ⟩ := h ε hε
    let r : NNReal → (Fin 1 → ℝ) → Set.Ioi (0 : ℝ) := fun _ _ => δ
    refine ⟨r, fun c Hr x => rfl, ?_⟩
    · intro c t ht htpart
      exact (hδ t (ht.isHenstock (by trivial)) ht.isSubordinate htpart).le

end MyRiemannIntegral
