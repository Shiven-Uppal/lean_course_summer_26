import Mathlib.Analysis.BoxIntegral.UnitPartition
import LectureNotes.lecture9.examples9
import Exercises.Sheet7

open BoxIntegral MyFunctions

namespace MyRiemannIntegral

noncomputable section



/-!
This is a version of the fundamental theorem on the unit interval.  We use Mathlib's
`BoxIntegral.unitPartition` for the partition itself and only replace its tags by the points
provided by the mean value theorem.

* A `Prepartition I` is a finite collection of pairwise disjoint subboxes of `I`.
* A prepartition is `IsPartition` if its boxes cover all of `I`.
* A tagged prepartition is `IsSubordinate r` if every box lies in the closed ball with radius `r`
  around its tag.
* It is `IsHenstock` if the tag of every box belongs to that box.
-/

abbrev unitInterval : Box (Fin 1) :=
  intervalToBox 0 1 zero_lt_one

lemma unitInterval_hasIntegralVertices : BoxIntegral.hasIntegralVertices unitInterval := by
  refine ⟨fun _ => 0, fun _ => 1, ?_, ?_⟩
  · intro i
    simp
  · intro i
    norm_num [unitInterval, intervalToBox]

def stdPartition (N : ℕ) (hN : 0 < N) : TaggedPrepartition unitInterval :=
  @BoxIntegral.unitPartition.prepartition _ N ⟨Nat.ne_of_gt hN⟩ _ unitInterval

noncomputable def tagValue {f : ℝ → ℝ} (hf : Differentiable f)
    (J : Box (Fin 1)) : ℝ :=
  Classical.choose (mean_value_theorem (J.lower_lt_upper 0) hf)

lemma tagValue_feq {f : ℝ → ℝ} (hf : Differentiable f) (J : Box (Fin 1)) :
    (J.upper 0 - J.lower 0) * MyFunctions.deriv f (tagValue hf J) =
      f (J.upper 0) - f (J.lower 0) := by
  have h : MyFunctions.deriv f (tagValue hf J) =
      (f (J.upper 0) - f (J.lower 0)) / (J.upper 0 - J.lower 0) := by
    exact (Classical.choose_spec (mean_value_theorem (J.lower_lt_upper 0) hf)).2
  rw [h]
  have hne : J.upper 0 - J.lower 0 ≠ 0 := sub_ne_zero.mpr (J.lower_lt_upper 0).ne'
  field_simp [hne]

noncomputable def mvtTag {f : ℝ → ℝ} (hf : Differentiable f)
    (J : Box (Fin 1)) : Fin 1 → ℝ :=
  fun _ => tagValue hf J

lemma tagValue_mem {f : ℝ → ℝ} (hf : Differentiable f) (J : Box (Fin 1)) :
    tagValue hf J ∈ Set.Ioo (J.lower 0) (J.upper 0) := by
  exact (Classical.choose_spec (mean_value_theorem (J.lower_lt_upper 0) hf)).1

lemma mvtTag_mem_Icc {f : ℝ → ℝ} (hf : Differentiable f) (J : Box (Fin 1)) :
    mvtTag hf J ∈ Box.Icc J := by
  rw [Box.Icc_def]
  constructor <;> intro i <;> fin_cases i
  · exact ((tagValue_mem) hf J).1.le
  · exact (tagValue_mem hf J).2.le

open scoped Classical in
noncomputable def mvtTagFunction {f : ℝ → ℝ} (hf : Differentiable f)
    (N : ℕ) (hN : 0 < N) (J : Box (Fin 1)) : Fin 1 → ℝ :=
  if J ∈ (stdPartition N hN).boxes then mvtTag hf J else unitInterval.lower

noncomputable def mvtPartition {f : ℝ → ℝ} (hf : Differentiable f)
    (N : ℕ) (hN : 0 < N) : TaggedPrepartition unitInterval where
  toPrepartition := (stdPartition N hN).toPrepartition
  tag := mvtTagFunction hf N hN
  tag_mem_Icc := by
    intro J
    by_cases hJ : J ∈ (stdPartition N hN).boxes
    · rw [mvtTagFunction, if_pos hJ]
      apply Box.le_iff_Icc.mp ((stdPartition N hN).le_of_mem hJ)
      exact mvtTag_mem_Icc hf J
    · rw [mvtTagFunction, if_neg hJ]
      exact Box.lower_mem_Icc _

lemma mvtPartition_tag_of_mem {f : ℝ → ℝ} (hf : Differentiable f)
    (N : ℕ) (hN : 0 < N) {J : Box (Fin 1)} (hJ : J ∈ (mvtPartition hf N hN).boxes) :
    (mvtPartition hf N hN).tag J = mvtTag hf J := if_pos hJ

lemma mvtPartition_isHenstock {f : ℝ → ℝ} (hf : Differentiable f)
    (N : ℕ) (hN : 0 < N) : (mvtPartition hf N hN).IsHenstock := by
  intro J hJ
  rw [mvtPartition_tag_of_mem hf N hN hJ]
  exact mvtTag_mem_Icc hf J

lemma mvtPartition_isPartition {f : ℝ → ℝ} (hf : Differentiable f)
    (N : ℕ) (hN : 0 < N) : (mvtPartition hf N hN).IsPartition := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  exact BoxIntegral.unitPartition.prepartition_isPartition N unitInterval_hasIntegralVertices

lemma mvtPartition_isSubordinate {f : ℝ → ℝ} (hf : Differentiable f)
    (N : ℕ) (hN : 0 < N) (δ : Set.Ioi (0 : ℝ)) (hδ : (1 : ℝ) / N ≤ δ) :
    (mvtPartition hf N hN).IsSubordinate (fun _ => δ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  intro J hJ x hx
  rw [Metric.mem_closedBall]
  apply (Metric.dist_le_diam_of_mem (Box.isBounded_Icc _) hx
    (mvtPartition_isHenstock hf N hN J hJ)).trans
  obtain ⟨ν, hν, rfl⟩ := BoxIntegral.unitPartition.mem_prepartition_boxes_iff.mp hJ
  exact (BoxIntegral.unitPartition.diam_boxIcc N ν).trans hδ


/- We are applying `sum_partition_boxes` for this we turn the function we're summing
into a box additive map and use `BoxAdditiveMap.ofMapSplitAdd`.
For this regard the difference of the endpoint values as a function of the box.
We turn this function into a box-additive map: splitting an interval at
`x` gives two endpoint differences whose middle terms cancel.-/
lemma sum_endpointDifference (f : ℝ → ℝ) {π : Prepartition unitInterval}
    (hπ : π.IsPartition) :
    ∑ J ∈ π.boxes, (f (J.upper 0) - f (J.lower 0)) = f 1 - f 0 := by
  let F : Fin 1 →ᵇᵃ[unitInterval] ℝ :=
    BoxAdditiveMap.ofMapSplitAdd
      (fun J : Box (Fin 1) => f (J.upper 0) - f (J.lower 0)) unitInterval (by
        intro J hJ i x hx
        -- Since the index type is `Fin 1`, its only coordinate is `0`.
        -- Thus updating coordinate `i` with `x` makes coordinate `0` equal `x`.
        have hupdate (g : Fin 1 → ℝ) : Function.update g i x 0 = x := by
          rw [show (0 : Fin 1) = i from Subsingleton.elim _ _]
          exact Function.update_self i x g
        -- Expand the endpoints of the two boxes obtained by the split.
        -- After replacing their updated coordinates by `x`, the equality is
        -- the elementary telescoping identity
        -- `(f x - f lower) + (f upper - f x) = f upper - f lower`.
        simp only [Box.splitLower_def hx, Box.splitUpper_def hx,
          ← WithBot.some_eq_coe, Option.elim']
        rw [hupdate, hupdate]
        ring)
  change (∑ J ∈ π.boxes, F J) = F unitInterval
  exact F.sum_partition_boxes le_rfl hπ

lemma mvtPartition_riemannSum {f : ℝ → ℝ} (hf : Differentiable f)
    (N : ℕ) (hN : 0 < N) :
    MyRiemannIntegral.riemannSum (MyFunctions.deriv f) zero_lt_one (mvtPartition hf N hN) = f 1 - f 0 := by
  simp only [riemannSum, integralSum, riemannVolume, ContinuousLinearEquiv.coe_funUnique,
    Function.eval, Fin.default_eq_zero, Fin.isValue, BoxAdditiveMap.volume_apply,
    Finset.univ_unique, Finset.prod_singleton, smul_eq_mul]
  have hsum :
      (∑ J ∈ (mvtPartition hf N hN).boxes,
        (J.upper 0 - J.lower 0) * MyFunctions.deriv f ((mvtPartition hf N hN).tag J 0)) =
      ∑ J ∈ (mvtPartition hf N hN).boxes,
        (f (J.upper 0) - f (J.lower 0)) := by
    exact Finset.sum_congr rfl (fun J hJ => by
      rw [mvtPartition_tag_of_mem hf N hN hJ]
      exact tagValue_feq hf J)
  rw [hsum]
  exact sum_endpointDifference f (mvtPartition_isPartition hf N hN)

theorem integral_of_differentiable_unitInterval {f : ℝ → ℝ} (hf : Differentiable f)
    (hf' : Integrable (MyFunctions.deriv f) zero_lt_one) :
    HasIntegral (MyFunctions.deriv f) zero_lt_one (f 1 - f 0) := by
  obtain ⟨α, hα⟩ := hf'
  have heq : α = f 1 - f 0 := by
    apply eq_of_forall_dist_le
    intro ε hε
    obtain ⟨δ, hδ⟩ := hasIntegral_iff.mp hα ε hε
    obtain ⟨N, hN, hNδ⟩ := nat_one_div_le δ.prop
    let t := mvtPartition hf N hN
    rw [← mvtPartition_riemannSum hf N hN]
    specialize hδ t (mvtPartition_isHenstock hf N hN) (mvtPartition_isSubordinate hf N hN δ hNδ)
       (mvtPartition_isPartition hf N hN)
    rw [dist_comm]
    exact hδ.le
  rw [← heq]
  exact hα

end

end MyRiemannIntegral
