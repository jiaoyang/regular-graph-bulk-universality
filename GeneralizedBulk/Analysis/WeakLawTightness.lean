import GeneralizedBulk.Analysis.CappedMomentTransfer
import Mathlib.MeasureTheory.Measure.Tight

/-! A genuinely weakly convergent probability-law sequence in a proper
normed space is uniformly tight. No uniform prelimit moment bound is needed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace GeneralizedBulk.Analysis
variable {V : Type*} [NormedAddCommGroup V] [ProperSpace V] [CompleteSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]

theorem isTightMeasureSet_of_weakLawConverges
    (μ : ℕ → Measure V) [∀ n,IsProbabilityMeasure (μ n)]
    (ν : Measure V) [IsProbabilityMeasure ν] (hweak : External.WeakLawConverges μ ν) :
    IsTightMeasureSet (range μ) := by
  rw [IsTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases htop : ε = ∞
  · exact ⟨∅,isCompact_empty,fun η hη => by simp [htop]⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  have htν : IsTightMeasureSet ({ν} : Set (Measure V)) := isTightMeasureSet_singleton
  obtain ⟨K,hK,hνK⟩ := IsTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htν
    (ENNReal.ofReal (ε.toReal/4)) (ENNReal.ofReal_pos.mpr (by linarith))
  have hνtail : ν.real Kᶜ ≤ ε.toReal/4 := by
    simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ ε.toReal/4)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hνK ν (by simp))
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0 : V)
  let F := nonnegativeCap (fun x : V => max (‖x‖-R) 0)
    ((continuous_norm.sub continuous_const).max continuous_const) (fun x => le_max_right _ _) 1 (by norm_num)
  have hF0 (x : V) : 0 ≤ F x := le_min (le_max_right _ _) (by norm_num)
  have hF1 (x : V) : F x ≤ 1 := min_le_right _ _
  have hFzero (x : V) (hx : x ∈ K) : F x = 0 := by
    have hh : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hR hx
    simp [F,nonnegativeCap,max_eq_right (by linarith : ‖x‖-R ≤ 0)]
  have hνF : (∫ x,F x ∂ν) ≤ ε.toReal/4 := by
    have hh := integral_mono (F.integrable ν) ((integrable_const (1 : ℝ)).indicator hK.isClosed.measurableSet.compl)
      (show ∀ x,F x ≤ Kᶜ.indicator (fun _ => (1 : ℝ)) x from by
        intro x
        by_cases hx : x ∈ K
        · simp [hx,hFzero x hx]
        · simpa [hx] using hF1 x)
    have hInt : (∫ x,Kᶜ.indicator (fun _ : V => (1 : ℝ)) x ∂ν) = ν.real Kᶜ := by
      rw [integral_indicator_const 1 hK.isClosed.measurableSet.compl]
      simp
    exact (hh.trans_eq hInt).trans hνtail
  have hlate := (tendsto_order.mp (hweak F)).2 (ε.toReal/2) (by linarith)
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp hlate
  have hcapture (n : ℕ) : ∃ K : Set V,IsCompact K ∧ μ n Kᶜ ≤ ε := by
    obtain ⟨K,hK,hcap⟩ := IsTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (isTightMeasureSet_singleton (μ := μ n)) ε hε
    exact ⟨K,hK,hcap (μ n) (by simp)⟩
  choose Kn hKn hKncap using hcapture
  let A := Metric.closedBall (0 : V) (R+1) ∪ ⋃ i : Fin N0,Kn i.val
  have hA : IsCompact A := (isCompact_closedBall _ _).union (isCompact_iUnion (fun i : Fin N0 => hKn i.val))
  refine ⟨A,hA,?_⟩
  rintro _ ⟨n,rfl⟩
  by_cases hn : n < N0
  · have hsub : Kn n ⊆ A := by
      intro x hx
      exact Or.inr (mem_iUnion.mpr ⟨⟨n,hn⟩,hx⟩)
    exact (measure_mono (compl_subset_compl.mpr hsub)).trans (hKncap n)
  · have hball : (μ n).real (Metric.closedBall (0 : V) (R+1))ᶜ ≤ ∫ x,F x ∂μ n := by
      have hh := integral_mono ((integrable_const (1 : ℝ)).indicator Metric.isClosed_closedBall.measurableSet.compl)
        (F.integrable (μ n)) (show ∀ x,(Metric.closedBall (0 : V) (R+1))ᶜ.indicator (fun _ => (1 : ℝ)) x ≤ F x from by
          intro x
          by_cases hx : x ∈ Metric.closedBall (0 : V) (R+1)
          · simpa [hx] using hF0 x
          · have hnorm : R+1 < ‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx
            simp [hx,F,nonnegativeCap,max_eq_left (by linarith : 0 ≤ ‖x‖-R),min_eq_right (by linarith : 1 ≤ ‖x‖-R)])
      simpa only [integral_indicator_const _ Metric.isClosed_closedBall.measurableSet.compl,smul_eq_mul,mul_one] using hh
    have ht : (μ n).real (Metric.closedBall (0 : V) (R+1))ᶜ ≤ ε.toReal := hball.trans (by linarith [hN0 n (by omega)])
    calc
      μ n Aᶜ ≤ μ n (Metric.closedBall (0 : V) (R+1))ᶜ := measure_mono (compl_subset_compl.mpr subset_union_left)
      _ = ENNReal.ofReal ((μ n).real (Metric.closedBall (0 : V) (R+1))ᶜ) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal ht
      _ = ε := ENNReal.ofReal_toReal htop

end GeneralizedBulk.Analysis
