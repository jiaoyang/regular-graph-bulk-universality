import GeneralizedBulk.Graph.WindowHYFactorization
import GeneralizedBulk.Graph.BulkFourthMoment

/-! Actual finite-window Gaussian marks factor from every bounded scalar
statistic. The common graph event, its failure, and all fourth moments are
constructed from the permitted BS/HY inputs and proved graph counting. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.KestenMcKay GeneralizedBulk.Gaussian
open GeneralizedBulk.Entropy.ChannelRates GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 2500000 in
theorem BS_window_count_factorization_of_bulk_entropy {m : ℕ} (hm : 0 < m) [Nonempty Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (K : Set ℝ) (BS : BSQualitativeInput D P K)
    (HC : HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast BS.degree_ge_three)))
    (J : Set ℝ) (hJ : IsCompact J) (hJbulk : ∀ E ∈ J,E^2 < 4*((d : ℝ)-1))
    (c0 : ℝ) (hcchannel : c0 < channelNoiseExponent (channelTheta 1 d))
    (hcrigidity : c0 < HC.rigidity_exponent) (hcsmall : c0 ≤ 1/16)
    (HL : HYLocalStarInput D P J c0 (treeGreenStar d (by exact_mod_cast BS.degree_ge_three)))
    (E sigma R gap : ℝ) (hsigma : 0 < sigma) (hE : E ∈ K) (hgap : 0 < gap)
    (hwindow : Icc (E-gap) (E+gap) ⊆ J)
    (leaf : Fin d) (F : BoundedContinuousFunction ((Fin m × Fin 4) → ℝ) ℝ)
    (H : ℕ → Ω → ℂ) (hH : ∀ n,Measurable (H n)) (C : ℝ) (hC : ∀ n ω,‖H n ω‖ ≤ C) :
    Tendsto (fun n => (∫ ω,D.windowCountWeight n E sigma R m (H n) ω*
      (↑(∫ x,F x ∂D.twoEdgeLaw n ω
        (D.paddedWindowSelection n ω E sigma (-R) R (fun _ => D.bulkPaddingIndex E m n)) leaf) : ℂ) ∂P)-
      (∫ ω,D.windowCountWeight n E sigma R m (H n) ω ∂P)*
        (↑(∫ x,F x ∂finiteMarkLaw (E/d) m) : ℂ)) atTop (nhds 0) := by
  let hd := BS.degree_ge_three
  let good := fun n => D.commonEntropyGood P 1 HC.events HL.events n ∩ BS.good m n
  have hgood (n) : MeasurableSet (good n) :=
    (D.measurableSet_commonEntropyGood P 1 HC.events HL.events n).inter (BS.measurable_good m n)
  have hbad : Tendsto (fun n => P.real (good n)ᶜ) atTop (nhds 0) :=
    intersection_failure_tendsto_zero P _ _
      (D.commonEntropyGood_failure_tendsto_zero hUniform (by have hh := BS.degree_ge_three; omega) 1 HC.events HL.events)
      (by exact ENNReal.tendsto_toReal ENNReal.zero_ne_top |>.comp (BS.good_probability m))
  have hEdegree := D.BS_bulk_abs_lt_degree P K BS E hE
  have hEd : E ≠ (d : ℝ) := by
    intro heq
    rw [heq,abs_of_nonneg (Nat.cast_nonneg d)] at hEdegree
    exact lt_irrefl _ hEdegree
  have hEbulk : E ∈ Ioo (-radius d) (radius d) := by
    exact abs_lt.mp (by simpa only [radius] using BS.compact_bulk.2 E hE)
  apply D.BS_window_count_factorization_of_HY_padding hm P K BS (by exact_mod_cast BS.degree_ge_three) HC
    E sigma R hsigma hE hEd hEbulk good hgood hbad
    (Eventually.of_forall (fun n ω hω => hω.2))
    (Eventually.of_forall (fun n ω hω => hω.1.1.1)) _ leaf F H hH C hC
  have hfourth := D.HY_common_event_fourth_le_one BS.degree_ge_three HC 1 (by norm_num) J hJ hJbulk c0
    hcchannel hcrigidity hcsmall HL
  have htol := D.windowPaddingTolerance_tendsto (by exact_mod_cast BS.degree_ge_three) HC E sigma R hEbulk m
  have hsmall := (tendsto_order.mp htol).2 gap hgap
  filter_upwards [hfourth,hsmall] with n hfourth hsmall ω hω k hk hnear j
  apply hfourth ω hω.1 (fun _ : Fin 1 => k) (fun a b hab => Subsingleton.elim a b)
    (fun a => ?_) (0,j) (0,j) (0,j) (0,j)
  have hh := abs_le.mp (hnear.trans hsmall.le)
  exact hwindow ⟨by linarith,by linarith⟩

end GeneralizedBulk.External.RegularSpectralData
