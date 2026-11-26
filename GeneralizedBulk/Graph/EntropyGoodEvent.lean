import GeneralizedBulk.Graph.HYResolventChannel
import GeneralizedBulk.Analysis.GoodEvents
import GeneralizedBulk.Analysis.EventIntersection

/-! The common entropy event is constructed from the actual HY and uniform
graph counting events. Its exceptional probability tends to zero. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Graph.Configuration
open GeneralizedBulk.Entropy

def entropyCountingConstant : ℝ := Classical.choose exists_log_factorial_error_bound

theorem entropyCountingConstant_bound : ∀ j : ℕ,|Real.log j.factorial-logFactorialMain j| ≤
    entropyCountingConstant+Real.log (j+1) := (Classical.choose_spec exists_log_factorial_error_bound).2

def entropyCountingSimplicity (d : ℕ) : ℕ := 8*d*(d+1)

end GeneralizedBulk.Graph.Configuration

namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Graph GeneralizedBulk.Graph.Configuration GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def commonEntropyGood (P : Measure Ω) [IsProbabilityMeasure P] (k : ℕ)
    (coarse localEvents : PolynomialGoodEvents P N) (n : ℕ) : Set Ω :=
  (coarse.good n ∩ localEvents.good n) ∩ D.entropyCountingGood k entropyCountingConstant (entropyCountingSimplicity d) n

theorem measurableSet_commonEntropyGood (P : Measure Ω) [IsProbabilityMeasure P] (k : ℕ)
    (coarse localEvents : PolynomialGoodEvents P N) (n : ℕ) : MeasurableSet (D.commonEntropyGood P k coarse localEvents n) :=
  ((coarse.measurable_good n).inter (localEvents.measurable_good n)).inter
    (D.measurableSet_entropyCountingGood k _ _ n)

theorem commonEntropyGood_failure_tendsto_zero {P : Measure Ω} [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 0 < d) (k : ℕ) (coarse localEvents : PolynomialGoodEvents P N) :
    Tendsto (fun n => P.real (D.commonEntropyGood P k coarse localEvents n)ᶜ) atTop (nhds 0) := by
  have hcount := D.entropyCountingGood_polynomial_failure hUniform hd k entropyCountingConstant
    entropyCountingConstant_bound (entropyCountingSimplicity d) (le_refl _) 1
  have hpow : Tendsto (fun n => (N n : ℝ)^(-(1:ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).comp (tendsto_natCast_atTop_atTop.comp D.size_tendsto)
  have hc : Tendsto (fun n => P.real (D.entropyCountingGood k entropyCountingConstant (entropyCountingSimplicity d) n)ᶜ)
      atTop (nhds 0) := squeeze_zero' (Eventually.of_forall (fun n => measureReal_nonneg)) hcount hpow
  exact intersection_failure_tendsto_zero P _ _
    (intersection_failure_tendsto_zero P _ _ (coarse.failure_tendsto_zero D.size_tendsto)
      (localEvents.failure_tendsto_zero D.size_tendsto)) hc

theorem commonEntropyGood_failure_polynomial {P : Measure Ω} [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 0 < d) (k : ℕ) (coarse localEvents : PolynomialGoodEvents P N) :
    ∃ β C : ℝ,0 < β ∧ 0 < C ∧ ∀ᶠ n in atTop,
      P.real (D.commonEntropyGood P k coarse localEvents n)ᶜ ≤ C*(N n : ℝ)^(-β) := by
  let β := min coarse.exponent (min localEvents.exponent 1)
  have hβ : 0 < β := lt_min coarse.exponent_pos (lt_min localEvents.exponent_pos (by norm_num))
  refine ⟨β,coarse.constant+localEvents.constant+1,hβ,by have hc := coarse.constant_pos; have hl := localEvents.constant_pos; linarith,?_⟩
  have hc := D.entropyCountingGood_polynomial_failure hUniform hd k entropyCountingConstant
    entropyCountingConstant_bound (entropyCountingSimplicity d) (le_refl _) 1
  filter_upwards [hc,eventually_ge_atTop coarse.threshold,eventually_ge_atTop localEvents.threshold]
    with n hn hnc hnl
  have hN : (1:ℝ) ≤ N n := by exact_mod_cast D.size_pos n
  have ha : P.real (coarse.good n)ᶜ ≤ coarse.constant*(N n : ℝ)^(-coarse.exponent) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (coarse.failure_bound n hnc)
    have hnonneg : 0 ≤ coarse.constant*(N n : ℝ)^(-coarse.exponent) :=
      mul_nonneg coarse.constant_pos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    rw [ENNReal.toReal_ofReal hnonneg] at hh
    exact hh
  have hb : P.real (localEvents.good n)ᶜ ≤ localEvents.constant*(N n : ℝ)^(-localEvents.exponent) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (localEvents.failure_bound n hnl)
    have hnonneg : 0 ≤ localEvents.constant*(N n : ℝ)^(-localEvents.exponent) :=
      mul_nonneg localEvents.constant_pos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    rw [ENNReal.toReal_ofReal hnonneg] at hh
    exact hh
  have hr1 := Real.rpow_le_rpow_of_exponent_le hN (show -coarse.exponent ≤ -β by dsimp [β]; linarith [min_le_left coarse.exponent (min localEvents.exponent 1)])
  have hr2 := Real.rpow_le_rpow_of_exponent_le hN (show -localEvents.exponent ≤ -β by
    have hh := (min_le_right coarse.exponent (min localEvents.exponent 1)).trans (min_le_left localEvents.exponent 1)
    dsimp [β]; linarith)
  have hr3 := Real.rpow_le_rpow_of_exponent_le hN (show -(1:ℝ) ≤ -β by
    have hh := (min_le_right coarse.exponent (min localEvents.exponent 1)).trans (min_le_right localEvents.exponent 1)
    dsimp [β]; linarith)
  have hsum : P.real (D.commonEntropyGood P k coarse localEvents n)ᶜ ≤
      (P.real (coarse.good n)ᶜ+P.real (localEvents.good n)ᶜ)+
        P.real (D.entropyCountingGood k entropyCountingConstant (entropyCountingSimplicity d) n)ᶜ := by
    change P.real ((coarse.good n ∩ localEvents.good n) ∩ _)ᶜ ≤ _
    rw [Set.compl_inter]
    refine (measureReal_union_le _ _).trans (add_le_add_right ?_ _)
    rw [Set.compl_inter]
    exact measureReal_union_le _ _
  have h1 := mul_le_mul_of_nonneg_left hr1 coarse.constant_pos.le
  have h2 := mul_le_mul_of_nonneg_left hr2 localEvents.constant_pos.le
  nlinarith only [hsum,ha,hb,hn,h1,h2,hr3]

end GeneralizedBulk.External.RegularSpectralData
