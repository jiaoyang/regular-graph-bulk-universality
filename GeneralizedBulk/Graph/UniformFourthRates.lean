import GeneralizedBulk.Graph.BulkFourthMoment
import GeneralizedBulk.LocalLaw.ProvedCoarseInput
import GeneralizedBulk.LocalLaw.ProvedLocalStarInput

/-! Fixed degree-dependent rates for the uniform fourth-moment theorem.
The rates are chosen before any graph eigenfamily or bad witness is selected. -/
noncomputable section
open MeasureTheory Filter
open scoped Classical Topology
namespace GeneralizedBulk.Graph
open GeneralizedBulk.LocalLawBridge GeneralizedBulk.Entropy.ChannelRates

def mixedFourthRigidityRate (d : ℕ) (hd : 3≤d) : ℝ :=
  min (Classical.choose (regularGraphLaw_source_weak_rigidity d hd)/2) (1/3)

theorem mixedFourthRigidityRate_pos (d : ℕ) (hd : 3≤d) :
    0 < mixedFourthRigidityRate d hd := by
  have h := (Classical.choose_spec (regularGraphLaw_source_weak_rigidity d hd)).1
  exact lt_min (by positivity) (by norm_num)

def mixedFourthExponent (d : ℕ) (hd : 3≤d) (k : ℕ) : ℝ :=
  bulkEntropyExponent k d (mixedFourthRigidityRate d hd) (1/1024)
    (entropyHeight k d (mixedFourthRigidityRate d hd))/36

theorem mixedFourthExponent_pos (d : ℕ) (hd : 3≤d) (k : ℕ) :
    0 < mixedFourthExponent d hd k := by
  have hc := entropyHeight_bounds k d (mixedFourthRigidityRate d hd) (mixedFourthRigidityRate_pos d hd)
  exact div_pos (bulkEntropyExponent_pos k d _ _ _ (by norm_num) hc.1 hc.2.2.1
    (by linarith [hc.2.2.2])) (by norm_num)

def mixedFourthFailureConstant (d : ℕ) : ℝ :=
  10 + SpectralConsequences.sourceEigenvectorConstant d / Real.sqrt ((d : ℝ)-1)

theorem mixedFourthFailureConstant_ge_ten (d : ℕ) (hd : 3≤d) :
    10 ≤ mixedFourthFailureConstant d := by
  have h := (SpectralConsequences.sourceEigenvectorConstant_positive d hd).le
  have hdiv := div_nonneg h (Real.sqrt_nonneg ((d : ℝ)-1))
  dsimp [mixedFourthFailureConstant]
  linarith

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Graph GeneralizedBulk.Graph.Configuration

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

/-- An explicit version of the common-event union bound. In particular the
exponent and constant can be fixed before a bad eigenfamily is chosen. -/
theorem commonEntropyGood_failure_explicit {P : Measure Ω} [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 0<d) (k : ℕ) (coarse localEvents : PolynomialGoodEvents P N)
    (β : ℝ) (hβc : β≤coarse.exponent) (hβl : β≤localEvents.exponent) (hβone : β≤1) :
    ∀ᶠ n in atTop,P.real (D.commonEntropyGood P k coarse localEvents n)ᶜ ≤
      (coarse.constant+localEvents.constant+1)*(N n : ℝ)^(-β) := by
  have hcount := D.entropyCountingGood_polynomial_failure hUniform hd k entropyCountingConstant
    entropyCountingConstant_bound (entropyCountingSimplicity d) (le_refl _) 1
  filter_upwards [hcount,eventually_ge_atTop coarse.threshold,eventually_ge_atTop localEvents.threshold]
    with n hn hnc hnl
  have hN : (1 : ℝ)≤N n := by exact_mod_cast D.size_pos n
  have hc : P.real (coarse.good n)ᶜ ≤ coarse.constant*(N n : ℝ)^(-coarse.exponent) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (coarse.failure_bound n hnc)
    rw [ENNReal.toReal_ofReal (mul_nonneg coarse.constant_pos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))] at h
    exact h
  have hl : P.real (localEvents.good n)ᶜ ≤ localEvents.constant*(N n : ℝ)^(-localEvents.exponent) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (localEvents.failure_bound n hnl)
    rw [ENNReal.toReal_ofReal (mul_nonneg localEvents.constant_pos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))] at h
    exact h
  have hpc := Real.rpow_le_rpow_of_exponent_le hN (show -coarse.exponent≤-β by linarith)
  have hpl := Real.rpow_le_rpow_of_exponent_le hN (show -localEvents.exponent≤-β by linarith)
  have hpone := Real.rpow_le_rpow_of_exponent_le hN (show -(1 : ℝ)≤-β by linarith)
  have hunion : P.real (D.commonEntropyGood P k coarse localEvents n)ᶜ ≤
      (P.real (coarse.good n)ᶜ+P.real (localEvents.good n)ᶜ)+
        P.real (D.entropyCountingGood k entropyCountingConstant (entropyCountingSimplicity d) n)ᶜ := by
    change P.real ((coarse.good n ∩ localEvents.good n) ∩ _)ᶜ ≤ _
    rw [Set.compl_inter]
    refine (measureReal_union_le _ _).trans (add_le_add_right ?_ _)
    rw [Set.compl_inter]
    exact measureReal_union_le _ _
  have hmc := mul_le_mul_of_nonneg_left hpc coarse.constant_pos.le
  have hml := mul_le_mul_of_nonneg_left hpl localEvents.constant_pos.le
  nlinarith only [hunion,hc,hl,hn,hmc,hml,hpone]

theorem provedCoarse_rigidityRate (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 3≤d) :
    (D.provedHYCoarseInput P hUniform hd).rigidity_exponent = mixedFourthRigidityRate d hd := rfl

end GeneralizedBulk.External.RegularSpectralData
