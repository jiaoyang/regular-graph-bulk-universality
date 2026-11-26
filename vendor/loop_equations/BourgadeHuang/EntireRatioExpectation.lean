import BourgadeHuang.EntireRatioBounds

/-! Actual multipair ratios with unrestricted entire numerator coordinates.
Their joint expectation is analytic wherever every denominator is off-real. -/
noncomputable section
open scoped Topology BigOperators NNReal ENNReal
open MeasureTheory Filter
namespace BourgadeHuang

theorem hasAnchoredPowerSeries_entireRatio_joint (u : ℂ) {v : ℂ} (hv : v.im ≠ 0) :
    HasAnchoredPowerSeries
      (fun s (p : ℂ × ℂ) => entireCharacteristicRatio s p.1 p.2) (u,v) := by
  have h₁ := HasAnchoredPowerSeries.pullback (ContinuousLinearMap.fst ℂ ℂ ℂ)
    (by
      apply (ContinuousLinearMap.fst ℂ ℂ ℂ).opNorm_le_bound zero_le_one
      intro p
      change ‖p.1‖ ≤ 1*‖p‖
      simpa only [one_mul] using norm_fst_le p) (u,v)
    (hasAnchoredPowerSeries_entireNumerator u)
  have h₂ := HasAnchoredPowerSeries.pullback (ContinuousLinearMap.snd ℂ ℂ ℂ)
    (by
      apply (ContinuousLinearMap.snd ℂ ℂ ℂ).opNorm_le_bound zero_le_one
      intro p
      change ‖p.2‖ ≤ 1*‖p‖
      simpa only [one_mul] using norm_snd_le p) (u,v)
    (hasAnchoredPowerSeries_inverseEntireNumerator hv)
  simpa only [entireCharacteristicRatio,div_eq_mul_inv] using h₁.mul h₂

def entireCharacteristicRatios {q : ℕ} (s : AnchoredCountingState) (u v : Fin q → ℂ) : ℂ :=
  ∏ j, entireCharacteristicRatio s (u j) (v j)

theorem entireCharacteristicRatios_eq_anchored {q : ℕ} (s : AnchoredCountingState)
    (u v : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j)) :
    entireCharacteristicRatios s u v = anchoredCharacteristicRatios s u v := by
  apply Finset.prod_congr rfl
  intro j _
  exact entireCharacteristicRatio_eq_anchored s (huv j)

theorem measurable_entireCharacteristicRatios {q : ℕ} (u v : Fin q → ℂ) :
    Measurable (fun s => entireCharacteristicRatios s u v) :=
  Finset.measurable_prod _ (fun j _ => measurable_entireCharacteristicRatio (u j) (v j))

theorem anchoredExponentialBound_entireCharacteristicRatio (u : ℂ) {v : ℂ} (hv : v.im ≠ 0) :
    AnchoredExponentialBound (fun s => entireCharacteristicRatio s u v) := by
  obtain ⟨R,hR,L,_,_,hb⟩ := exists_inverseEntireNumerator_bound hv
  have hF : AnchoredExponentialBound (fun s => anchoredEntireNumerator s u) :=
    ⟨entireNumeratorGrowthConstant ‖u‖, fun s => norm_anchoredEntireNumerator_le ‖u‖ (norm_nonneg _) s le_rfl⟩
  have hI : AnchoredExponentialBound (fun s => (anchoredEntireNumerator s v)⁻¹) :=
    ⟨L,fun s => hb s v (Metric.mem_closedBall_self R.coe_nonneg)⟩
  simpa only [entireCharacteristicRatio,div_eq_mul_inv] using hF.mul hI

theorem anchoredExponentialBound_entireCharacteristicRatios {q : ℕ}
    (u v : Fin q → ℂ) (hv : ∀ j, (v j).im ≠ 0) :
    AnchoredExponentialBound (fun s => entireCharacteristicRatios s u v) :=
  AnchoredExponentialBound.finset_prod _ _
    (fun j _ => anchoredExponentialBound_entireCharacteristicRatio (u j) (hv j))

theorem integrable_entireCharacteristicRatios {q : ℕ}
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v : Fin q → ℂ) (hv : ∀ j, (v j).im ≠ 0) :
    Integrable (fun s => entireCharacteristicRatios s u v) ν := by
  obtain ⟨L,hL⟩ := anchoredExponentialBound_entireCharacteristicRatios u v hv
  have hi := integrable_anchor_polynomial_exp ν ha he (by norm_num : (0:ℝ) ≤ 1) 0 L
  simp only [pow_zero,mul_one,one_mul] at hi
  exact hi.mono' (measurable_entireCharacteristicRatios u v).aestronglyMeasurable
    (Filter.Eventually.of_forall hL)

theorem hasAnchoredPowerSeries_entireRatio_coordinate {q : ℕ} (u v : Fin q → ℂ)
    (j : Fin q) (hv : (v j).im ≠ 0) :
    HasAnchoredPowerSeries
      (fun s (p : (Fin q → ℂ) × (Fin q → ℂ)) => entireCharacteristicRatio s (p.1 j) (p.2 j)) (u,v) := by
  have h := HasAnchoredPowerSeries.pullback
    (f := fun s (p : ℂ × ℂ) => entireCharacteristicRatio s p.1 p.2)
    (ratioCoordinateProjection q j) (norm_ratioCoordinateProjection_le q j) (u,v)
    (hasAnchoredPowerSeries_entireRatio_joint (u j) hv)
  simpa only [ratioCoordinateProjection_apply] using h

theorem hasAnchoredPowerSeries_entireRatios_joint {q : ℕ} (u v : Fin q → ℂ)
    (hv : ∀ j, (v j).im ≠ 0) :
    HasAnchoredPowerSeries
      (fun s (p : (Fin q → ℂ) × (Fin q → ℂ)) => entireCharacteristicRatios s p.1 p.2) (u,v) := by
  change HasAnchoredPowerSeries
    (fun s (p : (Fin q → ℂ) × (Fin q → ℂ)) =>
      ∏ j ∈ Finset.univ, entireCharacteristicRatio s (p.1 j) (p.2 j)) (u,v)
  apply HasAnchoredPowerSeries.finset_prod
  intro j _
  exact hasAnchoredPowerSeries_entireRatio_coordinate u v j (hv j)

def expectedEntireCharacteristicRatios {q : ℕ} (ν : Measure AnchoredCountingState)
    (u v : Fin q → ℂ) : ℂ := ∫ s, entireCharacteristicRatios s u v ∂ν

theorem expectedEntireCharacteristicRatios_eq {q : ℕ} (ν : Measure AnchoredCountingState)
    (u v : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j)) :
    expectedEntireCharacteristicRatios ν u v = expectedCharacteristicRatios ν u v := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => entireCharacteristicRatios_eq_anchored s u v huv)

theorem analyticAt_expectedEntireCharacteristicRatios_joint {q : ℕ}
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v : Fin q → ℂ) (hv : ∀ j, (v j).im ≠ 0) :
    AnalyticAt ℂ (fun p : (Fin q → ℂ) × (Fin q → ℂ) =>
      expectedEntireCharacteristicRatios ν p.1 p.2) (u,v) :=
  (hasAnchoredPowerSeries_entireRatios_joint u v hv).analyticAt_integral ν ha he

/-- The globally extended expectation in the combined CMS coordinate space. -/
def expectedEntireRatioFunction {q : ℕ} (ν : Measure AnchoredCountingState) : CMS.Point (q+q) → ℂ :=
  CMS.blockFunction (expectedEntireCharacteristicRatios (q := q) ν)

@[simp] theorem expectedEntireRatioFunction_append {q : ℕ} (ν : Measure AnchoredCountingState)
    (u v : CMS.Point q) : expectedEntireRatioFunction ν (Fin.append u v) =
      expectedEntireCharacteristicRatios ν u v := CMS.blockFunction_append _ _ _

theorem analyticAt_expectedEntireRatioFunction {q : ℕ}
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (z : CMS.Point (q+q)) (hz : ∀ j, (z (Fin.natAdd q j)).im ≠ 0) :
    AnalyticAt ℂ (expectedEntireRatioFunction ν) z := by
  have hleft : AnalyticAt ℂ (fun p : CMS.Point (q+q) => fun j : Fin q => p (Fin.castAdd q j)) z :=
    AnalyticAt.pi (fun j => (ContinuousLinearMap.proj (R := ℂ) (Fin.castAdd q j)).analyticAt z)
  have hright : AnalyticAt ℂ (fun p : CMS.Point (q+q) => fun j : Fin q => p (Fin.natAdd q j)) z :=
    AnalyticAt.pi (fun j => (ContinuousLinearMap.proj (R := ℂ) (Fin.natAdd q j)).analyticAt z)
  exact (analyticAt_expectedEntireCharacteristicRatios_joint ν ha he _ _ hz).comp
    (f := fun p : CMS.Point (q+q) =>
      ((fun j : Fin q => p (Fin.castAdd q j)),(fun j : Fin q => p (Fin.natAdd q j))))
    (hleft.prod hright)

end BourgadeHuang
