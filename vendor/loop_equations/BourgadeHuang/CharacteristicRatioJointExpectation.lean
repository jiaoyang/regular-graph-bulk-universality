import BourgadeHuang.AnchoredPowerSeriesFamily
import BourgadeHuang.CharacteristicRatioAnalytic
import BourgadeHuang.MultipairCMS
import BourgadeHuang.CMS.OriginalBasis

/-! Joint analytic dependence of actual finite characteristic-ratio expectations.
The power series are constructed from scalar Cauchy integrals and are integrated
using the positive exponential-square anchor moment. -/
noncomputable section
open scoped Topology BigOperators NNReal ENNReal
open MeasureTheory Filter
namespace BourgadeHuang

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A common local identity preserves the uniform measurable analytic family. -/
theorem HasAnchoredPowerSeries.congr_eventually
    {F G : AnchoredCountingState → E → ℂ} {x : E}
    (hF : HasAnchoredPowerSeries F x)
    (heq : ∀ᶠ z in nhds x, ∀ s, F s z = G s z) : HasAnchoredPowerSeries G x := by
  obtain ⟨r,hr,p,L,hL,hpm,hp,hpb⟩ := hF
  obtain ⟨r',hr',hr'r,hp'⟩ := exists_common_powerSeries_congr hr hp heq
  refine ⟨r',hr',p,L,hL,hpm,hp',fun s n => ?_⟩
  exact norm_powerSeries_le_div_pow_of_radius_le (p s) (Real.exp_nonneg _)
    hr' (show (r' : ℝ) ≤ r from hr'r) (hpb s) n

theorem hasAnchoredPowerSeries_ratio_numerator {u v : ℂ}
    (huv : SameOpenHalfPlane u v) :
    HasAnchoredPowerSeries (fun s z => anchoredCharacteristicRatio s z v) u := by
  obtain ⟨r,hr,L,hL,hm,_,hp⟩ := exists_ratio_cauchySeries_uniform_measurable huv
  exact ⟨r,hr,fun s => cauchyPowerSeries (fun z => anchoredCharacteristicRatio s z v) u r,
    L,hL,hm,fun s => (hp s).1,fun s n => ((hp s).2.2 n).1⟩

theorem hasAnchoredPowerSeries_ratio_denominator {u v : ℂ}
    (huv : SameOpenHalfPlane u v) :
    HasAnchoredPowerSeries (fun s z => anchoredCharacteristicRatio s u z) v := by
  obtain ⟨r,hr,L,hL,_,hm,hp⟩ := exists_ratio_cauchySeries_uniform_measurable huv.symm
  exact ⟨r,hr,fun s => cauchyPowerSeries (fun z => anchoredCharacteristicRatio s u z) v r,
    L,hL,hm,fun s => (hp s).2.1,fun s n => ((hp s).2.2 n).2⟩

/-- The cocycle turns two scalar expansions into the actual joint ratio series. -/
theorem hasAnchoredPowerSeries_ratio_joint {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    HasAnchoredPowerSeries
      (fun s (p : ℂ × ℂ) => anchoredCharacteristicRatio s p.1 p.2) (u,v) := by
  have h₁ := HasAnchoredPowerSeries.pullback (ContinuousLinearMap.fst ℂ ℂ ℂ)
    (by
      apply (ContinuousLinearMap.fst ℂ ℂ ℂ).opNorm_le_bound zero_le_one
      intro p
      change ‖p.1‖ ≤ 1*‖p‖
      simpa only [one_mul] using norm_fst_le p) (u,v)
    (hasAnchoredPowerSeries_ratio_numerator huv)
  have h₂ := HasAnchoredPowerSeries.pullback (ContinuousLinearMap.snd ℂ ℂ ℂ)
    (by
      apply (ContinuousLinearMap.snd ℂ ℂ ℂ).opNorm_le_bound zero_le_one
      intro p
      change ‖p.2‖ ≤ 1*‖p‖
      simpa only [one_mul] using norm_snd_le p) (u,v)
    (hasAnchoredPowerSeries_ratio_denominator
      (sameOpenHalfPlane_self_of_offReal huv.right_offReal))
  apply (h₁.mul h₂).congr_eventually
  filter_upwards [(continuous_fst.tendsto (u,v)).eventually (sameOpenHalfPlane_nhds huv),
    (continuous_snd.tendsto (u,v)).eventually
      (sameOpenHalfPlane_nhds (sameOpenHalfPlane_self_of_offReal huv.right_offReal))] with p hp₁ hp₂
  intro s
  exact (anchoredCharacteristicRatio_cocycle s hp₁ hp₂).symm

def ratioCoordinateProjection (q : ℕ) (j : Fin q) :
    ((Fin q → ℂ) × (Fin q → ℂ)) →L[ℂ] (ℂ × ℂ) :=
  ((ContinuousLinearMap.proj (R := ℂ) j).comp
    (ContinuousLinearMap.fst ℂ (Fin q → ℂ) (Fin q → ℂ))).prod
  ((ContinuousLinearMap.proj (R := ℂ) j).comp
    (ContinuousLinearMap.snd ℂ (Fin q → ℂ) (Fin q → ℂ)))

@[simp] theorem ratioCoordinateProjection_apply {q : ℕ} (j : Fin q)
    (p : (Fin q → ℂ) × (Fin q → ℂ)) : ratioCoordinateProjection q j p = (p.1 j,p.2 j) := rfl

theorem norm_ratioCoordinateProjection_le (q : ℕ) (j : Fin q) :
    ‖ratioCoordinateProjection q j‖ ≤ 1 := by
  apply (ratioCoordinateProjection q j).opNorm_le_bound zero_le_one
  intro p
  rw [ratioCoordinateProjection_apply, one_mul, Prod.norm_def]
  exact max_le ((norm_le_pi_norm p.1 j).trans (norm_fst_le p))
    ((norm_le_pi_norm p.2 j).trans (norm_snd_le p))

theorem hasAnchoredPowerSeries_ratio_coordinate {q : ℕ} (u v : Fin q → ℂ)
    (j : Fin q) (huv : SameOpenHalfPlane (u j) (v j)) :
    HasAnchoredPowerSeries
      (fun s (p : (Fin q → ℂ) × (Fin q → ℂ)) => anchoredCharacteristicRatio s (p.1 j) (p.2 j)) (u,v) := by
  have h := HasAnchoredPowerSeries.pullback
    (f := fun s (p : ℂ × ℂ) => anchoredCharacteristicRatio s p.1 p.2)
    (ratioCoordinateProjection q j) (norm_ratioCoordinateProjection_le q j) (u,v)
    (hasAnchoredPowerSeries_ratio_joint huv)
  simpa only [ratioCoordinateProjection_apply] using h

/-- All numerator and denominator coordinates have one uniform measurable
multivariate series, with an exponential anchor bound on its coefficients. -/
theorem hasAnchoredPowerSeries_ratios_joint {q : ℕ} (u v : Fin q → ℂ)
    (huv : ∀ j, SameOpenHalfPlane (u j) (v j)) :
    HasAnchoredPowerSeries
      (fun s (p : (Fin q → ℂ) × (Fin q → ℂ)) => anchoredCharacteristicRatios s p.1 p.2) (u,v) := by
  change HasAnchoredPowerSeries
    (fun s (p : (Fin q → ℂ) × (Fin q → ℂ)) =>
      ∏ j ∈ Finset.univ, anchoredCharacteristicRatio s (p.1 j) (p.2 j)) (u,v)
  apply HasAnchoredPowerSeries.finset_prod
  intro j _
  exact hasAnchoredPowerSeries_ratio_coordinate u v j (huv j)

/-- Positive exponential-square anchor moments imply genuine joint analyticity
of the expected product of all characteristic ratios. -/
theorem analyticAt_integral_characteristicRatios_joint {q : ℕ}
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j)) :
    AnalyticAt ℂ (fun p : (Fin q → ℂ) × (Fin q → ℂ) =>
      ∫ s, anchoredCharacteristicRatios s p.1 p.2 ∂ν) (u,v) :=
  (hasAnchoredPowerSeries_ratios_joint u v huv).analyticAt_integral ν ha he

/-- The genuine ratio expectation in the combined CMS coordinate space. -/
def expectedRatioFunction {q : ℕ} (ν : Measure AnchoredCountingState) : CMS.Point (q+q) → ℂ :=
  CMS.blockFunction (expectedCharacteristicRatios (q := q) ν)

@[simp] theorem expectedRatioFunction_append {q : ℕ} (ν : Measure AnchoredCountingState)
    (u v : CMS.Point q) : expectedRatioFunction ν (Fin.append u v) =
      expectedCharacteristicRatios ν u v := CMS.blockFunction_append _ _ _

/-- Joint analyticity on the combined CMS coordinates is a consequence of the
constructed uniform series, with no analytic regularity assumed of the expectation. -/
theorem analyticAt_expectedRatioFunction {q : ℕ}
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (z : CMS.Point (q+q))
    (hz : ∀ j, SameOpenHalfPlane (z (Fin.castAdd q j)) (z (Fin.natAdd q j))) :
    AnalyticAt ℂ (expectedRatioFunction ν) z := by
  have hleft : AnalyticAt ℂ (fun p : CMS.Point (q+q) => fun j : Fin q => p (Fin.castAdd q j)) z :=
    AnalyticAt.pi (fun j => (ContinuousLinearMap.proj (R := ℂ) (Fin.castAdd q j)).analyticAt z)
  have hright : AnalyticAt ℂ (fun p : CMS.Point (q+q) => fun j : Fin q => p (Fin.natAdd q j)) z :=
    AnalyticAt.pi (fun j => (ContinuousLinearMap.proj (R := ℂ) (Fin.natAdd q j)).analyticAt z)
  exact (analyticAt_integral_characteristicRatios_joint ν ha he _ _ hz).comp
    (f := fun p : CMS.Point (q+q) =>
      ((fun j : Fin q => p (Fin.castAdd q j)),(fun j : Fin q => p (Fin.natAdd q j))))
    (hleft.prod hright)

/-- The actual jointly analytic expectation satisfies both original CMS blocks. -/
theorem expectedRatioFunction_solvesOriginalAt {q : ℕ}
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .two)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (z : CMS.Point (q+q)) (hfree : CMS.CollisionFree z)
    (hz : ∀ j, SameOpenHalfPlane (z (Fin.castAdd q j)) (z (Fin.natAdd q j))) :
    CMS.SolvesOriginalAt (n := q) (m := q) (expectedRatioFunction ν) z := by
  let u : CMS.Point q := fun j => z (Fin.castAdd q j)
  let v : CMS.Point q := fun j => z (Fin.natAdd q j)
  have happ : Fin.append u v = z := Fin.append_castAdd_natAdd
  have hf := (CMS.collisionFree_append u v).mp (happ ▸ hfree)
  have heq : CMS.restrictBlocks (expectedRatioFunction (q := q) ν) = expectedCharacteristicRatios ν := by
    funext u v
    exact expectedRatioFunction_append ν u v
  change (∀ i, CMS.leftOriginal i (CMS.restrictBlocks (expectedRatioFunction ν)) u v = 0) ∧
    (∀ i, CMS.rightOriginal i (CMS.restrictBlocks (expectedRatioFunction ν)) u v = 0)
  rw [heq]
  exact ⟨expectedCharacteristicRatios_leftOriginal ν hh ha he u v hz hf.1 hf.2.2,
    expectedCharacteristicRatios_rightOriginal ν hh ha he u v hz hf.2.1 hf.2.2⟩

end BourgadeHuang
