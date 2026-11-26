import GaussianWave.BS.Reused.Entropy.GridClippingLoss

/-! Finite clipping recovers the countable grid entropy of every genuine
finite-second-moment vector law. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical
namespace GaussianWave.BS.Reused.Entropy

lemma eventually_not_integerClippingTail {m : ℕ} (j : Fin m → ℤ) :
    ∀ᶠ K : ℕ in atTop, ¬ integerClippingTail K j := by
  filter_upwards [eventually_ge_atTop ((∑ i, (j i).natAbs) + 1)] with K hK
  rintro ⟨i, hi⟩
  have hab : (j i).natAbs < K := lt_of_lt_of_le
    (Nat.lt_succ_of_le (Finset.single_le_sum (fun k _ => Nat.zero_le ((j k).natAbs)) (Finset.mem_univ i))) hK
  have hlo : -(j i) ≤ ((-(j i)).natAbs : ℤ) := Int.le_natAbs
  simp only [Int.natAbs_neg] at hlo
  have hhi : j i ≤ ((j i).natAbs : ℤ) := Int.le_natAbs
  rcases hi with hi | hi <;> omega

variable {Ω : Type*} [MeasurableSpace Ω]

theorem tendsto_integerClippingTail_probability {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → Fin m → ℤ) (hY : Measurable Y) :
    Tendsto (fun K => μ.real {x | integerClippingTail K (Y x)}) atTop (𝓝 0) := by
  let F := fun K (x : Ω) => if integerClippingTail K (Y x) then (1 : ℝ) else 0
  have hm (K : ℕ) : MeasurableSet {x | integerClippingTail K (Y x)} :=
    measurableSet_countable_event Y hY _
  have hfm (K : ℕ) : AEStronglyMeasurable (F K) μ := by
    exact ((measurable_const.indicator (hm K))).aestronglyMeasurable
  have hbound (K : ℕ) : ∀ᵐ x ∂μ, ‖F K x‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    dsimp [F]
    split_ifs <;> norm_num
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun K => F K x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [] with x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_not_integerClippingTail (Y x)] with K hK
    simp [F, hK]
  have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
    hfm (integrable_const 1) hbound hlim
  have he (K : ℕ) : (∫ x, F K x ∂μ) = μ.real {x | integerClippingTail K (Y x)} := by
    simpa only [F, Set.indicator_apply, Set.mem_setOf_eq, smul_eq_mul, mul_one] using
      integral_indicator_const (μ := μ) (1 : ℝ) (hm K)
  simpa only [he, integral_zero] using h

/-- No Gaussian or coordinate independence is required for this clipping
limit; finite coordinate second moments are enough. -/
theorem tendsto_grid_clipping_entropy {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Fin m → ℝ) (hX : Measurable X)
    (hcoord : ∀ i, MemLp (fun x => X x i) 2 μ)
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun K => Finite.entropy (lawMass μ
      (codedClipIntegerVector (K+1) (by omega) ∘ gridLabel a ∘ X))) atTop
        (𝓝 (countableEntropy (lawMass μ (gridLabel a ∘ X)))) := by
  let Y := gridLabel a ∘ X
  let p := lawMass μ Y
  have hY : Measurable Y := (measurable_gridLabel a).comp hX
  have hp : ∀ j, 0 ≤ p j := lawMass_nonneg μ Y
  have hs : HasSum p 1 := lawMass_hasSum μ Y hY
  have hE : MemLp (fun x => integerEnergy (Y x)) 2 μ := memLp_gridEnergy μ X hX hcoord a ha
  have hmoment := (lawMass_weighted_hasSum μ Y hY integerEnergy (hE.integrable (by norm_num))).summable
  have hH := summable_integer_entropy p hp hs hmoment
  let B := ∑ i, |∫ x, X x i ^ 2 ∂μ|
  have hB (i : Fin m) : (∫ x, X x i ^ 2 ∂μ) ≤ B := by
    apply (le_abs_self _).trans
    exact Finset.single_le_sum (f := fun j => |∫ x, X x j ^ 2 ∂μ|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hnonneg (K : ℕ) : 0 ≤ countableEntropy p - Finite.entropy
      (lawMass μ (codedClipIntegerVector (K+1) (by omega) ∘ Y)) := by
    have he : countablePush p (codedClipIntegerVector (K+1) (by omega)) =
        lawMass μ (codedClipIntegerVector (K+1) (by omega) ∘ Y) := by
      funext j
      exact countablePush_lawMass μ Y hY _ j
    have h := countableEntropy_push_le p hp hs hH (codedClipIntegerVector (K+1) (by omega))
    rw [he, countableEntropy, tsum_fintype] at h
    exact sub_nonneg.mpr h
  have hprob : Tendsto (fun K => μ.real {x | integerClippingTail (K+1) (Y x)}) atTop (𝓝 0) :=
    (tendsto_integerClippingTail_probability μ Y hY).comp (tendsto_add_atTop_nat 1)
  have hupper : Tendsto (fun K => gridClippingLossConstant m a B *
      Real.sqrt (μ.real {x | integerClippingTail (K+1) (Y x)})) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0 |>.comp hprob).const_mul (gridClippingLossConstant m a B)
  have hgap : Tendsto (fun K => countableEntropy p - Finite.entropy
      (lawMass μ (codedClipIntegerVector (K+1) (by omega) ∘ Y))) atTop (𝓝 0) := by
    apply squeeze_zero hnonneg _ hupper
    intro K
    exact grid_clipping_entropy_loss_le μ X hX hcoord B hB a ha (K+1) (by omega)
  have h := (tendsto_const_nhds (x := countableEntropy p)).sub hgap
  simpa only [sub_sub_cancel, sub_zero, p, Y, Function.comp_assoc] using h
end GaussianWave.BS.Reused.Entropy
