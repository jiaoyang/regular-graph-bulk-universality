import GeneralizedBulk.Graph.DyadicReciprocal

/-! Polynomial reciprocal-distance bounds from the genuine HY dyadic counts. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology Classical
namespace GeneralizedBulk.Graph

/-- The finite dyadic depth is bounded by its actual real logarithm. -/
theorem nat_clog_two_le_log (N : ℕ) :
    (Nat.clog 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 + 1 := by
  rw [← Real.natCeil_logb_natCast 2 N]
  have hnonneg : 0 ≤ Real.logb (2 : ℝ) (N : ℝ) :=
    div_nonneg (Real.log_natCast_nonneg N) (Real.log_pos (by norm_num)).le
  simpa only [Real.logb, Nat.cast_ofNat] using (Nat.ceil_lt_add_one hnonneg).le

/-- Every fixed extra dyadic depth is negligible compared with any positive
power of the graph size. -/
theorem dyadic_depth_eventually_le_rpow (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (alpha : ℝ) (halpha : 0 < alpha) (L : ℕ) :
    ∀ᶠ n in atTop, (Nat.clog 2 (N n) + L : ℕ) ≤
      (1 / Real.log 2 + 1 + (L : ℝ)) * (N n : ℝ) ^ alpha := by
  have hlog := (isLittleO_log_rpow_atTop halpha).bound (c := 1) (by norm_num)
  have hNat : Tendsto (fun n => (N n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  filter_upwards [hNat.eventually hlog, hN.eventually (eventually_ge_atTop 1)] with n hn hNn
  have hlogn : Real.log (N n : ℝ) ≤ (N n : ℝ) ^ alpha := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), one_mul] using hn
  have hpow : 1 ≤ (N n : ℝ) ^ alpha :=
    Real.one_le_rpow (by exact_mod_cast hNn) halpha.le
  have hclog := nat_clog_two_le_log (N n)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd := div_le_div_of_nonneg_right hlogn hlog2.le
  have hconst := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 1 + (L : ℝ) by positivity)
  push_cast
  calc
    _ ≤ Real.log (N n : ℝ) / Real.log 2 + 1 + (L : ℝ) := by linarith only [hclog]
    _ ≤ (N n : ℝ) ^ alpha / Real.log 2 + (1 + (L : ℝ)) * (N n : ℝ) ^ alpha := by
      linarith only [hd, hconst]
    _ = _ := by ring

/-- Multiplying the true mesoscopic height by `N` gives exactly `N^alpha`. -/
theorem size_mul_mesoscopicScale (N : ℕ) (hN : 0 < N) (alpha : ℝ) :
    (N : ℝ) * (N : ℝ) ^ (-1 + alpha) = (N : ℝ) ^ alpha := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  calc
    _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-1 + alpha) := by rw [Real.rpow_one]
    _ = (N : ℝ) ^ ((1 : ℝ) + (-1 + alpha)) := (Real.rpow_add hNR _ _).symm
    _ = _ := by congr 1; ring

/-- `clog₂ N + L` dyadic shells cover every fixed window of radius `2^L`
at the mesoscopic scale; no spectral tightness assumption is used. -/
theorem dyadic_mesoscopicRadius_covers (N : ℕ) (hN : 0 < N)
    (alpha : ℝ) (halpha : 0 ≤ alpha) (L : ℕ) :
    (2 : ℝ) ^ L ≤ dyadicRadius ((N : ℝ) ^ (-1 + alpha)) (Nat.clog 2 N + L) := by
  have hh : 0 ≤ (N : ℝ) ^ (-1 + alpha) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hdepth : (N : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 N := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) N
  have hprod := mul_le_mul_of_nonneg_right hdepth hh
  rw [size_mul_mesoscopicScale N hN alpha] at hprod
  have hpow : 1 ≤ (N : ℝ) ^ alpha :=
    Real.one_le_rpow (by exact_mod_cast hN) halpha
  calc
    _ ≤ (2 : ℝ) ^ L * ((2 : ℝ) ^ Nat.clog 2 N * (N : ℝ) ^ (-1 + alpha)) :=
      by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hpow.trans hprod) (by positivity : 0 ≤ (2 : ℝ) ^ L)
    _ = _ := by dsimp [dyadicRadius]; rw [pow_add]; ring

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

/-- HY implies the actual uniform `N^alpha` normalized reciprocal-distance
bound on every fixed bulk window down to height `cstar / N`. -/
theorem normalized_reciprocal_sum_le_rpow_of_HY
    {P : Measure Ω} [IsProbabilityMeasure P] {K : Set ℝ} {alpha : ℝ}
    (H : HYMesoscopicInput D P K alpha) (E : ℝ) (hE : E ∈ K)
    (cstar : ℝ) (hcstar : 0 < cstar) (L : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop,
      ∀ ω ∈ H.events.good n, ∀ s : Finset (Fin (N n)),
      (∀ k ∈ s, |D.eigenvalue n ω k - E| ≤ (2 : ℝ) ^ L) →
      ∀ eta : ℝ, 0 < eta → cstar ≤ (N n : ℝ) * eta →
        (∑ k ∈ s, ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - spectralParameter E eta)⁻¹‖) ≤
          B * (N n : ℝ) ^ alpha := by
  let C := max H.events.constant 1
  let Q := 1 / Real.log 2 + 1 + (L : ℝ)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨2 * C / cstar + 4 * C * Q, by positivity, ?_⟩
  filter_upwards [dyadic_depth_eventually_le_rpow N D.size_tendsto alpha H.alpha_pos L,
    eventually_ge_atTop H.events.threshold] with n hdepth hn
  intro ω hω s hs eta heta hheight
  let h := (N n : ℝ) ^ (-1 + alpha)
  have hh : 0 < h := Real.rpow_pos_of_pos (by exact_mod_cast D.size_pos n) _
  have hcover (k : Fin (N n)) (hk : k ∈ s) :
      |D.eigenvalue n ω k - E| ≤ dyadicRadius h (Nat.clog 2 (N n) + L) :=
    (hs k hk).trans (dyadic_mesoscopicRadius_covers (N n) (D.size_pos n) alpha H.alpha_pos.le L)
  have hp := D.normalized_reciprocal_sum_le_dyadic_of_HY n ω H hn hω s E eta h hE heta hh le_rfl _ hcover
  have hfrac : h / eta ≤ (N n : ℝ) ^ alpha / cstar := by
    rw [div_le_div_iff₀ heta hcstar]
    have hm := mul_le_mul_of_nonneg_right hheight hh.le
    have hsize := size_mul_mesoscopicScale (N n) (D.size_pos n) alpha
    change (N n : ℝ) * h = (N n : ℝ) ^ alpha at hsize
    calc
      h * cstar ≤ ((N n : ℝ) * eta) * h := by simpa only [mul_comm] using hm
      _ = ((N n : ℝ) * h) * eta := by ring
      _ = _ := by rw [hsize]
  have hcentral := mul_le_mul_of_nonneg_left hfrac (show 0 ≤ 2 * C by positivity)
  have houter := mul_le_mul_of_nonneg_left hdepth (show 0 ≤ 4 * C by positivity)
  calc
    _ ≤ 2 * C * h / eta + 4 * C * (Nat.clog 2 (N n) + L) := by simpa only [Nat.cast_add] using hp
    _ ≤ 2 * C * ((N n : ℝ) ^ alpha / cstar) + 4 * C * (Q * (N n : ℝ) ^ alpha) := by
      convert add_le_add hcentral houter using 1 <;> dsimp [Q] <;> push_cast <;> ring
    _ = _ := by ring

end GeneralizedBulk.External.RegularSpectralData
