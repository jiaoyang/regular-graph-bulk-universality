import BourgadeHuang.EntireCharacteristicRatio

/-! Reflection and the exact modulus identities of the genuine entire
characteristic ratio.  These identities also apply when its numerator and
its denominator lie in opposite half-planes. -/
noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace BourgadeHuang

/-- Conjugating both the argument and the value preserves complex
 differentiability. -/
theorem hasDerivAt_conj_comp_conj {f : ℂ → ℂ} {f' z : ℂ}
    (h : HasDerivAt f f' (starRingEnd ℂ z)) :
    HasDerivAt (fun w => starRingEnd ℂ (f (starRingEnd ℂ w)))
      (starRingEnd ℂ f') z := by
  have hc : Tendsto (starRingEnd ℂ) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using Complex.continuous_conj.continuousAt.tendsto.mono_left
        (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ) from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with w hw
      simpa using hw
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have ht := Complex.continuous_conj.continuousAt.tendsto.comp
    (h.tendsto_slope_zero.comp hc)
  change Tendsto (fun t => starRingEnd ℂ ((starRingEnd ℂ t)⁻¹ •
    (f (starRingEnd ℂ z + starRingEnd ℂ t) - f (starRingEnd ℂ z)))) _ _ at ht
  simpa only [smul_eq_mul, map_mul, map_inv₀, map_sub,
    map_add, Complex.conj_conj] using ht

@[simp] theorem ratioPath_conj (u v : ℂ) (t : ℝ) :
    ratioPath (starRingEnd ℂ u) (starRingEnd ℂ v) t =
      starRingEnd ℂ (ratioPath u v t) := by
  simp [ratioPath]

/-- Reflection of the path-integral ratio follows from reflection of the
reconstructed Nevanlinna function. -/
theorem anchoredCharacteristicRatio_conj (s : AnchoredCountingState) (u v : ℂ) :
    anchoredCharacteristicRatio s (starRingEnd ℂ u) (starRingEnd ℂ v) =
      starRingEnd ℂ (anchoredCharacteristicRatio s u v) := by
  unfold anchoredCharacteristicRatio
  simp_rw [ratioPath_conj, anchoredNevanlinna_conj]
  rw [← Complex.exp_conj, ← integral_conj]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp

/-- The true ratio satisfies Schwarz reflection even across the real line.
The proof extends the path identity by uniqueness of entire continuation. -/
theorem entireCharacteristicRatio_conj (s : AnchoredCountingState) (u : ℂ)
    {v : ℂ} (hv : v.im ≠ 0) :
    entireCharacteristicRatio s (starRingEnd ℂ u) (starRingEnd ℂ v) =
      starRingEnd ℂ (entireCharacteristicRatio s u v) := by
  let f := fun z => entireCharacteristicRatio s z v
  let g := fun z => starRingEnd ℂ
    (entireCharacteristicRatio s (starRingEnd ℂ z) (starRingEnd ℂ v))
  have hf : AnalyticOnNhd ℂ f Set.univ := fun z _ =>
    (differentiable_entireCharacteristicRatio_numerator s v).analyticAt z
  have hg : AnalyticOnNhd ℂ g Set.univ := by
    have hd : Differentiable ℂ g := by
      intro z
      exact (hasDerivAt_conj_comp_conj
        (differentiable_entireCharacteristicRatio_numerator s
          (starRingEnd ℂ v) (starRingEnd ℂ z)).hasDerivAt).differentiableAt
    exact fun z _ => hd.analyticAt z
  have he : f =ᶠ[𝓝 v] g := by
    filter_upwards [sameOpenHalfPlane_nhds (sameOpenHalfPlane_self_of_offReal hv)] with z hz
    have hc : SameOpenHalfPlane (starRingEnd ℂ z) (starRingEnd ℂ v) := by
      rcases hz with hz | hz
      · exact Or.inr ⟨by simpa using hz.1, by simpa using hz.2⟩
      · exact Or.inl ⟨by simpa using hz.1, by simpa using hz.2⟩
    dsimp [f, g]
    rw [entireCharacteristicRatio_eq_anchored s hz,
      entireCharacteristicRatio_eq_anchored s hc, anchoredCharacteristicRatio_conj]
    simp
  have hh := congrFun (hf.eq_of_eventuallyEq hg he) u
  simpa only [f, g, Complex.conj_conj] using congrArg (starRingEnd ℂ) hh.symm

/-- Squaring the modulus of a cross-half-plane ratio pairs its numerators
with reflected denominators, which lie in the same half-plane. -/
theorem entireCharacteristicRatio_norm_sq (s : AnchoredCountingState) (u : ℂ)
    {v : ℂ} (hv : v.im ≠ 0) :
    ((‖entireCharacteristicRatio s u v‖ ^ 2 : ℝ) : ℂ) =
      entireCharacteristicRatio s u (starRingEnd ℂ v) *
        entireCharacteristicRatio s (starRingEnd ℂ u) v := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', ← entireCharacteristicRatio_conj s u hv]
  unfold entireCharacteristicRatio
  ring

/-- The normalization at `i` has unit modulus at `−i` as well. -/
@[simp] theorem norm_anchoredEntireNumerator_neg_I (s : AnchoredCountingState) :
    ‖anchoredEntireNumerator s (-Complex.I)‖ = 1 := by
  have h := entireCharacteristicRatio_norm_sq s (-Complex.I)
    (show Complex.I.im ≠ 0 by simp)
  have hm : ((‖anchoredEntireNumerator s (-Complex.I)‖ ^ 2 : ℝ) : ℂ) = 1 := by
    have hn := anchoredEntireNumerator_ne_zero s (show (-Complex.I).im ≠ 0 by simp)
    simpa only [entireCharacteristicRatio, map_neg, Complex.conj_I, neg_neg,
      anchoredEntireNumerator_I, div_one, div_self hn, div_self one_ne_zero, mul_one] using h
  have hr := congrArg Complex.re hm
  simp only [Complex.ofReal_re, Complex.one_re] at hr
  nlinarith [norm_nonneg (anchoredEntireNumerator s (-Complex.I))]

/-- Reflection of the canonical numerator changes only its constant phase. -/
@[simp] theorem norm_anchoredEntireNumerator_conj (s : AnchoredCountingState) (z : ℂ) :
    ‖anchoredEntireNumerator s (starRingEnd ℂ z)‖ =
      ‖anchoredEntireNumerator s z‖ := by
  have h := congrArg norm (entireCharacteristicRatio_conj s z
    (show Complex.I.im ≠ 0 by simp))
  simpa [entireCharacteristicRatio, norm_div] using h

/-- Reflecting either argument preserves the modulus of the entire ratio. -/
@[simp] theorem norm_entireCharacteristicRatio_conj_numerator
    (s : AnchoredCountingState) (u v : ℂ) :
    ‖entireCharacteristicRatio s (starRingEnd ℂ u) v‖ =
      ‖entireCharacteristicRatio s u v‖ := by
  simp only [entireCharacteristicRatio, norm_div, norm_anchoredEntireNumerator_conj]

@[simp] theorem norm_entireCharacteristicRatio_conj_denominator
    (s : AnchoredCountingState) (u v : ℂ) :
    ‖entireCharacteristicRatio s u (starRingEnd ℂ v)‖ =
      ‖entireCharacteristicRatio s u v‖ := by
  simp only [entireCharacteristicRatio, norm_div, norm_anchoredEntireNumerator_conj]

end BourgadeHuang
