import BourgadeHuang.NevanlinnaReconstruction

/-!
# Closed anchored counting states

The cutoff inequalities are closed for the vague topology and encode exactly
that the weighted counting mass is finite and at most the imaginary anchor.
Any excess imaginary anchor records a possible linear Nevanlinna term at infinity.
-/
noncomputable section
open scoped BigOperators Topology CompactlySupported
open MeasureTheory Filter
namespace BourgadeHuang

/-- Compact tests that increase to the Nevanlinna weight. -/
def nevanlinnaWeightCutoff (n : ℕ) : ℝ →C_c ℝ :=
  ⟨⟨fun a => compactIntervalCutoff n a * nevanlinnaWeight a,
    (compactIntervalCutoff n).continuous.mul continuous_nevanlinnaWeight⟩,
    (compactIntervalCutoff n).hasCompactSupport.mul_right⟩

theorem nevanlinnaWeightCutoff_nonneg (n : ℕ) (a : ℝ) :
    0 ≤ nevanlinnaWeightCutoff n a :=
  mul_nonneg (intervalCutoff_mem_Icc n a).1 (nevanlinnaWeight_nonneg a)

theorem nevanlinnaWeightCutoff_le (n : ℕ) (a : ℝ) :
    nevanlinnaWeightCutoff n a ≤ nevanlinnaWeight a :=
  mul_le_of_le_one_left (nevanlinnaWeight_nonneg a) (intervalCutoff_mem_Icc n a).2

theorem nevanlinnaWeightCutoff_monotone (a : ℝ) :
    Monotone (fun n : ℕ => nevanlinnaWeightCutoff n a) := by
  intro n m hnm
  apply mul_le_mul_of_nonneg_right _ (nevanlinnaWeight_nonneg a)
  apply max_le_max le_rfl
  apply min_le_min le_rfl
  exact sub_le_sub_right (add_le_add_right (by exact_mod_cast hnm) 1) _

theorem nevanlinnaWeightCutoff_eventually_eq (a : ℝ) :
    ∀ᶠ n in atTop, nevanlinnaWeightCutoff n a = nevanlinnaWeight a := by
  obtain ⟨N, hN⟩ := exists_nat_ge |a|
  filter_upwards [eventually_ge_atTop N] with n hn
  have ha : a ∈ Set.Icc (-(n : ℝ)) (n : ℝ) :=
    abs_le.mp (hN.trans (by exact_mod_cast hn))
  change intervalCutoff n a * nevanlinnaWeight a = _
  rw [intervalCutoff_eq_one ha, one_mul]

/-- Closed state constraint, expressed entirely by compact continuous tests. -/
def ValidAnchoredCountingState (p : LocalCountingMeasure × ℂ) : Prop :=
  ∀ n : ℕ, (∫ a, nevanlinnaWeightCutoff n a ∂p.1.measure) ≤ p.2.im

theorem isClosed_validAnchoredCountingState :
    IsClosed {p : LocalCountingMeasure × ℂ | ValidAnchoredCountingState p} := by
  unfold ValidAnchoredCountingState
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro n
  exact isClosed_le ((continuous_linearStatistic (nevanlinnaWeightCutoff n)).comp continuous_fst)
    (Complex.continuous_im.comp continuous_snd)

/-- The valid states retain the natural subspace topology. -/
abbrev AnchoredCountingState := {p : LocalCountingMeasure × ℂ // ValidAnchoredCountingState p}

theorem AnchoredCountingState.im_nonneg (s : AnchoredCountingState) : 0 ≤ s.val.2.im :=
  (integral_nonneg (nevanlinnaWeightCutoff_nonneg 0)).trans (s.property 0)

/-- The closed cutoff conditions imply genuine integrability, not merely a
bound on a totalized integral. -/
theorem AnchoredCountingState.integrable_weight (s : AnchoredCountingState) :
    Integrable nevanlinnaWeight s.val.1.measure := by
  have hlim : Tendsto
      (fun n => ∫⁻ a, ENNReal.ofReal (nevanlinnaWeightCutoff n a) ∂s.val.1.measure) atTop
      (𝓝 (∫⁻ a, ENNReal.ofReal (nevanlinnaWeight a) ∂s.val.1.measure)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (nevanlinnaWeightCutoff n).continuous.measurable.ennreal_ofReal.aemeasurable)
    · exact Filter.Eventually.of_forall fun a =>
        fun n m hnm => ENNReal.ofReal_le_ofReal (nevanlinnaWeightCutoff_monotone a hnm)
    · apply Filter.Eventually.of_forall
      intro a
      apply tendsto_const_nhds.congr'
      filter_upwards [nevanlinnaWeightCutoff_eventually_eq a] with n hn
      exact congrArg ENNReal.ofReal hn.symm
  have hbound : (∫⁻ a, ENNReal.ofReal (nevanlinnaWeight a) ∂s.val.1.measure) ≤
      ENNReal.ofReal s.val.2.im := by
    apply le_of_tendsto hlim
    exact Filter.Eventually.of_forall fun n => by
      calc
        _ = ENNReal.ofReal (∫ a, nevanlinnaWeightCutoff n a ∂s.val.1.measure) :=
          (ofReal_integral_eq_lintegral_ofReal
            (show Integrable (fun a => nevanlinnaWeightCutoff n a) s.val.1.measure from
              (nevanlinnaWeightCutoff n).continuous.integrable_of_hasCompactSupport
                (nevanlinnaWeightCutoff n).hasCompactSupport)
            (Filter.Eventually.of_forall (nevanlinnaWeightCutoff_nonneg n))).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (s.property n)
  refine ⟨continuous_nevanlinnaWeight.measurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall nevanlinnaWeight_nonneg)]
  exact hbound.trans_lt ENNReal.ofReal_lt_top

theorem AnchoredCountingState.integral_weight_le_im (s : AnchoredCountingState) :
    (∫ a, nevanlinnaWeight a ∂s.val.1.measure) ≤ s.val.2.im := by
  have hlim : Tendsto
      (fun n => ∫ a, nevanlinnaWeightCutoff n a ∂s.val.1.measure) atTop
      (𝓝 (∫ a, nevanlinnaWeight a ∂s.val.1.measure)) := by
    apply integral_tendsto_of_tendsto_of_monotone
      (fun n => (nevanlinnaWeightCutoff n).continuous.integrable_of_hasCompactSupport
        (nevanlinnaWeightCutoff n).hasCompactSupport) s.integrable_weight
    · exact Filter.Eventually.of_forall nevanlinnaWeightCutoff_monotone
    · exact Filter.Eventually.of_forall fun a =>
        tendsto_const_nhds.congr' ((nevanlinnaWeightCutoff_eventually_eq a).mono (fun _ hn => hn.symm))
  exact le_of_tendsto hlim (Filter.Eventually.of_forall s.property)

/-- The actual analytic function reconstructed from the counting state. -/
def anchoredNevanlinna (s : AnchoredCountingState) (z : ℂ) : ℂ :=
  (s.val.2.re : ℂ) + z * (s.val.2.im : ℂ) +
    (1 + z ^ 2) * ∫ a, anchoredResolventKernel z a ∂s.val.1.measure

/-- Finite-particle configurations satisfy the state condition exactly. -/
theorem validAnchoredCountingState_finite {N : ℕ} (x : Fin N → ℝ) (center : ℝ)
    (ξ : LocalCountingMeasure) (hξ : ξ.measure = ∑ i, Measure.dirac (x i)) :
    ValidAnchoredCountingState (ξ, microscopicResolvent x center Complex.I) := by
  intro n
  rw [hξ, integral_finset_sum_measure (fun _ _ => integrable_dirac)]
  simp only [integral_dirac]
  rw [microscopicResolvent_im_I_eq_weight]
  exact Finset.sum_le_sum (fun i _ => nevanlinnaWeightCutoff_le n (x i))

/-- Reconstruction recovers the finite resolvent itself at every off-real point. -/
theorem anchoredNevanlinna_eq_finite {N : ℕ} (x : Fin N → ℝ) (center : ℝ)
    (ξ : LocalCountingMeasure) (hξ : ξ.measure = ∑ i, Measure.dirac (x i))
    {z : ℂ} (hz : z.im ≠ 0) :
    anchoredNevanlinna
      ⟨(ξ, microscopicResolvent x center Complex.I), validAnchoredCountingState_finite x center ξ hξ⟩ z =
      microscopicResolvent x center z := by
  rw [anchoredNevanlinna, hξ, integral_finset_sum_measure (fun _ _ => integrable_dirac)]
  simp only [integral_dirac]
  exact (microscopicResolvent_anchor_reconstruction x center hz).symm

end BourgadeHuang
