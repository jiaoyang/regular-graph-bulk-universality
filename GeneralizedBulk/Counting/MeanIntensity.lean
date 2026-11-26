import GeneralizedBulk.Analysis.NoLinearTerm

/-! Expected counting measures and deterministic atom-free cutoff boundaries. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped ENNReal Topology
namespace GeneralizedBulk.Counting

def meanIntensity (ν : Measure AnchoredCountingState) : Measure ℝ :=
  ν.bind (fun s => s.val.1.measure)

theorem measurable_countingMeasure : Measurable (fun s : AnchoredCountingState => s.val.1.measure) :=
  LocalCountingMeasure.measurable_measure.comp (measurable_fst.comp measurable_subtype_coe)

theorem meanIntensity_apply (ν : Measure AnchoredCountingState) {A : Set ℝ} (hA : MeasurableSet A) :
    meanIntensity ν A = ∫⁻ s, s.val.1.measure A ∂ν :=
  Measure.bind_apply hA measurable_countingMeasure.aemeasurable

/-- The first scalar anchor moment controls expected local counts. -/
theorem meanIntensity_Icc_le (ν : Measure AnchoredCountingState)
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (R : ℝ) : meanIntensity ν (Set.Icc (-R) R) ≤
      ENNReal.ofReal ((1 + R ^ 2) * (∫ s : AnchoredCountingState, ‖s.val.2‖ ∂ν)) := by
  rw [meanIntensity_apply ν measurableSet_Icc,← integral_const_mul]
  rw [ofReal_integral_eq_lintegral_ofReal (hm.const_mul _) (Eventually.of_forall (fun s => by positivity))]
  apply lintegral_mono
  intro s
  have hb := s.count_le_anchor (K := Set.Icc (-R) R) (R := R)
    (fun x hx => abs_le.mpr hx)
  change s.val.1.measure (Set.Icc (-R) R) ≤ ENNReal.ofReal _
  exact (ENNReal.le_ofReal_iff_toReal_le isCompact_Icc.measure_ne_top (by positivity)).mpr hb

instance meanIntensity_isFiniteOnCompacts (ν : Measure AnchoredCountingState)
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν) :
    IsFiniteMeasureOnCompacts (meanIntensity ν) := by
  constructor
  intro K hK
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  have hs : K ⊆ Set.Icc (-R) R := by
    intro x hx
    have hh := hR hx
    simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,abs_le] using hh
  exact ((measure_mono hs).trans (meanIntensity_Icc_le ν hm R)).trans_lt ENNReal.ofReal_lt_top

/-- Only countably many deterministic points have a positive probability of
being an atom of a random counting configuration. -/
theorem countable_mean_atoms (ν : Measure AnchoredCountingState)
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν) :
    Set.Countable {a : ℝ | meanIntensity ν {a} ≠ 0} := by
  letI : IsFiniteMeasureOnCompacts (meanIntensity ν) := meanIntensity_isFiniteOnCompacts ν hm
  simpa only [pos_iff_ne_zero] using
    (Measure.countable_meas_pos_of_disjoint_iUnion (μ := meanIntensity ν)
      (fun a : ℝ => measurableSet_singleton a) (fun a b hab => Set.disjoint_singleton.mpr hab))

theorem no_atom_ae_of_meanIntensity_zero (ν : Measure AnchoredCountingState) (a : ℝ)
    (ha : meanIntensity ν {a} = 0) : ∀ᵐ s ∂ν, s.val.1.measure {a} = 0 := by
  rw [meanIntensity_apply ν (measurableSet_singleton a)] at ha
  exact (lintegral_eq_zero_iff ((LocalCountingMeasure.measurable_mass
    (measurableSet_singleton a)).comp (measurable_fst.comp measurable_subtype_coe))).mp ha

/-- Deterministic expanding symmetric windows can be chosen with no boundary
atom on one common full-probability event. No simplicity assumption is used. -/
theorem exists_atom_free_radii (ν : Measure AnchoredCountingState)
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν) :
    ∃ R : ℕ → ℝ, StrictMono R ∧ Tendsto R atTop atTop ∧
      (∀ n : ℕ, (n : ℝ) < R n) ∧
      ∀ᵐ s ∂ν, ∀ n : ℕ, s.val.1.measure {R n} = 0 ∧ s.val.1.measure {-R n} = 0 := by
  classical
  let B := {a : ℝ | meanIntensity ν {a} ≠ 0}
  let bad := B ∪ (Neg.neg '' B)
  have hbad : Set.Countable bad := (countable_mean_atoms ν hm).union
    ((countable_mean_atoms ν hm).image Neg.neg)
  have hex (n : ℕ) : ∃ r ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1), r ∉ bad := by
    have hzero : volume bad = 0 := hbad.measure_zero volume
    have heq := measure_diff_null (s := Set.Ioo (n : ℝ) ((n : ℝ) + 1)) hzero
    have hpos : 0 < volume (Set.Ioo (n : ℝ) ((n : ℝ) + 1) \ bad) := by
      rw [heq,Real.volume_Ioo]
      norm_num
    obtain ⟨r,hr⟩ := nonempty_of_measure_ne_zero hpos.ne'
    exact ⟨r,hr.1,hr.2⟩
  choose R hR hn using hex
  have hmono : StrictMono R := strictMono_nat_of_lt_succ (fun n => by
    have h1 := (hR n).2
    have h2 := (hR (n + 1)).1
    norm_num only [Nat.cast_add,Nat.cast_one] at h2
    exact h1.trans h2)
  have htop : Tendsto R atTop atTop := tendsto_atTop_mono
    (fun n => (hR n).1.le) tendsto_natCast_atTop_atTop
  refine ⟨R,hmono,htop,fun n => (hR n).1,ae_all_iff.mpr ?_⟩
  intro n
  have hplus : meanIntensity ν {R n} = 0 := by
    by_cases h : meanIntensity ν {R n} = 0
    · exact h
    · exact False.elim (hn n (Or.inl h))
  have hminus : meanIntensity ν {-R n} = 0 := by
    by_cases h : meanIntensity ν {-R n} = 0
    · exact h
    · exact False.elim (hn n (Or.inr ⟨-R n,h,neg_neg _⟩))
  exact (no_atom_ae_of_meanIntensity_zero ν (R n) hplus).and
    (no_atom_ae_of_meanIntensity_zero ν (-R n) hminus)

end GeneralizedBulk.Counting
