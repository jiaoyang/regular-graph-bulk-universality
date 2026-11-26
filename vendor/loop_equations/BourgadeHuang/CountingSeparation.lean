import BourgadeHuang.CountingTightness
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Countable separation of the vague counting-measure space

A dense sequence of continuous functions, multiplied by countably many compact
cutoffs, separates locally finite counting measures. Atomicity makes each cutoff
integral a finite sum of evaluations, which is continuous for the compact-open
topology on continuous functions.
-/
noncomputable section
open scoped BigOperators Topology CompactlySupported ENNReal
open MeasureTheory Filter

namespace BourgadeHuang

/-- Multiplication by a fixed compact cutoff. -/
def cutoffTest (R : ℝ) (f : C(ℝ, ℝ)) : ℝ →C_c ℝ :=
  ⟨intervalCutoff R * f, (intervalCutoff_hasCompactSupport R).mul_right⟩

@[simp] theorem cutoffTest_apply (R : ℝ) (f : C(ℝ, ℝ)) (x : ℝ) :
    cutoffTest R f x = intervalCutoff R x * f x := rfl

/-- For a fixed counting measure, cutoff integration is a finite sum of continuous
evaluations of the test function. -/
theorem continuous_cutoff_integral (ξ : LocalCountingMeasure) (R : ℝ) :
    Continuous (fun f : C(ℝ, ℝ) => ∫ x, cutoffTest R f x ∂ξ.measure) := by
  obtain ⟨N, x, _, hμ, _⟩ := ξ.exists_compact_particle_list_with_multiplicity
    (K := Set.Icc (-(R + 1)) (R + 1)) isCompact_Icc
  have heq : (fun f : C(ℝ, ℝ) => ∫ x, cutoffTest R f x ∂ξ.measure) =
      fun f => ∑ i, intervalCutoff R (x i) * f (x i) := by
    funext f
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Icc (-(R + 1)) (R + 1)) (fun y hy => by
        simp only [cutoffTest_apply, intervalCutoff_eq_zero hy, zero_mul]), hμ]
    rw [integral_finset_sum_measure (fun _ _ => integrable_dirac)]
    simp
  rw [heq]
  exact continuous_finset_sum _ (fun i _ =>
    continuous_const.mul (continuous_eval_const (x i)))

/-- A fixed countable family of compact continuous tests. -/
def separatingCompactTest (j : ℕ × ℕ) : ℝ →C_c ℝ :=
  cutoffTest j.1 (match j.2 with
    | 0 => 1
    | m + 1 => TopologicalSpace.denseSeq C(ℝ, ℝ) m)

/-- Agreement on this one countable family implies agreement of configurations. -/
theorem LocalCountingMeasure.ext_countable_integrals {ξ ζ : LocalCountingMeasure}
    (h : ∀ j : ℕ × ℕ, (∫ x, separatingCompactTest j x ∂ξ.measure) =
      ∫ x, separatingCompactTest j x ∂ζ.measure) : ξ = ζ := by
  have hn (n : ℕ) : (fun f : C(ℝ, ℝ) => ∫ x, cutoffTest n f x ∂ξ.measure) =
      fun f : C(ℝ, ℝ) => ∫ x, cutoffTest n f x ∂ζ.measure := by
    apply (TopologicalSpace.denseRange_denseSeq C(ℝ, ℝ)).equalizer
      (continuous_cutoff_integral ξ n) (continuous_cutoff_integral ζ n)
    funext m
    exact h (n, m + 1)
  apply LocalCountingMeasure.ext_integral
  intro f
  obtain ⟨R, _, hR⟩ := f.hasCompactSupport.isBounded.exists_pos_norm_le
  obtain ⟨n, hnR⟩ := exists_nat_gt R
  have hf : cutoffTest n f.toContinuousMap = f := by
    ext x
    by_cases hx : x ∈ tsupport f
    · have hxn : x ∈ Set.Icc (-(n : ℝ)) n := by
        have h := hR x hx
        rw [Real.norm_eq_abs] at h
        exact abs_le.mp (h.trans hnR.le)
      change intervalCutoff n x * f x = f x
      rw [intervalCutoff_eq_one hxn, one_mul]
    · have hz : f x = 0 := by
        by_contra hz
        exact hx (subset_closure hz)
      change intervalCutoff n x * f x = f x
      rw [hz, mul_zero]
  simpa only [hf] using congrFun (hn n) f.toContinuousMap

/-- The countable vector of genuine compact linear statistics. -/
def countingCoordinates (ξ : LocalCountingMeasure) (j : ℕ × ℕ) : ℝ :=
  ∫ x, separatingCompactTest j x ∂ξ.measure

theorem continuous_countingCoordinates : Continuous countingCoordinates :=
  continuous_pi (fun j => continuous_linearStatistic (separatingCompactTest j))

theorem injective_countingCoordinates : Function.Injective countingCoordinates :=
  fun _ _ h => LocalCountingMeasure.ext_countable_integrals (congrFun h)

/-- A designated coordinate bounds the count in each annulus. -/
theorem annular_count_le_countingCoordinate (ξ : LocalCountingMeasure) (n : ℕ) :
    ξ.measure (realAnnulus n) ≤ ENNReal.ofReal (countingCoordinates ξ (n + 1, 0)) := by
  have hi := (compactIntervalCutoff ((n : ℝ) + 1)).continuous.integrable_of_hasCompactSupport
    (μ := ξ.measure) (compactIntervalCutoff ((n : ℝ) + 1)).hasCompactSupport
  have hb := hi.measure_le_integral
    (Filter.Eventually.of_forall (fun x => (intervalCutoff_mem_Icc ((n : ℝ) + 1) x).1))
    (s := realAnnulus n) (fun x hx => by
      have hx' := abs_le.mp (abs_le_of_mem_realAnnulus hx)
      exact le_of_eq (intervalCutoff_eq_one hx').symm)
  simpa [countingCoordinates, separatingCompactTest, cutoffTest, Nat.cast_add,
    Nat.cast_one, compactIntervalCutoff] using hb

/-- Convergence of the countable coordinates supplies uniform local count bounds. -/
theorem exists_annular_count_bound_of_coordinates_tendsto
    (ξ : ℕ → LocalCountingMeasure) {y : (ℕ × ℕ) → ℝ}
    (h : Tendsto (fun N => countingCoordinates (ξ N)) atTop (𝓝 y)) :
    ∃ B : ℕ → ℕ, ∀ N n, (ξ N).measure (realAnnulus n) ≤ B n := by
  have hb : ∀ n, ∃ B : ℕ, ∀ N, (ξ N).measure (realAnnulus n) ≤ B := by
    intro n
    have hn := ((continuous_apply (n + 1, 0)).tendsto y).comp h
    obtain ⟨C, _, hC⟩ := hn.cauchySeq.isBounded_range.exists_pos_norm_le
    obtain ⟨B, hB⟩ := exists_nat_gt C
    refine ⟨B, fun N => ?_⟩
    have hCN : |countingCoordinates (ξ N) (n + 1, 0)| ≤ C := by
      simpa only [Real.norm_eq_abs, Function.comp_apply] using hC _ (Set.mem_range_self N)
    calc
      (ξ N).measure (realAnnulus n) ≤ ENNReal.ofReal (countingCoordinates (ξ N) (n + 1, 0)) :=
        annular_count_le_countingCoordinate _ n
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal
        ((le_abs_self _).trans (hCN.trans hB.le))
      _ = B := by simp
  choose B hB using hb
  exact ⟨B, fun N n => hB n N⟩

/-- Closed sets remain closed under the countable coordinate map. A convergent
coordinate sequence has bounded local counts and therefore a vague subsequence. -/
theorem isClosedMap_countingCoordinates : IsClosedMap countingCoordinates := by
  intro A hA
  apply IsSeqClosed.isClosed
  intro y z hy hz
  choose ξ hξ hcoord using hy
  have hconv : Tendsto (fun N => countingCoordinates (ξ N)) atTop (𝓝 z) := by
    simpa only [hcoord] using hz
  obtain ⟨B, hB⟩ := exists_annular_count_bound_of_coordinates_tendsto ξ hconv
  obtain ⟨ζ, r, hr, hζ⟩ := exists_vaguely_convergent_subsequence_of_count_bound ξ B hB
  have hζA : ζ ∈ A := hA.mem_of_tendsto hζ (Filter.Eventually.of_forall (fun n => hξ (r n)))
  have hlim := (continuous_countingCoordinates.tendsto ζ).comp hζ
  have hz' := hconv.comp hr.tendsto_atTop
  exact ⟨ζ, hζA, tendsto_nhds_unique hlim hz'⟩

/-- The actual vague topology is a closed subspace of a countable product of reals. -/
theorem isClosedEmbedding_countingCoordinates : Topology.IsClosedEmbedding countingCoordinates :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    continuous_countingCoordinates injective_countingCoordinates isClosedMap_countingCoordinates

instance : SecondCountableTopology LocalCountingMeasure :=
  isClosedEmbedding_countingCoordinates.isEmbedding.secondCountableTopology

instance : PolishSpace LocalCountingMeasure :=
  isClosedEmbedding_countingCoordinates.polishSpace

/-- A compact real interval used for a bounded version of every coordinate. -/
abbrev CountingCoordinateInterval := Set.Icc (-(Real.pi / 2)) (Real.pi / 2)

instance : CompactSpace CountingCoordinateInterval :=
  isCompact_iff_compactSpace.mp isCompact_Icc

/-- A countable compact metric cube containing all counting configurations. -/
abbrev CountingCompactCube := (ℕ × ℕ) → CountingCoordinateInterval

/-- A bounded topological embedding of the real line into a compact interval. -/
def compactifiedRealCoordinate (x : ℝ) : CountingCoordinateInterval :=
  ⟨Real.arctan x, (Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩

theorem isEmbedding_compactifiedRealCoordinate :
    Topology.IsEmbedding compactifiedRealCoordinate := by
  apply Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
  exact Real.arctan_strictMono.isEmbedding_of_ordConnected
    (by rw [Real.range_arctan]; exact Set.ordConnected_Ioo)

/-- Compactification by the arctangents of compact linear statistics. -/
def countingCompactification (ξ : LocalCountingMeasure) : CountingCompactCube :=
  fun j => compactifiedRealCoordinate (countingCoordinates ξ j)

theorem continuous_countingCompactification : Continuous countingCompactification := by
  apply continuous_pi
  intro j
  exact (Real.continuous_arctan.comp
    ((continuous_apply j).comp continuous_countingCoordinates)).subtype_mk _

theorem injective_countingCompactification : Function.Injective countingCompactification := by
  intro ξ ζ h
  apply injective_countingCoordinates
  funext j
  apply Real.arctan_injective
  exact congrArg (fun z : CountingCoordinateInterval => (z : ℝ)) (congrFun h j)

/-- The compactification preserves the actual vague topology on its image. -/
theorem isEmbedding_countingCompactification : Topology.IsEmbedding countingCompactification := by
  refine ⟨⟨?_⟩, injective_countingCompactification⟩
  rw [isClosedEmbedding_countingCoordinates.isInducing.eq_induced,
    induced_to_pi, induced_to_pi]
  congr 1
  funext j
  exact (congrArg (TopologicalSpace.induced (fun ξ : LocalCountingMeasure => countingCoordinates ξ j))
    isEmbedding_compactifiedRealCoordinate.isInducing.eq_induced).trans (by
      rw [induced_compose]
      rfl)

/-- The compactification is a measurable embedding by the proved Polish structure
and the Lusin–Souslin theorem. -/
theorem measurableEmbedding_countingCompactification : MeasurableEmbedding countingCompactification :=
  continuous_countingCompactification.measurableEmbedding injective_countingCompactification

/-- A compatible metric on the countable compact cube. -/
instance : MetricSpace CountingCompactCube :=
  TopologicalSpace.metrizableSpaceMetric CountingCompactCube

end BourgadeHuang
