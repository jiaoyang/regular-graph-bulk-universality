import BourgadeHuang.NevanlinnaPositivity
import BourgadeHuang.NevanlinnaContinuity
import BourgadeHuang.CountingEvaluation
import Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# Recovering a counting law from its reconstructed resolvents

A shrinking Poisson kernel recovers each atomic mass. Since locally finite
counting measures have no diffuse part, their reconstructed analytic functions
determine the entire measure and the anchor. Countably many off-real samples
then give a measurable injection, allowing equality of resolvent laws to imply
equality of genuine counting laws.
-/
noncomputable section
open scoped Topology ENNReal ComplexConjugate
open MeasureTheory Filter
namespace BourgadeHuang

/-- Shrinking imaginary heights used for atomic mass recovery. -/
def atomRecoveryHeight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem atomRecoveryHeight_pos (n : ℕ) : 0 < atomRecoveryHeight n := by
  dsimp [atomRecoveryHeight]
  positivity

theorem atomRecoveryHeight_le_one (n : ℕ) : atomRecoveryHeight n ≤ 1 := by
  dsimp [atomRecoveryHeight]
  exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])

theorem tendsto_atomRecoveryHeight : Tendsto atomRecoveryHeight atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The normalized Poisson kernel converges to the indicator of its center. -/
def atomRecoveryKernel (x y a : ℝ) : ℝ := y ^ 2 / ((a - x) ^ 2 + y ^ 2)

theorem atomRecoveryKernel_le_weight (x a : ℝ) {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    atomRecoveryKernel x y a ≤ (3 + 2 * x ^ 2) * nevanlinnaWeight a := by
  have hy2 : y ^ 2 ≤ 1 := by nlinarith
  have ha2 : a ^ 2 ≤ 2 * (a - x) ^ 2 + 2 * x ^ 2 := by nlinarith [sq_nonneg (a - 2 * x)]
  have hc : y ^ 2 * (a - x) ^ 2 ≤ (a - x) ^ 2 :=
    mul_le_of_le_one_left (sq_nonneg _) hy2
  dsimp [atomRecoveryKernel, nevanlinnaWeight]
  rw [← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity : 0 < (a - x) ^ 2 + y ^ 2) (by positivity : 0 < 1 + a ^ 2)).mpr
  nlinarith [mul_le_mul_of_nonneg_left ha2 (sq_nonneg y),
    mul_nonneg (sq_nonneg x) (sq_nonneg (a - x))]

theorem tendsto_atomRecoveryKernel (x a : ℝ) :
    Tendsto (fun n => atomRecoveryKernel x (atomRecoveryHeight n) a) atTop
      (𝓝 (({x} : Set ℝ).indicator (fun _ => (1 : ℝ)) a)) := by
  by_cases hax : a = x
  · subst a
    have he (n : ℕ) : atomRecoveryKernel x (atomRecoveryHeight n) x = 1 := by
      simp [atomRecoveryKernel, (atomRecoveryHeight_pos n).ne']
    simpa only [he, Set.indicator_of_mem (Set.mem_singleton x)] using
      (tendsto_const_nhds (x := (1 : ℝ)))
  · have hd : (a - x) ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by
      simpa only [zero_pow (by decide : 2 ≠ 0), add_zero, ne_eq, sq_eq_zero_iff] using sub_ne_zero.mpr hax
    have hh := (tendsto_atomRecoveryHeight.pow 2).div
      (tendsto_const_nhds.add (tendsto_atomRecoveryHeight.pow 2)) hd
    simpa only [atomRecoveryKernel, zero_pow (by decide : 2 ≠ 0), zero_div,
      Set.indicator_of_not_mem (show a ∉ ({x} : Set ℝ) by simpa using hax)] using hh

/-- Weighted dominated convergence extracts the mass at one point. -/
theorem tendsto_integral_atomRecoveryKernel (s : AnchoredCountingState) (x : ℝ) :
    Tendsto (fun n => ∫ a, atomRecoveryKernel x (atomRecoveryHeight n) a ∂s.val.1.measure)
      atTop (𝓝 (s.val.1.measure {x}).toReal) := by
  have hh := tendsto_integral_of_dominated_convergence
    (μ := s.val.1.measure) (F := fun n a => atomRecoveryKernel x (atomRecoveryHeight n) a)
    (f := ({x} : Set ℝ).indicator (fun _ => (1 : ℝ)))
    (fun a => (3 + 2 * x ^ 2) * nevanlinnaWeight a)
    (fun n => (measurable_const.div (((measurable_id.sub measurable_const).pow_const 2).add measurable_const)).aestronglyMeasurable)
    (s.integrable_weight.const_mul _) (fun n => ?_) (Filter.Eventually.of_forall (tendsto_atomRecoveryKernel x))
  · simpa only [integral_indicator_const (1 : ℝ) (measurableSet_singleton x), smul_eq_mul, mul_one,
      measureReal_def] using hh
  · apply Filter.Eventually.of_forall
    intro a
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [atomRecoveryKernel]; positivity)]
    exact atomRecoveryKernel_le_weight x a (atomRecoveryHeight_pos n) (atomRecoveryHeight_le_one n)

/-- Imaginary resolvent values recover every singleton mass. -/
theorem tendsto_anchoredNevanlinna_atom_mass (s : AnchoredCountingState) (x : ℝ) :
    Tendsto (fun n => atomRecoveryHeight n *
      (anchoredNevanlinna s ((x : ℂ) + (atomRecoveryHeight n : ℂ) * Complex.I)).im)
      atTop (𝓝 (s.val.1.measure {x}).toReal) := by
  have he (y : ℝ) (hy : 0 < y) :
      y * (anchoredNevanlinna s ((x : ℂ) + (y : ℂ) * Complex.I)).im =
        y ^ 2 * anchoredLinearCoefficient s + ∫ a, atomRecoveryKernel x y a ∂s.val.1.measure := by
    have hz : ((x : ℂ) + (y : ℂ) * Complex.I).im ≠ 0 := by simpa using hy.ne'
    rw [anchoredNevanlinna_im_eq s hz]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.ofReal_re,
      mul_one, Complex.I_re, zero_mul, add_zero, zero_add]
    rw [mul_add, ← integral_const_mul]
    congr 1
    · ring
    · apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro a
      simp [atomRecoveryKernel, Complex.normSq_apply, pow_two, div_eq_mul_inv]
      ring
  have hh := ((tendsto_atomRecoveryHeight.pow 2).mul_const (anchoredLinearCoefficient s)).add
    (tendsto_integral_atomRecoveryKernel s x)
  simpa only [he _ (atomRecoveryHeight_pos _), zero_pow (by decide : 2 ≠ 0), zero_mul,
    zero_add] using hh

/-- Integer-valued locally finite measures are determined by their singleton masses. -/
theorem LocalCountingMeasure.ext_singletons {ξ ζ : LocalCountingMeasure}
    (h : ∀ a : ℝ, ξ.measure {a} = ζ.measure {a}) : ξ = ζ := by
  have hatoms : ξ.atoms = ζ.atoms := by ext a; simp only [LocalCountingMeasure.atoms, Set.mem_setOf_eq, h a]
  have hK {K : Set ℝ} (hK : IsCompact K) : ξ.measure K = ζ.measure K := by
    have hfin : (ξ.finite_atoms_inter_compact hK).toFinset = (ζ.finite_atoms_inter_compact hK).toFinset := by
      ext a
      simp only [Set.Finite.mem_toFinset, hatoms]
    have hr : ξ.measure.restrict K = ζ.measure.restrict K := by
      rw [ξ.restrict_compact_eq_sum_dirac hK, ζ.restrict_compact_eq_sum_dirac hK, hfin]
      apply Finset.sum_congr rfl
      intro a _
      rw [h a]
    simpa only [Measure.restrict_apply_univ] using congrArg (fun μ : Measure ℝ => μ Set.univ) hr
  have hm : ξ.measure = ζ.measure := by
    apply Measure.ext
    intro A hA
    rw [hA.measure_eq_iSup_isCompact ξ.measure, hA.measure_eq_iSup_isCompact ζ.measure]
    congr 1
    funext K
    congr 1
    funext hKA
    congr 1
    funext hcomp
    exact hK hcomp
  cases ξ
  cases ζ
  simpa only [LocalCountingMeasure.mk.injEq] using hm

/-- All off-real reconstructed values determine both the underlying counting
measure and the complex anchor, hence the entire state. -/
theorem AnchoredCountingState.ext_nevanlinna {s t : AnchoredCountingState}
    (h : ∀ z : ℂ, z.im ≠ 0 → anchoredNevanlinna s z = anchoredNevanlinna t z) : s = t := by
  have hcount : s.val.1 = t.val.1 := by
    apply LocalCountingMeasure.ext_singletons
    intro x
    have hs := tendsto_anchoredNevanlinna_atom_mass s x
    have ht := tendsto_anchoredNevanlinna_atom_mass t x
    have he (n : ℕ) : atomRecoveryHeight n *
        (anchoredNevanlinna s ((x : ℂ) + (atomRecoveryHeight n : ℂ) * Complex.I)).im =
        atomRecoveryHeight n *
        (anchoredNevanlinna t ((x : ℂ) + (atomRecoveryHeight n : ℂ) * Complex.I)).im := by
      rw [h _ (by simpa using (atomRecoveryHeight_pos n).ne')]
    simp_rw [he] at hs
    exact (ENNReal.toReal_eq_toReal
      (isCompact_singleton.measure_lt_top (μ := s.val.1.measure)).ne
      (isCompact_singleton.measure_lt_top (μ := t.val.1.measure)).ne).mp (tendsto_nhds_unique hs ht)
  have hanchor : s.val.2 = t.val.2 := by simpa only [anchoredNevanlinna_I] using h Complex.I (by simp)
  apply Subtype.ext
  exact Prod.ext hcount hanchor

/-- Off-real parameters form a separable space, so a fixed sequence can sample
all reconstructed analytic functions. -/
abbrev OffRealPoint := {z : ℂ // z.im ≠ 0}

instance : SecondCountableTopology OffRealPoint :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

instance : Nonempty OffRealPoint := ⟨⟨Complex.I, by simp⟩⟩

def nevanlinnaSample (n : ℕ) : OffRealPoint := TopologicalSpace.denseSeq OffRealPoint n

def nevanlinnaCoordinates (s : AnchoredCountingState) : ℕ → ℂ :=
  fun n => anchoredNevanlinna s (nevanlinnaSample n).val

theorem continuous_nevanlinnaCoordinates : Continuous nevanlinnaCoordinates := by
  apply continuous_pi
  intro n
  exact continuous_anchoredNevanlinna (nevanlinnaSample n).property

theorem continuous_anchoredNevanlinna_offReal (s : AnchoredCountingState) :
    Continuous (fun z : OffRealPoint => anchoredNevanlinna s z.val) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (differentiableAt_anchoredNevanlinna s z.property).continuousAt.comp
    continuous_subtype_val.continuousAt

/-- Countably many off-real samples determine the full anchored state. -/
theorem injective_nevanlinnaCoordinates : Function.Injective nevanlinnaCoordinates := by
  intro s t hst
  have he : (fun z : OffRealPoint => anchoredNevanlinna s z.val) =
      (fun z : OffRealPoint => anchoredNevanlinna t z.val) := by
    apply (TopologicalSpace.denseRange_denseSeq OffRealPoint).equalizer
      (continuous_anchoredNevanlinna_offReal s) (continuous_anchoredNevanlinna_offReal t)
    funext n
    exact congrFun hst n
  apply AnchoredCountingState.ext_nevanlinna
  intro z hz
  exact congrFun he ⟨z, hz⟩

instance : PolishSpace AnchoredCountingState := isClosed_validAnchoredCountingState.polishSpace

/-- Lusin–Souslin upgrades the actual countable evaluation injection to a
measurable embedding, with no identification hypothesis. -/
theorem measurableEmbedding_nevanlinnaCoordinates : MeasurableEmbedding nevanlinnaCoordinates :=
  continuous_nevanlinnaCoordinates.measurable.measurableEmbedding injective_nevanlinnaCoordinates

/-- Equality of the countable resolvent-coordinate laws determines the full
anchored laws. Pullback along the proved measurable injection is exact. -/
theorem anchored_law_eq_of_nevanlinnaCoordinates {μ ν : Measure AnchoredCountingState}
    (h : Measure.map nevanlinnaCoordinates μ = Measure.map nevanlinnaCoordinates ν) : μ = ν := by
  have hh := congrArg (Measure.comap nevanlinnaCoordinates) h
  simpa only [measurableEmbedding_nevanlinnaCoordinates.comap_map] using hh

/-- In particular the laws of the underlying point configurations agree. -/
theorem counting_law_eq_of_nevanlinnaCoordinates (μ ν : ProbabilityMeasure AnchoredCountingState)
    (h : Measure.map nevanlinnaCoordinates (μ : Measure AnchoredCountingState) =
      Measure.map nevanlinnaCoordinates (ν : Measure AnchoredCountingState)) :
    anchoredCountingLaw μ = anchoredCountingLaw ν := by
  have he : μ = ν := Subtype.ext (anchored_law_eq_of_nevanlinnaCoordinates h)
  rw [he]

/-- Finite-dimensional resolvent distributions on the fixed countable sample
already determine the full probability law of anchored states. -/
theorem anchored_law_eq_of_finite_sample_laws
    (μ ν : ProbabilityMeasure AnchoredCountingState)
    (h : ∀ I : Finset ℕ,
      Measure.map (fun s : AnchoredCountingState => fun i : I => nevanlinnaCoordinates s i.val)
        (μ : Measure AnchoredCountingState) =
      Measure.map (fun s : AnchoredCountingState => fun i : I => nevanlinnaCoordinates s i.val)
        (ν : Measure AnchoredCountingState)) : μ = ν := by
  apply Subtype.ext
  apply anchored_law_eq_of_nevanlinnaCoordinates
  haveI : IsProbabilityMeasure (Measure.map nevanlinnaCoordinates (μ : Measure AnchoredCountingState)) :=
    isProbabilityMeasure_map continuous_nevanlinnaCoordinates.measurable.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map nevanlinnaCoordinates (ν : Measure AnchoredCountingState)) :=
    isProbabilityMeasure_map continuous_nevanlinnaCoordinates.measurable.aemeasurable
  haveI : IsFiniteMeasure (Measure.map nevanlinnaCoordinates (μ : Measure AnchoredCountingState)) :=
    ⟨by rw [Measure.map_apply continuous_nevanlinnaCoordinates.measurable MeasurableSet.univ]; simp⟩
  apply ext_of_generate_finite (μ := Measure.map nevanlinnaCoordinates (μ : Measure AnchoredCountingState))
    (ν := Measure.map nevanlinnaCoordinates (ν : Measure AnchoredCountingState)) (measurableCylinders (fun _ : ℕ => ℂ))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro A hA
    obtain ⟨I, B, hB, rfl⟩ := (mem_measurableCylinders A).mp hA
    have hI := congrArg (fun η : Measure (I → ℂ) => η B) (h I)
    dsimp only at hI
    have hmeas : Measurable (fun s : AnchoredCountingState => fun i : I => nevanlinnaCoordinates s i.val) :=
      (Finset.measurable_restrict I).comp continuous_nevanlinnaCoordinates.measurable
    rw [Measure.map_apply hmeas hB, Measure.map_apply hmeas hB] at hI
    rw [Measure.map_apply continuous_nevanlinnaCoordinates.measurable hB.cylinder,
      Measure.map_apply continuous_nevanlinnaCoordinates.measurable hB.cylinder]
    exact hI
  · simp

/-- Equality of every finite collection of off-real resolvent laws determines
the actual anchored probability law, hence its underlying counting process. -/
theorem anchored_law_eq_of_finite_resolvent_laws
    (μ ν : ProbabilityMeasure AnchoredCountingState)
    (h : ∀ (q : ℕ) (z : Fin q → ℂ), (∀ j, (z j).im ≠ 0) →
      Measure.map (fun s : AnchoredCountingState => fun j => anchoredNevanlinna s (z j))
        (μ : Measure AnchoredCountingState) =
      Measure.map (fun s : AnchoredCountingState => fun j => anchoredNevanlinna s (z j))
        (ν : Measure AnchoredCountingState)) : μ = ν := by
  apply anchored_law_eq_of_finite_sample_laws μ ν
  intro I
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let z : Fin (Fintype.card I) → ℂ := fun j => (nevanlinnaSample (e.symm j).val).val
  let g : (Fin (Fintype.card I) → ℂ) → (I → ℂ) := fun f i => f (e i)
  have hg : Measurable g := measurable_pi_lambda _ (fun i => measurable_pi_apply (e i))
  have hm : Measurable (fun s : AnchoredCountingState => fun j => anchoredNevanlinna s (z j)) :=
    measurable_pi_lambda _ (fun j => (continuous_anchoredNevanlinna (nevanlinnaSample (e.symm j).val).property).measurable)
  have hh := congrArg (Measure.map g) (h (Fintype.card I) z
    (fun j => (nevanlinnaSample (e.symm j).val).property))
  rw [Measure.map_map hg hm, Measure.map_map hg hm] at hh
  simpa only [Function.comp_def, g, z, Equiv.symm_apply_apply, nevanlinnaCoordinates] using hh

end BourgadeHuang
