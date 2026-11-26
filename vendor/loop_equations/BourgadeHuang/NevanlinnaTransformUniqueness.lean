import BourgadeHuang.NevanlinnaDetermination
import BourgadeHuang.AnalyticExponentialTransform
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Exponential resolvent transforms determine the actual law

Reflection converts complex sources at conjugate parameters into every real
characteristic function of each finite vector of resolvents. Fourier uniqueness
then identifies these vector laws, and atomic inversion identifies the actual
anchored counting law. Exponential-square anchor control separately proves that
all complex source expectations are genuine integrals.
-/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open MeasureTheory Filter BoundedContinuousFunction
namespace BourgadeHuang

/-- A finite complex linear source built from the actual reconstructed resolvents. -/
def finiteNevanlinnaSource {q : ℕ} (z c : Fin q → ℂ) (s : AnchoredCountingState) : ℂ :=
  ∑ j, c j * anchoredNevanlinna s (z j)

/-- Its genuine exponential transform. -/
def finiteNevanlinnaTransform {q : ℕ} (ν : Measure AnchoredCountingState) (z c : Fin q → ℂ) : ℂ :=
  ∫ s, Complex.exp (finiteNevanlinnaSource z c s) ∂ν

theorem continuous_finiteNevanlinnaSource {q : ℕ} (z c : Fin q → ℂ) (hz : ∀ j, (z j).im ≠ 0) :
    Continuous (finiteNevanlinnaSource z c) :=
  continuous_finset_sum _ (fun j _ => continuous_const.mul (continuous_anchoredNevanlinna (hz j)))

theorem anchoredGrowth_finiteNevanlinnaSource {q : ℕ} (z c : Fin q → ℂ) (hz : ∀ j, (z j).im ≠ 0) :
    AnchoredGrowth (finiteNevanlinnaSource z c) 1 :=
  AnchoredGrowth.finset_sum Finset.univ _ (fun j _ => (anchoredGrowth_nevanlinna (hz j)).const_mul (c j))

/-- Exponential-square anchor control proves absolute integrability of every
finite complex exponential source, in both half-planes simultaneously. -/
theorem integrable_exp_finiteNevanlinnaSource (ν : Measure AnchoredCountingState)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    {q : ℕ} (z c : Fin q → ℂ) (hz : ∀ j, (z j).im ≠ 0) :
    Integrable (fun s => Complex.exp (finiteNevanlinnaSource z c s)) ν := by
  simpa only [one_mul] using integrable_growth_mul_exp ν ha he (fun _ => 1)
    (finiteNevanlinnaSource z c) continuous_const (continuous_finiteNevanlinnaSource z c hz)
    (AnchoredGrowth.const 1) (anchoredGrowth_finiteNevanlinnaSource z c hz)

/-- The same finite vector with its Hilbert-space norm, for Fourier uniqueness. -/
def resolventVectorL2 {q : ℕ} (v : Fin q → ℂ) : EuclideanSpace ℂ (Fin q) :=
  (WithLp.equiv 2 (Fin q → ℂ)).symm v

local instance {q : ℕ} : MeasurableSpace (EuclideanSpace ℂ (Fin q)) := borel _
local instance {q : ℕ} : BorelSpace (EuclideanSpace ℂ (Fin q)) := ⟨rfl⟩
local instance {q : ℕ} : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin q)) :=
  InnerProductSpace.rclikeToReal ℂ _

theorem continuous_resolventVectorL2 {q : ℕ} : Continuous (@resolventVectorL2 q) :=
  PiLp.continuous_equiv_symm _ _

theorem measurableEmbedding_resolventVectorL2 {q : ℕ} : MeasurableEmbedding (@resolventVectorL2 q) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin q => ℂ)).toHomeomorph.symm.measurableEmbedding

/-- One complex coordinate and its reflection encode an arbitrary real linear
functional of its real and imaginary parts. -/
theorem paired_characteristic_exponent (u t : ℂ) :
    (conj t * Complex.I / 2) * u + (t * Complex.I / 2) * conj u =
      ((t * conj u).re : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring

/-- Pair every parameter with its reflection. -/
def pairedNevanlinnaParameters {q : ℕ} (z : Fin q → ℂ) : Fin (q + q) → ℂ :=
  Fin.addCases z (fun j => conj (z j))

def pairedNevanlinnaCoefficients {q : ℕ} (t : EuclideanSpace ℂ (Fin q)) : Fin (q + q) → ℂ :=
  Fin.addCases (fun j => conj (t j) * Complex.I / 2) (fun j => t j * Complex.I / 2)

theorem pairedNevanlinnaParameters_offReal {q : ℕ} (z : Fin q → ℂ)
    (hz : ∀ j, (z j).im ≠ 0) : ∀ j, (pairedNevanlinnaParameters z j).im ≠ 0 := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa only [pairedNevanlinnaParameters, Fin.addCases_left] using hz i
  · simpa only [pairedNevanlinnaParameters, Fin.addCases_right, Complex.conj_im, neg_ne_zero] using hz i

/-- The paired finite source is precisely the real characteristic exponent of
the finite Hilbert-space vector of resolvents. -/
theorem finiteNevanlinnaSource_paired {q : ℕ} (z : Fin q → ℂ)
    (t : EuclideanSpace ℂ (Fin q)) (s : AnchoredCountingState) :
    finiteNevanlinnaSource (pairedNevanlinnaParameters z) (pairedNevanlinnaCoefficients t) s =
      (inner (𝕜 := ℝ) (resolventVectorL2 (fun j => anchoredNevanlinna s (z j))) t : ℂ) * Complex.I := by
  simp only [finiteNevanlinnaSource, Fin.sum_univ_add, pairedNevanlinnaParameters,
    pairedNevanlinnaCoefficients, Fin.addCases_left, Fin.addCases_right, anchoredNevanlinna_conj,
    ← Finset.sum_add_distrib, paired_characteristic_exponent]
  rw [real_inner_eq_re_inner ℂ, PiLp.inner_apply]
  simp only [RCLike.inner_apply, map_sum, ← Finset.sum_mul, ← Complex.ofReal_sum]
  rfl

/-- Equality of all finite complex source transforms determines the full
anchored probability law. The characteristic subfamily is automatically bounded. -/
theorem anchored_law_eq_of_exponential_transforms
    (μ ν : ProbabilityMeasure AnchoredCountingState)
    (h : ∀ (q : ℕ) (z c : Fin q → ℂ), (∀ j, (z j).im ≠ 0) →
      finiteNevanlinnaTransform (μ : Measure AnchoredCountingState) z c =
      finiteNevanlinnaTransform (ν : Measure AnchoredCountingState) z c) : μ = ν := by
  apply anchored_law_eq_of_finite_resolvent_laws μ ν
  intro q z hz
  let F : AnchoredCountingState → (Fin q → ℂ) := fun s j => anchoredNevanlinna s (z j)
  have hF : Measurable F := (continuous_pi (fun j => continuous_anchoredNevanlinna (hz j))).measurable
  let G : AnchoredCountingState → EuclideanSpace ℂ (Fin q) := resolventVectorL2 ∘ F
  have hG : Measurable G := continuous_resolventVectorL2.measurable.comp hF
  let μG : ProbabilityMeasure (EuclideanSpace ℂ (Fin q)) := μ.map hG.aemeasurable
  let νG : ProbabilityMeasure (EuclideanSpace ℂ (Fin q)) := ν.map hG.aemeasurable
  have he : (μG : Measure (EuclideanSpace ℂ (Fin q))) = (νG : Measure (EuclideanSpace ℂ (Fin q))) := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_eq_integral_innerProbChar, charFun_eq_integral_innerProbChar]
    change (∫ v, innerProbChar t v ∂Measure.map G (μ : Measure AnchoredCountingState)) =
      ∫ v, innerProbChar t v ∂Measure.map G (ν : Measure AnchoredCountingState)
    rw [integral_map hG.aemeasurable (innerProbChar t).continuous.aestronglyMeasurable,
      integral_map hG.aemeasurable (innerProbChar t).continuous.aestronglyMeasurable]
    have hh := h (q + q) (pairedNevanlinnaParameters z) (pairedNevanlinnaCoefficients t)
      (pairedNevanlinnaParameters_offReal z hz)
    simpa only [finiteNevanlinnaTransform, finiteNevanlinnaSource_paired, innerProbChar_apply,
      G, F, Function.comp_apply] using hh
  change Measure.map G (μ : Measure AnchoredCountingState) =
    Measure.map G (ν : Measure AnchoredCountingState) at he
  have hm := (continuous_resolventVectorL2 (q := q)).measurable
  rw [show G = resolventVectorL2 ∘ F from rfl, ← Measure.map_map hm hF,
    ← Measure.map_map hm hF] at he
  have hc := congrArg (Measure.comap resolventVectorL2) he
  simpa only [measurableEmbedding_resolventVectorL2.comap_map] using hc

end BourgadeHuang
