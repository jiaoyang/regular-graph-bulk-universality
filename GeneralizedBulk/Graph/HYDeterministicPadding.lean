import GeneralizedBulk.Spectral.KestenMcKayIndexPool
import GeneralizedBulk.Graph.KestenMcKayLogPotential

/-! Measurable deterministic padding by genuine nonconstant eigenindices
converging uniformly to a fixed bulk energy on the actual HY rigidity event. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.KestenMcKay GeneralizedBulk.Spectral
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def bulkPaddingIndex (E : ℝ) (k n : ℕ) : Fin k → Fin (N n) :=
  bulkIndexPool d E k (N n) (D.size_pos n)

theorem measurable_bulkPaddingIndex (E : ℝ) (k n : ℕ) (j : Fin k) :
    Measurable (fun _ : Ω => D.bulkPaddingIndex E k n j) := measurable_const

def bulkPaddingError {P : Measure Ω} [IsProbabilityMeasure P] (hd : 3 ≤ (d : ℝ))
    (H : HYCoarseInput D P (D.kestenMcKayQuantile hd)) (E : ℝ) (k n : ℕ) : ℝ :=
  (N n : ℝ)^(-H.rigidity_exponent) + bulkPoolQuantileError d hd E k (N n) (D.size_pos n)

theorem bulkPaddingError_nonneg {P : Measure Ω} [IsProbabilityMeasure P] (hd : 3 ≤ (d : ℝ))
    (H : HYCoarseInput D P (D.kestenMcKayQuantile hd)) (E : ℝ) (k n : ℕ) :
    0 ≤ D.bulkPaddingError hd H E k n :=
  add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (bulkPoolQuantileError_nonneg d hd E k (N n) (D.size_pos n))

theorem bulkPaddingError_tendsto {P : Measure Ω} [IsProbabilityMeasure P] (hd : 3 ≤ (d : ℝ))
    (H : HYCoarseInput D P (D.kestenMcKayQuantile hd)) (E : ℝ)
    (hE : E ∈ Ioo (-radius d) (radius d)) (k : ℕ) :
    Tendsto (fun n => D.bulkPaddingError hd H E k n) atTop (𝓝 0) := by
  have hr := (tendsto_rpow_neg_atTop H.rigidity_exponent_pos).comp
    (tendsto_natCast_atTop_atTop.comp D.size_tendsto)
  have hq := bulkPoolQuantileError_tendsto d hd E hE k N D.size_pos D.size_tendsto
  simpa only [bulkPaddingError,add_zero] using hr.add hq

theorem HY_bulkPaddingIndex_eventually {P : Measure Ω} [IsProbabilityMeasure P] (hd : 3 ≤ (d : ℝ))
    (H : HYCoarseInput D P (D.kestenMcKayQuantile hd)) (E : ℝ)
    (hE : E ∈ Ioo (-radius d) (radius d)) (k : ℕ) :
    ∀ᶠ n in atTop, ∀ ω ∈ H.events.good n,
      Function.Injective (D.bulkPaddingIndex E k n) ∧
      (∀ j, D.bulkPaddingIndex E k n j ≠ ⟨0,D.size_pos n⟩) ∧
      ∀ j, |D.eigenvalue n ω (D.bulkPaddingIndex E k n j)-E| ≤ D.bulkPaddingError hd H E k n := by
  filter_upwards [indexPool_eventually_ready (bulkIndexFraction d E) (bulkIndexFraction_mem d hd E hE)
    k N D.size_tendsto, eventually_ge_atTop H.events.threshold] with n hn hthreshold
  intro ω hω
  refine ⟨indexPool_injective _ _ _ _ hn, ?_, ?_⟩
  · intro j hj
    have hz := indexPool_ne_zero (bulkIndexFraction d E) k (N n) (D.size_pos n) hn j
    exact hz (congrArg Fin.val hj)
  · intro j
    have hz := indexPool_ne_zero (bulkIndexFraction d E) k (N n) (D.size_pos n) hn j
    have hr := H.rigidity n hthreshold ω hω (D.bulkPaddingIndex E k n j) hz
    have hq := bulkPoolQuantileError_bound d hd E k (N n) (D.size_pos n) j
    exact (abs_sub_le (D.eigenvalue n ω (D.bulkPaddingIndex E k n j))
      (D.kestenMcKayQuantile hd n (D.bulkPaddingIndex E k n j)) E).trans (add_le_add hr hq)

end GeneralizedBulk.External.RegularSpectralData
