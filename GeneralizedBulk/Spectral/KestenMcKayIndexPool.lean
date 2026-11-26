import GeneralizedBulk.Spectral.QuantileIndexPool

/-! Deterministic distinct quantile indices converging to every bulk energy,
with an explicit finite-sum error tending to zero. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Spectral

def bulkIndexFraction (d E : ℝ) : ℝ := 1-cdf d E

def bulkIndexPool (d E : ℝ) (k N : ℕ) (hN : 0 < N) : Fin k → Fin N :=
  indexPool (bulkIndexFraction d E) k N hN

theorem bulkIndexFraction_mem (d : ℝ) (hd : 3 ≤ d) (E : ℝ)
    (hE : E ∈ Ioo (-radius d) (radius d)) : bulkIndexFraction d E ∈ Ioo (0 : ℝ) 1 := by
  have hh := cdf_mem_Ioo d hd E hE
  constructor <;> dsimp [bulkIndexFraction] <;> linarith [hh.1,hh.2]

theorem finiteQuantile_bulkIndexPool_tendsto (d : ℝ) (hd : 3 ≤ d) (E : ℝ)
    (hE : E ∈ Ioo (-radius d) (radius d)) (k : ℕ) (N : ℕ → ℕ) (hpos : ∀ n, 0 < N n)
    (hN : Tendsto N atTop atTop) (j : Fin k) :
    Tendsto (fun n => finiteQuantile d hd (N n) (hpos n) (bulkIndexPool d E k (N n) (hpos n) j)) atTop (𝓝 E) := by
  let q := fun n => finiteQuantile d hd (N n) (hpos n) (bulkIndexPool d E k (N n) (hpos n) j)
  have hqmem (n) : q n ∈ Icc (-radius d) (radius d) := quantile_mem d hd _
  let p := fun n => cdfOrderIso d hd ⟨q n,hqmem n⟩
  let p0 := cdfOrderIso d hd ⟨E,hE.1.le,hE.2.le⟩
  have hp : Tendsto p atTop (𝓝 p0) := by
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun n => cdf d (q n)) atTop (𝓝 (cdf d E))
    have hr := indexPool_ratio_tendsto (bulkIndexFraction d E) (bulkIndexFraction_mem d hd E hE)
      k N hpos hN j
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hr
    simpa only [q,cdf_finiteQuantile,bulkIndexPool,bulkIndexFraction,sub_sub_cancel] using ht
  have ht := ((continuous_quantile d hd).tendsto p0).comp hp
  have he (n) : quantile d hd (p n) = q n := quantile_cdf d hd (q n) (hqmem n)
  have he0 : quantile d hd p0 = E := quantile_cdf d hd E ⟨hE.1.le,hE.2.le⟩
  simpa only [Function.comp_def,he,he0] using ht

def bulkPoolQuantileError (d : ℝ) (hd : 3 ≤ d) (E : ℝ) (k N : ℕ) (hN : 0 < N) : ℝ :=
  ∑ j : Fin k, |finiteQuantile d hd N hN (bulkIndexPool d E k N hN j)-E|

theorem bulkPoolQuantileError_nonneg (d : ℝ) (hd : 3 ≤ d) (E : ℝ) (k N : ℕ) (hN : 0 < N) :
    0 ≤ bulkPoolQuantileError d hd E k N hN := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem bulkPoolQuantileError_bound (d : ℝ) (hd : 3 ≤ d) (E : ℝ) (k N : ℕ) (hN : 0 < N) (j : Fin k) :
    |finiteQuantile d hd N hN (bulkIndexPool d E k N hN j)-E| ≤ bulkPoolQuantileError d hd E k N hN :=
  by
    unfold bulkPoolQuantileError
    exact Finset.single_le_sum (f := fun l : Fin k =>
      |finiteQuantile d hd N hN (bulkIndexPool d E k N hN l)-E|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

theorem bulkPoolQuantileError_tendsto (d : ℝ) (hd : 3 ≤ d) (E : ℝ)
    (hE : E ∈ Ioo (-radius d) (radius d)) (k : ℕ) (N : ℕ → ℕ) (hpos : ∀ n, 0 < N n)
    (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => bulkPoolQuantileError d hd E k (N n) (hpos n)) atTop (𝓝 0) := by
  have hh := tendsto_finset_sum Finset.univ (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) =>
    ((finiteQuantile_bulkIndexPool_tendsto d hd E hE k N hpos hN j).sub_const E).abs)
  simpa only [sub_self,abs_zero,Finset.sum_const_zero,bulkPoolQuantileError] using hh

end GeneralizedBulk.KestenMcKay
