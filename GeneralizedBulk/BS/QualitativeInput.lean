import GeneralizedBulk.BS.SpectralAdapter
import GaussianWave.BS.SpectralBSClassification
import GaussianWave.BS.WeakProbabilityLimit

/-!
# The proved BS qualitative input inside the merged bulk project

The hypotheses describe the literal uniform labeled simple-regular-graph
model and its edge count. The constructor proves the sibling's qualitative
Gaussianity contract; it accepts no BS or Gaussianity assumption.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.SiblingBulk
open BS BS.Reused.Graph

def fullEigenData {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (D : GeneralizedBulk.External.RegularSpectralData d N Ω) (n : ℕ) (ω : Ω) :
    RegularEigenData d (N n) (N n) :=
  selectedEigenData D n ω id Function.injective_id

def spectralRegularGraph {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (D : GeneralizedBulk.External.RegularSpectralData d N Ω) (n : ℕ) (ω : Ω) :
    RegularGraph (N n) d := (fullEigenData D n ω).regularGraph

theorem exists_squareMass_bound_of_eventually_orthonormal {r : ℕ} {N : ℕ → ℕ}
    (q : ∀ n, Fin r → Fin (N n) → ℝ)
    (horth : ∀ᶠ n in atTop, ∀ a b, (∑ v, q n a v * q n b v) = if a = b then 1 else 0) :
    ∃ M : Fin r → ℝ, ∀ n a, squareMass (q n a) ≤ M a := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp horth
  let M := fun a => 1 + ∑ j ∈ Finset.range n₀, squareMass (q j a)
  refine ⟨M, ?_⟩
  intro n a
  have hnonneg (j) : 0 ≤ squareMass (q j a) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hn : n₀ ≤ n
  · have hone : squareMass (q n a) = 1 := by
      simpa only [squareMass, pow_two, if_pos rfl] using hn₀ n hn a a
    rw [hone]
    have hs : 0 ≤ ∑ j ∈ Finset.range n₀, squareMass (q j a) :=
      Finset.sum_nonneg (fun j _ => hnonneg j)
    exact le_add_of_nonneg_right hs
  · have hs := Finset.single_le_sum (fun j _ => hnonneg j)
      (Finset.mem_range.mpr (Nat.lt_of_not_ge hn))
    change squareMass (q n a) ≤ 1 + ∑ j ∈ Finset.range n₀, squareMass (q j a)
    simpa only [Finset.sum_range] using hs.trans (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))

theorem tupleResidual_coordinate_le {d r : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (D : GeneralizedBulk.External.RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)
    (q : Fin r → Fin (N n) → ℝ) (energy : ℝ) (a : Fin r) :
    squareMass (eigenResidual (fullEigenData D n ω).adjacency energy (q a)) ≤
      D.tupleResidual n ω q energy := by
  exact Finset.single_le_sum
    (f := fun b : Fin r => squareMass
      (eigenResidual (fullEigenData D n ω).adjacency energy (q b)))
    (fun b _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ a)

def provedBSQualitativeInput {m : ℕ} (hm : 0 < m) {N : ℕ → ℕ}
    {Ω : Type*} [MeasurableSpace Ω]
    (D : GeneralizedBulk.External.RegularSpectralData (m + 2) N Ω)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (edgeCount : ℕ → ℕ) (hNE : ∀ n, N n * (m + 2) = 2 * edgeCount n)
    (hgraph : ∀ n, Measurable (spectralRegularGraph D n))
    (hmodel : ∀ n, Measure.map (spectralRegularGraph D n) P = regularGraphLaw (N n) (m + 2))
    (K : Set ℝ) (hcompact : IsCompact K)
    (hbulk : ∀ x ∈ K, |x| < 2 * Real.sqrt (m + 1 : ℝ)) :
    GeneralizedBulk.External.BSQualitativeInput D P K := by
  have hΩ : Nonempty Ω := (show ProbabilityMeasure Ω from ⟨P, inferInstance⟩).nonempty
  let ω₀ := Classical.choice hΩ
  have hgraphs (n) : Nonempty (RegularGraph (N n) (m + 2)) := ⟨spectralRegularGraph D n ω₀⟩
  letI (n : ℕ) : Nonempty (RegularGraph (N n) (m + 2)) := hgraphs n
  letI (n : ℕ) : IsProbabilityMeasure (regularGraphLaw (N n) (m + 2)) := regularGraphLaw_isProbability _ _
  let A : RRGClassificationEvents m N edgeCount :=
    Classical.choice (exists_RRGClassificationEvents m N edgeCount D.size_tendsto hgraphs hNE)
  let good := fun (_ : ℕ) n => (spectralRegularGraph D n) ⁻¹' A.good n
  refine { degree_ge_three := by omega
           compact_bulk := ⟨hcompact, ?_⟩
           good := good
           measurable_good := ?_
           good_probability := ?_
           gaussian_limit := ?_ }
  · intro x hx
    convert hbulk x hx using 1 <;> norm_num <;> ring
  · intro k n
    exact (Set.toFinite (A.good n)).measurableSet.preimage (hgraph n)
  · intro k
    have hreal : Tendsto (fun n => (regularGraphLaw (N n) (m + 2)).real (A.good n)ᶜ) atTop (𝓝 0) := by
      simpa only [RRGClassificationEvents.good, Set.compl_setOf] using A.failure_tendsto
    have hENN : Tendsto (fun n => (regularGraphLaw (N n) (m + 2)) (A.good n)ᶜ) atTop (𝓝 0) :=
      (ENNReal.tendsto_toReal_iff (fun n => measure_ne_top _ _) ENNReal.zero_ne_top).mp
        (by simpa only [ENNReal.toReal_zero] using hreal)
    have heq (n) : P (good k n)ᶜ = (regularGraphLaw (N n) (m + 2)) (A.good n)ᶜ := by
      rw [← hmodel n, Measure.map_apply (hgraph n) (Set.toFinite (A.good n)ᶜ).measurableSet]
      rfl
    simpa only [heq] using hENN
  · intro k _hk ω hgood q energy _henergy _hcenter horth hres energyLimit hEL henergyLimit φ hφ ν hweak
    obtain ⟨M, hM⟩ := exists_squareMass_bound_of_eventually_orthonormal q horth
    have hres' (a : Fin k) : Tendsto (fun n => squareMass
        (eigenResidual (fullEigenData D n (ω n)).adjacency (energy n) (q n a))) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        (fun n => tupleResidual_coordinate_le D n (ω n) (q n) (energy n) a) hres
    have hG := common_graph_signal_BSJointClassification N edgeCount m k hm N
      (fun n => fullEigenData D n (ω n)) D.size_tendsto hNE A.entropyConstant A.radius A.radius_tendsto
      hgood q M hM (fun n _ => energy n) energyLimit (fun _ => henergyLimit) (hbulk energyLimit hEL) hres'
    letI (n : ℕ) : IsProbabilityMeasure ((fullEigenData D (φ n) (ω (φ n))).starLaw (q (φ n))) :=
      (fullEigenData D (φ n) (ω (φ n))).starLaw_isProbability _
    have hprob : IsProbabilityMeasure ν :=
      weakLawConverges_isProbabilityMeasure
        (fun n => (fullEigenData D (φ n) (ω (φ n))).starLaw (q (φ n))) ν hweak
    exact hG φ hφ ⟨ν, hprob⟩ hweak

end GaussianWave.SiblingBulk
