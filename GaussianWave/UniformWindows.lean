import GaussianWave.UniformStars
import GaussianWave.CoverNormalization

/-!
# Uniform finite-window Gaussian limits in graph probability

The finite regular graph data and cover sampling spaces may depend on the
candidate orthonormal eigenfamily. Infinite covering maps and tree geometry
remain explicit combinatorial/sampling adapters. The covariance identities,
variance-one normalization, product law, Wasserstein upgrade, and uniform
probabilistic selection are proved consequences of those adapters and the
qualitative BS classification and tight root fourth bound.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace GaussianWave

/-- The uniform finite-window theorem of the note, with its two genuine
external inputs visible: common good-graph qualitative BS Gaussianity and
uniform root fourth-moment control tight in graph probability. Empty candidate
sets are allowed and contribute no bad event. -/
theorem uniform_normalizedWindow_wasserstein_inProbability
    {d k m : ℕ} (hd : 3 ≤ d) (hk : 0 < k)
    (N : ℕ → ℕ) {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (S : ∀ n, Ω n → Type*)
    (D : ∀ n ω, S n ω → RegularEigenData d (N n) k)
    {T : Type*} (G : RadialTreeGeometry d T) (site : Fin m → T)
    (CoverΩ : ∀ n ω, S n ω → Type*)
    [∀ n ω s, MeasurableSpace (CoverΩ n ω s)]
    (CoverP : ∀ n ω s, Measure (CoverΩ n ω s))
    [∀ n ω s, IsProbabilityMeasure (CoverP n ω s)]
    (Sc : ∀ n ω s, CoverSampling (D n ω s) G (CoverP n ω s))
    (K : Set ℝ) (hK : IsCompact K) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (good : ∀ n, Set (Ω n))
    (hbad : Tendsto (fun n => (P n (good n)ᶜ).toReal) atTop (𝓝 0))
    (M : ∀ n, Ω n → ℝ) (htight : TightInProbability P M)
    (hroot : ∀ n ω s, ω ∈ good n → StarAdmissible (D n ω s) K (δ n) →
      ∀ i, (N n : ℝ) * ∑ v, (D n ω s).eigenvector i v ^ 4 ≤ M n ω)
    (BS : ∀ r : ℕ → ℕ, StrictMono r → ∀ ω : ∀ j, Ω (r j),
      ∀ s : ∀ j, S (r j) (ω j),
      (∀ j, ω j ∈ good (r j)) →
      (∀ j, StarAdmissible (D (r j) (ω j) (s j)) K (δ (r j))) →
      ∀ E ∈ K, (∀ i, Tendsto (fun j => (D (r j) (ω j) (s j)).eigenvalue i)
        atTop (𝓝 E)) →
      BSJointClassification (fun j => (Sc (r j) (ω j) (s j)).eigenWindowLaw site)) :
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun n =>
      (P n {ω | ∃ s : S n ω, StarAdmissible (D n ω s) K (δ n) ∧
        ε ≤ wassersteinTwo ((Sc n ω s).eigenWindowLaw site)
          ((Sc n ω s).eigenWindowGaussian (by omega) site)}).toReal) atTop (𝓝 0) := by
  classical
  intro ε hε
  let bad : ∀ n, Set (Ω n) := fun n => {ω | ∃ s : S n ω,
    StarAdmissible (D n ω s) K (δ n) ∧
      ε ≤ wassersteinTwo ((Sc n ω s).eigenWindowLaw site)
        ((Sc n ω s).eigenWindowGaussian (by omega) site)}
  apply probability_bad_tendsto_zero_of_good_subsequences P good bad hbad M htight
  intro C r hr ω hω
  by_contra hn
  have hfreq : ∃ᶠ j in atTop, ω j ∈ bad (r j) := by
    simpa only [not_eventually, not_not] using hn
  obtain ⟨t, ht, hb⟩ := extraction_of_frequently_atTop hfreq
  let s : ∀ j, S (r (t j)) (ω (t j)) := fun j => Classical.choose (hb j)
  have hs (j : ℕ) : StarAdmissible (D (r (t j)) (ω (t j)) (s j)) K (δ (r (t j))) :=
    (Classical.choose_spec (hb j)).1
  have hlarge (j : ℕ) : ε ≤ wassersteinTwo
      ((Sc (r (t j)) (ω (t j)) (s j)).eigenWindowLaw site)
      ((Sc (r (t j)) (ω (t j)) (s j)).eigenWindowGaussian (by omega) site) :=
    (Classical.choose_spec (hb j)).2
  let i0 : Fin k := ⟨0, hk⟩
  obtain ⟨E, hEK, v, hv, hEv⟩ := hK.tendsto_subseq
    (fun j => (hs j).1 i0)
  let rr := r ∘ t ∘ v
  have hrr : StrictMono rr := hr.comp (ht.comp hv)
  let ω' : ∀ j, Ω (rr j) := fun j => ω (t (v j))
  let s' : ∀ j, S (rr j) (ω' j) := fun j => s (v j)
  let D' : ∀ j, RegularEigenData d (N (rr j)) k :=
    fun j => D (rr j) (ω' j) (s' j)
  have hEig (i : Fin k) : Tendsto (fun j => (D' j).eigenvalue i) atTop (𝓝 E) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    have hz := (tendsto_order.mp (hδ.comp hrr.tendsto_atTop)).2 (η / 2) (by linarith)
    have he := (Metric.tendsto_nhds.mp hEv) (η / 2) (by linarith)
    filter_upwards [hz, he] with j hj hjE
    rw [Real.dist_eq]
    have hp := (hs (v j)).2 i i0
    have hh := abs_sub_le ((D' j).eigenvalue i) ((D' j).eigenvalue i0) E
    rw [Real.dist_eq] at hjE
    change |(D' j).eigenvalue i0 - E| < η / 2 at hjE
    change δ (rr j) < η / 2 at hj
    change |(D' j).eigenvalue i - (D' j).eigenvalue i0| ≤ δ (rr j) at hp
    linarith
  have hBS : BSJointClassification (fun j => (Sc (rr j) (ω' j) (s' j)).eigenWindowLaw site) :=
    BS rr hrr ω' s' (fun j => (hω (t (v j))).1)
      (fun j => hs (v j)) E hEK hEig
  have hroot' (j : ℕ) (i : Fin k) :
      (N (rr j) : ℝ) * ∑ z, (D' j).eigenvector i z ^ 4 ≤ C :=
    (hroot (rr j) (ω' j) (s' j) (hω (t (v j))).1 (hs (v j)) i).trans
      (hω (t (v j))).2
  have hW := eigenvectors_normalizedWindow_wasserstein (by omega : 2 ≤ d)
    (N ∘ rr) D' G site
    (fun j => CoverΩ (rr j) (ω' j) (s' j))
    (fun j => CoverP (rr j) (ω' j) (s' j))
    (fun j => Sc (rr j) (ω' j) (s' j)) E hEig C hroot' hBS
  have hsmall := (tendsto_order.mp hW).2 ε hε
  obtain ⟨j, hj⟩ := hsmall.exists
  exact (not_lt_of_ge (hlarge (v j))) hj

end GaussianWave
