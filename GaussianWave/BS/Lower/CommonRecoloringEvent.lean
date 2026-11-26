import GaussianWave.BS.Lower.RecoloringLimit
import GaussianWave.BS.Reused.Graph.GrowingPaletteGood

/-! One literal uniform-simple-RRG event controls every finite palette and
therefore every randomized finite recoloring. A summable palette slack is
absorbed into the fixed-palette counting constant; no union over kernels is
needed. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
set_option maxHeartbeats 1000000

namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite
open GaussianWave.BS.Reused.Graph GaussianWave.BS.Reused.Graph.Configuration
open GaussianWave.BS.Reused.Graph.ColorProfiles

def paletteShift (q : ℕ) : ℝ := (q+1)*Real.log 2

/-- A fixed palette slack can be absorbed into the fixed counting constant. -/
theorem graphProfileGood_shift {N d q m : ℕ} (G : RegularGraph N d)
    (C t s : ℝ) (M : ℕ) (hs : 0 ≤ s)
    (hG : GraphProfileGood (q := q) (m := m) C (t+s) M G) :
    GraphProfileGood (q := q) (m := m) (C+s) t M G := by
  intro S
  apply (hG S).trans
  apply Real.exp_le_exp.mpr
  unfold symmetricProfileExponent
  have hsq : 0 ≤ (q : ℝ)^2 := sq_nonneg _
  nlinarith [mul_nonneg hsq hs]

def AllPaletteGood {N d m : ℕ} (C t : ℝ) (M : ℕ) (G : RegularGraph N d) : Prop :=
  ∀ q : ℕ,GraphProfileGood (q := q) (m := m) (C+paletteShift q) t M G

/-- Countable union bound against an actual summable nonnegative real
majorant, retaining the finite-measure hypotheses needed by `toReal`. -/
theorem measureReal_iUnion_le_of_majorant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : ℕ → Set Ω) (b : ℕ → ℝ)
    (hb0 : ∀ n,0 ≤ b n) (hbs : Summable b) (hb : ∀ n,μ.real (A n) ≤ b n) :
    μ.real (⋃ n,A n) ≤ ∑' n,b n := by
  have hENN (n : ℕ) : μ (A n) ≤ ENNReal.ofReal (b n) := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal (hb0 n)] using hb n
  have hm : μ (⋃ n,A n) ≤ ENNReal.ofReal (∑' n,b n) := by
    calc
      _ ≤ ∑' n,μ (A n) := measure_iUnion_le A
      _ ≤ ∑' n,ENNReal.ofReal (b n) := ENNReal.tsum_le_tsum hENN
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg hb0 hbs).symm
  have h := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hm
  simpa only [ENNReal.toReal_ofReal (tsum_nonneg hb0)] using h

/-- A single graph event simultaneously controls every finite palette under
the actual uniform labeled simple regular graph law. -/
theorem all_palette_good_probability {N d m : ℕ} [Nonempty (RegularGraph N d)]
    (C : ℝ) (hC : ∀ k : ℕ,|Real.log k.factorial-logFactorialMain k| ≤ C+Real.log (k+1))
    (hN : 0 < N) (hd : 0 < d) (hm : 0 < m) (hNd : N*d = 2*m)
    (M : ℕ) (hL : 6 ≤ N*d) (hM : 8*d*(d+1) ≤ M) (hsize : 4*d*(d+1)+M < N*d) (t : ℝ) :
    (regularGraphLaw N d).real {G | ¬AllPaletteGood (m := m) C t M G} ≤ Real.exp (-t) := by
  letI := regularGraphLaw_isProbability N d
  let b (q : ℕ) : ℝ := Real.exp (-t)*(1/2 : ℝ)^(q+1)
  have hr : |(1/2 : ℝ)| < 1 := by norm_num [abs_of_nonneg]
  have hgeom : HasSum (fun q : ℕ => (1/2 : ℝ)^(q+1)) 1 := by
    convert (hasSum_geometric_of_abs_lt_one (r := (1/2 : ℝ)) hr).mul_left (1/2 : ℝ) using 1
    · funext q; rw [pow_succ]; ring
    · norm_num
  have hsum : HasSum b (Real.exp (-t)) := by simpa only [mul_one] using hgeom.mul_left (Real.exp (-t))
  have hb (q : ℕ) : (regularGraphLaw N d).real
      {G | ¬GraphProfileGood (q := q) (m := m) (C+paletteShift q) t M G} ≤ b q := by
    have hshift : 0 ≤ paletteShift q := mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
    have hsub : {G : RegularGraph N d | ¬GraphProfileGood (q := q) (m := m) (C+paletteShift q) t M G} ⊆
        {G | ¬GraphProfileGood (q := q) (m := m) C (t+paletteShift q) M G} := by
      intro G hbad hgood
      exact hbad (graphProfileGood_shift G C t (paletteShift q) M hshift hgood)
    have hprob := regularGraph_uniform_symmetric_profile_probability (q := q) C hC hN hd hm hNd M hL hM hsize (t+paletteShift q)
    apply ((measureReal_mono hsub).trans hprob).trans_eq
    unfold b paletteShift
    rw [neg_add,Real.exp_add]
    congr 1
    calc
      _ = Real.exp (((q+1 : ℕ) : ℝ)*(-Real.log 2)) := by congr 1; push_cast; ring
      _ = (Real.exp (-Real.log 2))^(q+1) := Real.exp_nat_mul _ _
      _ = _ := by rw [Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have he : {G : RegularGraph N d | ¬AllPaletteGood (m := m) C t M G} =
      ⋃ q : ℕ,{G | ¬GraphProfileGood (q := q) (m := m) (C+paletteShift q) t M G} := by
    ext G; simp [AllPaletteGood]
  rw [he]
  exact (measureReal_iUnion_le_of_majorant (regularGraphLaw N d) _ b
    (fun q => mul_nonneg (Real.exp_pos _).le (pow_nonneg (by norm_num) _)) hsum.summable hb).trans_eq hsum.tsum_eq

/-- The simultaneous recoloring event has stretched-exponentially small
failure along every admissible growing graph-size sequence. -/
theorem all_palette_good_probability_eventually
    (d : ℕ) (hd : 0 < d) (N m : ℕ → ℕ) (hNinf : Tendsto N atTop atTop)
    (hgraphs : ∀ n,Nonempty (RegularGraph (N n) d)) (hNd : ∀ n,N n*d = 2*m n)
    (C : ℝ) (hC : ∀ k : ℕ,|Real.log k.factorial-logFactorialMain k| ≤ C+Real.log (k+1))
    (M : ℕ) (hM : 8*d*(d+1) ≤ M) :
    ∀ᶠ n in atTop,(regularGraphLaw (N n) d).real
      {G | ¬AllPaletteGood (m := m n) C (Real.sqrt (N n : ℝ)) M G} ≤ Real.exp (-Real.sqrt (N n : ℝ)) := by
  filter_upwards [hNinf.eventually (eventually_ge_atTop (7+4*d*(d+1)+M))] with n hn
  letI := hgraphs n
  have hmul : N n ≤ N n*d := Nat.le_mul_of_pos_right _ hd
  have hnp : 0 < N n := by omega
  have hmp : 0 < m n := by have h := hNd n; omega
  exact all_palette_good_probability C hC hnp hd hmp (hNd n) M (by omega) hM (by omega) _

/-- Genuine convergence in probability of the simultaneous all-palette
counting event under the actual uniform simple-regular-graph law. -/
theorem all_palette_good_failure_tendsto_zero
    (d : ℕ) (hd : 0 < d) (N m : ℕ → ℕ) (hNinf : Tendsto N atTop atTop)
    (hgraphs : ∀ n,Nonempty (RegularGraph (N n) d)) (hNd : ∀ n,N n*d = 2*m n)
    (C : ℝ) (hC : ∀ k : ℕ,|Real.log k.factorial-logFactorialMain k| ≤ C+Real.log (k+1))
    (M : ℕ) (hM : 8*d*(d+1) ≤ M) :
    Tendsto (fun n => (regularGraphLaw (N n) d).real
      {G | ¬AllPaletteGood (m := m n) C (Real.sqrt (N n : ℝ)) M G}) atTop (𝓝 0) := by
  have hNr : Tendsto (fun n => (N n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hNinf
  have hsqrt : Tendsto (fun n => Real.sqrt (N n : ℝ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hNr.eventually (eventually_ge_atTop ((max b 0)^2))] with n hn
    calc
      b ≤ max b 0 := le_max_left _ _
      _ = Real.sqrt ((max b 0)^2) := (Real.sqrt_sq (le_max_right _ _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt hn
  have hexp := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hsqrt)
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => measureReal_nonneg))
    (all_palette_good_probability_eventually d hd N m hNinf hgraphs hNd C hC M hM) hexp

/-- The counting constant and the degree-dependent simplicity budget are
obtained internally. No asymptotic graph-counting premise remains. -/
theorem exists_all_palette_good_events
    (d : ℕ) (hd : 0 < d) (N m : ℕ → ℕ) (hNinf : Tendsto N atTop atTop)
    (hgraphs : ∀ n,Nonempty (RegularGraph (N n) d)) (hNd : ∀ n,N n*d = 2*m n) :
    ∃ C : ℝ,0 ≤ C ∧ Tendsto (fun n => (regularGraphLaw (N n) d).real
      {G | ¬AllPaletteGood (m := m n) C (Real.sqrt (N n : ℝ)) (8*d*(d+1)) G}) atTop (𝓝 0) := by
  obtain ⟨C,hC0,hC⟩ := exists_log_factorial_error_bound
  exact ⟨C,hC0,all_palette_good_failure_tendsto_zero d hd N m hNinf hgraphs hNd C hC _ le_rfl⟩

/-- The same good graph sequence supplies the k=0 randomized lower bound for
all finite palettes; only the fixed-palette constant changes. -/
theorem all_palette_graph_limit_randomized_entropy {d r : ℕ}
    (hd : 0 < d) (N m : ℕ → ℕ) (hN : ∀ n,0 < N n) (hNinf : Tendsto N atTop atTop)
    (hNd : ∀ n,N n*d = 2*m n) (G : ∀ n,RegularGraph (N n) d)
    (x : ∀ n,Fin (N n) → Fin r → ℝ) (C : ℝ) (M : ℕ)
    (hG : ∀ᶠ n in atTop,AllPaletteGood (m := m n) C (Real.sqrt (N n : ℝ)) M (G n))
    (μ : Measure ((Fin r × Fin (d+1)) → ℝ))
    (hweak : WeakLawConverges (fun n => markedStarLaw (G n) (x n)) μ) :
    ∀ (q : ℕ) (_hq : 0 < q) (φ : (Fin r → ℝ) → Fin q → ℝ)
      (_hφ0 : ∀ y b,0 ≤ φ y b) (_hφ1 : ∀ y,∑ b,φ y b = 1)
      (_hφc : ∀ b,Continuous (fun y => φ y b)),
      (∫ y,rootEntropyTest φ y ∂μ) ≤
        entropy (starRecolorMass μ φ)-((d : ℝ)/2)*entropy (edgeMassOfStar (starRecolorMass μ φ)) := by
  intro q hq φ hφ0 hφ1 hφc
  apply randomized_star_entropy_lower_of_graph_limit hd hq N m hN hNinf hNd G x (C+paletteShift q) M
    (hG.mono (fun n hn => hn q)) μ hweak φ hφ0 hφ1 hφc

end GaussianWave.BS.Lower
