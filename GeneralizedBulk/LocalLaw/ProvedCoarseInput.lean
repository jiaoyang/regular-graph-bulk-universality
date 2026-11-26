import GeneralizedBulk.LocalLaw.CoarseSpectrum
import GeneralizedBulk.LocalLaw.CoarseQuantiles
import GeneralizedBulk.LocalLaw.SourceProbability
import GeneralizedBulk.Graph.HYResolventChannel
import GeneralizedBulk.Graph.KestenMcKayLogPotential

/-! The proved source rigidity and all-eigenvector estimates give the exact
coarse HY record, after the actual spectral and quantile normalizations. -/
noncomputable section
open MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Graph GeneralizedBulk.LocalLawBridge SpectralConsequences

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def sourceCoarseGood (hd : 3 ≤ d) (α : ℝ) (n : ℕ) : Set Ω :=
  {ω | PaperRigid hd α (D.localLawGraph n ω) ∧ PaperAllEigenvectors (D.localLawGraph n ω)}

theorem measurableSet_sourceCoarseGood (hd : 3 ≤ d) (α : ℝ) (n : ℕ) :
    MeasurableSet (D.sourceCoarseGood hd α n) := by
  change MeasurableSet ((D.spectralRegularGraph n) ⁻¹'
    {g : Graph.RegularGraph (N n) d | PaperRigid hd α g ∧ PaperAllEigenvectors g})
  exact (D.measurable_spectralRegularGraph n) (Set.to_countable _).measurableSet

theorem rigidity_of_localLaw_source (hd : 3 ≤ d) (n : ℕ) (ω : Ω)
    (α β : ℝ) (hβα : 2*β ≤ α) (hβq : 2*β ≤ 2/3)
    (hN : 1 ≤ N n)
    (hlarge : Real.sqrt ((d : ℝ)-1)*(1+(12*Real.pi)^(2/3 : ℝ)) ≤ (N n : ℝ)^β)
    (hrigid : PaperRigid hd α (D.localLawGraph n ω)) (i : Fin (N n)) (hi : i.val ≠ 0) :
    |D.eigenvalue n ω i-D.kestenMcKayQuantile (by exact_mod_cast hd) n i| ≤ (N n : ℝ)^(-β) := by
  let s : ℝ := Real.sqrt ((d : ℝ)-1)
  let C : ℝ := (12*Real.pi)^(2/3 : ℝ)
  let q := D.kestenMcKayQuantile (by exact_mod_cast hd) n i
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hn : (0 : ℝ) < N n := Nat.cast_pos.mpr (D.size_pos n)
  have hn1 : (1 : ℝ) ≤ N n := by exact_mod_cast hN
  have hsource : |D.eigenvalue n ω i/s-SpectralConsequences.classicalLocation d hd i| ≤ (N n : ℝ)^(-α) := by
    have hh := hrigid (i.val+1) (by omega) (by omega)
    simpa only [Nat.add_sub_cancel, Fin.eta, D.localLaw_sortedEigenvalues_eq hd n ω] using hh
  have hquant := finiteQuantile_source_error d hd (N n) (D.size_pos n) i
  change |q/s-SpectralConsequences.classicalLocation d hd i| ≤ C*(N n : ℝ)^(-(2/3 : ℝ)) at hquant
  have habs : |D.eigenvalue n ω i-q| = s*|D.eigenvalue n ω i/s-q/s| := by
    have he : s*(D.eigenvalue n ω i/s-q/s) = D.eigenvalue n ω i-q := by field_simp
    rw [←he,abs_mul,abs_of_pos hs]
  rw [show D.kestenMcKayQuantile (by exact_mod_cast hd) n i = q from rfl, habs]
  have hnorm : |D.eigenvalue n ω i/s-q/s| ≤
      (1+C)*(N n : ℝ)^(-(2*β)) := by
    calc
      _ ≤ |D.eigenvalue n ω i/s-SpectralConsequences.classicalLocation d hd i| +
          |SpectralConsequences.classicalLocation d hd i-q/s| := abs_sub_le _ _ _
      _ ≤ (N n : ℝ)^(-α)+C*(N n : ℝ)^(-(2/3 : ℝ)) := by
        rw [abs_sub_comm (SpectralConsequences.classicalLocation d hd i)]
        exact add_le_add hsource hquant
      _ ≤ (N n : ℝ)^(-(2*β))+C*(N n : ℝ)^(-(2*β)) :=
        add_le_add (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
            (Real.rpow_nonneg (by positivity) _))
      _ = _ := by ring
  calc
    _ ≤ s*((1+C)*(N n : ℝ)^(-(2*β))) := mul_le_mul_of_nonneg_left hnorm hs.le
    _ = (s*(1+C))*(N n : ℝ)^(-(2*β)) := by ring
    _ ≤ (N n : ℝ)^β*(N n : ℝ)^(-(2*β)) :=
      mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hn.le _)
    _ = (N n : ℝ)^(-β) := by rw [← Real.rpow_add hn]; congr 1; ring

/-- Exact coarse HY estimates for the original uniform-graph marginal.
The quantile grid is the bulk project's own Kesten--McKay grid. -/
def provedHYCoarseInput (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n, Measure.map (D.spectralRegularGraph n) P = regularGraphLaw (N n) d)
    (hd : 3 ≤ d) : HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast hd)) := by
  classical
  letI : Nonempty Ω := ProbabilityMeasure.nonempty (⟨P,inferInstance⟩ : ProbabilityMeasure Ω)
  let hex := regularGraphLaw_source_weak_rigidity d hd
  let α := Classical.choose hex
  have hα : 0 < α := (Classical.choose_spec hex).1
  let β := min (α/2) (1/3)
  have hβ : 0 < β := lt_min (by positivity) (by norm_num)
  have hβα : 2*β ≤ α := by have hh := min_le_left (α/2) (1/3 : ℝ); dsimp [β]; linarith
  have hβq : 2*β ≤ 2/3 := by have hh := min_le_right (α/2) (1/3 : ℝ); dsimp [β]; linarith
  have hprob := D.size_tendsto.eventually (Classical.choose_spec hex).2
  have hdeloc := D.size_tendsto.eventually (regularGraphLaw_source_all_eigenvectors d hd)
  have hlarge := D.size_tendsto.eventually (LocalLaw.eventually_const_mul_log_rpow_le
    (Real.sqrt ((d : ℝ)-1)*(1+(12*Real.pi)^(2/3 : ℝ))) 0 β hβ)
  have hN := D.size_tendsto.eventually (Filter.eventually_ge_atTop 1)
  let ht := eventually_atTop.mp (hprob.and (hdeloc.and (hlarge.and hN)))
  let T := Classical.choose ht
  have hT := Classical.choose_spec ht
  let events : PolynomialGoodEvents P N := {
    good := D.sourceCoarseGood hd α
    measurable_good := D.measurableSet_sourceCoarseGood hd α
    exponent := 1/32
    constant := 6
    exponent_pos := by norm_num
    constant_pos := by norm_num
    threshold := T
    failure_bound := by
      intro n hn
      letI : Nonempty (LocalLaw.RegularGraph (N n) d) :=
        ⟨D.localLawGraph n (Classical.choice inferInstance)⟩
      letI : Nonempty (Graph.RegularGraph (N n) d) :=
        ⟨D.spectralRegularGraph n (Classical.choice inferInstance)⟩
      letI : IsProbabilityMeasure (regularGraphLaw (N n) d) := regularGraphLaw_isProbability _ _
      have hp := (hT n hn).1 inferInstance
      have hq := (hT n hn).2.1 inferInstance
      let F : Set (Graph.RegularGraph (N n) d) := {g | ¬(PaperRigid hd α g ∧ PaperAllEigenvectors g)}
      have hF : MeasurableSet F := (Set.to_countable _).measurableSet
      have he : (P (D.sourceCoarseGood hd α n)ᶜ).toReal =
          (regularGraphLaw (N n) d F).toReal := by
        rw [← hUniform n,Measure.map_apply (D.measurable_spectralRegularGraph n) hF]
        rfl
      have hmass : (regularGraphLaw (N n) d F).toReal ≤ 6*(N n : ℝ)^(-(1/32 : ℝ)) := by
        have hset : F = {g | ¬PaperRigid hd α g} ∪ {g | ¬PaperAllEigenvectors g} := by
          ext g
          change ¬(PaperRigid hd α g ∧ PaperAllEigenvectors g) ↔
            (¬PaperRigid hd α g ∨ ¬PaperAllEigenvectors g)
          tauto
        rw [hset]
        have hh := measureReal_union_le (μ := regularGraphLaw (N n) d)
          {g | ¬PaperRigid hd α g} {g | ¬PaperAllEigenvectors g}
        change (regularGraphLaw (N n) d _).toReal ≤
          (regularGraphLaw (N n) d {g | ¬PaperRigid hd α g}).toReal +
            (regularGraphLaw (N n) d {g | ¬PaperAllEigenvectors g}).toReal at hh
        exact hh.trans (by linarith [hp,hq])
      apply (ENNReal.toReal_le_toReal (measure_ne_top P _) ENNReal.ofReal_ne_top).mp
      rw [ENNReal.toReal_ofReal (by positivity),he]
      exact hmass }
  refine {
    events := events
    rigidity_exponent := β
    rigidity_exponent_pos := hβ
    logPower := 151
    rigidity := ?_
    delocalization := ?_ }
  · intro n hn ω hgood i hi
    have hh := hT n hn
    have hc : Real.sqrt ((d : ℝ)-1)*(1+(12*Real.pi)^(2/3 : ℝ)) ≤ (N n : ℝ)^β := by
      simpa only [Real.rpow_zero,mul_one] using hh.2.2.1
    exact D.rigidity_of_localLaw_source hd n ω α β hβα hβq hh.2.2.2 hc hgood.1 i hi
  · intro n hn ω hgood q energy hq heigen v
    exact (D.delocalization_of_localLaw n ω hgood.2 q energy hq heigen v).trans
      (by change Real.log (N n : ℝ)^151 ≤ 6*Real.log (N n : ℝ)^151
          have hlog : 0 ≤ Real.log (N n : ℝ) := Real.log_nonneg (by exact_mod_cast (hT n hn).2.2.2)
          nlinarith [pow_nonneg hlog 151])

end GeneralizedBulk.External.RegularSpectralData
