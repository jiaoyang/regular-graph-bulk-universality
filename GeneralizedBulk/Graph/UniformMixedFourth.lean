import GeneralizedBulk.Graph.TupleSpectralData
import GeneralizedBulk.Graph.UniformFourthRates
import GeneralizedBulk.Graph.GaussianMixedFourth
import GeneralizedBulk.Graph.UniformEnsemble

/-! Polynomial mixed fourth moments uniformly over every orthonormal
eigenfamily on each actual uniform regular graph. Rates are fixed before
bad witnesses are chosen, and Gaussian terms are genuine integrals. -/
noncomputable section
open MeasureTheory Filter Matrix
open scoped Classical BigOperators Topology RealInnerProductSpace
namespace GeneralizedBulk.Graph

def starFourthDifference {d M k : ℕ} (A : GaussianWave.RegularEigenData d M k)
    (hd : 2≤d) (j1 j2 j3 j4 : Fin k × Fin (d+1)) : ℝ :=
  (∫ x,x j1*x j2*x j3*x j4 ∂A.eigenStarLaw) -
    (∫ x,x j1*x j2*x j3*x j4 ∂A.eigenStarGaussian hd)

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem empiricalFourth_eq_starFourthDifference (D : RegularSpectralData d N Ω)
    (n : ℕ) (ω : Ω) {k : ℕ} (f : Fin k → Fin (N n))
    (A : GaussianWave.RegularEigenData d (N n) k) (hd : 2≤d)
    (henergy : ∀ a,D.eigenvalue n ω (f a)=A.eigenvalue a)
    (hvec : ∀ a,D.eigenvector n ω (f a)=A.eigenvector a)
    (hneigh : D.neighbor n ω=A.neighbor)
    (j1 j2 j3 j4 : Fin k × Fin (d+1)) :
    D.empiricalFourthWickDiscrepancy n ω f j1 j2 j3 j4 =
      starFourthDifference A hd j1 j2 j3 j4 := by
  have hs : D.starLaw n ω (fun a => D.eigenvector n ω (f a))=A.eigenStarLaw := by
    rw [show (fun a => D.eigenvector n ω (f a))=A.eigenvector from funext hvec]
    unfold RegularSpectralData.starLaw GaussianWave.RegularEigenData.eigenStarLaw
      GaussianWave.RegularEigenData.starLaw
    rw [hneigh]
  have hcov (i j : Fin k × Fin (d+1)) :
      D.empiricalGaussianCovariance n ω f i j = A.eigenStarCovariance i j := by
    simp only [empiricalGaussianCovariance,GaussianWave.RegularEigenData.eigenStarCovariance,henergy]
    rfl
  unfold starFourthDifference
  rw [A.eigenStarGaussian_mixed_fourth hd,←hs,D.integral_starLaw n ω]
  simp only [empiricalFourthWickDiscrepancy,hcov,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  unfold empiricalStarWeight
  ring

end GeneralizedBulk.External.RegularSpectralData

namespace GeneralizedBulk.Graph
open GeneralizedBulk.External GeneralizedBulk.Entropy.ChannelRates CanonicalSpectrum

def HasBadMixedFourth {M d : ℕ} (g : RegularGraph M d) (hd : 3≤d)
    (k : ℕ) (K : Set ℝ) : Prop :=
  ∃ A : GraphEigenCandidate d M k g, (∀ a,A.val.eigenvalue a∈K) ∧
    ∃ j1 j2 j3 j4 : Fin k × Fin (d+1),
      (M : ℝ)^(-mixedFourthExponent d hd k) <
        |starFourthDifference A.val (by omega) j1 j2 j3 j4|

private theorem bulk_energy_ne_degree (d : ℕ) (E : ℝ)
    (hE : E^2<4*((d : ℝ)-1)) : E≠d := by
  intro he
  rw [he] at hE
  nlinarith [sq_nonneg ((d : ℝ)-2)]

private def mixedWitnessSelector (d : ℕ) (hd : 3≤d) (k : ℕ)
    (N : ℕ → ℕ) (K : Set ℝ) (hbulk : ∀ E∈K,E^2<4*((d : ℝ)-1))
    (n : ℕ) (g : RegularGraph (N n) d) : Option (NontrivialGraphEigenfamily g k) :=
  if h : HasBadMixedFourth g hd k K then
    some ⟨Classical.choose h,fun a => bulk_energy_ne_degree d _
      (hbulk _ ((Classical.choose_spec h).1 a))⟩
  else none

/-- For every fixed channel count, the failure rate and fourth-Wick power
are fixed functions of d and k, independent of the selected eigenfamily,
neighbor enumeration, or admissible size sequence. -/
theorem uniform_graph_mixed_fourth_fixed_k
    (d : ℕ) (hd : 3≤d) (N : ℕ → ℕ) (hN : ∀ n,0<N n)
    (hlim : Tendsto N atTop atTop) [∀ n,Nonempty (RegularGraph (N n) d)]
    (k : ℕ) (hk : 0<k) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E∈K,E^2<4*((d : ℝ)-1)) :
    ∀ᶠ n in atTop,(regularGraphLaw (N n) d).real {g | HasBadMixedFourth g hd k K} ≤
      mixedFourthFailureConstant d*(N n : ℝ)^(-(1/32 : ℝ)) := by
  let selector := mixedWitnessSelector d hd k N K hbulk
  let D := tupleSpectralData d k N hN hlim selector
  let P := uniformEnsembleLaw d N
  have hu : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d := by
    intro n
    have he : D.spectralRegularGraph n=(fun ω : UniformEnsemble d N => ω n) :=
      funext (tupleSpectralData_graph d k N hN hlim selector n)
    rw [he]
    exact uniformEnsembleLaw_map_eval d N n
  let HC := D.provedHYCoarseInput P hu hd
  let c := entropyHeight k d HC.rigidity_exponent
  have hc := entropyHeight_bounds k d HC.rigidity_exponent HC.rigidity_exponent_pos
  let HL := D.provedHYLocalStarInput P hu hd K c hc.1 (by linarith [hc.2.2.2])
  let good := D.commonEntropyGood P k HC.events HL.events
  have hrate : HC.rigidity_exponent=mixedFourthRigidityRate d hd := rfl
  have hlocal : HL.local_exponent=(1/1024 : ℝ) := rfl
  have hExp : bulkEntropyExponent k d HC.rigidity_exponent HL.local_exponent c/36 =
      mixedFourthExponent d hd k := by
    rw [hlocal]
    change bulkEntropyExponent k d HC.rigidity_exponent (1/1024)
      (entropyHeight k d HC.rigidity_exponent)/36 = _
    rw [hrate]
    rfl
  have hfail := D.commonEntropyGood_failure_explicit hu (by omega : 0<d) k HC.events HL.events
    (1/32) (by change (1/32 : ℝ)≤1/32; rfl) (by change (1/32 : ℝ)≤1/32; rfl) (by norm_num)
  have hC : HC.events.constant+HL.events.constant+1=mixedFourthFailureConstant d := by
    change 6+(3+SpectralConsequences.sourceEigenvectorConstant d/Real.sqrt ((d : ℝ)-1))+1 = _
    unfold mixedFourthFailureConstant
    ring
  have hfourth := D.HY_common_event_fourth_moments hd HC k hk K hK hbulk c
    hc.2.1 hc.2.2.1 hc.2.2.2 HL
  filter_upwards [hfail,hfourth] with n hn hfourth
  have hs : {ω : UniformEnsemble d N | HasBadMixedFourth (ω n) hd k K} ⊆ (good n)ᶜ := by
    intro ω hbad hgood
    change HasBadMixedFourth (ω n) hd k K at hbad
    let A := Classical.choose hbad
    have hA := Classical.choose_spec hbad
    let q : NontrivialGraphEigenfamily (ω n) k :=
      ⟨A,fun a => bulk_energy_ne_degree d _ (hbulk _ (hA.1 a))⟩
    have hsel : selector n (ω n)=some q := by
      change (if h : HasBadMixedFourth (ω n) hd k K then
        some ⟨Classical.choose h,fun a => bulk_energy_ne_degree d _
          (hbulk _ ((Classical.choose_spec h).1 a))⟩ else none)=some q
      rw [dif_pos hbad]
    obtain ⟨f,hfi,henergy,hvec,hneighbor⟩ :=
      tupleSpectralData_contains d k N hN hlim selector n ω q hsel
    obtain ⟨j1,j2,j3,j4,hlarge⟩ := hA.2
    have hw := hfourth ω hgood f hfi (fun a => (henergy a) ▸ hA.1 a) j1 j2 j3 j4
    have heq := D.empiricalFourth_eq_starFourthDifference n ω f A.val (by omega)
      henergy hvec hneighbor j1 j2 j3 j4
    rw [heq,neg_div,hExp] at hw
    exact (not_lt_of_ge hw) hlarge
  have he : P.real {ω : UniformEnsemble d N | HasBadMixedFourth (ω n) hd k K} =
      (regularGraphLaw (N n) d).real {g | HasBadMixedFourth g hd k K} := by
    rw [←uniformEnsembleLaw_map_eval d N n]
    change (P {ω : UniformEnsemble d N | HasBadMixedFourth (ω n) hd k K}).toReal =
      ((Measure.map (fun ω : UniformEnsemble d N => ω n) (uniformEnsembleLaw d N))
        {g | HasBadMixedFourth g hd k K}).toReal
    rw [Measure.map_apply (measurable_pi_apply n) (Set.to_countable _).measurableSet]
    rfl
  rw [←he]
  exact (measureReal_mono hs).trans (by simpa only [hC] using hn)

def mixedFourthUniformExponent (d : ℕ) (hd : 3≤d) : ℝ :=
  min (mixedFourthExponent d hd 1)
    (min (mixedFourthExponent d hd 2)
      (min (mixedFourthExponent d hd 3) (mixedFourthExponent d hd 4)))

theorem mixedFourthUniformExponent_pos (d : ℕ) (hd : 3≤d) :
    0 < mixedFourthUniformExponent d hd :=
  lt_min (mixedFourthExponent_pos d hd 1)
    (lt_min (mixedFourthExponent_pos d hd 2)
      (lt_min (mixedFourthExponent_pos d hd 3) (mixedFourthExponent_pos d hd 4)))

theorem mixedFourthUniformExponent_le (d : ℕ) (hd : 3≤d) (i : Fin 4) :
    mixedFourthUniformExponent d hd ≤ mixedFourthExponent d hd (i.val+1) := by
  dsimp only [mixedFourthUniformExponent]
  fin_cases i
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  · exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)

/-- One graph event for all channel counts one through four, all physical
coordinate choices and all orthonormal eigenfamilies, including rotations
within multiple eigenspaces and arbitrary exact neighbor enumerations. -/
def mixedFourthGood (d : ℕ) (hd : 3≤d) (M : ℕ) (K : Set ℝ) : Set (RegularGraph M d) :=
  (⋃ i : Fin 4,{g | HasBadMixedFourth g hd (i.val+1) K})ᶜ

theorem measurableSet_mixedFourthGood (d : ℕ) (hd : 3≤d) (M : ℕ) (K : Set ℝ) :
    MeasurableSet (mixedFourthGood d hd M K) := (Set.to_countable _).measurableSet

theorem mixedFourthGood_moment (d : ℕ) (hd : 3≤d) (M : ℕ) (hM : 0<M)
    (K : Set ℝ) (g : RegularGraph M d) (hg : g∈mixedFourthGood d hd M K)
    (k : ℕ) (hk : 0<k) (hk4 : k≤4) (A : GraphEigenCandidate d M k g)
    (henergy : ∀ a,A.val.eigenvalue a∈K) (j1 j2 j3 j4 : Fin k × Fin (d+1)) :
    |starFourthDifference A.val (by omega) j1 j2 j3 j4| ≤
      (4*mixedFourthFailureConstant d)*(M : ℝ)^(-mixedFourthUniformExponent d hd) := by
  let i : Fin 4 := ⟨k-1,by omega⟩
  have hik : i.val+1=k := by dsimp [i]; omega
  have hnot : ¬HasBadMixedFourth g hd k K := by
    intro hb
    apply hg
    apply Set.mem_iUnion.mpr
    refine ⟨i,?_⟩
    simpa only [hik] using hb
  have hw : |starFourthDifference A.val (by omega) j1 j2 j3 j4| ≤
      (M : ℝ)^(-mixedFourthExponent d hd k) := by
    apply le_of_not_gt
    intro hlarge
    exact hnot ⟨A,henergy,j1,j2,j3,j4,hlarge⟩
  have hrate := mixedFourthUniformExponent_le d hd i
  rw [hik] at hrate
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ)≤M by exact_mod_cast hM) (neg_le_neg hrate)
  have hC : (1 : ℝ)≤4*mixedFourthFailureConstant d := by
    linarith [mixedFourthFailureConstant_ge_ten d hd]
  exact (hw.trans hpow).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC
      (Real.rpow_nonneg (Nat.cast_nonneg M) (-mixedFourthUniformExponent d hd)))

/-- The article's polynomial mixed-fourth theorem, with an explicit single
good graph event and actual empirical/Gaussian integrals. The positive powers
and coefficient are fixed functions of the degree; no eigenfamily, graph,
size-sequence, BS, HY, entropy, covariance or moment estimate is assumed.
The event works simultaneously for 1≤k≤4 and all four coordinate slots,
with repetitions allowed and no eigenvalue-diameter restriction. -/
theorem uniform_graph_mixed_fourth
    (d : ℕ) (hd : 3≤d) (N : ℕ → ℕ) (hN : ∀ n,0<N n)
    (hlim : Tendsto N atTop atTop) [∀ n,Nonempty (RegularGraph (N n) d)]
    (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E∈K,E^2<4*((d : ℝ)-1)) :
    let χ := mixedFourthUniformExponent d hd
    let C := 4*mixedFourthFailureConstant d
    0<χ ∧ 0<C ∧
      (∀ n,MeasurableSet (mixedFourthGood d hd (N n) K)) ∧
      (∀ᶠ n in atTop,1-C*(N n : ℝ)^(-(1/32 : ℝ)) ≤
        (regularGraphLaw (N n) d).real (mixedFourthGood d hd (N n) K)) ∧
      ∀ n,∀ g∈mixedFourthGood d hd (N n) K,∀ k : ℕ,0<k → k≤4 →
        ∀ A : GraphEigenCandidate d (N n) k g,(∀ a,A.val.eigenvalue a∈K) →
        ∀ j1 j2 j3 j4 : Fin k × Fin (d+1),
          |starFourthDifference A.val (by omega) j1 j2 j3 j4| ≤ C*(N n : ℝ)^(-χ) := by
  intro χ C
  have hC : 0<C := by dsimp [C]; linarith [mixedFourthFailureConstant_ge_ten d hd]
  refine ⟨mixedFourthUniformExponent_pos d hd,hC,
    (fun n => measurableSet_mixedFourthGood d hd (N n) K),?_,?_⟩
  · have hall : ∀ᶠ n in atTop,∀ i : Fin 4,
        (regularGraphLaw (N n) d).real {g | HasBadMixedFourth g hd (i.val+1) K} ≤
          mixedFourthFailureConstant d*(N n : ℝ)^(-(1/32 : ℝ)) :=
      eventually_all.mpr (fun i => uniform_graph_mixed_fourth_fixed_k d hd N hN hlim
        (i.val+1) (by omega) K hK hbulk)
    filter_upwards [hall] with n hn
    letI : IsProbabilityMeasure (regularGraphLaw (N n) d) := regularGraphLaw_isProbability _ _
    have hb : (regularGraphLaw (N n) d).real (mixedFourthGood d hd (N n) K)ᶜ ≤
        C*(N n : ℝ)^(-(1/32 : ℝ)) := by
      change (regularGraphLaw (N n) d).real
        ((⋃ i : Fin 4,{g | HasBadMixedFourth g hd (i.val+1) K})ᶜ)ᶜ ≤ _
      rw [compl_compl]
      apply (measureReal_iUnion_fintype_le (fun i : Fin 4 =>
        {g | HasBadMixedFourth g hd (i.val+1) K})).trans
      apply (Finset.sum_le_sum (fun i _ => hn i)).trans_eq
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      dsimp [C]
      ring
    have hsum := measureReal_add_measureReal_compl (μ := regularGraphLaw (N n) d)
      (measurableSet_mixedFourthGood d hd (N n) K)
    rw [measureReal_univ_eq_one] at hsum
    linarith
  · intro n g hg k hk hk4 A henergy j1 j2 j3 j4
    exact mixedFourthGood_moment d hd (N n) (hN n) K g hg k hk hk4 A henergy j1 j2 j3 j4

end GeneralizedBulk.Graph
