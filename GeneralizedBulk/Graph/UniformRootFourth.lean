import GeneralizedBulk.Graph.EigenfamilySpectralData
import GeneralizedBulk.Graph.UniformEnsemble
import GeneralizedBulk.Graph.BulkFourthMoment
import GeneralizedBulk.Graph.StarFourthNorm
import GeneralizedBulk.Graph.BulkProofParameters
import GeneralizedBulk.BS.SpectralAdapter
import GeneralizedBulk.LocalLaw.ProvedCoarseInput
import GeneralizedBulk.LocalLaw.ProvedLocalStarInput

/-! Root fourth moments simultaneously for every unit bulk eigenvector.
A bad witness is chosen separately on each finite graph and inserted into
one measurable spectral family. This avoids an exchange of basis choices
and probability limits. -/
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology BigOperators Classical RealInnerProductSpace

namespace GeneralizedBulk.External.RegularSpectralData

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem root_fourth_le_four_of_wick (D : RegularSpectralData d N Ω)
    (n : ℕ) (ω : Ω) (j : Fin (N n))
    (hw : |D.empiricalFourthWickDiscrepancy n ω (fun _ : Fin 1 => j)
      (0,0) (0,0) (0,0) (0,0)| ≤ 1) :
    (N n : ℝ)*∑ v,D.eigenvector n ω j v^4 ≤ 4 := by
  let sel : Fin 1 → Fin (N n) := fun _ => j
  have hs : Function.Injective sel := Function.injective_of_subsingleton _
  let A := GaussianWave.SiblingBulk.selectedEigenData D n ω sel hs
  have hm := A.integral_star_coordinate_fourth (fun _ : Fin 1 => D.eigenvector n ω j) 0 0
  have he := D.star_coordinate_fourth_eq_discrepancy n ω sel (0,0)
  change (∫ x,x (0,0)^4 ∂A.starLaw (fun _ : Fin 1 => D.eigenvector n ω j)) = _ at he
  rw [hm] at he
  have hl := le_abs_self (D.empiricalFourthWickDiscrepancy n ω sel (0,0) (0,0) (0,0) (0,0))
  linarith

end GeneralizedBulk.External.RegularSpectralData

namespace GeneralizedBulk.Graph
open GeneralizedBulk.External GeneralizedBulk.Entropy.ChannelRates CanonicalSpectrum

/-- A graph has a unit eigenvector in K whose normalized empirical root
fourth moment exceeds four. Arbitrary eigenspace rotations are included. -/
def HasBadRootFourth {M d : ℕ} (g : RegularGraph M d) (K : Set ℝ) : Prop :=
  ∃ q : NontrivialUnitGraphEigenvector g,
    q.energy ∈ K ∧ 4 < (M : ℝ)*∑ v,q.vector v^4

private def fourthWitnessSelector (d : ℕ) (N : ℕ → ℕ) (K : Set ℝ)
    (n : ℕ) (g : RegularGraph (N n) d) : Option (NontrivialUnitGraphEigenvector g) :=
  if h : HasBadRootFourth g K then some (Classical.choose h) else none

/-- The fourth bound is uniform over every real unit eigenvector in the
compact bulk. Its exceptional probability tends to zero for the actual
uniform labelled graph law. All HY and BS estimates are constructed. -/
theorem uniform_root_fourth_probability
    (d : ℕ) (hd : 3≤d) (N : ℕ → ℕ) (hN : ∀ n,0<N n)
    (hlim : Tendsto N atTop atTop) [∀ n,Nonempty (RegularGraph (N n) d)]
    (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E∈K,E^2<4*((d : ℝ)-1)) :
    Tendsto (fun n => (regularGraphLaw (N n) d).real {g | HasBadRootFourth g K})
      atTop (𝓝 0) := by
  let selector := fourthWitnessSelector d N K
  let D := eigenfamilySpectralData d N hN hlim selector
  let P := uniformEnsembleLaw d N
  have hu : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d := by
    intro n
    have he : D.spectralRegularGraph n=(fun ω : UniformEnsemble d N => ω n) :=
      funext (eigenfamilySpectralData_graph d N hN hlim selector n)
    rw [he]
    exact uniformEnsembleLaw_map_eval d N n
  let HC := D.provedHYCoarseInput P hu hd
  let c := entropyHeight 2 d HC.rigidity_exponent
  have hc := canonical_entropy_height_bounds d HC.rigidity_exponent HC.rigidity_exponent_pos
  let HL := D.provedHYLocalStarInput P hu hd K c hc.1 (by linarith [hc.2.2.2.2])
  let good := D.commonEntropyGood P 1 HC.events HL.events
  have hbad := D.commonEntropyGood_failure_tendsto_zero hu (by omega : 0<d) 1 HC.events HL.events
  have hfourth := D.HY_common_event_fourth_le_one hd HC 1 (by norm_num) K hK hbulk c
    hc.2.1 hc.2.2.2.1 hc.2.2.2.2 HL
  have hineq : ∀ᶠ n in atTop,
      (regularGraphLaw (N n) d).real {g | HasBadRootFourth g K} ≤ P.real (good n)ᶜ := by
    filter_upwards [hfourth] with n hn
    have hs : {ω : UniformEnsemble d N | HasBadRootFourth (ω n) K} ⊆ (good n)ᶜ := by
      intro ω hω hgood
      change HasBadRootFourth (ω n) K at hω
      let q := Classical.choose hω
      have hq : q.energy∈K ∧ 4<(N n : ℝ)*∑ v,q.vector v^4 := Classical.choose_spec hω
      have hsel : selector n (ω n)=some q := by
        change (if h : HasBadRootFourth (ω n) K then some (Classical.choose h) else none)=some q
        rw [dif_pos hω]
      obtain ⟨j,hj,hvec⟩ := eigenfamilySpectralData_contains d N hN hlim selector n ω q hsel
      have hwick := hn ω hgood (fun _ : Fin 1 => j) (Function.injective_of_subsingleton _)
        (fun _ => hj ▸ hq.1) (0,0) (0,0) (0,0) (0,0)
      have hb := D.root_fourth_le_four_of_wick n ω j hwick
      rw [hvec] at hb
      exact (not_lt_of_ge hb) hq.2
    have he : P.real {ω : UniformEnsemble d N | HasBadRootFourth (ω n) K} =
        (regularGraphLaw (N n) d).real {g | HasBadRootFourth g K} := by
      rw [←uniformEnsembleLaw_map_eval d N n]
      change (P {ω : UniformEnsemble d N | HasBadRootFourth (ω n) K}).toReal =
        ((Measure.map (fun ω : UniformEnsemble d N => ω n) (uniformEnsembleLaw d N))
          {g | HasBadRootFourth g K}).toReal
      rw [Measure.map_apply (measurable_pi_apply n) (Set.to_countable _).measurableSet]
      rfl
    rw [←he]
    exact measureReal_mono hs
  exact squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) hineq hbad

end GeneralizedBulk.Graph
