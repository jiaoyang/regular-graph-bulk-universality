import GeneralizedBulk.LocalLaw.EdgeBallGeometry
import GeneralizedBulk.Graph.HYResolventChannel
import GeneralizedBulk.ExternalGeometry

/-! The fixed-radius geometric HY record is constructed on the original
uniform regular-graph ensemble using the proved short-cycle counts and
actual locally bijective word-tree covers. -/
noncomputable section
open MeasureTheory Filter
open scoped Classical BigOperators Topology
namespace GeneralizedBulk.Graph
open GaussianWave.BS GaussianWave.BS.Lower

def geometryBadRoots {N m : ℕ} (G : RegularGraph N (m+2)) (R : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun a => ¬GoodVertexCoverRoot G (R+1) a)

theorem geometryBadRoots_card {N m : ℕ} (G : RegularGraph N (m+2)) (R : ℕ) :
    ((geometryBadRoots G R).card : ℝ) = badVertexCoverRootCount G (R+1) := by
  simp only [geometryBadRoots,Finset.card_filter,Nat.cast_sum,badVertexCoverRootCount]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hg : GoodVertexCoverRoot G (R+1) a <;> simp [hg]

theorem geometryGoodRoot {N m : ℕ} (G : RegularGraph N (m+2)) (R : ℕ) (a : Fin N)
    (ha : a ∉ geometryBadRoots G R) : GoodVertexCoverRoot G (R+1) a := by
  simpa only [geometryBadRoots,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using ha

def geometryFailureConstant (m R : ℕ) : ℝ :=
  |shortCycleMassBound (m+2) (R+2) (2*(R+2))|+1

theorem geometry_failure_bound {N m : ℕ} [Nonempty (RegularGraph N (m+2))]
    (R : ℕ) (hN : 0 < N)
    (hsize : 2*(4*(m+2)+2*(m+2)^2+2*(2*(R+2)+2)) ≤ N*(m+2)) :
    (regularGraphLaw N (m+2)).real
      {G | (N : ℝ)^(1/2 : ℝ) < badVertexCoverRootCount G (R+1)} ≤
      geometryFailureConstant m R*(N : ℝ)^(-(1/2 : ℝ)) := by
  letI := regularGraphLaw_isProbability N (m+2)
  letI : Nonempty (GaussianWave.BS.Reused.Graph.RegularGraph N (m+2)) :=
    ⟨Classical.choice (inferInstance : Nonempty (RegularGraph N (m+2)))⟩
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have heq : (N : ℝ)^(-(1/2 : ℝ))*(N : ℝ) = (N : ℝ)^(1/2 : ℝ) := by
    calc
      _ = (N : ℝ)^(-(1/2 : ℝ))*(N : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
      _ = (N : ℝ)^(-(1/2 : ℝ)+1) := (Real.rpow_add hn _ _).symm
      _ = _ := by congr 1; ring
  have hb := bad_vertex_cover_mass_probability (m := m) (R+1) hN hsize
    ((N : ℝ)^(-(1/2 : ℝ))) (Real.rpow_pos_of_pos hn _)
  rw [heq] at hb
  have hsub : (regularGraphLaw N (m+2)).real
      {G | (N : ℝ)^(1/2 : ℝ) < badVertexCoverRootCount G (R+1)} ≤
      (regularGraphLaw N (m+2)).real
        {G | (N : ℝ)^(1/2 : ℝ) ≤ badVertexCoverRootCount G (R+1)} :=
    measureReal_mono (by
      intro G h
      change (N : ℝ)^(1/2 : ℝ) < badVertexCoverRootCount G (R+1) at h
      exact le_of_lt h)
  apply hsub.trans (hb.trans ?_)
  rw [div_eq_mul_inv,← Real.rpow_neg hn.le]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn.le _)
  exact (le_abs_self _).trans (by dsimp [geometryFailureConstant]; linarith)

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Graph GaussianWave.BS GaussianWave.BS.Lower

variable {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]

def geometryGood (m : ℕ) (D : RegularSpectralData (m+2) N Ω) (R n : ℕ) : Set Ω :=
  {ω | badVertexCoverRootCount (D.spectralRegularGraph n ω) (R+1) ≤ (N n : ℝ)^(1/2 : ℝ)}

theorem measurableSet_geometryGood (m : ℕ) (D : RegularSpectralData (m+2) N Ω) (R n : ℕ) :
    MeasurableSet (geometryGood m D R n) := by
  change MeasurableSet ((D.spectralRegularGraph n) ⁻¹'
    {G | badVertexCoverRootCount G (R+1) ≤ (N n : ℝ)^(1/2 : ℝ)})
  exact (D.measurable_spectralRegularGraph n) (Set.to_countable _).measurableSet

def provedGeometryEvents (m : ℕ) (D : RegularSpectralData (m+2) N Ω)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n, Measure.map (D.spectralRegularGraph n) P = regularGraphLaw (N n) (m+2))
    (R : ℕ) : PolynomialGoodEvents P N := by
  let B := 2*(4*(m+2)+2*(m+2)^2+2*(2*(R+2)+2))
  have hlarge := D.size_tendsto.eventually (eventually_ge_atTop B)
  let T := Classical.choose (eventually_atTop.mp hlarge)
  have hT := Classical.choose_spec (eventually_atTop.mp hlarge)
  let C := geometryFailureConstant m R
  have hC : 0 < C := by dsimp [C,geometryFailureConstant]; positivity
  refine {
    good := geometryGood m D R
    measurable_good := measurableSet_geometryGood m D R
    exponent := 1/2
    constant := C
    exponent_pos := by norm_num
    constant_pos := hC
    threshold := T
    failure_bound := ?_ }
  intro n hn
  letI : Nonempty Ω := ProbabilityMeasure.nonempty (⟨P,inferInstance⟩ : ProbabilityMeasure Ω)
  letI : Nonempty (RegularGraph (N n) (m+2)) := ⟨D.spectralRegularGraph n (Classical.choice inferInstance)⟩
  have hsize : B ≤ N n*(m+2) := (hT n hn).trans
    (Nat.le_mul_of_pos_right (N n) (by omega))
  have hb := geometry_failure_bound (m := m) R (D.size_pos n) hsize
  have hset : MeasurableSet {G : RegularGraph (N n) (m+2) |
      (N n : ℝ)^(1/2 : ℝ) < badVertexCoverRootCount G (R+1)} :=
    (Set.to_countable _).measurableSet
  have he : (P (geometryGood m D R n)ᶜ).toReal =
      (regularGraphLaw (N n) (m+2)).real
        {G | (N n : ℝ)^(1/2 : ℝ) < badVertexCoverRootCount G (R+1)} := by
    rw [← hUniform n,Measure.real,Measure.map_apply (D.measurable_spectralRegularGraph n) hset]
    congr 2
    ext ω
    simp only [geometryGood,Set.mem_compl_iff,Set.mem_setOf_eq,Set.mem_preimage,not_le]
  apply (ENNReal.toReal_le_toReal (measure_ne_top P _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))]
  exact he ▸ hb

/-- Exact fixed-radius HY geometry, with genuine rooted isomorphisms to the
specified finite word tree and a polynomial original-ensemble event. -/
def provedHYGeometryInputSucc (m : ℕ) (D : RegularSpectralData (m+2) N Ω)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n, Measure.map (D.spectralRegularGraph n) P = regularGraphLaw (N n) (m+2)) :
    HYGeometryInput D P where
  events := provedGeometryEvents m D P hUniform
  badRoots R n ω := geometryBadRoots (D.spectralRegularGraph n ω) R
  bad_count R n hn ω hω := by
    rw [geometryBadRoots_card]
    exact hω
  tree R n hn ω hω root hroot := by
    have hg := geometryGoodRoot (D.spectralRegularGraph n ω) R root hroot
    let b := D.neighbor n ω root 0
    have hb : (D.spectralRegularGraph n ω).val.Adj root b := by
      change D.adjacency n ω root b = 1
      exact (D.neighbor_exact n ω root b).mpr ⟨0,rfl⟩
    exact acyclic_ball_of_goodCover (D.spectralRegularGraph n ω) R root b hb hg
  edgeIso R n hn ω hω root hroot j := by
    have hg := geometryGoodRoot (D.spectralRegularGraph n ω) R root hroot
    have hb : (D.spectralRegularGraph n ω).val.Adj root (D.neighbor n ω root j) := by
      change D.adjacency n ω root (D.neighbor n ω root j) = 1
      exact (D.neighbor_exact n ω root _).mpr ⟨j,rfl⟩
    exact rootedEdgeBallIso_of_goodCover (D.spectralRegularGraph n ω) R root _ hb hg

/-- The geometric HY record for every degree at least three. -/
def provedHYGeometryInput {d : ℕ} (D : RegularSpectralData d N Ω)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n, Measure.map (D.spectralRegularGraph n) P = regularGraphLaw (N n) d)
    (hd : 3 ≤ d) : HYGeometryInput D P := by
  cases d with
  | zero => omega
  | succ d =>
    cases d with
    | zero => omega
    | succ m => exact provedHYGeometryInputSucc m D P hUniform

end GeneralizedBulk.External.RegularSpectralData
