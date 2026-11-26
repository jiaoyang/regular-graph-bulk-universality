import GeneralizedBulk.Graph.ScalarTail

/-!
# Actual finite graph capped scalar moments

The proved physical switching tail recursion is integrated only to a finite
cap. Rejection and the common-event failure remain explicit finite errors.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GeneralizedBulk.Graph
open Analysis Exterior External.RegularSpectralData

/-- The graph/proposal scalar tail is exactly the scalar graph-law tail. -/
theorem graphGoodTail_probability {N d : ℕ} [Nonempty (RegularGraph N d)]
    (hN : 0 < N) (hd : 0 < d) (good : Set (RegularGraph N d)) (z : ℂ) (t : ℝ) :
    (edgePairLaw N d).real (graphGoodTail good z t) =
      (regularGraphLaw N d).real (goodTail good (fun G => graphHeight G z) t) := by
  simp only [measureReal_def]
  rw [← edgePairLaw_graph_marginal hN hd,
    Measure.map_apply (measurable_of_finite _) (Set.toFinite _ |>.measurableSet)]
  rfl

/-- Uniform conditional physical entry variances yield every finite capped
moment of the actual scalar height. The tail law is not assumed. -/
theorem exists_graph_capped_goodExcess_moments
    (d : ℕ) (hd : 0 < d) (E : ℝ) (hE : |E| < d)
    (cstar : ℝ) (hcstar : 0 < cstar) (C : ℝ) (hC : 0 ≤ C) :
    ∃ B step : ℝ, 0 < B ∧ 0 < step ∧
      ∀ (N : ℕ) [Nonempty (RegularGraph N d)], 0 < N →
      ∀ eta : ℝ, 0 < eta → eta ≤ 1 → cstar ≤ (N : ℝ) * eta →
      ∀ good : Set (RegularGraph N d),
      (∀ G ∈ good, ∀ i j,
        (∫ s : {s : EdgePairState N d // edgePairGraph s = G},
          ‖graphDeviation (s : EdgePairState N d) (spectralParameter E eta) i j‖ ^ 2
          ∂finiteUniform {s : EdgePairState N d // edgePairGraph s = G}) ≤
            C * (1 + graphHeight G (spectralParameter E eta))) →
      ∀ m q : ℕ,
      (∫ G, min (goodExcess good (fun G => graphHeight G (spectralParameter E eta)) B G)
        (step * (m : ℝ)) ^ q ∂regularGraphLaw N d) ≤
      step ^ q * (geometricMomentConstant q +
        2 * ((4 + 2 * (d : ℝ)) / N + (regularGraphLaw N d).real goodᶜ) *
          (m : ℝ) * (((m + 1 : ℕ) : ℝ) ^ q)) := by
  obtain ⟨delta,hdelta,_hdeltaup,T0,hT0,hrec⟩ := exists_graph_scalar_tail_recursion d hd E hE cstar hcstar
  let A := 4 / cstar
  let K := 96 * C / delta ^ 2
  let B := max (T0 + A) (max (2 * A) (max (2 * K) 1))
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hBthreshold : T0 + A ≤ B := le_max_left _ _
  have hBshift : 2 * A ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBcontract : 2 * K ≤ B :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨B,A,hBpos,hA,?_⟩
  intro N _ hN eta heta hetaup hheight good hvariance m q
  letI := finiteUniform_isProbability (RegularGraph N d)
  let P := regularGraphLaw N d
  letI : IsProbabilityMeasure P := by
    change IsProbabilityMeasure (finiteUniform (RegularGraph N d))
    infer_instance
  let T := fun G : RegularGraph N d => graphHeight G (spectralParameter E eta)
  let H := goodExcess good T B
  have hgood : MeasurableSet good := Set.toFinite good |>.measurableSet
  have hH : Measurable H := measurable_goodExcess good T B hgood (measurable_of_finite _)
  have hHnonneg (G) : 0 ≤ H G := goodExcess_nonneg good T B G
  apply integral_capped_height_pow_le_of_recursion P H hH hHnonneg A
    ((4 + 2 * (d : ℝ)) / N + P.real goodᶜ) hA (by positivity) m q
  intro k _hk
  rw [goodExcess_tail_eq good T B _ (by positivity),
    goodExcess_tail_eq good T B _ (by positivity)]
  let t := B + A * ((k + 1 : ℕ) : ℝ)
  have ht : B ≤ t := le_add_of_nonneg_right (mul_nonneg hA.le (Nat.cast_nonneg _))
  have htpos : 0 < t := hBpos.trans_le ht
  have hp := hrec N hN eta heta hetaup hheight good C hC
    (fun G hG _ i j => hvariance G hG i j) t htpos (hBthreshold.trans ht) (hBshift.trans ht)
  rw [graphGoodTail_probability hN hd, graphGoodTail_probability hN hd] at hp
  have hshift : t - A = B + A * (k : ℝ) := by dsimp [t]; push_cast; ring
  rw [hshift] at hp
  have hratio : K / t ≤ 1 / 2 := by
    rw [div_le_iff₀ htpos]
    have hh := hBcontract.trans ht
    calc
      K = (2 * K) / 2 := by ring
      _ ≤ t / 2 := div_le_div_of_nonneg_right hh (by norm_num)
      _ = (1 / 2) * t := by ring
  have hprob : 0 ≤ P.real (goodTail good T (B + A * (k : ℝ))) := measureReal_nonneg
  have hm := mul_le_mul_of_nonneg_right hratio hprob
  change P.real (goodTail good T t) ≤ _ at hp
  change P.real (goodTail good T t) ≤ _
  change P.real (goodTail good T t) ≤ K / t *
    P.real (goodTail good T (B + A * (k : ℝ))) + _ + _ at hp
  nlinarith only [hp,hm]

end GeneralizedBulk.Graph
