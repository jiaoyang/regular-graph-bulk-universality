import GeneralizedBulk.Graph.EmpiricalWhitening
import GeneralizedBulk.Graph.OrientedEdgeSampling
import GeneralizedBulk.Entropy.PhysicalEdgeObservation
import GeneralizedBulk.Entropy.ConstructedReversalAdmissibility

/-! Exact endpoint reversal of the actual empirical edge law. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.Entropy.Mehler
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def empiricalPortReverseEquiv : (Fin (N n) × Fin d) ≃ (Fin (N n) × Fin d) :=
  (D.portDartEquiv n ω).trans ((Function.Involutive.toPerm
    (fun e : (D.simpleGraph n ω).Dart => e.symm)
    (fun e => SimpleGraph.Dart.symm_symm e)).trans (D.portDartEquiv n ω).symm)

theorem portDartEquiv_reverse (s : Fin (N n) × Fin d) :
    D.portDartEquiv n ω (D.empiricalPortReverseEquiv n ω s) = (D.portDartEquiv n ω s).symm := by
  simp [empiricalPortReverseEquiv]

theorem orientedEdgeMark_reverse {k : ℕ} (q : Fin k → Fin (N n) → ℝ) (s : Fin (N n) × Fin d) :
    D.orientedEdgeMark n ω q (D.empiricalPortReverseEquiv n ω s) = swapEdgeValues (D.orientedEdgeMark n ω q s) := by
  have h := D.portDartEquiv_reverse n ω s
  have hfst := congrArg (fun e : (D.simpleGraph n ω).Dart => e.fst) h
  have hsnd := congrArg (fun e : (D.simpleGraph n ω).Dart => e.snd) h
  change (D.empiricalPortReverseEquiv n ω s).1 = D.neighbor n ω s.1 s.2 at hfst
  change D.neighbor n ω (D.empiricalPortReverseEquiv n ω s).1 (D.empiricalPortReverseEquiv n ω s).2 = s.1 at hsnd
  funext aj
  rcases aj with ⟨a, j⟩
  fin_cases j
  · change Real.sqrt (N n) * q a (D.empiricalPortReverseEquiv n ω s).1 =
      Real.sqrt (N n) * q a (D.neighbor n ω s.1 s.2)
    rw [hfst]
  · change Real.sqrt (N n) * q a (D.neighbor n ω (D.empiricalPortReverseEquiv n ω s).1 (D.empiricalPortReverseEquiv n ω s).2) =
      Real.sqrt (N n) * q a s.1
    rw [hsnd]

/-- Endpoint exchange is an exact finite averaging identity, for arbitrary
functions of all selected channels simultaneously. -/
theorem sum_starEdge_swap {k : ℕ} (q : Fin k → Fin (N n) → ℝ) (leaf : Fin d)
    (F : ((Fin k × Fin 2) → ℝ) → ℝ) :
    (∑ s : EmpiricalStarSample d (N n), F (swapEdgeValues (starEdgeRestriction leaf (D.starSample n ω q s)))) =
      ∑ s : EmpiricalStarSample d (N n), F (starEdgeRestriction leaf (D.starSample n ω q s)) := by
  letI : Nonempty (Fin d) := ⟨leaf⟩
  have hrev := Equiv.sum_comp (D.empiricalPortReverseEquiv n ω)
    (fun s => F (D.orientedEdgeMark n ω q s))
  simp_rw [D.orientedEdgeMark_reverse n ω q] at hrev
  simp_rw [D.starEdgeRestriction_sample n ω q]
  simp only [Fintype.sum_prod_type] at hrev ⊢
  have hleft (v : Fin (N n)) := Graph.sum_perm_eval
    (fun j => F (swapEdgeValues (D.orientedEdgeMark n ω q (v, j)))) leaf
  have hright (v : Fin (N n)) := Graph.sum_perm_eval
    (fun j => F (D.orientedEdgeMark n ω q (v, j))) leaf
  simp_rw [hleft, hright]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hrev]

theorem empiricalWhiteStar_edgeValues {k : ℕ} (hd : 2 ≤ d) (selection : Fin k → Fin (N n))
    (hE : ∀ a, |D.eigenvalue n ω (selection a)| < d) (s : EmpiricalStarSample d (N n)) (i : Fin d) :
    coloredEdgeValues d k hd (fun a => D.eigenvalue n ω (selection a) / d) i
      (D.empiricalWhiteStar n ω hd selection s) =
      starEdgeRestriction i (D.starSample n ω (fun a => D.eigenvector n ω (selection a)) s) := by
  funext aj
  rcases aj with ⟨a, j⟩
  fin_cases j
  · have h := D.empiricalWhiteStar_row n ω hd selection hE s (a, 0)
    simpa only [coloredEdgeValues, starEdgeRestriction, Matrix.cons_val_zero,
      coloredPhysicalRow, blockVector_inner, GeneralizedBulk.Gaussian.starRow, Fin.cases_zero,
      edgeRootValue] using h
  · have h := D.empiricalWhiteStar_row n ω hd selection hE s (a, i.succ)
    simpa only [coloredEdgeValues, starEdgeRestriction, Matrix.cons_val_one, Matrix.cons_val_zero,
      coloredPhysicalRow, blockVector_inner, GeneralizedBulk.Gaussian.starRow, Fin.cases_succ,
      edgeLeafValue, GeneralizedBulk.Gaussian.starRho, rho] using h

/-- The genuine finite empirical projected signal satisfies the joint
endpoint reversal identity required by the Gaussian channel construction. -/
theorem empiricalWhiteStar_projected_reversal {k : ℕ} (hd : 2 ≤ d)
    (selection : Fin k → Fin (N n)) (hE : ∀ a, |D.eigenvalue n ω (selection a)| < d)
    (i : Fin d) (F : ColoredStar d k → ℝ) :
    (∑ s, D.empiricalStarWeight n s * F (coloredReversal d k hd
      (fun a => D.eigenvalue n ω (selection a) / d) i
        (coloredEdgeProjection d k hd i (D.empiricalWhiteStar n ω hd selection s)))) =
    ∑ s, D.empiricalStarWeight n s * F (coloredEdgeProjection d k hd i (D.empiricalWhiteStar n ω hd selection s)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hc (a : Fin k) : |D.eigenvalue n ω (selection a) / (d : ℝ)| < 1 := by
    rw [abs_div, abs_of_pos hdpos, div_lt_one hdpos]
    exact hE a
  simp_rw [coloredReversedProjection_decode d k hd _ hc,
    coloredEdgeProjection_decode d k hd _ hc, D.empiricalWhiteStar_edgeValues n ω hd selection hE]
  unfold empiricalStarWeight
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  exact D.sum_starEdge_swap n ω (fun a => D.eigenvector n ω (selection a)) i
    (fun x => F (decodeColoredEdge d k hd (fun a => D.eigenvalue n ω (selection a) / d) i x))

theorem empiricalNormalizedSignal_values {k : ℕ} (hd : 2 ≤ d)
    (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
    (hE : ∀ a, |D.eigenvalue n ω (selection a)| < d) (s : EmpiricalStarSample d (N n)) :
    (D.empiricalNormalizedSignal n ω hd selection hinj hE).signal s =
      scalarCoordinates d k (D.empiricalWhiteStar n ω hd selection s) := by
  funext j
  change @inner ℝ (ColoredStar d k) _ (scalarAdaptedBasis d k j)
    (D.empiricalWhiteStar n ω hd selection s) =
      (scalarAdaptedBasis d k).repr (D.empiricalWhiteStar n ω hd selection s) j
  rw [OrthonormalBasis.repr_apply_apply]

/-- Endpoint reversibility of the actual empirical graph signal discharges
the Gaussian admissibility hypothesis of the entropy-to-fourth-moment theorem. -/
theorem empiricalNormalizedSignal_admissible {k : ℕ} (hd : 2 ≤ d)
    (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
    (hE : ∀ a, |D.eigenvalue n ω (selection a)| < d)
    (a : ℝ) (ha : 0 < 1 - a ^ 2)
    (f : Lp ℝ 2 (GeneralizedBulk.Entropy.Hermite.standardGaussian (ScalarCoordinate d k)))
    (hf : (f : (ScalarCoordinate d k → ℝ) → ℝ) =ᵐ[GeneralizedBulk.Entropy.Hermite.standardGaussian (ScalarCoordinate d k)]
      (fun x => (D.empiricalNormalizedSignal n ω hd selection hinj hE).density a x - 1)) :
    (coloredGaussianFrameSystem d k hd (fun b => D.eigenvalue n ω (selection b) / d)
      (fun b => by
        have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
        rw [abs_div, abs_of_pos hdpos, div_lt_one hdpos]
        exact hE b)).Admissible f := by
  apply constructed_reversal_admissibility d k hd _ _
    (D.empiricalNormalizedSignal n ω hd selection hinj hE)
    (D.empiricalWhiteStar n ω hd selection)
    (D.empiricalNormalizedSignal_values n ω hd selection hinj hE) ?_ a ha f hf
  intro i F
  exact D.empiricalWhiteStar_projected_reversal n ω hd selection hE i F

end GeneralizedBulk.External.RegularSpectralData
