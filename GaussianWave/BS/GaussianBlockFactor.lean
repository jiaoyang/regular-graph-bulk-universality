import GaussianWave.BS.GaussianRadialApproximation
import GaussianWave.BS.TreeHomogeneity

/-! The constructed radial Gaussian samplers are genuine finite-radius
local rules, and their actual process laws are invariant under every tree
isomorphism. Their finite-window approximation to any identified Gaussian
wave is derived from the proved covariance convergence. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.BS

/-- The literal local rule only reads labels inside radius `k+1`. -/
theorem radialGaussianBlockSample_local (d : ℕ) (x : ℝ) (k : ℕ) (u : RegularTreeVertex d)
    (ξ η : RegularTreeVertex d → ℝ)
    (h : ∀ z, (regularWordTree d).dist z u≤k+1 → ξ z=η z) :
    finiteSupportGaussianSample (radialGaussianBlockCoefficient d x k) ξ u =
      finiteSupportGaussianSample (radialGaussianBlockCoefficient d x k) η u := by
  unfold finiteSupportGaussianSample Finsupp.sum
  apply Finset.sum_congr rfl
  intro z hz
  have hdist : (regularWordTree d).dist z u≤k+1 := by
    by_contra hdist
    have hne := Finsupp.mem_support_iff.1 hz
    simp [radialGaussianBlockCoefficient,Finsupp.smul_apply,
      regularTreeRadialFinsupp_apply,hdist] at hne
  dsimp only
  rw [h z hdist]

/-- The actual deterministic radius-local rule commutes with every tree
isomorphism, before taking the independent Gaussian label law. -/
theorem radialGaussianBlockSample_equivariant (d : ℕ) (x : ℝ) (k : ℕ)
    (e : regularWordTree d ≃g regularWordTree d) (ξ : RegularTreeVertex d → ℝ)
    (u : RegularTreeVertex d) :
    finiteSupportGaussianSample (radialGaussianBlockCoefficient d x k) ξ (e u) =
      finiteSupportGaussianSample (radialGaussianBlockCoefficient d x k) (fun v => ξ (e v)) u := by
  have hc : Finsupp.mapDomain e (radialGaussianBlockCoefficient d x k u)=
      radialGaussianBlockCoefficient d x k (e u) := by
    ext v
    obtain ⟨w,rfl⟩ := e.surjective v
    rw [Finsupp.mapDomain_apply e.injective]
    simp only [radialGaussianBlockCoefficient,Finsupp.smul_apply,
      regularTreeRadialFinsupp_apply,regularTreeIso_dist]
  unfold finiteSupportGaussianSample
  rw [← hc,Finsupp.sum_mapDomain_index (by intro b; simp) (by intro b m n; ring)]

/-- Finite-window convergence to an actual Gaussian reference with the
identified spherical covariance. Gaussianity is a reference-law identity,
not an approximation or process-classification assumption. -/
theorem radialGaussianBlockLaw_finite_weakConverges_to_gaussian
    (d : ℕ) (hd : 3 ≤ d) (x : ℝ) (hx : |x|<1)
    {I : Type*} [Fintype I] [DecidableEq I] (site : I → RegularTreeVertex d)
    (ν : Measure (I → ℝ)) [IsProbabilityMeasure ν]
    (hν : HasGaussianCovariance ν (radialFiniteWaveCovariance d (2*Real.sqrt ((d : ℝ)-1)*x) site)) :
    WeakLawConverges
      (fun k => Measure.map (fun z : RegularTreeVertex d → ℝ => fun i => z (site i))
        (radialGaussianBlockLaw d x k)) ν := by
  have he : ν=radialFiniteWaveLaw d hd x hx site :=
    eq_gaussianCovarianceLaw ν _ (radialFiniteWaveCovariance_posSemidef d hd x hx site) hν
  rw [he]
  exact radialGaussianBlockLaw_finite_weakConverges d hd x hx site

/-- The actual Gaussian block-factor law is invariant under every actual
tree isomorphism, established from its computed finite Gaussian laws. -/
theorem radialGaussianBlockLaw_invariant (d : ℕ) (hd : 2 ≤ d) (x : ℝ) (k : ℕ)
    (e : regularWordTree d ≃g regularWordTree d) :
    Measure.map (fun z : RegularTreeVertex d → ℝ => fun v => z (e v))
      (radialGaussianBlockLaw d x k)=radialGaussianBlockLaw d x k := by
  let Q := radialGaussianBlockLaw d x k
  let T := fun z : RegularTreeVertex d → ℝ => fun v => z (e v)
  have hT : Measurable T := measurable_pi_lambda _ (fun v => measurable_pi_apply (e v))
  let P := fun S : Finset (RegularTreeVertex d) => Measure.map S.restrict Q
  letI (S : Finset (RegularTreeVertex d)) : IsProbabilityMeasure (P S) :=
    isProbabilityMeasure_map (Finset.measurable_restrict S).aemeasurable
  have hQ : IsProjectiveLimit Q P := fun _ => rfl
  have hTQ : IsProjectiveLimit (Measure.map T Q) P := by
    intro S
    rw [Measure.map_map (Finset.measurable_restrict S) hT]
    change Measure.map (fun z : RegularTreeVertex d → ℝ => fun i : S => z (e i.val)) Q =
      Measure.map (fun z : RegularTreeVertex d → ℝ => fun i : S => z i.val) Q
    let left := fun z : RegularTreeVertex d → ℝ => fun i : S => z (e i.val)
    let right := fun z : RegularTreeVertex d → ℝ => fun i : S => z i.val
    letI : IsProbabilityMeasure (Measure.map left Q) :=
      isProbabilityMeasure_map (measurable_pi_lambda _ (fun i => measurable_pi_apply (e i.val))).aemeasurable
    letI : IsProbabilityMeasure (Measure.map right Q) :=
      isProbabilityMeasure_map (measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)).aemeasurable
    have hL := radialGaussianBlockLaw_finite_covariance d x k (fun i : S => e i.val)
    have hR := radialGaussianBlockLaw_finite_covariance d x k (fun i : S => i.val)
    have hC : (fun i j : S => radialBlockCovariance d x k (e i.val) (e j.val))=
        (fun i j : S => radialBlockCovariance d x k i.val j.val) := by
      ext i j
      rw [radialBlockCovariance_eq_profile d hd,radialBlockCovariance_eq_profile d hd,
        regularTreeIso_dist]
    rw [hC] at hL
    apply measure_eq_of_linear_characteristic
    intro t
    exact (hL t).trans (hR t).symm
  exact (hQ.unique hTQ).symm

end GaussianWave.BS
