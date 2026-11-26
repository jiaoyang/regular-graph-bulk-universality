import GaussianWave.BS.GaussianBallCovariance

/-!
# The Gaussian construction fills the eigen-solution space

The independent-noise parametrization is surjective onto the explicit
innovation coordinates.  Thus its deterministic range is exactly the
eigenrelation subspace, with the dimensions proved earlier.  In particular,
there are no additional hidden linear constraints in the reference law.
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

def rootStarFromDifferences (d : ℕ) (energy : ℝ) (z : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cases ((∑ a, z a) / (energy - d))
    (fun a => (∑ b, z b) / (energy - d) + z a)

theorem rootStarFromDifferences_mem (d : ℕ) (hd : 0 < d) (energy : ℝ)
    (he : energy ≠ (d : ℝ)) (z : Fin d → ℝ) :
    rootStarFromDifferences d energy z ∈ physicalStarHyperplane d (energy / d) := by
  change (∑ a, ((∑ b, z b) / (energy - d) + z a)) =
    (d : ℝ) * (energy / d) * ((∑ a, z a) / (energy - d))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have heR : energy - (d : ℝ) ≠ 0 := sub_ne_zero.mpr he
  field_simp [hdR, heR]
  ring

theorem abs_energy_ratio_lt_one (d : ℕ) (hd : 0 < d) (energy : ℝ)
    (he : |energy| < (d : ℝ)) : |energy / d| < 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [abs_div, abs_of_pos hdR]
  exact (div_lt_one hdR).mpr he

theorem vertexGaussianInnovation_surjective (m k : ℕ) (energy : ℝ)
    (he : |energy| < ((m + 2 : ℕ) : ℝ)) :
    Function.Surjective (vertexGaussianInnovationLinear m k energy) := by
  intro z
  have hd : 2 ≤ m + 2 := by omega
  have hd0 : 0 < m + 2 := by omega
  have hc := abs_energy_ratio_lt_one (m + 2) hd0 energy he
  have hc' : |energy / (m + 2 : ℝ)| < 1 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hc
  have hne : energy ≠ ((m + 2 : ℕ) : ℝ) := ne_of_lt ((le_abs_self energy).trans_lt he)
  let rootStar := rootStarFromDifferences (m + 2) energy (fun a => z (Sum.inl a))
  let rootWhite := physicalStarInverse (m + 2) (energy / (m + 2)) rootStar
  have hmem : rootStar ∈ physicalStarHyperplane (m + 2) (energy / (m + 2 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      rootStarFromDifferences_mem (m + 2) hd0 energy hne (fun a => z (Sum.inl a))
  have hphys : physicalStarMap (m + 2) (energy / (m + 2)) rootWhite = rootStar :=
    physicalStarInverse_right_inverse (m + 2) hd _ hc' _ hmem
  let scale := Real.sqrt (siblingVariance (m + 2) energy)
  have hs : scale ≠ 0 := (Real.sqrt_pos.mpr (siblingVariance_pos (m + 2) hd energy he)).ne'
  let noise : VertexGaussianInput m k → ℝ := Sum.elim rootWhite (fun aj =>
    branchNoiseRightInverse m k scale (fun j => z (Sum.inr (aj.1, j))) aj.2)
  refine ⟨noise, ?_⟩
  ext j
  cases j with
  | inl a =>
      change physicalStarMap (m + 2) (energy / (m + 2)) rootWhite a.succ -
        physicalStarMap (m + 2) (energy / (m + 2)) rootWhite 0 = z (Sum.inl a)
      rw [congrFun hphys a.succ, congrFun hphys 0]
      simp only [rootStar, rootStarFromDifferences, Fin.cases_succ, Fin.cases_zero]
      ring
  | inr aj =>
      exact congrFun (branchNoiseInnovation_rightInverse m k scale hs
        (fun j => z (Sum.inr (aj.1, j)))) aj.2

theorem edgeGaussianInnovation_surjective (m k : ℕ) (energy : ℝ)
    (he : |energy| < ((m + 2 : ℕ) : ℝ)) :
    Function.Surjective (edgeGaussianInnovationLinear m k energy) := by
  intro z
  have hd : 2 ≤ m + 2 := by omega
  have hc := abs_energy_ratio_lt_one (m + 2) (by omega) energy he
  have hc' : |energy / (m + 2 : ℝ)| < 1 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hc
  have hdet : (physicalEdgeMatrix (energy / (m + 2))).det ≠ 0 := by
    rw [physicalEdgeMatrix_det _ hc']
    exact (rho_pos _ hc').ne'
  have hsurj : Function.Surjective (physicalEdgeMatrix (energy / (m + 2))).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  obtain ⟨rootWhite, hroot⟩ := hsurj (fun b => z (Sum.inl b))
  let scale := Real.sqrt (siblingVariance (m + 2) energy)
  have hs : scale ≠ 0 := (Real.sqrt_pos.mpr (siblingVariance_pos (m + 2) hd energy he)).ne'
  let noise : EdgeGaussianInput m k → ℝ := Sum.elim rootWhite (fun bj =>
    branchNoiseRightInverse m k scale (fun j => z (Sum.inr (bj.1, j))) bj.2)
  refine ⟨noise, ?_⟩
  ext j
  cases j with
  | inl b => exact congrFun hroot b
  | inr bj =>
      exact congrFun (branchNoiseInnovation_rightInverse m k scale hs
        (fun j => z (Sum.inr (bj.1, j)))) bj.2

theorem vertexGaussianMap_range (m k : ℕ) (energy : ℝ)
    (he : |energy| < ((m + 2 : ℕ) : ℝ)) :
    LinearMap.range (vertexGaussianMap m k energy) = vertexBallEigenSpace m k energy := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨vertexGaussianInnovation m k energy z, rfl⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, hw⟩ := vertexGaussianInnovation_surjective m k energy he z
    refine ⟨w, ?_⟩
    change vertexBallBuild m k energy (vertexGaussianInnovationLinear m k energy w) = x
    rw [hw]
    exact hz

theorem edgeGaussianMap_range (m k : ℕ) (energy : ℝ)
    (he : |energy| < ((m + 2 : ℕ) : ℝ)) :
    LinearMap.range (edgeGaussianMap m k energy) = edgeBallEigenSpace m k energy := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨edgeGaussianInnovation m k energy z, rfl⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, hw⟩ := edgeGaussianInnovation_surjective m k energy he z
    refine ⟨w, ?_⟩
    change edgeBallBuild m k energy (edgeGaussianInnovationLinear m k energy w) = x
    rw [hw]
    exact hz

end GaussianWave.BS
