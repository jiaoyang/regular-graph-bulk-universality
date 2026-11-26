import GeneralizedBulk.Graph.EntryObstruction

/-! Uniform large-scalar obstruction with the literal finite graph mean. -/
noncomputable section
open scoped BigOperators Classical
namespace GeneralizedBulk.Graph
open GeneralizedSwitching Exterior External.RegularSpectralData

theorem entryBound_edgeMatrix : EntryBound (edgeMatrix : Mat) 1 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [edgeMatrix]

theorem entryBound_allOnes : EntryBound (Matrix.of (fun _ _ : Fin 4 => (1 : ℂ))) 1 :=
  fun _ _ => by norm_num

theorem meanMatrix_decomposition (g b q : ℂ) :
    meanMatrix g b q = g • (1 : Mat) + b • (edgeMatrix : Mat) +
      q • Matrix.of (fun _ _ : Fin 4 => (1 : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [meanMatrix, edgeMatrix, Matrix.one_apply, Matrix.of_apply, Matrix.smul_apply]

theorem entryBound_meanMatrix (g b q : ℂ) :
    EntryBound (meanMatrix g b q) (‖g‖ + ‖b‖ + ‖q‖) := by
  rw [meanMatrix_decomposition]
  simpa only [mul_one] using
    ((entryBound_one.smul g).add (entryBound_edgeMatrix.smul b)).add (entryBound_allOnes.smul q)

/-- The finite mean changes linearly with the scalar resolvent. The
constant-mode correction depends only on size, degree and spectral point,
so it cancels exactly between the two graphs. -/
theorem finiteMean_sub (N d : ℕ) (z mtilde m : ℂ) :
    finiteMean N d z mtilde - finiteMean N d z m =
      (mtilde - m) • covarianceMatrix (z / (d : ℂ)) := by
  ext i j
  rw [covarianceMatrix_eq]
  fin_cases i <;> fin_cases j <;>
    simp [finiteMean, meanMatrix, Matrix.sub_apply, Matrix.smul_apply, div_eq_mul_inv] <;> ring

/-- The exact finite mean has a uniform linear entry bound on the fixed
vertical strip. This is proved from its coefficients. -/
theorem finiteMean_entryBound (N d : ℕ) (hN : 0 < N) (hd : 0 < d)
    (E eta : ℝ) (hE : |E| < d) (heta : |eta| ≤ 1) (m : ℂ) (hm : 1 ≤ ‖m‖) :
    EntryBound (finiteMean N d (spectralParameter E eta) m)
      ((|E| + 4 + (|E| + 3) * ((d : ℝ) - E)⁻¹) * ‖m‖) := by
  let Z := |E| + 1
  let Q := ((d : ℝ) - E)⁻¹
  have hQ : 0 ≤ Q := inv_nonneg.mpr (sub_nonneg.mpr ((le_abs_self E).trans hE.le))
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hq : ‖constantMode N d (spectralParameter E eta)‖ ≤ Q :=
    constantMode_norm_le N d hN E eta ((le_abs_self E).trans_lt hE)
  have hh : ‖m - constantMode N d (spectralParameter E eta)‖ ≤ ‖m‖ + Q :=
    (norm_sub_le _ _).trans (add_le_add_left hq _)
  have hb : ‖(spectralParameter E eta * (m - constantMode N d (spectralParameter E eta)) +
      1 - (N : ℂ)⁻¹) / (d : ℂ)‖ ≤ Z * (‖m‖ + Q) + 2 := by
    have heq : (spectralParameter E eta * (m - constantMode N d (spectralParameter E eta)) +
        1 - (N : ℂ)⁻¹) / (d : ℂ) =
        (spectralParameter E eta / (d : ℂ)) * (m - constantMode N d (spectralParameter E eta)) +
          ((1 - (N : ℂ)⁻¹) / (d : ℂ)) := by ring
    rw [heq]
    calc
      _ ≤ ‖(spectralParameter E eta / (d : ℂ)) *
          (m - constantMode N d (spectralParameter E eta))‖ +
            ‖(1 - (N : ℂ)⁻¹) / (d : ℂ)‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul (spectral_ratio_norm_le d hd E eta heta) hh
          (norm_nonneg _) hZ) (finite_ratio_norm_le N d hN hd)
  apply (entryBound_meanMatrix _ _ _).mono
  have hcoef : 0 ≤ (Z + 2) * Q + 2 := by positivity
  have hprod := mul_le_mul_of_nonneg_left hm hcoef
  change ‖m - constantMode N d (spectralParameter E eta)‖ +
    ‖(spectralParameter E eta * (m - constantMode N d (spectralParameter E eta)) +
      1 - (N : ℂ)⁻¹) / (d : ℂ)‖ + ‖constantMode N d (spectralParameter E eta)‖ ≤ _
  dsimp [Z] at hb hprod
  nlinarith

/-- A scalar trace shift bounds every entry of the difference of the two
independent proposal means. -/
theorem finiteMean_difference_entryBound (N d : ℕ) (hd : 0 < d)
    (E eta : ℝ) (heta : |eta| ≤ 1) (mtilde m : ℂ) (A : ℝ)
    (hA : ‖mtilde - m‖ ≤ A) :
    EntryBound (finiteMean N d (spectralParameter E eta) mtilde -
      finiteMean N d (spectralParameter E eta) m) (A * (|E| + 2)) := by
  have hcov : EntryBound (covarianceMatrix (spectralParameter E eta / (d : ℂ))) (1 + (|E| + 1)) := by
    dsimp [covarianceMatrix]
    exact (entryBound_one.add (entryBound_edgeMatrix.smul _)).mono (by
      simpa only [mul_one] using add_le_add_left (spectral_ratio_norm_le d hd E eta heta) 1)
  rw [finiteMean_sub]
  exact (hcov.smul (mtilde - m)).mono (by nlinarith [abs_nonneg E])

/-- Uniform constants for the actual finite scalar polynomial and the actual
mean matrices. Its only matrix relation premise is the literal forward and
reverse compression equation; that relation is proved for finite switches
in the following graph adapter. -/
theorem exists_finiteMean_large_scalar_obstruction (d : ℕ) (hd : 0 < d)
    (E : ℝ) (hE : |E| < d) (A : ℝ) (hA : 0 ≤ A) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ N : ℕ, 0 < N → ∀ eta : ℝ, |eta| ≤ 1 → ∀ mtilde m : ℂ, T0 ≤ ‖m‖ →
        ‖mtilde - m‖ ≤ A → ∀ M Mtilde : Mat,
          (1 + M * switchIncrement) * (endpointPermutation * Mtilde * endpointPermutation) = M →
          ¬ (EntryBound (M - finiteMean N d (spectralParameter E eta) m) (delta * ‖m‖) ∧
            EntryBound (Mtilde - finiteMean N d (spectralParameter E eta) mtilde) (delta * ‖mtilde‖)) := by
  obtain ⟨c, hc, U, hU, hpoly⟩ := exists_finitePolynomial_lower_bound d hd E hE
  let K := |E| + 4 + (|E| + 3) * ((d : ℝ) - E)⁻¹
  have hK : 0 ≤ K := by
    have hg : 0 ≤ ((d : ℝ) - E)⁻¹ := inv_nonneg.mpr
      (sub_nonneg.mpr ((le_abs_self E).trans hE.le))
    dsimp [K]
    positivity
  obtain ⟨delta, hdelta, hdeltaup, V, hV, hobstruct⟩ :=
    exists_entrywise_large_scalar_obstruction c K (A * (|E| + 2)) hc hK (by positivity)
  refine ⟨delta, hdelta, hdeltaup, max V (max U A), hV.trans (le_max_left _ _), ?_⟩
  intro N hN eta heta mtilde m hm hshift M Mtilde hmatrix
  have hmV : V ≤ ‖m‖ := (le_max_left _ _).trans hm
  have hmU : U ≤ ‖m‖ := ((le_max_left _ _).trans (le_max_right _ _)).trans hm
  have hmA : A ≤ ‖m‖ := ((le_max_right _ _).trans (le_max_right _ _)).trans hm
  have hm1 : 1 ≤ ‖m‖ := hV.trans hmV
  have htilde : ‖mtilde‖ ≤ 2 * ‖m‖ := by
    have hh := norm_le_norm_add_norm_sub m mtilde
    rw [norm_sub_rev] at hh
    linarith
  apply hobstruct _ _ M Mtilde ‖m‖ ‖mtilde‖ hmV htilde
    (finiteMean_entryBound N d hN hd E eta hE heta m hm1)
    (finiteMean_difference_entryBound N d hd E eta heta mtilde m A hshift) _ hmatrix
  rw [norm_finiteMean_residual_entry]
  exact hpoly N hN eta heta m hmU

end GeneralizedBulk.Graph
