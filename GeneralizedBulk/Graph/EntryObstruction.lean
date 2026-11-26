import GeneralizedBulk.Graph.PolynomialLowerBound

/-!
# The inverse-free four-endpoint obstruction

Everything is formulated entrywise. The fixed dimension only contributes
explicit factors of four in multiplication, and the scalar residual is one
literal matrix entry. This formulation feeds the actual entrywise variances.
-/
noncomputable section
open scoped BigOperators Classical
namespace GeneralizedBulk.Graph
open GeneralizedSwitching Exterior

def EntryBound (M : Mat) (b : ℝ) : Prop := ∀ i j, ‖M i j‖ ≤ b

namespace EntryBound
variable {M L : Mat} {a b : ℝ}

theorem nonneg (h : EntryBound M a) : 0 ≤ a := (norm_nonneg (M 0 0)).trans (h 0 0)

theorem mono (h : EntryBound M a) (hab : a ≤ b) : EntryBound M b := fun i j => (h i j).trans hab

theorem neg (h : EntryBound M a) : EntryBound (-M) a := by
  intro i j
  simpa only [Matrix.neg_apply, norm_neg] using h i j

theorem add (hM : EntryBound M a) (hL : EntryBound L b) : EntryBound (M + L) (a + b) := by
  intro i j
  exact (norm_add_le _ _).trans (add_le_add (hM i j) (hL i j))

theorem sub (hM : EntryBound M a) (hL : EntryBound L b) : EntryBound (M - L) (a + b) := by
  simpa only [sub_eq_add_neg] using hM.add hL.neg

theorem mul (hM : EntryBound M a) (hL : EntryBound L b) : EntryBound (M * L) (4 * a * b) := by
  intro i j
  calc
    _ ≤ ∑ k : Fin 4, ‖M i k * L k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin 4, a * b := Finset.sum_le_sum (fun k _ => by
      rw [norm_mul]
      exact mul_le_mul (hM i k) (hL k j) (norm_nonneg _) hM.nonneg)
    _ = _ := by simp; ring

theorem smul (hM : EntryBound M a) (z : ℂ) : EntryBound (z • M) (‖z‖ * a) := by
  intro i j
  simpa only [Matrix.smul_apply, smul_eq_mul, norm_mul] using
    mul_le_mul_of_nonneg_left (hM i j) (norm_nonneg z)

theorem conjugate (hM : EntryBound M a) :
    EntryBound ((endpointPermutation : Mat) * M * endpointPermutation) a := by
  have he : (endpointPermutation : Mat) * M * endpointPermutation = M.submatrix swapPartners swapPartners := by
    simpa only [endpointPermutation_transpose] using endpointPermutation_conjugate_submatrix M
  rw [he]
  exact fun i j => hM _ _

end EntryBound

theorem entryBound_one : EntryBound (1 : Mat) 1 := by
  intro i j
  simp only [Matrix.one_apply]
  split_ifs <;> norm_num

theorem entryBound_switchIncrement : EntryBound (switchIncrement : Mat) 1 := by
  intro i j
  rw [switchIncrement_eq]
  fin_cases i <;> fin_cases j <;> norm_num

/-- If both directions are concentrated, the exact finite switching equation
bounds the common residual by an explicit quadratic error. This is a proved
consequence of the ordered identity, rather than an assumed flow identity. -/
theorem switchingResidual_entry_bound
    (H Htilde M Mtilde : Mat) (T Ttilde delta K B : ℝ)
    (hT : 1 ≤ T) (hTtilde : Ttilde ≤ 2 * T)
    (hdelta : 0 ≤ delta) (hdeltaup : delta ≤ 1)
    (hH : EntryBound H (K * T)) (hK : 0 ≤ K)
    (hdiff : EntryBound (Htilde - H) B)
    (hforward : EntryBound (M - H) (delta * T))
    (hreverse : EntryBound (Mtilde - Htilde) (delta * Ttilde))
    (hshift : (1 + M * switchIncrement) *
      (endpointPermutation * Mtilde * endpointPermutation) = M) :
    ‖switchingResidual H 0 1‖ ≤
      (48 * K + 35) * delta * T ^ 2 + (16 * K + 17) * B * T := by
  let X := M - H
  let Y := (endpointPermutation : Mat) * (Mtilde - H) * endpointPermutation
  have hX : EntryBound X (delta * T) := hforward
  have hY : EntryBound Y (2 * delta * T + B) := by
    have hs : Mtilde - H = (Mtilde - Htilde) + (Htilde - H) := by abel
    dsimp [Y]
    rw [hs]
    exact ((hreverse.add hdiff).mono (by nlinarith)).conjugate
  have hM : H + X = M := by dsimp [X]; abel
  have hMY : endpointPermutation * H * endpointPermutation + Y =
      endpointPermutation * Mtilde * (endpointPermutation : Mat) := by
    dsimp [Y]
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hR : switchingResidual H = X - Y - H * switchIncrement * Y -
      X * switchIncrement * endpointPermutation * H * endpointPermutation - X * switchIncrement * Y := by
    have hs : (1 + (H + X) * switchIncrement) *
        (endpointPermutation * H * endpointPermutation + Y) = H + X := by
      rw [hM, hMY]
      exact hshift
    have hid := switchingResidual_perturbation_identity H X Y hs
    have hexpand : (1 + H * switchIncrement) * Y = Y + H * switchIncrement * Y := by
      rw [Matrix.add_mul, one_mul]
    rw [hexpand] at hid
    apply sub_eq_zero.mp
    calc
      _ = switchingResidual H + (Y + H * switchIncrement * Y) +
        X * switchIncrement * endpointPermutation * H * endpointPermutation +
          X * switchIncrement * Y - X := by abel
      _ = 0 := hid
  have hHY := (hH.mul entryBound_switchIncrement).mul hY
  have hXH := (hX.mul entryBound_switchIncrement).mul hH.conjugate
  have hXY := (hX.mul entryBound_switchIncrement).mul hY
  have hXH' : EntryBound (X * switchIncrement * endpointPermutation * H * endpointPermutation)
      (4 * (4 * (delta * T) * 1) * (K * T)) := by
    simpa only [Matrix.mul_assoc] using hXH
  have hRb := ((((hX.sub hY).sub hHY).sub hXH').sub hXY) 0 1
  rw [← hR] at hRb
  apply hRb.trans
  have hB : 0 ≤ B := hdiff.nonneg
  have hT0 : 0 ≤ T := by linarith
  have hTsq : T ≤ T ^ 2 := by nlinarith
  have hdeltaT := mul_le_mul_of_nonneg_left hTsq hdelta
  have hdeltaSq : delta ^ 2 ≤ delta := by nlinarith
  have hdeltaSqT := mul_le_mul_of_nonneg_right hdeltaSq (sq_nonneg T)
  have hBT : B ≤ B * T := by nlinarith
  have hdeltaBT : delta * B * T ≤ B * T := by nlinarith
  nlinarith

/-- Positive quadratic growth of the common residual prevents simultaneous
concentration in the forward and reverse directions. The constants are
uniform whenever `c,K,B` are uniform. -/
theorem exists_entrywise_large_scalar_obstruction (c K B : ℝ)
    (hc : 0 < c) (hK : 0 ≤ K) (hB : 0 ≤ B) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ (H Htilde M Mtilde : Mat) (T Ttilde : ℝ), T0 ≤ T → Ttilde ≤ 2 * T →
        EntryBound H (K * T) → EntryBound (Htilde - H) B →
        c * T ^ 2 ≤ ‖switchingResidual H 0 1‖ →
        (1 + M * switchIncrement) * (endpointPermutation * Mtilde * endpointPermutation) = M →
        ¬ (EntryBound (M - H) (delta * T) ∧ EntryBound (Mtilde - Htilde) (delta * Ttilde)) := by
  let k := 48 * K + 35
  let L := (16 * K + 17) * B
  let delta := min (1 / 2 : ℝ) (c / (4 * k))
  let T0 := max 1 (4 * L / c)
  have hk : 0 < k := by dsimp [k]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hdelta : 0 < delta := lt_min (by norm_num) (div_pos hc (by positivity))
  have hdeltaup : delta ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hkdelta : k * delta ≤ c / 4 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right (1 / 2 : ℝ) (c / (4 * k))) hk.le
    convert hh using 1 <;> dsimp [delta] <;> field_simp <;> ring
  refine ⟨delta, hdelta, hdeltaup, T0, le_max_left _ _, ?_⟩
  intro H Htilde M Mtilde T Ttilde hT hTtilde hH hdiff hres hshift hcon
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hTpos : 0 < T := by linarith
  have hLT : 4 * L ≤ c * T := by
    have hh := (le_max_right (1 : ℝ) (4 * L / c)).trans hT
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hh
  have hb := switchingResidual_entry_bound H Htilde M Mtilde T Ttilde delta K B
    hT1 hTtilde hdelta.le hdeltaup hH hK hdiff hcon.1 hcon.2 hshift
  change ‖switchingResidual H 0 1‖ ≤ k * delta * T ^ 2 + L * T at hb
  have hfirst := mul_le_mul_of_nonneg_right hkdelta (sq_nonneg T)
  have hsecond := mul_le_mul_of_nonneg_right hLT hTpos.le
  have hlast : L * T ≤ c / 4 * T ^ 2 := by nlinarith only [hsecond]
  have hupper := hb.trans (add_le_add hfirst hlast)
  have hquad : 0 < c * T ^ 2 := mul_pos hc (sq_pos_of_pos hTpos)
  have hbad : c * T ^ 2 < c * T ^ 2 := by
    calc
      _ ≤ ‖switchingResidual H 0 1‖ := hres
      _ ≤ c / 4 * T ^ 2 + c / 4 * T ^ 2 := hupper
      _ < _ := by nlinarith only [hquad]
  exact lt_irrefl _ hbad

end GeneralizedBulk.Graph
