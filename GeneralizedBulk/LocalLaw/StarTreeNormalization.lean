import GeneralizedBulk.Spectral.TreeStarHeight
import LocalLaw.ReferenceBounds
import LocalLaw.ZeroDeficitForestReference

/-! Exact equality of the normalized source tree reference and the raw
adjacency tree reference on stars. -/
noncomputable section
open scoped Classical

namespace GeneralizedBulk.LocalLawBridge
open LocalLaw GeneralizedBulk.KestenMcKay

theorem source_cavity_scaled (d : ℕ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) :
    treeCavity d (by exact_mod_cast hd) z =
      semicircleRoot (z / (Real.sqrt ((d : ℝ)-1) : ℂ)) /
        (Real.sqrt ((d : ℝ)-1) : ℂ) := by
  let s : ℝ := Real.sqrt ((d : ℝ)-1)
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hsq : s^2 = (d : ℝ)-1 := Real.sq_sqrt (by linarith)
  have hsqc : (s : ℂ)^2 = (d : ℂ)-1 := by exact_mod_cast hsq
  have hw : 0 < (z/(s : ℂ)).im := by
    simpa only [Complex.div_ofReal_im] using div_pos hz hs
  let m := semicircleRoot (z/(s : ℂ))
  have hm : m^2+(z/(s : ℂ))*m+1=0 := semicircleRoot_equation _
  apply treeCavity_unique d (by exact_mod_cast hd) z hz
  · unfold IsCavityRoot
    push_cast
    change ((d : ℂ)-1)*(m/(s : ℂ))^2+z*(m/(s : ℂ))+1=0
    rw [←hsqc]
    convert hm using 1 <;> field_simp <;> ring
  · have hn : ‖m‖ < 1 := semicircleRoot_norm_lt_one hw
    rw [← Complex.sq_norm, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have he : ((d : ℝ)-1)*(‖m‖/s)^2 = ‖m‖^2 := by
      rw [←hsq]
      field_simp
    rw [he]
    nlinarith [norm_nonneg m]

theorem source_diagonal_scaled (d : ℕ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) :
    (Real.sqrt ((d : ℝ)-1) : ℂ)⁻¹ *
      kestenMcKayTransform d
        (semicircleRoot (z / (Real.sqrt ((d : ℝ)-1) : ℂ)))
        (z / (Real.sqrt ((d : ℝ)-1) : ℂ)) =
      cavityDiagonal (treeCavity d (by exact_mod_cast hd) z) := by
  let s : ℝ := Real.sqrt ((d : ℝ)-1)
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hsq : s^2=(d : ℝ)-1 := Real.sq_sqrt (by linarith)
  have hsqc : (s : ℂ)^2=(d : ℂ)-1 := by exact_mod_cast hsq
  have hk : ((d-1 : ℕ) : ℂ)=(s : ℂ)^2 := by
    rw [hsqc, Nat.cast_sub (by omega : 1≤d), Nat.cast_one]
  have hw : 0 < (z/(s : ℂ)).im := by
    simpa only [Complex.div_ofReal_im] using div_pos hz hs
  rw [kestenMcKayTransform_eq d hd _ _ (semicircleRoot_equation _) hw
    (semicircleRoot_im_pos hw).le, source_cavity_scaled d hd z hz]
  unfold cavityDiagonal
  rw [hk]
  change (s : ℂ)⁻¹ * (_/(1-_^2/(s : ℂ)^2)) = _
  rw [div_pow]
  ring

theorem source_edgeWeight_scaled (d : ℕ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) :
    -semicircleRoot (z / (Real.sqrt ((d : ℝ)-1) : ℂ)) * treeEdgeWeight d =
      -treeCavity d (by exact_mod_cast hd) z := by
  rw [source_cavity_scaled d hd z hz]
  unfold treeEdgeWeight
  simp only [Complex.ofReal_inv, div_eq_mul_inv, neg_mul]

end GeneralizedBulk.LocalLawBridge
