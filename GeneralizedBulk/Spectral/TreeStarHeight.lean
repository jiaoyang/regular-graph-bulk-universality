import GeneralizedBulk.Spectral.TreeCavityBoundary
import GeneralizedBulk.Spectral.TreeDiagonal
import GeneralizedBulk.Spectral.TreeGreenStar

/-! The actual height-dependent regular-tree star Green function and its
quantitative convergence to the computed Gaussian-wave boundary covariance. -/
noncomputable section
namespace GeneralizedBulk.KestenMcKay

def cavityStar (d : ℕ) (g : ℂ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  let m := cavityDiagonal g
  fun j l => Fin.cases (Fin.cases m (fun _ => -(m * g)) l)
    (fun a => Fin.cases (-(m * g)) (fun b => if a = b then m else m * g ^ 2) l) j

def treeGreenStar (d : ℕ) (hd : 3 ≤ (d : ℝ)) (z : ℂ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  cavityStar d (treeCavity d hd z)

theorem cavityStar_boundary (d : ℕ) (hd : 3 ≤ (d : ℝ)) (E : ℝ)
    (hbulk : E ^ 2 < 4 * ((d : ℝ) - 1)) : cavityStar d (cavityBoundary d E) = boundaryStar d E := by
  unfold cavityStar boundaryStar
  rw [cavityDiagonal_boundary d E hd hbulk]

theorem cavityStar_norm_bound (d : ℕ) (g : ℂ) (hg : ‖g‖ ^ 2 ≤ 1 / 2) (j l : Fin (d + 1)) :
    ‖cavityStar d g j l‖ ≤ 2 := by
  have hm := cavityDiagonal_norm_le_two g hg
  have hn := norm_le_one_of_sq_le_half g hg
  have hp : ‖g‖ ^ 2 ≤ 1 := by linarith
  have h1 : ‖cavityDiagonal g * g‖ ≤ 2 := by
    rw [norm_mul]
    exact (mul_le_mul hm hn (norm_nonneg g) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  have h2 : ‖cavityDiagonal g * g ^ 2‖ ≤ 2 := by
    rw [norm_mul, norm_pow]
    exact (mul_le_mul hm hp (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  refine Fin.cases ?_ (fun a => ?_) j <;> refine Fin.cases ?_ (fun b => ?_) l
  · exact hm
  · simpa only [cavityStar, Fin.cases_zero, Fin.cases_succ, norm_neg] using h1
  · simpa only [cavityStar, Fin.cases_zero, Fin.cases_succ, norm_neg] using h1
  · by_cases hab : a = b
    · simpa only [cavityStar, Fin.cases_succ, if_pos hab] using hm
    · simpa only [cavityStar, Fin.cases_succ, if_neg hab] using h2

/-- A uniform Lipschitz bound for every literal star entry on the small-root
region. -/
theorem cavityStar_entry_lipschitz (d : ℕ) (g h : ℂ) (hg : ‖g‖ ^ 2 ≤ 1 / 2)
    (hh : ‖h‖ ^ 2 ≤ 1 / 2) (j l : Fin (d + 1)) :
    ‖cavityStar d g j l - cavityStar d h j l‖ ≤ 12 * ‖g - h‖ := by
  have hm := cavityDiagonal_lipschitz g h hg hh
  have hn := norm_le_one_of_sq_le_half g hg
  have hn' := norm_le_one_of_sq_le_half h hh
  have hmh := cavityDiagonal_norm_le_two h hh
  have hp : ‖g ^ 2 - h ^ 2‖ ≤ 2 * ‖g - h‖ := by
    have he : g ^ 2 - h ^ 2 = (g - h) * (g + h) := by ring
    rw [he, norm_mul]
    have ht := norm_add_le g h
    have hsum : ‖g + h‖ ≤ 2 := by linarith
    exact (mul_le_mul_of_nonneg_left hsum (norm_nonneg _)).trans_eq (by ring)
  have h1 : ‖cavityDiagonal g * g - cavityDiagonal h * h‖ ≤ 10 * ‖g - h‖ := by
    have he : cavityDiagonal g * g - cavityDiagonal h * h =
        (cavityDiagonal g - cavityDiagonal h) * g + cavityDiagonal h * (g - h) := by ring
    rw [he]
    have ht := norm_add_le ((cavityDiagonal g - cavityDiagonal h) * g) (cavityDiagonal h * (g - h))
    simp only [norm_mul] at ht
    have hb1 := mul_le_mul hm hn (norm_nonneg g) (by positivity : 0 ≤ 8 * ‖g - h‖)
    have hb2 := mul_le_mul_of_nonneg_right hmh (norm_nonneg (g - h))
    nlinarith
  have h2 : ‖cavityDiagonal g * g ^ 2 - cavityDiagonal h * h ^ 2‖ ≤ 12 * ‖g - h‖ := by
    have he : cavityDiagonal g * g ^ 2 - cavityDiagonal h * h ^ 2 =
        (cavityDiagonal g - cavityDiagonal h) * g ^ 2 + cavityDiagonal h * (g ^ 2 - h ^ 2) := by ring
    rw [he]
    have ht := norm_add_le ((cavityDiagonal g - cavityDiagonal h) * g ^ 2) (cavityDiagonal h * (g ^ 2 - h ^ 2))
    simp only [norm_mul, norm_pow] at ht
    have hb1 := mul_le_mul hm (by linarith : ‖g‖ ^ 2 ≤ 1) (sq_nonneg _) (by positivity : 0 ≤ 8 * ‖g - h‖)
    have hb2 := mul_le_mul hmh hp (norm_nonneg (g ^ 2 - h ^ 2)) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  refine Fin.cases ?_ (fun a => ?_) j <;> refine Fin.cases ?_ (fun b => ?_) l
  · exact hm.trans (by nlinarith [norm_nonneg (g - h)])
  · simpa only [cavityStar, Fin.cases_zero, Fin.cases_succ, neg_sub_neg, norm_sub_rev] using
      h1.trans (by nlinarith [norm_nonneg (g - h)])
  · simpa only [cavityStar, Fin.cases_zero, Fin.cases_succ, neg_sub_neg, norm_sub_rev] using
      h1.trans (by nlinarith [norm_nonneg (g - h)])
  · by_cases hab : a = b
    · simpa only [cavityStar, Fin.cases_succ, if_pos hab] using hm.trans (by nlinarith [norm_nonneg (g - h)])
    · simpa only [cavityStar, Fin.cases_succ, if_neg hab] using h2

theorem treeGreenStar_norm_bound (d : ℕ) (hd : 3 ≤ (d : ℝ)) (z : ℂ) (hz : 0 < z.im)
    (j l : Fin (d + 1)) : ‖treeGreenStar d hd z j l‖ ≤ 2 :=
  cavityStar_norm_bound d _ (treeCavity_norm_sq_le_half d hd z hz) j l

theorem treeGreenStar_boundary_bound (d : ℕ) (hd : 3 ≤ (d : ℝ)) (E : ℝ)
    (hbulk : E ^ 2 < 4 * ((d : ℝ) - 1)) (z : ℂ) (hz : 0 < z.im) (j l : Fin (d + 1)) :
    ‖treeGreenStar d hd z j l - boundaryStar d E j l‖ ≤
      12 * ‖z - (E : ℂ)‖ / bulkHeightScale d E := by
  rw [← cavityStar_boundary d hd E hbulk]
  exact (cavityStar_entry_lipschitz d _ _ (treeCavity_norm_sq_le_half d hd z hz)
    (cavityBoundary_norm_sq_le_half d E hd hbulk) j l).trans
    (by convert mul_le_mul_of_nonneg_left (treeCavity_boundary_bound d E hd hbulk z hz) (by norm_num : (0 : ℝ) ≤ 12) using 1 <;> ring)

end GeneralizedBulk.KestenMcKay
