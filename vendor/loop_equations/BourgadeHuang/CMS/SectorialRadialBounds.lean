import BourgadeHuang.CMS.SectorialRadialSystem

/-! Uniform bounds and continuity of the constructed radial matrices. -/
noncomputable section
open scoped BigOperators Topology
open Set
namespace BourgadeHuang.CMS.SectorialData

def principalRowBound {d : ℕ} (D : SectorialData d) (ω : Point d) (S : Finset (Fin d)) : ℝ :=
  ∑i,‖ω i‖*SquareFreeTerm.rowBound (D.correctionRow S i)

def remainderRowBound {d : ℕ} (D : SectorialData d) (ω : Point d) (S : Finset (Fin d)) : ℝ :=
  S.card+∑i,‖ω i‖*(1+SquareFreeTerm.rowBound (D.correctionRow S i))

theorem principalRowBound_nonneg {d : ℕ} (D : SectorialData d) (ω : Point d)
    (S : Finset (Fin d)) : 0≤D.principalRowBound ω S :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (SquareFreeTerm.rowBound_nonneg _))

theorem remainderRowBound_nonneg {d : ℕ} (D : SectorialData d) (ω : Point d)
    (S : Finset (Fin d)) : 0≤D.remainderRowBound ω S := by
  apply add_nonneg (Nat.cast_nonneg _)
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _)
    (add_nonneg zero_le_one (SquareFreeTerm.rowBound_nonneg _)))

theorem norm_lowCoordinate_le {d : ℕ} (D : SectorialData d) (ω : Point d)
    (S T : Finset (Fin d)) (i : Fin d) {z : Point d} {t : ℝ} (ht : 0<t)
    (hsep : ∀i j,i≠j→t/4≤‖z i-z j‖) :
    ‖D.lowCoordinate ω z t S T i‖≤‖ω i‖*SquareFreeTerm.rowBound (D.correctionRow S i) := by
  unfold lowCoordinate
  split
  · rw [norm_mul,norm_neg]
    exact mul_le_mul_of_nonneg_left (SquareFreeTerm.norm_homogeneousEntry_le _ _ _ ht hsep) (norm_nonneg _)
  · simpa using mul_nonneg (norm_nonneg (ω i)) (SquareFreeTerm.rowBound_nonneg (D.correctionRow S i))

theorem norm_highCoordinate_le {d : ℕ} (D : SectorialData d) (ω : Point d)
    (S T : Finset (Fin d)) (i : Fin d) {z : Point d} {t : ℝ} (ht : 0<t)
    (hsep : ∀i j,i≠j→t/4≤‖z i-z j‖) :
    ‖D.highCoordinate ω z t S T i‖≤‖ω i‖*(1+SquareFreeTerm.rowBound (D.correctionRow S i)) := by
  unfold highCoordinate
  split_ifs
  · rw [norm_mul,norm_neg]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (SquareFreeTerm.norm_homogeneousEntry_le _ _ _ ht hsep).trans (le_add_of_nonneg_left zero_le_one)
  · have h := mul_nonneg (norm_nonneg (ω i)) (SquareFreeTerm.rowBound_nonneg (D.correctionRow S i))
    nlinarith
  · simpa using mul_nonneg (norm_nonneg (ω i))
      (add_nonneg zero_le_one (SquareFreeTerm.rowBound_nonneg (D.correctionRow S i)))

theorem norm_principalRemainder_le {d : ℕ} (D : SectorialData d) (ω : Point d)
    (S T : Finset (Fin d)) {z : Point d} {t : ℝ} (ht : 0<t)
    (hsep : ∀i j,i≠j→t/4≤‖z i-z j‖) :
    ‖D.principalRemainder ω z t S T‖≤D.principalRowBound ω S := by
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum (fun i _ => D.norm_lowCoordinate_le ω S T i ht hsep)

theorem norm_radialRemainder_le {d : ℕ} (D : SectorialData d) (ω : Point d)
    (S T : Finset (Fin d)) {z : Point d} {t : ℝ} (ht : 0<t)
    (hsep : ∀i j,i≠j→t/4≤‖z i-z j‖) :
    ‖D.radialRemainder ω z t S T‖≤D.remainderRowBound ω S := by
  apply (norm_add_le _ _).trans
  apply add_le_add
  · split_ifs <;> simp
  · apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum (fun i _ => D.norm_highCoordinate_le ω S T i ht hsep)

theorem continuous_lowCoordinate_ray {d : ℕ} (D : SectorialData d) (ω : Point d)
    (S T : Finset (Fin d)) (i : Fin d) (σ : Fin d → Sign) {z : Point d} {R : ℝ}
    (hz : z∈OrderedDomain d) :
    Continuous (fun t : Ici R => D.lowCoordinate ω (sectorialRay σ z R t) (t:ℝ) S T i) := by
  unfold lowCoordinate
  split
  · exact continuous_const.mul (SquareFreeTerm.continuous_homogeneousEntry_ray _ _ _ σ hz)
  · exact continuous_const

theorem continuous_highCoordinate_ray {d : ℕ} (D : SectorialData d) (ω : Point d)
    (S T : Finset (Fin d)) (i : Fin d) (σ : Fin d → Sign) {z : Point d} {R : ℝ}
    (hz : z∈OrderedDomain d) :
    Continuous (fun t : Ici R => D.highCoordinate ω (sectorialRay σ z R t) (t:ℝ) S T i) := by
  unfold highCoordinate
  split
  · exact continuous_const.mul (SquareFreeTerm.continuous_homogeneousEntry_ray _ _ _ σ hz)
  · exact continuous_const

theorem continuous_principalRemainder_ray {d : ℕ} (D : SectorialData d) (ω : Point d)
    (S T : Finset (Fin d)) (σ : Fin d → Sign) {z : Point d} {R : ℝ} (hz : z∈OrderedDomain d) :
    Continuous (fun t : Ici R => D.principalRemainder ω (sectorialRay σ z R t) (t:ℝ) S T) := by
  exact continuous_finset_sum _ (fun i _ => D.continuous_lowCoordinate_ray ω S T i σ hz)

theorem continuous_radialRemainder_ray {d : ℕ} (D : SectorialData d) (ω : Point d)
    (S T : Finset (Fin d)) (σ : Fin d → Sign) {z : Point d} {R : ℝ} (hz : z∈OrderedDomain d) :
    Continuous (fun t : Ici R => D.radialRemainder ω (sectorialRay σ z R t) (t:ℝ) S T) := by
  exact continuous_const.add (continuous_finset_sum _ (fun i _ => D.continuous_highCoordinate_ray ω S T i σ hz))

/-- A common bound for all entries, independent of the base point and radius. -/
def matrixBound {d : ℕ} (D : SectorialData d) (ω : Point d) : ℝ :=
  1+∑S : Finset (Fin d),(D.principalRowBound ω S+D.remainderRowBound ω S)

theorem matrixBound_pos {d : ℕ} (D : SectorialData d) (ω : Point d) : 0<D.matrixBound ω := by
  unfold matrixBound
  apply add_pos_of_pos_of_nonneg zero_lt_one
  exact Finset.sum_nonneg (fun S _ => add_nonneg (D.principalRowBound_nonneg ω S) (D.remainderRowBound_nonneg ω S))

theorem principalRowBound_le_matrixBound {d : ℕ} (D : SectorialData d) (ω : Point d)
    (S : Finset (Fin d)) : D.principalRowBound ω S≤D.matrixBound ω := by
  have h := Finset.single_le_sum (s := Finset.univ) (a := S)
    (f := fun S => D.principalRowBound ω S+D.remainderRowBound ω S)
    (fun S _ => add_nonneg (D.principalRowBound_nonneg ω S) (D.remainderRowBound_nonneg ω S)) (Finset.mem_univ _)
  have hp := D.remainderRowBound_nonneg ω S
  exact (le_add_of_nonneg_right hp).trans (h.trans (le_add_of_nonneg_left zero_le_one))

theorem remainderRowBound_le_matrixBound {d : ℕ} (D : SectorialData d) (ω : Point d)
    (S : Finset (Fin d)) : D.remainderRowBound ω S≤D.matrixBound ω := by
  have h := Finset.single_le_sum (s := Finset.univ) (a := S)
    (f := fun S => D.principalRowBound ω S+D.remainderRowBound ω S)
    (fun S _ => add_nonneg (D.principalRowBound_nonneg ω S) (D.remainderRowBound_nonneg ω S)) (Finset.mem_univ _)
  have hp := D.principalRowBound_nonneg ω S
  exact (le_add_of_nonneg_left hp).trans (h.trans (le_add_of_nonneg_left zero_le_one))

end BourgadeHuang.CMS.SectorialData
