import GaussianWave.BS.GaussianNoiseDeterminant

/-!
# Exceptional root energies after exact descendant separation
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

def vertexRadialGain (m k : ℕ) (energy : ℝ) : ℝ :=
  1 + (m + 2 : ℝ) * ((branchEnergyCoefficients (m + 1) energy k).1 * (energy / (m + 2)) ^ 2 +
    2 * (branchEnergyCoefficients (m + 1) energy k).2.1 * (energy / (m + 2)) +
    (branchEnergyCoefficients (m + 1) energy k).2.2)

def vertexContrastGain (m k : ℕ) (energy : ℝ) : ℝ :=
  siblingVariance (m + 2) energy * (branchEnergyCoefficients (m + 1) energy k).1

def edgeDiagonalGain (m k : ℕ) (energy : ℝ) : ℝ :=
  (branchEnergyCoefficients (m + 1) energy k).1 +
    (branchEnergyCoefficients (m + 1) energy k).2.2 +
    2 * (branchEnergyCoefficients (m + 1) energy k).2.1 * (energy / (m + 2))

def edgeOffDiagonalGain (m k : ℕ) (energy : ℝ) : ℝ :=
  ((branchEnergyCoefficients (m + 1) energy k).1 +
    (branchEnergyCoefficients (m + 1) energy k).2.2) * (energy / (m + 2)) +
    2 * (branchEnergyCoefficients (m + 1) energy k).2.1

theorem sum_boundary_quadratic {A : Type*} [Fintype A] (q energy : ℝ) (k : ℕ)
    (x : A → ℝ) (parent : ℝ) :
    (∑ a, branchMeanEnergy q energy k (x a) parent) =
      (branchEnergyCoefficients q energy k).1 * (∑ a, x a ^ 2) +
        2 * (branchEnergyCoefficients q energy k).2.1 * parent * (∑ a, x a) +
        Fintype.card A * (branchEnergyCoefficients q energy k).2.2 * parent ^ 2 := by
  unfold branchMeanEnergy
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.sum_mul]
  ring

theorem physicalLeafScale_sq (m : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    (rho (energy / (m + 2)) * transverseScale (m + 2)) ^ 2 = siblingVariance (m + 2) energy := by
  have hc : |energy / (m + 2 : ℝ)| < 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < m + 2)]
    exact (div_lt_one (by positivity)).mpr he
  rw [mul_pow, rho_sq _ hc, transverseScale_sq _ (by omega)]
  unfold siblingVariance
  norm_num only [Nat.cast_add, Nat.cast_ofNat]
  rw [show (m : ℝ) + 2 - 1 = (m : ℝ) + 1 by ring]
  have hd : (m : ℝ) + 2 ≠ 0 := by positivity
  have hq : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hd, hq]
  ring

theorem physicalStarMap_leaf_square_sum (m : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (z : Fin (m + 2) → ℝ) :
    (∑ a : Fin (m + 2), physicalStarMap (m + 2) (energy / (m + 2)) z a.succ ^ 2) =
      (m + 2 : ℝ) * (energy / (m + 2)) ^ 2 * starRootForm z ^ 2 +
        siblingVariance (m + 2) energy * ∑ a, starCenteredCoordinate z a ^ 2 := by
  have heq (a : Fin (m + 2)) : physicalStarMap (m + 2) (energy / (m + 2)) z a.succ =
      (energy / (m + 2)) * starRootForm z +
        (rho (energy / (m + 2)) * transverseScale (m + 2)) * centeredNoise z a := by
    rw [physicalStarMap_leaf]
    unfold starCenteredCoordinate centeredNoise
    ring
  simp_rw [heq]
  rw [sum_centered_shift_square (m + 1)]
  rw [physicalLeafScale_sq m energy he]
  change ((m + 1 : ℕ) + 1 : ℝ) * ((energy / (m + 2)) * starRootForm z) ^ 2 + _ = _
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  congr 1
  ring

theorem vertexOrthoGaussianMap_energy (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (z : VertexBallInnovation (m + 2) k → ℝ) :
    (∑ v, vertexOrthoGaussianMap m k energy z v ^ 2) =
      vertexRadialGain m k energy * starRootForm (fun i => z (Sum.inl i)) ^ 2 +
        vertexContrastGain m k energy * ∑ i, starCenteredCoordinate (fun j => z (Sum.inl j)) i ^ 2 +
        ∑ a, branchOrthoNoiseEnergy m energy k (fun j => z (Sum.inr (a, j))) := by
  have hne : energy ≠ (m + 2 : ℝ) := ne_of_lt ((le_abs_self energy).trans_lt he)
  let y := fun i : Fin (m + 2) => z (Sum.inl i)
  let r := starRootForm y
  let l := fun a : Fin (m + 2) => physicalStarMap (m + 2) (energy / (m + 2)) y a.succ
  have hr : vertexOrthoGaussianMap m k energy z (Sum.inl ()) = r := by
    change vertexInnovationRoot m k energy
      (vertexGaussianInnovationLinear m k energy (vertexOrthoInputLift m k z)) = r
    erw [vertexGaussianMap_root_eq_physical m k energy hne (vertexOrthoInputLift m k z)]
    rw [physicalStarMap_root]
    rfl
  have hl (a : Fin (m + 2)) (v : BranchVertex (m + 1) k) :
      vertexOrthoGaussianMap m k energy z (Sum.inr (a, v)) =
        gaussianBranchBuild m k energy r (l a)
          (branchOrthoNoiseLift m k (fun j => z (Sum.inr (a, j)))) v := by
    simpa only [vertexOrthoGaussianMap, LinearMap.comp_apply, vertexOrthoInputLift,
      LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr, physicalStarMap_root,
      r, l, y] using vertexGaussianMap_branch_eq m k energy hne (vertexOrthoInputLift m k z) a v
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, Fintype.sum_prod_type, hr]
  simp_rw [hl]
  have hsumEnergy :
      (∑ a : Fin (m + 2), ∑ v : BranchVertex (m + 1) k,
        gaussianBranchBuild m k energy r (l a)
          (branchOrthoNoiseLift m k (fun j => z (Sum.inr (a, j)))) v ^ 2) =
      ∑ a : Fin (m + 2), (branchMeanEnergy (m + 1) energy k (l a) r +
        branchOrthoNoiseEnergy m energy k (fun j => z (Sum.inr (a, j)))) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [gaussianBranchBuild_energy m k energy he r (l a), branchNoiseEnergy_orthoLift]
  erw [hsumEnergy]
  rw [Finset.sum_add_distrib, sum_boundary_quadratic,
    physicalStarMap_leaf_square_sum m energy he y]
  have hsum : (∑ a, l a) = energy * r := by
    change (∑ a : Fin (m + 2), physicalStarMap (m + 2) (energy / (m + 2)) y a.succ) = energy * starRootForm y
    rw [physicalStarMap_eigenrelation _ (by omega)]
    have hd : ((m + 2 : ℕ) : ℝ) * (energy / (m + 2 : ℝ)) = energy := by
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      field_simp
    rw [hd, physicalStarMap_root]
  rw [hsum]
  unfold vertexRadialGain vertexContrastGain
  norm_num only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat]
  dsimp only [r, y]
  have hd : (m : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hd]
  ring

theorem physicalEdgeMatrix_energy (c : ℝ) (hc : |c| < 1) (z : Bool → ℝ) :
    ((physicalEdgeMatrix c).mulVec z false) ^ 2 + ((physicalEdgeMatrix c).mulVec z true) ^ 2 =
      z false ^ 2 + z true ^ 2 + 2 * c * z false * z true := by
  rw [physicalEdgeMatrix_mulVec_false, physicalEdgeMatrix_mulVec_true]
  calc
    _ = (alpha c ^ 2 + beta c ^ 2) * (z false ^ 2 + z true ^ 2) +
        2 * (2 * alpha c * beta c) * z false * z true := by ring
    _ = _ := by rw [alpha_sq_add_beta_sq c hc, two_alpha_mul_beta c hc]; ring

theorem physicalEdgeMatrix_product (c : ℝ) (hc : |c| < 1) (z : Bool → ℝ) :
    (physicalEdgeMatrix c).mulVec z false * (physicalEdgeMatrix c).mulVec z true =
      c / 2 * (z false ^ 2 + z true ^ 2) + z false * z true := by
  rw [physicalEdgeMatrix_mulVec_false, physicalEdgeMatrix_mulVec_true]
  calc
    _ = (2 * alpha c * beta c) / 2 * (z false ^ 2 + z true ^ 2) +
        (alpha c ^ 2 + beta c ^ 2) * z false * z true := by ring
    _ = _ := by rw [alpha_sq_add_beta_sq c hc, two_alpha_mul_beta c hc]; ring

theorem edge_boundary_energy (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ))
    (z : Bool → ℝ) :
    (∑ b : Bool, branchMeanEnergy (m + 1) energy k
      ((physicalEdgeMatrix (energy / (m + 2))).mulVec z b)
      ((physicalEdgeMatrix (energy / (m + 2))).mulVec z (!b))) =
      edgeDiagonalGain m k energy * (z false ^ 2 + z true ^ 2) +
        2 * edgeOffDiagonalGain m k energy * z false * z true := by
  have hc : |energy / (m + 2 : ℝ)| < 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < m + 2)]
    exact (div_lt_one (by positivity)).mpr he
  let x := (physicalEdgeMatrix (energy / (m + 2))).mulVec z
  have hx : (∑ b : Bool, branchMeanEnergy (m + 1) energy k (x b) (x (!b))) =
      ((branchEnergyCoefficients (m + 1) energy k).1 +
        (branchEnergyCoefficients (m + 1) energy k).2.2) * (x false ^ 2 + x true ^ 2) +
        4 * (branchEnergyCoefficients (m + 1) energy k).2.1 * (x false * x true) := by
    simp only [Fintype.sum_bool, Bool.not_false, Bool.not_true, branchMeanEnergy]
    ring
  rw [hx, physicalEdgeMatrix_energy _ hc, physicalEdgeMatrix_product _ hc]
  unfold edgeDiagonalGain edgeOffDiagonalGain
  ring

theorem edgeOrthoGaussianMap_energy (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (z : EdgeBallInnovation (m + 2) k → ℝ) :
    (∑ v, edgeOrthoGaussianMap m k energy z v ^ 2) =
      edgeDiagonalGain m k energy * (z (Sum.inl false) ^ 2 + z (Sum.inl true) ^ 2) +
        2 * edgeOffDiagonalGain m k energy * z (Sum.inl false) * z (Sum.inl true) +
        ∑ b, branchOrthoNoiseEnergy m energy k (fun j => z (Sum.inr (b, j))) := by
  let x := (physicalEdgeMatrix (energy / (m + 2))).mulVec (fun b => z (Sum.inl b))
  have hl (b : Bool) (v : BranchVertex (m + 1) k) :
      edgeOrthoGaussianMap m k energy z (b, v) =
        gaussianBranchBuild m k energy (x (!b)) (x b)
          (branchOrthoNoiseLift m k (fun j => z (Sum.inr (b, j)))) v := rfl
  rw [Fintype.sum_prod_type]
  simp_rw [hl]
  have hsumEnergy :
      (∑ b : Bool, ∑ v : BranchVertex (m + 1) k,
        gaussianBranchBuild m k energy (x (!b)) (x b)
          (branchOrthoNoiseLift m k (fun j => z (Sum.inr (b, j)))) v ^ 2) =
      ∑ b : Bool, (branchMeanEnergy (m + 1) energy k (x b) (x (!b)) +
        branchOrthoNoiseEnergy m energy k (fun j => z (Sum.inr (b, j)))) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [gaussianBranchBuild_energy m k energy he (x (!b)) (x b), branchNoiseEnergy_orthoLift]
  erw [hsumEnergy]
  rw [Finset.sum_add_distrib, edge_boundary_energy m k energy he]

def edgePlusGain (m k : ℕ) (energy : ℝ) : ℝ :=
  (1 + energy / (m + 2)) * ((branchEnergyCoefficients (m + 1) energy k).1 +
    2 * (branchEnergyCoefficients (m + 1) energy k).2.1 + (branchEnergyCoefficients (m + 1) energy k).2.2)

def edgeMinusGain (m k : ℕ) (energy : ℝ) : ℝ :=
  (1 - energy / (m + 2)) * ((branchEnergyCoefficients (m + 1) energy k).1 -
    2 * (branchEnergyCoefficients (m + 1) energy k).2.1 + (branchEnergyCoefficients (m + 1) energy k).2.2)

theorem edgeDiagonalGain_add_offDiagonalGain (m k : ℕ) (energy : ℝ) :
    edgeDiagonalGain m k energy + edgeOffDiagonalGain m k energy = edgePlusGain m k energy := by
  unfold edgeDiagonalGain edgeOffDiagonalGain edgePlusGain
  ring

theorem edgeDiagonalGain_sub_offDiagonalGain (m k : ℕ) (energy : ℝ) :
    edgeDiagonalGain m k energy - edgeOffDiagonalGain m k energy = edgeMinusGain m k energy := by
  unfold edgeDiagonalGain edgeOffDiagonalGain edgeMinusGain
  ring

end GaussianWave.BS
