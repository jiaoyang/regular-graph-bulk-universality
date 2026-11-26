import GaussianWave.BS.GaussianBallCovariance
import GaussianWave.BS.GaussianRadialProfiles

/-!
# Recursive Gaussian branch coefficients

The independent noise supports of different child branches are kept
explicit.  This permits a direct row-Gram induction, without assuming
radiality or invariance of a Gaussian reference.
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

def branchRowExtension {I N : Type*} {q : ℕ} (a : Fin q)
    (v : ((I ⊕ Fin q) ⊕ N) → ℝ) : (I ⊕ (Fin q ⊕ (Fin q × N))) → ℝ :=
  Sum.elim (fun i => v (Sum.inl (Sum.inl i)))
    (Sum.elim (fun j => v (Sum.inl (Sum.inr j)))
      (fun bj => if bj.1 = a then v (Sum.inr bj.2) else 0))

theorem branchRowExtension_gram_same {I N : Type*} [Fintype I] [Fintype N]
    {q : ℕ} (a : Fin q) (v w : ((I ⊕ Fin q) ⊕ N) → ℝ) :
    (∑ s, branchRowExtension a v s * branchRowExtension a w s) = ∑ s, v s * w s := by
  simp only [Fintype.sum_sum_type, branchRowExtension, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_prod_type]
  have he (b : Fin q) (j : N) :
      (if b = a then v (Sum.inr j) else 0) * (if b = a then w (Sum.inr j) else 0) =
      if b = a then v (Sum.inr j) * w (Sum.inr j) else 0 := by split_ifs <;> simp
  simp_rw [he]
  rw [Finset.sum_comm]
  simp
  ring

theorem branchRowExtension_gram_distinct {I N : Type*} [Fintype I] [Fintype N]
    {q : ℕ} (a b : Fin q) (hab : a ≠ b) (v w : ((I ⊕ Fin q) ⊕ N) → ℝ) :
    (∑ s, branchRowExtension a v s * branchRowExtension b w s) =
      ∑ s : I ⊕ Fin q, v (Sum.inl s) * w (Sum.inl s) := by
  simp only [Fintype.sum_sum_type, branchRowExtension, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_prod_type]
  have he (c : Fin q) (j : N) :
      (if c = a then v (Sum.inr j) else 0) * (if c = b then w (Sum.inr j) else 0) = 0 := by
    split_ifs with ha hb hb <;> simp_all
  simp_rw [he]
  simp

def oldBranchRow {I N : Type*} (v : I → ℝ) : I ⊕ N → ℝ := Sum.elim v (fun _ => 0)

theorem oldBranchRow_gram {I N : Type*} [Fintype I] [Fintype N] (v w : I → ℝ) :
    (∑ s : I ⊕ N, oldBranchRow v s * oldBranchRow w s) = ∑ i, v i * w i := by
  simp [oldBranchRow, Fintype.sum_sum_type]

theorem oldBranchRow_extension_gram {I N : Type*} [Fintype I] [Fintype N]
    {q : ℕ} (r : I → ℝ) (a : Fin q) (v : ((I ⊕ Fin q) ⊕ N) → ℝ) :
    (∑ s, oldBranchRow r s * branchRowExtension a v s) =
      ∑ i, r i * v (Sum.inl (Sum.inl i)) := by
  simp [oldBranchRow, branchRowExtension, Fintype.sum_sum_type]

def branchRowSource {I N : Type*} {q : ℕ} (a : Fin q)
    (z : I ⊕ (Fin q ⊕ (Fin q × N)) → ℝ) : (I ⊕ Fin q) ⊕ N → ℝ :=
  Sum.elim (Sum.elim (fun i => z (Sum.inl i)) (fun j => z (Sum.inr (Sum.inl j))))
    (fun j => z (Sum.inr (Sum.inr (a, j))))

theorem branchRowExtension_linearForm {I N : Type*} [Fintype I] [Fintype N]
    {q : ℕ} (a : Fin q) (v : ((I ⊕ Fin q) ⊕ N) → ℝ)
    (z : I ⊕ (Fin q ⊕ (Fin q × N)) → ℝ) :
    finiteLinearForm (branchRowExtension a v) z = finiteLinearForm v (branchRowSource a z) := by
  simp only [finiteLinearForm, Fintype.sum_sum_type, branchRowExtension, branchRowSource,
    Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp
  ring

theorem oldBranchRow_linearForm {I N : Type*} [Fintype I] [Fintype N]
    (v : I → ℝ) (z : I ⊕ N → ℝ) :
    finiteLinearForm (oldBranchRow v) z = finiteLinearForm v (fun i => z (Sum.inl i)) := by
  simp [finiteLinearForm, oldBranchRow, Fintype.sum_sum_type]

theorem siblingExtensionMatrix_linearForm {I : Type*} [Fintype I]
    (q : ℕ) (energy scale : ℝ) (root parent : I → ℝ) (a : Fin q) (z : I ⊕ Fin q → ℝ) :
    finiteLinearForm (siblingExtensionMatrix q energy scale root parent a) z =
      (energy * finiteLinearForm root (fun i => z (Sum.inl i)) -
        finiteLinearForm parent (fun i => z (Sum.inl i))) / q +
      scale * centeredNoise (fun j => z (Sum.inr j)) a := by
  simp only [finiteLinearForm, Fintype.sum_sum_type, siblingExtensionMatrix,
    Sum.elim_inl, Sum.elim_inr]
  have hm : (∑ i, branchConditionalMean q energy root parent i * z (Sum.inl i)) =
      (energy * ∑ i, root i * z (Sum.inl i) - ∑ i, parent i * z (Sum.inl i)) / q := by
    simp only [branchConditionalMean, div_mul_eq_mul_div, sub_mul, mul_assoc,
      ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hm]
  congr 1
  rw [show (∑ j, (scale * centeredNoiseRow q a j) * z (Sum.inr j)) =
      scale * finiteLinearForm (centeredNoiseRow q a) (fun j => z (Sum.inr j)) by
      simp only [finiteLinearForm, Finset.mul_sum, mul_assoc]]
  rw [centeredNoiseRow_apply]

theorem gaussianBranchBuild_child (m k : ℕ) (energy parent root : ℝ)
    (z : BranchNoise (m + 1) (k + 1) → ℝ) (a : Fin (m + 1))
    (v : BranchVertex (m + 1) k) :
    gaussianBranchBuild m (k + 1) energy parent root z (Sum.inr (a, v)) =
      gaussianBranchBuild m k energy root
        ((energy * root - parent) / (m + 1) +
          Real.sqrt (siblingVariance (m + 2) energy) * centeredNoise (fun j => z (Sum.inl j)) a)
        (fun j => z (Sum.inr (a, j))) v := by
  change branchBuild m k energy root
    (siblingFill m (energy * root - parent)
      (fun i => Real.sqrt (siblingVariance (m + 2) energy) *
        (z (Sum.inl i.succ) - z (Sum.inl 0))) a) _ v = _
  rw [congrFun (siblingFill_noise m (energy * root - parent)
    (Real.sqrt (siblingVariance (m + 2) energy)) (fun j => z (Sum.inl j))) a]
  rfl

def gaussianBranchCoefficient (m : ℕ) (energy : ℝ) : (k : ℕ) →
    {I : Type*} → (I → ℝ) → (I → ℝ) → BranchVertex (m + 1) k →
      (I ⊕ BranchNoise (m + 1) k → ℝ)
  | 0, _, root, _, _ => oldBranchRow root
  | k + 1, _, root, parent, v => Sum.elim (fun _ => oldBranchRow root)
      (fun av => branchRowExtension av.1
        (gaussianBranchCoefficient m energy k
          (siblingExtensionMatrix (m + 1) energy
            (Real.sqrt (siblingVariance (m + 2) energy)) root parent av.1)
          (oldBranchRow root) av.2)) v

theorem gaussianBranchCoefficient_old (m k : ℕ) (energy : ℝ)
    {I : Type*} (root parent : I → ℝ) (v : BranchVertex (m + 1) k) (i : I) :
    gaussianBranchCoefficient m energy k root parent v (Sum.inl i) =
      branchMeanA (m + 1) energy (branchDepth (m + 1) k v) * root i +
        branchMeanB (m + 1) energy (branchDepth (m + 1) k v) * parent i := by
  induction k generalizing I with
  | zero => simp [gaussianBranchCoefficient, oldBranchRow, branchDepth, branchMeanA, branchMeanB]
  | succ k ih =>
      cases v with
      | inl u => simp [gaussianBranchCoefficient, oldBranchRow, branchDepth, branchMeanA, branchMeanB]
      | inr av =>
          change gaussianBranchCoefficient m energy k _ _ av.2 (Sum.inl (Sum.inl i)) = _
          rw [ih]
          simp only [siblingExtensionMatrix, branchConditionalMean, oldBranchRow, branchDepth,
            Sum.elim_inl, Sum.elim_inr, Nat.cast_add, Nat.cast_one]
          rw [(branchMean_succ _ _ _).1, (branchMean_succ _ _ _).2]
          ring

/-- These are the coefficient rows of the actual finite independent-noise
reconstruction, not merely another recursively specified covariance model. -/
theorem gaussianBranchCoefficient_linearForm {I : Type*} [Fintype I]
    (m k : ℕ) (energy : ℝ) (root parent : I → ℝ)
    (v : BranchVertex (m + 1) k) (z : I ⊕ BranchNoise (m + 1) k → ℝ) :
    finiteLinearForm (gaussianBranchCoefficient m energy k root parent v) z =
      gaussianBranchBuild m k energy
        (finiteLinearForm parent (fun i => z (Sum.inl i)))
        (finiteLinearForm root (fun i => z (Sum.inl i))) (fun j => z (Sum.inr j)) v := by
  induction k generalizing I with
  | zero => exact oldBranchRow_linearForm _ _
  | succ k ih =>
      cases v with
      | inl u => exact oldBranchRow_linearForm _ _
      | inr av =>
          change finiteLinearForm (branchRowExtension av.1
            (gaussianBranchCoefficient m energy k _ _ av.2)) z = _
          rw [branchRowExtension_linearForm, ih, oldBranchRow_linearForm,
            siblingExtensionMatrix_linearForm, gaussianBranchBuild_child]
          simp only [branchRowSource, Sum.elim_inl, Sum.elim_inr, Nat.cast_add, Nat.cast_one]

def branchDistance (q : ℕ) : (k : ℕ) → BranchVertex q k → BranchVertex q k → ℕ
  | 0, _, _ => 0
  | k + 1, v, w => Sum.elim
      (fun _ => Sum.elim (fun _ => 0) (fun bv => branchDepth q k bv.2 + 1) w)
      (fun av => Sum.elim (fun _ => branchDepth q k av.2 + 1)
        (fun bv => if av.1 = bv.1 then branchDistance q k av.2 bv.2
          else branchDepth q k av.2 + branchDepth q k bv.2 + 2) w) v

theorem siblingExtensionMatrix_root_dot {I : Type*} [Fintype I]
    (q : ℕ) (energy scale : ℝ) (root parent : I → ℝ) (a : Fin q) :
    (∑ i, oldBranchRow root i * siblingExtensionMatrix q energy scale root parent a i) =
      (energy * ∑ i, root i ^ 2 - ∑ i, root i * parent i) / q := by
  simp only [Fintype.sum_sum_type, oldBranchRow, siblingExtensionMatrix,
    Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero]
  have he (i : I) : root i * branchConditionalMean q energy root parent i =
      (energy * root i ^ 2 - root i * parent i) / q := by
    unfold branchConditionalMean
    ring
  simp_rw [he]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem siblingExtensionMatrix_root_covariance {I : Type*} [Fintype I]
    (m : ℕ) (energy scale : ℝ) (root parent : I → ℝ) (a : Fin (m + 1))
    (hr : (∑ i, root i ^ 2) = 1)
    (hrp : (∑ i, root i * parent i) = energy / (m + 2)) :
    (∑ i, oldBranchRow root i * siblingExtensionMatrix (m + 1) energy scale root parent a i) =
      energy / (m + 2) := by
  rw [siblingExtensionMatrix_root_dot, hr, hrp]
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hq : (m : ℝ) + 1 ≠ 0 := by positivity
  have hd : (m : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hq, hd]
  ring

theorem gaussianBranchCoefficient_root_gram {I : Type*} [Fintype I]
    (m k : ℕ) (energy : ℝ) (root parent : I → ℝ)
    (hr : (∑ i, root i ^ 2) = 1)
    (hrp : (∑ i, root i * parent i) = energy / (m + 2)) (v : BranchVertex (m + 1) k) :
    (∑ s, oldBranchRow root s * gaussianBranchCoefficient m energy k root parent v s) =
      sphericalCovariance (m + 2) energy (branchDepth (m + 1) k v) := by
  simp only [Fintype.sum_sum_type, oldBranchRow, Sum.elim_inl, Sum.elim_inr,
    zero_mul, Finset.sum_const_zero, add_zero]
  simp_rw [gaussianBranchCoefficient_old]
  have he (i : I) : root i *
      (branchMeanA (m + 1) energy (branchDepth (m + 1) k v) * root i +
        branchMeanB (m + 1) energy (branchDepth (m + 1) k v) * parent i) =
      branchMeanA (m + 1) energy (branchDepth (m + 1) k v) * root i ^ 2 +
        branchMeanB (m + 1) energy (branchDepth (m + 1) k v) * (root i * parent i) := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hr, hrp, mul_one]
  have h := branchMean_inside_covariance (m + 2) (by omega) energy (branchDepth (m + 1) k v)
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at h
  rw [show (m : ℝ) + 2 - 1 = (m : ℝ) + 1 by ring] at h
  exact h

theorem sum_two_linear_product {I : Type*} [Fintype I]
    (r s p : I → ℝ) (a b c d : ℝ) :
    (∑ i, (a * r i + b * p i) * (c * s i + d * p i)) =
      a * c * (∑ i, r i * s i) + a * d * (∑ i, r i * p i) +
        b * c * (∑ i, p i * s i) + b * d * (∑ i, p i ^ 2) := by
  calc
    _ = ∑ i, (a * c * (r i * s i) + a * d * (r i * p i) +
        b * c * (p i * s i) + b * d * p i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The reference covariance is computed from the actual independent-noise
coefficient rows at every pair of branch vertices. -/
theorem gaussianBranchCoefficient_gram {I : Type*} [Fintype I]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) (root parent : I → ℝ)
    (hr : (∑ i, root i ^ 2) = 1) (hp : (∑ i, parent i ^ 2) = 1)
    (hrp : (∑ i, root i * parent i) = energy / (m + 2))
    (v w : BranchVertex (m + 1) k) :
    (∑ s, gaussianBranchCoefficient m energy k root parent v s *
      gaussianBranchCoefficient m energy k root parent w s) =
      sphericalCovariance (m + 2) energy (branchDistance (m + 1) k v w) := by
  induction k generalizing I with
  | zero =>
      simpa only [gaussianBranchCoefficient, oldBranchRow_gram, branchDistance,
        sphericalCovariance_zero, pow_two] using hr
  | succ k ih =>
      cases v with
      | inl u =>
          have h := gaussianBranchCoefficient_root_gram m (k + 1) energy root parent hr hrp w
          simpa only [gaussianBranchCoefficient, Sum.elim_inl, branchDepth, branchDistance] using h
      | inr av =>
          cases w with
          | inl u =>
              have h := gaussianBranchCoefficient_root_gram m (k + 1) energy root parent hr hrp (Sum.inr av)
              rw [show (∑ s, gaussianBranchCoefficient m energy (k + 1) root parent (Sum.inr av) s *
                  gaussianBranchCoefficient m energy (k + 1) root parent (Sum.inl u) s) =
                  ∑ s, gaussianBranchCoefficient m energy (k + 1) root parent (Sum.inl u) s *
                    gaussianBranchCoefficient m energy (k + 1) root parent (Sum.inr av) s by
                    apply Finset.sum_congr rfl; intro s _; ring]
              simpa only [gaussianBranchCoefficient, Sum.elim_inl, branchDepth, branchDistance,
                Sum.elim_inr] using h
          | inr bv =>
              let scale := Real.sqrt (siblingVariance (m + 2) energy)
              let R := siblingExtensionMatrix (m + 1) energy scale root parent
              let P : I ⊕ Fin (m + 1) → ℝ := oldBranchRow root
              have hP : (∑ i, P i ^ 2) = 1 := by
                simpa only [P, pow_two, oldBranchRow_gram] using hr
              have hR (a : Fin (m + 1)) : (∑ i, R a i ^ 2) = 1 := by
                simpa only [R, scale, pow_two, if_pos rfl] using
                  siblingExtensionMatrix_wave_gram m energy he root parent hr hp hrp a a
              have hPR (a : Fin (m + 1)) : (∑ i, P i * R a i) = energy / (m + 2) :=
                siblingExtensionMatrix_root_covariance m energy scale root parent a hr hrp
              have hRP (a : Fin (m + 1)) : (∑ i, R a i * P i) = energy / (m + 2) := by
                simpa only [mul_comm] using hPR a
              change (∑ s, branchRowExtension av.1
                  (gaussianBranchCoefficient m energy k (R av.1) P av.2) s *
                branchRowExtension bv.1 (gaussianBranchCoefficient m energy k (R bv.1) P bv.2) s) = _
              by_cases hab : av.1 = bv.1
              · rw [hab, branchRowExtension_gram_same]
                have h := ih (R bv.1) P (hR bv.1) hP (hRP bv.1) av.2 bv.2
                simpa only [branchDistance, Sum.elim_inr, if_pos hab] using h
              · rw [branchRowExtension_gram_distinct _ _ hab]
                simp_rw [gaussianBranchCoefficient_old]
                rw [sum_two_linear_product, hRP, hPR, hP]
                have hRR : (∑ i, R av.1 i * R bv.1 i) = sphericalCovariance (m + 2) energy 2 := by
                  simpa only [R, scale, if_neg hab] using
                    siblingExtensionMatrix_wave_gram m energy he root parent hr hp hrp av.1 bv.1
                rw [hRR]
                have h := branchMean_cross_covariance (m + 2) energy
                  (branchDepth (m + 1) k av.2) (branchDepth (m + 1) k bv.2)
                norm_num only [Nat.cast_add, Nat.cast_ofNat] at h
                rw [show (m : ℝ) + 2 - 1 = (m : ℝ) + 1 by ring] at h
                simpa only [branchDistance, Sum.elim_inr, if_neg hab, mul_one, add_mul, add_assoc] using h

end GaussianWave.BS
