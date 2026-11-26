import GaussianWave.BS.GaussianBranchGram

/-!
# Gaussian covariance on a forest attached to a root star

The generic finite covariance theorem is instantiated below by the actual
physical-star factor.  Child branches use disjoint independent noise blocks.
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

def forestRowExtension {I A N : Type*} [DecidableEq A] (a : A) (v : I ⊕ N → ℝ) :
    I ⊕ (A × N) → ℝ :=
  Sum.elim (fun i => v (Sum.inl i)) (fun bj => if bj.1 = a then v (Sum.inr bj.2) else 0)

theorem forestRowExtension_gram_same {I A N : Type*} [Fintype I] [Fintype A] [Fintype N]
    [DecidableEq A] (a : A) (v w : I ⊕ N → ℝ) :
    (∑ s, forestRowExtension a v s * forestRowExtension a w s) = ∑ s, v s * w s := by
  simp only [Fintype.sum_sum_type, forestRowExtension, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_prod_type]
  have he (b : A) (j : N) :
      (if b = a then v (Sum.inr j) else 0) * (if b = a then w (Sum.inr j) else 0) =
      if b = a then v (Sum.inr j) * w (Sum.inr j) else 0 := by split_ifs <;> simp
  simp_rw [he]
  rw [Finset.sum_comm]
  simp

theorem forestRowExtension_gram_distinct {I A N : Type*} [Fintype I] [Fintype A] [Fintype N]
    [DecidableEq A] (a b : A) (hab : a ≠ b) (v w : I ⊕ N → ℝ) :
    (∑ s, forestRowExtension a v s * forestRowExtension b w s) =
      ∑ i, v (Sum.inl i) * w (Sum.inl i) := by
  simp only [Fintype.sum_sum_type, forestRowExtension, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_prod_type]
  have he (c : A) (j : N) :
      (if c = a then v (Sum.inr j) else 0) * (if c = b then w (Sum.inr j) else 0) = 0 := by
    split_ifs with ha hb hb <;> simp_all
  simp_rw [he]
  simp

theorem oldBranchRow_forest_gram {I A N : Type*} [Fintype I] [Fintype A] [Fintype N]
    [DecidableEq A] (r : I → ℝ) (a : A) (v : I ⊕ N → ℝ) :
    (∑ s, oldBranchRow r s * forestRowExtension a v s) =
      ∑ i, r i * v (Sum.inl i) := by
  simp [oldBranchRow, forestRowExtension, Fintype.sum_sum_type]

theorem forestRowExtension_linearForm {I A N : Type*} [Fintype I] [Fintype A] [Fintype N]
    [DecidableEq A] (a : A) (v : I ⊕ N → ℝ) (z : I ⊕ (A × N) → ℝ) :
    finiteLinearForm (forestRowExtension a v) z =
      finiteLinearForm v (Sum.elim (fun i => z (Sum.inl i)) (fun j => z (Sum.inr (a, j)))) := by
  simp only [finiteLinearForm, Fintype.sum_sum_type, forestRowExtension, Sum.elim_inl,
    Sum.elim_inr, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

def vertexBallDistance (m k : ℕ) : VertexBallVertex (m + 2) k → VertexBallVertex (m + 2) k → ℕ :=
  Sum.elim
    (fun _ => Sum.elim (fun _ => 0) (fun bv => branchDepth (m + 1) k bv.2 + 1))
    (fun av => Sum.elim (fun _ => branchDepth (m + 1) k av.2 + 1)
      (fun bv => if av.1 = bv.1 then branchDistance (m + 1) k av.2 bv.2
        else branchDepth (m + 1) k av.2 + branchDepth (m + 1) k bv.2 + 2))

def vertexForestCoefficient {I : Type*} (m k : ℕ) (energy : ℝ)
    (root : I → ℝ) (leaf : Fin (m + 2) → I → ℝ) :
    VertexBallVertex (m + 2) k → (I ⊕ (Fin (m + 2) × BranchNoise (m + 1) k) → ℝ) :=
  Sum.elim (fun _ => oldBranchRow root) (fun av =>
    forestRowExtension av.1 (gaussianBranchCoefficient m energy k (leaf av.1) root av.2))

theorem vertexForestCoefficient_gram {I : Type*} [Fintype I]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ))
    (root : I → ℝ) (leaf : Fin (m + 2) → I → ℝ)
    (hr : (∑ i, root i ^ 2) = 1)
    (hrl : ∀ a, (∑ i, root i * leaf a i) = energy / (m + 2))
    (hll : ∀ a b, (∑ i, leaf a i * leaf b i) =
      if a = b then 1 else sphericalCovariance (m + 2) energy 2)
    (v w : VertexBallVertex (m + 2) k) :
    (∑ s, vertexForestCoefficient m k energy root leaf v s *
      vertexForestCoefficient m k energy root leaf w s) =
      sphericalCovariance (m + 2) energy (vertexBallDistance m k v w) := by
  have hlr (a : Fin (m + 2)) : (∑ i, leaf a i * root i) = energy / (m + 2) := by
    simpa only [mul_comm] using hrl a
  have hroot (a : Fin (m + 2)) (u : BranchVertex (m + 1) k) :
      (∑ i, root i * gaussianBranchCoefficient m energy k (leaf a) root u (Sum.inl i)) =
        sphericalCovariance (m + 2) energy (branchDepth (m + 1) k u + 1) := by
    simp_rw [gaussianBranchCoefficient_old]
    have heq (i : I) : root i *
        (branchMeanA (m + 1) energy (branchDepth (m + 1) k u) * leaf a i +
          branchMeanB (m + 1) energy (branchDepth (m + 1) k u) * root i) =
        branchMeanA (m + 1) energy (branchDepth (m + 1) k u) * (root i * leaf a i) +
          branchMeanB (m + 1) energy (branchDepth (m + 1) k u) * root i ^ 2 := by ring
    simp_rw [heq]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hrl, hr, mul_one]
    have h := branchMean_root_covariance (m + 2) energy (branchDepth (m + 1) k u)
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at h
    rw [show (m : ℝ) + 2 - 1 = (m : ℝ) + 1 by ring] at h
    exact h
  cases v with
  | inl u =>
      cases w with
      | inl u' => simpa only [vertexForestCoefficient, Sum.elim_inl,
          oldBranchRow_gram, vertexBallDistance, sphericalCovariance_zero, pow_two] using hr
      | inr bv =>
          change (∑ s, oldBranchRow root s * forestRowExtension bv.1 _ s) = _
          rw [oldBranchRow_forest_gram]
          exact hroot bv.1 bv.2
  | inr av =>
      cases w with
      | inl u =>
          change (∑ s, forestRowExtension av.1 _ s * oldBranchRow root s) = _
          rw [show (∑ s, forestRowExtension av.1
              (gaussianBranchCoefficient m energy k (leaf av.1) root av.2) s * oldBranchRow root s) =
              ∑ s, oldBranchRow root s * forestRowExtension av.1
                (gaussianBranchCoefficient m energy k (leaf av.1) root av.2) s by
                apply Finset.sum_congr rfl; intro s _; ring,
            oldBranchRow_forest_gram]
          exact hroot av.1 av.2
      | inr bv =>
          change (∑ s, forestRowExtension av.1 _ s * forestRowExtension bv.1 _ s) = _
          by_cases hab : av.1 = bv.1
          · rw [hab, forestRowExtension_gram_same]
            have h := gaussianBranchCoefficient_gram m k energy he (leaf bv.1) root
              (by simpa only [if_pos rfl, pow_two] using hll bv.1 bv.1) hr
              (hlr bv.1) av.2 bv.2
            simpa only [vertexBallDistance, Sum.elim_inr, if_pos hab] using h
          · rw [forestRowExtension_gram_distinct _ _ hab]
            simp_rw [gaussianBranchCoefficient_old]
            rw [sum_two_linear_product, hll, if_neg hab, hlr, hrl, hr, mul_one]
            have h := branchMean_cross_covariance (m + 2) energy
              (branchDepth (m + 1) k av.2) (branchDepth (m + 1) k bv.2)
            norm_num only [Nat.cast_add, Nat.cast_ofNat] at h
            rw [show (m : ℝ) + 2 - 1 = (m : ℝ) + 1 by ring] at h
            simpa only [vertexBallDistance, Sum.elim_inr, if_neg hab, add_mul, add_assoc] using h

end GaussianWave.BS
