import BourgadeHuang.CMS.RayIndependence

/-! Explicit separating phase weights. Binary coding avoids any generic-ray
or noncancellation assumption in the finite sign selection argument. -/
noncomputable section
open scoped BigOperators
namespace BourgadeHuang.CMS

def binarySignCode {d : ℕ} (σ : Fin d → Sign) : ℕ :=
  ∑i,if σ i then 2^i.val else 0

theorem binarySignCode_succ {d : ℕ} (σ : Fin (d+1) → Sign) :
    binarySignCode σ=(if σ 0 then 1 else 0)+2*binarySignCode (fun i : Fin d=>σ i.succ) := by
  rw [binarySignCode,Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,Fin.val_succ,pow_succ,binarySignCode,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> omega

theorem binarySignCode_injective (d : ℕ) :
    Function.Injective (binarySignCode (d:=d)) := by
  induction d with
  | zero => intro σ τ h; funext i; exact Fin.elim0 i
  | succ d ih =>
    intro σ τ h
    rw [binarySignCode_succ,binarySignCode_succ] at h
    have hzero : σ 0=τ 0 := by
      cases hs : σ 0 <;> cases ht : τ 0 <;>
        simp only [hs,ht,Bool.false_eq_true,↓reduceIte] at h ⊢ <;> omega
    have htail : (fun i : Fin d=>σ i.succ)=(fun i : Fin d=>τ i.succ) := by
      apply ih
      rw [hzero] at h
      omega
    funext i
    refine Fin.cases hzero (fun j=>congrFun htail j) i

theorem sum_binary_weights (d : ℕ) :
    (∑i : Fin d,(2:ℝ)^i.val)=(2:ℝ)^d-1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,Fin.val_succ,pow_succ]
    rw [←Finset.sum_mul,ih]
    ring

theorem signed_binary_sum_eq_code {d : ℕ} (σ : Fin d → Sign) :
    (∑i,realSign (σ i)*(2:ℝ)^i.val)=2*(binarySignCode σ:ℝ)-((2:ℝ)^d-1) := by
  rw [←sum_binary_weights d,binarySignCode,Nat.cast_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  cases σ i <;> simp [realSign] <;> ring

/-- All signed binary phase weights are distinct. -/
theorem signed_binary_sum_injective (d : ℕ) :
    Function.Injective (fun σ : Fin d → Sign=>∑i,realSign (σ i)*(2:ℝ)^i.val) := by
  intro σ τ h
  dsimp only at h
  rw [signed_binary_sum_eq_code,signed_binary_sum_eq_code] at h
  apply binarySignCode_injective d
  have hh : (binarySignCode σ:ℝ)=(binarySignCode τ:ℝ) := by linarith
  exact_mod_cast hh

/-- Every later binary weight strictly dominates the sum of all earlier ones. -/
theorem sum_binary_weights_lt_pow {n j : ℕ} (hnj : n≤j) :
    (∑i : Fin n,(2:ℝ)^i.val)<(2:ℝ)^j := by
  rw [sum_binary_weights]
  have hh : (2:ℝ)^n≤(2:ℝ)^j := pow_le_pow_right₀ (by norm_num) hnj
  linarith

end BourgadeHuang.CMS
