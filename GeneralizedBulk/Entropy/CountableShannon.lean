import GeneralizedBulk.Entropy.FiniteHolder

/-! Countable Shannon entropy, with summability proved from a genuine
exponential reference energy and a first energy moment. -/
noncomputable section
open scoped BigOperators

namespace GeneralizedBulk.Entropy

variable {A : Type*}

def countableEntropy (p : A → ℝ) : ℝ := ∑' a,Real.negMulLog (p a)

theorem mass_le_one_of_hasSum (p : A → ℝ) (hp : ∀ a,0 ≤ p a) (hsum : HasSum p 1) (a : A) : p a ≤ 1 := by
  rw [← hsum.tsum_eq]
  exact hsum.summable.le_tsum a (fun b hb => hp b)

/-- The reference-energy estimate is a proved scalar inequality; it is not
an assumed entropy bound. -/
theorem negMulLog_le_energy_exp (p E : ℝ) (hp : 0 ≤ p) :
    Real.negMulLog p ≤ p*E+Real.exp (-E) := by
  let q := Real.exp (-E)
  have hq : 0 < q := Real.exp_pos _
  have hFq : Real.negMulLog q = q*E := by
    dsimp [Real.negMulLog,q]
    rw [Real.log_exp]
    ring
  have hmul : q*(p/q) = p := by field_simp
  have he : Real.negMulLog p = p*E+q*Real.negMulLog (p/q) := by
    calc
      _ = Real.negMulLog (q*(p/q)) := congrArg Real.negMulLog hmul.symm
      _ = (p/q)*Real.negMulLog q+q*Real.negMulLog (p/q) := Real.negMulLog_mul q (p/q)
      _ = _ := by rw [hFq]; field_simp <;> ring
  have h := Finite.negMulLog_le_one_sub (p/q) (div_nonneg hp hq.le)
  have hm := mul_le_mul_of_nonneg_left h hq.le
  have hb : q*(1-p/q) = q-p := by field_simp <;> ring
  rw [hb] at hm
  rw [he]
  dsimp only [q]
  linarith

theorem summable_entropy_of_reference_energy (p E : A → ℝ)
    (hp : ∀ a,0 ≤ p a) (hsum : HasSum p 1)
    (hE : Summable (fun a => p a*E a)) (href : Summable (fun a => Real.exp (-E a))) :
    Summable (fun a => Real.negMulLog (p a)) := by
  apply Summable.of_nonneg_of_le
    (fun a => Real.negMulLog_nonneg (hp a) (mass_le_one_of_hasSum p hp hsum a))
    (fun a => negMulLog_le_energy_exp (p a) (E a) (hp a))
    (hE.add href)

theorem countableEntropy_le_reference_energy (p E : A → ℝ)
    (hp : ∀ a,0 ≤ p a) (hsum : HasSum p 1)
    (hE : Summable (fun a => p a*E a)) (href : Summable (fun a => Real.exp (-E a))) :
    countableEntropy p ≤ (∑' a,Real.exp (-E a))+(∑' a,p a*E a) := by
  have hH := summable_entropy_of_reference_energy p E hp hsum hE href
  have h := Summable.tsum_le_tsum (fun a => negMulLog_le_energy_exp (p a) (E a) (hp a)) hH (hE.add href)
  simpa only [countableEntropy,hE.tsum_add href,add_comm] using h

theorem countableEntropy_nonneg (p : A → ℝ) (hp : ∀ a,0 ≤ p a) (hsum : HasSum p 1) :
    0 ≤ countableEntropy p :=
  tsum_nonneg (fun a => Real.negMulLog_nonneg (hp a) (mass_le_one_of_hasSum p hp hsum a))

end GeneralizedBulk.Entropy
