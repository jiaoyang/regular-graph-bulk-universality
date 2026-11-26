import BourgadeHuang.CMS.GeneralBranchRayAsymptotics

/-! Exact quadratic homogeneity of the general-coupling branch factor.
Neutral real charges have nonnegative degree, and degree zero is precisely
the signed charge-balance condition. -/
noncomputable section
open scoped BigOperators
namespace BourgadeHuang.CMS
variable {d : ℕ}

theorem twice_sum_upperPairs {f : Fin d → Fin d → ℂ}
    (hs : ∀i j,f i j=f j i) (hd : ∀i,f i i=0) :
    2*(∑p∈upperPairs d,f p.1 p.2)=∑i,∑j,f i j := by
  classical
  have he (i j : Fin d) : f i j=
      (if i < j then f i j else 0)+(if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with hij|rfl|hji
    · simp [hij,not_lt.mpr hij.le]
    · simp [hd]
    · simp [hji,not_lt.mpr hji.le]
  have hswap : (∑i,∑j,if j < i then f i j else 0)=
      ∑i,∑j,if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs j i]
  calc
    _=2*(∑i,∑j,if i < j then f i j else 0) := by
      simp only [upperPairs,Finset.sum_filter,Fintype.sum_prod_type]
    _=(∑i,∑j,if i < j then f i j else 0)+(∑i,∑j,if j < i then f i j else 0) := by rw [hswap];ring
    _=∑i,∑j,f i j := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      exact (he i j).symm

/-- Exact total logarithmic homogeneity, for arbitrary complex charges. -/
theorem generalRayDegree_eq_quadratic (β : ℂ) (hβ : β≠0)
    (c : Fin d → ℂ) (σ : Fin d → Sign) :
    generalRayDegree β c σ=
      ((∑i,c i*signValue (σ i))^2-(∑i,c i)^2)/(2*β) := by
  have htwo := twice_sum_upperPairs (couplingExponent_symm β c σ) (couplingExponent_self β c σ)
  change 2*generalRayDegree β c σ=∑i,∑j,couplingExponent β c σ i j at htwo
  have hsum : β*(∑i,∑j,couplingExponent β c σ i j)=
      (∑i,c i*signValue (σ i))^2-(∑i,c i)^2 := by
    simp only [Finset.mul_sum,pow_two,Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    unfold couplingExponent
    field_simp
    ring
  rw [←htwo] at hsum
  apply (eq_div_iff (mul_ne_zero (by norm_num) hβ)).mpr
  calc
    generalRayDegree β c σ*(2*β)=β*(2*generalRayDegree β c σ) := by ring
    _=_ := hsum

/-- Real charges have real homogeneity, with the exact signed-square formula. -/
theorem generalRayDegree_real {β : ℝ} (hβ : β≠0) (c : Fin d → ℝ)
    (σ : Fin d → Sign) :
    generalRayDegree (β:ℂ) (fun i=>(c i:ℂ)) σ=
      ((((∑i,c i*realSign (σ i))^2-(∑i,c i)^2)/(2*β):ℝ):ℂ) := by
  rw [generalRayDegree_eq_quadratic _ (Complex.ofReal_ne_zero.mpr hβ)]
  simp only [Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_pow,Complex.ofReal_sum,
    Complex.ofReal_mul,ofReal_realSign,Complex.ofReal_ofNat]

/-- For neutral real charges the degree is a nonnegative square. -/
theorem generalRayDegree_neutral_re {β : ℝ} (hβ : 0<β) (c : Fin d → ℝ)
    (hc : ∑i,c i=0) (σ : Fin d → Sign) :
    (generalRayDegree (β:ℂ) (fun i=>(c i:ℂ)) σ).re=
      (∑i,c i*realSign (σ i))^2/(2*β) := by
  rw [generalRayDegree_real hβ.ne' c σ,Complex.ofReal_re,hc]
  ring

theorem generalRayDegree_neutral_nonneg {β : ℝ} (hβ : 0<β) (c : Fin d → ℝ)
    (hc : ∑i,c i=0) (σ : Fin d → Sign) :
    0≤(generalRayDegree (β:ℂ) (fun i=>(c i:ℂ)) σ).re := by
  rw [generalRayDegree_neutral_re hβ c hc σ]
  positivity

theorem generalRayDegree_neutral_pos_iff {β : ℝ} (hβ : 0<β) (c : Fin d → ℝ)
    (hc : ∑i,c i=0) (σ : Fin d → Sign) :
    0<(generalRayDegree (β:ℂ) (fun i=>(c i:ℂ)) σ).re ↔
      (∑i,c i*realSign (σ i))≠0 := by
  rw [generalRayDegree_neutral_re hβ c hc σ]
  exact (div_pos_iff_of_pos_right (by positivity)).trans sq_pos_iff

end BourgadeHuang.CMS
