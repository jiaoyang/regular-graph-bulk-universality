import GaussianWave.BS.RadialAdjacencyPolynomial
import GaussianWave.BS.GaussianRadialFilter

/-! The actual Gaussian block-factor approximation. The local coefficient
normalization and eigen-equation error are computed, and no weak-convergence
or Gaussian-wave approximation conclusion is supplied as a premise. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.BS

private theorem raw_radial_filter_eq_operator (d R : ℕ) (hd : 1 ≤ d)
    (u : RegularTreeVertex d) (f : ℕ → ℝ) :
    regularTreeRadialFinsupp d R u f =
      radialFilterOperator (finiteAdjacency (regularWordTree d)) d R f (Finsupp.single u 1) := by
  ext v
  rw [regularTreeRadialFinsupp_apply,
    radialFilterOperator_single_apply (regularWordTree_isTree d) d (regularWordTree_regular d hd)]

/-- The normalized coefficient vector has actual Euclidean norm one. -/
theorem radialGaussianBlockCoefficient_norm (d : ℕ) (hd : 2 ≤ d) (x : ℝ) (k : ℕ)
    (u : RegularTreeVertex d) :
    finsuppPairing (radialGaussianBlockCoefficient d x k u) (radialGaussianBlockCoefficient d x k u)=1 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos := radialVertexExceptional_pos (show 0 < (d : ℝ)-1 by linarith) k (x := x)
  unfold radialGaussianBlockCoefficient
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
  rw [finsuppPairing_self,regularTree_spherical_filter_norm d hd]
  have hs := Real.sq_sqrt hpos.le
  have hs0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  field_simp

/-- The covariance of the actual normalized local sampler. -/
def radialBlockCovariance (d : ℕ) (x : ℝ) (k : ℕ)
    (u v : RegularTreeVertex d) : ℝ :=
  finsuppPairing (radialGaussianBlockCoefficient d x k u) (radialGaussianBlockCoefficient d x k v)

@[simp] theorem radialBlockCovariance_diagonal (d : ℕ) (hd : 2 ≤ d) (x : ℝ) (k : ℕ)
    (u : RegularTreeVertex d) : radialBlockCovariance d x k u u=1 :=
  radialGaussianBlockCoefficient_norm d hd x k u

/-- Covariance radiality follows from actual adjacency polynomials and their
self-adjointness, and is valid simultaneously at every center. -/
theorem radialBlockCovariance_radial (d : ℕ) (hd : 2 ≤ d) (x : ℝ) (k : ℕ) :
    ∃ g : ℕ → ℝ, ∀ u v : RegularTreeVertex d,
      radialBlockCovariance d x k u v=g ((regularWordTree d).dist u v) := by
  let f := sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x)
  let S := radialVertexExceptional ((d : ℝ)-1) x k
  let P := radialFilterOperator (radialAdjacencyProfile d) d (k+1) f
  refine ⟨fun n => (Real.sqrt S)⁻¹*((Real.sqrt S)⁻¹*(P (P (sphereIndicator 0)) n)),?_⟩
  intro u v
  unfold radialBlockCovariance radialGaussianBlockCoefficient
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
  rw [raw_radial_filter_eq_operator d (k+1) (by omega),
    raw_radial_filter_eq_operator d (k+1) (by omega)]
  rw [radial_filter_pairing_kernel (regularWordTree_isTree d) d (regularWordTree_regular d (by omega))]

/-- Every actual sampled window has precisely this normalized covariance. -/
theorem radialGaussianBlockLaw_finite_covariance (d : ℕ) (x : ℝ) (k : ℕ)
    {I : Type*} [Fintype I] (v : I → RegularTreeVertex d) :
    HasGaussianCovariance
      (Measure.map (fun z : RegularTreeVertex d → ℝ => fun i => z (v i)) (radialGaussianBlockLaw d x k))
      (fun i j => radialBlockCovariance d x k (v i) (v j)) := by
  have h := radialGaussianBlockLaw_finite_gaussian d x k v
  have he : finiteSupportGaussianMatrix (fun i => radialGaussianBlockCoefficient d x k (v i))*
      (finiteSupportGaussianMatrix (fun i => radialGaussianBlockCoefficient d x k (v i))).transpose =
      (fun i j => radialBlockCovariance d x k (v i) (v j)) := by
    ext i j
    exact finiteSupportGaussianMatrix_gram _ i j
  rwa [he] at h

/-- The exact radial profile of the unnormalized truncation's residual. -/
theorem truncated_spherical_residual (d : ℕ) (hd : 2 ≤ d) (energy : ℝ) (k n : ℕ) :
    radialAdjacencyProfile d (fun r => if r≤k+1 then sphericalCovariance d energy r else 0) n -
      energy*(if n≤k+1 then sphericalCovariance d energy n else 0) =
      if n=k+1 then -((d : ℝ)-1)*sphericalCovariance d energy (k+2) else
      if n=k+2 then sphericalCovariance d energy (k+1) else 0 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hq : (d : ℝ)-1 ≠ 0 := by linarith
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  by_cases hn : n=0
  · subst n
    simp only [radialAdjacencyProfile,LinearMap.coe_mk,AddHom.coe_mk,↓reduceIte,
      Nat.zero_le,if_pos (show 1≤k+1 by omega),sphericalCovariance_one,sphericalCovariance_zero,mul_one]
    have h1 : (0 : ℕ) ≠ k+1 := by omega
    have h2 : (0 : ℕ) ≠ k+2 := by omega
    rw [if_neg h1,if_neg h2,mul_div_cancel₀ _ hd0,sub_self]
  · have hnpos : 1 ≤ n := by omega
    have hr := sphericalCovariance_recurrence d energy hq (n-1)
    have h1 : n-1+1=n := by omega
    have h2 : n-1+2=n+1 := by omega
    rw [h1,h2] at hr
    change (if n=0 then _ else _)-_= _
    rw [if_neg hn]
    dsimp only
    by_cases hnk : n=k+1
    · subst n
      simp only [Nat.le_refl,↓reduceIte]
      have hh : k+1-1≤k+1 := by omega
      have hh' : ¬k+1+1≤k+1 := by omega
      rw [if_pos hh,if_neg hh']
      have he : k+1+1=k+2 := by omega
      rw [he] at hr
      linarith
    · rw [if_neg hnk]
      by_cases hnk' : n=k+2
      · subst n
        have hh : k+2-1=k+1 := by omega
        have hh' : ¬k+2≤k+1 := by omega
        have hh'' : ¬k+2+1≤k+1 := by omega
        rw [hh,if_pos (le_refl _),if_neg hh',if_neg hh'',if_pos rfl]
        ring
      · rw [if_neg hnk']
        by_cases hlt : n≤k+1
        · have hprev : n-1≤k+1 := by omega
          have hnext : n+1≤k+1 := by omega
          rw [if_pos hprev,if_pos hnext,if_pos hlt]
          linarith
        · have hprev : ¬n-1≤k+1 := by omega
          have hnext : ¬n+1≤k+1 := by omega
          rw [if_neg hprev,if_neg hnext,if_neg hlt]
          ring


/-- The two literal shells supporting a truncated spherical residual. -/
def sphericalBoundaryProfile (d : ℕ) (energy : ℝ) (k n : ℕ) : ℝ :=
  if n=k+1 then -((d : ℝ)-1)*sphericalCovariance d energy (k+2) else
  if n=k+2 then sphericalCovariance d energy (k+1) else 0

private theorem raw_spherical_residual_eq (d : ℕ) (hd : 2 ≤ d) (energy : ℝ)
    (k : ℕ) (u : RegularTreeVertex d) :
    finiteAdjacency (regularWordTree d) (regularTreeRadialFinsupp d (k+1) u (sphericalCovariance d energy)) -
      energy • regularTreeRadialFinsupp d (k+1) u (sphericalCovariance d energy) =
      regularTreeRadialFinsupp d (k+2) u (sphericalBoundaryProfile d energy k) := by
  let a := regularTreeRadialFinsupp d (k+1) u (sphericalCovariance d energy)
  have ha : HasTreeRadialProfile (regularWordTree d) u a
      (fun n => if n≤k+1 then sphericalCovariance d energy n else 0) :=
    fun v => regularTreeRadialFinsupp_apply d (k+1) u v _
  have hA := finiteAdjacency_has_radialProfile (regularWordTree_isTree d) d
    (regularWordTree_regular d (by omega)) u a _ ha
  ext v
  change finiteAdjacency (regularWordTree d) a v-energy*a v=_
  rw [hA,ha,truncated_spherical_residual d hd,regularTreeRadialFinsupp_apply]
  by_cases hv : (regularWordTree d).dist v u≤k+2
  · rw [if_pos hv]
    rfl
  · rw [if_neg hv]
    have h1 : (regularWordTree d).dist v u ≠ k+1 := by omega
    have h2 : (regularWordTree d).dist v u ≠ k+2 := by omega
    rw [if_neg h1,if_neg h2]

private theorem scaled_spherical_square (d : ℕ) (hd : 2 ≤ d) (x : ℝ) (n : ℕ) :
    ((d : ℝ)-1)^n*sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x) n ^ 2 =
      radialScaledWave ((d : ℝ)-1) x n ^ 2 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  rw [← sphericalCovariance_scaled_radial d hd x n,mul_pow,← pow_mul,
    mul_comm n 2,pow_mul,Real.sq_sqrt (show 0 ≤ (d : ℝ)-1 by linarith)]

/-- The exact squared residual norm is a bounded two-shell boundary term. -/
theorem raw_spherical_residual_norm (d : ℕ) (hd : 2 ≤ d) (x : ℝ) (k : ℕ)
    (u : RegularTreeVertex d) :
    let a := regularTreeRadialFinsupp d (k+1) u
      (sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x))
    let e := finiteAdjacency (regularWordTree d) a-(2*Real.sqrt ((d : ℝ)-1)*x) • a
    finsuppPairing e e=radialBoundaryError ((d : ℝ)-1) x k := by
  dsimp only
  rw [raw_spherical_residual_eq d hd,finsuppPairing_self,regularTreeRadialFinsupp_square_sum,
    regularTree_sum_ball_radial d (by omega) u (k+2)
      (fun n => sphericalBoundaryProfile d (2*Real.sqrt ((d : ℝ)-1)*x) k n ^ 2)]
  have hzero : sphericalBoundaryProfile d (2*Real.sqrt ((d : ℝ)-1)*x) k 0=0 := by
    unfold sphericalBoundaryProfile
    rw [if_neg (by omega),if_neg (by omega)]
  rw [hzero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_add]
  let energy := 2*Real.sqrt ((d : ℝ)-1)*x
  have hterm (n : ℕ) : sphericalBoundaryProfile d energy k (n+1)^2 =
      (if n=k then (((d : ℝ)-1)*sphericalCovariance d energy (k+2))^2 else 0)+
      (if n=k+1 then sphericalCovariance d energy (k+1)^2 else 0) := by
    unfold sphericalBoundaryProfile
    by_cases h1 : n=k
    · subst n
      have hh : k+1 ≠ k+2 := by omega
      simp [hh,neg_mul,neg_sq]
      ring
    · by_cases h2 : n=k+1
      · subst n
        have hh : k+1+1 ≠ k+1 := by omega
        have he : k+1+1=k+2 := by omega
        simp [hh,he]
      · have hh1 : n+1 ≠ k+1 := by omega
        have hh2 : n+1 ≠ k+2 := by omega
        simp [h1,h2,hh1,hh2]
  change (∑ n ∈ Finset.range (k+2),
    (d : ℝ)*((d-1 : ℕ) : ℝ)^n*sphericalBoundaryProfile d energy k (n+1)^2)=_
  simp_rw [hterm,mul_add,mul_ite,mul_zero]
  rw [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.sum_ite_eq']
  simp only [Finset.mem_range,show k<k+2 by omega,show k+1<k+2 by omega,↓reduceIte]
  rw [Nat.cast_sub (by omega : 1≤d),Nat.cast_one,mul_pow]
  have h1 := scaled_spherical_square d hd x (k+1)
  have h2 := scaled_spherical_square d hd x (k+2)
  have hp : ((d : ℝ)-1)^(k+2)=((d : ℝ)-1)^k*((d : ℝ)-1)^2 := by rw [pow_add]
  rw [hp] at h2
  change _ = ((d : ℝ)-1+1)*(radialScaledWave ((d : ℝ)-1) x (k+1)^2+
    radialScaledWave ((d : ℝ)-1) x (k+2)^2)
  dsimp only [energy] at *
  nlinarith [h1,h2]

/-- The actual local coefficient eigen-equation residual. -/
def radialGaussianBlockResidual (d : ℕ) (x : ℝ) (k : ℕ) (u : RegularTreeVertex d) :
    RegularTreeVertex d →₀ ℝ :=
  finiteAdjacency (regularWordTree d) (radialGaussianBlockCoefficient d x k u)-
    (2*Real.sqrt ((d : ℝ)-1)*x) • radialGaussianBlockCoefficient d x k u

/-- Its squared Euclidean error is exactly the computed bounded boundary
energy divided by the actual growing truncation variance. -/
theorem radialGaussianBlockResidual_norm (d : ℕ) (hd : 2 ≤ d) (x : ℝ) (k : ℕ)
    (u : RegularTreeVertex d) :
    finsuppPairing (radialGaussianBlockResidual d x k u) (radialGaussianBlockResidual d x k u) =
      radialBoundaryError ((d : ℝ)-1) x k/radialVertexExceptional ((d : ℝ)-1) x k := by
  let S := radialVertexExceptional ((d : ℝ)-1) x k
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hS : 0<S := radialVertexExceptional_pos (show 0 < (d : ℝ)-1 by linarith) k
  have hscale : radialGaussianBlockResidual d x k u = (Real.sqrt S)⁻¹ •
      (finiteAdjacency (regularWordTree d)
        (regularTreeRadialFinsupp d (k+1) u (sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x)))-
        (2*Real.sqrt ((d : ℝ)-1)*x) •
        regularTreeRadialFinsupp d (k+1) u (sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x))) := by
    unfold radialGaussianBlockResidual radialGaussianBlockCoefficient
    dsimp only [S]
    rw [map_smul,smul_sub,smul_smul,smul_smul]
    congr 1
    ring
  rw [hscale]
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
  rw [raw_spherical_residual_norm d hd]
  have hs : (Real.sqrt S)^2=S := Real.sq_sqrt hS.le
  have hs0 : Real.sqrt S ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hS)
  have hinv : (Real.sqrt S)⁻¹*(Real.sqrt S)⁻¹=1/S := by
    field_simp
  change (Real.sqrt S)⁻¹*((Real.sqrt S)⁻¹*radialBoundaryError ((d : ℝ)-1) x k)=_
  rw [← mul_assoc,hinv]
  ring

/-- The actually constructed radius-local Gaussian rules become exact
variance-one eigenfunctions in mean square throughout the strict bulk. -/
theorem radialGaussianBlockResidual_tendsto_zero (d : ℕ) (hd : 3 ≤ d) (x : ℝ) (hx : |x|<1)
    (u : RegularTreeVertex d) :
    Tendsto (fun k => finsuppPairing (radialGaussianBlockResidual d x k u)
      (radialGaussianBlockResidual d x k u)) atTop (𝓝 0) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  simp_rw [radialGaussianBlockResidual_norm d (by omega)]
  exact radialBoundaryError_div_variance_tendsto_zero (by linarith) hx


/-- Acting on the label coordinate and summing over neighboring centers
are the same actual coefficient vector, by polynomial commutation. -/
theorem radialGaussianBlockCoefficient_adjacency (d : ℕ) (hd : 2 ≤ d) (x : ℝ) (k : ℕ)
    (u : RegularTreeVertex d) :
    finiteAdjacency (regularWordTree d) (radialGaussianBlockCoefficient d x k u) =
      ∑ z : (regularWordTree d).neighborSet u, radialGaussianBlockCoefficient d x k z.val := by
  let A := finiteAdjacency (regularWordTree d)
  let f := sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x)
  let Q := radialFilterOperator A d (k+1) f
  let c := (Real.sqrt (radialVertexExceptional ((d : ℝ)-1) x k))⁻¹
  have he (v : RegularTreeVertex d) : radialGaussianBlockCoefficient d x k v=c • Q (Finsupp.single v 1) := by
    unfold radialGaussianBlockCoefficient
    rw [raw_radial_filter_eq_operator d (k+1) (by omega)]
  have hc : A*(Q)=Q*A := radialFilterOperator_commutes A d (k+1) f
  have hcu : A (Q (Finsupp.single u 1))=Q (A (Finsupp.single u 1)) :=
    congrArg (fun T : Module.End ℝ (RegularTreeVertex d →₀ ℝ) => T (Finsupp.single u 1)) hc
  simp_rw [he]
  rw [map_smul,hcu,finiteAdjacency_single_sum,map_sum,Finset.smul_sum]

/-- The actual covariance satisfies the eigen-equation up to its computed
local coefficient residual, with its true Cauchy--Schwarz error bound. -/
theorem radialBlockCovariance_eigen_error_sq (d : ℕ) (hd : 2 ≤ d) (x : ℝ) (k : ℕ)
    (u v : RegularTreeVertex d) :
    ((∑ z : (regularWordTree d).neighborSet u, radialBlockCovariance d x k z.val v)-
      (2*Real.sqrt ((d : ℝ)-1)*x)*radialBlockCovariance d x k u v)^2 ≤
      finsuppPairing (radialGaussianBlockResidual d x k u) (radialGaussianBlockResidual d x k u) := by
  have h := finsuppPairing_sq_le (radialGaussianBlockResidual d x k u)
    (radialGaussianBlockCoefficient d x k v)
  rw [radialGaussianBlockCoefficient_norm d hd x k v,mul_one] at h
  have he : finsuppPairing (radialGaussianBlockResidual d x k u) (radialGaussianBlockCoefficient d x k v) =
      (∑ z : (regularWordTree d).neighborSet u, radialBlockCovariance d x k z.val v)-
        (2*Real.sqrt ((d : ℝ)-1)*x)*radialBlockCovariance d x k u v := by
    unfold radialGaussianBlockResidual
    rw [map_sub,LinearMap.sub_apply,map_smul,LinearMap.smul_apply,
      radialGaussianBlockCoefficient_adjacency d hd,map_sum,LinearMap.sum_apply]
    rfl
  rwa [he] at h

/-- A generic elementary square-error limit used to solve the covariance
recurrence, with the actual error supplied by the constructed sampler. -/
private theorem tendsto_zero_of_square_bound (f e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hle : ∀ n, f n^2≤e n) :
    Tendsto f atTop (𝓝 0) := by
  have hs : Tendsto (fun n => Real.sqrt (e n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp he
  apply squeeze_zero_norm _ hs
  intro n
  rw [Real.norm_eq_abs]
  exact Real.le_sqrt_of_sq_le (by simpa only [sq_abs] using hle n)

/-- For every pair of actual tree sites, the covariance eigen-equation
error tends to zero. -/
theorem radialBlockCovariance_eigen_error_tendsto (d : ℕ) (hd : 3 ≤ d) (x : ℝ) (hx : |x|<1)
    (u v : RegularTreeVertex d) :
    Tendsto (fun k => (∑ z : (regularWordTree d).neighborSet u, radialBlockCovariance d x k z.val v)-
      (2*Real.sqrt ((d : ℝ)-1)*x)*radialBlockCovariance d x k u v) atTop (𝓝 0) := by
  apply tendsto_zero_of_square_bound _ _ (radialGaussianBlockResidual_tendsto_zero d hd x hx u)
  intro k
  exact radialBlockCovariance_eigen_error_sq d (by omega) x k u v

/-- A canonical radial covariance profile, chosen from the proved common
polynomial profile. -/
def radialBlockProfile (d : ℕ) (hd : 2 ≤ d) (x : ℝ) (k : ℕ) : ℕ → ℝ :=
  Classical.choose (radialBlockCovariance_radial d hd x k)

theorem radialBlockCovariance_eq_profile (d : ℕ) (hd : 2 ≤ d) (x : ℝ) (k : ℕ)
    (u v : RegularTreeVertex d) :
    radialBlockCovariance d x k u v=radialBlockProfile d hd x k ((regularWordTree d).dist u v) :=
  Classical.choose_spec (radialBlockCovariance_radial d hd x k) u v

@[simp] theorem radialBlockProfile_zero (d : ℕ) (hd : 2 ≤ d) (x : ℝ) (k : ℕ) :
    radialBlockProfile d hd x k 0=1 := by
  have h := radialBlockCovariance_eq_profile d hd x k none none
  rw [radialBlockCovariance_diagonal d hd,SimpleGraph.dist_self] at h
  exact h.symm

private theorem radialBlockProfile_root_error_tendsto (d : ℕ) (hd : 3 ≤ d) (x : ℝ) (hx : |x|<1) :
    Tendsto (fun k => (d : ℝ)*radialBlockProfile d (by omega) x k 1-
      (2*Real.sqrt ((d : ℝ)-1)*x)) atTop (𝓝 0) := by
  have h := radialBlockCovariance_eigen_error_tendsto d hd x hx none none
  simp_rw [radialBlockCovariance_eq_profile d (by omega)] at h
  have he (k : ℕ) : (∑ z : (regularWordTree d).neighborSet none,
      radialBlockProfile d (by omega) x k ((regularWordTree d).dist z.val none)) =
      (d : ℝ)*radialBlockProfile d (by omega) x k 1 := by
    rw [tree_sum_neighbor_radial (regularWordTree_isTree d) d (regularWordTree_regular d (by omega)),if_pos rfl]
  simpa only [he,SimpleGraph.dist_self,radialBlockProfile_zero,mul_one] using h

private theorem radialBlockProfile_recurrence_error_tendsto (d : ℕ) (hd : 3 ≤ d) (x : ℝ) (hx : |x|<1)
    (n : ℕ) :
    Tendsto (fun k => radialBlockProfile d (by omega) x k n+
      ((d : ℝ)-1)*radialBlockProfile d (by omega) x k (n+2)-
      (2*Real.sqrt ((d : ℝ)-1)*x)*radialBlockProfile d (by omega) x k (n+1)) atTop (𝓝 0) := by
  obtain ⟨v⟩ := regularTreeSphere_nonempty d (by omega) none (n+1)
  have hv : v.val ≠ none := by intro he; have h := v.property; simp [he,SimpleGraph.dist_self] at h
  have h := radialBlockCovariance_eigen_error_tendsto d hd x hx v.val none
  simp_rw [radialBlockCovariance_eq_profile d (by omega)] at h
  have he (k : ℕ) : (∑ z : (regularWordTree d).neighborSet v.val,
      radialBlockProfile d (by omega) x k ((regularWordTree d).dist z.val none)) =
      radialBlockProfile d (by omega) x k n+
        ((d : ℝ)-1)*radialBlockProfile d (by omega) x k (n+2) := by
    rw [tree_sum_neighbor_radial (regularWordTree_isTree d) d (regularWordTree_regular d (by omega)),if_neg hv,
      v.property]
    simp
  simpa only [he,v.property] using h

/-- Solving the actual approximate covariance recurrence identifies every
fixed-distance covariance with the unique variance-one spherical wave. -/
theorem radialBlockProfile_tendsto_spherical (d : ℕ) (hd : 3 ≤ d) (x : ℝ) (hx : |x|<1) (n : ℕ) :
    Tendsto (fun k => radialBlockProfile d (by omega) x k n) atTop
      (𝓝 (sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x) n)) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hq0 : (d : ℝ)-1 ≠ 0 := by linarith
  induction n using Nat.twoStepInduction with
  | zero => simpa only [radialBlockProfile_zero,sphericalCovariance_zero] using tendsto_const_nhds
  | one =>
    have h := ((radialBlockProfile_root_error_tendsto d hd x hx).add_const
      (2*Real.sqrt ((d : ℝ)-1)*x)).div_const (d : ℝ)
    simp only [zero_add,sphericalCovariance_one] at h ⊢
    convert h using 1
    funext k
    field_simp
  | more n hn hn1 =>
    have h := (((radialBlockProfile_recurrence_error_tendsto d hd x hx n).add
      (hn1.const_mul (2*Real.sqrt ((d : ℝ)-1)*x))).sub hn).div_const ((d : ℝ)-1)
    simp only [zero_add] at h
    rw [show (sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x) (n+2)) =
      ((2*Real.sqrt ((d : ℝ)-1)*x)*sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x) (n+1)-
        sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x) n)/((d : ℝ)-1) from rfl]
    convert h using 1
    funext k
    field_simp

/-- Entrywise covariance convergence of the actual constructed Gaussian
block factors, for every pair of actual sites. -/
theorem radialBlockCovariance_tendsto_spherical (d : ℕ) (hd : 3 ≤ d) (x : ℝ) (hx : |x|<1)
    (u v : RegularTreeVertex d) :
    Tendsto (fun k => radialBlockCovariance d x k u v) atTop
      (𝓝 (sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x) ((regularWordTree d).dist u v))) := by
  simp_rw [radialBlockCovariance_eq_profile d (by omega)]
  exact radialBlockProfile_tendsto_spherical d hd x hx _


/-- The computed covariance matrix of an actual finite sampled window. -/
def radialBlockCovarianceMatrix (d : ℕ) (x : ℝ) (k : ℕ)
    {I : Type*} (site : I → RegularTreeVertex d) : Matrix I I ℝ :=
  fun i j => radialBlockCovariance d x k (site i) (site j)

theorem radialBlockCovarianceMatrix_posSemidef (d : ℕ) (x : ℝ) (k : ℕ)
    {I : Type*} [Fintype I] (site : I → RegularTreeVertex d) :
    (radialBlockCovarianceMatrix d x k site).PosSemidef := by
  have he : radialBlockCovarianceMatrix d x k site =
      finiteSupportGaussianMatrix (fun i => radialGaussianBlockCoefficient d x k (site i))*
        (finiteSupportGaussianMatrix (fun i => radialGaussianBlockCoefficient d x k (site i))).transpose := by
    ext i j
    exact (finiteSupportGaussianMatrix_gram (fun i => radialGaussianBlockCoefficient d x k (site i)) i j).symm
  rw [he]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose
      (finiteSupportGaussianMatrix (fun i => radialGaussianBlockCoefficient d x k (site i)))

/-- The actual spherical covariance on any finite set of sites. -/
def radialFiniteWaveCovariance (d : ℕ) (energy : ℝ)
    {I : Type*} (site : I → RegularTreeVertex d) : Matrix I I ℝ :=
  fun i j => sphericalCovariance d energy ((regularWordTree d).dist (site i) (site j))

/-- Positivity of the spherical wave covariance is derived from the actual
Gaussian local samplers and their proved entrywise limit. -/
theorem radialFiniteWaveCovariance_posSemidef (d : ℕ) (hd : 3 ≤ d) (x : ℝ) (hx : |x|<1)
    {I : Type*} [Fintype I] (site : I → RegularTreeVertex d) :
    (radialFiniteWaveCovariance d (2*Real.sqrt ((d : ℝ)-1)*x) site).PosSemidef := by
  let C := fun k => radialBlockCovarianceMatrix d x k site
  let D := radialFiniteWaveCovariance d (2*Real.sqrt ((d : ℝ)-1)*x) site
  have hCD (i j : I) : Tendsto (fun k => C k i j) atTop (𝓝 (D i j)) :=
    radialBlockCovariance_tendsto_spherical d hd x hx (site i) (site j)
  refine ⟨?_,?_⟩
  · ext i j
    change sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x)
      ((regularWordTree d).dist (site j) (site i)) = _
    rw [SimpleGraph.dist_comm]
    rfl
  · intro t
    have hlim := finiteCovarianceQuadratic_tendsto C D hCD t
    have hnonneg (k : ℕ) : 0 ≤ finiteCovarianceQuadratic (C k) t := by
      have h := (radialBlockCovarianceMatrix_posSemidef d x k site).2 t
      simpa only [finiteCovarianceQuadratic,dotProduct,Matrix.mulVec,star_trivial,
        Finset.mul_sum,mul_assoc] using h
    have h := le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hnonneg)
    change 0 ≤ dotProduct (star t) (D.mulVec t)
    simpa only [finiteCovarianceQuadratic,dotProduct,Matrix.mulVec,star_trivial,
      Finset.mul_sum,mul_assoc] using h

/-- A constructed finite Gaussian-wave law with its actual covariance. -/
def radialFiniteWaveLaw (d : ℕ) (hd : 3 ≤ d) (x : ℝ) (hx : |x|<1)
    {I : Type*} [Fintype I] [DecidableEq I] (site : I → RegularTreeVertex d) : Measure (I → ℝ) :=
  gaussianCovarianceLaw (radialFiniteWaveCovariance d (2*Real.sqrt ((d : ℝ)-1)*x) site)
    (radialFiniteWaveCovariance_posSemidef d hd x hx site)

instance radialFiniteWaveLaw_isProbability (d : ℕ) (hd : 3 ≤ d) (x : ℝ) (hx : |x|<1)
    {I : Type*} [Fintype I] [DecidableEq I] (site : I → RegularTreeVertex d) :
    IsProbabilityMeasure (radialFiniteWaveLaw d hd x hx site) := by
  unfold radialFiniteWaveLaw
  infer_instance

/-- Genuine finite-window Gaussian block-factor approximation of the wave.
Both the samplers and limiting Gaussian laws are constructed; the only
restrictions are regular degree and strict-bulk energy. -/
theorem radialGaussianBlockLaw_finite_weakConverges (d : ℕ) (hd : 3 ≤ d) (x : ℝ) (hx : |x|<1)
    {I : Type*} [Fintype I] [DecidableEq I] (site : I → RegularTreeVertex d) :
    WeakLawConverges
      (fun k => Measure.map (fun z : RegularTreeVertex d → ℝ => fun i => z (site i))
        (radialGaussianBlockLaw d x k))
      (radialFiniteWaveLaw d hd x hx site) := by
  let C := fun k => radialBlockCovarianceMatrix d x k site
  have hC (k : ℕ) : (C k).PosSemidef := radialBlockCovarianceMatrix_posSemidef d x k site
  letI (k : ℕ) : IsProbabilityMeasure
      (Measure.map (fun z : RegularTreeVertex d → ℝ => fun i => z (site i)) (radialGaussianBlockLaw d x k)) :=
    isProbabilityMeasure_map (measurable_pi_lambda _ (fun i => measurable_pi_apply (site i))).aemeasurable
  have he (k : ℕ) : Measure.map (fun z : RegularTreeVertex d → ℝ => fun i => z (site i))
      (radialGaussianBlockLaw d x k) = gaussianCovarianceLaw (C k) (hC k) := by
    apply eq_gaussianCovarianceLaw
    exact radialGaussianBlockLaw_finite_covariance d x k site
  simp_rw [he]
  apply gaussianCovarianceLaw_weakConverges C hC _ _
  intro i j
  exact radialBlockCovariance_tendsto_spherical d hd x hx (site i) (site j)

end GaussianWave.BS
