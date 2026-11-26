import GeneralizedBulk.Entropy.FullChaosBasis

/-! A triangular Hermite filtration of actual polynomial functions. Linear
changes of Gaussian coordinates preserve this filtration before orthogonality
selects each homogeneous chaos. -/
noncomputable section
open MeasureTheory Filter Polynomial
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite

variable {I : Type*} [Fintype I] [DecidableEq I]

def upper (a : I → ℕ) (i : I) : I → ℕ := Function.update a i (a i + 1)

theorem multiHermite_exponent_factor (a : I → ℕ) (i : I) (n : ℕ) (x : I → ℝ) :
    multiHermite I (Function.update a i n) x = (hermite n).eval (x i) *
      ∏ j ∈ Finset.univ.erase i, (hermite (a j)).eval (x j) := by
  have h := multiHermite_update_factor (Function.update a i n) i x (x i)
  rw [Function.update_eq_self] at h
  rw [h]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem derivative_factor (a : I → ℕ) (i : I) (x : I → ℝ) :
    (hermite (a i)).derivative.eval (x i) * ∏ j ∈ Finset.univ.erase i, (hermite (a j)).eval (x j) =
      (a i : ℝ) * multiHermite I (lower a i) x := by
  have hp0 : HasDerivAt (fun t : ℝ => (hermite (a i)).eval (x i + t))
      ((hermite (a i)).derivative.eval (x i)) 0 := by
    simpa only [id_eq, add_zero, mul_one] using
      ((hermite (a i)).hasDerivAt (x i + 0)).comp 0 ((hasDerivAt_id (0 : ℝ)).const_add (x i))
  have hp := hp0.mul_const (∏ j ∈ Finset.univ.erase i, (hermite (a j)).eval (x j))
  have hfun : (fun t : ℝ => multiHermite I a (Function.update x i (x i + t))) =
      (fun t : ℝ => (hermite (a i)).eval (x i + t) * ∏ j ∈ Finset.univ.erase i, (hermite (a j)).eval (x j)) := by
    funext t
    exact multiHermite_update_factor a i x (x i + t)
  have h := hasDerivAt_multiHermite_coordinate a i x
  rw [hfun] at h
  exact hp.unique h

/-- The genuine multivariate Hermite creation formula. -/
theorem coordinate_creation (a : I → ℕ) (i : I) (x : I → ℝ) :
    x i * multiHermite I a x = multiHermite I (upper a i) x +
      (a i : ℝ) * multiHermite I (lower a i) x := by
  have hf := multiHermite_update_factor a i x (x i)
  rw [Function.update_eq_self] at hf
  rw [hf, upper, multiHermite_exponent_factor, hermite_succ,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, ← derivative_factor]
  ring

@[simp] theorem upper_degree (a : I → ℕ) (i : I) : (∑ j, upper a i j) = (∑ j, a j) + 1 := by
  rw [upper, Finset.sum_update_of_mem (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase]
  have h := Finset.add_sum_erase Finset.univ a (Finset.mem_univ i)
  omega

theorem lower_degree_le (a : I → ℕ) (i : I) : (∑ j, lower a i j) ≤ ∑ j, a j := by
  apply Finset.sum_le_sum
  intro j hj
  by_cases hji : j = i
  · subst j
    simp only [lower, Function.update_self]
    exact Nat.sub_le _ _
  · simp only [lower, Function.update_of_ne hji, le_refl]

/-- The filtration is a literal subspace of polynomial functions; it will be
mapped into actual Gaussian L² using the proved Hermite integrability. -/
def functionFiltration (degree : ℕ) : Submodule ℝ ((I → ℝ) → ℝ) :=
  Submodule.span ℝ {f | ∃ a : I → ℕ, (∑ i, a i) ≤ degree ∧ f = multiHermite I a}

omit [DecidableEq I] in
theorem multiHermite_mem_functionFiltration (a : I → ℕ) (degree : ℕ) (ha : (∑ i, a i) ≤ degree) :
    multiHermite I a ∈ functionFiltration degree := Submodule.subset_span ⟨a, ha, rfl⟩

omit [DecidableEq I] in
theorem functionFiltration_mono {n m : ℕ} (hnm : n ≤ m) :
    functionFiltration (I := I) n ≤ functionFiltration m := by
  apply Submodule.span_mono
  rintro f ⟨a, ha, rfl⟩
  exact ⟨a, ha.trans hnm, rfl⟩

theorem one_mem_functionFiltration : (fun _ : I → ℝ => (1 : ℝ)) ∈ functionFiltration (I := I) 0 := by
  have h := multiHermite_mem_functionFiltration (fun _ : I => 0) 0 (by simp)
  convert h using 1
  funext x
  simp [multiHermite]

def coordinateMul (i : I) : ((I → ℝ) → ℝ) →ₗ[ℝ] ((I → ℝ) → ℝ) where
  toFun f x := x i * f x
  map_add' f g := by funext x; simp; ring
  map_smul' r f := by funext x; simp; ring

/-- Multiplying by a coordinate raises the triangular Hermite filtration by
at most one. This is proved by the actual creation formula. -/
theorem coordinateMul_mem {f : (I → ℝ) → ℝ} {degree : ℕ}
    (hf : f ∈ functionFiltration degree) (i : I) :
    coordinateMul i f ∈ functionFiltration (degree + 1) := by
  have hincl : functionFiltration (I := I) degree ≤
      (functionFiltration (degree + 1)).comap (coordinateMul i) := by
    apply Submodule.span_le.mpr
    rintro g ⟨a, ha, rfl⟩
    change coordinateMul i (multiHermite I a) ∈ functionFiltration (degree + 1)
    have hu := multiHermite_mem_functionFiltration (upper a i) (degree + 1) (by rw [upper_degree]; omega)
    have hl := multiHermite_mem_functionFiltration (lower a i) (degree + 1)
      ((lower_degree_le a i).trans (ha.trans (Nat.le_succ degree)))
    have hsum := (functionFiltration (I := I) (degree + 1)).add_mem hu
      ((functionFiltration (I := I) (degree + 1)).smul_mem (a i : ℝ) hl)
    convert hsum using 1
    funext x
    exact coordinate_creation a i x
  exact hincl hf

def linearForm (c : I → ℝ) (x : I → ℝ) : ℝ := ∑ i, c i * x i

/-- Every linear coordinate observation raises polynomial Hermite degree by
at most one. The observation coefficients are arbitrary here. -/
theorem linearForm_mul_mem {f : (I → ℝ) → ℝ} {degree : ℕ}
    (hf : f ∈ functionFiltration degree) (c : I → ℝ) :
    (fun x => linearForm c x * f x) ∈ functionFiltration (degree + 1) := by
  have hs : (∑ i : I, c i • coordinateMul i f) ∈ functionFiltration (degree + 1) := by
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (coordinateMul_mem hf i)
  convert hs using 1
  funext x
  simp only [linearForm, Finset.sum_apply, Pi.smul_apply, coordinateMul, LinearMap.coe_mk,
    AddHom.coe_mk, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem linearForm_pow_mul_mem {f : (I → ℝ) → ℝ} {degree : ℕ}
    (hf : f ∈ functionFiltration degree) (c : I → ℝ) (power : ℕ) :
    (fun x => linearForm c x ^ power * f x) ∈ functionFiltration (degree + power) := by
  induction power with
  | zero => simpa only [pow_zero, one_mul, Nat.add_zero] using hf
  | succ power ih =>
    have h := linearForm_mul_mem ih c
    simp only [Nat.add_assoc] at h
    convert h using 1
    funext x
    rw [pow_succ]
    ring

/-- The real Hermite polynomial has its claimed actual polynomial degree. -/
theorem hermite_natDegree (n : ℕ) : (hermite n).natDegree = n := by
  rw [hermite_eq_map, (Polynomial.hermite_monic n).natDegree_map]
  exact Polynomial.natDegree_hermite

/-- A univariate polynomial of a linear observation raises the triangular
filtration by its genuine polynomial degree. -/
theorem polynomial_linearForm_mul_mem {f : (I → ℝ) → ℝ} {degree : ℕ}
    (hf : f ∈ functionFiltration degree) (c : I → ℝ) (P : ℝ[X]) :
    (fun x => P.eval (linearForm c x) * f x) ∈ functionFiltration (degree + P.natDegree) := by
  have hs : (∑ j ∈ Finset.range (P.natDegree + 1),
      P.coeff j • (fun x => linearForm c x ^ j * f x)) ∈ functionFiltration (degree + P.natDegree) := by
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    apply functionFiltration_mono (Nat.add_le_add_left (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj) degree)
    exact linearForm_pow_mul_mem hf c j
  convert hs using 1
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    P.eval (linearForm c x) * f x =
        (∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * linearForm c x ^ j) * f x := by
      rw [Polynomial.eval_eq_sum_range]
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem product_polynomial_linear_mem (s : Finset I) (P : I → ℝ[X]) (c : I → I → ℝ) :
    (fun x => ∏ i ∈ s, (P i).eval (linearForm (c i) x)) ∈
      functionFiltration (∑ i ∈ s, (P i).natDegree) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using (one_mem_functionFiltration (I := I))
  | @insert i s hi ih =>
    have h := polynomial_linearForm_mul_mem ih (c i) (P i)
    simpa only [Finset.prod_insert hi, Finset.sum_insert hi, Nat.add_comm] using h

/-- Any linear change of coordinates, without an orthogonality assumption,
preserves the triangular Hermite filtration of actual polynomial functions. -/
theorem multiHermite_linear_substitution_mem (a : I → ℕ) (O : I → I → ℝ) :
    (fun x => multiHermite I a (fun i => linearForm (O i) x)) ∈ functionFiltration (∑ i, a i) := by
  simpa only [multiHermite, hermite_natDegree] using
    product_polynomial_linear_mem Finset.univ (fun i => hermite (a i)) O

def linearSubstitution (O : I → I → ℝ) : ((I → ℝ) → ℝ) →ₗ[ℝ] ((I → ℝ) → ℝ) where
  toFun f x := f (fun i => linearForm (O i) x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The triangular degree-preservation result as a genuine linear subspace
invariance statement, ready to combine with Gaussian orthogonal invariance. -/
theorem linearSubstitution_mem {f : (I → ℝ) → ℝ} {degree : ℕ}
    (hf : f ∈ functionFiltration degree) (O : I → I → ℝ) :
    linearSubstitution O f ∈ functionFiltration degree := by
  have hincl : functionFiltration (I := I) degree ≤ (functionFiltration degree).comap (linearSubstitution O) := by
    apply Submodule.span_le.mpr
    rintro g ⟨a, ha, rfl⟩
    exact functionFiltration_mono ha (multiHermite_linear_substitution_mem a O)
  exact hincl hf

end GeneralizedBulk.Entropy.Hermite
