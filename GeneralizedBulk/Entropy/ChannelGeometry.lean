import Mathlib

/-!
# Concrete regular-star Gaussian channel geometry

The transverse space is the actual zero-sum subspace of Euclidean `ℝ^d`.
This avoids choosing a parameter-dependent orthonormal basis. The simplex,
whitening rows and edge projections are concrete vectors and linear maps.
-/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Channel

abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)


@[simp] theorem ambient_sum_apply {d ι : ℕ} (s : Finset (Fin ι))
    (f : Fin ι → Ambient d) (j : Fin d) : (∑ i ∈ s, f i) j = ∑ i ∈ s, f i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, PiLp.add_apply, ih]

def coordinateSum (d : ℕ) : Ambient d →ₗ[ℝ] ℝ where
  toFun y := ∑ j : Fin d, y j
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c y := by simp [Finset.mul_sum]

def transverse (d : ℕ) : Submodule ℝ (Ambient d) := LinearMap.ker (coordinateSum d)
abbrev Transverse (d : ℕ) := transverse d

@[simp] theorem transverse_sum {d : ℕ} (y : Transverse d) :
    (∑ j : Fin d, (y : Ambient d) j) = 0 := y.property

def ones (d : ℕ) : Ambient d := (WithLp.equiv 2 _).symm (fun _ => 1)

@[simp] theorem ones_apply (d : ℕ) (i : Fin d) : ones d i = 1 := rfl

def centeredCoordinate (d : ℕ) (i : Fin d) : Ambient d :=
  EuclideanSpace.single i 1 - (1 / (d : ℝ)) • ones d

@[simp] theorem centeredCoordinate_apply (d : ℕ) (i j : Fin d) :
    centeredCoordinate d i j = (if j = i then 1 else 0) - 1 / (d : ℝ) := by
  simp [centeredCoordinate]

theorem centeredCoordinate_sum (d : ℕ) (hd : 0 < d) (i : Fin d) :
    (∑ j : Fin d, centeredCoordinate d i j) = 0 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  simp [Finset.sum_sub_distrib, hd0]

/-- The explicit unit-simplex normalization. -/
def simplexScale (d : ℕ) : ℝ := Real.sqrt ((d : ℝ) / ((d : ℝ) - 1))

theorem simplexScale_pos (d : ℕ) (hd : 2 ≤ d) : 0 < simplexScale d := by
  unfold simplexScale
  apply Real.sqrt_pos.mpr
  have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_pos (by linarith) (by linarith)

theorem simplexScale_sq (d : ℕ) (hd : 2 ≤ d) :
    simplexScale d ^ 2 = (d : ℝ) / ((d : ℝ) - 1) := by
  unfold simplexScale
  apply Real.sq_sqrt
  have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_nonneg (by linarith) (by linarith)

def simplex (d : ℕ) (hd : 2 ≤ d) (i : Fin d) : Transverse d :=
  ⟨simplexScale d • centeredCoordinate d i, by
    change (∑ j : Fin d, (simplexScale d • centeredCoordinate d i) j) = 0
    simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      centeredCoordinate_sum d (by omega) i, mul_zero]⟩

theorem inner_ones_left (d : ℕ) (y : Ambient d) :
    @inner ℝ (Ambient d) _ (ones d) y = ∑ j : Fin d, y j := by
  simp [PiLp.inner_apply, RCLike.inner_apply, ones]

theorem inner_centeredCoordinate_left (d : ℕ) (i : Fin d) (y : Ambient d) :
    @inner ℝ (Ambient d) _ (centeredCoordinate d i) y =
      y i - (1 / (d : ℝ)) * ∑ j : Fin d, y j := by
  simp [centeredCoordinate, inner_sub_left, inner_smul_left,
    EuclideanSpace.inner_single_left, inner_ones_left]

theorem simplex_inner (d : ℕ) (hd : 2 ≤ d) (i j : Fin d) :
    @inner ℝ (Transverse d) _ (simplex d hd i) (simplex d hd j) =
      if i = j then 1 else -1 / ((d : ℝ) - 1) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  change @inner ℝ (Ambient d) _ (simplexScale d • centeredCoordinate d i)
    (simplexScale d • centeredCoordinate d j) = _
  rw [inner_smul_left, inner_smul_right, inner_centeredCoordinate_left,
    centeredCoordinate_sum d (by omega) j]
  simp only [starRingEnd_apply, star_trivial, mul_zero, sub_zero, centeredCoordinate_apply]
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte]
    calc
      simplexScale d * (simplexScale d * (1 - 1 / (d : ℝ))) =
          simplexScale d ^ 2 * (1 - 1 / (d : ℝ)) := by ring
      _ = 1 := by rw [simplexScale_sq d hd]; field_simp [hd0, hd1]
  · simp only [hij, ↓reduceIte, zero_sub]
    calc
      simplexScale d * (simplexScale d * -(1 / (d : ℝ))) =
          simplexScale d ^ 2 * -(1 / (d : ℝ)) := by ring
      _ = _ := by rw [simplexScale_sq d hd]; field_simp [hd0, hd1]; ring

@[simp] theorem simplex_norm_sq (d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    ‖simplex d hd i‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, simplex_inner]
  simp

theorem simplex_sum (d : ℕ) (hd : 2 ≤ d) : (∑ i : Fin d, simplex d hd i) = 0 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_zero]
  change (∑ i : Fin d, simplexScale d • centeredCoordinate d i) = 0
  ext j
  rw [ambient_sum_apply]
  simp [PiLp.smul_apply, centeredCoordinate_apply, Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hd0]

/-- The zero-sum simplex is a tight frame with its exact transverse eigenvalue. -/
theorem simplex_frame (d : ℕ) (hd : 2 ≤ d) (y : Transverse d) :
    (∑ i : Fin d, (@inner ℝ (Transverse d) _ (simplex d hd i) y) • simplex d hd i) =
      ((d : ℝ) / ((d : ℝ) - 1)) • y := by
  apply Subtype.ext
  ext j
  have hc (i : Fin d) : @inner ℝ (Transverse d) _ (simplex d hd i) y =
      simplexScale d * (y : Ambient d) i := by
    change @inner ℝ (Ambient d) _ (simplexScale d • centeredCoordinate d i) y = _
    rw [inner_smul_left, inner_centeredCoordinate_left, transverse_sum]
    simp
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  change (∑ i : Fin d, (@inner ℝ (Transverse d) _ (simplex d hd i) y) •
    (simplexScale d • centeredCoordinate d i)) j = (((d : ℝ) / ((d : ℝ) - 1)) • (y : Ambient d)) j
  rw [ambient_sum_apply]
  simp only [PiLp.smul_apply, hc, centeredCoordinate_apply, smul_eq_mul]
  calc
    (∑ i : Fin d, (simplexScale d * (y : Ambient d) i) *
      (simplexScale d * ((if j = i then 1 else 0) - 1 / (d : ℝ)))) =
      simplexScale d ^ 2 * ((y : Ambient d) j - (1 / (d : ℝ)) * ∑ i : Fin d, (y : Ambient d) i) := by
        have ht (i : Fin d) :
            (simplexScale d * (y : Ambient d) i) *
                (simplexScale d * ((if j = i then 1 else 0) - 1 / (d : ℝ))) =
              simplexScale d ^ 2 * ((y : Ambient d) i * (if j = i then 1 else 0) -
                (1 / (d : ℝ)) * (y : Ambient d) i) := by ring
        simp_rw [ht]
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp [mul_ite]
    _ = _ := by rw [transverse_sum, mul_zero, sub_zero, simplexScale_sq d hd]

/-- Parseval's identity for the actual simplex frame. -/
theorem simplex_parseval (d : ℕ) (hd : 2 ≤ d) (y : Transverse d) :
    (∑ i : Fin d, (@inner ℝ (Transverse d) _ (simplex d hd i) y) ^ 2) =
      ((d : ℝ) / ((d : ℝ) - 1)) * ‖y‖ ^ 2 := by
  have h := congrArg (fun z : Transverse d => @inner ℝ (Transverse d) _ z y) (simplex_frame d hd y)
  simpa only [sum_inner, inner_smul_left, starRingEnd_apply, star_trivial, real_inner_self_eq_norm_sq, pow_two] using h

/-- The fixed whitened one-channel star space has one scalar and `d−1`
transverse dimensions; its definition is independent of the spectral parameter. -/
abbrev WhiteStar (d : ℕ) := WithLp 2 (ℝ × Transverse d)

def rootVector (d : ℕ) : WhiteStar d := (WithLp.equiv 2 _).symm (1, 0)

def transverseVector (d : ℕ) (hd : 2 ≤ d) (i : Fin d) : WhiteStar d :=
  (WithLp.equiv 2 _).symm (0, simplex d hd i)

def leafVector (d : ℕ) (hd : 2 ≤ d) (c rho : ℝ) (i : Fin d) : WhiteStar d :=
  c • rootVector d + rho • transverseVector d hd i

@[simp] theorem root_inner_root (d : ℕ) : @inner ℝ (WhiteStar d) _ (rootVector d) (rootVector d) = 1 := by
  simp [rootVector, WithLp.prod_inner_apply]

@[simp] theorem root_inner_transverse (d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    @inner ℝ (WhiteStar d) _ (rootVector d) (transverseVector d hd i) = 0 := by
  simp [rootVector, transverseVector, WithLp.prod_inner_apply]

@[simp] theorem transverse_inner_root (d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    @inner ℝ (WhiteStar d) _ (transverseVector d hd i) (rootVector d) = 0 := by
  simp [rootVector, transverseVector, WithLp.prod_inner_apply]

theorem transverse_inner_transverse (d : ℕ) (hd : 2 ≤ d) (i j : Fin d) :
    @inner ℝ (WhiteStar d) _ (transverseVector d hd i) (transverseVector d hd j) =
      if i = j then 1 else -1 / ((d : ℝ) - 1) := by
  simpa [transverseVector, WithLp.prod_inner_apply] using simplex_inner d hd i j

/-- Root--leaf correlation is exactly the regular-star parameter `c=λ/d`. -/
theorem root_leaf_correlation (d : ℕ) (hd : 2 ≤ d) (c rho : ℝ) (i : Fin d) :
    @inner ℝ (WhiteStar d) _ (rootVector d) (leafVector d hd c rho i) = c := by
  simp only [leafVector, inner_add_right, inner_smul_right, root_inner_root, root_inner_transverse, mul_one, mul_zero, add_zero]

/-- The distinct-leaf covariance is computed from the actual whitened rows. -/
theorem leaf_leaf_correlation (d : ℕ) (hd : 2 ≤ d) (c rho : ℝ) (i j : Fin d) :
    @inner ℝ (WhiteStar d) _ (leafVector d hd c rho i) (leafVector d hd c rho j) =
      c ^ 2 + rho ^ 2 * (if i = j then 1 else -1 / ((d : ℝ) - 1)) := by
  simp only [leafVector, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, starRingEnd_apply, star_trivial, root_inner_root, root_inner_transverse,
    transverse_inner_root, transverse_inner_transverse]
  ring

/-- The actual fixed edge observation projection, independent of λ. -/
def edgeProjection (d : ℕ) (hd : 2 ≤ d) (i : Fin d) : WhiteStar d →ₗ[ℝ] WhiteStar d where
  toFun y := (WithLp.equiv 2 _).symm (y.fst,
    (@inner ℝ (Transverse d) _ (simplex d hd i) y.snd) • simplex d hd i)
  map_add' x y := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext <;> simp [inner_add_right, add_smul]
  map_smul' c y := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext <;> simp [inner_smul_right, smul_smul]

@[simp] theorem edgeProjection_fst (d : ℕ) (hd : 2 ≤ d) (i : Fin d) (y : WhiteStar d) :
    (edgeProjection d hd i y).fst = y.fst := rfl

@[simp] theorem edgeProjection_snd (d : ℕ) (hd : 2 ≤ d) (i : Fin d) (y : WhiteStar d) :
    (edgeProjection d hd i y).snd =
      (@inner ℝ (Transverse d) _ (simplex d hd i) y.snd) • simplex d hd i := rfl

@[simp] theorem edgeProjection_idempotent (d : ℕ) (hd : 2 ≤ d) (i : Fin d) (y : WhiteStar d) :
    edgeProjection d hd i (edgeProjection d hd i y) = edgeProjection d hd i y := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · rfl
  · change (@inner ℝ (Transverse d) _ (simplex d hd i)
      ((@inner ℝ (Transverse d) _ (simplex d hd i) y.snd) • simplex d hd i)) • simplex d hd i = _
    rw [inner_smul_right, simplex_inner]
    simp

theorem edgeProjection_selfAdjoint (d : ℕ) (hd : 2 ≤ d) (i : Fin d) (x y : WhiteStar d) :
    @inner ℝ (WhiteStar d) _ (edgeProjection d hd i x) y =
      @inner ℝ (WhiteStar d) _ x (edgeProjection d hd i y) := by
  simp only [WithLp.prod_inner_apply, edgeProjection_fst, edgeProjection_snd,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
  rw [real_inner_comm x.snd (simplex d hd i)]
  ring

@[simp] theorem star_sum_fst {d ι : ℕ} (s : Finset (Fin ι)) (f : Fin ι → WhiteStar d) :
    (∑ i ∈ s, f i).fst = ∑ i ∈ s, (f i).fst := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, ih]

@[simp] theorem star_sum_snd {d ι : ℕ} (s : Finset (Fin ι)) (f : Fin ι → WhiteStar d) :
    (∑ i ∈ s, f i).snd = ∑ i ∈ s, (f i).snd := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, ih]

/-- The sum of edge projections has the two exact eigenvalues d and d/(d−1)
on the scalar and transverse blocks. Their separation is used by the tensor
kernel argument in fourth-chaos coercivity. -/
theorem edgeProjection_sum (d : ℕ) (hd : 2 ≤ d) (y : WhiteStar d) :
    (∑ i : Fin d, edgeProjection d hd i y) =
      (WithLp.equiv 2 _).symm ((d : ℝ) * y.fst, ((d : ℝ) / ((d : ℝ) - 1)) • y.snd) := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · change (∑ i : Fin d, edgeProjection d hd i y).fst = (d : ℝ) * y.fst
    simp
  · change (∑ i : Fin d, edgeProjection d hd i y).snd = _
    simp only [star_sum_snd, edgeProjection_snd]
    exact simplex_frame d hd y.snd

/-- An actual physical star vector, as a linear map from the fixed whitened
Euclidean space. Gaussian covariance is the Gram matrix of these rows. -/
def physicalLinearMap (d : ℕ) (hd : 2 ≤ d) (c rho : ℝ) :
    WhiteStar d →ₗ[ℝ] EuclideanSpace ℝ (Option (Fin d)) where
  toFun y := (WithLp.equiv 2 _).symm (fun idx => match idx with
    | none => y.fst
    | some i => c * y.fst + rho * @inner ℝ (Transverse d) _ (simplex d hd i) y.snd)
  map_add' x y := by
    ext idx
    cases idx with
    | none => simp
    | some i => simp [inner_add_right]; ring
  map_smul' a y := by
    ext idx
    cases idx with
    | none => simp
    | some i => simp [inner_smul_right]; ring

@[simp] theorem physicalLinearMap_root (d : ℕ) (hd : 2 ≤ d) (c rho : ℝ) (y : WhiteStar d) :
    physicalLinearMap d hd c rho y none = y.fst := rfl

@[simp] theorem physicalLinearMap_leaf (d : ℕ) (hd : 2 ≤ d) (c rho : ℝ) (y : WhiteStar d) (i : Fin d) :
    physicalLinearMap d hd c rho y (some i) = c * y.fst +
      rho * @inner ℝ (Transverse d) _ (simplex d hd i) y.snd := rfl

/-- The literal regular-graph eigenvector star constraint is automatic under
whitening: the sum of the leaves is λ times the root when λ=d c. -/
theorem physical_star_constraint (d : ℕ) (hd : 2 ≤ d) (c rho : ℝ) (y : WhiteStar d) :
    (∑ i : Fin d, physicalLinearMap d hd c rho y (some i)) =
      ((d : ℝ) * c) * physicalLinearMap d hd c rho y none := by
  have hs : (∑ i : Fin d, @inner ℝ (Transverse d) _ (simplex d hd i) y.snd) = 0 := by
    rw [← sum_inner, simplex_sum, inner_zero_left]
  simp only [physicalLinearMap_leaf, physicalLinearMap_root, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum, hs, mul_zero, add_zero]
  ring

/-- The scalar and transverse eigenvalues of L*L, expressed as an exact norm
identity for the concrete whitening map. -/
theorem physicalLinearMap_norm_sq (d : ℕ) (hd : 2 ≤ d) (c rho : ℝ) (y : WhiteStar d) :
    ‖physicalLinearMap d hd c rho y‖ ^ 2 =
      (1 + (d : ℝ) * c ^ 2) * y.fst ^ 2 +
        ((d : ℝ) * rho ^ 2 / ((d : ℝ) - 1)) * ‖y.snd‖ ^ 2 := by
  have hs : (∑ i : Fin d, @inner ℝ (Transverse d) _ (simplex d hd i) y.snd) = 0 := by
    rw [← sum_inner, simplex_sum, inner_zero_left]
  have hterm (i : Fin d) :
      (c * y.fst + rho * @inner ℝ (Transverse d) _ (simplex d hd i) y.snd) ^ 2 =
      c ^ 2 * y.fst ^ 2 + (2 * c * y.fst * rho) * @inner ℝ (Transverse d) _ (simplex d hd i) y.snd +
        rho ^ 2 * (@inner ℝ (Transverse d) _ (simplex d hd i) y.snd) ^ 2 := by ring
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply, Fintype.sum_option]
  simp only [RCLike.inner_apply, conj_trivial, physicalLinearMap_root, physicalLinearMap_leaf]
  simp_rw [← pow_two, hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hs, mul_zero, add_zero,
    simplex_parseval]
  ring

end GeneralizedBulk.Entropy.Channel
