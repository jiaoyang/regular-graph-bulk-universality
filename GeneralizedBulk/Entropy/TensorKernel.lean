import GeneralizedBulk.Entropy.ColoredChannels

/-! The mixed-derivative kernel, proved directly by trilinearity and the simplex. -/
noncomputable section
open scoped BigOperators

namespace GeneralizedBulk.Entropy.Tensor

abbrev Trilinear (E : Type*) [AddCommGroup E] [Module ℝ E] :=
  E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem commute_of_mixed (T : Trilinear E) (P : E →ₗ[ℝ] E)
    (hs : ∀ x y z, T x y z = T y x z)
    (hm : ∀ x y z, T (x - P x) (P y) z = 0) (x y z : E) :
    T (P x) y z = T x (P y) z := by
  have h1 := hm x y z
  have h2 := hm y x z
  rw [← hs (P x) (y - P y) z] at h2
  simp only [map_sub, LinearMap.sub_apply] at h1 h2
  linarith

/-- Distinct eigenspaces of the sum of the projections cannot interact in a
trilinear form satisfying the actual mixed-kernel condition. -/
theorem spectral_separation {J : Type*} [Fintype J]
    (T : Trilinear E) (P : J → E →ₗ[ℝ] E)
    (hc : ∀ i x y z, T (P i x) y z = T x (P i y) z)
    (x y z : E) (lambda nu : ℝ) (hne : lambda ≠ nu)
    (hx : (∑ i, P i x) = lambda • x) (hy : (∑ i, P i y) = nu • y) :
    T x y z = 0 := by
  have h : lambda * T x y z = nu * T x y z := by
    calc
      _ = T (∑ i, P i x) y z := by rw [hx]; simp
      _ = ∑ i, T (P i x) y z := by simp
      _ = ∑ i, T x (P i y) z := Finset.sum_congr rfl (fun i _ => hc i x y z)
      _ = T x (∑ i, P i y) z := by simp
      _ = _ := by rw [hy]; simp
  have hz : (lambda - nu) * T x y z = 0 := by nlinarith
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

end GeneralizedBulk.Entropy.Tensor

namespace GeneralizedBulk.Entropy.Channel
open GeneralizedBulk.Entropy.Tensor

def scalarPart (d k : ℕ) : ColoredStar d k →ₗ[ℝ] ColoredStar d k where
  toFun y := (WithLp.equiv 2 _).symm (fun a => (WithLp.equiv 2 _).symm ((y a).fst, 0))
  map_add' x y := by ext a; apply (WithLp.equiv 2 _).injective; apply Prod.ext <;> simp
  map_smul' c y := by ext a; apply (WithLp.equiv 2 _).injective; apply Prod.ext <;> simp

def transversePart (d k : ℕ) : ColoredStar d k →ₗ[ℝ] ColoredStar d k where
  toFun y := (WithLp.equiv 2 _).symm (fun a => (WithLp.equiv 2 _).symm (0, (y a).snd))
  map_add' x y := by ext a; apply (WithLp.equiv 2 _).injective; apply Prod.ext <;> simp
  map_smul' c y := by ext a; apply (WithLp.equiv 2 _).injective; apply Prod.ext <;> simp

theorem scalarPart_add_transversePart (d k : ℕ) (x : ColoredStar d k) :
    scalarPart d k x + transversePart d k x = x := by
  ext a
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext <;> simp [scalarPart, transversePart]

theorem coloredEdgeProjection_scalarPart (d k : ℕ) (hd : 2 ≤ d)
    (i : Fin d) (x : ColoredStar d k) :
    coloredEdgeProjection d k hd i (scalarPart d k x) = scalarPart d k x := by
  ext a
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext <;> simp [scalarPart, coloredEdgeProjection, edgeProjection]

theorem coloredEdgeProjection_scalar_sum (d k : ℕ) (hd : 2 ≤ d) (x : ColoredStar d k) :
    (∑ i : Fin d, coloredEdgeProjection d k hd i (scalarPart d k x)) =
      (d : ℝ) • scalarPart d k x := by
  simp only [coloredEdgeProjection_scalarPart, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact_mod_cast (rfl : d • scalarPart d k x = d • scalarPart d k x)

theorem coloredEdgeProjection_transverse_sum (d k : ℕ) (hd : 2 ≤ d) (x : ColoredStar d k) :
    (∑ i : Fin d, coloredEdgeProjection d k hd i (transversePart d k x)) =
      ((d : ℝ) / ((d : ℝ) - 1)) • transversePart d k x := by
  ext a
  have hsum (t : Finset (Fin d)) :
      (∑ i ∈ t, coloredEdgeProjection d k hd i (transversePart d k x)) a =
        ∑ i ∈ t, (coloredEdgeProjection d k hd i (transversePart d k x)) a := by
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih => simp [Finset.sum_insert hi, PiLp.add_apply, ih]
  rw [hsum Finset.univ]
  change (∑ i : Fin d, edgeProjection d hd i ((transversePart d k x) a)) = _
  rw [edgeProjection_sum]
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext <;> simp [transversePart]

theorem trilinear_scalar_transverse_zero (d k : ℕ) (hd : 3 ≤ d)
    (T : Trilinear (ColoredStar d k))
    (hs : ∀ x y z, T x y z = T y x z)
    (hm : ∀ i : Fin d, ∀ x y z,
      T (x - coloredEdgeProjection d k (by omega) i x)
        (coloredEdgeProjection d k (by omega) i y) z = 0)
    (x y z : ColoredStar d k) :
    T (scalarPart d k x) (transversePart d k y) z = 0 := by
  apply spectral_separation T (coloredEdgeProjection d k (by omega))
    (fun i => commute_of_mixed T _ hs (hm i)) _ _ z (d : ℝ) ((d : ℝ) / ((d : ℝ) - 1))
  · have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    intro he
    have hh := (eq_div_iff (show (d : ℝ) - 1 ≠ 0 by linarith)).mp he
    nlinarith
  · exact coloredEdgeProjection_scalar_sum d k (by omega) x
  · exact coloredEdgeProjection_transverse_sum d k (by omega) y

def transverseBlock (d k : ℕ) (a : Fin k) : Transverse d →ₗ[ℝ] ColoredStar d k where
  toFun u := blockVector d k a ((WithLp.equiv 2 _).symm (0, u))
  map_add' u v := by
    ext b
    by_cases h : b = a
    · simp only [blockVector_apply, h, ↓reduceIte, PiLp.add_apply]
      apply (WithLp.equiv 2 _).injective
      apply Prod.ext <;> simp
    · simp [blockVector_apply, h]
  map_smul' c u := by
    ext b
    by_cases h : b = a
    · simp only [blockVector_apply, h, ↓reduceIte, PiLp.smul_apply]
      apply (WithLp.equiv 2 _).injective
      apply Prod.ext <;> simp
    · simp [blockVector_apply, h]

theorem coloredEdgeProjection_transverseBlock (d k : ℕ) (hd : 2 ≤ d)
    (i : Fin d) (a : Fin k) (u : Transverse d) :
    coloredEdgeProjection d k hd i (transverseBlock d k a u) =
      transverseBlock d k a ((@inner ℝ (Transverse d) _ (simplex d hd i) u) • simplex d hd i) := by
  ext b
  by_cases h : b = a
  · simp only [coloredEdgeProjection_apply, transverseBlock, LinearMap.coe_mk, AddHom.coe_mk,
      blockVector_apply, h, ↓reduceIte]
    rfl
  · simp [coloredEdgeProjection_apply, transverseBlock, blockVector_apply, h]

theorem colored_sum_apply {J : Type*} (d k : ℕ) (s : Finset J)
    (f : J → ColoredStar d k) (a : Fin k) :
    (∑ j ∈ s, f j) a = ∑ j ∈ s, f j a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => simp [Finset.sum_insert hj, PiLp.add_apply, ih]

theorem transversePart_eq_sum_transverseBlock (d k : ℕ) (x : ColoredStar d k) :
    transversePart d k x = ∑ a : Fin k, transverseBlock d k a (x a).snd := by
  classical
  ext b
  rw [colored_sum_apply]
  simp [transversePart, transverseBlock, blockVector_apply, Finset.sum_ite_eq']

section Mixed
variable (d k : ℕ) (hd : 3 ≤ d) (T : Trilinear (ColoredStar d k))
variable (hs : ∀ x y z, T x y z = T y x z)
variable (hm : ∀ i : Fin d, ∀ x y z,
  T (x - coloredEdgeProjection d k (by omega) i x)
    (coloredEdgeProjection d k (by omega) i y) z = 0)

include hs hm in
theorem trilinear_transverse_simplex (a b : Fin k) (i : Fin d)
    (u : Transverse d) (z : ColoredStar d k) :
    T (transverseBlock d k a u) (transverseBlock d k b (simplex d (by omega) i)) z =
      (@inner ℝ (Transverse d) _ (simplex d (by omega) i) u) *
        T (transverseBlock d k a (simplex d (by omega) i))
          (transverseBlock d k b (simplex d (by omega) i)) z := by
  have h := commute_of_mixed T (coloredEdgeProjection d k (by omega) i) hs (hm i)
    (transverseBlock d k a u) (transverseBlock d k b (simplex d (by omega) i)) z
  simp only [coloredEdgeProjection_transverseBlock, simplex_inner, ↓reduceIte, one_smul,
    map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  exact h.symm

include hs hm in
/-- The common transverse bilinear coefficient is independent of the simplex
vertex. The nonzero off-diagonal correlation is used explicitly. -/
theorem trilinear_simplex_diagonal_constant (a b : Fin k) (i j : Fin d)
    (z : ColoredStar d k) :
    T (transverseBlock d k a (simplex d (by omega) i))
      (transverseBlock d k b (simplex d (by omega) i)) z =
    T (transverseBlock d k a (simplex d (by omega) j))
      (transverseBlock d k b (simplex d (by omega) j)) z := by
  by_cases hij : i = j
  · subst j; rfl
  have hi := trilinear_transverse_simplex d k hd T hs hm a b i (simplex d (by omega) j) z
  have hj := trilinear_transverse_simplex d k hd T hs hm b a j (simplex d (by omega) i) z
  rw [hs] at hj
  have hswap := hs (transverseBlock d k b (simplex d (by omega) j))
    (transverseBlock d k a (simplex d (by omega) j)) z
  rw [hswap] at hj
  rw [simplex_inner, if_neg hij] at hi
  rw [simplex_inner, if_neg (Ne.symm hij)] at hj
  have hc : (-1 / ((d : ℝ) - 1)) ≠ 0 := by
    have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    exact div_ne_zero (by norm_num) (by linarith)
  apply mul_left_cancel₀ hc
  exact hi.symm.trans hj

include hs hm in
theorem trilinear_transverse_factor (a b : Fin k) (i0 : Fin d)
    (u v : Transverse d) (z : ColoredStar d k) :
    T (transverseBlock d k a u) (transverseBlock d k b v) z =
      (@inner ℝ (Transverse d) _ u v) *
        T (transverseBlock d k a (simplex d (by omega) i0))
          (transverseBlock d k b (simplex d (by omega) i0)) z := by
  have hframe := simplex_frame d (show 2 ≤ d by omega) v
  have he := congrArg (fun t : Transverse d =>
    T (transverseBlock d k a u) (transverseBlock d k b t) z) hframe
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul] at he
  have hvertex (i : Fin d) := trilinear_simplex_diagonal_constant d k hd T hs hm a b i i0 z
  have hsum : (∑ i : Fin d, (@inner ℝ (Transverse d) _ (simplex d (by omega) i) v) *
      T (transverseBlock d k a u) (transverseBlock d k b (simplex d (by omega) i)) z) =
      ∑ i : Fin d, ((@inner ℝ (Transverse d) _ (simplex d (by omega) i) v) *
        (@inner ℝ (Transverse d) _ (simplex d (by omega) i) u)) *
          T (transverseBlock d k a (simplex d (by omega) i0))
            (transverseBlock d k b (simplex d (by omega) i0)) z := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [trilinear_transverse_simplex d k hd T hs hm a b i u z, hvertex i]
    ring
  rw [hsum] at he
  rw [← Finset.sum_mul] at he
  have hip := congrArg (fun t : Transverse d => @inner ℝ (Transverse d) _ u t) hframe
  simp only [inner_sum, inner_smul_right, smul_eq_mul] at hip
  have hcomm (i : Fin d) := real_inner_comm (simplex d (show 2 ≤ d by omega) i) u
  simp_rw [hcomm] at hip
  rw [hip] at he
  have hc : (d : ℝ) / ((d : ℝ) - 1) ≠ 0 := by
    have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    exact div_ne_zero (by linarith) (by linarith)
  apply mul_left_cancel₀ hc
  nlinarith only [he]

include hs hm in
theorem trilinear_transverse_coefficient_zero
    (hsyz : ∀ x y z, T x y z = T x z y)
    (a b c : Fin k) (i0 l : Fin d) :
    T (transverseBlock d k a (simplex d (by omega) i0))
      (transverseBlock d k b (simplex d (by omega) i0))
      (transverseBlock d k c (simplex d (by omega) l)) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j : Fin d, j ≠ l := by
    by_cases hl : l.val = 0
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro h
      have hv := congrArg Fin.val h
      simp only at hv
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro h
      have hv := congrArg Fin.val h
      simp only at hv
      omega
  let r : ℝ := @inner ℝ (Transverse d) _ (simplex d (by omega) l) (simplex d (by omega) j)
  let v : Transverse d := simplex d (by omega) j - r • simplex d (by omega) l
  have hr : r = -1 / ((d : ℝ) - 1) := by
    simp only [r, simplex_inner, if_neg (Ne.symm hj)]
  have hr2 : r ^ 2 < 1 := by
    have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    rw [hr, div_pow]
    norm_num only [neg_one_sq]
    apply (div_lt_one (by nlinarith : (0 : ℝ) < ((d : ℝ) - 1) ^ 2)).2
    nlinarith
  have hvortho : @inner ℝ (Transverse d) _ v (simplex d (by omega) l) = 0 := by
    simp only [v, inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial,
      simplex_inner, if_neg hj, ↓reduceIte, mul_one, hr]
    ring
  have hvnorm : ‖v‖ ^ 2 = 1 - r ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [v, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_trivial, simplex_inner, if_neg hj, if_neg (Ne.symm hj),
      ↓reduceIte, hr]
    ring
  have hvpos : 0 < ‖v‖ ^ 2 := by rw [hvnorm]; linarith
  have h := hsyz (transverseBlock d k a v) (transverseBlock d k b v)
    (transverseBlock d k c (simplex d (by omega) l))
  rw [trilinear_transverse_factor d k hd T hs hm a b i0 v v,
    trilinear_transverse_factor d k hd T hs hm a c i0 v (simplex d (by omega) l),
    hvortho, zero_mul, real_inner_self_eq_norm_sq] at h
  exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hvpos)

include hs hm in
theorem trilinear_transverse_blocks_zero
    (hsyz : ∀ x y z, T x y z = T x z y)
    (a b c : Fin k) (u v w : Transverse d) :
    T (transverseBlock d k a u) (transverseBlock d k b v) (transverseBlock d k c w) = 0 := by
  let i0 : Fin d := ⟨0, by omega⟩
  have hz : T (transverseBlock d k a (simplex d (by omega) i0))
      (transverseBlock d k b (simplex d (by omega) i0)) (transverseBlock d k c w) = 0 := by
    have hframe := simplex_frame d (show 2 ≤ d by omega) w
    have h := congrArg (fun t : Transverse d =>
      T (transverseBlock d k a (simplex d (by omega) i0))
        (transverseBlock d k b (simplex d (by omega) i0)) (transverseBlock d k c t)) hframe
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul] at h
    simp_rw [trilinear_transverse_coefficient_zero d k hd T hs hm hsyz a b c i0] at h
    simp only [mul_zero, Finset.sum_const_zero] at h
    have hc : (d : ℝ) / ((d : ℝ) - 1) ≠ 0 := by
      have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
      exact div_ne_zero (by linarith) (by linarith)
    exact (mul_eq_zero.mp h.symm).resolve_left hc
  rw [trilinear_transverse_factor d k hd T hs hm a b i0 u v, hz, mul_zero]

include hs hm in
theorem trilinear_transverse_parts_zero
    (hsyz : ∀ x y z, T x y z = T x z y) (x y z : ColoredStar d k) :
    T (transversePart d k x) (transversePart d k y) (transversePart d k z) = 0 := by
  rw [transversePart_eq_sum_transverseBlock, transversePart_eq_sum_transverseBlock,
    transversePart_eq_sum_transverseBlock]
  simp only [map_sum, LinearMap.sum_apply]
  simp_rw [trilinear_transverse_blocks_zero d k hd T hs hm hsyz]
  simp

include hs hm in
theorem trilinear_transverse_first_zero
    (hsyz : ∀ x y z, T x y z = T x z y) (x y z : ColoredStar d k) :
    T (transversePart d k x) y z = 0 := by
  have h1 : T (transversePart d k x) (scalarPart d k y) (scalarPart d k z) = 0 := by
    rw [hs]
    exact trilinear_scalar_transverse_zero d k hd T hs hm y x _
  have h2 : T (transversePart d k x) (scalarPart d k y) (transversePart d k z) = 0 := by
    rw [hs]
    exact trilinear_scalar_transverse_zero d k hd T hs hm y x _
  have h3 : T (transversePart d k x) (transversePart d k y) (scalarPart d k z) = 0 := by
    rw [hsyz, hs]
    exact trilinear_scalar_transverse_zero d k hd T hs hm z x _
  have h4 := trilinear_transverse_parts_zero d k hd T hs hm hsyz x y z
  calc
    _ = T (transversePart d k x) (scalarPart d k y + transversePart d k y)
      (scalarPart d k z + transversePart d k z) := by
        rw [scalarPart_add_transversePart, scalarPart_add_transversePart]
    _ = 0 := by simp only [map_add, LinearMap.add_apply, h1, h2, h3, h4, add_zero]

include hs hm in
/-- The source mixed-derivative kernel: a symmetric trilinear form with no
mixed block across any actual edge projection depends only on scalar colors. -/
theorem mixed_third_derivative_kernel
    (hsyz : ∀ x y z, T x y z = T x z y) (x y z : ColoredStar d k) :
    T x y z = T (scalarPart d k x) (scalarPart d k y) (scalarPart d k z) := by
  have hzero (u v w : ColoredStar d k) := trilinear_transverse_first_zero d k hd T hs hm hsyz u v w
  have hx : T x y z = T (scalarPart d k x) y z := by
    calc
      _ = T (scalarPart d k x + transversePart d k x) y z := by rw [scalarPart_add_transversePart]
      _ = _ := by simp only [map_add, LinearMap.add_apply, hzero, add_zero]
  have hy : T (scalarPart d k x) y z = T (scalarPart d k x) (scalarPart d k y) z := by
    calc
      _ = T (scalarPart d k x) (scalarPart d k y + transversePart d k y) z := by
        rw [scalarPart_add_transversePart]
      _ = _ := by
        rw [map_add, LinearMap.add_apply, hs (scalarPart d k x) (transversePart d k y) z, hzero]
        simp
  have hz : T (scalarPart d k x) (scalarPart d k y) z =
      T (scalarPart d k x) (scalarPart d k y) (scalarPart d k z) := by
    calc
      _ = T (scalarPart d k x) (scalarPart d k y) (scalarPart d k z + transversePart d k z) := by
        rw [scalarPart_add_transversePart]
      _ = _ := by
        rw [map_add, hsyz (scalarPart d k x) (scalarPart d k y) (transversePart d k z),
          hs (scalarPart d k x) (transversePart d k z) (scalarPart d k y), hzero]
        simp
  exact hx.trans (hy.trans hz)

end Mixed

end GeneralizedBulk.Entropy.Channel
