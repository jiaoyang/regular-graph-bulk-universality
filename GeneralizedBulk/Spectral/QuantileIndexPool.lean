import GeneralizedBulk.Spectral.KestenMcKayQuantileContinuity

/-! A literal deterministic pool of distinct nonzero finite indices at any
fixed interior upper-tail fraction. No graph or spectral premise is used. -/
noncomputable section
open Filter
open scoped Topology Classical
namespace GeneralizedBulk.Spectral

def indexPoolBase (v : ℝ) (N : ℕ) : ℕ := Nat.floor (v * N)

def indexPoolReady (v : ℝ) (k N : ℕ) : Prop := indexPoolBase v N + k < N

def indexPool (v : ℝ) (k N : ℕ) (hN : 0 < N) (j : Fin k) : Fin N :=
  if h : indexPoolReady v k N then ⟨indexPoolBase v N + j.val + 1, by
    dsimp [indexPoolReady] at h
    omega⟩ else ⟨0,hN⟩

theorem indexPool_eventually_ready (v : ℝ) (hv : v ∈ Set.Ioo (0 : ℝ) 1) (k : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    ∀ᶠ n in atTop, indexPoolReady v k (N n) := by
  have hn := (tendsto_natCast_atTop_atTop.comp hN).eventually_gt_atTop ((k : ℝ)/(1-v))
  filter_upwards [hn] with n hn
  have hv1 : v < 1 := hv.2
  change (k : ℝ)/(1-v) < (N n : ℝ) at hn
  have hf := Nat.floor_le (mul_nonneg hv.1.le (Nat.cast_nonneg (N n)))
  have hh : (indexPoolBase v (N n) : ℝ) + k < N n := by
    dsimp [indexPoolBase]
    have ht := (div_lt_iff₀ (by linarith : 0 < 1-v)).mp hn
    nlinarith
  exact_mod_cast hh

theorem indexPool_injective (v : ℝ) (k N : ℕ) (hN : 0 < N) (hready : indexPoolReady v k N) :
    Function.Injective (indexPool v k N hN) := by
  intro a b hab
  apply Fin.ext
  have hh := congrArg Fin.val hab
  simp only [indexPool, dif_pos hready] at hh
  omega

theorem indexPool_ne_zero (v : ℝ) (k N : ℕ) (hN : 0 < N) (hready : indexPoolReady v k N) (j : Fin k) :
    (indexPool v k N hN j).val ≠ 0 := by
  simp only [indexPool, dif_pos hready]
  omega

theorem indexPool_error (v : ℝ) (hv : 0 ≤ v) (k N : ℕ) (hN : 0 < N)
    (hready : indexPoolReady v k N) (j : Fin k) :
    |((indexPool v k N hN j).val : ℝ) - v*N| ≤ k+1 := by
  have hf := Nat.floor_le (mul_nonneg hv (Nat.cast_nonneg N))
  have hfl := Nat.lt_floor_add_one (v*(N : ℝ))
  have hj : (j.val : ℝ)+1 ≤ k := by exact_mod_cast j.isLt
  simp only [indexPool, dif_pos hready, indexPoolBase, Nat.cast_add, Nat.cast_one]
  rw [abs_of_nonneg (by linarith [(Nat.cast_nonneg j.val : 0 ≤ (j.val : ℝ))] : 0 ≤ (Nat.floor (v*(N : ℝ)) : ℝ)+j.val+1-v*N)]
  linarith

theorem indexPool_ratio_error (v : ℝ) (hv : 0 ≤ v) (k N : ℕ) (hN : 0 < N)
    (hready : indexPoolReady v k N) (j : Fin k) :
    |((indexPool v k N hN j).val : ℝ)/(N : ℝ) - v| ≤ (k+1)/(N : ℝ) := by
  have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have he : ((indexPool v k N hN j).val : ℝ)/(N : ℝ) - v =
      (((indexPool v k N hN j).val : ℝ)-v*N)/(N : ℝ) := by field_simp <;> ring
  have hnpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  rw [he, abs_div, abs_of_pos hnpos]
  exact div_le_div_of_nonneg_right (indexPool_error v hv k N hN hready j) (Nat.cast_nonneg N)

theorem indexPool_ratio_tendsto (v : ℝ) (hv : v ∈ Set.Ioo (0 : ℝ) 1) (k : ℕ)
    (N : ℕ → ℕ) (hpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop) (j : Fin k) :
    Tendsto (fun n => ((indexPool v k (N n) (hpos n) j).val : ℝ)/(N n : ℝ)) atTop (𝓝 v) := by
  have he : Tendsto (fun n => ((k : ℝ)+1)/(N n : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)).const_mul ((k : ℝ)+1)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall := (tendsto_order.mp he).2 ε hε
  filter_upwards [indexPool_eventually_ready v hv k N hN, hsmall] with n hn hs
  simpa only [Real.dist_eq] using (indexPool_ratio_error v hv.1.le k (N n) (hpos n) hn j).trans_lt hs

end GeneralizedBulk.Spectral
