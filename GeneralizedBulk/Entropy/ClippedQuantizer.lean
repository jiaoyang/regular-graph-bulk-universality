import GeneralizedBulk.Entropy.QuantizerBoundaries

/-! The actual clipped integer-grid quantizer, its finite palette, and its
complete finite set of scalar jump boundaries. -/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Entropy

def clipInteger (K : ℕ) (j : ℤ) : ℤ := max (-(K : ℤ)) (min ((K : ℤ)-1) j)

abbrev ClipLabel (K : ℕ) := (Finset.Icc (-(K : ℤ)) ((K : ℤ)-1) : Finset ℤ)

theorem clipInteger_lower (K : ℕ) (j : ℤ) : -(K : ℤ) ≤ clipInteger K j := le_max_left _ _

theorem clipInteger_upper (K : ℕ) (hK : 0 < K) (j : ℤ) : clipInteger K j ≤ (K : ℤ)-1 :=
  max_le (by omega) (min_le_left _ _)

theorem clipInteger_eq_self (K : ℕ) (j : ℤ) (hj0 : -(K : ℤ) ≤ j) (hj1 : j ≤ (K : ℤ)-1) :
    clipInteger K j = j := by rw [clipInteger,min_eq_right hj1,max_eq_right hj0]

theorem clipInteger_mono (K : ℕ) : Monotone (clipInteger K) :=
  fun x y hxy => max_le_max_left _ (min_le_min_left _ hxy)

def clipLabel (K : ℕ) (hK : 0 < K) (j : ℤ) : ClipLabel K :=
  ⟨clipInteger K j,Finset.mem_Icc.mpr ⟨clipInteger_lower K j,clipInteger_upper K hK j⟩⟩

theorem clipLabel_card (K : ℕ) : Fintype.card (ClipLabel K) = 2*K := by
  rw [Fintype.card_coe,Int.card_Icc]
  omega

def clipLabelEquivFin (K : ℕ) : ClipLabel K ≃ Fin (2*K) := Fintype.equivFinOfCardEq (clipLabel_card K)

def clippedGridLabel (a : ℝ) (K : ℕ) (hK : 0 < K) (x : ℝ) : ClipLabel K := clipLabel K hK ⌊x/a⌋

def codedClippedGridLabel (a : ℝ) (K : ℕ) (hK : 0 < K) (x : ℝ) : Fin (2*K) :=
  clipLabelEquivFin K (clippedGridLabel a K hK x)

theorem measurable_clippedGridLabel (a : ℝ) (K : ℕ) (hK : 0 < K) : Measurable (clippedGridLabel a K hK) :=
  (measurable_of_countable (clipLabel K hK)).comp (by fun_prop)

theorem measurable_codedClippedGridLabel (a : ℝ) (K : ℕ) (hK : 0 < K) : Measurable (codedClippedGridLabel a K hK) :=
  (measurable_of_finite (clipLabelEquivFin K)).comp (measurable_clippedGridLabel a K hK)

def clippedGridBoundaries (a : ℝ) (K : ℕ) : Finset ℝ :=
  (Finset.Icc (-(K : ℤ)+1) ((K : ℤ)-1)).image (fun b : ℤ => (b : ℝ)*a)

theorem clippedGridBoundaries_card_le (a : ℝ) (K : ℕ) : (clippedGridBoundaries a K).card ≤ 2*K := by
  apply Finset.card_image_le.trans
  rw [← clipLabel_card K,Fintype.card_coe]
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_Icc] at hj ⊢
  omega

theorem clipInteger_le_of_strict_lower (K : ℕ) (hK : 0 < K) (j : ℤ)
    (h : -(K : ℤ) < clipInteger K j) : clipInteger K j ≤ j := by
  by_cases hj : -(K : ℤ) ≤ j
  · exact max_le hj (min_le_right _ _)
  · have hjU : j ≤ (K : ℤ)-1 := by omega
    rw [clipInteger,min_eq_right hjU,max_eq_left (le_of_not_ge hj)] at h
    exact False.elim (lt_irrefl _ h)

theorem le_clipInteger_of_strict_upper (K : ℕ) (hK : 0 < K) (j : ℤ)
    (h : clipInteger K j < (K : ℤ)-1) : j ≤ clipInteger K j := by
  by_cases hj : j ≤ (K : ℤ)-1
  · rw [clipInteger,min_eq_right hj]
    exact le_max_right _ _
  · have hU : -(K : ℤ) ≤ (K : ℤ)-1 := by omega
    rw [clipInteger,min_eq_left (le_of_not_ge hj),max_eq_right hU] at h
    exact False.elim (lt_irrefl _ h)

set_option maxHeartbeats 1000000 in
theorem clippedGrid_boundary_between_of_lt (a : ℝ) (ha : 0 < a) (K : ℕ) (hK : 0 < K)
    (x y : ℝ) (hxy : x ≤ y) (hne : clippedGridLabel a K hK x ≠ clippedGridLabel a K hK y) :
    ∃ b ∈ clippedGridBoundaries a K,x ≤ b ∧ b ≤ y := by
  have hfloor : ⌊x/a⌋ ≤ ⌊y/a⌋ := Int.floor_mono (div_le_div_of_nonneg_right hxy ha.le)
  have hclip : clipInteger K ⌊x/a⌋ < clipInteger K ⌊y/a⌋ := by
    apply lt_of_le_of_ne (clipInteger_mono K hfloor)
    intro he
    exact hne (Subtype.ext he)
  let b : ℤ := clipInteger K ⌊x/a⌋+1
  have hb0 : -(K : ℤ)+1 ≤ b := by dsimp [b]; have h := clipInteger_lower K ⌊x/a⌋; omega
  have hb1 : b ≤ (K : ℤ)-1 := by dsimp [b]; have h := clipInteger_upper K hK ⌊y/a⌋; omega
  have hxb : ⌊x/a⌋ < b := by
    have hupper : clipInteger K ⌊x/a⌋ < (K : ℤ)-1 := hclip.trans_le (clipInteger_upper K hK _)
    have hle := le_clipInteger_of_strict_upper K hK ⌊x/a⌋ hupper
    dsimp [b]
    omega
  have hby : b ≤ ⌊y/a⌋ := by
    have hlower : -(K : ℤ) < clipInteger K ⌊y/a⌋ := (clipInteger_lower K _).trans_lt hclip
    have hle := clipInteger_le_of_strict_lower K hK ⌊y/a⌋ hlower
    dsimp [b]
    omega
  refine ⟨(b : ℝ)*a,Finset.mem_image.mpr ⟨b,Finset.mem_Icc.mpr ⟨hb0,hb1⟩,rfl⟩,?_,?_⟩
  · exact le_of_lt ((div_lt_iff₀ ha).mp (Int.floor_lt.mp hxb))
  · exact (le_div_iff₀ ha).mp (Int.le_floor.mp hby)

theorem clippedGrid_has_boundaries (a : ℝ) (ha : 0 < a) (K : ℕ) (hK : 0 < K) :
    HasQuantizerBoundaries (clippedGridLabel a K hK) (clippedGridBoundaries a K) := by
  intro x y hne
  rcases le_total x y with hxy | hyx
  · obtain ⟨b,hb,hxb,hby⟩ := clippedGrid_boundary_between_of_lt a ha K hK x y hxy hne
    exact ⟨b,hb,by simpa only [min_eq_left hxy] using hxb,by simpa only [max_eq_right hxy] using hby⟩
  · obtain ⟨b,hb,hyb,hbx⟩ := clippedGrid_boundary_between_of_lt a ha K hK y x hyx hne.symm
    exact ⟨b,hb,by simpa only [min_eq_right hyx] using hyb,by simpa only [max_eq_left hyx] using hbx⟩

theorem codedClippedGrid_has_boundaries (a : ℝ) (ha : 0 < a) (K : ℕ) (hK : 0 < K) :
    HasQuantizerBoundaries (codedClippedGridLabel a K hK) (clippedGridBoundaries a K) := by
  intro x y hne
  apply clippedGrid_has_boundaries a ha K hK x y
  intro he
  exact hne (congrArg (clipLabelEquivFin K) he)

end GeneralizedBulk.Entropy
