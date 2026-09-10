import AffineTverberg.UpperSubdivision

set_option linter.style.header false

/-!
# The crossing order of the facet hyperplanes along a ray

This file formalizes the *ordering* half of a line shelling.  Fix an exact
finite halfspace presentation `H` of a polytope `R`, a point `w` strictly
inside the `j`-th inequality, and a direction `d`.  Along the ray
`s ↦ w + s • d` the affine form of the inequality is `form j w + s * form j d`,
so

* the inequality is ever violated only if `form j d > 0`, and then exactly
  after the *crossing parameter* `crossParam j w d = (c - a(w)) / a(d)`
  (`isViolatedAt_line_iff`);
* the set of violated — that is, visible — facets therefore only grows as one
  moves out along the ray (`isViolatedAt_mono`), and the order in which
  facets become visible is the order of their crossing parameters
  (`crossParam_lt_iff_visible_earlier`);
* far out along the ray precisely the facets with `form j d > 0` are visible
  (`exists_ray_threshold`).

This is the combinatorial skeleton of the Bruggesser--Mani line shelling: the
shelling order of the visible facets is by increasing crossing parameter.  The
recursive statement that the new facet meets the union of the earlier ones in a
shelled ball of one lower dimension is *not* proved here; it remains the open
geometric input to a `ShellableGluing.CellShelling` certificate.

The strict-interior hypotheses below apply only after removing the dummy
`0 ≤ 0` inequalities present in `polytopalPresentation`. The unfiltered
`FacetIndex` cannot satisfy strictness for every index. Distinct crossing
parameters also require identifying duplicate supporting hyperplanes.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace CompactConvexProjection
namespace FiniteHalfspacePresentation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {J : Type*} [Finite J] {A : CompactConvexProjection E F}
  (H : FiniteHalfspacePresentation A (J := J))

omit [Finite J] in
/-- The affine form of an inequality is linear, hence affine along a ray. -/
theorem form_add_smul (j : J) (w d : F × ℝ) (s : ℝ) :
    H.form j (w + s • d) = H.form j w + s * H.form j d := by
  simp only [form, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    map_add, map_smul, smul_eq_mul]
  ring

/-- The parameter at which the ray `s ↦ w + s • d` crosses the `j`-th
hyperplane. -/
def crossParam (j : J) (w d : F × ℝ) : ℝ :=
  (H.bound j - H.form j w) / H.form j d

omit [Finite J] in
/-- **The crossing criterion.**  Starting strictly inside the `j`-th
inequality, the point at parameter `s ≥ 0` of the ray violates it exactly when
the direction increases the form and the crossing parameter has been
passed. -/
theorem isViolatedAt_line_iff {j : J} {w d : F × ℝ}
    (hw : H.form j w < H.bound j) {s : ℝ} (hs : 0 ≤ s) :
    H.IsViolatedAt j (w + s • d) ↔ 0 < H.form j d ∧ H.crossParam j w d < s := by
  rw [IsViolatedAt, H.form_add_smul j w d s]
  constructor
  · intro hviol
    have hpos : 0 < s * H.form j d := by linarith
    have hd : 0 < H.form j d := by
      rcases le_or_gt (H.form j d) 0 with hle | hgt
      · exact absurd hpos (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hs hle))
      · exact hgt
    refine ⟨hd, ?_⟩
    rw [crossParam, div_lt_iff₀ hd]
    linarith
  · rintro ⟨hd, hlt⟩
    rw [crossParam, div_lt_iff₀ hd] at hlt
    linarith

omit [Finite J] in
/-- Visibility only grows along the ray. -/
theorem isViolatedAt_mono {j : J} {w d : F × ℝ}
    (hw : H.form j w < H.bound j) {s s' : ℝ} (hs : 0 ≤ s) (hss : s ≤ s')
    (hviol : H.IsViolatedAt j (w + s • d)) : H.IsViolatedAt j (w + s' • d) := by
  obtain ⟨hd, hlt⟩ := (H.isViolatedAt_line_iff hw hs).1 hviol
  exact (H.isViolatedAt_line_iff hw (hs.trans hss)).2 ⟨hd, lt_of_lt_of_le hlt hss⟩

omit [Finite J] in
/-- **The shelling order is the order of the crossing parameters.**  Of two
facets crossed by the ray, the one with the smaller crossing parameter becomes
visible strictly earlier. -/
theorem crossParam_lt_iff_visible_earlier {j k : J} {w d : F × ℝ}
    (hwj : H.form j w < H.bound j) (hwk : H.form k w < H.bound k)
    (hj : 0 < H.form j d) (hk : 0 < H.form k d) :
    H.crossParam j w d < H.crossParam k w d ↔
      ∃ s : ℝ, 0 ≤ s ∧ H.IsViolatedAt j (w + s • d) ∧ ¬ H.IsViolatedAt k (w + s • d) := by
  have hjpos : 0 < H.crossParam j w d := by
    rw [crossParam]
    exact div_pos (by linarith) hj
  constructor
  · intro hlt
    refine ⟨(H.crossParam j w d + H.crossParam k w d) / 2, by linarith, ?_, ?_⟩
    · exact (H.isViolatedAt_line_iff hwj (by linarith)).2 ⟨hj, by linarith⟩
    · intro hviol
      obtain ⟨-, hgt⟩ := (H.isViolatedAt_line_iff hwk (by linarith)).1 hviol
      linarith
  · rintro ⟨s, hs, hjv, hkv⟩
    obtain ⟨-, hjlt⟩ := (H.isViolatedAt_line_iff hwj hs).1 hjv
    have hkle : ¬ H.crossParam k w d < s := fun hlt ↦
      hkv ((H.isViolatedAt_line_iff hwk hs).2 ⟨hk, hlt⟩)
    push Not at hkle
    linarith

/-- **Far out along the ray, exactly the facets whose form increases in the
direction `d` are visible.** -/
theorem exists_ray_threshold {w d : F × ℝ} (hw : ∀ j : J, H.form j w < H.bound j) :
    ∃ s₀ : ℝ, 0 ≤ s₀ ∧ ∀ s ≥ s₀, ∀ j : J,
      (H.IsViolatedAt j (w + s • d) ↔ 0 < H.form j d) := by
  classical
  have : Fintype J := Fintype.ofFinite J
  refine ⟨1 + ∑ j : J, |H.crossParam j w d|, ?_, ?_⟩
  · have : (0 : ℝ) ≤ ∑ j : J, |H.crossParam j w d| :=
      Finset.sum_nonneg fun j _ ↦ abs_nonneg _
    linarith
  · intro s hs j
    have hle : |H.crossParam j w d| ≤ ∑ k : J, |H.crossParam k w d| :=
      Finset.single_le_sum (f := fun k ↦ |H.crossParam k w d|)
        (fun k _ ↦ abs_nonneg _) (Finset.mem_univ j)
    have habs : H.crossParam j w d ≤ |H.crossParam j w d| := le_abs_self _
    have hsum : (0 : ℝ) ≤ ∑ k : J, |H.crossParam k w d| :=
      Finset.sum_nonneg fun k _ ↦ abs_nonneg _
    have hs0 : 0 ≤ s := by linarith
    rw [H.isViolatedAt_line_iff (hw j) hs0]
    constructor
    · exact fun h ↦ h.1
    · intro hd
      exact ⟨hd, by linarith⟩

omit [Finite J] in
/-- **The earlier facets are exactly those visible from the crossing point.**
At the parameter where the ray crosses the `k`-th hyperplane, the `j`-th
inequality is violated precisely when its crossing parameter is smaller.  This
is the combinatorial form of the statement that the overlap of a newly attached
facet with the previously attached ones is the part of its boundary visible
from the crossing point. -/
theorem isViolatedAt_crossParam_iff {j k : J} {w d : F × ℝ}
    (hwj : H.form j w < H.bound j) (hwk : H.form k w < H.bound k)
    (hk : 0 < H.form k d) :
    H.IsViolatedAt j (w + (H.crossParam k w d) • d) ↔
      (0 < H.form j d ∧ H.crossParam j w d < H.crossParam k w d) := by
  have hkpos : 0 ≤ H.crossParam k w d := by
    rw [crossParam]
    exact le_of_lt (div_pos (by linarith) hk)
  exact H.isViolatedAt_line_iff hwj hkpos

omit [Finite J] in
include H in
/-- **The visible facets never exhaust the whole boundary.**  If every
inequality increased in the direction `d`, the whole opposite ray would lie in
`R`, contradicting boundedness.  Hence some inequality is not crossed, i.e.
some facet stays invisible from every point of the ray. -/
theorem exists_form_nonpos_of_ray {w d : F × ℝ} (hd : d ≠ 0)
    (hw : ∀ j : J, H.form j w < H.bound j) :
    ∃ j : J, H.form j d ≤ 0 := by
  by_contra hcon
  push Not at hcon
  have hray : ∀ t : ℝ, 0 ≤ t → (w + (-t) • d) ∈ A.liftedImage := by
    intro t ht
    refine (H.mem_liftedImage_iff _).2 fun j ↦ ?_
    have h := H.form_add_smul j w d (-t)
    have hnonpos : (-t) * H.form j d ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt (hcon j))
    have : H.form j (w + (-t) • d) ≤ H.form j w := by rw [h]; linarith
    exact le_of_lt (lt_of_le_of_lt this (hw j))
  obtain ⟨M, hM⟩ := (A.liftedImage_compact.isBounded).exists_norm_le
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  set t : ℝ := (M + ‖w‖ + 1) / ‖d‖ with htdef
  have ht0 : 0 ≤ t := by
    apply div_nonneg _ hdpos.le
    have h1 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) (hM _ (hray 0 le_rfl))
    have := norm_nonneg w
    linarith
  have hmem := hray t ht0
  have hnorm : ‖w + (-t) • d‖ ≤ M := hM _ hmem
  have hlow : t * ‖d‖ - ‖w‖ ≤ ‖w + (-t) • d‖ := by
    have h1 : ‖(-t) • d‖ = t * ‖d‖ := by
      rw [norm_smul]
      simp [abs_of_nonneg ht0]
    have h2 : ‖(-t) • d‖ - ‖w‖ ≤ ‖w + (-t) • d‖ := by
      have := norm_sub_norm_le ((-t) • d) (-w)
      simpa [sub_neg_eq_add, add_comm, norm_neg] using this
    linarith [h1 ▸ h2]
  have htd : t * ‖d‖ = M + ‖w‖ + 1 := by
    rw [htdef, div_mul_cancel₀ _ (ne_of_gt hdpos)]
  linarith

end FiniteHalfspacePresentation
end CompactConvexProjection
end AffineTverberg
