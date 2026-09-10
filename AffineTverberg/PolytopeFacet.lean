import AffineTverberg.PolytopalGoodVertexCount

set_option linter.style.header false

/-!
# Facets of a `V`-polytope avoiding a prescribed point

This file proves the missing gradedness statement of the face lattice of a
finitely generated polytope that a pulling subdivision needs:

> For a polytope `A = conv s` (`s` finite), an exposed face `G ⊆ A` and a point
> `a ∈ A \ G`, there is an exposed face `F` of `A` with `G ⊆ F`, `a ∉ F` and
> `arank F + 1 = arank A`.

The proof is the perturbation argument for `V`-polytopes: among the exposed
faces containing `G` and avoiding `a` choose one of maximal affine rank.  If it
had codimension at least two, a linear functional `g` vanishing on the direction
of the face and on `a - p` but nonconstant on the generators can be added to a
functional exposing the face; increasing the coefficient until the first extra
generator ties produces a strictly larger exposed face still avoiding `a`
(because `g a = g p`), contradicting maximality.  The empty face is handled
separately.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace PolytopeFace

open CayleyJoin BadVertex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Elementary facts about `exposedBy` of a `V`-polytope -/

omit [FiniteDimensional ℝ E] in
/-- A generator maximizing a functional over the generators lies in the exposed
face it determines. -/
theorem mem_exposedBy_of_forall_le {s : Finset E} {g : E →L[ℝ] ℝ} {v : E}
    (hv : v ∈ (s : Set E)) (hmax : ∀ w ∈ (s : Set E), g w ≤ g v) :
    v ∈ exposedBy (convexHull ℝ (s : Set E)) g := by
  refine ⟨subset_convexHull ℝ _ hv, ?_⟩
  have hsub : convexHull ℝ (s : Set E) ⊆ {z | g z ≤ g v} :=
    convexHull_min hmax (convex_halfSpace_le g.toLinearMap.isLinear _)
  exact fun y hy ↦ hsub hy

omit [FiniteDimensional ℝ E] in
/-- Any point of the hull at which the maximal value is attained belongs to the
exposed face. -/
theorem mem_exposedBy_of_eq_max {s : Finset E} {g : E →L[ℝ] ℝ} {x p : E}
    (hx : x ∈ convexHull ℝ (s : Set E))
    (hp : p ∈ exposedBy (convexHull ℝ (s : Set E)) g) (hgx : g x = g p) :
    x ∈ exposedBy (convexHull ℝ (s : Set E)) g :=
  ⟨hx, fun y hy ↦ by rw [hgx]; exact hp.2 y hy⟩

omit [FiniteDimensional ℝ E] in
/-- A functional is constant on an exposed face. -/
theorem eq_of_mem_exposedBy {A : Set E} {g : E →L[ℝ] ℝ} {x p : E}
    (hx : x ∈ exposedBy A g) (hp : p ∈ exposedBy A g) : g x = g p :=
  le_antisymm (hp.2 x hx.1) (hx.2 p hp.1)

/-- A linear functional vanishing on a submodule and not at a given outside
point; in finite dimension no continuity hypothesis is needed. -/
theorem exists_clm_vanishing_of_notMem {W : Submodule ℝ E} {u : E} (hu : u ∉ W) :
    ∃ g : E →L[ℝ] ℝ, (∀ w ∈ W, g w = 0) ∧ g u ≠ 0 := by
  obtain ⟨f, hfu, hfW⟩ := Submodule.exists_le_ker_of_notMem hu
  refine ⟨LinearMap.toContinuousLinearMap f, fun w hw ↦ ?_, ?_⟩
  · have : f w = 0 := hfW hw
    simpa using this
  · simpa using hfu

/-! ### The perturbation step -/

variable {s : Finset E}

omit [FiniteDimensional ℝ E] in
/-- **The perturbation step.**  Let `F = exposedBy A l` be a nonempty exposed
face of the polytope `A = conv s` with a point `p ∈ F`, let `a ∈ A \ F`, and let
`g` be a functional constant on `F` with `g a = g p`, which is somewhere on the
generators strictly larger than `g p`.  Then some exposed face of `A` strictly
contains `F` (it contains a generator off `F`) and still avoids `a`. -/
theorem exists_exposedBy_strict_of_slope (l g : E →L[ℝ] ℝ) {p a : E}
    (hp : p ∈ exposedBy (convexHull ℝ (s : Set E)) l)
    (hgF : ∀ y ∈ exposedBy (convexHull ℝ (s : Set E)) l, g y = g p)
    (ha : a ∈ convexHull ℝ (s : Set E))
    (haF : a ∉ exposedBy (convexHull ℝ (s : Set E)) l)
    (hga : g a = g p) (hslope : ∃ v ∈ s, g p < g v) :
    ∃ l' : E →L[ℝ] ℝ,
      exposedBy (convexHull ℝ (s : Set E)) l ⊆ exposedBy (convexHull ℝ (s : Set E)) l' ∧
      a ∉ exposedBy (convexHull ℝ (s : Set E)) l' ∧
      ∃ v₀ ∈ (s : Set E), v₀ ∈ exposedBy (convexHull ℝ (s : Set E)) l' ∧
        v₀ ∉ exposedBy (convexHull ℝ (s : Set E)) l := by
  classical
  set A := convexHull ℝ (s : Set E) with hA
  set c := l p with hc
  have hmax : ∀ y ∈ A, l y ≤ c := fun y hy ↦ hp.2 y hy
  have hla : l a < c := by
    rcases lt_or_eq_of_le (hmax a ha) with h | h
    · exact h
    · exact absurd (mem_exposedBy_of_eq_max ha hp h) haF
  -- the generators of positive slope
  set D := s.filter (fun v ↦ g p < g v) with hD
  have hDne : D.Nonempty := by
    obtain ⟨v, hv, hgv⟩ := hslope
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hgv⟩⟩
  -- each such generator is strictly below the maximum of `l`
  have hDlt : ∀ v ∈ D, l v < c := by
    intro v hv
    obtain ⟨hvs, hgv⟩ := Finset.mem_filter.mp hv
    have hvA : v ∈ A := subset_convexHull ℝ _ (Finset.mem_coe.mpr hvs)
    rcases lt_or_eq_of_le (hmax v hvA) with h | h
    · exact h
    · exact absurd (hgF v (mem_exposedBy_of_eq_max hvA hp h)) (ne_of_gt hgv)
  obtain ⟨v₀, hv₀D, hv₀min⟩ :=
    Finset.exists_min_image D (fun v ↦ (c - l v) / (g v - g p)) hDne
  set t := (c - l v₀) / (g v₀ - g p) with ht
  have hg₀ : g p < g v₀ := (Finset.mem_filter.mp hv₀D).2
  have hv₀s : v₀ ∈ s := (Finset.mem_filter.mp hv₀D).1
  have hl₀ : l v₀ < c := hDlt v₀ hv₀D
  have htpos : 0 < t := div_pos (by linarith) (by linarith)
  have hden₀ : g v₀ - g p ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    linarith
  have hteq : t * (g v₀ - g p) = c - l v₀ := by
    rw [ht, div_mul_cancel₀ _ hden₀]
  set l' := l + t • g with hl'
  have hl'apply : ∀ x : E, l' x = l x + t * g x := by
    intro x; simp [hl']
  -- `p` maximizes `l'` over the generators, hence over `A`
  have hgen : ∀ v ∈ (s : Set E), l' v ≤ l' p := by
    intro v hv
    have hvA : v ∈ A := subset_convexHull ℝ _ hv
    have hlv : l v ≤ c := hmax v hvA
    rw [hl'apply, hl'apply, ← hc]
    by_cases hgv : g v ≤ g p
    · nlinarith
    · have hgv' : g p < g v := not_le.mp hgv
      have hvD : v ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hv, hgv'⟩
      have hmin := hv₀min v hvD
      have hden : (0:ℝ) < g v - g p := by linarith
      have hle : t * (g v - g p) ≤ c - l v := by
        calc t * (g v - g p) ≤ ((c - l v) / (g v - g p)) * (g v - g p) :=
              mul_le_mul_of_nonneg_right hmin (le_of_lt hden)
          _ = c - l v := div_mul_cancel₀ _ (ne_of_gt hden)
      linarith
  have hpmax : ∀ y ∈ A, l' y ≤ l' p := by
    have hsub : A ⊆ {z | l' z ≤ l' p} :=
      convexHull_min hgen (convex_halfSpace_le l'.toLinearMap.isLinear _)
    exact fun y hy ↦ hsub hy
  have hpA : p ∈ A := hp.1
  have hpF' : p ∈ exposedBy A l' := ⟨hpA, hpmax⟩
  refine ⟨l', ?_, ?_, v₀, Finset.mem_coe.mpr hv₀s, ?_, ?_⟩
  · intro y hy
    have hly : l y = c := eq_of_mem_exposedBy hy hp
    have hgy : g y = g p := hgF y hy
    refine mem_exposedBy_of_eq_max hy.1 hpF' ?_
    rw [hl'apply, hl'apply, hly, hgy, hc]
  · intro hmem
    have : l' a = l' p := eq_of_mem_exposedBy hmem hpF'
    rw [hl'apply, hl'apply, hga] at this
    have : l a = l p := by linarith
    exact absurd this (by rw [← hc]; exact ne_of_lt hla)
  · refine mem_exposedBy_of_eq_max (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv₀s)) hpF' ?_
    rw [hl'apply, hl'apply, ← hc]
    linarith [hteq]
  · intro hmem
    have : l v₀ = c := eq_of_mem_exposedBy hmem hp
    linarith

/-- **Enlarging a non-facet exposed face while avoiding a point.**  If the
exposed face `F` of `A = conv s` has codimension at least two and misses the
point `a ∈ A`, then some exposed face of strictly larger affine rank contains
`F` and still misses `a`. -/
theorem exists_exposed_arank_lt {F : Set E}
    (hF : IsExposed ℝ (convexHull ℝ (s : Set E)) F) {a : E}
    (ha : a ∈ convexHull ℝ (s : Set E)) (haF : a ∉ F)
    (hcodim : arank F + 2 ≤ arank (convexHull ℝ (s : Set E))) :
    ∃ F', IsExposed ℝ (convexHull ℝ (s : Set E)) F' ∧ F ⊆ F' ∧ a ∉ F' ∧
      arank F < arank F' := by
  classical
  set A := convexHull ℝ (s : Set E) with hA
  have hsne : (s : Set E).Nonempty := by
    rcases (s : Set E).eq_empty_or_nonempty with he | h
    · rw [hA, he] at ha; simp at ha
    · exact h
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · -- the empty face: any exposed face determined by a functional exceeding `g a`
    -- somewhere on the generators works.
    have hrk : 2 ≤ arank A := by rw [hFe] at hcodim; simpa using hcodim
    -- a functional nonconstant on the generators
    have hns : ∃ g : E →L[ℝ] ℝ, ∃ v ∈ (s : Set E), ∃ w ∈ (s : Set E), g v ≠ g w := by
      by_contra hcon
      push Not at hcon
      obtain ⟨v₁, hv₁⟩ := hsne
      have hall : ∀ g : E →L[ℝ] ℝ, ∀ v ∈ (s : Set E), g v = g v₁ := by
        intro g v hv; exact hcon g v hv v₁ hv₁
      -- then all generators coincide, so `A` is a point
      have hpt : ∀ v ∈ (s : Set E), v = v₁ := by
        intro v hv
        by_contra hne
        have hu : v - v₁ ≠ 0 := sub_ne_zero_of_ne hne
        obtain ⟨g, -, hgu⟩ :=
          exists_clm_vanishing_of_notMem (W := (⊥ : Submodule ℝ E)) (u := v - v₁)
            (by simpa using hu)
        exact hgu (by rw [map_sub, hall g v hv]; ring)
      have hsub : (s : Set E) ⊆ {v₁} := fun v hv ↦ hpt v hv
      have : arank A ≤ 1 := by
        calc arank A = arank (s : Set E) := by rw [hA, arank_convexHull]
          _ ≤ arank ({v₁} : Set E) := arank_mono hsub
          _ = 1 := arank_singleton v₁
      omega
    obtain ⟨g, v, hv, w, hw, hgvw⟩ := hns
    -- choose a sign so that the maximum over the generators exceeds `g a`
    have hex : ∃ g : E →L[ℝ] ℝ, ∃ v ∈ (s : Set E), g a < g v := by
      by_cases h1 : ∃ v ∈ (s : Set E), g a < g v
      · exact ⟨g, h1⟩
      push Not at h1
      refine ⟨-g, ?_⟩
      by_contra h2
      push Not at h2
      simp only [neg_apply, neg_le_neg_iff] at h2
      have : g v = g w := by
        have hv' := le_antisymm (h1 v hv) (h2 v hv)
        have hw' := le_antisymm (h1 w hw) (h2 w hw)
        rw [hv', hw']
      exact hgvw this
    obtain ⟨g₀, v₁, hv₁, hlt⟩ := hex
    obtain ⟨u, hu, humax⟩ := Finset.exists_max_image s g₀ ⟨v₁, Finset.mem_coe.mp hv₁⟩
    refine ⟨exposedBy A g₀, isExposed_exposedBy A g₀, by rw [hFe]; exact empty_subset _, ?_, ?_⟩
    · intro hmem
      have h1 : g₀ v₁ ≤ g₀ a := hmem.2 v₁ (subset_convexHull ℝ _ hv₁)
      linarith
    · rw [hFe, arank_empty]
      refine arank_pos ⟨u, mem_exposedBy_of_forall_le (Finset.mem_coe.mpr hu) ?_⟩
      intro z hz
      exact humax z (Finset.mem_coe.mp hz)
  · obtain ⟨l, hl⟩ := hF hFne
    obtain ⟨p, hp⟩ := hFne
    rw [hl] at hp haF hcodim ⊢
    set F' := exposedBy A l with hF'
    have hcodim' : arank F' + 2 ≤ arank A := hcodim
    -- the subspace on which the perturbing functional must vanish
    set W := vectorSpan ℝ F' ⊔ Submodule.span ℝ ({a - p} : Set E) with hW
    have hFsub : F' ⊆ A := exposedBy_subset A l
    have hdimF : Module.finrank ℝ (vectorSpan ℝ F') + 1 = arank F' :=
      (arank_of_nonempty ⟨p, hp⟩).symm
    have hWle : Module.finrank ℝ W ≤ arank F' := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq (vectorSpan ℝ F')
        (Submodule.span ℝ ({a - p} : Set E))
      have h2 : Module.finrank ℝ (Submodule.span ℝ ({a - p} : Set E)) ≤ 1 := by
        rcases eq_or_ne (a - p) (0 : E) with h0 | h0
        · rw [h0, Submodule.span_zero_singleton]; simp
        · rw [show (Submodule.span ℝ ({a - p} : Set E)) = ℝ ∙ (a - p) from rfl,
            finrank_span_singleton h0]
      rw [hW]
      omega
    -- `W` sits inside the direction of `A`
    have hWsub : W ≤ vectorSpan ℝ A := by
      rw [hW]
      refine sup_le (vectorSpan_mono ℝ hFsub) ?_
      rw [Submodule.span_le]
      rintro z hz
      rw [mem_singleton_iff] at hz
      subst hz
      exact vsub_mem_vectorSpan ℝ ha (hFsub hp)
    have hAne : A.Nonempty := ⟨a, ha⟩
    have hdimA : Module.finrank ℝ (vectorSpan ℝ A) + 1 = arank A :=
      (arank_of_nonempty hAne).symm
    have hlt : Module.finrank ℝ W < Module.finrank ℝ (vectorSpan ℝ A) := by omega
    -- a vector of the direction of `A` outside `W`
    have hexu : ∃ u : E, u ∈ vectorSpan ℝ A ∧ u ∉ W := by
      by_contra hcon
      push Not at hcon
      have hle : vectorSpan ℝ A ≤ W := fun x hx ↦ hcon x hx
      exact absurd (Submodule.finrank_mono hle) (by omega)
    obtain ⟨u, huA, huW⟩ := hexu
    obtain ⟨g, hgW, hgu⟩ := exists_clm_vanishing_of_notMem huW
    have hgF : ∀ y ∈ F', g y = g p := by
      intro y hy
      have hmem : y - p ∈ W := le_sup_left (b := Submodule.span ℝ ({a - p} : Set E))
        (vsub_mem_vectorSpan ℝ hy hp)
      have := hgW _ hmem
      rw [map_sub] at this
      linarith
    have hga : g a = g p := by
      have hmem : a - p ∈ W :=
        le_sup_right (a := vectorSpan ℝ F') (Submodule.subset_span rfl)
      have := hgW _ hmem
      rw [map_sub] at this
      linarith
    -- `g` is nonconstant on the generators
    have hslopeex : ∃ v ∈ s, g v ≠ g p := by
      by_contra hcon
      push Not at hcon
      have hker : vectorSpan ℝ (s : Set E) ≤ LinearMap.ker (g : E →ₗ[ℝ] ℝ) := by
        obtain ⟨v₁, hv₁⟩ := hsne
        rw [vectorSpan_eq_span_vsub_set_right ℝ hv₁, Submodule.span_le]
        rintro _ ⟨y, hy, rfl⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
          vsub_eq_sub, map_sub]
        rw [hcon y (Finset.mem_coe.mp hy), hcon v₁ (Finset.mem_coe.mp hv₁), sub_self]
      have hAspan : vectorSpan ℝ A = vectorSpan ℝ (s : Set E) := by
        rw [hA, ← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull]
      rw [hAspan] at huA
      exact hgu (by simpa using hker huA)
    -- fix the sign so that some generator has strictly positive slope
    have hsign : ∃ g' : E →L[ℝ] ℝ, (∀ y ∈ F', g' y = g' p) ∧ g' a = g' p ∧
        ∃ v ∈ s, g' p < g' v := by
      obtain ⟨v, hv, hne⟩ := hslopeex
      rcases lt_or_gt_of_ne hne with hlt' | hgt
      · refine ⟨-g, fun y hy ↦ ?_, ?_, v, hv, ?_⟩
        · simp only [neg_apply]
          rw [hgF y hy]
        · simp only [neg_apply]
          rw [hga]
        · simp only [neg_apply]
          linarith
      · exact ⟨g, hgF, hga, v, hv, hgt⟩
    obtain ⟨g', hg'F, hg'a, hg'slope⟩ := hsign
    obtain ⟨l', hsubset, hna, v₀, hv₀s, hv₀mem, hv₀not⟩ :=
      exists_exposedBy_strict_of_slope l g' hp hg'F ha haF hg'a hg'slope
    refine ⟨exposedBy A l', isExposed_exposedBy A l', hsubset, hna, ?_⟩
    refine arank_lt_of_notMem_affineSpan hsubset hv₀mem ?_
    intro hspan
    exact hv₀not (mem_of_mem_affineSpan_exposed (isExposed_exposedBy A l)
      (subset_convexHull ℝ _ hv₀s) hspan)

/-- An exposed face missing a point of the polytope has strictly smaller affine
rank than the polytope. -/
theorem arank_lt_of_exposed_notMem {A F : Set E} (hF : IsExposed ℝ A F) {a : E}
    (ha : a ∈ A) (haF : a ∉ F) : arank F < arank A := by
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · simpa using arank_pos ⟨a, ha⟩
  · by_contra hcon
    push Not at hcon
    have hspan := affineSpan_eq_of_subset_of_arank_le hFne hF.subset hcon
    exact haF (mem_of_mem_affineSpan_exposed hF ha
      (hspan ▸ subset_affineSpan ℝ A ha))

private theorem exists_facet_aux (d : ℕ) {a : E} (ha : a ∈ convexHull ℝ (s : Set E)) :
    ∀ F : Set E, IsExposed ℝ (convexHull ℝ (s : Set E)) F → a ∉ F →
      arank (convexHull ℝ (s : Set E)) ≤ arank F + d →
      ∃ F', IsExposed ℝ (convexHull ℝ (s : Set E)) F' ∧ F ⊆ F' ∧ a ∉ F' ∧
        arank F' + 1 = arank (convexHull ℝ (s : Set E)) := by
  induction d with
  | zero =>
      intro F hF haF hle
      exact absurd (arank_lt_of_exposed_notMem hF ha haF) (by omega)
  | succ d ih =>
      intro F hF haF hle
      have hlt := arank_lt_of_exposed_notMem hF ha haF
      by_cases hfacet : arank F + 1 = arank (convexHull ℝ (s : Set E))
      · exact ⟨F, hF, subset_rfl, haF, hfacet⟩
      · have hcodim : arank F + 2 ≤ arank (convexHull ℝ (s : Set E)) := by omega
        obtain ⟨F₁, hF₁, hsub, ha₁, hrank⟩ := exists_exposed_arank_lt hF ha haF hcodim
        obtain ⟨F', hF', hsub', ha', hfac⟩ := ih F₁ hF₁ ha₁ (by omega)
        exact ⟨F', hF', hsub.trans hsub', ha', hfac⟩

/-- **Every exposed face of a `V`-polytope extends to a facet avoiding any
prescribed point outside it.**  This is the gradedness statement of the face
lattice needed by a pulling subdivision. -/
theorem exists_facet_exposed_avoiding {F₀ : Set E}
    (hF₀ : IsExposed ℝ (convexHull ℝ (s : Set E)) F₀) {a : E}
    (ha : a ∈ convexHull ℝ (s : Set E)) (haF : a ∉ F₀) :
    ∃ F, IsExposed ℝ (convexHull ℝ (s : Set E)) F ∧ F₀ ⊆ F ∧ a ∉ F ∧
      arank F + 1 = arank (convexHull ℝ (s : Set E)) :=
  exists_facet_aux (arank (convexHull ℝ (s : Set E))) ha F₀ hF₀ haF (by omega)

end PolytopeFace
end AffineTverberg
