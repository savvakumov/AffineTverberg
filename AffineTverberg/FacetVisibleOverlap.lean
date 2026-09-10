import AffineTverberg.FacetRidge

set_option linter.style.header false

/-!
# The visible overlap of a facet

This file combines the two geometric sublemmas of the line-shelling route:

* `affineSpan_facet_eq` — the affine span of a facet is exactly the part of the
  affine span of the polytope on which the facet inequality is tight (a
  hyperplane section of the affine span);
* `iUnion_facetFace_inter_eq_iUnion_visible_ridge` — **the overlap
  identification.**  For a point `q` of the affine span lying on the hyperplane
  of the facet `F`, the union of the intersections of `F` with the facets
  visible from `q` is *exactly* the union of the ridges of `F` visible from `q`
  inside `aff F`.

The first inclusion uses the ridge theorem `exists_ambient_facet_of_ridge`
(every visible ridge is the intersection with a visible ambient facet); the
second uses the visible-facet extension `exists_facetIdx_face_subset_violated`
inside the facet polytope (every intersection with a visible ambient facet lies
in a visible ridge).

This is the attaching data required by a recursive cell shelling; the induction
on dimension producing a `ShellableGluing.CellShelling` certificate from it is
not carried out here.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace PolytopeFace

open CayleyJoin RelInt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Contact generators of an attained valid inequality -/

omit [FiniteDimensional ℝ E] in
/-- If a valid inequality is attained on the polytope, its contact generators
are exactly the generators maximizing it. -/
theorem contactGens_eq_filter_of_attained {t : Finset E} {g : E →L[ℝ] ℝ} {c : ℝ}
    (hvalid : ∀ y ∈ convexHull ℝ (t : Set E), g y ≤ c)
    {x : E} (hx : x ∈ convexHull ℝ (t : Set E)) (hxc : g x = c) :
    contactGens t g c = t.filter fun v ↦ ∀ w ∈ t, g w ≤ g v := by
  classical
  ext v
  simp only [mem_contactGens, Finset.mem_filter]
  constructor
  · rintro ⟨hv, hgv⟩
    refine ⟨hv, fun w hw ↦ ?_⟩
    rw [hgv]
    exact hvalid w (subset_convexHull ℝ _ (Finset.mem_coe.mpr hw))
  · rintro ⟨hv, hmax⟩
    refine ⟨hv, le_antisymm (hvalid v (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))) ?_⟩
    have hexp : v ∈ exposedBy (convexHull ℝ (t : Set E)) g :=
      mem_exposedBy_of_forall_le (Finset.mem_coe.mpr hv)
        (fun w hw ↦ hmax w (Finset.mem_coe.mp hw))
    have := hexp.2 x hx
    rw [hxc] at this
    exact this

omit [FiniteDimensional ℝ E] in
/-- The contact face of an attained valid inequality is the hull of its contact
generators. -/
theorem convexHull_contactGens_of_attained {t : Finset E} {g : E →L[ℝ] ℝ} {c : ℝ}
    (hvalid : ∀ y ∈ convexHull ℝ (t : Set E), g y ≤ c)
    {x : E} (hx : x ∈ convexHull ℝ (t : Set E)) (hxc : g x = c) :
    convexHull ℝ ((contactGens t g c : Finset E) : Set E)
      = exposedBy (convexHull ℝ (t : Set E)) g := by
  rw [contactGens_eq_filter_of_attained hvalid hx hxc, ← exposedBy_convexHull t g]

/-! ### The affine span of a facet is a hyperplane section -/

/-- **The affine span of a facet is exactly the tight part of the affine span of
the polytope.** -/
theorem affineSpan_facet_eq {s : Finset E} (hs : s.Nonempty) (j : FacetIdx s) :
    {x : E | x ∈ affineSpan ℝ (s : Set E) ∧ facetForm j x = facetRhs j}
      = (affineSpan ℝ ((j.1.1 : Finset E) : Set E) : Set E) := by
  classical
  set C : Set E := {x : E | x ∈ affineSpan ℝ (s : Set E) ∧ facetForm j x = facetRhs j}
    with hC
  set A : Set E := (affineSpan ℝ ((j.1.1 : Finset E) : Set E) : Set E) with hA
  have hj := facetIdx_isFacetIneq j
  have ht : (j.1.1).Nonempty := facetIdx_nonempty j
  have htsub : j.1.1 ⊆ s := Finset.mem_powerset.mp j.1.2
  have hAne : A.Nonempty := by
    obtain ⟨v, hv⟩ := ht
    exact ⟨v, subset_affineSpan ℝ _ (Finset.mem_coe.mpr hv)⟩
  have hAC : A ⊆ C := by
    intro x hx
    refine ⟨?_, facetForm_eq_of_mem_affineSpan j hx⟩
    exact affineSpan_mono ℝ (by exact_mod_cast htsub) hx
  -- `C` is an affine subspace
  have hCmem : ∀ x, x ∈ affineSpan ℝ C → x ∈ C := by
    intro x hx
    set Q : AffineSubspace ℝ E :=
      { carrier := C
        smul_vsub_vadd_mem' := by
          rintro c p₁ p₂ p₃ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩ ⟨h₃, h₃'⟩
          refine ⟨AffineSubspace.smul_vsub_vadd_mem _ c h₁ h₂ h₃, ?_⟩
          simp only [vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub,
            smul_eq_mul, h₁', h₂', h₃']
          ring } with hQ
    have hle : affineSpan ℝ C ≤ Q := affineSpan_le.mpr (fun y hy ↦ hy)
    exact hle hx
  -- a relative interior point of the polytope is not on the hyperplane
  obtain ⟨p, hp⟩ := exists_isRelInt_convexHull hs
  have hplt : facetForm j p < facetRhs j := facetForm_lt_facetRhs_of_isRelInt j hp
  have hpB : p ∈ affineSpan ℝ (s : Set E) :=
    convexHull_subset_affineSpan (𝕜 := ℝ) (s : Set E) hp.mem
  have hpC : p ∉ C := fun hmem ↦ absurd hmem.2 (ne_of_lt hplt)
  -- rank comparison
  have hCB : C ⊆ (affineSpan ℝ (s : Set E) : Set E) := fun x hx ↦ hx.1
  have hrankC : arank C < arank ((affineSpan ℝ (s : Set E) : Set E)) :=
    arank_lt_of_notMem_affineSpan hCB hpB (fun hmem ↦ hpC (hCmem p hmem))
  have hrankA : arank A = arank (convexHull ℝ ((j.1.1 : Finset E) : Set E)) := by
    rw [arank_convexHull]
    refine arank_eq_of_affineSpan_eq ?_
    rw [hA, AffineSubspace.affineSpan_coe]
  have hrankB : arank ((affineSpan ℝ (s : Set E) : Set E))
      = arank (convexHull ℝ (s : Set E)) := by
    rw [arank_convexHull]
    refine arank_eq_of_affineSpan_eq ?_
    rw [AffineSubspace.affineSpan_coe]
  have hcodim := facetIdx_codim j
  have hle : arank C ≤ arank A := by omega
  have hspanCA := affineSpan_eq_of_subset_of_arank_le hAne hAC hle
  refine Subset.antisymm ?_ hAC
  intro x hx
  have hx' : x ∈ affineSpan ℝ A := by
    rw [hspanCA]
    exact subset_affineSpan ℝ C hx
  have hAspan : affineSpan ℝ A = affineSpan ℝ ((j.1.1 : Finset E) : Set E) := by
    rw [hA, AffineSubspace.affineSpan_coe]
  rw [hAspan] at hx'
  exact hx'

/-! ### The overlap of a facet with the visible facets -/

/-- **The overlap identification.**  If `q` lies in the affine span of the
polytope and on the hyperplane of the facet `j`, then the union of the
intersections of that facet with the facets visible from `q` is exactly the
union of the ridges of the facet visible from `q`. -/
theorem iUnion_facetFace_inter_eq_iUnion_visible_ridge {s : Finset E}
    (hs : s.Nonempty) (j : FacetIdx s) {q : E}
    (hq : q ∈ affineSpan ℝ (s : Set E)) (hqj : facetForm j q = facetRhs j) :
    (⋃ (j' : FacetIdx s) (_ : facetRhs j' < facetForm j' q),
        facetFace j ∩ facetFace j')
      = ⋃ (i : FacetIdx j.1.1) (_ : facetRhs i < facetForm i q), facetFace i := by
  classical
  have ht : (j.1.1).Nonempty := facetIdx_nonempty j
  have htsub : j.1.1 ⊆ s := Finset.mem_powerset.mp j.1.2
  have hFP : convexHull ℝ ((j.1.1 : Finset E) : Set E) ⊆ convexHull ℝ (s : Set E) :=
    convexHull_mono (by exact_mod_cast htsub)
  have hqt : q ∈ affineSpan ℝ ((j.1.1 : Finset E) : Set E) := by
    have hmem : q ∈ {x : E | x ∈ affineSpan ℝ (s : Set E) ∧ facetForm j x = facetRhs j} :=
      ⟨hq, hqj⟩
    rw [affineSpan_facet_eq hs j] at hmem
    exact hmem
  apply Subset.antisymm
  · -- every intersection with a visible facet lies in a visible ridge
    intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨j', hj'vis, hxj, hxj'⟩ := hx
    have hxt : x ∈ convexHull ℝ ((j.1.1 : Finset E) : Set E) := hxj
    have hxform : facetForm j' x = facetRhs j' := ((mem_facetFace_iff j').1 hxj').2
    have hvalid : ∀ y ∈ convexHull ℝ ((j.1.1 : Finset E) : Set E),
        facetForm j' y ≤ facetRhs j' := fun y hy ↦ facetForm_le_facetRhs j' (hFP hy)
    have hcontact := convexHull_contactGens_of_attained hvalid hxt hxform
    have hne : (contactGens (j.1.1) (facetForm j') (facetRhs j')).Nonempty := by
      by_contra hcon
      have hempty : contactGens (j.1.1) (facetForm j') (facetRhs j') = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hcon
      have hxexp : x ∈ exposedBy (convexHull ℝ ((j.1.1 : Finset E) : Set E))
          (facetForm j') := by
        refine ⟨hxt, fun y hy ↦ ?_⟩
        rw [hxform]
        exact hvalid y hy
      rw [← hcontact, hempty] at hxexp
      simp at hxexp
    obtain ⟨i, hisub, hivis⟩ :=
      exists_facetIdx_face_subset_violated ht hvalid hne hqt hj'vis
    have hxH : x ∈ facetFace i := by
      apply hisub
      rw [hcontact]
      exact ⟨hxt, fun y hy ↦ by rw [hxform]; exact hvalid y hy⟩
    simp only [mem_iUnion]
    exact ⟨i, hivis, hxH⟩
  · -- every visible ridge is the intersection with a visible facet
    intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨i, hivis, hxi⟩ := hx
    obtain ⟨j', -, hinter, horient⟩ := exists_ambient_facet_of_ridge hs j i
    have hj'vis : facetRhs j' < facetForm j' q := (horient q hqt).1 hivis
    simp only [mem_iUnion]
    refine ⟨j', hj'vis, ?_⟩
    rw [← hinter]
    exact hxi

end PolytopeFace
end AffineTverberg
