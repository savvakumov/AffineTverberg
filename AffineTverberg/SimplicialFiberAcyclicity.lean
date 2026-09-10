import AffineTverberg.SimplicialJoinAcyclicity
import AffineTverberg.SimplicialLemmaY

set_option linter.style.header false

/-!
# Acyclicity of the ridge fiber of Lemma Y

This file connects the general join-acyclicity theorem of
`AffineTverberg/SimplicialJoinAcyclicity.lean` with the concrete finite colored
model of the fiber used in `AffineTverberg/SimplicialRidgeJoin.lean` and
`AffineTverberg/SimplicialLemmaY.lean`.

Contents:

* `isReducedAcyclicAt_ridgeColorChoiceFamily` : for a fixed unit functional `y`
  the finite face-closed family of color-choice faces of the ridge `L` has
  vanishing reduced homology in every augmented degree `k < L.card`, i.e. in
  every geometric degree `j ≤ L.card - 2`.  The only input is the diagonal
  relation, which makes each allowed color set `W_v(y)` nonempty.
* `coloredCayleyVertex` : the point of the join ambient space carried by a
  colored vertex, and `joinCellCarrier_cellOfColorFace`, which identifies the
  geometric carrier of a nonnegative cell with the convex hull of the colored
  Cayley vertices of the corresponding color-choice face.
* `affineIndependent_polytopalJoinCopy` and
  `affineIndependent_coloredCayleyVertex` : if the ridge `L` is a simplex (an
  affinely independent vertex set, which holds for every face of a geometric
  simplicial complex), then *all* colored Cayley vertices over `L` are affinely
  independent.  Hence every carrier above is a genuine geometric simplex and the
  carriers form a geometric simplicial complex isomorphic to the abstract one.
* `coloredCayleyComplex` : the resulting genuine *geometric* simplicial complex,
  with `coloredCayleyComplex_faces_eq_image` identifying its faces with the faces
  of the abstract complex `nonnegativeJoinComplex`.
* `ridgeNonnegLocus_eq_iUnion_colorChoiceFamily` and
  `ridgeNonnegLocus_eq_coloredCayleyComplex_space` : the geometric fiber is
  exactly the union of the carriers of the faces of the abstract family, i.e. the
  polyhedron of that geometric simplicial complex.

The one remaining gap towards Lemma Y is stated explicitly in the final section:
a comparison theorem between the simplicial homology of the abstract family used
here and the singular homology of its geometric realization.  It is *not*
assumed anywhere: no definition of acyclicity below hides it.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg

open Simplicial

section Acyclicity

variable {e m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Acyclicity of the ridge fiber (combinatorial form).**  For a fixed
functional `y`, the family of color-choice faces of the allowed colors over the
ridge `L` is reduced acyclic in every degree `k < L.card`.  The hypothesis is the
diagonal relation of the join map, which is what makes every color set `W_v(y)`
nonempty; no acyclicity is assumed. -/
theorem isReducedAcyclicAt_ridgeColorChoiceFamily (𝕜 : Type*) [Field 𝕜]
    (L : Finset (CoordinateSpace e)) (Φ : PolytopalJoinAmbient e m →L[ℝ] E)
    (y : StrongDual ℝ E)
    [Fintype (NonnegativeColoredVertex L (ridgeEval Φ y))]
    [LinearOrder (NonnegativeColoredVertex L (ridgeEval Φ y))]
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    {k : ℕ} (hk : k < L.card) :
    IsReducedAcyclicAt 𝕜 (colorChoiceFamily L (ridgeEval Φ y)) k :=
  isReducedAcyclicAt_colorChoiceFamily L (ridgeEval Φ y) 𝕜
    (fun v _ => sum_ridgeEval_eq_zero hdiag y v) hk

/-- The homology-module form of the previous theorem. -/
theorem homology_ridgeColorChoiceFamily_subsingleton (𝕜 : Type*) [Field 𝕜]
    (L : Finset (CoordinateSpace e)) (Φ : PolytopalJoinAmbient e m →L[ℝ] E)
    (y : StrongDual ℝ E)
    [Fintype (NonnegativeColoredVertex L (ridgeEval Φ y))]
    [LinearOrder (NonnegativeColoredVertex L (ridgeEval Φ y))]
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    {k : ℕ} (hk : k < L.card) :
    Subsingleton (homology 𝕜 (colorChoiceFamily L (ridgeEval Φ y)) k) :=
  (homology_subsingleton_iff _ _).mpr
    (isReducedAcyclicAt_ridgeColorChoiceFamily 𝕜 L Φ y hdiag hk)

end Acyclicity

section CayleyVertices

variable {e m : ℕ} {L : Finset (CoordinateSpace e)}
  {eval : CoordinateSpace e → Fin (m + 1) → ℝ}

/-- The point of the join ambient space carried by a colored vertex: the copy of
the underlying vertex in the factor given by its color. -/
def coloredCayleyVertex (a : NonnegativeColoredVertex L eval) : PolytopalJoinAmbient e m :=
  polytopalJoinCopy (a.2 : Fin (m + 1)) (a.1 : CoordinateSpace e)

theorem coloredCayleyVertex_injective :
    Function.Injective (coloredCayleyVertex (L := L) (eval := eval)) := by
  intro a b hab
  have h := congrFun hab (a.2 : Fin (m + 1))
  simp only [coloredCayleyVertex, polytopalJoinCopy, Pi.single_eq_same] at h
  by_cases hc : (a.2 : Fin (m + 1)) = (b.2 : Fin (m + 1))
  · rw [← hc, Pi.single_eq_same] at h
    exact coloredVertex_ext (congrArg Prod.fst h) hc
  · rw [Pi.single_eq_of_ne hc] at h
    have hone : (1 : ℝ) = 0 := by simpa using congrArg Prod.snd h
    exact absurd hone one_ne_zero

/-- The vertices of the geometric cell of a color-choice face are exactly the
colored Cayley vertices of the face. -/
theorem joinCellVertices_cellOfColorFace (s : Finset (NonnegativeColoredVertex L eval)) :
    joinCellVertices (cellOfColorFace s) = s.image coloredCayleyVertex := by
  ext w
  rw [mem_joinCellVertices, Finset.mem_image]
  constructor
  · rintro ⟨i, v, hv, rfl⟩
    obtain ⟨a, ha, hai, hav⟩ := mem_cellOfColorFace.mp hv
    exact ⟨a, ha, by rw [coloredCayleyVertex, hai, hav]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(a.2 : Fin (m + 1)), (a.1 : CoordinateSpace e),
      mem_cellOfColorFace.mpr ⟨a, ha, rfl, rfl⟩, rfl⟩

/-- The geometric carrier of the cell of a color-choice face is the convex hull
of the colored Cayley vertices of that face. -/
theorem joinCellCarrier_cellOfColorFace (s : Finset (NonnegativeColoredVertex L eval)) :
    joinCellCarrier (cellOfColorFace s)
      = convexHull ℝ ((s.image coloredCayleyVertex : Finset (PolytopalJoinAmbient e m)) :
          Set (PolytopalJoinAmbient e m)) := by
  rw [joinCellCarrier, joinCellVertices_cellOfColorFace]

end CayleyVertices

section AffineIndependence

variable {e m : ℕ}

/-- **Affine independence of the Cayley copies.**  If the vertex set `L` is
affinely independent (i.e. `L` spans a simplex), then all copies
`polytopalJoinCopy i v`, `i` a color and `v ∈ L`, are affinely independent in the
join ambient space. -/
theorem affineIndependent_polytopalJoinCopy {L : Finset (CoordinateSpace e)}
    (hL : AffineIndependent ℝ ((↑) : ↥L → CoordinateSpace e)) :
    AffineIndependent ℝ (fun p : Fin (m + 1) × ↥L ↦
      polytopalJoinCopy p.1 (p.2 : CoordinateSpace e)) := by
  classical
  rw [affineIndependent_iff]
  intro s w _hw hsum q hq
  set t : Finset (Fin (m + 1) × ↥L) := s.filter (fun p ↦ p.1 = q.1) with ht
  have h : ∑ p ∈ s, (w p • polytopalJoinCopy p.1 (p.2 : CoordinateSpace e)) q.1 = 0 := by
    have hz := congrFun hsum q.1
    rwa [Finset.sum_apply, Pi.zero_apply] at hz
  have hcoord : ∑ p ∈ t, w p • (((p.2 : CoordinateSpace e), (1 : ℝ)) : CoordinateSpace e × ℝ)
      = 0 := by
    have hrw : ∑ p ∈ t, w p • (((p.2 : CoordinateSpace e), (1 : ℝ)) : CoordinateSpace e × ℝ)
        = ∑ p ∈ s, (w p • polytopalJoinCopy p.1 (p.2 : CoordinateSpace e)) q.1 := by
      rw [ht, Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      by_cases hp : p.1 = q.1
      · simp [hp, polytopalJoinCopy]
      · simp [hp, polytopalJoinCopy]
    rw [hrw, h]
  have hinj : ∀ x ∈ t, ∀ y ∈ t, x.2 = y.2 → x = y := by
    intro x hx y hy hxy
    have hx1 : x.1 = q.1 := (Finset.mem_filter.mp hx).2
    have hy1 : y.1 = q.1 := (Finset.mem_filter.mp hy).2
    exact Prod.ext (hx1.trans hy1.symm) hxy
  set u : ↥L → ℝ := fun v ↦ w (q.1, v) with hu
  have hmem : ∀ p ∈ t, (q.1, p.2) = p := fun p hp ↦
    Prod.ext (Finset.mem_filter.mp hp).2.symm rfl
  have hsum1 : ∑ v ∈ t.image Prod.snd, u v = 0 := by
    rw [Finset.sum_image hinj]
    have hcongr : ∀ p ∈ t, u p.2 = w p := fun p hp ↦ congrArg w (hmem p hp)
    rw [Finset.sum_congr rfl hcongr]
    have hc2 := congrArg Prod.snd hcoord
    rw [Prod.snd_sum] at hc2
    simpa using hc2
  have hsum2 : ∑ v ∈ t.image Prod.snd, u v • (v : CoordinateSpace e) = 0 := by
    rw [Finset.sum_image hinj]
    have hcongr : ∀ p ∈ t, u p.2 • (p.2 : CoordinateSpace e)
        = w p • (p.2 : CoordinateSpace e) := fun p hp ↦
      congrArg (fun c ↦ c • (p.2 : CoordinateSpace e)) (congrArg w (hmem p hp))
    rw [Finset.sum_congr rfl hcongr]
    have hc1 := congrArg Prod.fst hcoord
    rw [Prod.fst_sum] at hc1
    simpa using hc1
  have hq' : q.2 ∈ t.image Prod.snd :=
    Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, rfl⟩, rfl⟩
  have hzero := affineIndependent_iff.mp hL (t.image Prod.snd) u hsum1 hsum2 q.2 hq'
  simpa [hu] using hzero

variable {L : Finset (CoordinateSpace e)} {eval : CoordinateSpace e → Fin (m + 1) → ℝ}

/-- The colored Cayley vertices over an affinely independent ridge are affinely
independent. -/
theorem affineIndependent_coloredCayleyVertex
    (hL : AffineIndependent ℝ ((↑) : ↥L → CoordinateSpace e)) :
    AffineIndependent ℝ (coloredCayleyVertex (L := L) (eval := eval)) := by
  classical
  have hemb : Function.Injective
      (fun a : NonnegativeColoredVertex L eval ↦ (((a.2 : Fin (m + 1))), a.1)) := by
    intro a b hab
    have h1 : (a.2 : Fin (m + 1)) = (b.2 : Fin (m + 1)) := congrArg Prod.fst hab
    have h2 : (a.1 : CoordinateSpace e) = (b.1 : CoordinateSpace e) :=
      congrArg (fun p ↦ ((p.2 : ↥L) : CoordinateSpace e)) hab
    exact coloredVertex_ext h2 h1
  exact (affineIndependent_polytopalJoinCopy hL).comp_embedding ⟨_, hemb⟩

/-- The restriction to a color-choice face: its colored Cayley vertices are
affinely independent, so each face spans a genuine geometric simplex. -/
theorem affineIndependent_coloredCayleyVertex_face
    (hL : AffineIndependent ℝ ((↑) : ↥L → CoordinateSpace e))
    (s : Finset (NonnegativeColoredVertex L eval)) :
    AffineIndependent ℝ (fun a : {a // a ∈ s} ↦ coloredCayleyVertex a.1) :=
  (affineIndependent_coloredCayleyVertex hL).comp_embedding
    (Function.Embedding.subtype (fun a ↦ a ∈ s))

/-- A boundary ridge of a geometric simplicial complex is a simplex, so its
colored Cayley vertices are affinely independent. -/
theorem affineIndependent_coloredCayleyVertex_of_isBoundaryRidge {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
    (hL : IsBoundaryRidge n K L) :
    AffineIndependent ℝ (coloredCayleyVertex (L := L) (eval := eval)) :=
  affineIndependent_coloredCayleyVertex (K.indep hL.1)

end AffineIndependence

section GeometricFiber

variable {e m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The geometric fiber is the realization of the abstract family.**  The union
of the cells of the deleted join of the ridge on which `y ∘ Φ` is nonnegative is
exactly the union of the convex hulls of the colored Cayley vertex sets of the
faces of `colorChoiceFamily`. -/
theorem ridgeNonnegLocus_eq_iUnion_colorChoiceFamily (L : Finset (CoordinateSpace e))
    (Φ : PolytopalJoinAmbient e m →L[ℝ] E) (y : StrongDual ℝ E)
    [Fintype (NonnegativeColoredVertex L (ridgeEval Φ y))] :
    ridgeNonnegLocus L Φ y =
      ⋃ s ∈ colorChoiceFamily L (ridgeEval Φ y),
        convexHull ℝ ((s.image coloredCayleyVertex :
          Finset (PolytopalJoinAmbient e m)) : Set (PolytopalJoinAmbient e m)) := by
  ext z
  rw [mem_ridgeNonnegLocus_iff_colorChoiceFace]
  constructor
  · rintro ⟨s, hzs⟩
    refine Set.mem_iUnion₂.mpr
      ⟨s.1, (mem_colorChoiceFamily_iff L (ridgeEval Φ y) s.1).mpr s.2, ?_⟩
    rwa [← joinCellCarrier_cellOfColorFace]
  · intro hz
    obtain ⟨s, hs, hzs⟩ := Set.mem_iUnion₂.mp hz
    refine ⟨⟨s, (mem_colorChoiceFamily_iff L (ridgeEval Φ y) s).mp hs⟩, ?_⟩
    rwa [joinCellCarrier_cellOfColorFace]

end GeometricFiber

section GeometricComplex

variable {e m : ℕ} {L : Finset (CoordinateSpace e)}
  {eval : CoordinateSpace e → Fin (m + 1) → ℝ}

theorem coe_image_coloredCayleyVertex_subset_range
    (s : Finset (NonnegativeColoredVertex L eval)) :
    ((s.image coloredCayleyVertex : Finset (PolytopalJoinAmbient e m)) :
        Set (PolytopalJoinAmbient e m))
      ⊆ Set.range (coloredCayleyVertex (L := L) (eval := eval)) := by
  intro x hx
  rw [Finset.coe_image, Set.mem_image] at hx
  obtain ⟨a, -, rfl⟩ := hx
  exact ⟨a, rfl⟩

/-- Any finite set of colored Cayley vertices over an affinely independent ridge
is affinely independent, hence spans a genuine geometric simplex. -/
theorem affineIndependent_subset_coloredCayleyVertex
    (hL : AffineIndependent ℝ ((↑) : ↥L → CoordinateSpace e))
    {T : Finset (PolytopalJoinAmbient e m)}
    (hT : (T : Set (PolytopalJoinAmbient e m))
      ⊆ Set.range (coloredCayleyVertex (L := L) (eval := eval))) :
    AffineIndependent ℝ (Subtype.val : ↥T → PolytopalJoinAmbient e m) :=
  (affineIndependent_coloredCayleyVertex hL).range.mono hT

/-- **The geometric simplicial complex of the fiber.**  For an affinely
independent ridge, the convex hulls of the colored Cayley vertex sets of the
nonempty color-choice faces form a genuine geometric simplicial complex: each is
a simplex and two of them meet in a common face. -/
def coloredCayleyComplex (hL : AffineIndependent ℝ ((↑) : ↥L → CoordinateSpace e))
    (eval : CoordinateSpace e → Fin (m + 1) → ℝ) :
    Geometry.SimplicialComplex ℝ (PolytopalJoinAmbient e m) where
  faces := {T | T.Nonempty ∧ ∃ s : Finset (NonnegativeColoredVertex L eval),
    IsColorChoiceFace L eval s ∧ T = s.image coloredCayleyVertex}
  isRelLowerSet_faces := by
    rintro T ⟨hTne, s, hs, rfl⟩
    refine ⟨hTne, ?_⟩
    intro U hU hUne
    refine ⟨hUne, s.filter (fun a ↦ coloredCayleyVertex a ∈ U), ?_, ?_⟩
    · exact fun a ha b hb hab =>
        hs a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
    · ext x
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · intro hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hU hx)
        exact ⟨a, ⟨ha, hx⟩, rfl⟩
      · rintro ⟨a, ⟨-, ha⟩, rfl⟩
        exact ha
  indep := by
    rintro T ⟨-, s, -, rfl⟩
    exact affineIndependent_subset_coloredCayleyVertex hL
      (coe_image_coloredCayleyVertex_subset_range s)
  inter_subset_convexHull := by
    rintro T U ⟨-, s, -, rfl⟩ ⟨-, t, -, rfl⟩
    have hai : AffineIndependent ℝ
        (Subtype.val : ↥((s ∪ t).image (coloredCayleyVertex (L := L) (eval := eval)))
          → PolytopalJoinAmbient e m) :=
      affineIndependent_subset_coloredCayleyVertex hL
        (coe_image_coloredCayleyVertex_subset_range (s ∪ t))
    have h1 : s.image (coloredCayleyVertex (L := L) (eval := eval))
        ⊆ (s ∪ t).image coloredCayleyVertex :=
      Finset.image_subset_image Finset.subset_union_left
    have h2 : t.image (coloredCayleyVertex (L := L) (eval := eval))
        ⊆ (s ∪ t).image coloredCayleyVertex :=
      Finset.image_subset_image Finset.subset_union_right
    exact (hai.convexHull_inter h1 h2).ge

theorem mem_coloredCayleyComplex_faces
    (hL : AffineIndependent ℝ ((↑) : ↥L → CoordinateSpace e))
    (T : Finset (PolytopalJoinAmbient e m)) :
    T ∈ (coloredCayleyComplex hL eval).faces ↔
      T.Nonempty ∧ ∃ s : Finset (NonnegativeColoredVertex L eval),
        IsColorChoiceFace L eval s ∧ T = s.image coloredCayleyVertex :=
  Iff.rfl

/-- The faces of the geometric complex are exactly the images of the faces of the
abstract join complex `nonnegativeJoinComplex`. -/
theorem coloredCayleyComplex_faces_eq_image
    (hL : AffineIndependent ℝ ((↑) : ↥L → CoordinateSpace e)) :
    (coloredCayleyComplex hL eval).faces =
      (fun s : Finset (NonnegativeColoredVertex L eval) ↦ s.image coloredCayleyVertex) ''
        {s | s ∈ nonnegativeJoinComplex L eval} := by
  ext T
  simp only [mem_coloredCayleyComplex_faces, Set.mem_image, Set.mem_ofPred_eq,
    mem_nonnegativeJoinComplex_iff]
  constructor
  · rintro ⟨hTne, s, hs, rfl⟩
    refine ⟨s, ⟨?_, hs⟩, rfl⟩
    rcases Finset.eq_empty_or_nonempty s with rfl | hsne
    · simp at hTne
    · exact hsne
  · rintro ⟨s, ⟨hsne, hs⟩, rfl⟩
    exact ⟨hsne.image _, s, hs, rfl⟩

end GeometricComplex

section FiberIsPolyhedron

variable {e m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The geometric fiber is the polyhedron of the geometric simplicial complex
of the color-choice faces.**  Together with the acyclicity theorem this says that
the fiber is the realization of an abstract complex whose reduced simplicial
homology vanishes in all degrees `k < L.card`. -/
theorem ridgeNonnegLocus_eq_coloredCayleyComplex_space {L : Finset (CoordinateSpace e)}
    (Φ : PolytopalJoinAmbient e m →L[ℝ] E) (y : StrongDual ℝ E)
    (hL : AffineIndependent ℝ ((↑) : ↥L → CoordinateSpace e)) :
    ridgeNonnegLocus L Φ y = (coloredCayleyComplex hL (ridgeEval Φ y)).space := by
  ext z
  rw [mem_ridgeNonnegLocus_iff_colorChoiceFace, Geometry.SimplicialComplex.space]
  constructor
  · rintro ⟨s, hzs⟩
    rw [joinCellCarrier_cellOfColorFace] at hzs
    rcases Finset.eq_empty_or_nonempty s.1 with hse | hsne
    · rw [hse] at hzs
      simp at hzs
    · refine Set.mem_iUnion₂.mpr ⟨s.1.image coloredCayleyVertex, ?_, hzs⟩
      exact ⟨hsne.image _, s.1, s.2, rfl⟩
  · intro hz
    obtain ⟨T, ⟨-, s, hs, rfl⟩, hzT⟩ := Set.mem_iUnion₂.mp hz
    refine ⟨⟨s, hs⟩, ?_⟩
    rwa [joinCellCarrier_cellOfColorFace]

end FiberIsPolyhedron

/-! ### The comparison gap, now closed

The gap described in this section (the simplicial-to-singular comparison) has
since been proved; see the note at the end of the section.

Everything above is proved: the reduced *simplicial* homology of the finite
family `colorChoiceFamily`, computed with the genuine oriented boundary of
`AffineTverberg/SimplicialHomology.lean`, vanishes in every degree `k < L.card`
(`isReducedAcyclicAt_ridgeColorChoiceFamily`); for an affinely independent ridge
the colored Cayley vertices are affinely independent
(`affineIndependent_coloredCayleyVertex`), the color-choice faces span a genuine
geometric simplicial complex (`coloredCayleyComplex`) whose faces are exactly the
images of the faces of `nonnegativeJoinComplex`
(`coloredCayleyComplex_faces_eq_image`), and the geometric fiber is precisely the
polyhedron of that complex (`ridgeNonnegLocus_eq_coloredCayleyComplex_space`).

What Lemma Y ultimately needs in addition is the vanishing of the reduced
*singular* homology of `ridgeNonnegLocus`.  That was the statement left unproved
here -- never assumed as a hypothesis anywhere, and never hidden inside any
definition of acyclicity -- namely the comparison theorem

`H̃ₖ^{simp}(colorChoiceFamily L (ridgeEval Φ y); 𝕜)`
  `≅ H̃_{k-1}^{sing}((coloredCayleyComplex hL (ridgeEval Φ y)).space; 𝕜)`

i.e. that the simplicial homology of a finite geometric simplicial complex agrees
with the singular homology of its polyhedron.

**This is no longer a gap.**  The general comparison theorem
`AffineTverberg.Simplicial.isIso_comparisonHomologyMap` of
`AffineTverberg/ComparisonInduction.lean` proves, for every finite face-closed
family over a finite linearly ordered vertex type and every ordinary degree,
that the explicit comparison chain map into Mathlib's singular chain complex of
the barycentric realization is a quasi-isomorphism.  Transported along the
verified homeomorphisms of `AffineTverberg/SimplicialFiberRealization.lean` and
`AffineTverberg/SimplicialLemmaY.lean`, this yields
`AffineTverberg.isZero_ridgeNonnegLocusSingularHomology` in
`AffineTverberg/RidgeFiberComparison.lean`: the singular homology of the
concrete geometric fiber `ridgeNonnegLocus L Φ y` vanishes in every degree
`n + 1` with `n + 2 < L.card`. -/

end AffineTverberg
