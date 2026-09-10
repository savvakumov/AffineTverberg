import AffineTverberg.PolytopeFacet
import AffineTverberg.PullingPurity

set_option linter.style.header false

/-!
# Purity of the general polytopal bad-vertex triangulation

The abstract purity theorem `AffineTverberg.BadEdge.sdPoset_purity` applies to
the face family `faceFamily P m` of the Cayley join `Q = P * ⋯ * P` once the
family is shown to be *apex graded*: a face `G ⊆ S` of the family missing the
apex of `S` extends to a face `H ⊆ S` of the family which still misses the apex
and has `jrank H + 1 = jrank S`.

This is proved factorwise from the facet lemma
`AffineTverberg.PolytopeFace.exists_facet_exposed_avoiding`: keep every factor
of `S` except the one containing the missing apex vertex, and replace that
factor by a facet of it containing the corresponding factor of `G` and avoiding
the missing vertex.

## Main results

* `apexGraded_faceFamily` — the face family of the Cayley join is apex graded.
* `sdQ_purity` — every simplex of `sdQ P m S` extends to an apex-flag simplex
  of `S`, which by `IsApexFlag.card_eq_rank` has exactly `jrank S` vertices.
* `sdQ_exists_top_extension_good` — the extension has `jrank S` vertices and at
  least `projDim S + 1` good vertices; for the whole join
  (`sdQ_top_extension_good`) at least `n + 1`.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg
namespace BadVertex

open CayleyJoin PolytopeFace BadEdge

variable {n : ℕ} {P : FullDimensionalPolytope n} {m : ℕ}

/-! ### Faces of `P` and their actual vertices -/

/-- The actual vertices of `P` lying in a subset. -/
def faceActualVertices (P : FullDimensionalPolytope n) (A : Set (CoordinateSpace n)) :
    Finset (CoordinateSpace n) := by
  classical
  exact P.actualVertices.filter fun v ↦ v ∈ A

theorem mem_faceActualVertices {A : Set (CoordinateSpace n)} {v : CoordinateSpace n} :
    v ∈ faceActualVertices P A ↔ v ∈ P.actualVertices ∧ v ∈ A := by
  classical
  simp [faceActualVertices]

theorem coe_faceActualVertices (A : Set (CoordinateSpace n)) :
    ((faceActualVertices P A : Finset (CoordinateSpace n)) : Set (CoordinateSpace n)) =
      A ∩ (P.actualVertices : Set (CoordinateSpace n)) := by
  ext v
  simp only [Finset.mem_coe, mem_faceActualVertices, mem_inter_iff, Finset.mem_coe]
  exact ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩

/-- A face of `P` is the convex hull of the actual vertices it contains. -/
theorem face_eq_convexHull_faceActualVertices {A : Set (CoordinateSpace n)}
    (hA : P.IsFace A) :
    A = convexHull ℝ ((faceActualVertices P A : Finset (CoordinateSpace n)) :
      Set (CoordinateSpace n)) := by
  rw [coe_faceActualVertices]
  exact P.face_eq_convexHull_actualVertices hA

/-- A face of `P` contained in another face is a face of it. -/
theorem isExposed_of_face_subset {A G : Set (CoordinateSpace n)} (hA : P.IsFace A)
    (hG : P.IsFace G) (hGA : G ⊆ A) : IsExposed ℝ A G := by
  intro hGne
  obtain ⟨l, hl⟩ := hG hGne
  obtain ⟨p, hp⟩ := hGne
  refine ⟨l, ?_⟩
  have hAP : A ⊆ P.carrier := hA.subset
  have hpmax : ∀ y ∈ P.carrier, l y ≤ l p := by
    intro y hy
    rw [hl] at hp
    exact hp.2 y hy
  ext x
  constructor
  · intro hx
    refine ⟨hGA hx, fun y hy ↦ ?_⟩
    rw [hl] at hx
    exact hx.2 y (hAP hy)
  · rintro ⟨hxA, hxmax⟩
    have hxP : x ∈ P.carrier := hAP hxA
    have h1 : l p ≤ l x := hxmax p (hGA hp)
    have h2 : l x ≤ l p := hpmax x hxP
    have hxeq : l x = l p := le_antisymm h2 h1
    rw [hl]
    refine ⟨hxP, fun y hy ↦ ?_⟩
    rw [hxeq]
    exact hpmax y hy

/-! ### The factors of a face of the Cayley join -/

theorem arank_factorPts_faceVertexSet (C : Fin (m + 1) → PolytopeFaceIndex P)
    (i : Fin (m + 1)) :
    arank (factorPts P m (faceVertexSet P m C) i) = arank ((C i).carrier) :=
  arank_eq_of_affineSpan_eq (affineSpan_factorPts_faceVertexSet C i)

/-! ### Apex gradedness of the polytopal face family -/

/-- **The face family of the Cayley join is apex graded.**  This is the
polytopal input of purity: it is proved factorwise from the facet lemma for
`V`-polytopes. -/
theorem apexGraded_faceFamily (P : FullDimensionalPolytope n) (m : ℕ) :
    ApexGraded (origIndex P m) (faceFamily P m) (jrank P m) := by
  classical
  intro S hS G hG hGS hna
  obtain ⟨w, hwapex, hwG⟩ := Finset.not_subset.mp hna
  have hwS : w ∈ S := apexSet_subset _ S hwapex
  obtain ⟨C, rfl⟩ := (mem_faceFamily_iff P m).mp hS
  obtain ⟨C', rfl⟩ := (mem_faceFamily_iff P m).mp hG
  set i₀ := w.1 with hi₀
  set a := vtx P w.2 with hadef
  set A := (C i₀).carrier with hA
  set G₀ := (C' i₀).carrier with hG₀
  have haA : a ∈ A := (mem_faceVertexSet P m).mp hwS
  have haG : a ∉ G₀ := fun hmem ↦ hwG ((mem_faceVertexSet P m).mpr hmem)
  -- the smaller factor sits inside the bigger one
  have hG₀A : G₀ ⊆ A := by
    rw [hG₀, face_eq_convexHull_faceActualVertices ((C' i₀).isFace)]
    refine convexHull_min ?_ ((C i₀).convex)
    intro v hv
    rw [coe_faceActualVertices] at hv
    obtain ⟨k, rfl⟩ := exists_vtx P (Finset.mem_coe.mp hv.2)
    have hmem : ((i₀, k) : JoinVertex P m) ∈ faceVertexSet P m C' :=
      (mem_faceVertexSet P m).mpr hv.1
    have := (mem_faceVertexSet P m).mp (hGS hmem)
    exact this
  have hGexp : IsExposed ℝ A G₀ :=
    isExposed_of_face_subset ((C i₀).isFace) ((C' i₀).isFace) hG₀A
  -- the facet lemma inside the factor
  set sA := faceActualVertices P A with hsA
  have hAhull : A = convexHull ℝ ((sA : Finset (CoordinateSpace n)) : Set (CoordinateSpace n)) :=
    face_eq_convexHull_faceActualVertices ((C i₀).isFace)
  obtain ⟨F, hFexp, hGF, haF, hFrank⟩ :=
    exists_facet_exposed_avoiding (s := sA) (F₀ := G₀) (a := a)
      (by rw [← hAhull]; exact hGexp) (by rw [← hAhull]; exact haA)
      haG
  rw [← hAhull] at hFexp hFrank
  -- the facet is a face of `P`
  have hFface : P.IsFace F := by
    have hPhull : P.carrier =
        convexHull ℝ ((P.actualVertices : Finset (CoordinateSpace n)) :
          Set (CoordinateSpace n)) := P.convexHull_actualVertices.symm
    have hAexp : IsExposed ℝ (convexHull ℝ
        ((P.actualVertices : Finset (CoordinateSpace n)) : Set (CoordinateSpace n))) A := by
      rw [← hPhull]; exact (C i₀).isFace
    have := isExposed_trans_convexHull hAexp hFexp
    rw [← hPhull] at this
    exact this
  -- the new tuple of faces
  set C'' := Function.update C i₀ (PolytopeFaceIndex.ofFace F hFface) with hC''
  have hC''i₀ : (C'' i₀).carrier = F := by
    rw [hC'', Function.update_self, PolytopeFaceIndex.carrier_ofFace]
  have hC''ne : ∀ i, i ≠ i₀ → C'' i = C i := by
    intro i hi
    rw [hC'', Function.update_of_ne hi]
  refine ⟨faceVertexSet P m C'', by rw [mem_faceFamily_iff]; exact ⟨C'', rfl⟩, ?_, ?_, ?_, ?_⟩
  · -- `G ⊆ H`
    intro x hx
    rw [mem_faceVertexSet] at hx ⊢
    by_cases hxi : x.1 = i₀
    · rw [hxi, hC''i₀]
      apply hGF
      rw [hG₀, ← hxi]
      exact hx
    · rw [hC''ne x.1 hxi]
      exact (mem_faceVertexSet P m).mp (hGS ((mem_faceVertexSet P m).mpr hx))
  · -- `H ⊆ S`
    intro x hx
    rw [mem_faceVertexSet] at hx ⊢
    by_cases hxi : x.1 = i₀
    · rw [hxi] at hx ⊢
      rw [hC''i₀] at hx
      exact hFexp.subset hx
    · rwa [hC''ne x.1 hxi] at hx
  · -- the apex is still missed
    intro hsub
    have hwmem := hsub hwapex
    rw [mem_faceVertexSet, ← hi₀, hC''i₀, ← hadef] at hwmem
    exact haF hwmem
  · -- the rank drops by exactly one
    have hfac : ∀ i, i ≠ i₀ →
        arank (factorPts P m (faceVertexSet P m C'') i)
          = arank (factorPts P m (faceVertexSet P m C) i) := by
      intro i hi
      rw [arank_factorPts_faceVertexSet, arank_factorPts_faceVertexSet, hC''ne i hi]
    have hi₀eq : arank (factorPts P m (faceVertexSet P m C'') i₀) = arank F := by
      rw [arank_factorPts_faceVertexSet, hC''i₀]
    have hSi₀ : arank (factorPts P m (faceVertexSet P m C) i₀) = arank A := by
      rw [arank_factorPts_faceVertexSet]
    unfold jrank
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i₀),
      ← Finset.sum_erase_add (Finset.univ : Finset (Fin (m + 1)))
        (fun i ↦ arank (factorPts P m (faceVertexSet P m C) i)) (Finset.mem_univ i₀)]
    have hsum : ∑ i ∈ Finset.univ.erase i₀,
          arank (factorPts P m (faceVertexSet P m C'') i)
        = ∑ i ∈ Finset.univ.erase i₀,
          arank (factorPts P m (faceVertexSet P m C) i) :=
      Finset.sum_congr rfl fun i hi ↦ hfac i (Finset.ne_of_mem_erase hi)
    rw [hsum, hi₀eq, hSi₀]
    omega

theorem nonempty_of_jrank_ne_zero {S : Finset (JoinVertex P m)}
    (h : jrank P m S ≠ 0) : S.Nonempty := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact absurd (jrank_eq_zero_iff.mpr rfl) h
  · exact hne

/-! ### Purity of the triangulation -/

/-- **Purity of the polytopal bad-vertex triangulation.**  Every simplex of the
triangulation of a face `S` of the Cayley join extends to an apex-flag simplex
of `S`. -/
theorem sdQ_purity {S : Finset (JoinVertex P m)} (hS : S ∈ faceFamily P m)
    {σ : Finset (Finset (JoinVertex P m))} (hσ : σ ∈ sdQ P m S) :
    ∃ τ, IsApexFlag (origIndex P m) (faceFamily P m) (jrank P m) S τ ∧ σ ⊆ τ :=
  sdPoset_purity (apexGraded_faceFamily P m) (empty_mem_faceFamily P m)
    (fun _ _ h ↦ nonempty_of_jrank_ne_zero h) hS hσ

/-- Full simplices of the triangulation of a face exist. -/
theorem exists_isApexFlag_faceFamily {S : Finset (JoinVertex P m)}
    (hS : S ∈ faceFamily P m) :
    ∃ τ, IsApexFlag (origIndex P m) (faceFamily P m) (jrank P m) S τ :=
  exists_isApexFlag (apexGraded_faceFamily P m) (empty_mem_faceFamily P m)
    (fun _ _ h ↦ nonempty_of_jrank_ne_zero h) hS

/-- **Purity in the form consumed by local acyclicity**: every simplex of the
triangulation of the face `S` is contained in a simplex with exactly `jrank S`
vertices, at least `projDim S + 1` of which are good. -/
theorem sdQ_exists_top_extension_good {S : Finset (JoinVertex P m)}
    (hS : S ∈ faceFamily P m) (hS1 : 1 ≤ jrank P m S)
    {σ : Finset (Finset (JoinVertex P m))} (hσ : σ ∈ sdQ P m S) :
    ∃ τ ∈ sdQ P m S, σ ⊆ τ ∧ τ.card = jrank P m S ∧
      projDim P m S + 1 ≤ (goodVertices τ).card := by
  obtain ⟨τ, hτ, hστ⟩ := sdQ_purity hS hσ
  exact ⟨τ, hτ.mem_sdPoset, hστ, hτ.card_eq_rank,
    card_goodVertices_ge_projDim_succ hS hS1 hτ⟩

/-- The same statement for the whole Cayley join: every simplex extends to one
with `jrank Q` vertices, at least `n + 1` of which are good. -/
theorem sdQ_top_extension_good {σ : Finset (Finset (JoinVertex P m))}
    (hσ : σ ∈ sdQ P m (topFace P m)) :
    ∃ τ ∈ sdQ P m (topFace P m), σ ⊆ τ ∧ τ.card = jrank P m (topFace P m) ∧
      n + 1 ≤ (goodVertices τ).card := by
  obtain ⟨τ, hτ, hστ⟩ := sdQ_purity (topFace_mem_faceFamily P m) hσ
  exact ⟨τ, hτ.mem_sdPoset, hστ, hτ.card_eq_rank, card_goodVertices_ge_of_top hτ⟩

end BadVertex
end AffineTverberg
