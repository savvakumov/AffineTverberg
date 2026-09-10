import AffineTverberg.CoefficientReducedHomologyComparison
import AffineTverberg.RidgeLinkRealization
import AffineTverberg.PseudomanifoldCycle
import Mathlib.Data.ZMod.Basic

set_option linter.style.header false

/-!
# A simplicial ball has a boundary ridge

We encode the actual finite geometric complex by a finite ordered vertex type.
Contractibility kills its top homology over `ZMod 2` via the actual comparison
quasi-isomorphism. The mod-two fundamental chain then gives an odd cofacet
count. The local ball theorem bounds this count by two, so it is one.
No boundary-sphere identification or extra manifold hypothesis is used.
-/

noncomputable section

open Set

namespace AffineTverberg.Simplicial

variable {e : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- A finite geometric complex, with the empty face adjoined, has a faithful
finite ordered abstract presentation of exactly the same polyhedron. -/
theorem exists_finite_face_presentation (hfin : K.faces.Finite) :
    ∃ (W : Type) (_ : Fintype W) (_ : LinearOrder W)
      (q : W → CoordinateSpace e) (A : Finset (Finset W)),
      Function.Injective q ∧ FaceClosed A ∧ IsGeometricRealization A q ∧
      geometricCarrier A q = K.space ∧
      (∀ s, s ∈ A ↔ s = ∅ ∨ Finset.image q s ∈ K.faces) ∧
      (∀ F ∈ K.faces, ∃ s ∈ A, Finset.image q s = F) := by
  classical
  let M := hfin.toFinset.biUnion id
  obtain ⟨W, _, _, q, hq, hsurj⟩ := exists_abstract_vertexType M
  let A : Finset (Finset W) := Finset.univ.filter
    (fun s => s = ∅ ∨ Finset.image q s ∈ K.faces)
  have hmem (s : Finset W) : s ∈ A ↔ s = ∅ ∨ Finset.image q s ∈ K.faces := by
    simp [A]
  have hpre (F : Finset (CoordinateSpace e)) (hF : F ∈ K.faces) :
      ∃ s ∈ A, Finset.image q s = F := by
    let s := Finset.univ.filter (fun w => q w ∈ F)
    have himg : Finset.image q s = F := by
      ext x
      constructor
      · rintro hx
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
        simpa [s] using hw
      · intro hx
        have hxM : x ∈ M := Finset.mem_biUnion.mpr
          ⟨F, hfin.mem_toFinset.mpr hF, hx⟩
        obtain ⟨w, rfl⟩ := (hsurj x).mp hxM
        exact Finset.mem_image.mpr ⟨w, by simpa [s] using hx, rfl⟩
    exact ⟨s, (hmem s).mpr (Or.inr (himg ▸ hF)), himg⟩
  have hclosed : FaceClosed A := by
    intro s hs t hts
    apply (hmem t).mpr
    rcases Finset.eq_empty_or_nonempty t with rfl | ht
    · exact Or.inl rfl
    · right
      rcases (hmem s).mp hs with rfl | hsK
      · have : t = ∅ := Finset.subset_empty.mp hts
        exact (ht.ne_empty this).elim
      · exact K.down_closed hsK (Finset.image_subset_image hts) (ht.image q)
  have hgeom : IsGeometricRealization A q :=
    isGeometricRealization_of_image_mem_faces hq (fun s hs hne =>
      ((hmem s).mp hs).resolve_left hne.ne_empty)
  have hcarrier : geometricCarrier A q = K.space := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
      rcases (hmem s).mp hs with rfl | hsK
      · simp at hxs
      · apply Geometry.SimplicialComplex.mem_space_iff.mpr
        exact ⟨Finset.image q s, hsK, by simpa only [Finset.coe_image] using hxs⟩
    · intro hx
      obtain ⟨F, hF, hxF⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
      obtain ⟨s, hs, himg⟩ := hpre F hF
      apply Set.mem_iUnion₂.mpr
      refine ⟨s, hs, ?_⟩
      rw [← Finset.coe_image, himg]
      exact hxF
  exact ⟨W, inferInstance, inferInstance, q, A, hq, hclosed, hgeom,
    hcarrier, hmem, hpre⟩

end AffineTverberg.Simplicial

namespace AffineTverberg.IsSimplicialBall

open AffineTverberg.Simplicial

variable {e n : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- A simplicial ball has a codimension-one face in an odd number of facets.
The coefficient field is genuinely characteristic two, not the reals. -/
theorem exists_odd_facetsThrough (hball : IsSimplicialBall n K) (hn : 2 ≤ n) :
    ∃ L ∈ K.faces, L.card = n ∧ Odd (facetsThrough K L).ncard := by
  classical
  obtain ⟨W, _, _, q, A, hq, hclosed, hgeom, hcarrier, hmem, hpre⟩ :=
    exists_finite_face_presentation hball.finite_faces
  have hcard (s : Finset W) : (Finset.image q s).card = s.card :=
    Finset.card_image_of_injective s hq
  have hmax : ∀ s ∈ A, s.card ≤ n + 1 := by
    intro s hs
    rcases (hmem s).mp hs with rfl | hsK
    · simp
    · rw [← hcard s]
      exact card_le_of_mem_faces hball.finite_faces hball.pure hsK
  have htop (s : Finset W) : s ∈ topSimplices A (n + 1) ↔
      Finset.image q s ∈ K.facets := by
    rw [mem_topSimplices, mem_facets_iff_card hball.finite_faces hball.pure, hcard]
    constructor
    · rintro ⟨hs, hsz⟩
      rcases (hmem s).mp hs with rfl | hsK
      · simp at hsz
      · exact ⟨hsK, hsz⟩
    · rintro ⟨hsK, hsz⟩
      exact ⟨(hmem s).mpr (Or.inr hsK), hsz⟩
  have hne : (topSimplices A (n + 1)).Nonempty := by
    let x : K.space := hball.homeomorph_closedBall.some.symm ⟨0, by simp⟩
    obtain ⟨s, hs, -⟩ := Geometry.SimplicialComplex.mem_space_iff.mp x.property
    obtain ⟨F, hF, -⟩ := exists_facet_superset hball.finite_faces hs
    obtain ⟨s, hs, himg⟩ := hpre F (Geometry.SimplicialComplex.facets_subset hF)
    exact ⟨s, (htop s).mpr (himg ▸ hF)⟩
  have : ContractibleSpace ↥K.space := hball.contractibleSpace_space
  have : ContractibleSpace ↥(geometricCarrier A q) :=
    (Homeomorph.setCongr hcarrier).toHomotopyEquiv.contractibleSpace
  have hacyc : IsReducedAcyclicAt (ZMod 2) A (n + 1) := by
    have h := Coefficients.isReducedAcyclicAt_of_contractible_geometricRealization
      (ZMod 2) hclosed hgeom (n - 1)
    convert h using 1; omega
  obtain ⟨f, hf, hfcard, hfodd⟩ :=
    exists_odd_facetCount_of_isReducedAcyclicAt (𝕜 := ZMod 2) (ZMod.natCast_self 2)
      hclosed hmax hne hacyc
  have hfne : f.Nonempty := Finset.card_pos.mp (by omega)
  have hfK : Finset.image q f ∈ K.faces :=
    ((hmem f).mp hf).resolve_left hfne.ne_empty
  have hfcard' : (Finset.image q f).card = n := by rw [hcard]; omega
  refine ⟨Finset.image q f, hfK, hfcard', ?_⟩
  have hcount : facetCount A (n + 1) f = (facetsThrough K (Finset.image q f)).ncard := by
    rw [facetCount, Set.ncard_eq_toFinset_card _
      (facetsThrough_finite hball.finite_faces (Finset.image q f))]
    refine Finset.card_bij (fun s _ => Finset.image q s) ?_ ?_ ?_
    · intro s hs
      obtain ⟨hs, hfs, -⟩ := Finset.mem_filter.mp hs
      exact (facetsThrough_finite hball.finite_faces _).mem_toFinset.mpr
        ⟨(htop s).mp hs, Finset.image_subset_image hfs⟩
    · intro s hs t ht hst
      exact Finset.image_injective hq hst
    · intro F hF
      have hF' : F ∈ facetsThrough K (Finset.image q f) :=
        (facetsThrough_finite hball.finite_faces _).mem_toFinset.mp hF
      obtain ⟨s, hs, himg⟩ := hpre F (Geometry.SimplicialComplex.facets_subset hF'.1)
      refine ⟨s, Finset.mem_filter.mpr ⟨(htop s).mpr (himg ▸ hF'.1), ?_, ?_⟩, himg⟩
      · apply (Finset.image_subset_image_iff hq).mp
        rw [himg]
        exact hF'.2
      · have hsz : s.card = n + 1 := by rw [← hcard s, himg]; exact hball.pure F hF'.1
        omega
  rwa [← hcount]

/-- Every simplicial ball of dimension at least two has a boundary ridge,
derived solely from the finite, pure, topological-ball hypotheses. -/
theorem exists_isBoundaryRidge (hball : IsSimplicialBall n K) (hn : 2 ≤ n) :
    ∃ L, IsBoundaryRidge n K L :=
  hball.exists_isBoundaryRidge_of_odd hn (hball.exists_odd_facetsThrough hn)

end AffineTverberg.IsSimplicialBall
