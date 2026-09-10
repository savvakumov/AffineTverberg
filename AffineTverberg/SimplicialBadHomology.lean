import AffineTverberg.BadEdgeFreeFacets
import AffineTverberg.BadEdgeSubdivisionGlobalRetraction
import AffineTverberg.SimplicialCohomology

set_option linter.style.header false

/-!
# Vanishing of the top homology of the actual bad subcomplex

The finite family used in the private-facet counting argument is instantiated
by joins of boundary ridges of the given geometric simplicial complex. Every
boundary join face extends to such a ridge join. We then identify the bad
subcomplex with the one in the geometric subdivision and prove its top
simplicial homology vanishes for `r = m + 1 ≥ 3`.

This does not yet invoke Alexander duality or conclude deleted-join cohomology
vanishing. It establishes the bad-complex side of that duality argument.
-/

noncomputable section

open scoped BigOperators
open AffineTverberg.Simplicial

namespace AffineTverberg.BadEdge

variable {e n m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
variable {W : Type*} [Fintype W] [LinearOrder W]
variable (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e)

omit [Fintype W] [LinearOrder W] in
/-- The cardinality of a join face is the sum of its factor cardinalities. -/
theorem card_eq_sum_card_joinFactor (hinj : Function.Injective fun w ↦ (idx w, vert w))
    (S : Finset W) : S.card = ∑ i, (joinFactor idx vert S i).card := by
  classical
  have hsum := Finset.card_eq_sum_card_fiberwise
    (f := idx) (s := S) (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  symm
  apply Finset.card_image_iff.mpr
  intro u hu w hw hv
  have hui := (Finset.mem_filter.mp hu).2
  have hwi := (Finset.mem_filter.mp hw).2
  exact hinj (Prod.ext (hui.trans hwi.symm) hv)

/-- Maximal boundary-join cells, represented as colored vertex sets. -/
def ridgeJoinFaces : Finset (Finset W) := by
  classical
  exact Finset.univ.filter fun S ↦ ∀ i, IsBoundaryRidge n K (joinFactor idx vert S i)

omit [LinearOrder W] in
@[simp]
theorem mem_ridgeJoinFaces {S : Finset W} :
    S ∈ ridgeJoinFaces (n := n) (K := K) idx vert ↔
      ∀ i, IsBoundaryRidge n K (joinFactor idx vert S i) := by
  classical
  simp [ridgeJoinFaces]

omit [LinearOrder W] in
theorem isJoinFace_of_mem_ridgeJoinFaces {S : Finset W}
    (hS : S ∈ ridgeJoinFaces (n := n) (K := K) idx vert) : IsJoinFace n K idx vert S := by
  intro i
  have hi := mem_ridgeJoinFaces idx vert |>.mp hS i
  exact Or.inr ⟨hi.1, _, hi, Finset.Subset.refl _⟩

omit [LinearOrder W] in
theorem card_ridgeJoinFace (hinj : Function.Injective fun w ↦ (idx w, vert w))
    {S : Finset W} (hS : S ∈ ridgeJoinFaces (n := n) (K := K) idx vert) :
    S.card = (m + 1) * n := by
  rw [card_eq_sum_card_joinFactor idx vert hinj]
  have hi : ∀ i, (joinFactor idx vert S i).card = n :=
    fun i ↦ (mem_ridgeJoinFaces idx vert |>.mp hS i).2.1
  simp [hi]

omit [LinearOrder W] in
theorem card_original_ridgeJoinFace {S : Finset W}
    (hS : S ∈ ridgeJoinFaces (n := n) (K := K) idx vert) : n ≤ (S.image vert).card := by
  classical
  have hsub : joinFactor idx vert S 0 ⊆ S.image vert := by
    intro x hx
    obtain ⟨w, hw, _, rfl⟩ := mem_joinFactor.mp hx
    exact Finset.mem_image_of_mem _ hw
  have hcard := Finset.card_le_card hsub
  rwa [(mem_ridgeJoinFaces idx vert |>.mp hS 0).2.1] at hcard

omit [LinearOrder W] in
/-- Every boundary join face extends to a join of ridges, when a ridge exists.
Empty factors can use any fixed boundary ridge. -/
theorem exists_ridgeJoinFace_extension
    (hcover : ∀ (i : Fin (m + 1)) (s : Finset (CoordinateSpace e)),
      IsBoundarySimplicialFace n K s → ∀ v ∈ s, ∃ w, idx w = i ∧ vert w = v)
    (hR : ∃ R, IsBoundaryRidge n K R)
    {S : Finset W} (hS : IsJoinFace n K idx vert S) :
    ∃ T ∈ ridgeJoinFaces (n := n) (K := K) idx vert, S ⊆ T := by
  classical
  obtain ⟨R, hR⟩ := hR
  have hf : ∀ i, ∃ f, IsBoundaryRidge n K f ∧ joinFactor idx vert S i ⊆ f := by
    intro i
    rcases hS i with hemp | hface
    · exact ⟨R, hR, by rw [hemp]; exact Finset.empty_subset _⟩
    · exact hface.2
  choose f hf using hf
  have hfc : ∀ (i : Fin (m + 1)) (v : CoordinateSpace e), v ∈ f i →
      ∃ w, idx w = i ∧ vert w = v := by
    intro i v hv
    exact hcover i (f i) ⟨(hf i).1.1, f i, (hf i).1, Finset.Subset.refl _⟩ v hv
  refine ⟨preimageJoinFace idx vert f, (mem_ridgeJoinFaces idx vert).mpr ?_, ?_⟩
  · intro i
    rw [joinFactor_preimageJoinFace idx vert hfc i]
    exact (hf i).1
  · intro w hw
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (hf (idx w)).2 (mem_joinFactor.mpr ⟨w, hw, rfl, rfl⟩)⟩

omit [Fintype W] [LinearOrder W] in
/-- A nonempty join face witnesses the existence of a boundary ridge. -/
theorem exists_boundaryRidge_of_nonempty_joinFace {S : Finset W}
    (hS : IsJoinFace n K idx vert S) (hne : S.Nonempty) :
    ∃ R, IsBoundaryRidge n K R := by
  obtain ⟨w, hw⟩ := hne
  have hv : vert w ∈ joinFactor idx vert S (idx w) := mem_joinFactor.mpr ⟨w, hw, rfl, rfl⟩
  rcases hS (idx w) with hemp | hface
  · rw [hemp] at hv
    exact False.elim (Finset.notMem_empty _ hv)
  · obtain ⟨R, hR, _⟩ := hface.2
    exact ⟨R, hR⟩

/-- The bad subcomplex of the actual compatible geometric subdivision. -/
def badJoinFaces : Finset (Finset (Finset W)) :=
  inducedFaces (sdJoinFaces n K idx vert) (goodSdVertices W)ᶜ

@[simp]
theorem mem_badJoinFaces {τ : Finset (Finset W)} :
    τ ∈ badJoinFaces (n := n) (K := K) idx vert ↔
      τ ∈ sdJoinFaces n K idx vert ∧ (∀ s ∈ τ, ¬ IsGoodSdVertex s) := by
  classical
  simp only [badJoinFaces, mem_inducedFaces, Finset.subset_iff, Finset.mem_compl,
    mem_goodSdVertices]

theorem faceClosed_badJoinFaces : FaceClosed (badJoinFaces (n := n) (K := K) idx vert) :=
  faceClosed_inducedFaces (faceClosed_sdJoinFaces idx vert) _

/-- When the boundary is nonempty, the bad complex is the union over ridge
joins to which the counting theorem applies. -/
theorem badJoinFaces_eq_badFacesOfFamily
    (hcover : ∀ (i : Fin (m + 1)) (s : Finset (CoordinateSpace e)),
      IsBoundarySimplicialFace n K s → ∀ v ∈ s, ∃ w, idx w = i ∧ vert w = v)
    (hR : ∃ R, IsBoundaryRidge n K R) :
    badJoinFaces (n := n) (K := K) idx vert =
      badFacesOfFamily vert (ridgeJoinFaces (n := n) (K := K) idx vert) := by
  classical
  ext τ
  rw [mem_badJoinFaces, mem_badFacesOfFamily]
  constructor
  · rintro ⟨hτ, hbad⟩
    obtain ⟨S, hS, hτS⟩ := (mem_sdJoinFaces idx vert).mp hτ
    obtain ⟨T, hT, hST⟩ := exists_ridgeJoinFace_extension idx vert hcover hR hS
    exact ⟨⟨T, hT, sdFaces_mono vert hST hτS⟩, hbad⟩
  · rintro ⟨⟨S, hS, hτS⟩, hbad⟩
    exact ⟨(mem_sdJoinFaces idx vert).mpr
      ⟨S, isJoinFace_of_mem_ridgeJoinFaces idx vert hS, hτS⟩, hbad⟩

/-- Every top bad simplex in the actual boundary join has a private facet.
The empty-boundary case is handled without assuming a ridge exists. -/
theorem hasFreeFacets_badJoinFaces (hm : 2 ≤ m) (hn : 0 < n)
    (hinj : Function.Injective fun w ↦ (idx w, vert w))
    (hcover : ∀ (i : Fin (m + 1)) (s : Finset (CoordinateSpace e)),
      IsBoundarySimplicialFace n K s → ∀ v ∈ s, ∃ w, idx w = i ∧ vert w = v) :
    HasFreeFacets (topSimplices (badJoinFaces (n := n) (K := K) idx vert) (m * n)) := by
  classical
  by_cases hR : ∃ R, IsBoundaryRidge n K R
  · rw [badJoinFaces_eq_badFacesOfFamily idx vert hcover hR]
    exact hasFreeFacets_badFacesOfFamily hm hn idx vert hinj _
      (fun S hS ↦ (card_ridgeJoinFace idx vert hinj hS).le)
      (fun S hS ↦ card_original_ridgeJoinFace idx vert hS)
  · intro τ
    obtain ⟨hτ, hcard⟩ := mem_topSimplices.mp τ.property
    obtain ⟨S, hS, hτS⟩ := (mem_sdJoinFaces idx vert).mp ((mem_badJoinFaces idx vert).mp hτ).1
    have hsize := sdFaces_card_le vert S hτS
    have hSnonempty : S.Nonempty := Finset.card_pos.mp (by
      have : 0 < m * n := Nat.mul_pos (by omega) hn
      omega)
    exact False.elim (hR (exists_boundaryRidge_of_nonempty_joinFace idx vert hS hSnonempty))

section Homology

variable [LinearOrder (Finset W)] (𝕜 : Type*) [Field 𝕜]

/-- The bad-complex homology vanishing used in the simplicial-ball argument:
augmented degree `m * n` is geometric degree `(r - 1) * n - 1`. -/
theorem homology_badJoinFaces_subsingleton (hm : 2 ≤ m) (hn : 0 < n)
    (hinj : Function.Injective fun w ↦ (idx w, vert w))
    (hcover : ∀ (i : Fin (m + 1)) (s : Finset (CoordinateSpace e)),
      IsBoundarySimplicialFace n K s → ∀ v ∈ s, ∃ w, idx w = i ∧ vert w = v) :
    Subsingleton (homology 𝕜 (badJoinFaces (n := n) (K := K) idx vert) (m * n)) :=
  homology_top_subsingleton_of_hasFreeFacets (hasFreeFacets_badJoinFaces idx vert hm hn hinj hcover)

/-- The corresponding actual dual simplicial-cochain quotient also vanishes. -/
theorem cohomology_badJoinFaces_subsingleton (hm : 2 ≤ m) (hn : 0 < n)
    (hinj : Function.Injective fun w ↦ (idx w, vert w))
    (hcover : ∀ (i : Fin (m + 1)) (s : Finset (CoordinateSpace e)),
      IsBoundarySimplicialFace n K s → ∀ v ∈ s, ∃ w, idx w = i ∧ vert w = v) :
    Subsingleton (cohomology 𝕜 (faceClosed_badJoinFaces (n := n) (K := K) idx vert) (m * n)) :=
  cohomology_subsingleton_of_hasFreeFacets (faceClosed_badJoinFaces idx vert)
    (hasFreeFacets_badJoinFaces idx vert hm hn hinj hcover)

end Homology

end AffineTverberg.BadEdge
