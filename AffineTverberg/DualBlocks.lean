import AffineTverberg.BarycentricSubdivisionGeometry
import Mathlib.Analysis.Convex.Contractible

set_option linter.style.header false

/-!
# Dual blocks in the barycentric subdivision

For a face `s` of a finite complex `K` the *dual block* `D(s)` is the
subcomplex of the barycentric subdivision spanned by the chains all of whose
members contain `s`; its *boundary* `∂D(s)` consists of the chains all of whose
members contain `s` strictly.

The results here are the combinatorial backbone of the dual cell decomposition:

* both families are face-closed subfamilies of `subdivisionFaces K`;
* `dualBlockFaces_inter` — blocks intersect in the block of the union;
* `insert_mem_dualBlockFaces` — a block is a cone with apex the vertex `s`,
  hence `starConvex_geometricCarrier_dualBlockFaces`: its polyhedron is
  star-shaped about the barycenter of `s`, and therefore contractible;
* `mem_dualBlockBoundaryFaces_iff` — the boundary of a block is the union of
  the blocks of the faces strictly containing `s`;
* `card_add_card_le_of_mem_dualBlockFaces` — the dimension count
  `dim D(s) ≤ N - dim s` for a complex of dimension `N`.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg.Simplicial

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The dual block of a face: chains all of whose members contain `s`. -/
def dualBlockFaces (K : Finset (Finset V)) (s : Finset V) : Finset (Finset (Finset V)) :=
  (subdivisionFaces K).filter fun C ↦ ∀ t ∈ C, s ⊆ t

/-- The boundary of the dual block: chains all of whose members contain `s`
strictly. -/
def dualBlockBoundaryFaces (K : Finset (Finset V)) (s : Finset V) :
    Finset (Finset (Finset V)) :=
  (subdivisionFaces K).filter fun C ↦ ∀ t ∈ C, s ⊂ t

@[simp]
theorem mem_dualBlockFaces {K : Finset (Finset V)} {s : Finset V} {C : Finset (Finset V)} :
    C ∈ dualBlockFaces K s ↔ C ∈ subdivisionFaces K ∧ ∀ t ∈ C, s ⊆ t := by
  simp [dualBlockFaces]

@[simp]
theorem mem_dualBlockBoundaryFaces {K : Finset (Finset V)} {s : Finset V}
    {C : Finset (Finset V)} :
    C ∈ dualBlockBoundaryFaces K s ↔ C ∈ subdivisionFaces K ∧ ∀ t ∈ C, s ⊂ t := by
  simp [dualBlockBoundaryFaces]

theorem dualBlockFaces_subset (K : Finset (Finset V)) (s : Finset V) :
    dualBlockFaces K s ⊆ subdivisionFaces K := Finset.filter_subset _ _

theorem dualBlockBoundaryFaces_subset (K : Finset (Finset V)) (s : Finset V) :
    dualBlockBoundaryFaces K s ⊆ dualBlockFaces K s := by
  intro C hC
  obtain ⟨hCsd, hC⟩ := mem_dualBlockBoundaryFaces.mp hC
  exact mem_dualBlockFaces.mpr ⟨hCsd, fun t ht ↦ (hC t ht).subset⟩

theorem faceClosed_dualBlockFaces (K : Finset (Finset V)) (s : Finset V) :
    FaceClosed (dualBlockFaces K s) := by
  intro C hC D hDC
  obtain ⟨hCsd, hC⟩ := mem_dualBlockFaces.mp hC
  exact mem_dualBlockFaces.mpr ⟨faceClosed_subdivisionFaces K C hCsd D hDC,
    fun t ht ↦ hC t (hDC ht)⟩

theorem faceClosed_dualBlockBoundaryFaces (K : Finset (Finset V)) (s : Finset V) :
    FaceClosed (dualBlockBoundaryFaces K s) := by
  intro C hC D hDC
  obtain ⟨hCsd, hC⟩ := mem_dualBlockBoundaryFaces.mp hC
  exact mem_dualBlockBoundaryFaces.mpr ⟨faceClosed_subdivisionFaces K C hCsd D hDC,
    fun t ht ↦ hC t (hDC ht)⟩

/-- Dual blocks meet in the dual block of the union. -/
theorem dualBlockFaces_inter (K : Finset (Finset V)) (s t : Finset V) :
    dualBlockFaces K s ∩ dualBlockFaces K t = dualBlockFaces K (s ∪ t) := by
  ext C
  simp only [Finset.mem_inter, mem_dualBlockFaces]
  constructor
  · rintro ⟨⟨hC, hs⟩, ⟨-, ht⟩⟩
    exact ⟨hC, fun u hu ↦ Finset.union_subset (hs u hu) (ht u hu)⟩
  · rintro ⟨hC, hst⟩
    exact ⟨⟨hC, fun u hu ↦ Finset.subset_union_left.trans (hst u hu)⟩,
      ⟨hC, fun u hu ↦ Finset.subset_union_right.trans (hst u hu)⟩⟩

theorem dualBlockFaces_mono {K : Finset (Finset V)} {s t : Finset V} (hst : s ⊆ t) :
    dualBlockFaces K t ⊆ dualBlockFaces K s := by
  intro C hC
  obtain ⟨hCsd, hC⟩ := mem_dualBlockFaces.mp hC
  exact mem_dualBlockFaces.mpr ⟨hCsd, fun u hu ↦ hst.trans (hC u hu)⟩

/-- A dual block is a cone with apex the subdivision vertex `s`. -/
theorem insert_mem_dualBlockFaces {K : Finset (Finset V)} {s : Finset V} (hs : s ∈ K)
    (hsne : s.Nonempty) {C : Finset (Finset V)} (hC : C ∈ dualBlockFaces K s) :
    insert s C ∈ dualBlockFaces K s := by
  obtain ⟨hCsd, hCs⟩ := mem_dualBlockFaces.mp hC
  obtain ⟨hCK, hchain⟩ := mem_subdivisionFaces.mp hCsd
  refine mem_dualBlockFaces.mpr ⟨mem_subdivisionFaces.mpr
    ⟨Finset.insert_subset hs hCK, ⟨?_, ?_⟩⟩, ?_⟩
  · intro u hu
    rcases Finset.mem_insert.mp hu with hus | hu
    · exact hus ▸ hsne
    · exact hchain.1 u hu
  · intro u hu v hv
    rcases Finset.mem_insert.mp hu with hus | hu
    · rcases Finset.mem_insert.mp hv with hvs | hv
      · exact Or.inl (hus.trans hvs.symm).subset
      · exact Or.inl (hus ▸ hCs v hv)
    · rcases Finset.mem_insert.mp hv with hvs | hv
      · exact Or.inr (hvs ▸ hCs u hu)
      · exact hchain.2 u hu v hv
  · intro u hu
    rcases Finset.mem_insert.mp hu with hus | hu
    · exact hus.symm.subset
    · exact hCs u hu

/-- The boundary of a dual block is exactly the union of the dual blocks of the
faces strictly containing `s`. -/
theorem mem_dualBlockBoundaryFaces_iff {K : Finset (Finset V)} {s : Finset V}
    {C : Finset (Finset V)} (hCne : C.Nonempty) :
    C ∈ dualBlockBoundaryFaces K s ↔ ∃ u ∈ K, s ⊂ u ∧ C ∈ dualBlockFaces K u := by
  constructor
  · intro hC
    obtain ⟨hCsd, hC⟩ := mem_dualBlockBoundaryFaces.mp hC
    obtain ⟨hCK, hchain⟩ := mem_subdivisionFaces.mp hCsd
    obtain ⟨u, huC, hmin⟩ := hchain.exists_min hCne
    exact ⟨u, hCK huC, hC u huC, mem_dualBlockFaces.mpr ⟨hCsd, hmin⟩⟩
  · rintro ⟨u, -, hsu, hC⟩
    obtain ⟨hCsd, hCu⟩ := mem_dualBlockFaces.mp hC
    exact mem_dualBlockBoundaryFaces.mpr ⟨hCsd, fun t ht ↦ hsu.trans_le (hCu t ht)⟩

/-- Every nonempty chain lies in the dual block of its least member, so the
dual blocks cover the subdivision. -/
theorem exists_mem_dualBlockFaces {K : Finset (Finset V)} {C : Finset (Finset V)}
    (hC : C ∈ subdivisionFaces K) (hCne : C.Nonempty) :
    ∃ u ∈ K, C ∈ dualBlockFaces K u := by
  obtain ⟨hCK, hchain⟩ := mem_subdivisionFaces.mp hC
  obtain ⟨u, huC, hmin⟩ := hchain.exists_min hCne
  exact ⟨u, hCK huC, mem_dualBlockFaces.mpr ⟨hC, hmin⟩⟩

omit [Fintype V] [DecidableEq V] in
private theorem chain_card_add_card_le_aux (n : ℕ) :
    ∀ C : Finset (Finset V), C.card ≤ n → IsFaceChain C → ∀ s T : Finset V, T ∈ C →
      (∀ t ∈ C, s ⊆ t) → (∀ t ∈ C, t ⊆ T) → C.card + s.card ≤ T.card + 1 := by
  classical
  induction n with
  | zero =>
      intro C hcard _ s T hT _ _
      exact absurd (Finset.card_pos.mpr ⟨T, hT⟩) (by omega)
  | succ n ih =>
      intro C hcard hchain s T hT hs hmax
      have hcardC : C.card = (C.erase T).card + 1 := (Finset.card_erase_add_one hT).symm
      rcases Finset.eq_empty_or_nonempty (C.erase T) with hempty | hne
      · have hsT : s.card ≤ T.card := Finset.card_le_card (hs T hT)
        rw [hcardC, hempty, Finset.card_empty]
        omega
      · obtain ⟨T', hT', hT'max⟩ := (hchain.mono (Finset.erase_subset T C)).exists_max hne
        have hT'C : T' ∈ C := Finset.mem_of_mem_erase hT'
        have hT'ne : T' ≠ T := Finset.ne_of_mem_erase hT'
        have hT'lt : T'.card < T.card :=
          Finset.card_lt_card (lt_of_le_of_ne (hmax T' hT'C) hT'ne)
        have hcard' : (C.erase T).card ≤ n := by omega
        have := ih (C.erase T) hcard' (hchain.mono (Finset.erase_subset T C)) s T' hT'
          (fun t ht ↦ hs t (Finset.mem_of_mem_erase ht)) hT'max
        omega

/-- Dimension count: in a complex whose faces have at most `n` vertices, a chain
in the dual block of `s` has at most `n + 1 - #s` members. -/
theorem card_add_card_le_of_mem_dualBlockFaces {K : Finset (Finset V)} {s : Finset V}
    {n : ℕ} (hcard : ∀ t ∈ K, t.card ≤ n) {C : Finset (Finset V)}
    (hC : C ∈ dualBlockFaces K s) (hCne : C.Nonempty) :
    C.card + s.card ≤ n + 1 := by
  obtain ⟨hCsd, hCs⟩ := mem_dualBlockFaces.mp hC
  obtain ⟨hCK, hchain⟩ := mem_subdivisionFaces.mp hCsd
  obtain ⟨T, hTC, hTmax⟩ := hchain.exists_max hCne
  have h := chain_card_add_card_le_aux C.card C le_rfl hchain s T hTC hCs hTmax
  have := hcard T (hCK hTC)
  omega

section Geometric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Finset (Finset V)} {p : V → E}

/-- The polyhedron of a dual block is star-shaped about the barycenter of `s`:
the block is a geometric cone with that apex. -/
theorem singleton_mem_dualBlockFaces {s : Finset V} (hs : s ∈ K) (hsne : s.Nonempty) :
    ({s} : Finset (Finset V)) ∈ dualBlockFaces K s := by
  refine mem_dualBlockFaces.mpr ⟨mem_subdivisionFaces.mpr
    ⟨Finset.singleton_subset_iff.mpr hs, ⟨?_, ?_⟩⟩, ?_⟩
  · intro u hu; rw [Finset.mem_singleton.mp hu]; exact hsne
  · intro u hu v hv
    rw [Finset.mem_singleton.mp hu, Finset.mem_singleton.mp hv]
    exact Or.inl Finset.Subset.rfl
  · intro u hu; rw [Finset.mem_singleton.mp hu]

theorem faceBarycenter_mem_geometricCarrier_dualBlockFaces {s : Finset V} (hs : s ∈ K)
    (hsne : s.Nonempty) :
    faceBarycenter p s ∈ geometricCarrier (dualBlockFaces K s) (faceBarycenter p) :=
  Set.mem_iUnion₂.mpr ⟨{s}, singleton_mem_dualBlockFaces hs hsne,
    subset_convexHull ℝ _ ⟨s, by simp, rfl⟩⟩

theorem starConvex_geometricCarrier_dualBlockFaces {s : Finset V} (hs : s ∈ K)
    (hsne : s.Nonempty) :
    StarConvex ℝ (faceBarycenter p s)
      (geometricCarrier (dualBlockFaces K s) (faceBarycenter p)) := by
  intro x hx a b ha hb hab
  obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hx
  have hins : insert s C ∈ dualBlockFaces K s := insert_mem_dualBlockFaces hs hsne hC
  have hsubset : (faceBarycenter p) '' (C : Set (Finset V)) ⊆
      (faceBarycenter p) '' ((insert s C : Finset (Finset V)) : Set (Finset V)) :=
    Set.image_mono (by intro t ht; exact Finset.mem_insert_of_mem ht)
  have hxins : x ∈ convexHull ℝ
      ((faceBarycenter p) '' ((insert s C : Finset (Finset V)) : Set (Finset V))) :=
    convexHull_mono hsubset hxC
  have hsins : faceBarycenter p s ∈ convexHull ℝ
      ((faceBarycenter p) '' ((insert s C : Finset (Finset V)) : Set (Finset V))) :=
    subset_convexHull ℝ _ ⟨s, by simp, rfl⟩
  exact Set.mem_iUnion₂.mpr ⟨insert s C, hins,
    (convex_convexHull ℝ _) hsins hxins ha hb hab⟩

theorem contractible_geometricCarrier_dualBlockFaces {s : Finset V} (hs : s ∈ K)
    (hsne : s.Nonempty) :
    ContractibleSpace ↥(geometricCarrier (dualBlockFaces K s) (faceBarycenter p)) := by
  have hmem : faceBarycenter p s ∈
      geometricCarrier (dualBlockFaces K s) (faceBarycenter p) :=
    faceBarycenter_mem_geometricCarrier_dualBlockFaces hs hsne
  exact StarConvex.contractibleSpace
    (starConvex_geometricCarrier_dualBlockFaces (p := p) hs hsne) ⟨_, hmem⟩

end Geometric

end AffineTverberg.Simplicial

end
