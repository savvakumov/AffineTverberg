import AffineTverberg.BadEdgeSubdivisionCayley
import AffineTverberg.SimplicialCellStructure

set_option linter.style.header false

/-!
# The bad-edge subdivision of the whole join complex

The previous files subdivide one join face at a time.  By compatibility
(`sdFaces_mono`) these subdivisions agree on shared subfaces, so they assemble
into a subdivision `sdJoinComplex` of the whole join complex `(∂K)^{*(m+1)}`
realized on the Cayley points.

The join vertices are indexed by a finite linearly ordered type `W`, with
`idx w` the join factor of `w` and `vert w` the original vertex of which `w` is
a copy.  Two hypotheses connect this indexing with the complex `K`:

* `hinj` : distinct join vertices are distinct copies;
* `hcover` : every vertex of a boundary face of `K` has a copy in every factor.

Both are satisfied by the tautological indexing of the copies of the vertices,
and neither refers to the subdivision.

## Main results

* `iUnion_deleted_joinFactor_eq_deletedJoin` : the join cells of the deleted
  join faces are exactly the cells of `simplicialDeletedJoinCarrier`;
* `iUnion_sdRealize_sdJoinComplex` : the subdivision covers the join complex;
* `iUnion_good_sdRealize_eq_deletedJoin` : **the good induced subcomplex of the
  subdivision triangulates exactly the deleted join**
  `simplicialDeletedJoinCarrier n K m`.
-/

open scoped BigOperators
open Set

namespace AffineTverberg
namespace BadEdge

variable {e n m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
variable {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]

/-- A set of join vertices spans a face of the join complex when each of its
factorwise vertex sets is empty or a boundary face of `K`. -/
def IsJoinFace (n : ℕ) (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e) (S : Finset W) : Prop :=
  ∀ i, joinFactor idx vert S i = ∅ ∨ IsBoundarySimplicialFace n K (joinFactor idx vert S i)

omit [Fintype W] [DecidableEq W] [LinearOrder W] in
theorem IsJoinFace.mono {idx : W → Fin (m + 1)} {vert : W → CoordinateSpace e}
    {S T : Finset W} (hS : IsJoinFace n K idx vert S) (hTS : T ⊆ S) :
    IsJoinFace n K idx vert T := by
  intro i
  rcases (joinFactor idx vert T i).eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · rcases hS i with hS' | hS'
    · obtain ⟨x, hx⟩ := h
      have hxS := joinFactor_mono hTS i hx
      rw [hS'] at hxS
      exact absurd hxS (Finset.notMem_empty x)
    · exact Or.inr (hS'.mono (joinFactor_mono hTS i) h)

omit [Fintype W] [DecidableEq W] [LinearOrder W] in
/-- A deleted join face determines a cell of the deleted join. -/
theorem isBoundaryDeletedJoinCell_joinFactor {idx : W → Fin (m + 1)}
    {vert : W → CoordinateSpace e} {T : Finset W}
    (hdel : IsDeletedFace vert T) (hface : IsJoinFace n K idx vert T) :
    IsBoundaryDeletedJoinCell n K (joinFactor idx vert T) :=
  ⟨hface, pairwise_disjoint_joinFactor hdel⟩

section Cells

variable (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e)

/-- The join face consisting of all join vertices whose original vertex belongs
to the given cell in their own factor. -/
noncomputable def preimageJoinFace (f : Fin (m + 1) → Finset (CoordinateSpace e)) :
    Finset W := by
  classical
  exact Finset.univ.filter fun w ↦ vert w ∈ f (idx w)

omit [DecidableEq W] [LinearOrder W] in
theorem joinFactor_preimageJoinFace {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    (hf : ∀ (i : Fin (m + 1)) (v : CoordinateSpace e), v ∈ f i → ∃ w, idx w = i ∧ vert w = v)
    (i : Fin (m + 1)) :
    joinFactor idx vert (preimageJoinFace idx vert f) i = f i := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw, hwi, hwx⟩ := mem_joinFactor.mp hx
    have hmem := (Finset.mem_filter.mp hw).2
    rw [hwi, hwx] at hmem
    exact hmem
  · intro hx
    obtain ⟨w, hwi, hwx⟩ := hf i x hx
    refine mem_joinFactor.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, ?_⟩, hwi, hwx⟩
    rw [hwi, hwx]
    exact hx

omit [DecidableEq W] [LinearOrder W] in
theorem isDeletedFace_preimageJoinFace
    (hinj : Function.Injective fun w ↦ (idx w, vert w))
    {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    (hdisj : Pairwise fun i j ↦ Disjoint (f i) (f j)) :
    IsDeletedFace vert (preimageJoinFace idx vert f) := by
  classical
  intro w hw w' hw' hvv
  have h1 := (Finset.mem_filter.mp hw).2
  have h2 := (Finset.mem_filter.mp hw').2
  have hidx : idx w = idx w' := by
    by_contra hne
    have hd : Disjoint (f (idx w)) (f (idx w')) := hdisj hne
    rw [Finset.disjoint_left] at hd
    exact hd h1 (by rw [hvv]; exact h2)
  exact hinj (show (idx w, vert w) = (idx w', vert w') by rw [hidx, hvv])

omit [Fintype W] [DecidableEq W] [LinearOrder W] in
/-- **The deleted join faces realize exactly the deleted join.** -/
theorem iUnion_deleted_joinFactor_eq_deletedJoin [Finite W]
    (hinj : Function.Injective fun w ↦ (idx w, vert w))
    (hcover : ∀ (i : Fin (m + 1)) (s : Finset (CoordinateSpace e)),
      IsBoundarySimplicialFace n K s → ∀ v ∈ s, ∃ w, idx w = i ∧ vert w = v) :
    (⋃ T ∈ {T : Finset W | IsDeletedFace vert T ∧ IsJoinFace n K idx vert T},
        joinCellCarrier (joinFactor idx vert T)) = simplicialDeletedJoinCarrier n K m := by
  classical
  have : Fintype W := Fintype.ofFinite W
  apply Set.Subset.antisymm
  · refine Set.iUnion₂_subset fun T hT ↦ ?_
    exact joinCellCarrier_subset_simplicialDeletedJoinCarrier K
      (isBoundaryDeletedJoinCell_joinFactor hT.1 hT.2)
  · intro x hx
    obtain ⟨f, hf, hxf⟩ := (mem_simplicialDeletedJoinCarrier_iff K x).mp hx
    have hfvert : ∀ (i : Fin (m + 1)) (v : CoordinateSpace e), v ∈ f i →
        ∃ w, idx w = i ∧ vert w = v := by
      intro i v hv
      rcases hf.1 i with hemp | hbd
      · rw [hemp] at hv
        exact absurd hv (Finset.notMem_empty v)
      · exact hcover i (f i) hbd v hv
    have hfac : joinFactor idx vert (preimageJoinFace idx vert f) = f :=
      funext fun i ↦ joinFactor_preimageJoinFace idx vert hfvert i
    refine Set.mem_iUnion₂.mpr ⟨preimageJoinFace idx vert f, ⟨?_, ?_⟩, ?_⟩
    · exact isDeletedFace_preimageJoinFace idx vert hinj hf.2
    · intro i
      rw [hfac]
      exact hf.1 i
    · rw [hfac]
      exact hxf

end Cells

section Global

variable (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e)

/-- The bad-edge subdivision of the whole join complex: the simplices of the
subdivisions of all its faces.  By `sdFaces_mono` these agree on common
subfaces. -/
def sdJoinComplex (n : ℕ) (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e) : Set (Finset (Finset W)) :=
  {σ | ∃ S, IsJoinFace n K idx vert S ∧ σ ∈ sdFaces vert S}

/-- **The subdivision covers the join complex.** -/
theorem iUnion_sdRealize_sdJoinComplex :
    (⋃ σ ∈ sdJoinComplex n K idx vert, sdRealize (cayleyPt idx vert) σ) =
      ⋃ S ∈ {S : Finset W | IsJoinFace n K idx vert S},
        joinCellCarrier (joinFactor idx vert S) := by
  apply Set.Subset.antisymm
  · refine Set.iUnion₂_subset fun σ hσ ↦ ?_
    obtain ⟨S, hS, hσS⟩ := hσ
    refine subset_trans (sdRealize_subset_convexHull vert hσS) ?_
    rw [convexHull_cayleyPt_eq_joinCellCarrier]
    exact Set.subset_biUnion_of_mem (u := fun S ↦ joinCellCarrier (joinFactor idx vert S)) hS
  · refine Set.iUnion₂_subset fun S hS ↦ ?_
    rw [← iUnion_sdRealize_eq_joinCellCarrier idx vert S]
    refine Set.iUnion₂_subset fun σ hσ ↦ ?_
    exact Set.subset_biUnion_of_mem (u := fun σ ↦ sdRealize (cayleyPt idx vert) σ)
      (⟨S, hS, hσ⟩ : σ ∈ sdJoinComplex n K idx vert)

/-- **The good induced subcomplex triangulates the deleted join.**  The
simplices of the subdivision all of whose vertices are original Cayley points
(rather than inserted bad-edge midpoints) cover exactly the deleted join
`simplicialDeletedJoinCarrier n K m`. -/
theorem iUnion_good_sdRealize_eq_deletedJoin
    (hinj : Function.Injective fun w ↦ (idx w, vert w))
    (hcover : ∀ (i : Fin (m + 1)) (s : Finset (CoordinateSpace e)),
      IsBoundarySimplicialFace n K s → ∀ v ∈ s, ∃ w, idx w = i ∧ vert w = v) :
    (⋃ σ ∈ {σ | σ ∈ sdJoinComplex n K idx vert ∧ ∀ s ∈ σ, IsGoodSdVertex s},
        sdRealize (cayleyPt idx vert) σ) = simplicialDeletedJoinCarrier n K m := by
  rw [← iUnion_deleted_joinFactor_eq_deletedJoin idx vert hinj hcover]
  apply Set.Subset.antisymm
  · refine Set.iUnion₂_subset fun σ hσ ↦ ?_
    obtain ⟨⟨S, hS, hσS⟩, hgood⟩ := hσ
    obtain ⟨T, hTS, hTdel, rfl⟩ := (good_mem_sdFaces_iff vert S).mp ⟨hσS, hgood⟩
    rw [sdRealize_sdSimplexOf, convexHull_cayleyPt_eq_joinCellCarrier]
    exact Set.subset_biUnion_of_mem
      (u := fun T ↦ joinCellCarrier (joinFactor idx vert T)) ⟨hTdel, hS.mono hTS⟩
  · refine Set.iUnion₂_subset fun T hT ↦ ?_
    have hmem : sdSimplexOf T ∈ sdFaces vert T ∧ ∀ s ∈ sdSimplexOf T, IsGoodSdVertex s :=
      (good_mem_sdFaces_iff vert T).mpr ⟨T, Finset.Subset.refl T, hT.1, rfl⟩
    have : sdRealize (cayleyPt idx vert) (sdSimplexOf T) =
        joinCellCarrier (joinFactor idx vert T) := by
      rw [sdRealize_sdSimplexOf, convexHull_cayleyPt_eq_joinCellCarrier]
    rw [← this]
    exact Set.subset_biUnion_of_mem
      (u := fun σ ↦ sdRealize (cayleyPt idx vert) σ) ⟨⟨T, hT.2, hmem.1⟩, hmem.2⟩

end Global

section Indexing

/-- **The hypotheses above are satisfiable**: the tautological indexing of the
`m + 1` copies of `N` original vertices is injective and covers every original
vertex in every factor.  So the global statements are not vacuous. -/
theorem exists_joinVertexIndexing (m N : ℕ) (hN : 0 < N) (pt : Fin N → CoordinateSpace e)
    (hpt : Function.Injective pt) :
    ∃ (idx : Fin ((m + 1) * N) → Fin (m + 1)) (vert : Fin ((m + 1) * N) → CoordinateSpace e),
      Function.Injective (fun w ↦ (idx w, vert w)) ∧
        ∀ (i : Fin (m + 1)) (j : Fin N), ∃ w, idx w = i ∧ vert w = pt j := by
  refine ⟨fun w ↦ ⟨w.val / N, ?_⟩, fun w ↦ pt ⟨w.val % N, Nat.mod_lt _ hN⟩, ?_, ?_⟩
  · exact (Nat.div_lt_iff_lt_mul hN).mpr w.isLt
  · intro w w' h
    simp only [Prod.mk.injEq, Fin.mk.injEq] at h
    obtain ⟨hdiv, hmod⟩ := h
    have hmod' : w.val % N = w'.val % N := by
      have := hpt hmod
      simpa using congrArg Fin.val this
    have : w.val = w'.val := by
      rw [← Nat.div_add_mod w.val N, ← Nat.div_add_mod w'.val N, hdiv, hmod']
    exact Fin.ext this
  · intro i j
    have hlt : N * i.val + j.val < (m + 1) * N := by
      have h1 : N * i.val + j.val < N * i.val + N := by omega
      have h2 : N * i.val + N = N * (i.val + 1) := by ring
      have h3 : N * (i.val + 1) ≤ N * (m + 1) := Nat.mul_le_mul_left N i.isLt
      have h4 : N * (m + 1) = (m + 1) * N := Nat.mul_comm _ _
      omega
    refine ⟨⟨N * i.val + j.val, hlt⟩, ?_, ?_⟩
    · apply Fin.ext
      simp only
      rw [Nat.mul_add_div hN, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
    · exact congrArg pt (Fin.ext (by
        simp only
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]))

end Indexing

end BadEdge
end AffineTverberg
