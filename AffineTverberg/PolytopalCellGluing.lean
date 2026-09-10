import AffineTverberg.PolytopalLocalAcyclicity
import AffineTverberg.ShellableGluing
import AffineTverberg.SimplicialCohomology

set_option linter.style.header false

/-!
# The polytopal good subcomplexes as an assignment on the face lattice

The acyclic gluing theorem `isReducedAcyclicUpTo_assignedUnion_of_cellShelling`
consumes an assignment `A` of subcomplexes to the cells of a poset satisfying

* `A ⊥ = {∅}`,
* `A (c ⊓ d) = A c ∩ A d`,
* `FaceClosed (A c)`,
* local reduced acyclicity of `A c` up to `dim c`,

together with a recursive shelling certificate for the displayed top cells.

This file proves **all four hypotheses** for the polytopal bad-vertex
triangulation, with the cells the actual faces of the Cayley join, the
assignment the good induced subcomplex, and `dim` the sharp affine dimension
`projDim`.  The key new combinatorial input is `sdQ_inter`: the triangulation
of an intersection of two faces is the intersection of their triangulations,
which is the exact-restriction statement `sdQ_filter_mem` combined with the
fact that the vertices of a simplex of `sdQ S` are contained in `S`.

Consequently
`isReducedAcyclicUpTo_goodUnion_of_cellShelling` proves reduced acyclicity of
the union of the good subcomplexes over any shelled family of faces, and
`geometricCarrier_goodUnion` identifies the carrier of that union with the
union of the deleted joins inside those faces.

The remaining input is the *geometric* statement that a line shelling of a
polytope supplies a `CellShelling` certificate; it is an explicit hypothesis of
the theorems below and is not assumed anywhere else.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace Simplicial

section CellShellingUnion

variable {𝕜 C V : Type*} [Field 𝕜] [SemilatticeInf C] [OrderBot C] [DecidableEq C]
  [LinearOrder V] [Fintype V]

/-- The acyclic gluing theorem in a form that is independent of the decidable
equality used to form the union: any finite family `U` whose members are
exactly the simplices of the assigned cells is reduced acyclic. -/
theorem isReducedAcyclicUpTo_union_of_cellShelling
    (dim : C → ℕ) (A : C → Finset (Finset V))
    (hbot : A ⊥ = {∅})
    (hinter : ∀ c d s, s ∈ A (c ⊓ d) ↔ s ∈ A c ∧ s ∈ A d)
    (hclosed : ∀ c, FaceClosed (A c))
    (hlocal : ∀ c, c ≠ ⊥ → IsReducedAcyclicUpTo 𝕜 (A c) (dim c))
    {N : ℕ} {S : Finset C} (hshell : CellShelling dim N S)
    (U : Finset (Finset V)) (hU : ∀ s, s ∈ U ↔ ∃ c ∈ S, s ∈ A c) :
    IsReducedAcyclicUpTo 𝕜 U N := by
  have hinter' : ∀ c d, A (c ⊓ d) = A c ∩ A d := fun c d ↦ by
    ext s
    rw [Finset.mem_inter]
    exact hinter c d s
  have hUeq : U = assignedUnion A S := by
    ext s
    rw [hU, mem_assignedUnion]
  rw [hUeq]
  exact isReducedAcyclicUpTo_assignedUnion_of_cellShelling dim A hbot hinter' hclosed
    hlocal hshell

end CellShellingUnion

end Simplicial

namespace BadVertex

open CayleyJoin PolytopeFace BadEdge _root_.AffineTverberg.Simplicial

variable {n : ℕ} {P : FullDimensionalPolytope n} {m : ℕ}

/-! ### The triangulation of an intersection of faces -/

/-- The subdivision of the empty face is the single empty simplex. -/
theorem sdQ_empty : sdQ P m (∅ : Finset (JoinVertex P m)) = {∅} := by
  rw [sdQ, sdPoset_eq]
  have hfil : ((faceFamily P m).filter fun G ↦ G ⊆ (∅ : Finset (JoinVertex P m)) ∧
      ¬ apexSet (origIndex P m) ∅ ⊆ G) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr ?_
    rintro G - ⟨hG, hna⟩
    rw [Finset.subset_empty] at hG
    subst hG
    exact hna (apexSet_subset _ _)
  rw [hfil]
  simp

/-- **The triangulations restrict exactly**: the bad-vertex triangulation of the
intersection of two faces of the Cayley join is the intersection of their
triangulations. -/
theorem sdQ_inter {S T : Finset (JoinVertex P m)} (hS : S ∈ faceFamily P m)
    (hT : T ∈ faceFamily P m) :
    sdQ P m (S ∩ T) = sdQ P m S ∩ sdQ P m T := by
  obtain ⟨hST, -⟩ := sdCarrier_inter hS hT
  apply Finset.Subset.antisymm
  · intro σ hσ
    exact Finset.mem_inter.mpr ⟨sdQ_mono P m hST Finset.inter_subset_left hσ,
      sdQ_mono P m hST Finset.inter_subset_right hσ⟩
  · intro σ hσ
    obtain ⟨hσS, hσT⟩ := Finset.mem_inter.mp hσ
    have hfil : σ.filter (fun b ↦ b ⊆ S ∩ T) = σ :=
      Finset.filter_true_of_mem fun b hb ↦ Finset.subset_inter
        (sdPoset_vertex_subset hσS hb) (sdPoset_vertex_subset hσT hb)
    have h := sdQ_filter_mem hST Finset.inter_subset_left hσS
    rwa [hfil] at h

/-! ### The face lattice of the Cayley join as a cell poset -/

/-- A cell: an actual face of the Cayley join, recorded by its vertex set. -/
def FaceCell (P : FullDimensionalPolytope n) (m : ℕ) : Type :=
  {S : Finset (JoinVertex P m) // S ∈ faceFamily P m}

instance : DecidableEq (FaceCell P m) := fun a b ↦ Subtype.instDecidableEq a b

instance : SemilatticeInf (FaceCell P m) :=
  Subtype.semilatticeInf fun _ _ hx hy ↦ (sdCarrier_inter hx hy).1

instance : OrderBot (FaceCell P m) where
  bot := ⟨∅, empty_mem_faceFamily P m⟩
  bot_le := fun c ↦ Finset.empty_subset c.1

@[simp] theorem FaceCell.coe_bot : (⊥ : FaceCell P m).1 = ∅ := rfl

@[simp] theorem FaceCell.coe_inf (c d : FaceCell P m) : (c ⊓ d).1 = c.1 ∩ d.1 := rfl

theorem FaceCell.nonempty_of_ne_bot {c : FaceCell P m} (hc : c ≠ ⊥) : c.1.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  exact hc (Subtype.ext h)

/-- The dimension of a cell used by the shelling induction: the sharp affine
dimension of the projected union of the factors of the face. -/
def dimCell (P : FullDimensionalPolytope n) (m : ℕ) (c : FaceCell P m) : ℕ :=
  projDim P m c.1

/-- The subcomplex assigned to a cell: the good induced subcomplex of the
bad-vertex triangulation of that face. -/
def goodAssign (P : FullDimensionalPolytope n) (m : ℕ) (c : FaceCell P m) :
    Finset (Finset (Finset (JoinVertex P m))) :=
  inducedFaces (sdQ P m c.1) (goodJoinVertices P m)

theorem mem_goodAssign {c : FaceCell P m} {σ : Finset (Finset (JoinVertex P m))} :
    σ ∈ goodAssign P m c ↔ σ ∈ sdQ P m c.1 ∧ ∀ a ∈ σ, a.card = 1 := by
  rw [goodAssign, mem_inducedFaces]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a ha ↦ (Finset.mem_filter.mp (h2 ha)).2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a ha ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2 a ha⟩⟩

/-- The good induced subcomplex is the family of good simplices. -/
theorem inducedFaces_eq_goodSimplices (S : Finset (JoinVertex P m)) :
    inducedFaces (sdQ P m S) (goodJoinVertices P m) = goodSimplices P m S := by
  classical
  ext σ
  rw [mem_inducedFaces, goodSimplices, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a ha ↦ (Finset.mem_filter.mp (h2 ha)).2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a ha ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2 a ha⟩⟩

/-! ### The four hypotheses of the acyclic gluing theorem -/

theorem goodAssign_bot : goodAssign P m ⊥ = {∅} := by
  rw [goodAssign, FaceCell.coe_bot, sdQ_empty, inducedFaces]
  simp

theorem goodAssign_inf (c d : FaceCell P m) (σ : Finset (Finset (JoinVertex P m))) :
    σ ∈ goodAssign P m (c ⊓ d) ↔ σ ∈ goodAssign P m c ∧ σ ∈ goodAssign P m d := by
  simp only [mem_goodAssign, FaceCell.coe_inf, sdQ_inter c.2 d.2, Finset.mem_inter]
  tauto

theorem faceClosed_goodAssign (c : FaceCell P m) : FaceClosed (goodAssign P m c) :=
  faceClosed_inducedFaces (faceClosed_sdQ c.1) _

/-- The union of the good subcomplexes over a family of faces. -/
def goodUnion (S : Finset (FaceCell P m)) :
    Finset (Finset (Finset (JoinVertex P m))) :=
  S.biUnion (goodAssign P m)

theorem mem_goodUnion {S : Finset (FaceCell P m)}
    {σ : Finset (Finset (JoinVertex P m))} :
    σ ∈ goodUnion S ↔ ∃ c ∈ S, σ ∈ goodAssign P m c := by
  rw [goodUnion, Finset.mem_biUnion]

section Order

variable [LinearOrder (Finset (JoinVertex P m))]

theorem local_acyclicity_goodAssign (c : FaceCell P m) (hc : c ≠ ⊥) :
    IsReducedAcyclicUpTo ℝ (goodAssign P m c) (dimCell P m c) :=
  local_simplicial_acyclicity_sdQ c.2 (FaceCell.nonempty_of_ne_bot hc)

/-- **Acyclic gluing for the polytopal good subcomplexes.**  Given a recursive
shelling certificate for a family of faces of the Cayley join, the union of the
good subcomplexes of those faces is reduced acyclic up to the shelling
dimension.  The shelling certificate is a hypothesis: no geometric shelling
theorem is assumed here. -/
theorem isReducedAcyclicUpTo_goodUnion_of_cellShelling {N : ℕ} {S : Finset (FaceCell P m)}
    (hshell : CellShelling (dimCell P m) N S) :
    IsReducedAcyclicUpTo ℝ (goodUnion S) N :=
  isReducedAcyclicUpTo_union_of_cellShelling (dimCell P m) (goodAssign P m)
    goodAssign_bot goodAssign_inf faceClosed_goodAssign local_acyclicity_goodAssign
    hshell _ fun _ ↦ mem_goodUnion

omit [LinearOrder (Finset (JoinVertex P m))] in
theorem faceClosed_goodUnion (S : Finset (FaceCell P m)) : FaceClosed (goodUnion S) :=
  faceClosed_assignedUnion (goodAssign P m) faceClosed_goodAssign S

/-- The cohomological form: the reduced simplicial cohomology of the glued good
complex vanishes up to the shelling dimension. -/
theorem cohomology_goodUnion_subsingleton_of_cellShelling {N : ℕ} {S : Finset (FaceCell P m)}
    (hshell : CellShelling (dimCell P m) N S) (k : ℕ) (hk : k ≤ N) :
    Subsingleton (cohomology ℝ (faceClosed_goodUnion S) k) :=
  cohomology_subsingleton_of_isReducedAcyclicUpTo (faceClosed_goodUnion S)
    (isReducedAcyclicUpTo_goodUnion_of_cellShelling hshell) k hk

/-- A one-cell shelling; this shows the shelling hypothesis above is
satisfiable and recovers the local statement. -/
theorem isReducedAcyclicUpTo_goodUnion_singleton (c : FaceCell P m) (hc : c ≠ ⊥) :
    IsReducedAcyclicUpTo ℝ (goodUnion {c}) (dimCell P m c) :=
  isReducedAcyclicUpTo_goodUnion_of_cellShelling
    (CellShelling.single (dim := dimCell P m) c hc)

end Order

/-- The carrier of the glued complex is the union of the deleted joins inside
the given faces. -/
theorem geometricCarrier_goodUnion (S : Finset (FaceCell P m)) :
    geometricCarrier (goodUnion S) (sdPoint P m) = ⋃ c ∈ S, goodRealization P m c.1 := by
  ext x
  simp only [geometricCarrier, goodRealization, simplexCarrier, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨σ, hσ, hx⟩
    obtain ⟨c, hc, hσc⟩ := mem_goodUnion.mp hσ
    refine ⟨c, hc, σ, ?_, hx⟩
    rwa [goodAssign, inducedFaces_eq_goodSimplices] at hσc
  · rintro ⟨c, hc, σ, hσ, hx⟩
    refine ⟨σ, mem_goodUnion.mpr ⟨c, hc, ?_⟩, hx⟩
    rwa [goodAssign, inducedFaces_eq_goodSimplices]

/-- The carrier of the good subcomplex of a face is its good realization. -/
theorem geometricCarrier_goodAssign (S : Finset (JoinVertex P m)) :
    geometricCarrier (inducedFaces (sdQ P m S) (goodJoinVertices P m)) (sdPoint P m) =
      goodRealization P m S := by
  rw [inducedFaces_eq_goodSimplices]
  rfl

/-- **Actual singular acyclicity of the polytopal deleted join through degree
`n - 1`.**  This combines the local acyclicity of the good subcomplex of the
whole Cayley join with its identification with the polytopal deleted join. -/
theorem singular_acyclicity_polytopalDeletedJoin :
    (polytopalDeletedJoinCarrier P m).Nonempty ∧
      (1 ≤ n → CategoryTheory.IsIso (realSingularAugmentation
        (TopCat.of ↑(polytopalDeletedJoinCarrier P m)))) ∧
      ∀ k, k ≠ 0 → k + 1 ≤ n →
        CategoryTheory.Limits.IsZero ((realSingularHomology k).obj
          (TopCat.of ↑(polytopalDeletedJoinCarrier P m))) := by
  let _ : LinearOrder (Finset (JoinVertex P m)) := joinVertexSetOrder P m
  have hne : (topFace P m).Nonempty := by
    obtain ⟨v, hv⟩ := P.actualVertices_nonempty
    obtain ⟨k, -⟩ := exists_vtx P hv
    exact ⟨((0, k) : JoinVertex P m), Finset.mem_univ _⟩
  have h := local_singular_acyclicity_sdQ (topFace_mem_faceFamily P m) hne
  rw [projDim_topFace, geometricCarrier_goodAssign, goodRealization_topFace] at h
  exact h

end BadVertex
end AffineTverberg
