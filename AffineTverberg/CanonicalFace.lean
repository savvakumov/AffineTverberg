import AffineTverberg.VisibleShelling
import AffineTverberg.CellShellingSupport

set_option linter.style.header false

/-!
# The canonical face lattice of a finite generating set

The recursive shelling of `VisibleShelling.lean` displays cells which are
canonical generator sets of genuine faces of `conv s`.  For the transport to
the good subcomplexes of the Cayley join it is essential to know this: the
convex hull does *not* preserve intersections of arbitrary subsets of `s`,
while it does preserve intersections of canonical faces.

This file introduces the corresponding cell poset.

* `IsExposedGens s t` — `t` consists exactly of the generators of `s` lying on
  a supporting hyperplane `g = c` of `s`.  Closure under intersection
  (`IsExposedGens.inter`), the two trivial faces, transitivity along a face of
  a face (`IsExposedGens.trans`, the finite version of "a face of a face is a
  face"), and the fact that every genuine facet index is of this form
  (`isExposedGens_facetIdx`) are proved.
* `CanonFace s` — the resulting finite meet-semilattice with bottom element,
  which is the cell poset used by the polytopal shelling.
* `canonCells` — the canonical faces belonging to a finite family of
  generator sets, together with the transfer of `cellSupport` between the two
  posets (`mem_cellSupport_canonCells`).
-/

noncomputable section

open Set

namespace AffineTverberg
namespace PolytopeFace

open CayleyJoin AffineTverberg.Simplicial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E]

/-- `t` is the set of *all* generators of `s` lying on a supporting hyperplane
`g = c`: the canonical index of an exposed face of `conv s`. -/
def IsExposedGens (s t : Finset E) : Prop :=
  ∃ (g : E →L[ℝ] ℝ) (c : ℝ), (∀ v ∈ s, g v ≤ c) ∧ ∀ v, v ∈ t ↔ (v ∈ s ∧ g v = c)

omit [DecidableEq E] in
theorem IsExposedGens.subset {s t : Finset E} (h : IsExposedGens s t) : t ⊆ s := by
  obtain ⟨g, c, -, hmem⟩ := h
  exact fun v hv ↦ ((hmem v).1 hv).1

omit [DecidableEq E] in
/-- The whole generating set is an exposed face. -/
theorem isExposedGens_self (s : Finset E) : IsExposedGens s s :=
  ⟨0, 0, fun v _ ↦ le_rfl, fun v ↦ by simp⟩

omit [DecidableEq E] in
/-- The empty face is an exposed face. -/
theorem isExposedGens_empty (s : Finset E) : IsExposedGens s ∅ :=
  ⟨0, 1, fun v _ ↦ zero_le_one, fun v ↦ by
    simp only [Finset.notMem_empty, zero_apply, false_iff, not_and]
    intro _
    norm_num⟩

/-- **Exposed faces are closed under intersection**, exposed by the sum of the
two supporting functionals. -/
theorem IsExposedGens.inter {s t₁ t₂ : Finset E} (h₁ : IsExposedGens s t₁)
    (h₂ : IsExposedGens s t₂) : IsExposedGens s (t₁ ∩ t₂) := by
  classical
  obtain ⟨g₁, c₁, hv₁, hm₁⟩ := h₁
  obtain ⟨g₂, c₂, hv₂, hm₂⟩ := h₂
  refine ⟨g₁ + g₂, c₁ + c₂, fun v hv ↦ by
    have := hv₁ v hv; have := hv₂ v hv; simp only [add_apply]; linarith, ?_⟩
  intro v
  simp only [Finset.mem_inter, hm₁, hm₂, add_apply]
  constructor
  · rintro ⟨⟨hvs, h1⟩, -, h2⟩
    exact ⟨hvs, by rw [h1, h2]⟩
  · rintro ⟨hvs, hsum⟩
    have hle₁ := hv₁ v hvs
    have hle₂ := hv₂ v hvs
    exact ⟨⟨hvs, by linarith⟩, ⟨hvs, by linarith⟩⟩

omit [DecidableEq E] in
/-- **A face of a face is a face.**  The supporting functional is a large
multiple of the first one plus the second. -/
theorem IsExposedGens.trans {s u t : Finset E} (hu : IsExposedGens s u)
    (ht : IsExposedGens u t) : IsExposedGens s t := by
  classical
  obtain ⟨g, c, hgv, hgm⟩ := hu
  obtain ⟨h, d, hhv, hhm⟩ := ht
  -- the generators of `s` outside `u` have a strict slack for `g`
  set T : Finset E := s.filter fun v ↦ v ∉ u with hT
  have hslack : ∀ v ∈ T, 0 < c - g v := by
    intro v hv
    obtain ⟨hvs, hvu⟩ := Finset.mem_filter.mp hv
    have hle := hgv v hvs
    rcases lt_or_eq_of_le hle with hlt | heq
    · linarith
    · exact absurd ((hgm v).2 ⟨hvs, heq⟩) hvu
  obtain ⟨N, hN0, hNbig⟩ : ∃ N : ℝ, 0 ≤ N ∧ ∀ v ∈ T, h v - d < N * (c - g v) := by
    rcases Finset.eq_empty_or_nonempty T with hTe | hTne
    · exact ⟨0, le_rfl, fun v hv ↦ absurd hv (by rw [hTe]; exact Finset.notMem_empty v)⟩
    · obtain ⟨v₀, -, hmax⟩ :=
        Finset.exists_max_image T (fun v ↦ (h v - d) / (c - g v)) hTne
      refine ⟨max 0 ((h v₀ - d) / (c - g v₀) + 1), le_max_left _ _, fun v hv ↦ ?_⟩
      have hpos := hslack v hv
      have hle : (h v - d) / (c - g v) ≤ (h v₀ - d) / (c - g v₀) := hmax v hv
      have hlt : (h v - d) / (c - g v) < max 0 ((h v₀ - d) / (c - g v₀) + 1) :=
        lt_of_lt_of_le (by linarith) (le_max_right _ _)
      exact (div_lt_iff₀ hpos).mp hlt
  refine ⟨N • g + h, N * c + d, ?_, ?_⟩
  · intro v hvs
    simp only [add_apply, smul_apply, smul_eq_mul]
    by_cases hvu : v ∈ u
    · have hgc : g v = c := ((hgm v).1 hvu).2
      have := hhv v hvu
      rw [hgc]
      linarith
    · have hvT : v ∈ T := Finset.mem_filter.mpr ⟨hvs, hvu⟩
      have := hNbig v hvT
      nlinarith
  · intro v
    simp only [add_apply, smul_apply, smul_eq_mul]
    constructor
    · intro hvt
      obtain ⟨hvu, hhd⟩ := (hhm v).1 hvt
      have hgc : g v = c := ((hgm v).1 hvu).2
      exact ⟨((hgm v).1 hvu).1, by rw [hgc, hhd]⟩
    · rintro ⟨hvs, heq⟩
      by_cases hvu : v ∈ u
      · have hgc : g v = c := ((hgm v).1 hvu).2
        rw [hgc] at heq
        have hhd : h v = d := by linarith
        exact (hhm v).2 ⟨hvu, hhd⟩
      · have hvT : v ∈ T := Finset.mem_filter.mpr ⟨hvs, hvu⟩
        have := hNbig v hvT
        nlinarith

omit [DecidableEq E] in
/-- **Every genuine facet index is a canonical exposed generator set.** -/
theorem isExposedGens_facetIdx {s : Finset E} (j : FacetIdx s) :
    IsExposedGens s j.1.1 := by
  refine ⟨facetForm j, facetRhs j, fun v hv ↦ facetForm_le_facetRhs j
    (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)), fun v ↦ ?_⟩
  rw [facetIdx_index_eq_contactGens j, mem_contactGens]

/-! ### The canonical face lattice -/

/-- The finite meet-semilattice of canonical exposed generator sets. -/
def CanonFace (s : Finset E) : Type _ := {t : Finset E // IsExposedGens s t}

namespace CanonFace

variable {s : Finset E}

/-- The canonical face of `s` determined by a canonical generator set.  Using
this constructor keeps the elaborated type synthetically equal to
`CanonFace s`, so that the lattice instances below are found. -/
def mk' (t : Finset E) (h : IsExposedGens s t) : CanonFace s := ⟨t, h⟩

omit [DecidableEq E] in
@[simp] theorem coe_mk' (t : Finset E) (h : IsExposedGens s t) :
    (mk' t h).1 = t := rfl

instance : DecidableEq (CanonFace s) := fun a b ↦
  decidable_of_iff (a.1 = b.1) Subtype.ext_iff.symm

instance : SemilatticeInf (CanonFace s) :=
  Subtype.semilatticeInf fun _ _ hx hy ↦ hx.inter hy

instance : OrderBot (CanonFace s) where
  bot := ⟨∅, isExposedGens_empty s⟩
  bot_le := fun c ↦ Finset.empty_subset c.1

@[simp] theorem coe_bot : (⊥ : CanonFace s).1 = ∅ := rfl

@[simp] theorem coe_inf (c d : CanonFace s) : (c ⊓ d).1 = c.1 ∩ d.1 := rfl

theorem le_iff {c d : CanonFace s} : c ≤ d ↔ c.1 ⊆ d.1 := Iff.rfl

theorem ne_bot_iff {c : CanonFace s} : c ≠ ⊥ ↔ c.1.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  constructor
  · intro hc h
    exact hc (Subtype.ext h)
  · intro hc h
    exact hc (by rw [h]; rfl)

end CanonFace

instance instDecidablePredIsExposedGens (s : Finset E) :
    DecidablePred (IsExposedGens s) := Classical.decPred _

/-- The canonical faces belonging to a finite family of generator sets. -/
def canonCells (s : Finset E) (X : Finset (Finset E)) : Finset (CanonFace s) :=
  X.subtype (IsExposedGens s)

omit [DecidableEq E] in
@[simp] theorem mem_canonCells {s : Finset E} {X : Finset (Finset E)} {t : CanonFace s} :
    t ∈ canonCells s X ↔ t.1 ∈ X := Finset.mem_subtype

omit [DecidableEq E] in
@[simp] theorem canonCells_empty {s : Finset E} :
    canonCells s (∅ : Finset (Finset E)) = ∅ := by
  ext t
  simp only [mem_canonCells, Finset.notMem_empty]

theorem canonCells_insert {s : Finset E} {X : Finset (Finset E)} {c : Finset E}
    (hc : IsExposedGens s c) :
    canonCells s (insert c X) = insert (CanonFace.mk' c hc) (canonCells s X) := by
  ext t
  constructor
  · intro ht
    rcases Finset.mem_insert.mp (mem_canonCells.mp ht) with h | h
    · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext h))
    · exact Finset.mem_insert.mpr (Or.inr (mem_canonCells.mpr h))
  · intro ht
    rcases Finset.mem_insert.mp ht with h | h
    · exact mem_canonCells.mpr (by rw [h]; exact Finset.mem_insert_self c X)
    · exact mem_canonCells.mpr (Finset.mem_insert_of_mem (mem_canonCells.mp h))

/-- **Transfer of cell supports between the two posets.**  For a family of
canonical faces, the support inside the canonical face lattice is the
restriction of the support inside the poset of all finite subsets. -/
theorem mem_cellSupport_canonCells {s : Finset E} {X : Finset (Finset E)}
    (hX : ∀ t ∈ X, IsExposedGens s t) {e : CanonFace s} :
    e ∈ cellSupport (canonCells s X) ↔ e.1 ∈ cellSupport X := by
  constructor
  · rintro ⟨hne, c, hc, hec⟩
    refine ⟨fun h ↦ hne (Subtype.ext h), c.1, mem_canonCells.mp hc, hec⟩
  · rintro ⟨hne, c, hc, hec⟩
    exact ⟨fun h ↦ hne (congrArg Subtype.val h), ⟨c, hX c hc⟩,
      mem_canonCells.mpr hc, hec⟩

/-- Equal supports in the ambient poset give equal supports in the canonical
face lattice. -/
theorem cellSupport_canonCells_congr {s : Finset E} {X Y : Finset (Finset E)}
    (hX : ∀ t ∈ X, IsExposedGens s t) (hY : ∀ t ∈ Y, IsExposedGens s t)
    (h : cellSupport X = cellSupport Y) :
    cellSupport (canonCells s X) = cellSupport (canonCells s Y) := by
  ext e
  rw [mem_cellSupport_canonCells hX, mem_cellSupport_canonCells hY, h]

end PolytopeFace
end AffineTverberg
