import AffineTverberg.MayerVietoris

set_option linter.style.header false

/-!
# Acyclic gluing along a recursive cell shelling

In the augmented chain grading, a chain degree `k` represents geometric
degree `k - 1`.  Thus the paper's bound through geometric degree `n - 1`
is `IsReducedAcyclicUpTo ... n`.  On an overlap of two `n`-dimensional
pieces, only the bound through chain degree `n - 1` is required.

`CellShelling` records the incidence data used in the proof of the paper's
acyclic-gluing lemma: a single cell, or the attachment of another cell along
a recursively shelled overlap of dimension one less.  Its hypotheses refer
only to the ordered cell family and dimensions; there are no homological
hypotheses in this certificate.  The theorem proves acyclicity for every
intersection-preserving assignment of complexes satisfying the local bounds.

The geometric theorem that a line shelling supplies this certificate for
the top-face subdivision is a separate input still to be formalized.
-/

noncomputable section

namespace AffineTverberg
namespace Simplicial

section DegreeShift

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder V] [Fintype V]

/-- Sharp bounded-degree Mayer--Vietoris: the overlap is needed only in
strictly lower chain degrees.  This also handles the augmentation degree. -/
theorem isReducedAcyclicUpTo_union_of_lowerIntersection
    {K L : Finset (Finset V)} (hK : FaceClosed K) (hL : FaceClosed L)
    {N : ℕ} (hKa : IsReducedAcyclicUpTo 𝕜 K N)
    (hLa : IsReducedAcyclicUpTo 𝕜 L N)
    (hIa : ∀ k < N, IsReducedAcyclicAt 𝕜 (K ∩ L) k) :
    IsReducedAcyclicUpTo 𝕜 (K ∪ L) N := by
  intro k hk
  cases k with
  | zero =>
      exact isReducedAcyclicAt_union_zero (hKa 0 (Nat.zero_le N))
        (hLa 0 (Nat.zero_le N))
  | succ k =>
      exact isReducedAcyclicAt_union_succ hK hL
        (hKa (k + 1) hk) (hLa (k + 1) hk) (hIa k (by omega))

/-- The sharp degree shift propagated through a finite ordered union. -/
theorem isReducedAcyclicUpTo_partialUnion_of_lowerIntersection
    {F : ℕ → Finset (Finset V)} {N m : ℕ}
    (hFC : ∀ i < m, FaceClosed (F i))
    (hFa : ∀ i < m, IsReducedAcyclicUpTo 𝕜 (F i) N)
    (hIa : ∀ i < m, ∀ k < N,
      IsReducedAcyclicAt 𝕜 (partialUnion F i ∩ F i) k) :
    IsReducedAcyclicUpTo 𝕜 (partialUnion F m) N := by
  induction m with
  | zero =>
      rw [partialUnion_zero]
      exact isReducedAcyclicUpTo_of_isReducedAcyclic isReducedAcyclic_empty N
  | succ m ih =>
      have hprev := ih (fun i hi ↦ hFC i (by omega))
        (fun i hi ↦ hFa i (by omega)) (fun i hi ↦ hIa i (by omega))
      rw [partialUnion_succ]
      exact isReducedAcyclicUpTo_union_of_lowerIntersection
        (faceClosed_partialUnion fun i hi ↦ hFC i (by omega))
        (hFC m (by omega)) hprev (hFa m (by omega)) (hIa m (by omega))

end DegreeShift

section CellCombinatorics

variable {C : Type*} [SemilatticeInf C] [OrderBot C] [DecidableEq C]

/-- The nonempty cells lying below one of the displayed cells.  Equality
of these supports expresses equality of two cell subcomplexes. -/
def cellSupport (S : Finset C) : Set C :=
  {e | e ≠ ⊥ ∧ ∃ c ∈ S, e ≤ c}

/-- The algebraic incidence data of a recursive shelling of a cell ball.
The overlap has a shelling in one lower dimension and its support is exactly
the family of nonempty faces lying below intersections with previous cells.
No homology or acyclicity occurs in this definition. -/
inductive CellShelling (dim : C → ℕ) : ℕ → Finset C → Prop
  | single (c : C) (hc : c ≠ ⊥) : CellShelling dim (dim c) {c}
  | attach {n : ℕ} {S T : Finset C} (c : C)
      (hS : CellShelling dim (n + 1) S)
      (hc : c ≠ ⊥) (hdim : dim c = n + 1) (hnew : c ∉ S)
      (hT : CellShelling dim n T)
      (hoverlap : cellSupport (S.image fun d ↦ c ⊓ d) = cellSupport T) :
      CellShelling dim (n + 1) (insert c S)

/-- A recursively shelled ball has at least one maximal cell. -/
theorem CellShelling.nonempty {dim : C → ℕ} {n : ℕ} {S : Finset C}
    (h : CellShelling dim n S) : S.Nonempty := by
  cases h with
  | single c hc => exact Finset.singleton_nonempty c
  | attach c hS hc hdim hnew hT hoverlap => exact Finset.insert_nonempty c _

/-- Every displayed maximal cell is nonempty and has the ambient dimension. -/
theorem CellShelling.pure {dim : C → ℕ} {n : ℕ} {S : Finset C}
    (h : CellShelling dim n S) : ∀ c ∈ S, c ≠ ⊥ ∧ dim c = n := by
  induction h with
  | single c hc =>
      intro d hd
      have : d = c := Finset.mem_singleton.mp hd
      subst d
      exact ⟨hc, rfl⟩
  | attach c hS hc hdim hnew hT hoverlap ihS ihT =>
      intro d hd
      rcases Finset.mem_insert.mp hd with rfl | hd
      · exact ⟨hc, hdim⟩
      · exact ihS d hd

end CellCombinatorics

section Assignment

variable {C V : Type*} [SemilatticeInf C] [OrderBot C] [DecidableEq C]
  [DecidableEq V]

/-- Union of the assigned subcomplexes over a finite cell family. -/
def assignedUnion (A : C → Finset (Finset V)) (S : Finset C) :
    Finset (Finset V) :=
  S.biUnion A

omit [SemilatticeInf C] [OrderBot C] [DecidableEq C] in
@[simp]
theorem mem_assignedUnion {A : C → Finset (Finset V)} {S : Finset C}
    {s : Finset V} : s ∈ assignedUnion A S ↔ ∃ c ∈ S, s ∈ A c :=
  Finset.mem_biUnion

omit [SemilatticeInf C] [OrderBot C] [DecidableEq C] in
@[simp]
theorem assignedUnion_singleton (A : C → Finset (Finset V)) (c : C) :
    assignedUnion A {c} = A c := by
  ext s
  simp

omit [SemilatticeInf C] [OrderBot C] in
theorem assignedUnion_insert (A : C → Finset (Finset V)) (S : Finset C)
    (c : C) : assignedUnion A (insert c S) = assignedUnion A S ∪ A c := by
  ext s
  simp only [mem_assignedUnion, Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro ⟨d, rfl | hd, hs⟩
    · exact Or.inr hs
    · exact Or.inl ⟨d, hd, hs⟩
  · rintro (⟨d, hd, hs⟩ | hs)
    · exact ⟨d, Or.inr hd, hs⟩
    · exact ⟨c, Or.inl rfl, hs⟩

omit [OrderBot C] [DecidableEq C] in
/-- The intersection identity forces the assignment to preserve inclusions. -/
theorem assignment_mono_of_inter
    (A : C → Finset (Finset V))
    (hinter : ∀ c d, A (c ⊓ d) = A c ∩ A d)
    {c d : C} (hcd : c ≤ d) : A c ⊆ A d := by
  have heq : A c = A c ∩ A d := by
    simpa only [inf_eq_left.mpr hcd] using hinter c d
  intro s hs
  rw [heq] at hs
  exact (Finset.mem_inter.mp hs).2

omit [DecidableEq C] in
/-- Every augmented assigned complex contains the formal empty simplex.
In particular, the empty *geometric* complex is represented by `{∅}`. -/
theorem empty_mem_assignment
    (A : C → Finset (Finset V)) (hbot : A ⊥ = {∅})
    (hinter : ∀ c d, A (c ⊓ d) = A c ∩ A d) (c : C) :
    ∅ ∈ A c := by
  apply assignment_mono_of_inter A hinter (bot_le : (⊥ : C) ≤ c)
  rw [hbot]
  exact Finset.mem_singleton_self ∅

omit [DecidableEq C] in
/-- Equal cell supports give equal assigned unions.  Both indexing families
are nonempty so their augmented unions retain the formal empty simplex.
The empty geometric cell is represented by `{∅}`, not by the void family. -/
theorem assignedUnion_eq_of_cellSupport_eq
    (A : C → Finset (Finset V)) (hbot : A ⊥ = {∅})
    (hinter : ∀ c d, A (c ⊓ d) = A c ∩ A d)
    {S T : Finset C} (hst : cellSupport S = cellSupport T)
    (hS : S.Nonempty) (hT : T.Nonempty) :
    assignedUnion A S = assignedUnion A T := by
  have hsub {U W : Finset C} (hUW : cellSupport U ⊆ cellSupport W)
      (hW : W.Nonempty) :
      assignedUnion A U ⊆ assignedUnion A W := by
    intro s hs
    by_cases hs0 : s = ∅
    · obtain ⟨d, hd⟩ := hW
      subst s
      exact mem_assignedUnion.mpr ⟨d, hd, empty_mem_assignment A hbot hinter d⟩
    obtain ⟨c, hc, hsc⟩ := mem_assignedUnion.mp hs
    have hcne : c ≠ ⊥ := by
      intro heq
      rw [heq, hbot] at hsc
      exact hs0 (Finset.mem_singleton.mp hsc)
    have hcU : c ∈ cellSupport U := ⟨hcne, c, hc, le_rfl⟩
    obtain ⟨_, d, hd, hcd⟩ := hUW hcU
    exact mem_assignedUnion.mpr
      ⟨d, hd, assignment_mono_of_inter A hinter hcd hsc⟩
  exact Finset.Subset.antisymm (hsub hst.subset hT) (hsub hst.symm.subset hS)

omit [OrderBot C] in
/-- Distributing the overlap of an assigned cell with the previous union
produces the assigned union of the pairwise cell intersections. -/
theorem assignedUnion_inter_cell
    (A : C → Finset (Finset V))
    (hinter : ∀ c d, A (c ⊓ d) = A c ∩ A d)
    (S : Finset C) (c : C) :
    assignedUnion A S ∩ A c = assignedUnion A (S.image fun d ↦ c ⊓ d) := by
  ext s
  simp only [Finset.mem_inter, mem_assignedUnion, Finset.mem_image]
  constructor
  · rintro ⟨⟨d, hd, hsd⟩, hsc⟩
    refine ⟨c ⊓ d, ⟨d, hd, rfl⟩, ?_⟩
    rw [hinter]
    exact Finset.mem_inter.mpr ⟨hsc, hsd⟩
  · rintro ⟨_, ⟨d, hd, rfl⟩, hs⟩
    rw [hinter] at hs
    exact ⟨⟨d, hd, (Finset.mem_inter.mp hs).2⟩, (Finset.mem_inter.mp hs).1⟩

omit [SemilatticeInf C] [OrderBot C] [DecidableEq C] in
/-- A union of assigned subcomplexes is again a subcomplex. -/
theorem faceClosed_assignedUnion (A : C → Finset (Finset V))
    (hclosed : ∀ c, FaceClosed (A c)) (S : Finset C) :
    FaceClosed (assignedUnion A S) := by
  intro s hs t hts
  obtain ⟨c, hc, hsc⟩ := mem_assignedUnion.mp hs
  exact mem_assignedUnion.mpr ⟨c, hc, hclosed c s hsc t hts⟩

end Assignment

section AcyclicGluing

variable {𝕜 C V : Type*} [Field 𝕜] [SemilatticeInf C] [OrderBot C]
  [DecidableEq C] [LinearOrder V] [Fintype V]

/-- **Acyclic gluing over a recursive cell shelling.** Local reduced
acyclicity through chain degree `dim E` implies the same bound through `n`
on the assigned union over an `n`-dimensional shelling.  In geometric
degrees this is exactly the paper's bound through `n - 1`. -/
theorem isReducedAcyclicUpTo_assignedUnion_of_cellShelling
    (dim : C → ℕ) (A : C → Finset (Finset V))
    (hbot : A ⊥ = {∅})
    (hinter : ∀ c d, A (c ⊓ d) = A c ∩ A d)
    (hclosed : ∀ c, FaceClosed (A c))
    (hlocal : ∀ c, c ≠ ⊥ → IsReducedAcyclicUpTo 𝕜 (A c) (dim c))
    {n : ℕ} {S : Finset C} (hshell : CellShelling dim n S) :
    IsReducedAcyclicUpTo 𝕜 (assignedUnion A S) n := by
  induction hshell with
  | single c hc =>
      rw [assignedUnion_singleton]
      exact hlocal c hc
  | @attach n S T c hS hc hdim hnew hT hoverlap ihS ihT =>
      rw [assignedUnion_insert]
      have hcell : IsReducedAcyclicUpTo 𝕜 (A c) (n + 1) := by
        rw [← hdim]
        exact hlocal c hc
      have hoverlapA : assignedUnion A S ∩ A c = assignedUnion A T := by
        rw [assignedUnion_inter_cell A hinter]
        exact assignedUnion_eq_of_cellSupport_eq A hbot hinter hoverlap
          (hS.nonempty.image _) hT.nonempty
      apply isReducedAcyclicUpTo_union_of_lowerIntersection
        (faceClosed_assignedUnion A hclosed S) (hclosed c) ihS hcell
      intro k hk
      rw [hoverlapA]
      exact ihT k (by omega)

/-- The same gluing theorem expressed as vanishing of actual reduced
homology modules. -/
theorem homology_assignedUnion_subsingleton_of_cellShelling
    (dim : C → ℕ) (A : C → Finset (Finset V))
    (hbot : A ⊥ = {∅})
    (hinter : ∀ c d, A (c ⊓ d) = A c ∩ A d)
    (hclosed : ∀ c, FaceClosed (A c))
    (hlocal : ∀ c, c ≠ ⊥ → IsReducedAcyclicUpTo 𝕜 (A c) (dim c))
    {n : ℕ} {S : Finset C} (hshell : CellShelling dim n S)
    (k : ℕ) (hk : k ≤ n) :
    Subsingleton (homology 𝕜 (assignedUnion A S) k) := by
  rw [homology_subsingleton_iff]
  exact isReducedAcyclicUpTo_assignedUnion_of_cellShelling
    dim A hbot hinter hclosed hlocal hshell k hk

end AcyclicGluing

section ConcreteCheck

/-- A concrete recursive shelling: two edges attached along their shared
vertex.  This checks that the overlap certificate is realizable. -/
theorem twoEdgeCellShelling :
    CellShelling (fun c : Finset (Fin 3) ↦ c.card - 1) 1
      {{1, 2}, {0, 1}} := by
  refine CellShelling.attach (n := 0) (S := {{0, 1}}) (T := {{1}})
    {1, 2} ?_ (by decide) (by decide) (by decide) ?_ ?_
  · exact CellShelling.single (dim := fun c : Finset (Fin 3) ↦ c.card - 1)
      ({0, 1} : Finset (Fin 3)) (by decide)
  · exact CellShelling.single (dim := fun c : Finset (Fin 3) ↦ c.card - 1)
      ({1} : Finset (Fin 3)) (by decide)
  · congr 1

/-- Applying the gluing theorem to the usual simplex assignment on those
two edges, with the empty cell sent to its augmented empty complex. -/
theorem twoEdge_assignedUnion_acyclicUpTo_one :
    IsReducedAcyclicUpTo ℚ
      (assignedUnion (fun c : Finset (Fin 3) ↦ c.powerset) {{1, 2}, {0, 1}}) 1 := by
  apply isReducedAcyclicUpTo_assignedUnion_of_cellShelling
    (fun c : Finset (Fin 3) ↦ c.card - 1) (fun c ↦ c.powerset)
    (by decide) ?_ (fun c ↦ faceClosed_powerset c) ?_ twoEdgeCellShelling
  · intro c d
    ext s
    simp [Finset.subset_inter_iff]
  · intro c hc
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hc
    exact isReducedAcyclicUpTo_of_isReducedAcyclic
      (isReducedAcyclic_powerset ha) _

end ConcreteCheck

end Simplicial
end AffineTverberg
