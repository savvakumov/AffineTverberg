import AffineTverberg.ShellableGluing
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option linter.style.header false

/-!
# Reduced simplicial cohomology over a field

This is the algebraic homology-to-cohomology step used twice in the paper.
The cochain groups are the actual linear duals of the augmented chain
groups of `SimplicialHomology`; their differentials are the duals of the
oriented boundary maps.  In degree zero (geometric degree minus one), the
outgoing chain differential is zero, so the incoming cochain image is zero.

The annihilator identities for vector spaces prove that reduced cohomology
vanishes in a degree if and only if reduced homology vanishes in that degree.
This does not yet identify these groups with the cohomology of the geometric
realization; that comparison is a separate topological theorem.
-/

noncomputable section

namespace AffineTverberg
namespace Simplicial

section ChainDifferential

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder V] [Fintype V]

/-- The outgoing boundary on the chain group of degree `n`.  In augmented
degree zero it is the zero map. -/
def chainDifferential (𝕜 : Type*) [Field 𝕜]
    {K : Finset (Finset V)} (hK : FaceClosed K) :
    (n : ℕ) → chains 𝕜 K n →ₗ[𝕜] chains 𝕜 K (n - 1)
  | 0 => 0
  | n + 1 => chainBoundary 𝕜 hK n

/-- The bundled differential agrees with the ambient oriented boundary in
every degree, including the empty-simplex degree. -/
theorem chainDifferential_coe {K : Finset (Finset V)} (hK : FaceClosed K)
    (n : ℕ) (c : chains 𝕜 K n) :
    (chainDifferential 𝕜 hK n c : Finset V → 𝕜) = boundary 𝕜 V c := by
  cases n with
  | zero => exact (boundary_eq_zero_of_mem_chains_zero c.property).symm
  | succ n => rfl

/-- Kernel membership is exactly the reduced cycle condition. -/
theorem mem_ker_chainDifferential_iff {K : Finset (Finset V)}
    (hK : FaceClosed K) (n : ℕ) (c : chains 𝕜 K n) :
    c ∈ LinearMap.ker (chainDifferential 𝕜 hK n) ↔
      (c : Finset V → 𝕜) ∈ cycles 𝕜 K n := by
  rw [LinearMap.mem_ker, mem_cycles_iff]
  constructor
  · intro hc
    refine ⟨c.property, ?_⟩
    have heq := congrArg Subtype.val hc
    simpa only [chainDifferential_coe, ZeroMemClass.coe_zero] using heq
  · rintro ⟨_, hc⟩
    apply Subtype.ext
    rw [chainDifferential_coe]
    exact hc

/-- The image of the incoming boundary is exactly the reduced boundary
condition within the bundled chain group. -/
theorem mem_range_chainBoundary_iff {K : Finset (Finset V)}
    (hK : FaceClosed K) (n : ℕ) (c : chains 𝕜 K n) :
    c ∈ LinearMap.range (chainBoundary 𝕜 hK n) ↔
      (c : Finset V → 𝕜) ∈ boundaries 𝕜 K n := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.val, b.property, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb, hbc⟩
    exact ⟨⟨b, hb⟩, Subtype.ext hbc⟩

/-- The incoming image is contained in the outgoing kernel. -/
theorem range_chainBoundary_le_ker_chainDifferential
    {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ) :
    LinearMap.range (chainBoundary 𝕜 hK n) ≤
      LinearMap.ker (chainDifferential 𝕜 hK n) := by
  intro c hc
  rw [mem_ker_chainDifferential_iff]
  exact boundaries_le_cycles hK n ((mem_range_chainBoundary_iff hK n c).mp hc)

/-- The familiar exactness equation in bundled chain groups is equivalent
to the existing reduced-acyclicity predicate. -/
theorem chain_exact_iff_isReducedAcyclicAt
    {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ) :
    LinearMap.range (chainBoundary 𝕜 hK n) =
      LinearMap.ker (chainDifferential 𝕜 hK n) ↔ IsReducedAcyclicAt 𝕜 K n := by
  constructor
  · intro heq c hc
    have hc' : (⟨c, hc.1⟩ : chains 𝕜 K n) ∈
        LinearMap.ker (chainDifferential 𝕜 hK n) :=
      (mem_ker_chainDifferential_iff hK n _).mpr hc
    rw [← heq] at hc'
    exact (mem_range_chainBoundary_iff hK n _).mp hc'
  · intro ha
    apply le_antisymm (range_chainBoundary_le_ker_chainDifferential hK n)
    intro c hc
    rw [mem_range_chainBoundary_iff]
    exact ha ((mem_ker_chainDifferential_iff hK n c).mp hc)

end ChainDifferential

section Cohomology

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder V] [Fintype V]

/-- Reduced simplicial cochains are the linear duals of the augmented
chain groups, still indexed by simplex cardinality. -/
abbrev cochains (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) (n : ℕ) :=
  Module.Dual 𝕜 (chains 𝕜 K n)

/-- The cochain coboundary, obtained by precomposing with the oriented
chain boundary. -/
def coboundary (𝕜 : Type*) [Field 𝕜]
    {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ) :
    cochains 𝕜 K n →ₗ[𝕜] cochains 𝕜 K (n + 1) :=
  (chainBoundary 𝕜 hK n).dualMap

def cocycles (𝕜 : Type*) [Field 𝕜]
    {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ) :
    Submodule 𝕜 (cochains 𝕜 K n) :=
  LinearMap.ker (coboundary 𝕜 hK n)

/-- The incoming cochain image.  The zero differential in chain degree zero
ensures the correct augmentation endpoint automatically. -/
def coboundaries (𝕜 : Type*) [Field 𝕜]
    {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ) :
    Submodule 𝕜 (cochains 𝕜 K n) :=
  LinearMap.range (chainDifferential 𝕜 hK n).dualMap

theorem cocycles_eq_dualAnnihilator_range
    {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ) :
    cocycles 𝕜 hK n = (LinearMap.range (chainBoundary 𝕜 hK n)).dualAnnihilator :=
  (chainBoundary 𝕜 hK n).ker_dualMap_eq_dualAnnihilator_range

theorem coboundaries_eq_dualAnnihilator_ker
    {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ) :
    coboundaries 𝕜 hK n =
      (LinearMap.ker (chainDifferential 𝕜 hK n)).dualAnnihilator :=
  (chainDifferential 𝕜 hK n).range_dualMap_eq_dualAnnihilator_ker

/-- The cochain differential squares to zero, in image/kernel form. -/
theorem coboundaries_le_cocycles
    {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ) :
    coboundaries 𝕜 hK n ≤ cocycles 𝕜 hK n := by
  rw [coboundaries_eq_dualAnnihilator_ker, cocycles_eq_dualAnnihilator_range]
  intro f hf
  rw [Submodule.mem_dualAnnihilator] at hf ⊢
  intro c hc
  exact hf c (range_chainBoundary_le_ker_chainDifferential hK n hc)

/-- Reduced cohomology as cocycles modulo coboundaries. -/
def cohomology (𝕜 : Type*) [Field 𝕜]
    {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ) :=
  (cocycles 𝕜 hK n) ⧸
    ((coboundaries 𝕜 hK n).comap (cocycles 𝕜 hK n).subtype)

instance {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ) :
    AddCommGroup (cohomology 𝕜 hK n) :=
  Submodule.Quotient.addCommGroup _

instance {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ) :
    Module 𝕜 (cohomology 𝕜 hK n) :=
  Submodule.Quotient.module _

theorem cohomology_subsingleton_iff_cocycles_le
    {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ) :
    Subsingleton (cohomology 𝕜 hK n) ↔ cocycles 𝕜 hK n ≤ coboundaries 𝕜 hK n := by
  rw [cohomology, Submodule.Quotient.subsingleton_iff]
  constructor
  · intro h f hf
    have hmem : (⟨f, hf⟩ : cocycles 𝕜 hK n) ∈
        (coboundaries 𝕜 hK n).comap (cocycles 𝕜 hK n).subtype := by
      rw [h]
      trivial
    exact hmem
  · intro h
    exact eq_top_iff.mpr fun f _ ↦ h f.property

/-- **Homology and cohomology vanish in the same degrees over a field.**
This uses the actual chain and dual cochain complexes and applies also in
augmented degree zero. -/
theorem cohomology_subsingleton_iff_isReducedAcyclicAt
    {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ) :
    Subsingleton (cohomology 𝕜 hK n) ↔ IsReducedAcyclicAt 𝕜 K n := by
  rw [cohomology_subsingleton_iff_cocycles_le]
  have hle := coboundaries_le_cocycles (𝕜 := 𝕜) hK n
  rw [show (cocycles 𝕜 hK n ≤ coboundaries 𝕜 hK n) ↔
      cocycles 𝕜 hK n = coboundaries 𝕜 hK n from ⟨fun h ↦ le_antisymm h hle,
        fun h ↦ h.le⟩]
  rw [cocycles_eq_dualAnnihilator_range, coboundaries_eq_dualAnnihilator_ker,
    Subspace.dualAnnihilator_inj]
  exact chain_exact_iff_isReducedAcyclicAt hK n

/-- The same universal-coefficient consequence directly in terms of
vanishing homology modules. -/
theorem cohomology_subsingleton_iff_homology_subsingleton
    {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ) :
    Subsingleton (cohomology 𝕜 hK n) ↔ Subsingleton (homology 𝕜 K n) := by
  rw [cohomology_subsingleton_iff_isReducedAcyclicAt, homology_subsingleton_iff]

/-- A bounded reduced-homology vanishing statement supplies the identical
bounded reduced-cohomology vanishing statement. -/
theorem cohomology_subsingleton_of_isReducedAcyclicUpTo
    {K : Finset (Finset V)} (hK : FaceClosed K) {N : ℕ}
    (hacyclic : IsReducedAcyclicUpTo 𝕜 K N) (n : ℕ) (hn : n ≤ N) :
    Subsingleton (cohomology 𝕜 hK n) :=
  (cohomology_subsingleton_iff_isReducedAcyclicAt hK n).mpr (hacyclic n hn)

/-- Free facets give vanishing of reduced cohomology in the same degree as
the already verified boundary-matrix argument. -/
theorem cohomology_subsingleton_of_hasFreeFacets
    {K : Finset (Finset V)} (hK : FaceClosed K) {n : ℕ}
    (hfree : HasFreeFacets (topSimplices K n)) :
    Subsingleton (cohomology 𝕜 hK n) :=
  (cohomology_subsingleton_iff_homology_subsingleton hK n).mpr
    (homology_top_subsingleton_of_hasFreeFacets hfree)

section Shelling

variable {C : Type*} [SemilatticeInf C] [OrderBot C] [DecidableEq C]

/-- The cohomological form of the paper's acyclic-gluing induction, ready
for the top-face subdivision once its shelling and local bounds are proved. -/
theorem cohomology_assignedUnion_subsingleton_of_cellShelling
    (dim : C → ℕ) (A : C → Finset (Finset V))
    (hbot : A ⊥ = {∅})
    (hinter : ∀ c d, A (c ⊓ d) = A c ∩ A d)
    (hclosed : ∀ c, FaceClosed (A c))
    (hlocal : ∀ c, c ≠ ⊥ → IsReducedAcyclicUpTo 𝕜 (A c) (dim c))
    {N : ℕ} {S : Finset C} (hshell : CellShelling dim N S)
    (n : ℕ) (hn : n ≤ N) :
    Subsingleton (cohomology 𝕜 (faceClosed_assignedUnion A hclosed S) n) :=
  cohomology_subsingleton_of_isReducedAcyclicUpTo
    (faceClosed_assignedUnion A hclosed S)
    (isReducedAcyclicUpTo_assignedUnion_of_cellShelling
      dim A hbot hinter hclosed hlocal hshell) n hn

end Shelling

end Cohomology

end Simplicial
end AffineTverberg
