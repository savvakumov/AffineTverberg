import Mathlib.Tactic
import AffineTverberg.SimplicialHomology

set_option linter.style.header false

/-!
# Reduced Mayer-Vietoris for finite face-closed simplicial families

Building on `AffineTverberg/SimplicialHomology.lean`, this file develops the
reduced Mayer-Vietoris machinery for two finite face-closed families `K`, `L` of
simplices on a finite linearly ordered vertex type `V`, with coefficients in an
arbitrary field.  Everything uses the genuine oriented boundary operator and the
augmented (i.e. reduced) chain complex of that file; degree `0` — the degree of
the empty simplex, where the boundary map is the augmentation — is treated as an
honest degree of the complex, so no silent switch to unreduced homology takes
place.

## Main definitions

* `restrictTo` : the linear splitting `c ↦ (fun s => if s ∈ K then c s else 0)`
  of a chain of `K ∪ L` into its `K`-part; it provides a *linear* section of the
  surjection in the Mayer-Vietoris short exact sequence.
* `chainBoundary` : the boundary operator as a map of chain groups
  `chains 𝕜 K (n+1) →ₗ[𝕜] chains 𝕜 K n`.
* `mvIota`, `mvPi` : the two chain maps of
  `0 → C(K ∩ L) → C(K) × C(L) → C(K ∪ L) → 0`.
* `connecting` : the Mayer-Vietoris connecting morphism
  `homology 𝕜 (K ∪ L) (n+1) →ₗ[𝕜] homology 𝕜 (K ∩ L) n`.
* `IsReducedAcyclicUpTo` : bounded-degree reduced acyclicity.
* `partialUnion` : the union of the first `m` members of a family.

## Main results

* `mvIota_injective`, `mvPi_surjective`, `range_mvIota_eq_ker_mvPi` : exactness
  of the short exact sequence of chain groups in every degree.
* `mvIota_comp_chainBoundary`, `mvPi_comp_chainBoundary` : both maps are chain
  maps, i.e. commute with the boundary.
* `connecting_apply` : the explicit description of the connecting morphism.
* `mem_boundaries_of_connecting_eq_zero` : exactness of the Mayer-Vietoris
  sequence at `homology (K ∪ L)`, in explicit cycle/boundary form.
* `isReducedAcyclicAt_union_zero`, `isReducedAcyclicAt_union_succ`,
  `isReducedAcyclic_union` : the acyclic-union theorem, with the degree-zero
  (augmentation) case handled separately and correctly.
* `isReducedAcyclicUpTo_union`, `isReducedAcyclicUpTo_partialUnion`,
  `isReducedAcyclic_partialUnion` : the finite iterative gluing corollary.
* `boundary_eq_zero_iff_augmentation_of_mem_chains_one` : a `1`-chain is a
  reduced cycle iff its augmentation vanishes.
* `not_isReducedAcyclicAt_twoPoints`, `not_isReducedAcyclicAt_inter_singletons` :
  two disjoint points are not reduced acyclic, and neither is the intersection
  `{∅}` of the two single-vertex pieces — so the hypothesis on `K ∩ L` in the
  acyclic-union theorem cannot be dropped.
-/

open scoped BigOperators

namespace AffineTverberg

namespace Simplicial

noncomputable section

section MayerVietoris

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder V] [Fintype V]

/-! ### Face-closedness of unions and intersections -/

omit [Fintype V] in
theorem faceClosed_union {K L : Finset (Finset V)} (hK : FaceClosed K) (hL : FaceClosed L) :
    FaceClosed (K ∪ L) := by
  intro s hs t ht
  rcases Finset.mem_union.mp hs with h | h
  · exact Finset.mem_union_left _ (hK s h t ht)
  · exact Finset.mem_union_right _ (hL s h t ht)

omit [Fintype V] in
theorem faceClosed_inter {K L : Finset (Finset V)} (hK : FaceClosed K) (hL : FaceClosed L) :
    FaceClosed (K ∩ L) := by
  intro s hs t ht
  rw [Finset.mem_inter] at hs ⊢
  exact ⟨hK s hs.1 t ht, hL s hs.2 t ht⟩

omit [LinearOrder V] [Fintype V] in
theorem faceClosed_empty : FaceClosed (∅ : Finset (Finset V)) := by
  intro s hs
  exact absurd hs (Finset.notMem_empty s)

/-! ### The linear splitting -/

/-- The linear map killing all coefficients outside `K`.  Restricted to the
chains of `K ∪ L` it is a linear section of the Mayer-Vietoris surjection. -/
def restrictTo (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) :
    (Finset V → 𝕜) →ₗ[𝕜] (Finset V → 𝕜) where
  toFun c := fun s => if s ∈ K then c s else 0
  map_add' c d := by funext s; by_cases h : s ∈ K <;> simp [h]
  map_smul' a c := by funext s; by_cases h : s ∈ K <;> simp [h]

omit [Fintype V] in
theorem restrictTo_apply (K : Finset (Finset V)) (c : Finset V → 𝕜) (s : Finset V) :
    restrictTo 𝕜 K c s = if s ∈ K then c s else 0 := rfl

omit [Fintype V] in
theorem restrictTo_mem_chains {K L : Finset (Finset V)} {n : ℕ} {c : Finset V → 𝕜}
    (hc : c ∈ chains 𝕜 (K ∪ L) n) : restrictTo 𝕜 K c ∈ chains 𝕜 K n := by
  intro s hs
  rw [restrictTo_apply] at hs
  by_cases hsK : s ∈ K
  · simp only [hsK, ite_true] at hs
    exact ⟨hsK, (hc s hs).2⟩
  · simp only [hsK, ite_false] at hs
    exact absurd rfl hs

omit [Fintype V] in
theorem sub_restrictTo_mem_chains {K L : Finset (Finset V)} {n : ℕ} {c : Finset V → 𝕜}
    (hc : c ∈ chains 𝕜 (K ∪ L) n) : c - restrictTo 𝕜 K c ∈ chains 𝕜 L n := by
  intro s hs
  rw [Pi.sub_apply, restrictTo_apply] at hs
  by_cases hsK : s ∈ K
  · simp only [hsK, ite_true, sub_self, ne_eq, not_true_eq_false] at hs
  · simp only [hsK, ite_false, sub_zero] at hs
    exact ⟨(Finset.mem_union.mp (hc s hs).1).resolve_left hsK, (hc s hs).2⟩

/-! ### The chain groups as a complex -/

/-- The boundary operator viewed as a map of the chain groups of `K`. -/
def chainBoundary (𝕜 : Type*) [Field 𝕜] {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ) :
    chains 𝕜 K (n + 1) →ₗ[𝕜] chains 𝕜 K n :=
  LinearMap.codRestrict _ ((boundary 𝕜 V).comp (chains 𝕜 K (n + 1)).subtype)
    (fun c => boundary_mem_chains hK c.2)

@[simp]
theorem chainBoundary_coe {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ)
    (c : chains 𝕜 K (n + 1)) : (chainBoundary 𝕜 hK n c : Finset V → 𝕜) = boundary 𝕜 V c := rfl

/-- The first map of the Mayer-Vietoris short exact sequence, `c ↦ (c, -c)`. -/
def mvIota (𝕜 : Type*) [Field 𝕜] (K L : Finset (Finset V)) (n : ℕ) :
    chains 𝕜 (K ∩ L) n →ₗ[𝕜] chains 𝕜 K n × chains 𝕜 L n :=
  LinearMap.prod (Submodule.inclusion (chains_mono Finset.inter_subset_left n))
    (-Submodule.inclusion (chains_mono Finset.inter_subset_right n))

omit [Fintype V] in
@[simp]
theorem mvIota_apply_fst (K L : Finset (Finset V)) (n : ℕ) (c : chains 𝕜 (K ∩ L) n) :
    ((mvIota 𝕜 K L n c).1 : Finset V → 𝕜) = (c : Finset V → 𝕜) := rfl

omit [Fintype V] in
@[simp]
theorem mvIota_apply_snd (K L : Finset (Finset V)) (n : ℕ) (c : chains 𝕜 (K ∩ L) n) :
    ((mvIota 𝕜 K L n c).2 : Finset V → 𝕜) = -(c : Finset V → 𝕜) := rfl

/-- The second map of the Mayer-Vietoris short exact sequence, `(a, b) ↦ a + b`. -/
def mvPi (𝕜 : Type*) [Field 𝕜] (K L : Finset (Finset V)) (n : ℕ) :
    chains 𝕜 K n × chains 𝕜 L n →ₗ[𝕜] chains 𝕜 (K ∪ L) n :=
  LinearMap.codRestrict _ ((chains 𝕜 K n).subtype.coprod (chains 𝕜 L n).subtype)
    (fun c => by
      rw [chains_union]
      exact Submodule.add_mem_sup c.1.2 c.2.2)

omit [Fintype V] in
@[simp]
theorem mvPi_coe (K L : Finset (Finset V)) (n : ℕ) (c : chains 𝕜 K n × chains 𝕜 L n) :
    (mvPi 𝕜 K L n c : Finset V → 𝕜) = (c.1 : Finset V → 𝕜) + (c.2 : Finset V → 𝕜) := rfl

/-! ### Exactness of the short exact sequence of chain groups -/

omit [Fintype V] in
theorem mvIota_injective (K L : Finset (Finset V)) (n : ℕ) :
    Function.Injective (mvIota 𝕜 K L n) := by
  intro c d h
  have h1 : ((mvIota 𝕜 K L n c).1 : Finset V → 𝕜) = ((mvIota 𝕜 K L n d).1 : Finset V → 𝕜) := by
    rw [h]
  rw [mvIota_apply_fst, mvIota_apply_fst] at h1
  exact Subtype.ext h1

omit [Fintype V] in
theorem mvPi_surjective (K L : Finset (Finset V)) (n : ℕ) :
    Function.Surjective (mvPi 𝕜 K L n) := by
  intro c
  refine ⟨(⟨restrictTo 𝕜 K (c : Finset V → 𝕜), restrictTo_mem_chains c.2⟩,
      ⟨(c : Finset V → 𝕜) - restrictTo 𝕜 K (c : Finset V → 𝕜), sub_restrictTo_mem_chains c.2⟩), ?_⟩
  have habel : ∀ x y : Finset V → 𝕜, x + (y - x) = y := fun x y => by abel
  apply Subtype.ext
  rw [mvPi_coe]
  exact habel _ _

omit [Fintype V] in
/-- Exactness in the middle: the image of `C(K ∩ L)` is exactly the kernel of
`C(K) × C(L) → C(K ∪ L)`. -/
theorem range_mvIota_eq_ker_mvPi (K L : Finset (Finset V)) (n : ℕ) :
    LinearMap.range (mvIota 𝕜 K L n) = LinearMap.ker (mvPi 𝕜 K L n) := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    rw [mvPi_coe, mvIota_apply_fst, mvIota_apply_snd]
    simp
  · rintro ⟨a, b⟩ hab
    rw [LinearMap.mem_ker] at hab
    have hab' : (a : Finset V → 𝕜) + (b : Finset V → 𝕜) = 0 := congrArg Subtype.val hab
    have hb : (b : Finset V → 𝕜) = -(a : Finset V → 𝕜) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hab'
    have haL : (a : Finset V → 𝕜) ∈ chains 𝕜 L n := by
      have hbn : -(b : Finset V → 𝕜) ∈ chains 𝕜 L n := Submodule.neg_mem _ b.2
      rwa [hb, neg_neg] at hbn
    have ha : (a : Finset V → 𝕜) ∈ chains 𝕜 (K ∩ L) n := by
      rw [chains_inter]
      exact ⟨a.2, haL⟩
    refine ⟨⟨(a : Finset V → 𝕜), ha⟩, ?_⟩
    refine Prod.ext ?_ ?_ <;> apply Subtype.ext
    · rw [mvIota_apply_fst]
    · rw [mvIota_apply_snd]
      exact hb.symm

/-! ### Compatibility with the boundary -/

theorem mvIota_comp_chainBoundary {K L : Finset (Finset V)} (hK : FaceClosed K)
    (hL : FaceClosed L) (n : ℕ) :
    (mvIota 𝕜 K L n).comp (chainBoundary 𝕜 (faceClosed_inter hK hL) n) =
      ((chainBoundary 𝕜 hK n).prodMap (chainBoundary 𝕜 hL n)).comp (mvIota 𝕜 K L (n + 1)) := by
  refine LinearMap.ext fun c => ?_
  refine Prod.ext ?_ ?_ <;> apply Subtype.ext
  · rfl
  · change -(boundary 𝕜 V (c : Finset V → 𝕜)) = boundary 𝕜 V (-(c : Finset V → 𝕜))
    rw [map_neg]

theorem mvPi_comp_chainBoundary {K L : Finset (Finset V)} (hK : FaceClosed K)
    (hL : FaceClosed L) (n : ℕ) :
    (mvPi 𝕜 K L n).comp ((chainBoundary 𝕜 hK n).prodMap (chainBoundary 𝕜 hL n)) =
      (chainBoundary 𝕜 (faceClosed_union hK hL) n).comp (mvPi 𝕜 K L (n + 1)) := by
  refine LinearMap.ext fun c => ?_
  apply Subtype.ext
  change boundary 𝕜 V (c.1 : Finset V → 𝕜) + boundary 𝕜 V (c.2 : Finset V → 𝕜) =
    boundary 𝕜 V ((c.1 : Finset V → 𝕜) + (c.2 : Finset V → 𝕜))
  rw [map_add]

/-! ### Homology classes -/

/-- The homology class of a reduced cycle. -/
def homologyMk (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) (n : ℕ) (c : cycles 𝕜 K n) :
    homology 𝕜 K n := Submodule.Quotient.mk c

theorem homologyMk_eq_zero_iff {K : Finset (Finset V)} {n : ℕ} (c : cycles 𝕜 K n) :
    homologyMk 𝕜 K n c = 0 ↔ (c : Finset V → 𝕜) ∈ boundaries 𝕜 K n := by
  constructor
  · intro h
    have h' : c ∈ (boundaries 𝕜 K n).comap (cycles 𝕜 K n).subtype :=
      (Submodule.Quotient.mk_eq_zero _).mp h
    simpa using h'
  · intro h
    exact (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using h)

theorem homologyMk_surjective (K : Finset (Finset V)) (n : ℕ) :
    Function.Surjective (homologyMk 𝕜 K n) := Quotient.mk_surjective

/-! ### The connecting morphism -/

theorem boundary_restrictTo_mem_cycles {K L : Finset (Finset V)} (hK : FaceClosed K)
    (hL : FaceClosed L) {n : ℕ} {c : Finset V → 𝕜} (hc : c ∈ cycles 𝕜 (K ∪ L) (n + 1)) :
    boundary 𝕜 V (restrictTo 𝕜 K c) ∈ cycles 𝕜 (K ∩ L) n := by
  obtain ⟨hcc, hcz⟩ := hc
  refine ⟨?_, boundary_boundary_apply _⟩
  rw [chains_inter]
  refine ⟨boundary_mem_chains hK (restrictTo_mem_chains hcc), ?_⟩
  have hb : boundary 𝕜 V (c - restrictTo 𝕜 K c) ∈ chains 𝕜 L n :=
    boundary_mem_chains hL (sub_restrictTo_mem_chains hcc)
  have hrw : boundary 𝕜 V (restrictTo 𝕜 K c) = -boundary 𝕜 V (c - restrictTo 𝕜 K c) := by
    rw [map_sub, hcz]
    abel
  rw [hrw]
  exact Submodule.neg_mem _ hb

/-- The linear map `cycles (K ∪ L) (n+1) → homology (K ∩ L) n` which induces the
connecting morphism. -/
def connectingAux (𝕜 : Type*) [Field 𝕜] {K L : Finset (Finset V)} (hK : FaceClosed K)
    (hL : FaceClosed L) (n : ℕ) :
    cycles 𝕜 (K ∪ L) (n + 1) →ₗ[𝕜] homology 𝕜 (K ∩ L) n :=
  (Submodule.mkQ _).comp
    (LinearMap.codRestrict (cycles 𝕜 (K ∩ L) n)
      ((boundary 𝕜 V).comp ((restrictTo 𝕜 K).comp (cycles 𝕜 (K ∪ L) (n + 1)).subtype))
      (fun c => boundary_restrictTo_mem_cycles hK hL c.2))

theorem connectingAux_apply {K L : Finset (Finset V)} (hK : FaceClosed K) (hL : FaceClosed L)
    (n : ℕ) (c : cycles 𝕜 (K ∪ L) (n + 1)) :
    connectingAux 𝕜 hK hL n c =
      homologyMk 𝕜 (K ∩ L) n ⟨boundary 𝕜 V (restrictTo 𝕜 K (c : Finset V → 𝕜)),
        boundary_restrictTo_mem_cycles hK hL c.2⟩ := rfl

/-- Well-definedness of the connecting morphism: the class of `∂(c|_K)` only
depends on the class of the cycle `c` modulo boundaries. -/
theorem boundary_restrictTo_mem_boundaries {K L : Finset (Finset V)}
    (hK : FaceClosed K) (hL : FaceClosed L) {n : ℕ} {c : Finset V → 𝕜}
    (hc : c ∈ boundaries 𝕜 (K ∪ L) (n + 1)) :
    boundary 𝕜 V (restrictTo 𝕜 K c) ∈ boundaries 𝕜 (K ∩ L) n := by
  obtain ⟨d, hd, rfl⟩ := hc
  set a := restrictTo 𝕜 K (boundary 𝕜 V d) with ha
  set p := restrictTo 𝕜 K d with hp
  have hpK : p ∈ chains 𝕜 K (n + 1 + 1) := restrictTo_mem_chains hd
  have hqL : d - p ∈ chains 𝕜 L (n + 1 + 1) := sub_restrictTo_mem_chains hd
  have haK : a ∈ chains 𝕜 K (n + 1) :=
    restrictTo_mem_chains (boundary_mem_chains (faceClosed_union hK hL) hd)
  have hbL : boundary 𝕜 V d - a ∈ chains 𝕜 L (n + 1) :=
    sub_restrictTo_mem_chains (boundary_mem_chains (faceClosed_union hK hL) hd)
  refine ⟨a - boundary 𝕜 V p, ?_, ?_⟩
  · rw [chains_inter]
    refine ⟨Submodule.sub_mem _ haK (boundary_mem_chains hK hpK), ?_⟩
    have hrw : a - boundary 𝕜 V p = boundary 𝕜 V (d - p) - (boundary 𝕜 V d - a) := by
      rw [map_sub]
      abel
    rw [hrw]
    exact Submodule.sub_mem _ (boundary_mem_chains hL hqL) hbL
  · rw [map_sub, boundary_boundary_apply, sub_zero]

/-- The Mayer-Vietoris connecting morphism on reduced homology. -/
def connecting (𝕜 : Type*) [Field 𝕜] {K L : Finset (Finset V)} (hK : FaceClosed K)
    (hL : FaceClosed L) (n : ℕ) :
    homology 𝕜 (K ∪ L) (n + 1) →ₗ[𝕜] homology 𝕜 (K ∩ L) n :=
  Submodule.liftQ _ (connectingAux 𝕜 hK hL n) (by
    intro c hc
    rw [LinearMap.mem_ker, connectingAux_apply, homologyMk_eq_zero_iff]
    exact boundary_restrictTo_mem_boundaries hK hL (by simpa using hc))

@[simp]
theorem connecting_apply {K L : Finset (Finset V)} (hK : FaceClosed K) (hL : FaceClosed L)
    (n : ℕ) (c : cycles 𝕜 (K ∪ L) (n + 1)) :
    connecting 𝕜 hK hL n (homologyMk 𝕜 (K ∪ L) (n + 1) c) =
      homologyMk 𝕜 (K ∩ L) n ⟨boundary 𝕜 V (restrictTo 𝕜 K (c : Finset V → 𝕜)),
        boundary_restrictTo_mem_cycles hK hL c.2⟩ := rfl

/-! ### Exactness of Mayer-Vietoris at `H(K ∪ L)` -/

/-- Exactness of the reduced Mayer-Vietoris sequence at `homology (K ∪ L)`,
stated explicitly on cycles: a cycle of `K ∪ L` killed by the connecting
morphism is a boundary, provided `K` and `L` are exact in that degree. -/
theorem mem_boundaries_of_connecting_eq_zero {K L : Finset (Finset V)} (hK : FaceClosed K)
    (hL : FaceClosed L) {n : ℕ} (hKa : IsReducedAcyclicAt 𝕜 K (n + 1))
    (hLa : IsReducedAcyclicAt 𝕜 L (n + 1)) {c : Finset V → 𝕜}
    (hc : c ∈ cycles 𝕜 (K ∪ L) (n + 1))
    (hδ : connecting 𝕜 hK hL n (homologyMk 𝕜 (K ∪ L) (n + 1) ⟨c, hc⟩) = 0) :
    c ∈ boundaries 𝕜 (K ∪ L) (n + 1) := by
  rw [connecting_apply, homologyMk_eq_zero_iff] at hδ
  obtain ⟨e, he, hee⟩ := hδ
  obtain ⟨hcc, hcz⟩ := hc
  set a := restrictTo 𝕜 K c with ha
  have hee' : boundary 𝕜 V e = boundary 𝕜 V a := hee
  have hcz' : boundary 𝕜 V c = 0 := hcz
  have haK : a ∈ chains 𝕜 K (n + 1) := restrictTo_mem_chains hcc
  have hbL : c - a ∈ chains 𝕜 L (n + 1) := sub_restrictTo_mem_chains hcc
  have he' : e ∈ chains 𝕜 K (n + 1) ∧ e ∈ chains 𝕜 L (n + 1) := by
    have := he
    rw [chains_inter] at this
    exact this
  have h1 : a - e ∈ cycles 𝕜 K (n + 1) := by
    rw [mem_cycles_iff]
    refine ⟨Submodule.sub_mem _ haK he'.1, ?_⟩
    rw [map_sub, hee', sub_self]
  have h2 : c - a + e ∈ cycles 𝕜 L (n + 1) := by
    rw [mem_cycles_iff]
    refine ⟨Submodule.add_mem _ hbL he'.2, ?_⟩
    rw [map_add, map_sub, hcz', hee']
    abel
  obtain ⟨u, hu, hue⟩ := hKa h1
  obtain ⟨w, hw, hwe⟩ := hLa h2
  refine ⟨u + w, ?_, ?_⟩
  · rw [chains_union]
    exact Submodule.add_mem_sup hu hw
  · rw [map_add, hue, hwe]
    abel

/-! ### The acyclic-union theorem -/

/-- In degree `0` (the degree of the empty simplex) the boundary of a chain
vanishes automatically: there is nothing below the augmentation. -/
theorem boundary_eq_zero_of_mem_chains_zero {K : Finset (Finset V)} {c : Finset V → 𝕜}
    (hc : c ∈ chains 𝕜 K 0) : boundary 𝕜 V c = 0 := by
  have hc0 : ∀ s : Finset V, s.card ≠ 0 → c s = 0 := by
    intro s hs
    by_contra h
    exact hs (hc s h).2
  funext f
  rw [boundary_apply]
  refine Finset.sum_eq_zero fun v hv => ?_
  have hvf : v ∉ f := by simpa using hv
  rw [hc0 (insert v f) (by rw [Finset.card_insert_of_notMem hvf]; omega), mul_zero]

/-- A `1`-chain (degree of the vertices) is a reduced cycle exactly when its
augmentation vanishes.  This is the concrete form of the degree-zero end of the
augmented complex. -/
theorem boundary_eq_zero_iff_augmentation_of_mem_chains_one {K : Finset (Finset V)}
    {c : Finset V → 𝕜} (hc : c ∈ chains 𝕜 K 1) :
    boundary 𝕜 V c = 0 ↔ ∑ v : V, c {v} = 0 := by
  constructor
  · intro h
    have hemp := congrFun h (∅ : Finset V)
    rwa [boundary_apply_empty, augmentation_apply] at hemp
  · intro h
    funext f
    rcases eq_or_ne f ∅ with rfl | hf
    · rw [boundary_apply_empty, augmentation_apply]
      exact h
    · rw [boundary_apply]
      refine Finset.sum_eq_zero fun v hv => ?_
      have hvf : v ∉ f := by simpa using hv
      have hcard : (insert v f).card ≠ 1 := by
        rw [Finset.card_insert_of_notMem hvf]
        have hf0 : f.card ≠ 0 := fun h0 => hf (Finset.card_eq_zero.mp h0)
        omega
      have hz : c (insert v f) = 0 := by
        by_contra h'
        exact hcard (hc _ h').2
      rw [hz, mul_zero]

/-- The degree-zero (augmentation) case of the acyclic-union theorem: it does
*not* need any hypothesis on `K ∩ L`. -/
theorem isReducedAcyclicAt_union_zero {K L : Finset (Finset V)}
    (hKa : IsReducedAcyclicAt 𝕜 K 0) (hLa : IsReducedAcyclicAt 𝕜 L 0) :
    IsReducedAcyclicAt 𝕜 (K ∪ L) 0 := by
  rintro c ⟨hcc, -⟩
  set a := restrictTo 𝕜 K c with ha
  have haK : a ∈ chains 𝕜 K 0 := restrictTo_mem_chains hcc
  have hbL : c - a ∈ chains 𝕜 L 0 := sub_restrictTo_mem_chains hcc
  obtain ⟨u, hu, hue⟩ := hKa ⟨haK, boundary_eq_zero_of_mem_chains_zero haK⟩
  obtain ⟨w, hw, hwe⟩ := hLa ⟨hbL, boundary_eq_zero_of_mem_chains_zero hbL⟩
  refine ⟨u + w, ?_, ?_⟩
  · rw [chains_union]
    exact Submodule.add_mem_sup hu hw
  · rw [map_add, hue, hwe]
    abel

/-- The positive-degree case of the acyclic-union theorem: exactness of `K` and
`L` in degree `n+1` together with exactness of `K ∩ L` in the adjacent degree
`n` gives exactness of `K ∪ L` in degree `n+1`. -/
theorem isReducedAcyclicAt_union_succ {K L : Finset (Finset V)} (hK : FaceClosed K)
    (hL : FaceClosed L) {n : ℕ} (hKa : IsReducedAcyclicAt 𝕜 K (n + 1))
    (hLa : IsReducedAcyclicAt 𝕜 L (n + 1)) (hKLa : IsReducedAcyclicAt 𝕜 (K ∩ L) n) :
    IsReducedAcyclicAt 𝕜 (K ∪ L) (n + 1) := by
  intro c hc
  refine mem_boundaries_of_connecting_eq_zero hK hL hKa hLa hc ?_
  rw [connecting_apply, homologyMk_eq_zero_iff]
  exact hKLa (boundary_restrictTo_mem_cycles hK hL hc)

/-- **Acyclic union.** If `K`, `L` and `K ∩ L` all have vanishing reduced
homology, so does `K ∪ L`. -/
theorem isReducedAcyclic_union {K L : Finset (Finset V)} (hK : FaceClosed K) (hL : FaceClosed L)
    (hKa : IsReducedAcyclic 𝕜 K) (hLa : IsReducedAcyclic 𝕜 L)
    (hKLa : IsReducedAcyclic 𝕜 (K ∩ L)) : IsReducedAcyclic 𝕜 (K ∪ L) := by
  intro n
  cases n with
  | zero => exact isReducedAcyclicAt_union_zero (hKa 0) (hLa 0)
  | succ m => exact isReducedAcyclicAt_union_succ hK hL (hKa (m + 1)) (hLa (m + 1)) (hKLa m)

/-- The acyclic-union theorem in terms of vanishing homology modules. -/
theorem homology_union_subsingleton {K L : Finset (Finset V)} (hK : FaceClosed K)
    (hL : FaceClosed L) (hKa : ∀ n, Subsingleton (homology 𝕜 K n))
    (hLa : ∀ n, Subsingleton (homology 𝕜 L n))
    (hKLa : ∀ n, Subsingleton (homology 𝕜 (K ∩ L) n)) (n : ℕ) :
    Subsingleton (homology 𝕜 (K ∪ L) n) := by
  rw [homology_subsingleton_iff]
  refine isReducedAcyclic_union hK hL (fun m => ?_) (fun m => ?_) (fun m => ?_) n <;>
    rw [← homology_subsingleton_iff]
  exacts [hKa m, hLa m, hKLa m]

/-! ### Bounded-degree acyclicity and iterated gluing -/

/-- `K` has vanishing reduced homology in all degrees `≤ N`. -/
def IsReducedAcyclicUpTo (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) (N : ℕ) : Prop :=
  ∀ n ≤ N, IsReducedAcyclicAt 𝕜 K n

theorem isReducedAcyclicUpTo_of_isReducedAcyclic {K : Finset (Finset V)} (h : IsReducedAcyclic 𝕜 K)
    (N : ℕ) : IsReducedAcyclicUpTo 𝕜 K N := fun n _ => h n

theorem isReducedAcyclic_of_isReducedAcyclicUpTo_all {K : Finset (Finset V)}
    (h : ∀ N, IsReducedAcyclicUpTo 𝕜 K N) : IsReducedAcyclic 𝕜 K := fun n => h n n le_rfl

theorem IsReducedAcyclicUpTo.mono {K : Finset (Finset V)} {N M : ℕ} (h : IsReducedAcyclicUpTo 𝕜 K N)
    (hMN : M ≤ N) : IsReducedAcyclicUpTo 𝕜 K M := fun n hn => h n (hn.trans hMN)

/-- Bounded-degree version of the acyclic-union theorem. -/
theorem isReducedAcyclicUpTo_union {K L : Finset (Finset V)} (hK : FaceClosed K)
    (hL : FaceClosed L) {N : ℕ} (hKa : IsReducedAcyclicUpTo 𝕜 K N)
    (hLa : IsReducedAcyclicUpTo 𝕜 L N) (hKLa : IsReducedAcyclicUpTo 𝕜 (K ∩ L) N) :
    IsReducedAcyclicUpTo 𝕜 (K ∪ L) N := by
  intro n hn
  cases n with
  | zero => exact isReducedAcyclicAt_union_zero (hKa 0 (Nat.zero_le _)) (hLa 0 (Nat.zero_le _))
  | succ m =>
      exact isReducedAcyclicAt_union_succ hK hL (hKa (m + 1) hn) (hLa (m + 1) hn)
        (hKLa m (le_trans (Nat.le_succ m) hn))

omit [LinearOrder V] [Fintype V] in
theorem chains_empty (n : ℕ) : chains 𝕜 (∅ : Finset (Finset V)) n = ⊥ := by
  refine le_antisymm (fun c hc => ?_) bot_le
  have hz : c = 0 := by
    funext s
    by_contra h
    exact absurd (hc s h).1 (Finset.notMem_empty s)
  simpa using hz

/-- The empty family is reduced acyclic; this starts the iterated gluing. -/
theorem isReducedAcyclic_empty : IsReducedAcyclic 𝕜 (∅ : Finset (Finset V)) := by
  intro n c hc
  have hz : c = 0 := by
    have h1 := hc.1
    rw [chains_empty] at h1
    simpa using h1
  rw [hz]
  exact Submodule.zero_mem _

/-- The union of the first `m` members of a family of simplicial families. -/
def partialUnion (F : ℕ → Finset (Finset V)) (m : ℕ) : Finset (Finset V) :=
  (Finset.range m).biUnion F

omit [Fintype V] in
@[simp]
theorem partialUnion_zero (F : ℕ → Finset (Finset V)) : partialUnion F 0 = ∅ := by
  simp [partialUnion]

omit [Fintype V] in
theorem partialUnion_succ (F : ℕ → Finset (Finset V)) (m : ℕ) :
    partialUnion F (m + 1) = partialUnion F m ∪ F m := by
  ext s
  simp only [partialUnion, Finset.mem_biUnion, Finset.mem_range, Finset.mem_union]
  constructor
  · rintro ⟨i, hi, hs⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
    · exact Or.inl ⟨i, h, hs⟩
    · exact Or.inr hs
  · rintro (⟨i, hi, hs⟩ | hs)
    · exact ⟨i, hi.trans (Nat.lt_succ_self m), hs⟩
    · exact ⟨m, Nat.lt_succ_self m, hs⟩

omit [Fintype V] in
theorem faceClosed_partialUnion {F : ℕ → Finset (Finset V)} {m : ℕ}
    (hF : ∀ i < m, FaceClosed (F i)) : FaceClosed (partialUnion F m) := by
  intro s hs t ht
  rw [partialUnion, Finset.mem_biUnion] at hs ⊢
  obtain ⟨i, hi, hsi⟩ := hs
  exact ⟨i, hi, hF i (Finset.mem_range.mp hi) s hsi t ht⟩

/-- **Iterated acyclic gluing** (bounded-degree form).  If each piece `F i` and
each intersection of `F i` with the union of the previous pieces is reduced
acyclic up to degree `N`, then the union of the first `m` pieces is reduced
acyclic up to degree `N`. -/
theorem isReducedAcyclicUpTo_partialUnion {F : ℕ → Finset (Finset V)} {N m : ℕ}
    (hFC : ∀ i < m, FaceClosed (F i)) (hFa : ∀ i < m, IsReducedAcyclicUpTo 𝕜 (F i) N)
    (hIa : ∀ i < m, IsReducedAcyclicUpTo 𝕜 (partialUnion F i ∩ F i) N) :
    IsReducedAcyclicUpTo 𝕜 (partialUnion F m) N := by
  induction m with
  | zero =>
      rw [partialUnion_zero]
      exact isReducedAcyclicUpTo_of_isReducedAcyclic isReducedAcyclic_empty N
  | succ k ih =>
      have hk : ∀ i, i < k → i < k + 1 := fun i hi => hi.trans (Nat.lt_succ_self k)
      have hprev := ih (fun i hi => hFC i (hk i hi)) (fun i hi => hFa i (hk i hi))
        (fun i hi => hIa i (hk i hi))
      rw [partialUnion_succ]
      exact isReducedAcyclicUpTo_union (faceClosed_partialUnion fun i hi => hFC i (hk i hi))
        (hFC k (Nat.lt_succ_self k)) hprev (hFa k (Nat.lt_succ_self k))
        (hIa k (Nat.lt_succ_self k))

/-- **Iterated acyclic gluing** (unbounded form): a finite ordered family of
face-closed pieces, each reduced acyclic and meeting the union of its
predecessors in a reduced acyclic subfamily, has reduced acyclic union. -/
theorem isReducedAcyclic_partialUnion {F : ℕ → Finset (Finset V)} {m : ℕ}
    (hFC : ∀ i < m, FaceClosed (F i)) (hFa : ∀ i < m, IsReducedAcyclic 𝕜 (F i))
    (hIa : ∀ i < m, IsReducedAcyclic 𝕜 (partialUnion F i ∩ F i)) :
    IsReducedAcyclic 𝕜 (partialUnion F m) :=
  isReducedAcyclic_of_isReducedAcyclicUpTo_all fun N =>
    isReducedAcyclicUpTo_partialUnion hFC
      (fun i hi => isReducedAcyclicUpTo_of_isReducedAcyclic (hFa i hi) N)
      (fun i hi => isReducedAcyclicUpTo_of_isReducedAcyclic (hIa i hi) N)

/-! ### Necessity of the hypothesis on the intersection

The union of two acyclic pieces need *not* be acyclic: two disjoint points are
the union of two single-vertex complexes, whose intersection `{∅}` fails to be
reduced acyclic in degree `0`.  Both facts are proved below with the genuine
reduced (augmented) chain complex, so the acyclic-union theorem is sharp and its
hypotheses are not vacuous. -/

/-- Two disjoint points, as the union of two (acyclic) single-vertex complexes. -/
def twoPoints : Finset (Finset (Fin 2)) :=
  ({0} : Finset (Fin 2)).powerset ∪ ({1} : Finset (Fin 2)).powerset

theorem not_isReducedAcyclicAt_twoPoints : ¬ IsReducedAcyclicAt ℚ twoPoints 1 := by
  intro h
  set c : Finset (Fin 2) → ℚ := fun s => if s = {0} then 1 else if s = {1} then -1 else 0 with hcdef
  have hcc : c ∈ chains ℚ twoPoints 1 := by
    intro s hs
    by_cases h0 : s = {0}
    · exact ⟨by rw [h0]; decide, by rw [h0]; decide⟩
    · by_cases h1 : s = {1}
      · exact ⟨by rw [h1]; decide, by rw [h1]; decide⟩
      · simp [hcdef, h0, h1] at hs
  have hcyc : c ∈ cycles ℚ twoPoints 1 := by
    rw [mem_cycles_iff]
    refine ⟨hcc, (boundary_eq_zero_iff_augmentation_of_mem_chains_one hcc).mpr ?_⟩
    simp [hcdef, Fin.sum_univ_two]
  obtain ⟨d, hd, hde⟩ := h hcyc
  have hd0 : d = 0 := by
    funext s
    by_contra hs
    obtain ⟨hsm, hscard⟩ := hd s hs
    revert hscard
    fin_cases hsm <;> decide
  rw [hd0, map_zero] at hde
  have hc0 : c {0} = (0 : ℚ) := by rw [← hde]; rfl
  simp [hcdef] at hc0

theorem not_isReducedAcyclicAt_inter_singletons :
    ¬ IsReducedAcyclicAt ℚ
      (({0} : Finset (Fin 2)).powerset ∩ ({1} : Finset (Fin 2)).powerset) 0 := by
  intro h
  set c : Finset (Fin 2) → ℚ := fun s => if s = ∅ then 1 else 0 with hcdef
  have hcc :
      c ∈ chains ℚ (({0} : Finset (Fin 2)).powerset ∩ ({1} : Finset (Fin 2)).powerset) 0 := by
    intro s hs
    by_cases h0 : s = ∅
    · exact ⟨by rw [h0]; decide, by rw [h0]; decide⟩
    · simp [hcdef, h0] at hs
  obtain ⟨d, hd, hde⟩ := h ⟨hcc, boundary_eq_zero_of_mem_chains_zero hcc⟩
  have hd0 : d = 0 := by
    funext s
    by_contra hs
    obtain ⟨hsm, hscard⟩ := hd s hs
    revert hscard
    fin_cases hsm
    decide
  rw [hd0, map_zero] at hde
  have hc0 : c ∅ = (0 : ℚ) := by rw [← hde]; rfl
  simp [hcdef] at hc0

/-! ### A non-degeneracy check

The acyclic-union theorem is not vacuous: gluing the edge `{0,1}` and the edge
`{1,2}` along the vertex `{1}` gives a reduced acyclic complex (a path). -/

omit [LinearOrder V] [Fintype V] in
theorem faceClosed_powerset (S : Finset V) : FaceClosed S.powerset :=
  fun _s hs _t ht => Finset.mem_powerset.mpr (ht.trans (Finset.mem_powerset.mp hs))

example : IsReducedAcyclic ℚ
    (({0, 1} : Finset (Fin 3)).powerset ∪ ({1, 2} : Finset (Fin 3)).powerset) := by
  have hinter : ({0, 1} : Finset (Fin 3)).powerset ∩ ({1, 2} : Finset (Fin 3)).powerset =
      ({1} : Finset (Fin 3)).powerset := by decide
  refine isReducedAcyclic_union (faceClosed_powerset _) (faceClosed_powerset _)
    (isReducedAcyclic_powerset (a := 1) (by decide))
    (isReducedAcyclic_powerset (a := 1) (by decide)) ?_
  rw [hinter]
  exact isReducedAcyclic_powerset (a := 1) (by decide)

/-! ### Next steps

The layer above is complete and self-contained.  The first statements *not*
formalized here are:

* the induced maps of `mvIota` and `mvPi` on reduced homology, and exactness of
  the resulting long Mayer-Vietoris sequence at the two remaining spots
  (exactness at `homology (K ∪ L)` is `mem_boundaries_of_connecting_eq_zero`);
* the combinatorial notion of a shellable ball together with a shelling-induced
  ordered family `F` whose pieces satisfy the hypotheses of
  `isReducedAcyclicUpTo_partialUnion`, which is what turns the gluing corollary
  above into the paper's acyclic gluing over a shellable ball. -/

end MayerVietoris

end

end Simplicial

end AffineTverberg

