import AffineTverberg.LocalAcyclicity
import AffineTverberg.SingularAcyclicFiber

set_option linter.style.header false

/-!
# From reduced simplicial acyclicity to actual singular acyclicity

`AffineTverberg/LocalAcyclicity.lean` derives singular acyclicity of a
*geometric* triangulated face from a good-vertex count.  The acyclic gluing
theorem, however, produces reduced acyclicity of a glued family in the
oriented augmented simplicial complex.  This file supplies the missing
general bridge, with no geometric hypothesis beyond the fact that the family
is realized by a genuine geometric simplicial complex:

* `isIso_augHomology_of_isReducedAcyclicAt_one` — reduced simplicial
  exactness in the vertex degree, together with the existence of a vertex,
  makes the simplicial augmentation an isomorphism on `H₀`.  This is the
  general form of `isIso_augHomology_simplicial`, which assumed a cone.
* `singular_acyclicity_of_isReducedAcyclicUpTo` — **the bridge**: if a
  face-closed family `K` with a geometric realization `p` is reduced acyclic
  up to the chain degree `N`, then the actual geometric carrier is nonempty,
  its actual degree-zero singular augmentation is invertible (as soon as
  `1 ≤ N`), and its actual singular homology vanishes in every degree `k ≠ 0`
  with `k + 1 ≤ N`.

Everything is computed with Mathlib's singular homology of the actual
subspace of the ambient normed space; the comparison used is the verified
chain-level comparison map of `SimplicialToSingular.lean`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.Simplicial

variable {V E : Type} [Fintype V] [LinearOrder V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Reduced exactness in the vertex degree gives an invertible
augmentation.**  Only a vertex of `K` and reduced acyclicity at chain degree
`1` are used. -/
theorem isIso_augHomology_of_isReducedAcyclicAt_one {K : Finset (Finset V)}
    (hK : FaceClosed K) {a : V} (hvertex : ({a} : Finset V) ∈ K)
    (hacy : IsReducedAcyclicAt ℝ K 1) :
    IsIso (augHomology (simplicialChains hK) (simplicialAug hK) (d_simplicialAug hK)) := by
  classical
  set D := simplicialChains hK with hD
  set desc := D.descOpcycles (simplicialAug hK) 1 (by simp) (d_simplicialAug hK) with hdescdef
  have hpd : D.pOpcycles 0 ≫ desc = simplicialAug hK :=
    D.p_descOpcycles (simplicialAug hK) 1 (by simp) (d_simplicialAug hK)
  have hpd' : ∀ c : ↥(chains ℝ K 1),
      desc.hom ((D.pOpcycles 0).hom c) = augmentation ℝ V (c : Finset V → ℝ) :=
    fun c ↦ congrArg (fun (g : D.X 0 ⟶ ModuleCat.of ℝ ℝ) ↦ g.hom c) hpd
  have hsurj_p : ∀ z, ∃ c : ↥(chains ℝ K 1), (D.pOpcycles 0).hom c = z := by
    intro z
    obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective (D.pOpcycles 0)).mp inferInstance z
    exact ⟨(c : ↥(chains ℝ K 1)), hc⟩
  have hiso : IsIso desc := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨c, rfl⟩ := hsurj_p z
      have hcz : augmentation ℝ V (c : Finset V → ℝ) = 0 := (hpd' c).symm.trans hz
      have hcycle : ((c : Finset V → ℝ)) ∈ cycles ℝ K 1 :=
        ⟨c.2, (boundary_eq_zero_iff_augmentation_of_mem_chains_one c.2).mpr hcz⟩
      obtain ⟨b, hb, hbc⟩ := hacy hcycle
      have hbeq : ((D.d 1 0).hom (⟨b, hb⟩ : ↥(chains ℝ K 2)) : ↥(chains ℝ K 1)) = c :=
        Subtype.ext (by rw [simplicialChains_d_apply hK 0 ⟨b, hb⟩]; exact hbc)
      have hzero : (D.pOpcycles 0).hom ((D.d 1 0).hom (⟨b, hb⟩ : ↥(chains ℝ K 2))) = 0 :=
        congrArg (fun (g : D.X 1 ⟶ D.opcycles 0) ↦ g.hom (⟨b, hb⟩ : ↥(chains ℝ K 2)))
          (D.d_pOpcycles 1 0)
      rw [← hbeq]
      exact hzero
    · intro r
      have hmem : (fun s ↦ if s = ({a} : Finset V) then r else 0) ∈ chains ℝ K 1 := by
        intro s hs
        by_cases hsa : s = {a}
        · exact ⟨hsa ▸ hvertex, by simp [hsa]⟩
        · simp [hsa] at hs
      refine ⟨(D.pOpcycles 0).hom ⟨_, hmem⟩, ?_⟩
      rw [hpd' ⟨_, hmem⟩]
      change ∑ v : V, (if ({v} : Finset V) = {a} then r else 0) = r
      rw [Finset.sum_eq_single a]
      · simp
      · intro v _ hv
        have hva : ({v} : Finset V) ≠ {a} := by simpa using hv
        simp [hva]
      · intro h
        exact absurd (Finset.mem_univ a) h
  rw [augHomology]
  infer_instance

omit [Fintype V] [LinearOrder V] [FiniteDimensional ℝ E] in
/-- A vertex of the family gives a point of the geometric carrier. -/
theorem mem_geometricCarrier_of_vertex {K : Finset (Finset V)} {p : V → E} {a : V}
    (hvertex : ({a} : Finset V) ∈ K) : p a ∈ geometricCarrier K p := by
  refine Set.mem_iUnion₂.2 ⟨{a}, hvertex, ?_⟩
  exact subset_convexHull ℝ _ ⟨a, by simp, rfl⟩

omit [FiniteDimensional ℝ E] in
/-- **The bridge from reduced simplicial acyclicity to actual singular
acyclicity of the geometric carrier.** -/
theorem singular_acyclicity_of_isReducedAcyclicUpTo {K : Finset (Finset V)} {p : V → E}
    (hK : FaceClosed K) (hgeom : IsGeometricRealization K p) {a : V}
    (hvertex : ({a} : Finset V) ∈ K) {N : ℕ} (hacy : IsReducedAcyclicUpTo ℝ K N) :
    (geometricCarrier K p).Nonempty ∧
      (1 ≤ N → IsIso (realSingularAugmentation
        (TopCat.of ↥(geometricCarrier K p)))) ∧
      ∀ k, k ≠ 0 → k + 1 ≤ N →
        IsZero ((realSingularHomology k).obj (TopCat.of ↥(geometricCarrier K p))) := by
  have hhomeo := geometricRealizationHomeomorph hgeom
  refine ⟨⟨p a, mem_geometricCarrier_of_vertex hvertex⟩, ?_, ?_⟩
  · intro hN
    have hbary : IsIso (realSingularAugmentation (barySpace K)) :=
      isIso_realSingularAugmentation_of_simplicial hK
        (isIso_augHomology_of_isReducedAcyclicAt_one hK hvertex (hacy 1 hN))
    have hnat := realSingularAugmentation_naturality
      (TopCat.ofHom (hhomeo.symm : C(↥(geometricCarrier K p), ↥(barycentricCarrier K))))
    have hmap : IsIso ((realSingularHomology 0).map
        (TopCat.ofHom (hhomeo.symm : C(↥(geometricCarrier K p), ↥(barycentricCarrier K))))) :=
      (realSingularHomologyIsoOfHomotopyEquiv hhomeo.symm.toHomotopyEquiv 0).isIso_hom
    rw [← hnat]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hmap hbary
  · intro k hk hkN
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hsrc : IsZero ((simplicialChains hK).homology (j + 1)) :=
      isZero_simplicialChains_homology hK j (hacy (j + 2) (by omega))
    have hiso := isIso_comparisonHomologyMap hK (j + 1)
    have hbary : IsZero ((realSingularHomology (j + 1)).obj (barySpace K)) :=
      IsZero.of_iso hsrc (@asIso _ _ _ _ (comparisonHomologyMap hK (j + 1)) hiso).symm
    exact IsZero.of_iso hbary
      (realSingularHomologyIsoOfHomotopyEquiv hhomeo.toHomotopyEquiv (j + 1)).symm

end AffineTverberg.Simplicial
