import AffineTverberg.BarycentricLink
import AffineTverberg.BarycentricMayerVietoris
import AffineTverberg.SingularHomology
import AffineTverberg.SimplicialToSingular

set_option linter.style.header false

/-!
# Identifying the three terms of the Mayer-Vietoris cover along a maximal face

For a nonempty maximal face `s` of a finite face-closed family `K` the sets
`punctured K s` and `openStar K s` form an open cover of the realization of `K`
(`AffineTverberg.Simplicial.faceMv_exact_space` and companions). This file
identifies the singular homology of the three terms of the associated
Mayer-Vietoris sequence with the singular homology of realizations of
subfamilies:

* `puncturedHomologyIso` — the punctured realization has the homology of the
  realization of `K.erase s`;
* `linkHomologyIso` — the intersection has the homology of the realization of
  the boundary family `boundaryFamily s` of `s`;
* the open star is contractible (`contractibleSpace_openStar`), so its homology
  is that of a point.

Moreover the identifications are *compatible with the inclusions*: the square

```
   H(link)      ⟶   H(punctured)
     ≅                  ≅
   H(|∂s|)      ⟶   H(|K \ s|)
```

commutes on the nose (`homologyMap_linkToPunctured_square`), because the radial
retraction used for the intersection is literally the restriction of the one
used for the punctured realization. This is the compatibility needed to feed
the Mayer-Vietoris sequence into an induction over subfamilies.

Nothing is assumed: all maps are the actual inclusions and the actual radial
retraction, and the homotopy invariance is Mathlib's homotopy invariance of
singular homology (`realSingularHomologyIsoOfHomotopyEquiv`).
-/

noncomputable section

open CategoryTheory AffineTverberg.AffChain

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [DecidableEq V] {K : Finset (Finset V)} {s : Finset V}

/-! ### The homology of the Mayer-Vietoris terms is the homology of `singChains` -/

theorem realSingularHomology_obj_eq (X : TopCat.{0}) (n : ℕ) :
    (realSingularHomology n).obj X = (singChains X).homology n := rfl

/-! ### The boundary of a maximal face is a subfamily of the deletion -/

omit [Fintype V] in
theorem boundaryFamily_subset_erase (hK : FaceClosed K) (hsK : s ∈ K) :
    boundaryFamily s ⊆ K.erase s := by
  intro u hu
  obtain ⟨husub, hune⟩ := mem_boundaryFamily.1 hu
  exact Finset.mem_erase.2 ⟨hune, hK s hsK u husub⟩

/-- The inclusion of the realization of the boundary of `s` into the realization
of `K.erase s`. -/
def boundaryInclusion (hK : FaceClosed K) (hsK : s ∈ K) :
    C(↥(barycentricCarrier (boundaryFamily s)), ↥(barycentricCarrier (K.erase s))) where
  toFun y := ⟨y.val, barycentricCarrier_mono (boundaryFamily_subset_erase hK hsK) y.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-! ### The strict compatibility of the two radial retractions -/

/-- The radial retraction of the punctured realization restricts to the radial
retraction of the intersection: the square of continuous maps

```
   link  ⟶  punctured
    ↓            ↓
   |∂s|  ⟶  |K \ s|
```

commutes on the nose. -/
theorem boundaryInclusion_comp_linkRetract (hK : FaceClosed K) (hs : s.Nonempty) (hsK : s ∈ K)
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) :
    (boundaryInclusion hK hsK).comp (linkRetract hs hmax) =
      (puncturedRetract hK hs).comp (linkToPunctured K s) := rfl

/-! ### The homology identifications -/

/-- **The punctured realization has the singular homology of the realization of
`K.erase s`.** -/
def puncturedHomologyIso (hK : FaceClosed K) (hs : s.Nonempty)
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) (n : ℕ) :
    (realSingularHomology n).obj (TopCat.of ↥(punctured K s)) ≅
      (realSingularHomology n).obj (barySpace (K.erase s)) :=
  realSingularHomologyIsoOfHomotopyEquiv (puncturedHomotopyEquiv hK hs hmax) n

lemma puncturedHomologyIso_hom (hK : FaceClosed K) (hs : s.Nonempty)
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) (n : ℕ) :
    (puncturedHomologyIso hK hs hmax n).hom =
      (realSingularHomology n).map (TopCat.ofHom (puncturedRetract hK hs)) := rfl

/-- **The intersection of the two members of the cover has the singular homology
of the realization of the boundary of `s`.** -/
def linkHomologyIso (hs : s.Nonempty) (hsK : s ∈ K) (hmax : ∀ t ∈ K, s ⊆ t → t = s) (n : ℕ) :
    (realSingularHomology n).obj (TopCat.of ↥(linkSet K s)) ≅
      (realSingularHomology n).obj (barySpace (boundaryFamily s)) :=
  realSingularHomologyIsoOfHomotopyEquiv (linkHomotopyEquiv hs hsK hmax) n

lemma linkHomologyIso_hom (hs : s.Nonempty) (hsK : s ∈ K) (hmax : ∀ t ∈ K, s ⊆ t → t = s)
    (n : ℕ) :
    (linkHomologyIso hs hsK hmax n).hom =
      (realSingularHomology n).map (TopCat.ofHom (linkRetract hs hmax)) := rfl

/-! ### Compatibility of the identifications with the inclusions -/

/-- **The identifications of the intersection and of the punctured realization
are compatible with the inclusions.** Both composites are induced by the radial
retraction of the intersection. -/
theorem homologyMap_linkToPunctured_square (hK : FaceClosed K) (hs : s.Nonempty) (hsK : s ∈ K)
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) (n : ℕ) :
    (realSingularHomology n).map (TopCat.ofHom (linkToPunctured K s)) ≫
        (puncturedHomologyIso hK hs hmax n).hom =
      (linkHomologyIso hs hsK hmax n).hom ≫
        (realSingularHomology n).map (TopCat.ofHom (boundaryInclusion hK hsK)) := by
  refine (Functor.map_comp (realSingularHomology n) (TopCat.ofHom (linkToPunctured K s))
    (TopCat.ofHom (puncturedRetract hK hs))).symm.trans ?_
  exact Eq.trans rfl (Functor.map_comp (realSingularHomology n)
    (TopCat.ofHom (linkRetract hs hmax)) (TopCat.ofHom (boundaryInclusion hK hsK)))

/-- The chain-level Mayer-Vietoris map out of the intersection is induced by the
actual inclusion of the intersection into the punctured realization: on homology
it is the map identified above. -/
theorem homologyMap_subMap_inter_left (n : ℕ) :
    HomologicalComplex.homologyMap
        (subMap (X := realSpace K)
          (Set.inter_subset_left (s := punctured K s) (t := openStar K s))) n =
      (realSingularHomology n).map (TopCat.ofHom (linkToPunctured K s)) := rfl

/-! ### The open star -/

omit [DecidableEq V] in
/-- The open star of a nonempty face of `K` is contractible, hence its singular
homology vanishes in positive degrees and its augmentation is invertible. This
is the third term of the Mayer-Vietoris cover. -/
theorem openStar_homology (hs : s.Nonempty) (hsK : s ∈ K) :
    IsIso (realSingularAugmentation (TopCat.of ↥(openStar K s))) ∧
      ∀ k, k ≠ 0 → Subsingleton ((realSingularHomology k).obj (TopCat.of ↥(openStar K s))) :=
  openStar_singularAcyclic hs hsK

end AffineTverberg.Simplicial
