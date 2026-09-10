import AffineTverberg.SmallChainExcision

set_option linter.style.header false

/-!
# Excision for actual relative singular homology

For an open cover `A ∪ B = X`, the inclusion of pairs `(A, A ∩ B) → (X, B)`
induces a quasi-isomorphism of the actual relative singular complexes, hence
isomorphisms in all homological degrees. The source is the literal subspace
pair, not an assumed or replacement homology theory.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.AffChain

variable {X : TopCat.{0}} (A B : Set X)

/-- The intersection, viewed inside the left-hand subspace. -/
def intersectionInLeft : Set ↥(subSpace A) := Subtype.val ⁻¹' B

/-- Flatten the double subtype of the intersection. -/
def intersectionInLeftHomeomorph : ↥(intersectionInLeft A B) ≃ₜ ↥(subSpace (A ∩ B)) where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def intersectionFlattenChains :
    singChains (subSpace (intersectionInLeft A B)) ⟶ singChains (subSpace (A ∩ B)) :=
  singChainsMap (TopCat.ofHom (intersectionInLeftHomeomorph A B).toHomotopyEquiv.toFun)

theorem intersectionFlattenChains_comp :
    intersectionFlattenChains A B ≫ subMap (Set.inter_subset_left (s := A) (t := B)) =
      chainsInclusion (intersectionInLeft A B) := by
  rw [intersectionFlattenChains, subMap_eq_singChainsMap, ← singChainsMap_comp]
  rfl

/-- The relative complex with the intersection in its flat presentation. -/
def flatRelativeShortComplex : ShortComplex (ChainComplex (ModuleCat.{0} ℝ) ℕ) :=
  ShortComplex.mk (subMap (Set.inter_subset_left (s := A) (t := B)))
    (cokernel.π _) (cokernel.condition _)

theorem flatRelativeShortExact : (flatRelativeShortComplex A B).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := HomologicalComplex.mono_of_mono_f _ (fun n =>
    (ModuleCat.mono_iff_injective _).mpr (subMap_injective _ n))
  epi_g := coequalizer.π_epi

/-- The canonical map from the literal relative pair to the flat presentation. -/
def flattenRelativeMap :
    relCx (intersectionInLeft A B) ⟶
      cokernel (subMap (Set.inter_subset_left (s := A) (t := B))) :=
  cokernel.map _ _ (intersectionFlattenChains A B) (𝟙 _) (by
    rw [Category.comp_id]
    exact (intersectionFlattenChains_comp A B).symm)

theorem flattenRelativeMap_proj :
    relProj (intersectionInLeft A B) ≫ flattenRelativeMap A B =
      cokernel.π (subMap (Set.inter_subset_left (s := A) (t := B))) := by
  exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)

def flattenRelativeShortComplexMap :
    relShortComplex (intersectionInLeft A B) ⟶ flatRelativeShortComplex A B where
  τ₁ := intersectionFlattenChains A B
  τ₂ := 𝟙 _
  τ₃ := flattenRelativeMap A B
  comm₁₂ := by
    change intersectionFlattenChains A B ≫ subMap Set.inter_subset_left =
      chainsInclusion (intersectionInLeft A B) ≫ 𝟙 _
    rw [Category.comp_id]
    exact intersectionFlattenChains_comp A B
  comm₂₃ := by
    change 𝟙 _ ≫ cokernel.π (subMap (Set.inter_subset_left (s := A) (t := B))) =
      relProj (intersectionInLeft A B) ≫ flattenRelativeMap A B
    rw [Category.id_comp]
    exact (flattenRelativeMap_proj A B).symm

theorem quasiIso_flattenRelativeMap : QuasiIso (flattenRelativeMap A B) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (flattenRelativeShortComplexMap A B)
    (relShortExact (intersectionInLeft A B)) (flatRelativeShortExact A B)
    (Simplicial.quasiIso_singChainsMap_of_homotopyEquiv
      (intersectionInLeftHomeomorph A B).toHomotopyEquiv)
    (by change QuasiIso (𝟙 (singChains (subSpace A))); infer_instance)

theorem flatExcisionMap_proj :
    cokernel.π (subMap (Set.inter_subset_left (s := A) (t := B))) ≫ flatExcisionMap A B =
      chainsInclusion A ≫ relProj B := by
  change cokernel.π _ ≫ smallRelativeMap A B ≫ relativeSmallInc A B = _
  have hπ : cokernel.π (subMap (Set.inter_subset_left (s := A) (t := B))) ≫
      smallRelativeMap A B = smallLeft A B ≫ cokernel.π (smallRight A B) :=
    cokernel.π_desc _ _ _
  rw [← Category.assoc, hπ, Category.assoc, relativeSmallInc_proj,
    ← Category.assoc, toSmallCx_comp_smallInc]

/-- The actual chain map induced by the inclusion of pairs. -/
def relativeExcisionMap : relCx (intersectionInLeft A B) ⟶ relCx B :=
  relativeMap (subIncl A) (fun _ hx => hx)

theorem relativeExcisionMap_factorization :
    relativeExcisionMap A B = flattenRelativeMap A B ≫ flatExcisionMap A B := by
  apply (cancel_epi (cokernel.π (chainsInclusion (intersectionInLeft A B)))).mp
  change relProj (intersectionInLeft A B) ≫ relativeExcisionMap A B =
    relProj (intersectionInLeft A B) ≫ flattenRelativeMap A B ≫ flatExcisionMap A B
  have hπ : relProj (intersectionInLeft A B) ≫ relativeExcisionMap A B =
      chainsInclusion A ≫ relProj B := relativeMap_proj _ _
  rw [hπ, ← Category.assoc, flattenRelativeMap_proj, flatExcisionMap_proj]

/-- **Excision:** the actual inclusion of pairs is a quasi-isomorphism. -/
theorem quasiIso_relativeExcisionMap (hA : IsOpen A) (hB : IsOpen B)
    (hcov : ∀ x : X, x ∈ A ∨ x ∈ B) : QuasiIso (relativeExcisionMap A B) := by
  rw [relativeExcisionMap_factorization]
  have := quasiIso_flattenRelativeMap A B
  have := quasiIso_flatExcisionMap A B hA hB hcov
  infer_instance

/-- The genuine relative singular homology excision isomorphism in every degree. -/
def relativeExcisionHomologyIso (hA : IsOpen A) (hB : IsOpen B)
    (hcov : ∀ x : X, x ∈ A ∨ x ∈ B) (k : ℕ) :
    relativeHomology (intersectionInLeft A B) k ≅ relativeHomology B k := by
  have := quasiIso_relativeExcisionMap A B hA hB hcov
  exact asIso (HomologicalComplex.homologyMap (relativeExcisionMap A B) k)

variable {A B}

/-- Relative homology supported on a closed set can be computed in any open
neighborhood of that set. This is the geometric excision form used in local
duality, with the actual neighborhood-inclusion map. -/
theorem quasiIso_relativeNeighborhoodMap {S U : Set X}
    (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U) :
    QuasiIso (relativeExcisionMap U Sᶜ) := by
  apply quasiIso_relativeExcisionMap U Sᶜ hU hS.isOpen_compl
  intro x
  by_cases hx : x ∈ S
  · exact Or.inl (hSU hx)
  · exact Or.inr hx

/-- The excision isomorphism for an arbitrary open neighborhood of a closed set. -/
def relativeNeighborhoodHomologyIso {S U : Set X}
    (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U) (k : ℕ) :
    relativeHomology (intersectionInLeft U Sᶜ) k ≅ relativeHomology Sᶜ k := by
  have := quasiIso_relativeNeighborhoodMap hS hU hSU
  exact asIso (HomologicalComplex.homologyMap (relativeExcisionMap U Sᶜ) k)

/-- Local relative homology is unchanged on passing to any open neighborhood
of the puncture. No manifold or local-flatness hypothesis is used. -/
def puncturedRelativeHomologyIso [T1Space X] {U : Set X} (p : X)
    (hU : IsOpen U) (hp : p ∈ U) (k : ℕ) :
    relativeHomology (intersectionInLeft U ({p} : Set X)ᶜ) k ≅
      relativeHomology ({p} : Set X)ᶜ k :=
  relativeNeighborhoodHomologyIso isClosed_singleton hU (Set.singleton_subset_iff.mpr hp) k

end AffineTverberg.AffChain
