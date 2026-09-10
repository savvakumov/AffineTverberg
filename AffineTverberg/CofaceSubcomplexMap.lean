import AffineTverberg.CofaceRelativeChains

set_option linter.style.header false

/-!
# Inclusion of subcomplexes in the actual coface chain model

An inclusion induces the literal inclusion of coefficient chains at a fixed
face. When the two ambient complexes have exactly the same cofaces there,
this map is an isomorphism of chain complexes, not just an equality of ranks.
This is the local excision map used at adjacent dual blocks.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [LinearOrder V] {K J : Finset (Finset V)}

omit [Fintype V] in
theorem cofaceChains_mono_complex (h : K ⊆ J) (L : Finset V) (n : ℕ) :
    cofaceChains K L n ≤ cofaceChains J L n := by
  apply chains_mono
  intro t ht
  obtain ⟨htK, hLt⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨h htK, hLt⟩

/-- Inclusion leaves all actual coface coefficients unchanged. -/
def cofaceSubcomplexMap (hK : FaceClosed K) (hJ : FaceClosed J) (h : K ⊆ J) (L : Finset V) :
    cofaceComplex hK L ⟶ cofaceComplex hJ L :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (Submodule.inclusion (cofaceChains_mono_complex h L (n + 1))))
    (fun n => by
      rw [cofaceComplex_d, cofaceComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact Subtype.ext rfl)

theorem cofaceSubcomplexMap_apply (hK : FaceClosed K) (hJ : FaceClosed J)
    (h : K ⊆ J) (L : Finset V) (n : ℕ) (c : (cofaceComplex hK L).X n) :
    (((cofaceSubcomplexMap hK hJ h L).f n).hom c).val = c.val := rfl

theorem cofaceProjection_subcomplex (hK : FaceClosed K) (hJ : FaceClosed J)
    (h : K ⊆ J) (L : Finset V) :
    cofaceProjection hK L ≫ cofaceSubcomplexMap hK hJ h L =
      simplicialChainsInclusion hK hJ h ≫ cofaceProjection hJ L := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact Subtype.ext rfl

/-- If no coface is lost, inclusion is an actual chain isomorphism in all
degrees, including degree zero. -/
theorem isIso_cofaceSubcomplexMap (hK : FaceClosed K) (hJ : FaceClosed J)
    (h : K ⊆ J) (L : Finset V)
    (heq : K.filter (fun t => L ⊆ t) = J.filter (fun t => L ⊆ t)) :
    IsIso (cofaceSubcomplexMap hK hJ h L) := by
  have hcomp : ∀ n, IsIso ((cofaceSubcomplexMap hK hJ h L).f n) := by
    intro n
    have hchains : cofaceChains K L (n + 1) = cofaceChains J L (n + 1) :=
      congrArg (fun T => chains ℝ T (n + 1)) heq
    have hinj : Function.Injective ((cofaceSubcomplexMap hK hJ h L).f n).hom := by
      intro c d hcd
      have hv := congrArg (fun x : (cofaceComplex hJ L).X n => x.val) hcd
      exact Subtype.ext hv
    have hsurj : Function.Surjective ((cofaceSubcomplexMap hK hJ h L).f n).hom := by
      intro c
      exact ⟨⟨c.val, hchains.symm ▸ c.property⟩, Subtype.ext rfl⟩
    have : Mono ((cofaceSubcomplexMap hK hJ h L).f n) :=
      (ModuleCat.mono_iff_injective _).mpr hinj
    have : Epi ((cofaceSubcomplexMap hK hJ h L).f n) :=
      (ModuleCat.epi_iff_surjective _).mpr hsurj
    exact isIso_of_mono_of_epi _
  exact HomologicalComplex.Hom.isIso_of_components _

end AffineTverberg.Simplicial
