import AffineTverberg.SingularMayerVietoris
import Mathlib.Algebra.Homology.HomologySequenceLemmas

set_option linter.style.header false

/-!
# Naturality of the singular Mayer-Vietoris sequence

The Mayer-Vietoris long exact sequence of `AffineTverberg.SingularMayerVietoris`
is natural: a continuous map `f : X ⟶ Y` carrying an open cover `{A, B}` of `X`
into an open cover `{A', B'}` of `Y` induces a morphism between the two
sequences, commuting with all three maps, including the connecting
homomorphism.

The main ingredients are

* `CategoryTheory.ShortComplex.ShortExact.delta_naturality` — naturality of the
  connecting homomorphism of the homology sequence of a short exact sequence of
  homological complexes, which is Mathlib's
  `HomologicalComplex.HomologySequence.δ_naturality`;
* `AffChain.mvNat` — the morphism of Mayer-Vietoris short exact sequences of
  chain complexes induced by `f`;
* `AffChain.mvAlpha_naturality`, `AffChain.mvBeta_naturality`,
  `AffChain.mvDelta_naturality` — the resulting commuting squares.

Nothing is assumed; all maps are the actual induced maps.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex HomologySequence

namespace CategoryTheory.ShortComplex

variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)}

/-- **Naturality of the connecting homomorphism** of the homology sequence of a
short exact sequence of homological complexes. -/
theorem ShortExact.delta_naturality (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)
    (i j : ι) (hij : c.Rel i j) :
    h₁.δ i j hij ≫ HomologicalComplex.homologyMap φ.τ₁ j =
      HomologicalComplex.homologyMap φ.τ₃ i ≫ h₂.δ i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality φ h₁ h₂ i j hij

end CategoryTheory.ShortComplex

namespace AffineTverberg

namespace AffChain

variable {X Y : TopCat.{0}}

/-! ### Functoriality of the singular chain complex -/

lemma singChainsMap_comp {Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    singChainsMap (f ≫ g) = singChainsMap f ≫ singChainsMap g :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℝ)).obj
    (ModuleCat.of ℝ ℝ)).map_comp f g

lemma subMap_eq_singChainsMap {S T : Set X} (h : S ⊆ T) :
    subMap h = singChainsMap (subInclMap h) := rfl

/-! ### Restriction of a map to subspaces -/

/-- The restriction of a continuous map to subspaces. -/
def restrictMap (f : X ⟶ Y) {S : Set X} {T : Set Y}
    (h : ∀ x ∈ S, (ConcreteCategory.hom f) x ∈ T) : subSpace S ⟶ subSpace T :=
  TopCat.ofHom ⟨fun x => ⟨(ConcreteCategory.hom f) x, h x.1 x.2⟩, by fun_prop⟩

lemma restrictMap_comp_subIncl (f : X ⟶ Y) {S : Set X} {T : Set Y}
    (h : ∀ x ∈ S, (ConcreteCategory.hom f) x ∈ T) :
    restrictMap f h ≫ subIncl T = subIncl S ≫ f := rfl

lemma chainsInclusion_eq (S : Set X) : chainsInclusion S = singChainsMap (subIncl S) := rfl

/-- **The chain map of a subspace inclusion is natural.** -/
theorem chainsInclusion_naturality (f : X ⟶ Y) {S : Set X} {T : Set Y}
    (h : ∀ x ∈ S, (ConcreteCategory.hom f) x ∈ T) :
    singChainsMap (restrictMap f h) ≫ chainsInclusion T =
      chainsInclusion S ≫ singChainsMap f := by
  rw [chainsInclusion_eq, chainsInclusion_eq, ← singChainsMap_comp, ← singChainsMap_comp,
    restrictMap_comp_subIncl]

/-- Chains carried by `S` are sent to chains carried by `T`. -/
theorem map_mem_chainsIn (f : X ⟶ Y) {S : Set X} {T : Set Y}
    (h : ∀ x ∈ S, (ConcreteCategory.hom f) x ∈ T) (n : ℕ) {c : (singChains X).X n}
    (hc : c ∈ chainsIn S n) : ((singChainsMap f).f n).hom c ∈ chainsIn T n := by
  rw [← range_chainsInclusion S n] at hc
  obtain ⟨a, rfl⟩ := hc
  rw [← range_chainsInclusion T n]
  refine ⟨((singChainsMap (restrictMap f h)).f n).hom a, ?_⟩
  have hnat := congrArg (fun (g : singChains (subSpace S) ⟶ singChains Y) => (g.f n).hom a)
    (chainsInclusion_naturality f h)
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using hnat

/-! ### The induced map of small chains -/

variable (A B : Set X) (A' B' : Set Y)

variable {A B A' B'} in
theorem map_mem_smallChains (f : X ⟶ Y)
    (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') (n : ℕ)
    {c : (singChains X).X n} (hc : c ∈ smallChains (mvCover A B) n) :
    ((singChainsMap f).f n).hom c ∈ smallChains (mvCover A' B') n := by
  rw [smallChains_mvCover] at hc
  rw [smallChains_mvCover]
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hc
  rw [map_add]
  exact Submodule.add_mem_sup (map_mem_chainsIn f hA n ha) (map_mem_chainsIn f hB n hb)

/-- The map of small-chain complexes induced by a map of covered spaces. -/
def smallCxMap (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') :
    smallCx (mvCover A B) ⟶ smallCx (mvCover A' B') where
  f n := ModuleCat.ofHom (LinearMap.restrict ((singChainsMap f).f n).hom
    (fun _ hx => map_mem_smallChains f hA hB n hx))
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hc := congrArg (fun (g : (singChains X).X (j + 1) ⟶ (singChains Y).X j) =>
      g.hom x.1) ((singChainsMap f).comm (j + 1) j)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
    simp only [smallCx_d_eq, smallCxD]
    exact hc

theorem smallCxMap_comp_smallInc (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') :
    smallCxMap A B A' B' f hA hB ≫ smallInc (mvCover A' B') =
      smallInc (mvCover A B) ≫ singChainsMap f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-! ### The morphism of Mayer-Vietoris short exact sequences -/

variable {A B A' B'}

lemma inter_map (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') :
    ∀ x ∈ A ∩ B, (ConcreteCategory.hom f) x ∈ A' ∩ B' :=
  fun x hx => ⟨hA x hx.1, hB x hx.2⟩

/-- The map of degreewise direct sums induced by two chain maps. -/
def pairMap {C D C' D' : ChainComplex (ModuleCat.{0} ℝ) ℕ} (φ : C ⟶ C') (ψ : D ⟶ D') :
    pairCx C D ⟶ pairCx C' D' :=
  pairLift (pairFst C D ≫ φ) (pairSnd C D ≫ ψ)

@[simp] lemma pairMap_f_apply {C D C' D' : ChainComplex (ModuleCat.{0} ℝ) ℕ}
    (φ : C ⟶ C') (ψ : D ⟶ D') (n : ℕ) (a : C.X n) (b : D.X n) :
    ((pairMap φ ψ).f n).hom (a, b) = ((φ.f n).hom a, (ψ.f n).hom b) := rfl

/-- The pair of restricted maps of a map of covered spaces. -/
abbrev mvPairMap (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') :
    pairCx (singChains (subSpace A)) (singChains (subSpace B)) ⟶
      pairCx (singChains (subSpace A')) (singChains (subSpace B')) :=
  pairMap (singChainsMap (restrictMap f hA)) (singChainsMap (restrictMap f hB))

theorem mvF_naturality (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') :
    mvF A B ≫ mvPairMap f hA hB =
      singChainsMap (restrictMap f (inter_map f hA hB)) ≫ mvF A' B' := by
  have hleft : subMap (Set.inter_subset_left (s := A) (t := B)) ≫
      singChainsMap (restrictMap f hA) =
      singChainsMap (restrictMap f (inter_map f hA hB)) ≫
        subMap (Set.inter_subset_left (s := A') (t := B')) := by
    rw [subMap_eq_singChainsMap, subMap_eq_singChainsMap, ← singChainsMap_comp,
      ← singChainsMap_comp]
    rfl
  have hright : subMap (Set.inter_subset_right (s := A) (t := B)) ≫
      singChainsMap (restrictMap f hB) =
      singChainsMap (restrictMap f (inter_map f hA hB)) ≫
        subMap (Set.inter_subset_right (s := A') (t := B')) := by
    rw [subMap_eq_singChainsMap, subMap_eq_singChainsMap, ← singChainsMap_comp,
      ← singChainsMap_comp]
    rfl
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  have hl := congrArg (fun (g : singChains (subSpace (A ∩ B)) ⟶ singChains (subSpace A')) =>
    (g.f n).hom c) hleft
  have hr := congrArg (fun (g : singChains (subSpace (A ∩ B)) ⟶ singChains (subSpace B')) =>
    (g.f n).hom c) hright
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hl hr
  refine Prod.ext hl ?_
  change ((singChainsMap (restrictMap f hB)).f n).hom
      (-(((subMap (Set.inter_subset_right (s := A) (t := B))).f n).hom c)) = _
  rw [map_neg, hr]
  rfl

theorem mvG_naturality (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') :
    mvG A B ≫ smallCxMap A B A' B' f hA hB = mvPairMap f hA hB ≫ mvG A' B' := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨a, b⟩
  apply Subtype.ext
  have hA' := congrArg (fun (g : singChains (subSpace A) ⟶ singChains Y) => (g.f n).hom a)
    (chainsInclusion_naturality f hA)
  have hB' := congrArg (fun (g : singChains (subSpace B) ⟶ singChains Y) => (g.f n).hom b)
    (chainsInclusion_naturality f hB)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hA' hB'
  change ((singChainsMap f).f n).hom
      (((chainsInclusion A).f n).hom a + ((chainsInclusion B).f n).hom b) =
    ((chainsInclusion A').f n).hom (((singChainsMap (restrictMap f hA)).f n).hom a) +
      ((chainsInclusion B').f n).hom (((singChainsMap (restrictMap f hB)).f n).hom b)
  rw [map_add, hA', hB']

/-- **The morphism of Mayer-Vietoris short exact sequences of chain complexes**
induced by a map of covered spaces. -/
def mvNat (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') :
    mvShortComplex A B ⟶ mvShortComplex A' B' where
  τ₁ := singChainsMap (restrictMap f (inter_map f hA hB))
  τ₂ := mvPairMap f hA hB
  τ₃ := smallCxMap A B A' B' f hA hB
  comm₁₂ := (mvF_naturality f hA hB).symm
  comm₂₃ := (mvG_naturality f hA hB).symm

/-- **Naturality of the first Mayer-Vietoris map.** -/
theorem mvAlpha_naturality (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') (n : ℕ) :
    mvAlpha A B n ≫ HomologicalComplex.homologyMap (mvPairMap f hA hB) n =
      HomologicalComplex.homologyMap
          (singChainsMap (restrictMap f (inter_map f hA hB))) n ≫ mvAlpha A' B' n := by
  rw [mvAlpha_eq, mvAlpha_eq, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp, mvF_naturality f hA hB]

theorem pairDesc_naturality (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') :
    pairDesc (chainsInclusion A) (chainsInclusion B) ≫ singChainsMap f =
      mvPairMap f hA hB ≫ pairDesc (chainsInclusion A') (chainsInclusion B') := by
  rw [← mvG_comp_smallInc, ← mvG_comp_smallInc, Category.assoc,
    ← smallCxMap_comp_smallInc A B A' B' f hA hB, ← Category.assoc,
    mvG_naturality f hA hB, Category.assoc]

/-- **Naturality of the second Mayer-Vietoris map.** -/
theorem mvBeta_naturality (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') (n : ℕ) :
    mvBeta A B n ≫ HomologicalComplex.homologyMap (singChainsMap f) n =
      HomologicalComplex.homologyMap (mvPairMap f hA hB) n ≫ mvBeta A' B' n := by
  rw [mvBeta, mvBeta, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp, pairDesc_naturality f hA hB]

theorem mvSmallIso_naturality (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B')
    (hAo : IsOpen A) (hBo : IsOpen B) (hcov : ∀ x : X, x ∈ A ∨ x ∈ B)
    (hAo' : IsOpen A') (hBo' : IsOpen B') (hcov' : ∀ y : Y, y ∈ A' ∨ y ∈ B') (n : ℕ) :
    (mvSmallIso A B hAo hBo hcov n).inv ≫
        HomologicalComplex.homologyMap (smallCxMap A B A' B' f hA hB) n =
      HomologicalComplex.homologyMap (singChainsMap f) n ≫
        (mvSmallIso A' B' hAo' hBo' hcov' n).inv := by
  have hhom : HomologicalComplex.homologyMap (smallCxMap A B A' B' f hA hB) n ≫
      (mvSmallIso A' B' hAo' hBo' hcov' n).hom =
      (mvSmallIso A B hAo hBo hcov n).hom ≫
        HomologicalComplex.homologyMap (singChainsMap f) n := by
    rw [mvSmallIso_hom, mvSmallIso_hom, ← HomologicalComplex.homologyMap_comp,
      smallCxMap_comp_smallInc A B A' B' f hA hB, HomologicalComplex.homologyMap_comp]
    rfl
  symm
  refine (Iso.comp_inv_eq _).2 ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_
    (congrArg (fun g => (mvSmallIso A B hAo hBo hcov n).inv ≫ g) hhom.symm)
  exact (Iso.inv_hom_id_assoc _ _).symm

/-- **Naturality of the Mayer-Vietoris connecting homomorphism.** -/
theorem mvDelta_naturality (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B')
    (hAo : IsOpen A) (hBo : IsOpen B) (hcov : ∀ x : X, x ∈ A ∨ x ∈ B)
    (hAo' : IsOpen A') (hBo' : IsOpen B') (hcov' : ∀ y : Y, y ∈ A' ∨ y ∈ B') (n : ℕ) :
    mvDelta A B hAo hBo hcov n ≫ HomologicalComplex.homologyMap
        (singChainsMap (restrictMap f (inter_map f hA hB))) n =
      HomologicalComplex.homologyMap (singChainsMap f) (n + 1) ≫
        mvDelta A' B' hAo' hBo' hcov' n := by
  have hδ : (mvShortExact A B).δ (n + 1) n (by simp) ≫
        HomologicalComplex.homologyMap (mvNat f hA hB).τ₁ n =
      HomologicalComplex.homologyMap (mvNat f hA hB).τ₃ (n + 1) ≫
        (mvShortExact A' B').δ (n + 1) n (by simp) :=
    CategoryTheory.ShortComplex.ShortExact.delta_naturality (mvShortExact A B)
      (mvShortExact A' B') (mvNat f hA hB) (n + 1) n (by simp)
  have hiso' : (mvSmallIso A B hAo hBo hcov (n + 1)).inv ≫
        HomologicalComplex.homologyMap (mvNat f hA hB).τ₃ (n + 1) =
      HomologicalComplex.homologyMap (singChainsMap f) (n + 1) ≫
        (mvSmallIso A' B' hAo' hBo' hcov' (n + 1)).inv :=
    mvSmallIso_naturality f hA hB hAo hBo hcov hAo' hBo' hcov' (n + 1)
  have key : ((mvSmallIso A B hAo hBo hcov (n + 1)).inv ≫
        (mvShortExact A B).δ (n + 1) n (by simp)) ≫
        HomologicalComplex.homologyMap (mvNat f hA hB).τ₁ n =
      HomologicalComplex.homologyMap (singChainsMap f) (n + 1) ≫
        ((mvSmallIso A' B' hAo' hBo' hcov' (n + 1)).inv ≫
          (mvShortExact A' B').δ (n + 1) n (by simp)) := by
    rw [Category.assoc, hδ, reassoc_of% hiso']
  exact key

end AffChain

end AffineTverberg
