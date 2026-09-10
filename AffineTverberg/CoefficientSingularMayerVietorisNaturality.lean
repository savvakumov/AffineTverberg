import AffineTverberg.CoefficientSingularMayerVietoris
import AffineTverberg.SingularMayerVietorisNaturality

set_option linter.style.header false

/-!
# Naturality of arbitrary-field singular Mayer–Vietoris

Maps of covered spaces induce maps of the actual short exact chain sequences.
The connecting maps commute by the homology-sequence naturality theorem.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex HomologySequence AffineTverberg.AffChain

namespace AffineTverberg.Coefficients.AffChain

variable (𝕜 : Type) [Field 𝕜]
variable {X Y : TopCat.{0}}

lemma singChainsMap_comp {Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    singChainsMap 𝕜 (f ≫ g) = singChainsMap 𝕜 f ≫ singChainsMap 𝕜 g :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} 𝕜)).obj
    (ModuleCat.of 𝕜 𝕜)).map_comp f g

lemma subMap_eq_singChainsMap {S T : Set X} (h : S ⊆ T) :
    subMap 𝕜 h = singChainsMap 𝕜 (subInclMap h) := rfl

lemma chainsInclusion_eq (S : Set X) : chainsInclusion 𝕜 S = singChainsMap 𝕜 (subIncl S) := rfl

/-- **The chain map of a subspace inclusion is natural.** -/
theorem chainsInclusion_naturality (f : X ⟶ Y) {S : Set X} {T : Set Y}
    (h : ∀ x ∈ S, (ConcreteCategory.hom f) x ∈ T) :
    singChainsMap 𝕜 (restrictMap f h) ≫ chainsInclusion 𝕜 T =
      chainsInclusion 𝕜 S ≫ singChainsMap 𝕜 f := by
  rw [chainsInclusion_eq 𝕜, chainsInclusion_eq 𝕜, ← singChainsMap_comp 𝕜, ← singChainsMap_comp 𝕜,
    restrictMap_comp_subIncl]

/-- Chains carried by `S` are sent to chains carried by `T`. -/
theorem map_mem_chainsIn (f : X ⟶ Y) {S : Set X} {T : Set Y}
    (h : ∀ x ∈ S, (ConcreteCategory.hom f) x ∈ T) (n : ℕ) {c : (singChains 𝕜 X).X n}
    (hc : c ∈ chainsIn 𝕜 S n) : ((singChainsMap 𝕜 f).f n).hom c ∈ chainsIn 𝕜 T n := by
  rw [← range_chainsInclusion 𝕜 S n] at hc
  obtain ⟨a, rfl⟩ := hc
  rw [← range_chainsInclusion 𝕜 T n]
  refine ⟨((singChainsMap 𝕜 (restrictMap f h)).f n).hom a, ?_⟩
  have hnat := congrArg (fun (g : singChains 𝕜 (subSpace S) ⟶ singChains 𝕜 Y) => (g.f n).hom a)
    (chainsInclusion_naturality 𝕜 f h)
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using hnat

/-! ### The induced map of small chains -/

variable (A B : Set X) (A' B' : Set Y)

variable {A B A' B'} in
theorem map_mem_smallChains (f : X ⟶ Y)
    (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') (n : ℕ)
    {c : (singChains 𝕜 X).X n} (hc : c ∈ smallChains 𝕜 (mvCover A B) n) :
    ((singChainsMap 𝕜 f).f n).hom c ∈ smallChains 𝕜 (mvCover A' B') n := by
  rw [smallChains_mvCover 𝕜] at hc
  rw [smallChains_mvCover 𝕜]
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hc
  rw [map_add]
  exact Submodule.add_mem_sup (map_mem_chainsIn 𝕜 f hA n ha) (map_mem_chainsIn 𝕜 f hB n hb)

/-- The map of small-chain complexes induced by a map of covered spaces. -/
def smallCxMap (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') :
    smallCx 𝕜 (mvCover A B) ⟶ smallCx 𝕜 (mvCover A' B') where
  f n := ModuleCat.ofHom (LinearMap.restrict ((singChainsMap 𝕜 f).f n).hom
    (fun _ hx => map_mem_smallChains 𝕜 f hA hB n hx))
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hc := congrArg (fun (g : (singChains 𝕜 X).X (j + 1) ⟶ (singChains 𝕜 Y).X j) =>
      g.hom x.1) ((singChainsMap 𝕜 f).comm (j + 1) j)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
    simp only [smallCx_d_eq 𝕜, smallCxD]
    exact hc

theorem smallCxMap_comp_smallInc (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') :
    smallCxMap 𝕜 A B A' B' f hA hB ≫ smallInc 𝕜 (mvCover A' B') =
      smallInc 𝕜 (mvCover A B) ≫ singChainsMap 𝕜 f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-! ### The morphism of Mayer-Vietoris short exact sequences -/

variable {A B A' B'}

/-- The map of degreewise direct sums induced by two chain maps. -/
def pairMap {C D C' D' : ChainComplex (ModuleCat.{0} 𝕜) ℕ} (φ : C ⟶ C') (ψ : D ⟶ D') :
    pairCx 𝕜 C D ⟶ pairCx 𝕜 C' D' :=
  pairLift 𝕜 (pairFst 𝕜 C D ≫ φ) (pairSnd 𝕜 C D ≫ ψ)

@[simp] lemma pairMap_f_apply {C D C' D' : ChainComplex (ModuleCat.{0} 𝕜) ℕ}
    (φ : C ⟶ C') (ψ : D ⟶ D') (n : ℕ) (a : C.X n) (b : D.X n) :
    ((pairMap 𝕜 φ ψ).f n).hom (a, b) = ((φ.f n).hom a, (ψ.f n).hom b) := rfl

/-- The pair of restricted maps of a map of covered spaces. -/
abbrev mvPairMap (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') :
    pairCx 𝕜 (singChains 𝕜 (subSpace A)) (singChains 𝕜 (subSpace B)) ⟶
      pairCx 𝕜 (singChains 𝕜 (subSpace A')) (singChains 𝕜 (subSpace B')) :=
  pairMap 𝕜 (singChainsMap 𝕜 (restrictMap f hA)) (singChainsMap 𝕜 (restrictMap f hB))

theorem mvF_naturality (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') :
    mvF 𝕜 A B ≫ mvPairMap 𝕜 f hA hB =
      singChainsMap 𝕜 (restrictMap f (inter_map f hA hB)) ≫ mvF 𝕜 A' B' := by
  have hleft : subMap 𝕜 (Set.inter_subset_left (s := A) (t := B)) ≫
      singChainsMap 𝕜 (restrictMap f hA) =
      singChainsMap 𝕜 (restrictMap f (inter_map f hA hB)) ≫
        subMap 𝕜 (Set.inter_subset_left (s := A') (t := B')) := by
    rw [subMap_eq_singChainsMap 𝕜, subMap_eq_singChainsMap 𝕜, ← singChainsMap_comp 𝕜,
      ← singChainsMap_comp 𝕜]
    rfl
  have hright : subMap 𝕜 (Set.inter_subset_right (s := A) (t := B)) ≫
      singChainsMap 𝕜 (restrictMap f hB) =
      singChainsMap 𝕜 (restrictMap f (inter_map f hA hB)) ≫
        subMap 𝕜 (Set.inter_subset_right (s := A') (t := B')) := by
    rw [subMap_eq_singChainsMap 𝕜, subMap_eq_singChainsMap 𝕜, ← singChainsMap_comp 𝕜,
      ← singChainsMap_comp 𝕜]
    rfl
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  have hl := congrArg (fun (g : singChains 𝕜 (subSpace (A ∩ B)) ⟶ singChains 𝕜 (subSpace A')) =>
    (g.f n).hom c) hleft
  have hr := congrArg (fun (g : singChains 𝕜 (subSpace (A ∩ B)) ⟶ singChains 𝕜 (subSpace B')) =>
    (g.f n).hom c) hright
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hl hr
  refine Prod.ext hl ?_
  change ((singChainsMap 𝕜 (restrictMap f hB)).f n).hom
      (-(((subMap 𝕜 (Set.inter_subset_right (s := A) (t := B))).f n).hom c)) = _
  rw [map_neg, hr]
  rfl

theorem mvG_naturality (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') :
    mvG 𝕜 A B ≫ smallCxMap 𝕜 A B A' B' f hA hB = mvPairMap 𝕜 f hA hB ≫ mvG 𝕜 A' B' := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨a, b⟩
  apply Subtype.ext
  have hA' := congrArg (fun (g : singChains 𝕜 (subSpace A) ⟶ singChains 𝕜 Y) => (g.f n).hom a)
    (chainsInclusion_naturality 𝕜 f hA)
  have hB' := congrArg (fun (g : singChains 𝕜 (subSpace B) ⟶ singChains 𝕜 Y) => (g.f n).hom b)
    (chainsInclusion_naturality 𝕜 f hB)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hA' hB'
  change ((singChainsMap 𝕜 f).f n).hom
      (((chainsInclusion 𝕜 A).f n).hom a + ((chainsInclusion 𝕜 B).f n).hom b) =
    ((chainsInclusion 𝕜 A').f n).hom (((singChainsMap 𝕜 (restrictMap f hA)).f n).hom a) +
      ((chainsInclusion 𝕜 B').f n).hom (((singChainsMap 𝕜 (restrictMap f hB)).f n).hom b)
  rw [map_add, hA', hB']

/-- **The morphism of Mayer-Vietoris short exact sequences of chain complexes**
induced by a map of covered spaces. -/
def mvNat (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') :
    mvShortComplex 𝕜 A B ⟶ mvShortComplex 𝕜 A' B' where
  τ₁ := singChainsMap 𝕜 (restrictMap f (inter_map f hA hB))
  τ₂ := mvPairMap 𝕜 f hA hB
  τ₃ := smallCxMap 𝕜 A B A' B' f hA hB
  comm₁₂ := (mvF_naturality 𝕜 f hA hB).symm
  comm₂₃ := (mvG_naturality 𝕜 f hA hB).symm

/-- **Naturality of the first Mayer-Vietoris map.** -/
theorem mvAlpha_naturality (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') (n : ℕ) :
    mvAlpha 𝕜 A B n ≫ HomologicalComplex.homologyMap (mvPairMap 𝕜 f hA hB) n =
      HomologicalComplex.homologyMap
          (singChainsMap 𝕜 (restrictMap f (inter_map f hA hB))) n ≫ mvAlpha 𝕜 A' B' n := by
  rw [mvAlpha_eq 𝕜, mvAlpha_eq 𝕜, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp, mvF_naturality 𝕜 f hA hB]

theorem pairDesc_naturality (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') :
    pairDesc 𝕜 (chainsInclusion 𝕜 A) (chainsInclusion 𝕜 B) ≫ singChainsMap 𝕜 f =
      mvPairMap 𝕜 f hA hB ≫ pairDesc 𝕜 (chainsInclusion 𝕜 A') (chainsInclusion 𝕜 B') := by
  rw [← mvG_comp_smallInc 𝕜, ← mvG_comp_smallInc 𝕜, Category.assoc,
    ← smallCxMap_comp_smallInc 𝕜 A B A' B' f hA hB, ← Category.assoc,
    mvG_naturality 𝕜 f hA hB, Category.assoc]

/-- **Naturality of the second Mayer-Vietoris map.** -/
theorem mvBeta_naturality (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B') (n : ℕ) :
    mvBeta 𝕜 A B n ≫ HomologicalComplex.homologyMap (singChainsMap 𝕜 f) n =
      HomologicalComplex.homologyMap (mvPairMap 𝕜 f hA hB) n ≫ mvBeta 𝕜 A' B' n := by
  rw [mvBeta, mvBeta, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp, pairDesc_naturality 𝕜 f hA hB]

theorem mvSmallIso_naturality (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B')
    (hAo : IsOpen A) (hBo : IsOpen B) (hcov : ∀ x : X, x ∈ A ∨ x ∈ B)
    (hAo' : IsOpen A') (hBo' : IsOpen B') (hcov' : ∀ y : Y, y ∈ A' ∨ y ∈ B') (n : ℕ) :
    (mvSmallIso 𝕜 A B hAo hBo hcov n).inv ≫
        HomologicalComplex.homologyMap (smallCxMap 𝕜 A B A' B' f hA hB) n =
      HomologicalComplex.homologyMap (singChainsMap 𝕜 f) n ≫
        (mvSmallIso 𝕜 A' B' hAo' hBo' hcov' n).inv := by
  have hhom : HomologicalComplex.homologyMap (smallCxMap 𝕜 A B A' B' f hA hB) n ≫
      (mvSmallIso 𝕜 A' B' hAo' hBo' hcov' n).hom =
      (mvSmallIso 𝕜 A B hAo hBo hcov n).hom ≫
        HomologicalComplex.homologyMap (singChainsMap 𝕜 f) n := by
    rw [mvSmallIso_hom 𝕜, mvSmallIso_hom 𝕜, ← HomologicalComplex.homologyMap_comp,
      smallCxMap_comp_smallInc 𝕜 A B A' B' f hA hB, HomologicalComplex.homologyMap_comp]
    rfl
  symm
  refine (Iso.comp_inv_eq _).2 ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_
    (congrArg (fun g => (mvSmallIso 𝕜 A B hAo hBo hcov n).inv ≫ g) hhom.symm)
  exact (Iso.inv_hom_id_assoc _ _).symm

/-- **Naturality of the Mayer-Vietoris connecting homomorphism.** -/
theorem mvDelta_naturality (f : X ⟶ Y) (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B')
    (hAo : IsOpen A) (hBo : IsOpen B) (hcov : ∀ x : X, x ∈ A ∨ x ∈ B)
    (hAo' : IsOpen A') (hBo' : IsOpen B') (hcov' : ∀ y : Y, y ∈ A' ∨ y ∈ B') (n : ℕ) :
    mvDelta 𝕜 A B hAo hBo hcov n ≫ HomologicalComplex.homologyMap
        (singChainsMap 𝕜 (restrictMap f (inter_map f hA hB))) n =
      HomologicalComplex.homologyMap (singChainsMap 𝕜 f) (n + 1) ≫
        mvDelta 𝕜 A' B' hAo' hBo' hcov' n := by
  have hδ : (mvShortExact 𝕜 A B).δ (n + 1) n (by simp) ≫
        HomologicalComplex.homologyMap (mvNat 𝕜 f hA hB).τ₁ n =
      HomologicalComplex.homologyMap (mvNat 𝕜 f hA hB).τ₃ (n + 1) ≫
        (mvShortExact 𝕜 A' B').δ (n + 1) n (by simp) :=
    CategoryTheory.ShortComplex.ShortExact.delta_naturality (mvShortExact 𝕜 A B)
      (mvShortExact 𝕜 A' B') (mvNat 𝕜 f hA hB) (n + 1) n (by simp)
  have hiso' : (mvSmallIso 𝕜 A B hAo hBo hcov (n + 1)).inv ≫
        HomologicalComplex.homologyMap (mvNat 𝕜 f hA hB).τ₃ (n + 1) =
      HomologicalComplex.homologyMap (singChainsMap 𝕜 f) (n + 1) ≫
        (mvSmallIso 𝕜 A' B' hAo' hBo' hcov' (n + 1)).inv :=
    mvSmallIso_naturality 𝕜 f hA hB hAo hBo hcov hAo' hBo' hcov' (n + 1)
  have key : ((mvSmallIso 𝕜 A B hAo hBo hcov (n + 1)).inv ≫
        (mvShortExact 𝕜 A B).δ (n + 1) n (by simp)) ≫
        HomologicalComplex.homologyMap (mvNat 𝕜 f hA hB).τ₁ n =
      HomologicalComplex.homologyMap (singChainsMap 𝕜 f) (n + 1) ≫
        ((mvSmallIso 𝕜 A' B' hAo' hBo' hcov' (n + 1)).inv ≫
          (mvShortExact 𝕜 A' B').δ (n + 1) n (by simp)) := by
    rw [Category.assoc, hδ, reassoc_of% hiso']
  exact key

end AffineTverberg.Coefficients.AffChain

