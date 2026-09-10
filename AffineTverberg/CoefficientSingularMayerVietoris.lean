import AffineTverberg.CoefficientSingularChainBasis
import AffineTverberg.SingularMayerVietoris

set_option linter.style.header false

/-!
# Singular Mayer–Vietoris over arbitrary fields

The sequence is formed from the actual inclusion maps of subspaces and the
actual complex of small singular chains. Degreewise exactness follows from the
free basis, and the proved small-chain quasi-isomorphism identifies its long
exact homology sequence with actual singular homology of the open cover.
-/

noncomputable section

open CategoryTheory Limits Simplicial AffineTverberg.AffChain

namespace AffineTverberg.Coefficients.AffChain

variable (𝕜 : Type) [Field 𝕜]
variable {X : TopCat.{0}}

/-- The chain map induced by an inclusion of subspaces. -/
def subMap {S T : Set X} (h : S ⊆ T) : singChains 𝕜 (subSpace S) ⟶ singChains 𝕜 (subSpace T) :=
  SSet.chainComplexMap (TopCat.toSSet.map (subInclMap h)) (ModuleCat.of 𝕜 𝕜)

lemma ιs_subMap {S T : Set X} (h : S ⊆ T) {n : ℕ} (x : singIdx (subSpace S) n) :
    ιs 𝕜 x ≫ (subMap 𝕜 h).f n =
      ιs 𝕜 ((TopCat.toSSet.map (subInclMap h)).app (Opposite.op ⦋n⦌) x) := by
  rw [subMap, SSet.ι_chainComplexMap_f]

/-- Compatibility of the induced maps with the inclusions into the ambient
space. -/
theorem subMap_comp_chainsInclusion {S T : Set X} (h : S ⊆ T) :
    subMap 𝕜 h ≫ chainsInclusion 𝕜 T = chainsInclusion 𝕜 S := by
  apply HomologicalComplex.hom_ext
  intro n
  refine singChains_hom_ext 𝕜 fun x => ?_
  rw [HomologicalComplex.comp_f, ← Category.assoc, ιs_subMap 𝕜, ιs_chainsInclusion 𝕜,
    ιs_chainsInclusion 𝕜]
  congr 1

lemma subMap_injective {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    Function.Injective ((subMap 𝕜 h).f n).hom := by
  intro a b hab
  apply chainsInclusion_injective 𝕜 S n
  have hA := congrArg (fun (g : singChains 𝕜 (subSpace S) ⟶ singChains 𝕜 X) => (g.f n).hom a)
    (subMap_comp_chainsInclusion 𝕜 h)
  have hB := congrArg (fun (g : singChains 𝕜 (subSpace S) ⟶ singChains 𝕜 X) => (g.f n).hom b)
    (subMap_comp_chainsInclusion 𝕜 h)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hA hB
  rw [← hA, ← hB, hab]

/-! ### The direct sum of two chain complexes -/

variable (C D : ChainComplex (ModuleCat.{0} 𝕜) ℕ)

/-- The differential of the degreewise direct sum. -/
def pairCxD (n : ℕ) :
    ModuleCat.of 𝕜 (C.X (n + 1) × D.X (n + 1)) ⟶ ModuleCat.of 𝕜 (C.X n × D.X n) :=
  ModuleCat.ofHom (LinearMap.prodMap (C.d (n + 1) n).hom (D.d (n + 1) n).hom)

/-- The degreewise direct sum of two chain complexes of `𝕜`-modules. -/
def pairCx : ChainComplex (ModuleCat.{0} 𝕜) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of 𝕜 (C.X n × D.X n)) (pairCxD 𝕜 C D)
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨a, b⟩
      have ha := congrArg (fun (g : C.X (n + 2) ⟶ C.X n) => g.hom a) (C.d_comp_d (n + 2) (n + 1) n)
      have hb := congrArg (fun (g : D.X (n + 2) ⟶ D.X n) => g.hom b) (D.d_comp_d (n + 2) (n + 1) n)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] at ha hb
      exact Prod.ext ha hb)

lemma pairCx_d_eq (n : ℕ) : (pairCx 𝕜 C D).d (n + 1) n = pairCxD 𝕜 C D n :=
  ChainComplex.of_d (fun n => ModuleCat.of 𝕜 (C.X n × D.X n)) (pairCxD 𝕜 C D) n

@[simp] lemma pairCx_d_apply (n : ℕ) (a : C.X (n + 1)) (b : D.X (n + 1)) :
    ((pairCx 𝕜 C D).d (n + 1) n).hom (a, b) = ((C.d (n + 1) n).hom a, (D.d (n + 1) n).hom b) := by
  rw [pairCx_d_eq 𝕜]
  rfl

variable {C D}

/-- The map into a direct sum determined by its two components. -/
def pairLift {E : ChainComplex (ModuleCat.{0} 𝕜) ℕ} (φ : E ⟶ C) (ψ : E ⟶ D) : E ⟶ pairCx 𝕜 C D where
  f n := ModuleCat.ofHom (LinearMap.prod (φ.f n).hom (ψ.f n).hom)
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have hφ := congrArg (fun (g : E.X (j + 1) ⟶ C.X j) => g.hom a) (φ.comm (j + 1) j)
    have hψ := congrArg (fun (g : E.X (j + 1) ⟶ D.X j) => g.hom a) (ψ.comm (j + 1) j)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hφ hψ
    change ((pairCx 𝕜 C D).d (j + 1) j).hom ((φ.f (j + 1)).hom a, (ψ.f (j + 1)).hom a) =
      ((φ.f j).hom ((E.d (j + 1) j).hom a), (ψ.f j).hom ((E.d (j + 1) j).hom a))
    rw [pairCx_d_apply 𝕜, hφ, hψ]

/-- The map out of a direct sum determined by its two components. -/
def pairDesc {E : ChainComplex (ModuleCat.{0} 𝕜) ℕ} (φ : C ⟶ E) (ψ : D ⟶ E) : pairCx 𝕜 C D ⟶ E where
  f n := ModuleCat.ofHom (LinearMap.coprod (φ.f n).hom (ψ.f n).hom)
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨a, b⟩
    have hφ := congrArg (fun (g : C.X (j + 1) ⟶ E.X j) => g.hom a) (φ.comm (j + 1) j)
    have hψ := congrArg (fun (g : D.X (j + 1) ⟶ E.X j) => g.hom b) (ψ.comm (j + 1) j)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hφ hψ
    change (E.d (j + 1) j).hom ((φ.f (j + 1)).hom a + (ψ.f (j + 1)).hom b) =
      (φ.f j).hom (((pairCx 𝕜 C D).d (j + 1) j).hom (a, b)).1 +
        (ψ.f j).hom (((pairCx 𝕜 C D).d (j + 1) j).hom (a, b)).2
    rw [pairCx_d_apply 𝕜, map_add, hφ, hψ]

@[simp] lemma pairLift_f_apply {E : ChainComplex (ModuleCat.{0} 𝕜) ℕ} (φ : E ⟶ C) (ψ : E ⟶ D)
    (n : ℕ) (a : E.X n) : ((pairLift 𝕜 φ ψ).f n).hom a = ((φ.f n).hom a, (ψ.f n).hom a) := rfl

@[simp] lemma pairDesc_f_apply {E : ChainComplex (ModuleCat.{0} 𝕜) ℕ} (φ : C ⟶ E) (ψ : D ⟶ E)
    (n : ℕ) (a : C.X n) (b : D.X n) :
    ((pairDesc 𝕜 φ ψ).f n).hom (a, b) = (φ.f n).hom a + (ψ.f n).hom b := rfl

/-! ### The pair complex is the direct sum -/

variable (C D)

/-- The first projection of the direct sum complex. -/
def pairFst : pairCx 𝕜 C D ⟶ C where
  f n := ModuleCat.ofHom (LinearMap.fst 𝕜 (C.X n) (D.X n))
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨a, b⟩
    change (C.d (j + 1) j).hom a = (((pairCx 𝕜 C D).d (j + 1) j).hom (a, b)).1
    rw [pairCx_d_apply 𝕜]

/-- The second projection of the direct sum complex. -/
def pairSnd : pairCx 𝕜 C D ⟶ D where
  f n := ModuleCat.ofHom (LinearMap.snd 𝕜 (C.X n) (D.X n))
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨a, b⟩
    change (D.d (j + 1) j).hom b = (((pairCx 𝕜 C D).d (j + 1) j).hom (a, b)).2
    rw [pairCx_d_apply 𝕜]

/-- The first inclusion into the direct sum complex. -/
def pairInl : C ⟶ pairCx 𝕜 C D := pairLift 𝕜 (𝟙 C) 0

/-- The second inclusion into the direct sum complex. -/
def pairInr : D ⟶ pairCx 𝕜 C D := pairLift 𝕜 0 (𝟙 D)

/-- The direct sum complex, as a binary bicone. -/
def pairBicone : Limits.BinaryBicone C D where
  pt := pairCx 𝕜 C D
  fst := pairFst 𝕜 C D
  snd := pairSnd 𝕜 C D
  inl := pairInl 𝕜 C D
  inr := pairInr 𝕜 C D
  inl_fst := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl
  inl_snd := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl
  inr_fst := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl
  inr_snd := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl

theorem pairBicone_total :
    (pairBicone 𝕜 C D).fst ≫ (pairBicone 𝕜 C D).inl +
      (pairBicone 𝕜 C D).snd ≫ (pairBicone 𝕜 C D).inr =
      𝟙 (pairBicone 𝕜 C D).pt := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨a, b⟩
  change ((a, 0) + (0, b) : C.X n × D.X n) = (a, b)
  simp

/-- **The pair complex really is the direct sum** of the two chain complexes. -/
def pairBicone_isBilimit : (pairBicone 𝕜 C D).IsBilimit :=
  Limits.isBinaryBilimitOfTotal _ (pairBicone_total 𝕜 C D)

/-- The identification of the pair complex with the categorical biproduct. -/
def pairCxIsoBiprod : pairCx 𝕜 C D ≅ C ⊞ D :=
  Limits.biprod.uniqueUpToIso C D (pairBicone_isBilimit 𝕜 C D)

/-- The homology bicone of the pair complex. -/
def homologyPairBicone (n : ℕ) :
    Limits.BinaryBicone (C.homology n) (D.homology n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} 𝕜) (ComplexShape.down ℕ) n).mapBinaryBicone
    (pairBicone 𝕜 C D)

/-- **The homology of the pair complex is the direct sum of the homologies.** -/
def homologyPairBicone_isBilimit (n : ℕ) : (homologyPairBicone 𝕜 C D n).IsBilimit := by
  refine Limits.isBinaryBilimitOfTotal _ ?_
  have h := congrArg
    (fun φ => (HomologicalComplex.homologyFunctor (ModuleCat.{0} 𝕜) (ComplexShape.down ℕ) n).map φ)
    (pairBicone_total 𝕜 C D)
  simp only [Functor.map_add, Functor.map_comp] at h
  exact h.trans
    ((HomologicalComplex.homologyFunctor (ModuleCat.{0} 𝕜) (ComplexShape.down ℕ) n).map_id _)

/-- The homology of the pair complex is the biproduct of the homologies. -/
def homologyPairIso (n : ℕ) :
    (pairCx 𝕜 C D).homology n ≅ C.homology n ⊞ D.homology n :=
  Limits.biprod.uniqueUpToIso _ _ (homologyPairBicone_isBilimit 𝕜 C D n)

variable {C D}

/-! ### The Mayer-Vietoris short exact sequence -/

variable (A B : Set X)

lemma smallChains_mvCover (n : ℕ) :
    smallChains 𝕜 (mvCover A B) n = chainsIn 𝕜 A n ⊔ chainsIn 𝕜 B n := smallChains_bool 𝕜 A B n

lemma chainsIn_le_smallChains_left (n : ℕ) :
    chainsIn 𝕜 A n ≤ smallChains 𝕜 (mvCover A B) n := by
  rw [smallChains_mvCover 𝕜]
  exact le_sup_left

lemma chainsIn_le_smallChains_right (n : ℕ) :
    chainsIn 𝕜 B n ≤ smallChains 𝕜 (mvCover A B) n := by
  rw [smallChains_mvCover 𝕜]
  exact le_sup_right

/-- The inclusion of the chains of a subspace into the complex of small chains
of the cover. -/
def toSmallCx (S : Set X) (h : ∀ n, chainsIn 𝕜 S n ≤ smallChains 𝕜 (mvCover A B) n) :
    singChains 𝕜 (subSpace S) ⟶ smallCx 𝕜 (mvCover A B) where
  f n := ModuleCat.ofHom
    (LinearMap.codRestrict (smallChains 𝕜 (mvCover A B) n) ((chainsInclusion 𝕜 S).f n).hom
      (fun x => h n (by rw [← range_chainsInclusion 𝕜 S n]; exact ⟨x, rfl⟩)))
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hc := congrArg (fun (g : (singChains 𝕜 (subSpace S)).X (j + 1) ⟶ (singChains 𝕜 X).X j) =>
      g.hom x) ((chainsInclusion 𝕜 S).comm (j + 1) j)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
    simp only [smallCx_d_eq 𝕜, smallCxD]
    exact hc

lemma toSmallCx_val (S : Set X) (h : ∀ n, chainsIn 𝕜 S n ≤ smallChains 𝕜 (mvCover A B) n) (n : ℕ)
    (x : (singChains 𝕜 (subSpace S)).X n) :
    ((smallInc 𝕜 (mvCover A B)).f n).hom (((toSmallCx 𝕜 A B S h).f n).hom x) =
      ((chainsInclusion 𝕜 S).f n).hom x := rfl

/-- The first map of the Mayer-Vietoris sequence: `c ↦ (c, -c)`. -/
def mvF : singChains 𝕜 (subSpace (A ∩ B)) ⟶
    pairCx 𝕜 (singChains 𝕜 (subSpace A)) (singChains 𝕜 (subSpace B)) :=
  pairLift 𝕜 (subMap 𝕜 Set.inter_subset_left) (-(subMap 𝕜 Set.inter_subset_right))

/-- The second map of the Mayer-Vietoris sequence: `(a, b) ↦ a + b`. -/
def mvG : pairCx 𝕜 (singChains 𝕜 (subSpace A)) (singChains 𝕜 (subSpace B)) ⟶
    smallCx 𝕜 (mvCover A B) :=
  pairDesc 𝕜 (toSmallCx 𝕜 A B A (chainsIn_le_smallChains_left 𝕜 A B))
    (toSmallCx 𝕜 A B B (chainsIn_le_smallChains_right 𝕜 A B))

theorem mvF_comp_mvG : mvF 𝕜 A B ≫ mvG 𝕜 A B = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  have hA := congrArg (fun (g : singChains 𝕜 (subSpace (A ∩ B)) ⟶ singChains 𝕜 X) => (g.f n).hom c)
    (subMap_comp_chainsInclusion 𝕜 (Set.inter_subset_left (s := A) (t := B)))
  have hB := congrArg (fun (g : singChains 𝕜 (subSpace (A ∩ B)) ⟶ singChains 𝕜 X) => (g.f n).hom c)
    (subMap_comp_chainsInclusion 𝕜 (Set.inter_subset_right (s := A) (t := B)))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hA hB
  change ((smallInc 𝕜 (mvCover A B)).f n).hom
      (((toSmallCx 𝕜 A B A (chainsIn_le_smallChains_left 𝕜 A B)).f n).hom
          (((subMap 𝕜 (Set.inter_subset_left (s := A) (t := B))).f n).hom c) +
        ((toSmallCx 𝕜 A B B (chainsIn_le_smallChains_right 𝕜 A B)).f n).hom
          (-(((subMap 𝕜 (Set.inter_subset_right (s := A) (t := B))).f n).hom c))) = 0
  rw [map_add, toSmallCx_val 𝕜, toSmallCx_val 𝕜, map_neg, hA, hB, add_neg_cancel]

/-- The Mayer-Vietoris short complex of chain complexes. -/
def mvShortComplex : ShortComplex (ChainComplex (ModuleCat.{0} 𝕜) ℕ) :=
  ShortComplex.mk (mvF 𝕜 A B) (mvG 𝕜 A B) (mvF_comp_mvG 𝕜 A B)

lemma mvF_f_injective (n : ℕ) : Function.Injective ((mvF 𝕜 A B).f n).hom := by
  intro a b hab
  exact subMap_injective 𝕜 (Set.inter_subset_left (s := A) (t := B)) n (congrArg Prod.fst hab)

lemma mvG_f_surjective (n : ℕ) : Function.Surjective ((mvG 𝕜 A B).f n).hom := by
  rintro ⟨c, hc⟩
  rw [smallChains_mvCover 𝕜] at hc
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hc
  rw [← range_chainsInclusion 𝕜 A n] at ha
  rw [← range_chainsInclusion 𝕜 B n] at hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  exact ⟨(a', b'), rfl⟩

lemma exists_mvF_eq_of_mvG_eq_zero (n : ℕ)
    (x : (pairCx 𝕜 (singChains 𝕜 (subSpace A)) (singChains 𝕜 (subSpace B))).X n)
    (hx : ((mvG 𝕜 A B).f n).hom x = 0) : ∃ y, ((mvF 𝕜 A B).f n).hom y = x := by
  revert hx
  obtain ⟨a, b⟩ := x
  intro hab
  have hsum : ((chainsInclusion 𝕜 A).f n).hom a + ((chainsInclusion 𝕜 B).f n).hom b = 0 :=
    congrArg Subtype.val hab
  have hmemA : ((chainsInclusion 𝕜 A).f n).hom a ∈ chainsIn 𝕜 A n := by
    rw [← range_chainsInclusion 𝕜 A n]; exact ⟨a, rfl⟩
  have hneg : ((chainsInclusion 𝕜 A).f n).hom a = -(((chainsInclusion 𝕜 B).f n).hom b) := by
    linear_combination (norm := module) hsum
  have hmemB : ((chainsInclusion 𝕜 A).f n).hom a ∈ chainsIn 𝕜 B n := by
    rw [hneg]
    refine Submodule.neg_mem _ ?_
    rw [← range_chainsInclusion 𝕜 B n]
    exact ⟨b, rfl⟩
  have hmem : ((chainsInclusion 𝕜 A).f n).hom a ∈ chainsIn 𝕜 (A ∩ B) n := by
    rw [← chainsIn_inf 𝕜]
    exact ⟨hmemA, hmemB⟩
  rw [← range_chainsInclusion 𝕜 (A ∩ B) n] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, ?_⟩
  have hzA := congrArg (fun (g : singChains 𝕜 (subSpace (A ∩ B)) ⟶ singChains 𝕜 X) => (g.f n).hom z)
    (subMap_comp_chainsInclusion 𝕜 (Set.inter_subset_left (s := A) (t := B)))
  have hzB := congrArg (fun (g : singChains 𝕜 (subSpace (A ∩ B)) ⟶ singChains 𝕜 X) => (g.f n).hom z)
    (subMap_comp_chainsInclusion 𝕜 (Set.inter_subset_right (s := A) (t := B)))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hzA hzB
  have hfst : ((subMap 𝕜 (Set.inter_subset_left (s := A) (t := B))).f n).hom z = a := by
    apply chainsInclusion_injective 𝕜 A n
    rw [hzA, hz]
  have hsnd : ((subMap 𝕜 (Set.inter_subset_right (s := A) (t := B))).f n).hom z = -b := by
    apply chainsInclusion_injective 𝕜 B n
    rw [hzB, hz, map_neg, hneg]
  change (((subMap 𝕜 (Set.inter_subset_left (s := A) (t := B))).f n).hom z,
    -(((subMap 𝕜 (Set.inter_subset_right (s := A) (t := B))).f n).hom z)) = (a, b)
  rw [hfst, hsnd, neg_neg]

/-- **The Mayer-Vietoris sequence of chain complexes is short exact.** -/
theorem mvShortExact : (mvShortComplex 𝕜 A B).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have hexact : ((mvShortComplex 𝕜 A B).map
      (HomologicalComplex.eval (ModuleCat.{0} 𝕜) (ComplexShape.down ℕ) n)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact exists_mvF_eq_of_mvG_eq_zero 𝕜 A B n x hx
  exact ShortComplex.ShortExact.mk' hexact
    ((ModuleCat.mono_iff_injective _).2 (mvF_f_injective 𝕜 A B n))
    ((ModuleCat.epi_iff_surjective _).2 (mvG_f_surjective 𝕜 A B n))

/-! ### The Mayer-Vietoris long exact sequence -/

section LongExact

variable (hA : IsOpen A) (hB : IsOpen B) (hcov : ∀ x : X, x ∈ A ∨ x ∈ B)


include hA hB hcov in
lemma isIso_homologyMap_smallInc_mvCover (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (smallInc 𝕜 (mvCover A B)) n) := by
  have := quasiIso_smallInc 𝕜 (mvCover A B) (isOpen_mvCover A B hA hB) (exists_mem_mvCover A B hcov)
  rw [← quasiIsoAt_iff_isIso_homologyMap]
  exact (quasiIso_iff _).1 this n

/-- The isomorphism between the homology of the small chains of the cover and
the actual singular homology of `X`, given by the small chain theorem. -/
def mvSmallIso (n : ℕ) :
    (mvShortComplex 𝕜 A B).X₃.homology n ≅ (singChains 𝕜 X).homology n :=
  @asIso _ _ _ _ (HomologicalComplex.homologyMap (smallInc 𝕜 (mvCover A B)) n)
    (isIso_homologyMap_smallInc_mvCover 𝕜 A B hA hB hcov n)

lemma mvSmallIso_hom (n : ℕ) :
    (mvSmallIso 𝕜 A B hA hB hcov n).hom =
      HomologicalComplex.homologyMap (smallInc 𝕜 (mvCover A B)) n := rfl

/-- The chain map of the second Mayer-Vietoris map, composed with the inclusion
of small chains, is the sum of the two subspace inclusions. -/
theorem mvG_comp_smallInc :
    mvG 𝕜 A B ≫ smallInc 𝕜 (mvCover A B) =
      pairDesc 𝕜 (chainsInclusion 𝕜 A) (chainsInclusion 𝕜 B) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨a, b⟩
  rfl

/-- The first Mayer-Vietoris map on homology: `c ↦ (c, -c)`. -/
def mvAlpha (n : ℕ) :
    (singChains 𝕜 (subSpace (A ∩ B))).homology n ⟶
      (pairCx 𝕜 (singChains 𝕜 (subSpace A)) (singChains 𝕜 (subSpace B))).homology n :=
  HomologicalComplex.homologyMap (mvShortComplex 𝕜 A B).f n

lemma mvAlpha_eq (n : ℕ) : mvAlpha 𝕜 A B n = HomologicalComplex.homologyMap (mvF 𝕜 A B) n := rfl

/-- The second Mayer-Vietoris map on homology: the sum of the maps induced by
the two inclusions `A ↪ X` and `B ↪ X`. -/
def mvBeta (n : ℕ) :
    (pairCx 𝕜 (singChains 𝕜 (subSpace A)) (singChains 𝕜 (subSpace B))).homology n ⟶
      (singChains 𝕜 X).homology n :=
  HomologicalComplex.homologyMap (pairDesc 𝕜 (chainsInclusion 𝕜 A) (chainsInclusion 𝕜 B)) n

lemma mvBeta_eq (n : ℕ) :
    mvBeta 𝕜 A B n = HomologicalComplex.homologyMap (mvShortComplex 𝕜 A B).g n ≫
      (mvSmallIso 𝕜 A B hA hB hcov n).hom :=
  (congrArg (fun φ => HomologicalComplex.homologyMap φ n) (mvG_comp_smallInc 𝕜 A B)).symm.trans
    (HomologicalComplex.homologyMap_comp (mvG 𝕜 A B) (smallInc 𝕜 (mvCover A B)) n)

/-- The Mayer-Vietoris connecting homomorphism of the open cover `{A, B}`. -/
def mvDelta (n : ℕ) :
    (singChains 𝕜 X).homology (n + 1) ⟶ (singChains 𝕜 (subSpace (A ∩ B))).homology n :=
  (mvSmallIso 𝕜 A B hA hB hcov (n + 1)).inv ≫
    (mvShortExact 𝕜 A B).δ (n + 1) n (by simp)

lemma mvAlpha_comp_mvBeta (n : ℕ) : mvAlpha 𝕜 A B n ≫ mvBeta 𝕜 A B n = 0 := by
  rw [mvAlpha_eq 𝕜, mvBeta, ← HomologicalComplex.homologyMap_comp]
  have h : mvF 𝕜 A B ≫ pairDesc 𝕜 (chainsInclusion 𝕜 A) (chainsInclusion 𝕜 B) = 0 := by
    rw [← mvG_comp_smallInc 𝕜, ← Category.assoc, mvF_comp_mvG 𝕜, zero_comp]
  rw [h, HomologicalComplex.homologyMap_zero]

include hA hB hcov in
/-- **Exactness of the Mayer-Vietoris sequence at `Hₙ(A) ⊕ Hₙ(B)`.** -/
theorem mv_exact_pair (n : ℕ) :
    (ShortComplex.mk (mvAlpha 𝕜 A B n) (mvBeta 𝕜 A B n) (mvAlpha_comp_mvBeta 𝕜 A B n)).Exact := by
  have hex := (mvShortExact 𝕜 A B).homology_exact₂ n
  refine ShortComplex.exact_of_iso ?_ hex
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (mvSmallIso 𝕜 A B hA hB hcov n) ?_ ?_
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (mvBeta_eq 𝕜 A B hA hB hcov n)

include hA hB hcov in
lemma mvBeta_comp_mvDelta (n : ℕ) : mvBeta 𝕜 A B (n + 1) ≫ mvDelta 𝕜 A B hA hB hcov n = 0 := by
  rw [mvBeta_eq 𝕜 A B hA hB hcov]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => HomologicalComplex.homologyMap (mvShortComplex 𝕜 A B).g (n + 1) ≫ t)
      (Iso.hom_inv_id_assoc (mvSmallIso 𝕜 A B hA hB hcov (n + 1))
        ((mvShortExact 𝕜 A B).δ (n + 1) n (by simp)))).trans
      ((mvShortExact 𝕜 A B).comp_δ (n + 1) n (by simp)))

include hA hB hcov in
/-- **Exactness of the Mayer-Vietoris sequence at `Hₙ₊₁(X)`.** -/
theorem mv_exact_space (n : ℕ) :
    (ShortComplex.mk (mvBeta 𝕜 A B (n + 1)) (mvDelta 𝕜 A B hA hB hcov n)
      (mvBeta_comp_mvDelta 𝕜 A B hA hB hcov n)).Exact := by
  have hex := (mvShortExact 𝕜 A B).homology_exact₃ (n + 1) n (by simp)
  refine ShortComplex.exact_of_iso ?_ hex
  refine ShortComplex.isoMk (Iso.refl _) (mvSmallIso 𝕜 A B hA hB hcov (n + 1)) (Iso.refl _) ?_ ?_
  · exact (Category.id_comp _).trans (mvBeta_eq 𝕜 A B hA hB hcov (n + 1))
  · exact (Iso.hom_inv_id_assoc _ _).trans (Category.comp_id _).symm

include hA hB hcov in
lemma mvDelta_comp_mvAlpha (n : ℕ) : mvDelta 𝕜 A B hA hB hcov n ≫ mvAlpha 𝕜 A B n = 0 := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => (mvSmallIso 𝕜 A B hA hB hcov (n + 1)).inv ≫ t)
      ((mvShortExact 𝕜 A B).δ_comp (n + 1) n (by simp))).trans comp_zero)

include hA hB hcov in
/-- **Exactness of the Mayer-Vietoris sequence at `Hₙ(A ∩ B)`.** -/
theorem mv_exact_inter (n : ℕ) :
    (ShortComplex.mk (mvDelta 𝕜 A B hA hB hcov n) (mvAlpha 𝕜 A B n)
      (mvDelta_comp_mvAlpha 𝕜 A B hA hB hcov n)).Exact := by
  have hex := (mvShortExact 𝕜 A B).homology_exact₁ (n + 1) n (by simp)
  refine ShortComplex.exact_of_iso ?_ hex
  refine ShortComplex.isoMk (mvSmallIso 𝕜 A B hA hB hcov (n + 1)) (Iso.refl _) (Iso.refl _) ?_ ?_
  · exact (Iso.hom_inv_id_assoc _ _).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

end LongExact

end AffineTverberg.Coefficients.AffChain
