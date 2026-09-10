import AffineTverberg.SingularChainBasis
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

set_option linter.style.header false

/-!
# The singular Mayer-Vietoris short exact sequence and long exact sequence

For two subsets `A B ⊆ X` whose interiors cover `X` (here: two open sets
covering `X`) the sequence of singular chain complexes

`0 ⟶ C(A ∩ B) ⟶ C(A) ⊕ C(B) ⟶ C^{A,B}(X) ⟶ 0`

is short exact, where `C^{A,B}(X)` is the complex of `{A,B}`-small chains.
Since the inclusion of small chains into all singular chains is a
quasi-isomorphism (`AffChain.quasiIso_smallInc`), the associated long exact
homology sequence is the Mayer-Vietoris sequence of the cover.

Everything is proved from the free basis of singular chains
(`AffineTverberg.SingularChainBasis`); no excision or comparison statement is
assumed.
-/

noncomputable section

open CategoryTheory Limits Simplicial

namespace AffineTverberg

namespace AffChain

variable {X : TopCat.{0}}

/-! ### Chain maps induced by inclusions of subspaces -/

/-- The inclusion of one subspace into a bigger one. -/
def subInclMap {S T : Set X} (h : S ⊆ T) : subSpace S ⟶ subSpace T :=
  TopCat.ofHom ⟨fun x => ⟨x.1, h x.2⟩, by fun_prop⟩

/-- The chain map induced by an inclusion of subspaces. -/
def subMap {S T : Set X} (h : S ⊆ T) : singChains (subSpace S) ⟶ singChains (subSpace T) :=
  SSet.chainComplexMap (TopCat.toSSet.map (subInclMap h)) (ModuleCat.of ℝ ℝ)

lemma ιs_subMap {S T : Set X} (h : S ⊆ T) {n : ℕ} (x : singIdx (subSpace S) n) :
    ιs x ≫ (subMap h).f n =
      ιs ((TopCat.toSSet.map (subInclMap h)).app (Opposite.op ⦋n⦌) x) := by
  rw [subMap, SSet.ι_chainComplexMap_f]

/-- Compatibility of the induced maps with the inclusions into the ambient
space. -/
theorem subMap_comp_chainsInclusion {S T : Set X} (h : S ⊆ T) :
    subMap h ≫ chainsInclusion T = chainsInclusion S := by
  apply HomologicalComplex.hom_ext
  intro n
  refine singChains_hom_ext fun x => ?_
  rw [HomologicalComplex.comp_f, ← Category.assoc, ιs_subMap, ιs_chainsInclusion,
    ιs_chainsInclusion]
  congr 1

lemma subMap_injective {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    Function.Injective ((subMap h).f n).hom := by
  intro a b hab
  apply chainsInclusion_injective S n
  have hA := congrArg (fun (g : singChains (subSpace S) ⟶ singChains X) => (g.f n).hom a)
    (subMap_comp_chainsInclusion h)
  have hB := congrArg (fun (g : singChains (subSpace S) ⟶ singChains X) => (g.f n).hom b)
    (subMap_comp_chainsInclusion h)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hA hB
  rw [← hA, ← hB, hab]

/-! ### The direct sum of two chain complexes -/

variable (C D : ChainComplex (ModuleCat.{0} ℝ) ℕ)

/-- The differential of the degreewise direct sum. -/
def pairCxD (n : ℕ) :
    ModuleCat.of ℝ (C.X (n + 1) × D.X (n + 1)) ⟶ ModuleCat.of ℝ (C.X n × D.X n) :=
  ModuleCat.ofHom (LinearMap.prodMap (C.d (n + 1) n).hom (D.d (n + 1) n).hom)

/-- The degreewise direct sum of two chain complexes of `ℝ`-modules. -/
def pairCx : ChainComplex (ModuleCat.{0} ℝ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℝ (C.X n × D.X n)) (pairCxD C D)
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨a, b⟩
      have ha := congrArg (fun (g : C.X (n + 2) ⟶ C.X n) => g.hom a) (C.d_comp_d (n + 2) (n + 1) n)
      have hb := congrArg (fun (g : D.X (n + 2) ⟶ D.X n) => g.hom b) (D.d_comp_d (n + 2) (n + 1) n)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] at ha hb
      exact Prod.ext ha hb)

lemma pairCx_d_eq (n : ℕ) : (pairCx C D).d (n + 1) n = pairCxD C D n :=
  ChainComplex.of_d (fun n => ModuleCat.of ℝ (C.X n × D.X n)) (pairCxD C D) n

@[simp] lemma pairCx_d_apply (n : ℕ) (a : C.X (n + 1)) (b : D.X (n + 1)) :
    ((pairCx C D).d (n + 1) n).hom (a, b) = ((C.d (n + 1) n).hom a, (D.d (n + 1) n).hom b) := by
  rw [pairCx_d_eq]
  rfl

variable {C D}

/-- The map into a direct sum determined by its two components. -/
def pairLift {E : ChainComplex (ModuleCat.{0} ℝ) ℕ} (φ : E ⟶ C) (ψ : E ⟶ D) : E ⟶ pairCx C D where
  f n := ModuleCat.ofHom (LinearMap.prod (φ.f n).hom (ψ.f n).hom)
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have hφ := congrArg (fun (g : E.X (j + 1) ⟶ C.X j) => g.hom a) (φ.comm (j + 1) j)
    have hψ := congrArg (fun (g : E.X (j + 1) ⟶ D.X j) => g.hom a) (ψ.comm (j + 1) j)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hφ hψ
    change ((pairCx C D).d (j + 1) j).hom ((φ.f (j + 1)).hom a, (ψ.f (j + 1)).hom a) =
      ((φ.f j).hom ((E.d (j + 1) j).hom a), (ψ.f j).hom ((E.d (j + 1) j).hom a))
    rw [pairCx_d_apply, hφ, hψ]

/-- The map out of a direct sum determined by its two components. -/
def pairDesc {E : ChainComplex (ModuleCat.{0} ℝ) ℕ} (φ : C ⟶ E) (ψ : D ⟶ E) : pairCx C D ⟶ E where
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
      (φ.f j).hom (((pairCx C D).d (j + 1) j).hom (a, b)).1 +
        (ψ.f j).hom (((pairCx C D).d (j + 1) j).hom (a, b)).2
    rw [pairCx_d_apply, map_add, hφ, hψ]

@[simp] lemma pairLift_f_apply {E : ChainComplex (ModuleCat.{0} ℝ) ℕ} (φ : E ⟶ C) (ψ : E ⟶ D)
    (n : ℕ) (a : E.X n) : ((pairLift φ ψ).f n).hom a = ((φ.f n).hom a, (ψ.f n).hom a) := rfl

@[simp] lemma pairDesc_f_apply {E : ChainComplex (ModuleCat.{0} ℝ) ℕ} (φ : C ⟶ E) (ψ : D ⟶ E)
    (n : ℕ) (a : C.X n) (b : D.X n) :
    ((pairDesc φ ψ).f n).hom (a, b) = (φ.f n).hom a + (ψ.f n).hom b := rfl

/-! ### The pair complex is the direct sum -/

variable (C D)

/-- The first projection of the direct sum complex. -/
def pairFst : pairCx C D ⟶ C where
  f n := ModuleCat.ofHom (LinearMap.fst ℝ (C.X n) (D.X n))
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨a, b⟩
    change (C.d (j + 1) j).hom a = (((pairCx C D).d (j + 1) j).hom (a, b)).1
    rw [pairCx_d_apply]

/-- The second projection of the direct sum complex. -/
def pairSnd : pairCx C D ⟶ D where
  f n := ModuleCat.ofHom (LinearMap.snd ℝ (C.X n) (D.X n))
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨a, b⟩
    change (D.d (j + 1) j).hom b = (((pairCx C D).d (j + 1) j).hom (a, b)).2
    rw [pairCx_d_apply]

/-- The first inclusion into the direct sum complex. -/
def pairInl : C ⟶ pairCx C D := pairLift (𝟙 C) 0

/-- The second inclusion into the direct sum complex. -/
def pairInr : D ⟶ pairCx C D := pairLift 0 (𝟙 D)

/-- The direct sum complex, as a binary bicone. -/
def pairBicone : Limits.BinaryBicone C D where
  pt := pairCx C D
  fst := pairFst C D
  snd := pairSnd C D
  inl := pairInl C D
  inr := pairInr C D
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
    (pairBicone C D).fst ≫ (pairBicone C D).inl + (pairBicone C D).snd ≫ (pairBicone C D).inr =
      𝟙 (pairBicone C D).pt := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨a, b⟩
  change ((a, 0) + (0, b) : C.X n × D.X n) = (a, b)
  simp

/-- **The pair complex really is the direct sum** of the two chain complexes. -/
def pairBicone_isBilimit : (pairBicone C D).IsBilimit :=
  Limits.isBinaryBilimitOfTotal _ (pairBicone_total C D)

/-- The identification of the pair complex with the categorical biproduct. -/
def pairCxIsoBiprod : pairCx C D ≅ C ⊞ D :=
  Limits.biprod.uniqueUpToIso C D (pairBicone_isBilimit C D)

/-- The homology bicone of the pair complex. -/
def homologyPairBicone (n : ℕ) :
    Limits.BinaryBicone (C.homology n) (D.homology n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℝ) (ComplexShape.down ℕ) n).mapBinaryBicone
    (pairBicone C D)

/-- **The homology of the pair complex is the direct sum of the homologies.** -/
def homologyPairBicone_isBilimit (n : ℕ) : (homologyPairBicone C D n).IsBilimit := by
  refine Limits.isBinaryBilimitOfTotal _ ?_
  have h := congrArg
    (fun φ => (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℝ) (ComplexShape.down ℕ) n).map φ)
    (pairBicone_total C D)
  simp only [Functor.map_add, Functor.map_comp] at h
  exact h.trans
    ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℝ) (ComplexShape.down ℕ) n).map_id _)

/-- The homology of the pair complex is the biproduct of the homologies. -/
def homologyPairIso (n : ℕ) :
    (pairCx C D).homology n ≅ C.homology n ⊞ D.homology n :=
  Limits.biprod.uniqueUpToIso _ _ (homologyPairBicone_isBilimit C D n)

variable {C D}

/-! ### The Mayer-Vietoris short exact sequence -/

variable (A B : Set X)

/-- The two-element open cover used in the Mayer-Vietoris argument. -/
def mvCover : Bool → Set X := fun b => bif b then A else B

lemma mvCover_true : mvCover A B true = A := rfl
lemma mvCover_false : mvCover A B false = B := rfl

lemma smallChains_mvCover (n : ℕ) :
    smallChains (mvCover A B) n = chainsIn A n ⊔ chainsIn B n := smallChains_bool A B n

lemma chainsIn_le_smallChains_left (n : ℕ) :
    chainsIn A n ≤ smallChains (mvCover A B) n := by
  rw [smallChains_mvCover]
  exact le_sup_left

lemma chainsIn_le_smallChains_right (n : ℕ) :
    chainsIn B n ≤ smallChains (mvCover A B) n := by
  rw [smallChains_mvCover]
  exact le_sup_right

/-- The inclusion of the chains of a subspace into the complex of small chains
of the cover. -/
def toSmallCx (S : Set X) (h : ∀ n, chainsIn S n ≤ smallChains (mvCover A B) n) :
    singChains (subSpace S) ⟶ smallCx (mvCover A B) where
  f n := ModuleCat.ofHom
    (LinearMap.codRestrict (smallChains (mvCover A B) n) ((chainsInclusion S).f n).hom
      (fun x => h n (by rw [← range_chainsInclusion S n]; exact ⟨x, rfl⟩)))
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hc := congrArg (fun (g : (singChains (subSpace S)).X (j + 1) ⟶ (singChains X).X j) =>
      g.hom x) ((chainsInclusion S).comm (j + 1) j)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
    simp only [smallCx_d_eq, smallCxD]
    exact hc

lemma toSmallCx_val (S : Set X) (h : ∀ n, chainsIn S n ≤ smallChains (mvCover A B) n) (n : ℕ)
    (x : (singChains (subSpace S)).X n) :
    ((smallInc (mvCover A B)).f n).hom (((toSmallCx A B S h).f n).hom x) =
      ((chainsInclusion S).f n).hom x := rfl

/-- The first map of the Mayer-Vietoris sequence: `c ↦ (c, -c)`. -/
def mvF : singChains (subSpace (A ∩ B)) ⟶
    pairCx (singChains (subSpace A)) (singChains (subSpace B)) :=
  pairLift (subMap Set.inter_subset_left) (-(subMap Set.inter_subset_right))

/-- The second map of the Mayer-Vietoris sequence: `(a, b) ↦ a + b`. -/
def mvG : pairCx (singChains (subSpace A)) (singChains (subSpace B)) ⟶ smallCx (mvCover A B) :=
  pairDesc (toSmallCx A B A (chainsIn_le_smallChains_left A B))
    (toSmallCx A B B (chainsIn_le_smallChains_right A B))

theorem mvF_comp_mvG : mvF A B ≫ mvG A B = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  have hA := congrArg (fun (g : singChains (subSpace (A ∩ B)) ⟶ singChains X) => (g.f n).hom c)
    (subMap_comp_chainsInclusion (Set.inter_subset_left (s := A) (t := B)))
  have hB := congrArg (fun (g : singChains (subSpace (A ∩ B)) ⟶ singChains X) => (g.f n).hom c)
    (subMap_comp_chainsInclusion (Set.inter_subset_right (s := A) (t := B)))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hA hB
  change ((smallInc (mvCover A B)).f n).hom
      (((toSmallCx A B A (chainsIn_le_smallChains_left A B)).f n).hom
          (((subMap (Set.inter_subset_left (s := A) (t := B))).f n).hom c) +
        ((toSmallCx A B B (chainsIn_le_smallChains_right A B)).f n).hom
          (-(((subMap (Set.inter_subset_right (s := A) (t := B))).f n).hom c))) = 0
  rw [map_add, toSmallCx_val, toSmallCx_val, map_neg, hA, hB, add_neg_cancel]

/-- The Mayer-Vietoris short complex of chain complexes. -/
def mvShortComplex : ShortComplex (ChainComplex (ModuleCat.{0} ℝ) ℕ) :=
  ShortComplex.mk (mvF A B) (mvG A B) (mvF_comp_mvG A B)

lemma mvF_f_injective (n : ℕ) : Function.Injective ((mvF A B).f n).hom := by
  intro a b hab
  exact subMap_injective (Set.inter_subset_left (s := A) (t := B)) n (congrArg Prod.fst hab)

lemma mvG_f_surjective (n : ℕ) : Function.Surjective ((mvG A B).f n).hom := by
  rintro ⟨c, hc⟩
  rw [smallChains_mvCover] at hc
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hc
  rw [← range_chainsInclusion A n] at ha
  rw [← range_chainsInclusion B n] at hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  exact ⟨(a', b'), rfl⟩

lemma exists_mvF_eq_of_mvG_eq_zero (n : ℕ)
    (x : (pairCx (singChains (subSpace A)) (singChains (subSpace B))).X n)
    (hx : ((mvG A B).f n).hom x = 0) : ∃ y, ((mvF A B).f n).hom y = x := by
  revert hx
  obtain ⟨a, b⟩ := x
  intro hab
  have hsum : ((chainsInclusion A).f n).hom a + ((chainsInclusion B).f n).hom b = 0 :=
    congrArg Subtype.val hab
  have hmemA : ((chainsInclusion A).f n).hom a ∈ chainsIn A n := by
    rw [← range_chainsInclusion A n]; exact ⟨a, rfl⟩
  have hneg : ((chainsInclusion A).f n).hom a = -(((chainsInclusion B).f n).hom b) := by
    linear_combination (norm := module) hsum
  have hmemB : ((chainsInclusion A).f n).hom a ∈ chainsIn B n := by
    rw [hneg]
    refine Submodule.neg_mem _ ?_
    rw [← range_chainsInclusion B n]
    exact ⟨b, rfl⟩
  have hmem : ((chainsInclusion A).f n).hom a ∈ chainsIn (A ∩ B) n := by
    rw [← chainsIn_inf]
    exact ⟨hmemA, hmemB⟩
  rw [← range_chainsInclusion (A ∩ B) n] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, ?_⟩
  have hzA := congrArg (fun (g : singChains (subSpace (A ∩ B)) ⟶ singChains X) => (g.f n).hom z)
    (subMap_comp_chainsInclusion (Set.inter_subset_left (s := A) (t := B)))
  have hzB := congrArg (fun (g : singChains (subSpace (A ∩ B)) ⟶ singChains X) => (g.f n).hom z)
    (subMap_comp_chainsInclusion (Set.inter_subset_right (s := A) (t := B)))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hzA hzB
  have hfst : ((subMap (Set.inter_subset_left (s := A) (t := B))).f n).hom z = a := by
    apply chainsInclusion_injective A n
    rw [hzA, hz]
  have hsnd : ((subMap (Set.inter_subset_right (s := A) (t := B))).f n).hom z = -b := by
    apply chainsInclusion_injective B n
    rw [hzB, hz, map_neg, hneg]
  change (((subMap (Set.inter_subset_left (s := A) (t := B))).f n).hom z,
    -(((subMap (Set.inter_subset_right (s := A) (t := B))).f n).hom z)) = (a, b)
  rw [hfst, hsnd, neg_neg]

/-- **The Mayer-Vietoris sequence of chain complexes is short exact.** -/
theorem mvShortExact : (mvShortComplex A B).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have hexact : ((mvShortComplex A B).map
      (HomologicalComplex.eval (ModuleCat.{0} ℝ) (ComplexShape.down ℕ) n)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact exists_mvF_eq_of_mvG_eq_zero A B n x hx
  exact ShortComplex.ShortExact.mk' hexact
    ((ModuleCat.mono_iff_injective _).2 (mvF_f_injective A B n))
    ((ModuleCat.epi_iff_surjective _).2 (mvG_f_surjective A B n))

/-! ### The Mayer-Vietoris long exact sequence -/

section LongExact

variable (hA : IsOpen A) (hB : IsOpen B) (hcov : ∀ x : X, x ∈ A ∨ x ∈ B)

include hA hB in
lemma isOpen_mvCover : ∀ b : Bool, IsOpen (mvCover A B b) := by
  rintro (_ | _)
  · exact hB
  · exact hA

include hcov in
lemma exists_mem_mvCover : ∀ x : X, ∃ b, x ∈ mvCover A B b := by
  intro x
  rcases hcov x with h | h
  · exact ⟨true, h⟩
  · exact ⟨false, h⟩

include hA hB hcov in
lemma isIso_homologyMap_smallInc_mvCover (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (smallInc (mvCover A B)) n) := by
  have := quasiIso_smallInc (mvCover A B) (isOpen_mvCover A B hA hB) (exists_mem_mvCover A B hcov)
  rw [← quasiIsoAt_iff_isIso_homologyMap]
  exact (quasiIso_iff _).1 this n

/-- The isomorphism between the homology of the small chains of the cover and
the actual singular homology of `X`, given by the small chain theorem. -/
def mvSmallIso (n : ℕ) :
    (mvShortComplex A B).X₃.homology n ≅ (singChains X).homology n :=
  @asIso _ _ _ _ (HomologicalComplex.homologyMap (smallInc (mvCover A B)) n)
    (isIso_homologyMap_smallInc_mvCover A B hA hB hcov n)

lemma mvSmallIso_hom (n : ℕ) :
    (mvSmallIso A B hA hB hcov n).hom =
      HomologicalComplex.homologyMap (smallInc (mvCover A B)) n := rfl

/-- The chain map of the second Mayer-Vietoris map, composed with the inclusion
of small chains, is the sum of the two subspace inclusions. -/
theorem mvG_comp_smallInc :
    mvG A B ≫ smallInc (mvCover A B) = pairDesc (chainsInclusion A) (chainsInclusion B) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨a, b⟩
  rfl

/-- The first Mayer-Vietoris map on homology: `c ↦ (c, -c)`. -/
def mvAlpha (n : ℕ) :
    (singChains (subSpace (A ∩ B))).homology n ⟶
      (pairCx (singChains (subSpace A)) (singChains (subSpace B))).homology n :=
  HomologicalComplex.homologyMap (mvShortComplex A B).f n

lemma mvAlpha_eq (n : ℕ) : mvAlpha A B n = HomologicalComplex.homologyMap (mvF A B) n := rfl

/-- The second Mayer-Vietoris map on homology: the sum of the maps induced by
the two inclusions `A ↪ X` and `B ↪ X`. -/
def mvBeta (n : ℕ) :
    (pairCx (singChains (subSpace A)) (singChains (subSpace B))).homology n ⟶
      (singChains X).homology n :=
  HomologicalComplex.homologyMap (pairDesc (chainsInclusion A) (chainsInclusion B)) n

lemma mvBeta_eq (n : ℕ) :
    mvBeta A B n = HomologicalComplex.homologyMap (mvShortComplex A B).g n ≫
      (mvSmallIso A B hA hB hcov n).hom :=
  (congrArg (fun φ => HomologicalComplex.homologyMap φ n) (mvG_comp_smallInc A B)).symm.trans
    (HomologicalComplex.homologyMap_comp (mvG A B) (smallInc (mvCover A B)) n)

/-- The Mayer-Vietoris connecting homomorphism of the open cover `{A, B}`. -/
def mvDelta (n : ℕ) :
    (singChains X).homology (n + 1) ⟶ (singChains (subSpace (A ∩ B))).homology n :=
  (mvSmallIso A B hA hB hcov (n + 1)).inv ≫
    (mvShortExact A B).δ (n + 1) n (by simp)

lemma mvAlpha_comp_mvBeta (n : ℕ) : mvAlpha A B n ≫ mvBeta A B n = 0 := by
  rw [mvAlpha_eq, mvBeta, ← HomologicalComplex.homologyMap_comp]
  have h : mvF A B ≫ pairDesc (chainsInclusion A) (chainsInclusion B) = 0 := by
    rw [← mvG_comp_smallInc, ← Category.assoc, mvF_comp_mvG, zero_comp]
  rw [h, HomologicalComplex.homologyMap_zero]

include hA hB hcov in
/-- **Exactness of the Mayer-Vietoris sequence at `Hₙ(A) ⊕ Hₙ(B)`.** -/
theorem mv_exact_pair (n : ℕ) :
    (ShortComplex.mk (mvAlpha A B n) (mvBeta A B n) (mvAlpha_comp_mvBeta A B n)).Exact := by
  have hex := (mvShortExact A B).homology_exact₂ n
  refine ShortComplex.exact_of_iso ?_ hex
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (mvSmallIso A B hA hB hcov n) ?_ ?_
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (mvBeta_eq A B hA hB hcov n)

include hA hB hcov in
lemma mvBeta_comp_mvDelta (n : ℕ) : mvBeta A B (n + 1) ≫ mvDelta A B hA hB hcov n = 0 := by
  rw [mvBeta_eq A B hA hB hcov]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => HomologicalComplex.homologyMap (mvShortComplex A B).g (n + 1) ≫ t)
      (Iso.hom_inv_id_assoc (mvSmallIso A B hA hB hcov (n + 1))
        ((mvShortExact A B).δ (n + 1) n (by simp)))).trans
      ((mvShortExact A B).comp_δ (n + 1) n (by simp)))

include hA hB hcov in
/-- **Exactness of the Mayer-Vietoris sequence at `Hₙ₊₁(X)`.** -/
theorem mv_exact_space (n : ℕ) :
    (ShortComplex.mk (mvBeta A B (n + 1)) (mvDelta A B hA hB hcov n)
      (mvBeta_comp_mvDelta A B hA hB hcov n)).Exact := by
  have hex := (mvShortExact A B).homology_exact₃ (n + 1) n (by simp)
  refine ShortComplex.exact_of_iso ?_ hex
  refine ShortComplex.isoMk (Iso.refl _) (mvSmallIso A B hA hB hcov (n + 1)) (Iso.refl _) ?_ ?_
  · exact (Category.id_comp _).trans (mvBeta_eq A B hA hB hcov (n + 1))
  · exact (Iso.hom_inv_id_assoc _ _).trans (Category.comp_id _).symm

include hA hB hcov in
lemma mvDelta_comp_mvAlpha (n : ℕ) : mvDelta A B hA hB hcov n ≫ mvAlpha A B n = 0 := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => (mvSmallIso A B hA hB hcov (n + 1)).inv ≫ t)
      ((mvShortExact A B).δ_comp (n + 1) n (by simp))).trans comp_zero)

include hA hB hcov in
/-- **Exactness of the Mayer-Vietoris sequence at `Hₙ(A ∩ B)`.** -/
theorem mv_exact_inter (n : ℕ) :
    (ShortComplex.mk (mvDelta A B hA hB hcov n) (mvAlpha A B n)
      (mvDelta_comp_mvAlpha A B hA hB hcov n)).Exact := by
  have hex := (mvShortExact A B).homology_exact₁ (n + 1) n (by simp)
  refine ShortComplex.exact_of_iso ?_ hex
  refine ShortComplex.isoMk (mvSmallIso A B hA hB hcov (n + 1)) (Iso.refl _) (Iso.refl _) ?_ ?_
  · exact (Iso.hom_inv_id_assoc _ _).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

end LongExact

/-! ### What this does and does not give

The sequence above is the genuine singular Mayer-Vietoris sequence of an open
cover `{A, B}` of `X`: the maps are induced by the actual inclusions of the
subspaces `A ∩ B`, `A`, `B` into one another and into `X`, the middle term is
the actual direct sum (`pairBicone_isBilimit`, `homologyPairBicone_isBilimit`),
and the identification with `H_*(X)` is the small chain quasi-isomorphism
`quasiIso_smallInc`, not an assumption.

It is *not* yet the general simplicial-to-singular comparison theorem
`IsIso (Simplicial.comparisonHomologyMap hK n)`. To run the induction on the
number of simplices of a finite face-closed family `K` with this sequence one
needs, for a maximal face `s ∈ K`, *open* sets `A, B ⊆ barycentricCarrier K`
covering the realization with

* `A` deformation retracting onto the realization of `K \ {s}`,
* `B` contractible,
* `A ∩ B` having the homotopy type of the boundary sphere of `s`.

The first two are now available: `AffineTverberg.Simplicial.puncturedHomotopyEquiv`
takes `A` to be the realization minus the barycenter of `s` and produces the
deformation retraction onto the realization of `K.erase s`, and
`AffineTverberg.Simplicial.contractibleSpace_openStar` gives contractibility of
the open star `B`; `AffineTverberg.Simplicial.faceMv_exact_space` and its
companions instantiate the sequence below at that verified open cover. The
third piece is `AffineTverberg.Simplicial.linkHomotopyEquiv`: the intersection
`A ∩ B` deformation retracts onto the realization of the boundary of `s`.

What is still missing for the general comparison theorem is the comparison of
this sequence with the simplicial Mayer-Vietoris sequence of the decomposition
`K = (K \ {s}) ∪ (powerset of s)`, i.e. the naturality of
`Simplicial.comparisonHomologyMap` through the three homotopy equivalences,
followed by a five-lemma induction on the number of faces of `K`. That step is
deliberately not assumed anywhere.
-/

end AffChain

end AffineTverberg
