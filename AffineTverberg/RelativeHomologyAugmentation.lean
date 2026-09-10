import AffineTverberg.RelativeHomologyShift
import AffineTverberg.SingularAcyclicFiber

set_option linter.style.header false

/-!
# Relative degree one and the actual augmentation kernel

For a contractible ambient space, the connecting map identifies relative
H1 with the kernel of the actual H0 augmentation of the subspace. This is
the missing reduced degree-zero endpoint of the usual positive-degree
relative homology shift. The maps are the genuine pair sequence and the
natural singular augmentation, not an assumed reduced-homology model.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.AffChain

variable {X : TopCat.{0}}

theorem relIota_comp_augmentation (A : Set X) :
    relIota A 0 ≫ realSingularAugmentation X =
      realSingularAugmentation (subSpace A) :=
  realSingularAugmentation_naturality (subIncl A)

theorem mono_relDelta_of_isZero (A : Set X)
    (hX : IsZero ((singChains X).homology 1)) : Mono (relDelta A 0) :=
  (ShortComplex.exact_iff_mono _ (hX.eq_zero_of_src (relPi A 1))).mp
    (relExact_relative A 0)

/-- The isomorphism to the kernel is induced by the connecting map of the
actual pair sequence. -/
def relativeHomologyOneKernelIso (A : Set X)
    (hX : IsZero ((singChains X).homology 1)) :
    relativeHomology A 1 ≅ kernel (relIota A 0) := by
  have := mono_relDelta_of_isZero A hX
  exact (relExact_sub A 0).fIsKernel.conePointUniqueUpToIso
    (limit.isLimit (parallelPair (relIota A 0) 0))

theorem relativeHomologyOneKernelIso_hom_ι (A : Set X)
    (hX : IsZero ((singChains X).homology 1)) :
    (relativeHomologyOneKernelIso A hX).hom ≫ kernel.ι (relIota A 0) =
      relDelta A 0 := by
  have := mono_relDelta_of_isZero A hX
  exact IsLimit.conePointUniqueUpToIso_hom_comp (relExact_sub A 0).fIsKernel
    (limit.isLimit (parallelPair (relIota A 0) 0)) WalkingParallelPair.zero

/-- For a contractible ambient space the relative H1 group is the kernel
of the subspace's actual H0 augmentation, including disconnected subspaces. -/
def relativeHomologyOneAugmentationKernelIso [ContractibleSpace X] (A : Set X) :
    relativeHomology A 1 ≅ kernel (realSingularAugmentation (subSpace A)) := by
  have hsub : Subsingleton ((singChains X).homology 1) :=
    realSingularHomology_subsingleton_of_contractible X 1 (by omega)
  have hzero : IsZero ((singChains X).homology 1) := ModuleCat.isZero_of_subsingleton _
  have hpath : PathConnectedSpace X := inferInstance
  have haug : IsIso (realSingularAugmentation X) := inferInstance
  let iota : (realSingularHomology 0).obj (subSpace A) ⟶
      (realSingularHomology 0).obj X := relIota A 0
  let eiota := kernelCompMono iota (realSingularAugmentation X)
  exact relativeHomologyOneKernelIso A hzero ≪≫
    eiota.symm ≪≫
    kernelIsoOfEq (relIota_comp_augmentation A)

/-- The reduced endpoint is still the actual connecting homomorphism. -/
theorem relativeHomologyOneAugmentationKernelIso_hom_ι [ContractibleSpace X] (A : Set X) :
    (relativeHomologyOneAugmentationKernelIso A).hom ≫
        kernel.ι (realSingularAugmentation (subSpace A)) = relDelta A 0 := by
  have hsub : Subsingleton ((singChains X).homology 1) :=
    realSingularHomology_subsingleton_of_contractible X 1 (by omega)
  have hzero : IsZero ((singChains X).homology 1) := ModuleCat.isZero_of_subsingleton _
  have hpath : PathConnectedSpace X := inferInstance
  have haug : IsIso (realSingularAugmentation X) := inferInstance
  let iota : (realSingularHomology 0).obj (subSpace A) ⟶
      (realSingularHomology 0).obj X := relIota A 0
  let k : relativeHomology A 1 ⟶ kernel iota := (relativeHomologyOneKernelIso A hzero).hom
  have hnat : iota ≫ realSingularAugmentation X =
      realSingularAugmentation (subSpace A) := relIota_comp_augmentation A
  have h : k ≫
      (kernelCompMono iota (realSingularAugmentation X)).inv ≫
      (kernelIsoOfEq hnat).hom ≫
      kernel.ι (realSingularAugmentation (subSpace A)) = relDelta A 0 := by
    rw [kernelIsoOfEq_hom_comp_ι]
    simp only [kernelCompMono_inv, kernel.lift_ι]
    exact relativeHomologyOneKernelIso_hom_ι A hzero
  exact h

end AffineTverberg.AffChain

namespace AffineTverberg

/-- Actual homotopy equivalences identify the kernels of the genuine H0
augmentations, through naturality of the singular homology map. -/
def singularAugmentationKernelIsoOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    kernel (realSingularAugmentation (TopCat.of X)) ≅
      kernel (realSingularAugmentation (TopCat.of Y)) := by
  have hmap : IsIso ((realSingularHomology 0).map (TopCat.ofHom e.toFun)) :=
    (realSingularHomologyIsoOfHomotopyEquiv e 0).isIso_hom
  exact (kernelIsoOfEq (realSingularAugmentation_naturality (TopCat.ofHom e.toFun))).symm ≪≫
    kernelIsIsoComp ((realSingularHomology 0).map (TopCat.ofHom e.toFun))
      (realSingularAugmentation (TopCat.of Y))

/-- The kernel isomorphism is the restriction of the actual homology map. -/
theorem singularAugmentationKernelIsoOfHomotopyEquiv_hom_ι
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    (singularAugmentationKernelIsoOfHomotopyEquiv e).hom ≫
        kernel.ι (realSingularAugmentation (TopCat.of Y)) =
      kernel.ι (realSingularAugmentation (TopCat.of X)) ≫
        (realSingularHomology 0).map (TopCat.ofHom e.toFun) := by
  have hmap : IsIso ((realSingularHomology 0).map (TopCat.ofHom e.toFun)) :=
    (realSingularHomologyIsoOfHomotopyEquiv e 0).isIso_hom
  have h : (kernelIsoOfEq
      (realSingularAugmentation_naturality (TopCat.ofHom e.toFun))).inv ≫
      (kernelIsIsoComp ((realSingularHomology 0).map (TopCat.ofHom e.toFun))
        (realSingularAugmentation (TopCat.of Y))).hom ≫
      kernel.ι (realSingularAugmentation (TopCat.of Y)) =
      kernel.ι (realSingularAugmentation (TopCat.of X)) ≫
        (realSingularHomology 0).map (TopCat.ofHom e.toFun) := by
    simp only [kernelIsIsoComp_hom, kernel.lift_ι]
    rw [← Category.assoc, kernelIsoOfEq_inv_comp_ι]
  exact h

end AffineTverberg
