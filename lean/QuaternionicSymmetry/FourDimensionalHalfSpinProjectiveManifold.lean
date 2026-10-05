import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCore
import QuaternionicSymmetry.ManifoldTwistorSphereManifold

/-! The independently topologized projective half-spin associated bundle is
a genuine smooth manifold. Its CP¹ fiber charts are the pre-existing affine
complex projective charts, and its overlap maps are the literal matrix action
proved smooth in `FourDimensionalHalfSpinActualTransitionSmooth`. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveManifold

open scoped ContDiff Manifold Quaternion
open FourDimensionalHalfSpinProjectiveCore
  FourDimensionalHalfSpinActualTransitionSmooth
  FourDimensionalHalfSpinProjective

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

def SpinorBundleTotal := (projectiveSpinorCore Q).TotalSpace

instance : TopologicalSpace (SpinorBundleTotal Q) :=
  (projectiveSpinorCore Q).toTopologicalSpace

instance : FiberBundle ProjectiveSpinor (projectiveSpinorCore Q).Fiber :=
  (projectiveSpinorCore Q).fiberBundle

instance : ChartedSpace (M × ProjectiveSpinor) (SpinorBundleTotal Q) :=
  FiberBundle.chartedSpace'

instance : ChartedSpace (ModelProd ℍ ProjectiveSpinor)
    (SpinorBundleTotal Q) := by
  change ChartedSpace (ModelProd ℍ ProjectiveSpinor)
    (Bundle.TotalSpace ProjectiveSpinor (projectiveSpinorCore Q).Fiber)
  infer_instance

instance : ChartedSpace (ModelProd ℍ (Fin 1 → ℂ))
    (SpinorBundleTotal Q) := by
  letI : ChartedSpace (ModelProd ℍ (Fin 1 → ℂ))
      (M × ProjectiveSpinor) := inferInstance
  exact ChartedSpace.comp _ (M × ProjectiveSpinor) _

private abbrev productModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)

private def smoothProductPregroupoid : Pregroupoid (M × ProjectiveSpinor) where
  property f s := ContMDiffOn productModel productModel ∞ f s
  comp {f g u v} hf hg _ _ _ := by
    refine hg.comp (hf.mono ?_) ?_
    · intro x hx
      exact hx.1
    · intro x hx
      exact hx.2
  id_mem := contMDiffOn_id
  locality {f u} _ H := contMDiffOn_of_locally_contMDiffOn H
  congr {f g u} _ fg hf := hf.congr (fun x hx => fg x hx)

private theorem bundle_hasSmoothProductGroupoid :
    HasGroupoid (SpinorBundleTotal Q)
      (smoothProductPregroupoid (M := M)).groupoid := by
  apply hasGroupoid_of_pregroupoid
  intro e e' he he'
  let Z := projectiveSpinorCore Q
  change e ∈ (fun t : Trivialization ProjectiveSpinor
      (Bundle.TotalSpace.proj (F := ProjectiveSpinor) (E := Z.Fiber)) =>
      t.toOpenPartialHomeomorph) '' Set.range Z.localTriv at he
  change e' ∈ (fun t : Trivialization ProjectiveSpinor
      (Bundle.TotalSpace.proj (F := ProjectiveSpinor) (E := Z.Fiber)) =>
      t.toOpenPartialHomeomorph) '' Set.range Z.localTriv at he'
  rcases he with ⟨_, ⟨i, rfl⟩, rfl⟩
  rcases he' with ⟨_, ⟨j, rfl⟩, rfl⟩
  change ContMDiffOn productModel productModel ∞
    (↑((Z.localTriv i).toOpenPartialHomeomorph.symm.trans
      (Z.localTriv j).toOpenPartialHomeomorph))
    ((Z.localTriv i).toOpenPartialHomeomorph.symm.trans
      (Z.localTriv j).toOpenPartialHomeomorph).source
  have hsource :
      ((Z.localTriv i).toOpenPartialHomeomorph.symm.trans
        (Z.localTriv j).toOpenPartialHomeomorph).source =
        ((Z.baseSet i ∩ Z.baseSet j) ×ˢ Set.univ) := by
    ext p
    simp
  rw [hsource]
  have hsmooth : ContMDiffOn productModel productModel ∞
      (fun p : M × ProjectiveSpinor =>
        (p.1, spinorCoordChange Q i j p))
      ((Z.baseSet i ∩ Z.baseSet j) ×ˢ Set.univ) :=
    contMDiffOn_fst.prodMk (spinorCoordChange_contMDiffOn Q i j)
  apply hsmooth.congr
  intro p hp
  have hi : p.1 ∈ Z.baseSet i := hp.1.1
  have hj : p.1 ∈ Z.baseSet j := hp.1.2
  change ((Z.localTriv j).toOpenPartialHomeomorph
    ((Z.localTriv i).toOpenPartialHomeomorph.symm p)) =
      (p.1, Z.coordChange i j p.1 p.2)
  simp only [Z.localTriv_symm_apply]
  change (p.1, Z.coordChange (Z.indexAt p.1) j p.1
      (Z.coordChange i (Z.indexAt p.1) p.1 p.2)) =
    (p.1, Z.coordChange i j p.1 p.2)
  congr 1
  exact Z.coordChange_comp i (Z.indexAt p.1) j p.1
    ⟨⟨hi, Z.mem_baseSet_at _⟩, hj⟩ p.2

instance projectiveSpinorBundle_isManifold :
    IsManifold productModel ∞ (SpinorBundleTotal Q) := by
  letI : HasGroupoid (SpinorBundleTotal Q)
      (smoothProductPregroupoid (M := M)).groupoid :=
    bundle_hasSmoothProductGroupoid Q
  refine { StructureGroupoid.HasGroupoid.comp
    (smoothProductPregroupoid (M := M)).groupoid ?_ with }
  intro e he
  rw [mem_groupoid_of_pregroupoid] at he
  rwa [isLocalStructomorphOn_contDiffGroupoid_iff]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveManifold
