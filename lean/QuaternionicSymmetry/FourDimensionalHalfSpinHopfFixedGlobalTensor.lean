import QuaternionicSymmetry.FourDimensionalHalfSpinHopfAllRawTensor
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleMFDeriv
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartGlobalTensorConjugacy
import QuaternionicSymmetry.ManifoldTwistorGlobalComplexSmooth
import QuaternionicSymmetry.ManifoldTwistorRawChartConjugacy

/-! Global-tangent corrected-Hopf complex intertwining on the source of
an arbitrary actual fixed affine projective chart. Both affine indices
are handled by the independently checked local derivative identities. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfFixedGlobalTensor

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinHopfAllRawTensor
  FourDimensionalHalfSpinProjectiveCorrectedBundleMFDeriv
  FourDimensionalHalfSpinProjectiveCorrectedBundleChart
  FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative
  FourDimensionalHalfSpinProjectiveCorrectedBundleDiffeomorph
  FourDimensionalHalfSpinProjectiveFixedChartGlobalTensorConjugacy
  FourDimensionalHalfSpinProjectiveFixedChartGerm
  FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveFixedChartTarget
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveCore
  FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap
  ComplexProjectiveTopology
  ManifoldTwistorGlobalAlmostComplex
  ManifoldTwistorSphereBundle
  ManifoldTwistorSphereCore
  ManifoldQuaternionicReduction
  ManifoldQuaternionicMetric

noncomputable section

private abbrev projectiveModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)
private abbrev sphereModel := 𝓘(ℝ, ℍ).prod (𝓡 2)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem correctedHopf_fixedChart_globalTensor
    (p : M) (i : Fin 2) (z : SpinorBundleTotal Q)
    (hp : z.1 ∈ (extChartAt 𝓘(ℝ, ℍ) p).source)
    (hi : ((projectiveSpinorCore Q).localTriv (achart ℍ p) z).2 ∈
      affineDomain 1 i)
    (v : TangentSpace projectiveModel z) :
    let f := correctedSpinorSphereDiffeomorph Q
    let F := mfderiv projectiveModel sphereModel f z
    F (FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS.tangentComplex Q D z v) =
      tangentComplex Q D (f z) (F v) := by
  dsimp only
  let f := correctedSpinorSphereDiffeomorph Q
  let zz := f z
  let c := fixedProjectiveChart Q p i z
  let A := mfderiv projectiveModel 𝓘(ℝ, ℍ × ℂ)
    (fixedProjectiveChart Q p i) z
  let H := mfderiv 𝓘(ℝ, ℍ × ℂ) sphereModel (fixedCorrectedHopf i) c
  let B := mfderiv sphereModel sphereModel (fixedRawChart Q p) zz
  let F := mfderiv projectiveModel sphereModel f z
  have hz : z ∈ fixedChartSource Q p i :=
    mem_fixedChartSource Q p i z hp hi
  have hchain : B.comp F = H.comp A := by
    exact correctedHopf_fixedChart_mfderiv_chain Q p i z hz
  have hval : fixedRawChart Q p zz = fixedCorrectedHopf i c := by
    exact fixedRawChart_correctedHopf Q p i z hz
  have hrawsrc : zz ∈
      ((sphereCore Q).localTriv (achart ℍ p)).toOpenPartialHomeomorph.source := by
    apply ((sphereCore Q).mem_localTriv_source (achart ℍ p) zz).mpr
    have hbase : z.1 ∈ (projectiveSpinorCore Q).baseSet (achart ℍ p) :=
      ((projectiveSpinorCore Q).mem_localTriv_source (achart ℍ p) z).mp hz.1
    simpa only [correctedSpinorSphereDiffeomorph_base] using hbase
  have hc : c ∈ fixedChartTarget Q p i :=
    fixedChart_mem_target Q p i z hz
  have hsource (w : TangentSpace projectiveModel z) :
      A (FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS.tangentComplex
        Q D z w) = indexedLocalTensor Q D i p c.1 c.2 (A w) := by
    exact tangentComplex_fixedChart_conjugacy Q D p i z hp hi w
  have hraw (w : TangentSpace projectiveModel z) :
      rawTangentCoordinates Q p ⟨zz,F w⟩ =
      ((c.1,(H (A w)).1),
        ⟨indexedCorrectedHopf i c.2,(H (A w)).2⟩) := by
    have hw := congrArg (fun L : TangentSpace projectiveModel z →L[ℝ]
      TangentSpace sphereModel (fixedRawChart Q p zz) => L w) hchain
    change B (F w) = H (A w) at hw
    simp only [rawTangentCoordinates, productTangentCoordinates,
      tangentMap, hval]
    rw [hw]
    rw [hval]
    rfl
  have hlocal := fixedCorrectedHopf_allRawTensor_mfderiv Q D i p c hc (A v)
  dsimp only at hlocal
  have hH : H = mfderiv (𝓘(ℝ,ℍ).prod 𝓘(ℝ,ℂ))
      (𝓘(ℝ,ℍ).prod (𝓡 2)) (fixedCorrectedHopf i) c := by
    dsimp only [H, sphereModel]
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  have hsphere := tangentComplex_rawChart_conjugacy Q D p zz hrawsrc (F v)
  have heq : rawTangentCoordinates Q p
      ⟨zz, F (FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS.tangentComplex
        Q D z v)⟩ =
      rawTangentCoordinates Q p ⟨zz,tangentComplex Q D zz (F v)⟩ := by
    rw [hsphere, hraw, hraw]
    rw [hsource]
    rw [hH]
    exact hlocal.symm
  have hleft := rawTangentCoordinatesInv_left Q p zz hrawsrc
    (F (FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS.tangentComplex Q D z v))
  have hright := rawTangentCoordinatesInv_left Q p zz hrawsrc
    (tangentComplex Q D zz (F v))
  rw [heq] at hleft
  have ht := hleft.symm.trans hright
  exact congrArg Bundle.TotalSpace.snd ht

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfFixedGlobalTensor
