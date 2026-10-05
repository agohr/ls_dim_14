import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTransitionDerivative
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartPointwiseOverlap
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredFixedChartDerivative
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredFixedTensor

/-! The pointwise projective almost-complex operator has the checked local
formula in EVERY actual fixed affine chart: its true total-space chart
differential intertwines it with the independent local CP¹ tensor. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartGlobalTensorConjugacy

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveFixedChartGerm
  FourDimensionalHalfSpinProjectiveFixedChartPointwiseOverlap
  FourDimensionalHalfSpinProjectiveFixedChartTransitionDerivative
  FourDimensionalHalfSpinProjectiveFixedChartTangentChain
  FourDimensionalHalfSpinProjectiveFixedChartLeftInverse
  FourDimensionalHalfSpinProjectivePreferredFixedChartDerivative
  FourDimensionalHalfSpinProjectivePreferredFixedTensor
  FourDimensionalHalfSpinProjectivePreferredChart
  FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS
  FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap
  FourDimensionalHalfSpinProjectiveScalarFiber
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveCore
  ComplexProjectiveTopology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev productModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)

theorem tangentComplex_fixedChart_conjugacy
    (p : M) (i : Fin 2) (z : SpinorBundleTotal Q)
    (hp : z.1 ∈ (extChartAt 𝓘(ℝ, ℍ) p).source)
    (hi : ((projectiveSpinorCore Q).localTriv (achart ℍ p) z).2 ∈
      affineDomain 1 i)
    (v : TangentSpace productModel z) :
    let c := fixedProjectiveChart Q p i z
    let A := mfderiv productModel 𝓘(ℝ, ℍ × ℂ)
      (fixedProjectiveChart Q p i) z
    A (tangentComplex Q D z v) =
      indexedLocalTensor Q D i p c.1 c.2 (A v) := by
  dsimp
  let q := z.1
  let j := preferredProjectiveChartIndex z.2
  let c := fixedProjectiveChart Q p i z
  let T := mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ)
    (fun t : ℍ × ℂ => fixedProjectiveChart Q q j
      (fixedProjectiveChartInv Q p i t)) c
  let A := mfderiv productModel 𝓘(ℝ, ℍ × ℂ)
    (fixedProjectiveChart Q p i) z
  let B := mfderiv productModel 𝓘(ℝ, ℍ × ℂ)
    (fixedProjectiveChart Q q j) z
  have hsrcp : z ∈ fixedChartSource Q p i :=
    mem_fixedChartSource Q p i z hp hi
  have hsrcq : z ∈ fixedChartSource Q q j := by
    apply mem_fixedChartSource Q q j z (mem_extChartAt_source z.1)
    rw [preferred_localTriv Q z]
    exact preferredProjectiveChartIndex_mem z.2
  have hchain : B = T.comp A :=
    fixedChart_mfderiv_transition_chain Q p q i j z hsrcp hsrcq
  obtain ⟨eT, heT⟩ :=
    fixedChart_transition_mfderiv_isInvertible Q p q i j z hsrcp hsrcq
  have hpoint : fixedProjectiveChartInv Q p i c = z :=
    fixedProjectiveChartInv_left Q p i z hp hi
  have htarget : fixedProjectiveChart Q q j
      (fixedProjectiveChartInv Q p i c) = fixedProjectiveChart Q q j z := by
    rw [hpoint]
  have hcov := fixed_chart_tensor_overlap_at_actual_point Q D p q i j z
    hp (mem_extChartAt_source z.1) hi
    (by rw [preferred_localTriv Q z]; exact preferredProjectiveChartIndex_mem z.2)
    (A v)
  have hcov' : T (indexedLocalTensor Q D i p c.1 c.2 (A v)) =
      indexedLocalTensor Q D j q
        (fixedProjectiveChart Q q j z).1
        (fixedProjectiveChart Q q j z).2 (T (A v)) := by
    simpa only [c, T, htarget] using hcov
  have hpre : B (tangentComplex Q D z v) =
      indexedLocalTensor Q D j q
        (fixedProjectiveChart Q q j z).1
        (fixedProjectiveChart Q q j z).2 (B v) := by
    dsimp only [B, q, j]
    rw [preferred_fixedChart_mfderiv Q z]
    rw [← preferredLocalModel_eq_indexed Q D z]
    simpa only [tangentComplex, LinearMap.comp_apply] using
      (projectiveTangentModelEquiv.apply_symm_apply
        (preferredLocalModel Q D z (projectiveTangentModelEquiv v)))
  have hTinj : Function.Injective T := by
    intro a b hab
    apply eT.injective
    have ha := congrArg (fun f : (ℍ × ℂ) →L[ℝ] (ℍ × ℂ) => f a) heT
    have hb := congrArg (fun f : (ℍ × ℂ) →L[ℝ] (ℍ × ℂ) => f b) heT
    exact ha.trans (hab.trans hb.symm)
  apply hTinj
  change T (A (tangentComplex Q D z v)) =
    T (indexedLocalTensor Q D i p c.1 c.2 (A v))
  calc
    T (A (tangentComplex Q D z v)) = B (tangentComplex Q D z v) := by
      rw [hchain]
      rfl
    _ = indexedLocalTensor Q D j q
          (fixedProjectiveChart Q q j z).1
          (fixedProjectiveChart Q q j z).2 (B v) := hpre
    _ = indexedLocalTensor Q D j q
          (fixedProjectiveChart Q q j z).1
          (fixedProjectiveChart Q q j z).2 (T (A v)) := by
      rw [hchain]
      rfl
    _ = T (indexedLocalTensor Q D i p c.1 c.2 (A v)) := hcov'.symm

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartGlobalTensorConjugacy
