import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveScalarFiber
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondTensor

/-! A pointwise almost-complex operator on the actual tangent fibers of
the independently constructed projective-spinor total space. It uses
the actual CP¹ chart selected at each projective point and the checked
real-linear scalar coordinate equivalence. Smooth dependence and the
identification with the source AHS object are separate obligations. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveScalarFiber
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveSecondTensor
  FourDimensionalHalfSpinProjective
  ComplexProjectiveTopology
  ManifoldTwistorLocalAlmostComplex
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

private abbrev productModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)

def preferredProjectiveChartIndex (s : ProjectiveSpinor) : Fin 2 :=
  Classical.choose (exists_mem_affineDomain 1 s)

theorem preferredProjectiveChartIndex_mem (s : ProjectiveSpinor) :
    s ∈ affineDomain 1 (preferredProjectiveChartIndex s) :=
  Classical.choose_spec (exists_mem_affineDomain 1 s)

def preferredProjectiveScalar (s : ProjectiveSpinor) : ℂ :=
  (projectiveChart 1 (preferredProjectiveChartIndex s) s) 0

def preferredLocalModel (z : SpinorBundleTotal Q) :
    (ℍ × ℂ) →ₗ[ℝ] (ℍ × ℂ) :=
  let y := extChartAt 𝓘(ℝ, ℍ) z.1 z.1
  let w := preferredProjectiveScalar z.2
  if preferredProjectiveChartIndex z.2 = 0 then
    localActualProjectiveAHS Q D z.1 y w
  else
    secondLocalActualProjectiveAHS Q D z.1 y w

theorem preferredLocalModel_sq (z : SpinorBundleTotal Q) (v : ℍ × ℂ) :
    preferredLocalModel Q D z (preferredLocalModel Q D z v) = -v := by
  have hy : extChartAt 𝓘(ℝ, ℍ) z.1 z.1 ∈
      (extChartAt 𝓘(ℝ, ℍ) z.1).target :=
    (extChartAt 𝓘(ℝ, ℍ) z.1).map_source (mem_extChartAt_source z.1)
  unfold preferredLocalModel
  split_ifs
  · exact localActualProjectiveAHS_sq Q D z.1 _ hy _ v
  · exact secondLocalActualProjectiveAHS_sq Q D z.1 _ hy _ v

def tangentComplex (z : SpinorBundleTotal Q) :
    TangentSpace productModel z →ₗ[ℝ]
      TangentSpace productModel z :=
  projectiveTangentModelEquiv.symm.toLinearMap.comp
    ((preferredLocalModel Q D z).comp
      projectiveTangentModelEquiv.toLinearMap)

theorem tangentComplex_sq (z : SpinorBundleTotal Q)
    (v : TangentSpace productModel z) :
    tangentComplex Q D z (tangentComplex Q D z v) = -v := by
  apply projectiveTangentModelEquiv.injective
  simpa [tangentComplex] using
    preferredLocalModel_sq Q D z (projectiveTangentModelEquiv v)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS
