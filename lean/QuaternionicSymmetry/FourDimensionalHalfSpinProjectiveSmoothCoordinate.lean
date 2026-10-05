import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBundleHomeomorphism

/-! Exact local product-chart expression of the global associated-bundle
Hopf map. The fiber map in these genuine bundle charts is the independently
proved CP¹-to-round-sphere diffeomorphism, uniformly over the base. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSmoothCoordinate

open scoped ContDiff Manifold Quaternion
open FourDimensionalHalfSpinProjectiveCore
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveBundleEquiv
  FourDimensionalHalfSpinProjectiveBundleHomeomorphism
  FourDimensionalHalfSpinHopfProjectiveSmooth
  FourDimensionalHalfSpinProjective
  ManifoldTwistorSphereCore
  ManifoldTwistorCoefficientSphere

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

def productHopf (p : M × ProjectiveSpinor) : M × geometricSphere :=
  (p.1, projectiveHopfGeometric p.2)

theorem productHopf_contMDiff :
    ContMDiff (𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ))
      (𝓘(ℝ, ℍ).prod (𝓡 2)) ∞ (productHopf (M := M)) := by
  have hfst : ContMDiff
      (𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)) 𝓘(ℝ, ℍ) ∞
      (fun p : M × ProjectiveSpinor => p.1) := contMDiff_fst
  have hsnd : ContMDiff
      (𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)) (𝓡 2) ∞
      (fun p : M × ProjectiveSpinor => projectiveHopfGeometric p.2) :=
    FourDimensionalHalfSpinHopfDiffeomorphPackage.projectiveHopfGeometricDiffeomorph.contMDiff_toFun.comp
      contMDiff_snd
  exact hfst.prodMk hsnd

theorem product_chart_hopf (p q : SpinorBundleTotal Q)
    (hq : q ∈ (chartAt (M × ProjectiveSpinor) p).source) :
    (chartAt (M × geometricSphere) (spinorToSphere Q p))
      (spinorToSphere Q q) =
      productHopf ((chartAt (M × ProjectiveSpinor) p) q) := by
  rw [FiberBundle.chartedSpace'_chartAt,
    FiberBundle.chartedSpace'_chartAt]
  let Zp := projectiveSpinorCore Q
  let Zs := sphereCore Q
  have hi : q.1 ∈ Zp.baseSet (Zp.indexAt p.1) := by
    simpa only [FiberBundle.chartedSpace'_chartAt] using hq
  apply Prod.ext
  · rfl
  · exact localTriv_hopf Q (Zp.indexAt p.1) q hi

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSmoothCoordinate
