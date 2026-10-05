import QuaternionicSymmetry.ManifoldTwistorRadialInverseSmooth

/-!
# Smooth vertical complex structure on the geometric twistor sphere

The cross-product complex structure on the orthogonal plane of each unit
coefficient vector is realized on the actual tangent bundle of the smooth
two-sphere.  Radial retraction supplies a smooth inverse to the tangent map
of the sphere inclusion.
-/

namespace QuaternionicSymmetry.ManifoldTwistorRadialRetraction

open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open scoped Manifold ContDiff

noncomputable section

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

def smoothVerticalComplexMap (p : TangentBundle (𝓡 2) geometricSphere) :
    TangentBundle (𝓡 2) geometricSphere :=
  radialTangentMap
    (p.1, (EuclideanSpace.equiv (Fin 3) ℝ).symm
      (crossProduct (coefficientSphereHomeomorph.symm p.1).1
        (sphereTangentAmbient p)))

theorem smoothVerticalComplexMap_smooth :
    ContMDiff (𝓡 2).tangent (𝓡 2).tangent ∞ smoothVerticalComplexMap := by
  have hproj : ContMDiff (𝓡 2).tangent (𝓡 2) ∞
      (fun p : TangentBundle (𝓡 2) geometricSphere => p.1) :=
    Bundle.contMDiff_proj (TangentSpace (𝓡 2))
  have hcoef : ContMDiff (𝓡 2).tangent 𝓘(ℝ,Fin 3 → ℝ) ∞
      (fun p : TangentBundle (𝓡 2) geometricSphere =>
        crossProduct (coefficientSphereHomeomorph.symm p.1).1
          (sphereTangentAmbient p)) :=
    sphereCrossSmooth.comp (hproj.prodMk sphereTangentAmbient_smooth)
  exact radialTangentMap_smooth.comp
    (hproj.prodMk ((EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.contMDiff.comp hcoef))

theorem smoothVerticalComplexMap_eq (a : coefficientSphere)
    (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph a)) :
    smoothVerticalComplexMap
      (⟨coefficientSphereHomeomorph a, v⟩ : TangentBundle (𝓡 2) geometricSphere) =
    (⟨coefficientSphereHomeomorph a, sphereVerticalComplex a v⟩ :
      TangentBundle (𝓡 2) geometricSphere) := by
  apply Bundle.TotalSpace.ext
  · rfl
  · apply heq_of_eq
    simp only [smoothVerticalComplexMap, radialTangentMap,
      Homeomorph.symm_apply_apply]
    change mfderiv 𝓘(ℝ,EuclideanThree) (𝓡 2) radial
        (sphereIntoNonzero (coefficientSphereHomeomorph a))
        ((EuclideanSpace.equiv (Fin 3) ℝ).symm
          (crossProduct a.1 (sphereTangentAmbient
            (⟨coefficientSphereHomeomorph a, v⟩ : TangentBundle (𝓡 2) geometricSphere)))) =
      sphereVerticalComplex a v
    rw [sphereTangentAmbient_eq_vertical]
    have h := radialDerivative_eq_verticalInverse a
      (verticalComplex a (sphereTangentVerticalEquiv a v))
    simpa [verticalComplex, sphereVerticalComplex] using h

end
end QuaternionicSymmetry.ManifoldTwistorRadialRetraction
