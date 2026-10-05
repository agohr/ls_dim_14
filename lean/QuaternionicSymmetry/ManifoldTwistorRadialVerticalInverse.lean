import QuaternionicSymmetry.ManifoldTwistorRadialTangent
/-! On the actual sphere tangent plane, the derivative of the smooth
radial retraction is the inverse of the derivative of sphere inclusion.
The latter is the orthogonal-plane identification used by the twistor
vertical complex operator. -/
namespace QuaternionicSymmetry.ManifoldTwistorRadialRetraction
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open scoped Manifold ContDiff
noncomputable section
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

theorem radialDerivative_eq_verticalInverse (a : coefficientSphere)
  (w : verticalSubmodule a) :
  mfderiv 𝓘(ℝ,EuclideanThree) (𝓡 2) radial
      (sphereIntoNonzero (coefficientSphereHomeomorph a))
      ((EuclideanSpace.equiv (Fin 3) ℝ).symm w.1) =
    (sphereTangentVerticalEquiv a).symm w := by
  let v := (sphereTangentVerticalEquiv a).symm w
  have hv : sphereTangentVerticalEquiv a v = w :=
    (sphereTangentVerticalEquiv a).apply_symm_apply w
  have hderiv := sphereIntoNonzero_mfderiv (coefficientSphereHomeomorph a) v
  have hrad := radialTangent_left_inverse
    (⟨coefficientSphereHomeomorph a,v⟩ : TangentBundle (𝓡 2) geometricSphere)
  have hval := congrArg (fun p : TangentBundle (𝓡 2) geometricSphere => p.2) hrad
  simp only [tangentMap] at hval
  have hA : mfderiv (𝓡 2) 𝓘(ℝ,EuclideanThree)
      sphereIntoNonzero (coefficientSphereHomeomorph a) v =
      (EuclideanSpace.equiv (Fin 3) ℝ).symm w.1 := by
    rw [hderiv]
    have he := sphereTangentAmbient_eq_vertical a v
    rw [hv] at he
    have he' : (EuclideanSpace.equiv (Fin 3) ℝ)
        (mfderiv (𝓡 2) 𝓘(ℝ,EuclideanThree)
          ((↑) : geometricSphere → EuclideanThree)
          (coefficientSphereHomeomorph a) v) = w.1 := by
      simpa only [sphereTangentAmbient] using he
    have he'' := congrArg (EuclideanSpace.equiv (Fin 3) ℝ).symm he'
    simpa using he''
  rw [hA] at hval
  exact hval
end
end QuaternionicSymmetry.ManifoldTwistorRadialRetraction
