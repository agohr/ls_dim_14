import QuaternionicSymmetry.ManifoldTwistorLocalComplexAmbientSmooth
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
/-! The tangent map of the genuine sphere inclusion gives a smooth
coefficient-valued map on the sphere tangent bundle. It agrees fiberwise
with the verified orthogonal-plane equivalence. -/
namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open scoped Manifold ContDiff
noncomputable section
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩
def sphereTangentAmbient (p : TangentBundle (𝓡 2) geometricSphere) : Fin 3 → ℝ :=
  EuclideanSpace.equiv (Fin 3) ℝ
    ((tangentMap (𝓡 2) 𝓘(ℝ,EuclideanThree)
      ((↑) : geometricSphere → EuclideanThree) p).2)
theorem sphereTangentAmbient_smooth :
    ContMDiff (𝓡 2).tangent 𝓘(ℝ,Fin 3 → ℝ) ∞ sphereTangentAmbient := by
  have hinc : ContMDiff (𝓡 2).tangent (𝓘(ℝ,EuclideanThree)).tangent ∞
      (tangentMap (𝓡 2) 𝓘(ℝ,EuclideanThree)
        ((↑) : geometricSphere → EuclideanThree)) :=
    (contMDiff_coe_sphere (m := ∞) (n := 2) (E := EuclideanThree)).contMDiff_tangentMap
      (by simp)
  exact (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.contMDiff.comp
    ((contMDiff_snd_tangentBundle_modelSpace EuclideanThree 𝓘(ℝ,EuclideanThree)).comp hinc)

theorem sphereTangentAmbient_eq_vertical (a : coefficientSphere)
    (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph a)) :
    sphereTangentAmbient
      (⟨coefficientSphereHomeomorph a, v⟩ :
        TangentBundle (𝓡 2) geometricSphere) =
      (sphereTangentVerticalEquiv a v).1 := by
  rfl
end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
