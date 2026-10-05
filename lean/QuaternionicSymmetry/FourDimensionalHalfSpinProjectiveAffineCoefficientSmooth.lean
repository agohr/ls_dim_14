import QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineSphere
import QuaternionicSymmetry.FourDimensionalHalfSpinAntipodalVerticalSign

/-! A source-free C∞ ambient-coordinate form of the antipodal Hopf
coefficient on each genuine CP¹ affine chart.  This is the coefficient
used by the independent local projective AHS formula. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAffineCoefficientSmooth

open scoped Manifold ContDiff
open FourDimensionalHalfSpinHopfAffineSphere
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinAntipodalVerticalSign
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorSphereBundle
  ComplexProjectiveTopology

noncomputable section

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

def affineAntipodalVector (i : Fin 2) (w : Fin 1 → ℂ) : Fin 3 → ℝ :=
  -(EuclideanSpace.equiv (Fin 3) ℝ (affineSphere i w).1)

theorem affineAntipodalVector_smooth (i : Fin 2) :
    ContDiff ℝ ∞ (affineAntipodalVector i) := by
  have hs : ContMDiff 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, EuclideanThree) ∞
      (fun w => (affineSphere i w).1) :=
    (contMDiff_coe_sphere (n := 2) (E := EuclideanThree)).comp
      (contMDiff_affineSphere i)
  have hv : ContDiff ℝ ∞
      (fun w : Fin 1 → ℂ =>
        EuclideanSpace.equiv (Fin 3) ℝ (affineSphere i w).1) :=
    (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.contDiff.comp
      hs.contDiff
  exact hv.neg

theorem affineAntipodalVector_eq_hopf (i : Fin 2) (w : Fin 1 → ℂ) :
    affineAntipodalVector i w =
      (antipodalCoefficient
        (hopfSphere (homogeneousVector 1 i w)
          (homogeneousVector_ne_zero 1 i w))).1 := by
  unfold affineAntipodalVector
  rw [affineSphere_eq_hopf]
  rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAffineCoefficientSmooth
