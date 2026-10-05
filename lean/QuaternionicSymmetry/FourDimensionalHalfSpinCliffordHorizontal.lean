import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSphere
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfScalar
import QuaternionicSymmetry.QuaternionicLeftLineAction
import QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex

/-! A quaternionic candidate for the local Clifford chart. For a nonzero
half-spin coordinate `v`, its unit quaternion `q` gives a real-linear
identification `x ↦ q* x`. Under it, the Hopf-selected horizontal complex
structure `q i q*` is multiplication by `i` on the target. The conjugate
dependence on `v` is proved explicitly; matching Hitchin's named
`V_-`, `V_+` complex modules is a separate representation-convention step. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinCliffordHorizontal

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinHopfScalar
  FourDimensionalHalfSpinQuaternionCoordinates
  ManifoldTwistorLocalAlmostComplex
  ManifoldTwistorSphereBundle
  QuaternionicLeftLineAction
  QuaternionicProjectiveStandardHilbertStructure
  QuaternionicUnitQuaternionTransport
  QuaternionicUnitScalarIsometries
  VectorBundleFrameTransitions.QuaternionicFrameReduction

noncomputable section

def rawCliffordChart (v : Spinor) (x : ℍ) : ℍ :=
  star (fromSpinor v) * x

theorem rawCliffordChart_smul (c : ℂ) (v : Spinor) (x : ℍ) :
    rawCliffordChart (c • v) x =
      star (c : ℍ) * rawCliffordChart v x := by
  rw [rawCliffordChart, rawCliffordChart, fromSpinor_smul, star_mul]
  exact mul_assoc _ _ _

def cliffordChart (v : Spinor) (hv : v ≠ 0) (x : ℍ) : ℍ :=
  star (spinorUnit v hv : ℍ) * x

theorem cliffordChart_complex (v : Spinor) (hv : v ≠ 0) (x : ℍ) :
    cliffordChart v hv
      (baseComplex leftLineStructure (hopfSphere v hv) x) =
    basisI * cliffordChart v hv x := by
  let q := spinorUnit v hv
  change star (q : ℍ) *
      (synth leftLineStructure (hopfSphere v hv).1 x) =
    basisI * (star (q : ℍ) * x)
  rw [← action_pureScalar]
  rw [pureScalar_hopfSphere]
  rw [action_eq_mul]
  change star (q : ℍ) * (((q : ℍ) * basisI * star (q : ℍ)) * x) =
    basisI * (star (q : ℍ) * x)
  calc
    star (q : ℍ) * (((q : ℍ) * basisI * star (q : ℍ)) * x) =
        (star (q : ℍ) * (q : ℍ)) *
          (basisI * (star (q : ℍ) * x)) := by simp only [mul_assoc]
    _ = basisI * (star (q : ℍ) * x) := by rw [q.property.1, one_mul]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinCliffordHorizontal
