import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSouthSmooth
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfProjectiveSmooth

/-! Compose the two explicit local inverse formulas with the independently
smooth Euclidean sphere inclusion. The resulting maps are smooth on the
genuine complementary open subsets of the round sphere. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfSphereInverseLocal

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfLocalInverseRaw
  FourDimensionalHalfSpinHopfSouthSection
  FourDimensionalHalfSpinHopfSouthSmooth
open QuaternionicUnitQuaternionTransport
  QuaternionicUnitScalarIsometries
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorSphereBundle

noncomputable section

private def pureScalarLinear : (Fin 3 → ℝ) →ₗ[ℝ] ℍ where
  toFun := pureScalar
  map_add' a b := by ext <;> simp [pureScalar]
  map_smul' r a := by ext <;> simp [pureScalar]

def sphereQuaternion (s : geometricSphere) : ℍ :=
  pureScalar ((EuclideanSpace.equiv (Fin 3) ℝ) s.1)

theorem sphereQuaternion_contMDiff :
    ContMDiff (𝓡 2) 𝓘(ℝ,ℍ) ∞ sphereQuaternion := by
  haveI : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) :=
    ⟨by simp [EuclideanThree]⟩
  have hcoe : ContMDiff (𝓡 2) 𝓘(ℝ,EuclideanThree) ∞
      (fun s : geometricSphere => (s : EuclideanThree)) :=
    contMDiff_coe_sphere
  have hcoord :=
    (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.contDiff.contMDiff.comp hcoe
  exact pureScalarLinear.toContinuousLinearMap.contDiff.contMDiff.comp hcoord

def northDomain : Set geometricSphere :=
  {s | sphereQuaternion s ≠ -basisI}

def southDomain : Set geometricSphere :=
  {s | sphereQuaternion s ≠ basisI}

theorem isOpen_northDomain : IsOpen northDomain :=
  isOpen_ne.preimage sphereQuaternion_contMDiff.continuous

theorem isOpen_southDomain : IsOpen southDomain :=
  isOpen_ne.preimage sphereQuaternion_contMDiff.continuous

theorem northSphereSection_contMDiffOn :
    ContMDiffOn (𝓡 2) 𝓘(ℝ,Fin 1 → ℂ) ∞
      (fun s : geometricSphere => localProjective basisI (sphereQuaternion s))
      northDomain := by
  have hs := FourDimensionalHalfSpinHopfLocalInverseRaw.localProjective_contMDiffOn
    basisI (imaginaryUnit_sq basisI basisI_unit.1 basisI_unit.2)
  exact hs.comp sphereQuaternion_contMDiff.contMDiffOn (fun s hs => hs)

theorem southSphereSection_contMDiffOn :
    ContMDiffOn (𝓡 2) 𝓘(ℝ,Fin 1 → ℂ) ∞
      (fun s : geometricSphere => southProjective (sphereQuaternion s))
      southDomain := by
  exact southProjective_contMDiffOn.comp
    sphereQuaternion_contMDiff.contMDiffOn (fun s hs => hs)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfSphereInverseLocal
