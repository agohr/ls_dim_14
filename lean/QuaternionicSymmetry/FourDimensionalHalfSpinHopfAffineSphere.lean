import QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineSmooth
import QuaternionicSymmetry.ManifoldTwistorCoefficientSphere

/-! The explicit Hopf formula in each genuine `CP¹` affine chart lands
smoothly in the independently charted Euclidean unit two-sphere. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineSphere

open scoped Quaternion ContDiff Manifold
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinQuaternionCoordinates
  FourDimensionalHalfSpinHopfRaw
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinHopfNormalization
  FourDimensionalHalfSpinHopfAffineSmooth
open ComplexProjectiveTopology
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorSphereBundle

noncomputable section

private def imaginaryCoordsLinear : ℍ →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun q := ![q.imI, q.imJ, q.imK]
  map_add' p q := by ext j; fin_cases j <;> simp
  map_smul' r q := by ext j; fin_cases j <;> simp

private def affineQuaternion (i : Fin 2) (w : Fin 1 → ℂ) : ℍ :=
  (Quaternion.normSq (fromSpinor (homogeneousVector 1 i w)))⁻¹ •
    hopfRaw (homogeneousVector 1 i w)

private theorem contDiff_affineQuaternion (i : Fin 2) :
    ContDiff ℝ ∞ (affineQuaternion i) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  exact contDiffAt_affineHopfQuaternion i w

private theorem affineQuaternion_eq (i : Fin 2) (w : Fin 1 → ℂ) :
    affineQuaternion i w =
      hopfQuaternion (homogeneousVector 1 i w)
        (homogeneousVector_ne_zero 1 i w) :=
  (hopfQuaternion_eq_ratio _ _).symm

def affineEuclideanHopf (i : Fin 2) (w : Fin 1 → ℂ) : EuclideanThree :=
  toEuclidean (imaginaryCoordsLinear (affineQuaternion i w))

private theorem contDiff_affineEuclideanHopf (i : Fin 2) :
    ContDiff ℝ ∞ (affineEuclideanHopf i) := by
  exact ((EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.contDiff.comp
    (imaginaryCoordsLinear.toContinuousLinearMap.contDiff.comp
      (contDiff_affineQuaternion i)))

theorem affineEuclideanHopf_mem (i : Fin 2) (w : Fin 1 → ℂ) :
    affineEuclideanHopf i w ∈ geometricSphere := by
  have h := (hopfSphere (homogeneousVector 1 i w)
    (homogeneousVector_ne_zero 1 i w)).2
  apply (mem_geometricSphere _).2
  convert h using 1
  simp [affineQuaternion_eq, imaginaryCoordsLinear, hopfSphere]

def affineSphere (i : Fin 2) (w : Fin 1 → ℂ) : geometricSphere :=
  ⟨affineEuclideanHopf i w, affineEuclideanHopf_mem i w⟩

theorem affineSphere_eq_hopf (i : Fin 2) (w : Fin 1 → ℂ) :
    affineSphere i w = coefficientSphereHomeomorph
      (hopfSphere (homogeneousVector 1 i w)
        (homogeneousVector_ne_zero 1 i w)) := by
  apply Subtype.ext
  simp [affineSphere, affineEuclideanHopf, affineQuaternion_eq,
    imaginaryCoordsLinear, coefficientSphereHomeomorph,
    hopfSphere]

/-- A real C∞ map from each actual affine coordinate plane to the actual
Euclidean unit sphere, equal to the normalized projective Hopf formula. -/
theorem contMDiff_affineSphere (i : Fin 2) :
    ContMDiff 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) ∞
      (affineSphere i) := by
  haveI : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) :=
    ⟨by simp [EuclideanThree]⟩
  exact (contDiff_affineEuclideanHopf i).contMDiff.codRestrict_sphere
    (affineEuclideanHopf_mem i)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineSphere
