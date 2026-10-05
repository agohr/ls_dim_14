import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSphereInverseLocal
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfNorthSection
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfHomeomorph

/-! The explicit Hopf homeomorphism is a real C∞ diffeomorphism between
the genuine projective `CP¹` atlas and Mathlib's independently defined
round `S²` atlas. This does not yet compare their almost-complex tensors
or identify a global projective half-spin associated bundle. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfDiffeomorph

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinHopfHomeomorph
  FourDimensionalHalfSpinHopfProjectiveSmooth
  FourDimensionalHalfSpinHopfNorthSection
  FourDimensionalHalfSpinHopfSouthSection
  FourDimensionalHalfSpinHopfSphereInverseLocal
  FourDimensionalHalfSpinHopfLocalInverseRaw
open QuaternionicUnitQuaternionTransport
  QuaternionicUnitScalarIsometries
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorSphereBundle

noncomputable section

def projectiveHopfGeometricHomeomorph : ProjectiveSpinor ≃ₜ geometricSphere :=
  projectiveHopfHomeomorph.trans coefficientSphereHomeomorph

private theorem sphereQuaternion_eq (s : geometricSphere) :
    sphereQuaternion s = pureScalar (coefficientSphereHomeomorph.symm s).1 := rfl

private theorem inverse_eq_north (s : geometricSphere) (hs : s ∈ northDomain) :
    projectiveHopfGeometricHomeomorph.symm s =
      localProjective basisI (sphereQuaternion s) := by
  apply projectiveHopfGeometricHomeomorph.injective
  rw [projectiveHopfGeometricHomeomorph.apply_symm_apply]
  simp only [projectiveHopfGeometricHomeomorph, Homeomorph.trans_apply,
    projectiveHopfHomeomorph_apply]
  change s = projectiveHopfGeometric (localProjective basisI (sphereQuaternion s))
  rw [← coefficientSphereHomeomorph.apply_symm_apply s]
  change coefficientSphereHomeomorph (coefficientSphereHomeomorph.symm s) =
    coefficientSphereHomeomorph
      (projectiveHopf (localProjective basisI (sphereQuaternion s)))
  congr 1
  rw [sphereQuaternion_eq]
  exact (projectiveHopf_localNorth (coefficientSphereHomeomorph.symm s) hs).symm

private theorem inverse_eq_south (s : geometricSphere) (hs : s ∈ southDomain) :
    projectiveHopfGeometricHomeomorph.symm s =
      southProjective (sphereQuaternion s) := by
  apply projectiveHopfGeometricHomeomorph.injective
  rw [projectiveHopfGeometricHomeomorph.apply_symm_apply]
  simp only [projectiveHopfGeometricHomeomorph, Homeomorph.trans_apply,
    projectiveHopfHomeomorph_apply]
  change s = projectiveHopfGeometric (southProjective (sphereQuaternion s))
  rw [← coefficientSphereHomeomorph.apply_symm_apply s]
  change coefficientSphereHomeomorph (coefficientSphereHomeomorph.symm s) =
    coefficientSphereHomeomorph
      (projectiveHopf (southProjective (sphereQuaternion s)))
  congr 1
  rw [sphereQuaternion_eq]
  exact (projectiveHopf_localSouth (coefficientSphereHomeomorph.symm s) hs).symm

private theorem cover (s : geometricSphere) :
    s ∈ northDomain ∨ s ∈ southDomain := by
  by_cases hn : s ∈ northDomain
  · exact Or.inl hn
  right
  change sphereQuaternion s ≠ basisI
  intro h2
  have h1 : sphereQuaternion s = -basisI := by
    simpa only [northDomain, Set.mem_setOf_eq, not_ne_iff] using hn
  have hi : (-basisI : ℍ) = basisI := h1.symm.trans h2
  have him := congrArg (fun q : ℍ => q.imI) hi
  norm_num [basisI] at him

theorem projectiveHopfGeometric_inverse_contMDiff :
    ContMDiff (𝓡 2) 𝓘(ℝ,Fin 1 → ℂ) ∞
      projectiveHopfGeometricHomeomorph.symm := by
  intro s
  rcases cover s with hn | hs
  · have h := (northSphereSection_contMDiffOn.congr
      (fun y hy => inverse_eq_north y hy)).contMDiffAt
        (isOpen_northDomain.mem_nhds hn)
    exact h
  · have h := (southSphereSection_contMDiffOn.congr
      (fun y hy => inverse_eq_south y hy)).contMDiffAt
        (isOpen_southDomain.mem_nhds hs)
    exact h

theorem projectiveHopfGeometric_forward_contMDiff :
    ContMDiff 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) ∞
      projectiveHopfGeometricHomeomorph :=
  projectiveHopfGeometric_contMDiff

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfDiffeomorph
