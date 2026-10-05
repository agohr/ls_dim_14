import QuaternionicSymmetry.ManifoldQuaternionicContactPowerSectionAction
import QuaternionicSymmetry.ManifoldQuaternionicIsometryContactIsotropy
import QuaternionicSymmetry.ManifoldQuaternionicVerticalComplexCharacter

/-! The preferred holomorphic contact-fiber scalar at a fixed point is
exactly the actual vertical isotropy scalar. No continuity of preferred
coordinates away from a fixed fiber is used. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicContactIsotropyScalar

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorVerticalAction
open ManifoldQuaternionicIsometryContactIsotropy
open ManifoldQuaternionicIsometryVerticalComplex
open ManifoldQuaternionicIsometryContactFiberEquiv
open ManifoldQuaternionicHolomorphicContactFiberAction
open ManifoldQuaternionicVerticalComplexCharacter
open ManifoldQuaternionicContactPowerSectionAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorGlobalAlmostComplex ManifoldTwistorVerticalComplex
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩
local instance (x : M) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore Q).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2)) geometricSphere
  infer_instance

def verticalCoefficientComplexEquiv
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (z : SphereBundleTotal Q) :
    letI := verticalComplexModule Q D z
    letI := coefficientVerticalComplexModule (coefficientSphereHomeomorph.symm z.2)
    verticalTangentSubmodule Q z ≃ₗ[ℂ]
      verticalSubmodule (coefficientSphereHomeomorph.symm z.2) := by
  letI := verticalComplexModule Q D z
  letI := coefficientVerticalComplexModule (coefficientSphereHomeomorph.symm z.2)
  exact { verticalTangentEquiv Q z with
    map_smul' := by
      intro c v
      change verticalTangentEquiv Q z (verticalComplexSmul Q D z c v) =
        coefficientVerticalComplexSmul (coefficientSphereHomeomorph.symm z.2) c
          (verticalTangentEquiv Q z v)
      simp only [verticalComplexSmul, coefficientVerticalComplexSmul, map_add, map_smul]
      rw [verticalTangentEquiv_complex] }

def contactCoefficientComplexEquiv
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} {B : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n B) (z : SphereBundleTotal Q) :
    letI := coefficientVerticalComplexModule (coefficientSphereHomeomorph.symm z.2)
    L.core.Fiber z ≃ₗ[ℂ]
      verticalSubmodule (coefficientSphereHomeomorph.symm z.2) := by
  letI := contactQuotientComplexModule Q D z
  letI := verticalComplexModule Q D z
  letI := coefficientVerticalComplexModule (coefficientSphereHomeomorph.symm z.2)
  exact (L.quotientEquiv z).trans
    ((contactQuotientComplexEquiv Q D z).trans (verticalCoefficientComplexEquiv Q D z))

theorem contactScalar_eq_verticalScalar
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} {B : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n B)
    (z : SphereBundleTotal Q) (f : QuaternionicIsometries Q)
    (hz : f • z = z) :
    contactScalar Q D L f z = verticalScalar Q z ⟨f,hz⟩ := by
  letI := contactQuotientComplexModule Q D z
  letI := contactQuotientComplexModule Q D (sphereTotalMap Q f z)
  letI := coefficientVerticalComplexModule (coefficientSphereHomeomorph.symm z.2)
  have h := isotropy_contact_weight_complex Q D z ⟨f,hz⟩ (L.quotientEquiv z (1 : ℂ))
  rw [ManifoldQuaternionicVerticalComplexCharacter.isotropyVerticalRepresentation_eq_verticalScalar] at h
  rw [← quotientEquiv_contactLineFiberMap Q D L f z (1 : ℂ)] at h
  change (contactCoefficientComplexEquiv Q D L (sphereTotalMap Q f z)
      (contactScalar Q D L f z)).1 =
    (coefficientVerticalComplexSmul (coefficientSphereHomeomorph.symm z.2)
      (verticalScalar Q z ⟨f,hz⟩) (contactCoefficientComplexEquiv Q D L z (1 : ℂ))).1 at h
  have hz' : sphereTotalMap Q f z = z := hz
  rw [hz'] at h
  have heq : contactCoefficientComplexEquiv Q D L z (contactScalar Q D L f z) =
      verticalScalar Q z ⟨f,hz⟩ • contactCoefficientComplexEquiv Q D L z (1 : ℂ) :=
    Subtype.ext h
  rw [← map_smul] at heq
  have hc := (contactCoefficientComplexEquiv Q D L z).injective heq
  simpa only [smul_eq_mul, mul_one] using hc

end
end QuaternionicSymmetry.ManifoldQuaternionicContactIsotropyScalar
