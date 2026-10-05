import QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
import QuaternionicSymmetry.ManifoldTwistorContactQuotientNaturality

/-! The holomorphic contact-line part of LeBrun's twistor theorem is
represented by an actual complex vector-bundle core over the already
constructed sphere total space. Its comparison with the differential-
geometric quotient is fiberwise. Existence of this data is precisely a
source theorem input; no holomorphic splitting is asserted. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

private abbrev RealModel := (𝓘(ℝ,E)).prod (𝓡 2)

/-- A holomorphic complex line with the actual contact quotient as its
underlying complex fiber. The complex atlas and horizontal distribution
are fixed by the previously checked twistor construction. -/
structure HolomorphicContactLine (n : ℕ) (A : CompatibleComplexAtlas Q D n) where
  Index : Type
  core : VectorBundleCore ℂ (SphereBundleTotal Q) ℂ Index
  holomorphic : letI := A.charts
    core.IsContMDiff 𝓘(ℂ, ComplexTwistorModel n) ∞
  quotientEquiv : ∀ z,
    letI := contactQuotientComplexModule Q D z
    core.Fiber z ≃ₗ[ℂ]
      (TangentSpace (RealModel (E := E)) z ⧸ horizontalTangentSubmodule Q D z)

theorem contactQuotient_real_smul (z : SphereBundleTotal Q) (r : ℝ)
    (v : TangentSpace (RealModel (E := E)) z ⧸ horizontalTangentSubmodule Q D z) :
    letI := contactQuotientComplexModule Q D z
    (r : ℂ) • v = r • v := by
  letI := verticalComplexModule Q D z
  letI := contactQuotientComplexModule Q D z
  apply (contactQuotientEquiv Q D z).injective
  calc
    (contactQuotientEquiv Q D z) ((r : ℂ) • v) =
        (r : ℂ) • (contactQuotientEquiv Q D z v) :=
      (contactQuotientComplexEquiv Q D z).map_smul _ _
    _ = r • (contactQuotientEquiv Q D z v) :=
      verticalComplexSmul_real Q D z r _
    _ = (contactQuotientEquiv Q D z) (r • v) := by rw [map_smul]

/-- The contact form as a real-linear fiber map. Its kernel is exactly
the checked connection-horizontal plane. -/
def HolomorphicContactLine.contactFormReal {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (z : SphereBundleTotal Q) :
    TangentSpace (RealModel (E := E)) z →ₗ[ℝ] L.core.Fiber z := by
  letI := contactQuotientComplexModule Q D z
  letI : IsScalarTower ℝ ℂ
      (TangentSpace (RealModel (E := E)) z ⧸ horizontalTangentSubmodule Q D z) := ⟨by
    intro r c v
    rw [show r • c = (r : ℂ) * c by simp, mul_smul,
      contactQuotient_real_smul Q D z]⟩
  exact (L.quotientEquiv z).symm.restrictScalars ℝ |>.toLinearMap.comp
    (horizontalTangentSubmodule Q D z).mkQ

theorem HolomorphicContactLine.contactFormReal_ker {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (z : SphereBundleTotal Q) :
    LinearMap.ker (L.contactFormReal Q D z) = horizontalTangentSubmodule Q D z := by
  letI := contactQuotientComplexModule Q D z
  ext v
  simp [HolomorphicContactLine.contactFormReal]

/-- The source contact form is of complex type with respect to the
checked global almost-complex structure and the complex line fiber. -/
theorem HolomorphicContactLine.contactFormReal_i {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (z : SphereBundleTotal Q) (v : TangentSpace (RealModel (E := E)) z) :
    L.contactFormReal Q D z (tangentComplex Q D z v) =
      Complex.I • L.contactFormReal Q D z v := by
  letI := contactQuotientComplexModule Q D z
  apply (L.quotientEquiv z).injective
  simp only [HolomorphicContactLine.contactFormReal, LinearMap.comp_apply, map_smul]
  rw [← contactQuotientTangentComplex_eq_i_smul Q D z]
  simp [contactQuotientTangentComplex]

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
