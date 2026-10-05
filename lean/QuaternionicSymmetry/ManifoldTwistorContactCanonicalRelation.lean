import QuaternionicSymmetry.ManifoldTwistorAnticanonicalCore
import QuaternionicSymmetry.HolomorphicLinePowers
import QuaternionicSymmetry.ManifoldTwistorLeBrunContactNondegenerate

/-! The exact target of the complex-contact canonical-bundle formula on
the actual twistor complex manifold. Both sides are now genuine
holomorphic complex-line bundle cores: the left side is det(TZ), the
right side is the (n+1)-st tensor power of the contact line. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

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

/-- A fiberwise complex-linear identification of the actual
anticanonical line with the (n+1)-st contact-line tensor power, whose
forward and inverse maps are holomorphic on the genuine bundle total
spaces. This is the geometric conclusion of the general complex-contact
canonical-line theorem. -/
structure HolomorphicContactCanonicalIso (n : ℕ)
    (A : CompatibleComplexAtlas Q D n)
    (L : HolomorphicContactLine Q D n A) where
  fiberEquiv : letI := A.charts
    ∀ z : SphereBundleTotal Q,
      (A.anticanonicalCore Q D).Fiber z ≃ₗ[ℂ]
        (L.canonicalPowerCore Q D).Fiber z
  holomorphicForward : letI := A.charts
    letI := A.complexManifold
    letI := A.anticanonicalCore_holomorphic Q D
    letI := L.canonicalPowerCore_holomorphic Q D
    ContMDiff ((𝓘(ℂ,ComplexTwistorModel n)).prod 𝓘(ℂ,ℂ))
      ((𝓘(ℂ,ComplexTwistorModel n)).prod 𝓘(ℂ,ℂ)) ∞
      (fun t : Bundle.TotalSpace ℂ (A.anticanonicalCore Q D).Fiber =>
        (⟨t.1, fiberEquiv t.1 t.2⟩ :
          Bundle.TotalSpace ℂ (L.canonicalPowerCore Q D).Fiber))
  holomorphicBackward : letI := A.charts
    letI := A.complexManifold
    letI := A.anticanonicalCore_holomorphic Q D
    letI := L.canonicalPowerCore_holomorphic Q D
    ContMDiff ((𝓘(ℂ,ComplexTwistorModel n)).prod 𝓘(ℂ,ℂ))
      ((𝓘(ℂ,ComplexTwistorModel n)).prod 𝓘(ℂ,ℂ)) ∞
      (fun t : Bundle.TotalSpace ℂ (L.canonicalPowerCore Q D).Fiber =>
        (⟨t.1, (fiberEquiv t.1).symm t.2⟩ :
          Bundle.TotalSpace ℂ (A.anticanonicalCore Q D).Fiber))

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
