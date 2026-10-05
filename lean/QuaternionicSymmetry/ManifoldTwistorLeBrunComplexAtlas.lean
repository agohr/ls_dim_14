import QuaternionicSymmetry.ManifoldTwistorContactHorizontalLiftSmooth
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerHomothety

/-! A precise geometric target for the complex-atlas part of LeBrun's
positive quaternionic-Kähler twistor theorem. This is source theorem data,
not an internally proved integrability theorem: the underlying smooth
sphere bundle and its almost-complex endomorphism have already been built.
The compatibility law below requires the source complex atlas to realize
that exact endomorphism on the actual real tangent bundle. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

/-- Complex model dimension of the twistor of a quaternionic `n`-fold. -/
abbrev ComplexTwistorModel (n : ℕ) := EuclideanSpace ℂ (Fin (2*n+1))

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

private abbrev RealModel := (𝓘(ℝ,E)).prod (𝓡 2)

/-- The exact complex-manifold part of the cited twistor theorem. In
particular, the complex charts must be smoothly compatible in both
directions with the already constructed real smooth sphere bundle, and
their multiplication by `i` must be the checked global twistor operator. -/
structure CompatibleComplexAtlas (n : ℕ) where
  charts : ChartedSpace (ComplexTwistorModel n) (SphereBundleTotal Q)
  complexManifold : letI := charts
    IsManifold 𝓘(ℂ,ComplexTwistorModel n) ∞ (SphereBundleTotal Q)
  realManifold : letI := charts
    IsManifold 𝓘(ℝ,ComplexTwistorModel n) ∞ (SphereBundleTotal Q)
  smoothToExisting : letI := charts
    ContMDiff 𝓘(ℝ,ComplexTwistorModel n) (RealModel (E := E)) ∞
      (id : SphereBundleTotal Q → SphereBundleTotal Q)
  smoothFromExisting : letI := charts
    ContMDiff (RealModel (E := E)) 𝓘(ℝ,ComplexTwistorModel n) ∞
      (id : SphereBundleTotal Q → SphereBundleTotal Q)
  tangentI : letI := charts
    ∀ (z : SphereBundleTotal Q)
      (v : TangentSpace 𝓘(ℝ,ComplexTwistorModel n) z),
      mfderiv 𝓘(ℝ,ComplexTwistorModel n) (RealModel (E := E))
        (id : SphereBundleTotal Q → SphereBundleTotal Q) z
          ((Complex.I : ℂ) • (show ComplexTwistorModel n from v)) =
      tangentComplex Q D z
        (mfderiv 𝓘(ℝ,ComplexTwistorModel n) (RealModel (E := E))
          (id : SphereBundleTotal Q → SphereBundleTotal Q) z v)

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
