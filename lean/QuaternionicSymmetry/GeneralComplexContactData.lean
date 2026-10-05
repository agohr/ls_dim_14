import QuaternionicSymmetry.ManifoldTwistorContactComplexExact
import QuaternionicSymmetry.ManifoldTwistorLeBrunContactNondegenerate
import QuaternionicSymmetry.HolomorphicDeterminantLine
import QuaternionicSymmetry.HolomorphicLinePowers

/-! General complex-contact data on an arbitrary complex manifold with a
smooth real companion atlas. This has no quaternionic reduction or twistor
assumption. The quotient map is a holomorphic map of genuine bundle total
spaces, is fiberwise onto, and its kernel has nondegenerate local Levi
bracket. These are the hypotheses of LeBrun 1995, Definition 2.1. -/

namespace QuaternionicSymmetry.GeneralComplexContactData

open QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
open scoped Manifold ContDiff

noncomputable section

variable {R H Z : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
  {IR : ModelWithCorners ℝ R H} [IsManifold IR ∞ Z]

private abbrev V (n : ℕ) := ComplexTwistorModel n

/-- A holomorphic line-valued contact form with nondegenerate Levi
bracket, on an arbitrary complex `(2n+1)`-manifold. The auxiliary real
smooth atlas is used only to express the actual manifold Lie bracket. -/
structure ContactGeometry (n : ℕ) where
  charts : ChartedSpace (V n) Z
  complexManifold : letI := charts
    IsManifold 𝓘(ℂ,V n) ∞ Z
  realManifold : letI := charts
    IsManifold 𝓘(ℝ,V n) ∞ Z
  smoothToReal : letI := charts
    ContMDiff 𝓘(ℝ,V n) IR ∞ (id : Z → Z)
  smoothFromReal : letI := charts
    ContMDiff IR 𝓘(ℝ,V n) ∞ (id : Z → Z)
  Index : Type
  line : VectorBundleCore ℂ Z ℂ Index
  lineHolomorphic : letI := charts
    line.IsContMDiff 𝓘(ℂ,V n) ∞
  theta : ∀ z : Z, TangentSpace IR z →ₗ[ℝ] line.Fiber z
  thetaSurjective : ∀ z, Function.Surjective (theta z)
  thetaHolomorphic : letI := charts
    letI := complexManifold
    letI := lineHolomorphic
    ContMDiff (𝓘(ℂ,V n)).tangent ((𝓘(ℂ,V n)).prod 𝓘(ℂ,ℂ)) ∞
      (fun t : TangentBundle 𝓘(ℂ,V n) Z =>
        (⟨t.1, theta t.1
          (mfderiv 𝓘(ℝ,V n) IR (id : Z → Z) t.1 t.2)⟩ :
          Bundle.TotalSpace ℂ line.Fiber))
  leviNondegenerate : ∀ z : Z,
    ∀ u : LinearMap.ker (theta z), u ≠ 0 →
      ∃ U : Set Z, IsOpen U ∧ z ∈ U ∧
      ∃ X Y : ∀ y : Z, TangentSpace IR y,
        ContMDiffOn IR IR.tangent ∞
          (fun y => (⟨y,X y⟩ : TangentBundle IR Z)) U ∧
        ContMDiffOn IR IR.tangent ∞
          (fun y => (⟨y,Y y⟩ : TangentBundle IR Z)) U ∧
        (∀ y ∈ U, X y ∈ LinearMap.ker (theta y)) ∧
        (∀ y ∈ U, Y y ∈ LinearMap.ker (theta y)) ∧
        X z = u.1 ∧
        theta z (VectorField.mlieBracket IR X Y z) ≠ 0

end
end QuaternionicSymmetry.GeneralComplexContactData
