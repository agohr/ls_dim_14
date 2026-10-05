import QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

/-! The two real smooth atlases in LeBrun's source conclusion give inverse
tangent derivatives of the identity. This identifies the new complex
tangent fiber with the previously constructed sphere tangent fiber. -/

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

private abbrev RealModel := (𝓘(ℝ,E)).prod (𝓡 2)

theorem CompatibleComplexAtlas.realId_deriv_comp_inverse {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (z : SphereBundleTotal Q) :
    letI := A.charts
    (mfderiv 𝓘(ℝ,ComplexTwistorModel n) (RealModel (E := E))
      (id : SphereBundleTotal Q → SphereBundleTotal Q) z).comp
      (mfderiv (RealModel (E := E)) 𝓘(ℝ,ComplexTwistorModel n)
        (id : SphereBundleTotal Q → SphereBundleTotal Q) z) =
      ContinuousLinearMap.id ℝ (TangentSpace (RealModel (E := E)) z) := by
  letI := A.charts
  have hto : MDifferentiableAt 𝓘(ℝ,ComplexTwistorModel n)
      (RealModel (E := E))
      (id : SphereBundleTotal Q → SphereBundleTotal Q) z :=
    A.smoothToExisting.contMDiffAt.mdifferentiableAt (by simp)
  have hfrom : MDifferentiableAt (RealModel (E := E))
      𝓘(ℝ,ComplexTwistorModel n)
      (id : SphereBundleTotal Q → SphereBundleTotal Q) z :=
    A.smoothFromExisting.contMDiffAt.mdifferentiableAt (by simp)
  simpa only [Function.comp_id, mfderiv_id] using
    (mfderiv_comp z hto hfrom).symm

theorem CompatibleComplexAtlas.realId_inverse_comp_deriv {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (z : SphereBundleTotal Q) :
    letI := A.charts
    (mfderiv (RealModel (E := E)) 𝓘(ℝ,ComplexTwistorModel n)
      (id : SphereBundleTotal Q → SphereBundleTotal Q) z).comp
      (mfderiv 𝓘(ℝ,ComplexTwistorModel n) (RealModel (E := E))
        (id : SphereBundleTotal Q → SphereBundleTotal Q) z) =
      ContinuousLinearMap.id ℝ (ComplexTwistorModel n) := by
  letI := A.charts
  have hto : MDifferentiableAt 𝓘(ℝ,ComplexTwistorModel n)
      (RealModel (E := E))
      (id : SphereBundleTotal Q → SphereBundleTotal Q) z :=
    A.smoothToExisting.contMDiffAt.mdifferentiableAt (by simp)
  have hfrom : MDifferentiableAt (RealModel (E := E))
      𝓘(ℝ,ComplexTwistorModel n)
      (id : SphereBundleTotal Q → SphereBundleTotal Q) z :=
    A.smoothFromExisting.contMDiffAt.mdifferentiableAt (by simp)
  simpa only [Function.comp_id, mfderiv_id] using
    (mfderiv_comp z hfrom hto).symm

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
