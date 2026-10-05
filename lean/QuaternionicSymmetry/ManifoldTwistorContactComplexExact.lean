import QuaternionicSymmetry.ManifoldTwistorContactComplexLinear
import QuaternionicSymmetry.ManifoldTwistorAtlasTangentEquiv

/-! The holomorphic contact form on the source complex tangent bundle is
fiberwise surjective, with kernel the transport of the already checked
horizontal distribution. Both claims are derived from the quotient
construction and the inverse tangent derivatives of the two real atlases. -/

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

theorem HolomorphicContactLine.contactFormReal_surjective {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (z : SphereBundleTotal Q) :
    Function.Surjective (L.contactFormReal Q D z) := by
  letI := contactQuotientComplexModule Q D z
  intro w
  obtain ⟨q, hq⟩ := (L.quotientEquiv z).symm.surjective w
  obtain ⟨v, hv⟩ :=
    (horizontalTangentSubmodule Q D z).mkQ_surjective q
  refine ⟨v, ?_⟩
  simp only [HolomorphicContactLine.contactFormReal, LinearMap.comp_apply, hv]
  exact hq

theorem HolomorphicContactLine.contactFormComplex_surjective {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (z : SphereBundleTotal Q) :
    letI := A.charts
    Function.Surjective (L.contactFormComplex Q D z) := by
  letI := A.charts
  intro w
  obtain ⟨u, hu⟩ := L.contactFormReal_surjective Q D z w
  let v := (mfderiv (RealModel (E := E)) 𝓘(ℝ,ComplexTwistorModel n)
    (id : SphereBundleTotal Q → SphereBundleTotal Q) z) u
  refine ⟨v, ?_⟩
  have h := congrArg
    (fun T : TangentSpace (RealModel (E := E)) z →L[ℝ]
      TangentSpace (RealModel (E := E)) z => T u)
    (A.realId_deriv_comp_inverse Q D z)
  simp only [ContinuousLinearMap.id_apply] at h
  change L.contactFormReal Q D z
    ((mfderiv 𝓘(ℝ,ComplexTwistorModel n) (RealModel (E := E))
      (id : SphereBundleTotal Q → SphereBundleTotal Q) z) v) = w
  rw [show (mfderiv 𝓘(ℝ,ComplexTwistorModel n) (RealModel (E := E))
      (id : SphereBundleTotal Q → SphereBundleTotal Q) z) v = u from h]
  exact hu

theorem HolomorphicContactLine.contactFormComplex_kernel {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (z : SphereBundleTotal Q) :
    letI := A.charts
    ∀ v : TangentSpace 𝓘(ℂ,ComplexTwistorModel n) z,
      L.contactFormComplex Q D z v = 0 ↔
        (mfderiv 𝓘(ℝ,ComplexTwistorModel n) (RealModel (E := E))
          (id : SphereBundleTotal Q → SphereBundleTotal Q) z v) ∈
          horizontalTangentSubmodule Q D z := by
  letI := A.charts
  intro v
  change L.contactFormReal Q D z
    ((mfderiv 𝓘(ℝ,ComplexTwistorModel n) (RealModel (E := E))
      (id : SphereBundleTotal Q → SphereBundleTotal Q) z) v) = 0 ↔ _
  rw [← LinearMap.mem_ker, L.contactFormReal_ker Q D z]

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
