import QuaternionicSymmetry.GeneralComplexTorusLineKernelPreservation
import QuaternionicSymmetry.ManifoldTwistorContactAutomorphisms
import QuaternionicSymmetry.ManifoldTwistorLineCoreClasses

/-! The actual jointly holomorphic complex-torus extension of quaternionic
isometries preserves the genuine twistor contact distribution. Preservation
is derived by holomorphic uniqueness from the compact torus, not supplied
as an extra property of the complex action. -/

namespace QuaternionicSymmetry.ManifoldTwistorComplexTorusContactPreservation

open ManifoldQuaternionicTorusAction ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore ManifoldTwistorContactAutomorphisms
open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B)

theorem complex_action_preserves_contact {r : ℕ}
    (A : ContinuousTorusAction Q r)
    (ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal Q))
    (hJoint : letI := B.charts
      ContMDiff (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ, ComplexTwistorModel n))
        𝓘(ℂ, ComplexTwistorModel n) ∞
        (fun p : ComplexTorus r × SphereBundleTotal Q => ρ p.1 p.2))
    (hRestrict : ∀ (t : Torus r) (z : SphereBundleTotal Q),
      ρ (compactInclusion r t) z = sphereTotalMap Q (A.representation t) z) :
    letI := B.charts
    ∀ (g : ComplexTorus r) (z : SphereBundleTotal Q)
      (v : TangentSpace 𝓘(ℂ, ComplexTwistorModel n) z),
      C.line.contactFormComplex Q D z v = 0 →
        C.line.contactFormComplex Q D (ρ g z)
          (mfderiv 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, ComplexTwistorModel n)
            (ρ g) z v) = 0 := by
  letI := B.charts
  letI := B.complexManifold
  let L : HolomorphicLineCoreClasses.LineCore
      (B := SphereBundleTotal Q) 𝓘(ℂ, ComplexTwistorModel n) := {
    Index := C.line.Index
    core := C.line.core
    holomorphic := C.line.holomorphic }
  apply GeneralComplexTorusLineKernelPreservation.preserves_kernel
    L (C.line.contactFormComplex Q D)
    C.contactHolomorphic (fun p : ComplexTorus r × SphereBundleTotal Q => ρ p.1 p.2)
    hJoint
  intro t z v hv
  have hmap : (fun y => ρ (compactInclusion r t) y) =
      sphereTotalMap Q (A.representation t) := funext (hRestrict t)
  change C.line.contactFormComplex Q D ((fun y => ρ (compactInclusion r t) y) z)
    (mfderiv 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, ComplexTwistorModel n)
      (fun y => ρ (compactInclusion r t) y) z v) = 0
  rw [hmap]
  exact complexLift_preserves_contact_forward Q D B C.line
    (A.representation t) z v hv

end
end QuaternionicSymmetry.ManifoldTwistorComplexTorusContactPreservation
