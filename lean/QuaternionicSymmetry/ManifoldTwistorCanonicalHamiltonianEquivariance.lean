import QuaternionicSymmetry.ManifoldTwistorCanonicalHamiltonianNaturality
import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismIsometrySections

/-! A checked canonical Hamiltonian linear equivalence, whenever the
actual orbit-field contraction has separately established bijectivity.
The equivalence, conjugation law, and isometry restriction all use the
same supplied contact-group complex Lie atlas and joint action. -/

namespace QuaternionicSymmetry.ManifoldTwistorCanonicalHamiltonianEquivariance

open ManifoldTwistorCanonicalHamiltonianNaturality
open ManifoldTwistorContactInfinitesimalAction
open ManifoldTwistorContactAutomorphisms
open ManifoldTwistorContactContraction
open ManifoldTwistorContactAutomorphismSections
open ManifoldTwistorContactAutomorphismIsometrySections
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses
open HolomorphicVectorFieldPushforward HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section
set_option maxHeartbeats 200000

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B)

def canonicalHamiltonianEquiv
    [ChartedSpace V (ContactAutomorphisms Q D B C.line)]
    [IsManifold 𝓘(ℂ,V) ∞ (ContactAutomorphisms Q D B C.line)]
    (hJoint :
      letI := B.charts
      letI := B.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : ContactAutomorphisms Q D B C.line × SphereBundleTotal Q =>
          p.1.1 p.2))
    (hBij :
      letI := B.charts
      letI := B.complexManifold
      Function.Bijective
        ((contraction Q D B C).comp
          (contactInfinitesimalActionLinear (V := V) Q D B C.line hJoint))) :
    letI := B.charts
    letI := B.complexManifold
    GroupLieAlgebra 𝓘(ℂ,V) (ContactAutomorphisms Q D B C.line) ≃ₗ[ℂ]
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) := by
  letI := B.charts
  letI := B.complexManifold
  exact LinearEquiv.ofBijective
    ((contraction Q D B C).comp
      (contactInfinitesimalActionLinear (V := V) Q D B C.line hJoint)) hBij

theorem canonicalHamiltonianEquiv_apply
    [ChartedSpace V (ContactAutomorphisms Q D B C.line)]
    [IsManifold 𝓘(ℂ,V) ∞ (ContactAutomorphisms Q D B C.line)]
    (hJoint :
      letI := B.charts
      letI := B.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : ContactAutomorphisms Q D B C.line × SphereBundleTotal Q =>
          p.1.1 p.2))
    (hBij :
      letI := B.charts
      letI := B.complexManifold
      Function.Bijective
        ((contraction Q D B C).comp
          (contactInfinitesimalActionLinear (V := V) Q D B C.line hJoint)))
    (v : GroupLieAlgebra 𝓘(ℂ,V) (ContactAutomorphisms Q D B C.line))
    (z : SphereBundleTotal Q) :
    letI := B.charts
    letI := B.complexManifold
    canonicalHamiltonianEquiv (V := V) Q D B C hJoint hBij v z =
      C.line.contactFormComplex Q D z
        ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,ComplexTwistorModel n)
          (fun f : ContactAutomorphisms Q D B C.line => f.1 z) 1) v) := by
  letI := B.charts
  letI := B.complexManifold
  exact congrArg (fun w => C.line.contactFormComplex Q D z w)
    (contactInfinitesimalActionLinear_apply (V := V) Q D B C.line hJoint v z)

theorem canonicalHamiltonianEquiv_conjugation
    [ChartedSpace V (ContactAutomorphisms Q D B C.line)]
    [IsManifold 𝓘(ℂ,V) ∞ (ContactAutomorphisms Q D B C.line)]
    [LieGroup 𝓘(ℂ,V) ∞ (ContactAutomorphisms Q D B C.line)]
    (hJoint :
      letI := B.charts
      letI := B.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : ContactAutomorphisms Q D B C.line × SphereBundleTotal Q =>
          p.1.1 p.2))
    (hBij :
      letI := B.charts
      letI := B.complexManifold
      Function.Bijective
        ((contraction Q D B C).comp
          (contactInfinitesimalActionLinear (V := V) Q D B C.line hJoint)))
    (f : ContactAutomorphisms Q D B C.line)
    (v : GroupLieAlgebra 𝓘(ℂ,V) (ContactAutomorphisms Q D B C.line)) :
    letI := B.charts
    letI := B.complexManifold
    canonicalHamiltonianEquiv (V := V) Q D B C hJoint hBij
      ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
        (fun g : ContactAutomorphisms Q D B C.line => f * g * f⁻¹) 1) v) =
      contactSectionEquiv Q D B C f
        (canonicalHamiltonianEquiv (V := V) Q D B C hJoint hBij v) := by
  letI := B.charts
  letI := B.complexManifold
  change contraction Q D B C
      (contactInfinitesimalActionLinear (V := V) Q D B C.line hJoint
        ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
          (fun g : ContactAutomorphisms Q D B C.line => f * g * f⁻¹) 1) v)) =
    contactSectionEquiv Q D B C f
      (contraction Q D B C
        (contactInfinitesimalActionLinear (V := V) Q D B C.line hJoint v))
  rw [canonicalField_conjugation_natural Q D B C hJoint f v]
  exact contraction_equivariant Q D B C f _

theorem canonicalHamiltonianEquiv_isometry
    [ChartedSpace V (ContactAutomorphisms Q D B C.line)]
    [IsManifold 𝓘(ℂ,V) ∞ (ContactAutomorphisms Q D B C.line)]
    [LieGroup 𝓘(ℂ,V) ∞ (ContactAutomorphisms Q D B C.line)]
    (hJoint :
      letI := B.charts
      letI := B.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : ContactAutomorphisms Q D B C.line × SphereBundleTotal Q =>
          p.1.1 p.2))
    (hBij :
      letI := B.charts
      letI := B.complexManifold
      Function.Bijective
        ((contraction Q D B C).comp
          (contactInfinitesimalActionLinear (V := V) Q D B C.line hJoint)))
    (f : ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries Q)
    (v : GroupLieAlgebra 𝓘(ℂ,V) (ContactAutomorphisms Q D B C.line)) :
    letI := B.charts
    letI := B.complexManifold
    canonicalHamiltonianEquiv (V := V) Q D B C hJoint hBij
      ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
        (fun g : ContactAutomorphisms Q D B C.line =>
          isometryContactLift Q D B C.line f * g *
            (isometryContactLift Q D B C.line f)⁻¹) 1) v) =
      ManifoldQuaternionicIsometryContactSections.contactSectionEquiv
        Q D B C f
        (canonicalHamiltonianEquiv (V := V) Q D B C hJoint hBij v) := by
  letI := B.charts
  letI := B.complexManifold
  exact (canonicalHamiltonianEquiv_conjugation Q D B C hJoint hBij
    (isometryContactLift Q D B C.line f) v).trans
    (congrArg (fun F => F (canonicalHamiltonianEquiv (V := V) Q D B C hJoint hBij v))
      (contactSectionEquiv_isometry Q D B C f))

end
end QuaternionicSymmetry.ManifoldTwistorCanonicalHamiltonianEquivariance
