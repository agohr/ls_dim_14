import QuaternionicSymmetry.ManifoldTwistorUniqueContactFullLieTransfer
import QuaternionicSymmetry.ManifoldTwistorLeBrunContactNondegenerate
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry
import QuaternionicSymmetry.RealToComplexTangentComplexificationLinear
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-!
# Reviewed derived NT infinitesimal contact complexification contract

Nitta--Takeuchi, *Contact structures on twistor spaces*, J. Math. Soc.
Japan 39 (1987), 139--162,
https://www.jstage.jst.go.jp/article/jmath1948/39/1/39_1_139/_pdf,
Theorem 3.1 (p. 152), Theorem 3.2 (p. 155),
and Corollary 2 (p. 159), with the compact-complete Corollaries 3--4
(pp. 159--160), identify the quaternionic-isometry fields with the compact
real form of the actual holomorphic contact fields. Lee, *Introduction to
Smooth Manifolds*, Problem 20-11(b,c) (pp. 537--538), supplies uniqueness
of the real Lie atlas, and Kobayashi, *Transformation Groups in Differential
Geometry*, III.1.1 (p. 77), supplies the canonical holomorphic-field
interpretation of the jointly holomorphic automorphism atlas. This is an
explicitly derived literature contract, not a literal single theorem.

The typed consequence is ONLY bijectivity of the complex-linear extension
of the derivative of the literal isometry-to-contact lift, in supplied
actual Lie atlases. Smoothness of that lift and joint holomorphicity of
the supplied full-automorphism action are explicit premises. No Cartan,
centralizer, root, weight, or global complexified group is concluded.

This reviewed derived NT-C source boundary has no project-specific
Cartan, root, or recognition conclusion. -/

namespace QuaternionicSymmetry.ManifoldTwistorNTContactInfinitesimalSource

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open RealToComplexTangentComplexification
open scoped Manifold ContDiff TensorProduct
noncomputable section

/-- Actual-object derived NT-C contract: contact-field complexification, with
the exact derivative of the literal isometry contact lift and no bespoke
Cartan assumption. The contact Lie atlas is the pullback of the SAME
supplied full-automorphism atlas. -/
def NTContactInfinitesimalComplexificationSource : Prop :=
  ∀ {E M VR VC : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [NormedAddCommGroup VR] [NormedSpace ℝ VR] [FiniteDimensional ℝ VR]
    [NormedAddCommGroup VC] [NormedSpace ℂ VC] [FiniteDimensional ℂ VC]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ), 2 ≤ n → Module.finrank ℝ E = 4*n →
    ∀ (A : CompatibleComplexAtlas P.tangent P.connection n)
      (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
      (hPreserve : FullPreservesContact
        P.tangent P.connection A C.contact.line),
      letI := A.charts
      letI := A.complexManifold
      ∀ (hRealChart : ChartedSpace VR
          (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent))
        (hRealManifold : letI := hRealChart
          IsManifold 𝓘(ℝ,VR) ∞
            (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent))
        (hRealLie : letI := hRealChart
          LieGroup 𝓘(ℝ,VR) ∞
            (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent))
        (hAutChart : ChartedSpace VC
          (TwistorHolomorphicAutomorphisms P.tangent P.connection A))
        (hAutManifold : letI := hAutChart
          IsManifold 𝓘(ℂ,VC) ∞
            (TwistorHolomorphicAutomorphisms P.tangent P.connection A))
        (hAutLie : letI := hAutChart
          LieGroup 𝓘(ℂ,VC) ∞
            (TwistorHolomorphicAutomorphisms P.tangent P.connection A)),
        letI : ChartedSpace VR
            (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) :=
          hRealChart
        letI : IsManifold 𝓘(ℝ,VR) ∞
            (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) :=
          hRealManifold
        letI : LieGroup 𝓘(ℝ,VR) ∞
            (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent) :=
          hRealLie
        letI : ChartedSpace VC
            (TwistorHolomorphicAutomorphisms P.tangent P.connection A) :=
          hAutChart
        letI : IsManifold 𝓘(ℂ,VC) ∞
            (TwistorHolomorphicAutomorphisms P.tangent P.connection A) :=
          hAutManifold
        letI : LieGroup 𝓘(ℂ,VC) ∞
            (TwistorHolomorphicAutomorphisms P.tangent P.connection A) :=
          hAutLie
        ∀ (hJoint : ContMDiff
            (𝓘(ℂ,VC).prod 𝓘(ℂ,ComplexTwistorModel n))
            𝓘(ℂ,ComplexTwistorModel n) ∞
            (fun p : TwistorHolomorphicAutomorphisms
                P.tangent P.connection A × SphereBundleTotal P.tangent =>
              p.1.1 p.2))
          (hSmooth :
            letI := contactCharts (V := VC)
              P.tangent P.connection A C.contact.line hPreserve
            ContMDiff 𝓘(ℝ,VR) 𝓘(ℝ,VC) ∞
              (isometryContactLift P.tangent P.connection A C.contact.line)),
          letI := contactCharts (V := VC)
            P.tangent P.connection A C.contact.line hPreserve
          letI := contactManifold (V := VC)
            P.tangent P.connection A C.contact.line hPreserve
          letI := contactLieGroup (V := VC)
            P.tangent P.connection A C.contact.line hPreserve
          let f : GroupLieAlgebra 𝓘(ℝ,VR)
              (ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries P.tangent)
              →ₗ[ℝ] GroupLieAlgebra 𝓘(ℂ,VC)
                (ContactAutomorphisms
                  P.tangent P.connection A C.contact.line) :=
            (mfderiv 𝓘(ℝ,VR) 𝓘(ℝ,VC)
              (isometryContactLift
                P.tangent P.connection A C.contact.line) 1).toLinearMap
          Function.Bijective (complexifiedMapComplex f)

end
end QuaternionicSymmetry.ManifoldTwistorNTContactInfinitesimalSource
