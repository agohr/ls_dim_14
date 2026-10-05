import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismSections
import QuaternionicSymmetry.ManifoldQuaternionicIsometryContactSectionAction

/-! The canonical representation of the full contact automorphism group
restricts exactly to the previously constructed quaternionic-isometry
representation. Both act on the same actual holomorphic contact sections. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactAutomorphismIsometrySections

open ManifoldTwistorContactAutomorphisms ManifoldTwistorContactAutomorphismFiber
open ManifoldTwistorContactAutomorphismSections ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses ManifoldTwistorSphereCore
open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryContactFiberEquiv
open ManifoldQuaternionicIsometryContactComplexNaturality
open ManifoldQuaternionicTwistorIsometryDiffeomorph
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)

theorem contactFiberEquiv_isometry (L : HolomorphicContactLine Q D n B)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    contactFiberEquiv Q D B L (isometryContactLift Q D B L f) z =
      contactLineFiberEquiv Q D L f z := by
  letI := B.charts
  letI := B.complexManifold
  apply LinearEquiv.ext
  intro w
  obtain ⟨v, rfl⟩ := L.contactFormComplex_surjective Q D z w
  rw [contactFiberEquiv_contactForm]
  exact contactLineFiberEquiv_contactFormComplex Q D B L f z v

theorem contactSectionEquiv_isometry (C : HolomorphicContactData Q D n B)
    (f : QuaternionicIsometries Q) :
    letI := B.charts
    contactSectionEquiv Q D B C (isometryContactLift Q D B C.line f) =
      ManifoldQuaternionicIsometryContactSections.contactSectionEquiv Q D B C f := by
  letI := B.charts
  letI := B.complexManifold
  apply LinearEquiv.ext
  intro s
  apply ContMDiffSection.ext
  intro y
  obtain ⟨z, rfl⟩ := (complexLift Q D B f).surjective y
  have hnew := contactSectionEquiv_apply_at_image Q D B C
    (isometryContactLift Q D B C.line f) s z
  rw [contactFiberEquiv_isometry] at hnew
  exact hnew.trans
    (ManifoldQuaternionicIsometryContactSections.contactSectionEquiv_apply_at_image
      Q D B C f s z).symm

theorem contactSectionRepresentation_isometry (C : HolomorphicContactData Q D n B) :
    letI := B.charts
    (contactSectionRepresentation Q D B C).comp
        (isometryContactLift Q D B C.line) =
      ManifoldQuaternionicIsometryContactSectionAction.contactSectionRepresentation
        Q D B C := by
  letI := B.charts
  apply MonoidHom.ext
  intro f
  exact congrArg LinearEquiv.toLinearMap (contactSectionEquiv_isometry Q D B C f)

end
end QuaternionicSymmetry.ManifoldTwistorContactAutomorphismIsometrySections
