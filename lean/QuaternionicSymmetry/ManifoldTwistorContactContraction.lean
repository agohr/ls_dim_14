import QuaternionicSymmetry.GeneralHolomorphicDistributionVectorFields
import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismSections

/-! Contraction with the actual holomorphic contact form is a complex-linear
map from genuine global holomorphic tangent fields to genuine contact-line
sections. It intertwines their canonical full-contact-group actions.
Neither injectivity nor surjectivity on global sections is asserted here. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactContraction

open HolomorphicVectorFieldPushforward
open ManifoldTwistorContactAutomorphisms ManifoldTwistorContactAutomorphismFiber
open ManifoldTwistorContactAutomorphismSections ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses ManifoldTwistorSphereCore
open HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B)

def contraction :
    letI := B.charts
    letI := B.complexManifold
    Fields (V := ComplexTwistorModel n) (Z := SphereBundleTotal Q) →ₗ[ℂ]
      GlobalSections 𝓘(ℂ, ComplexTwistorModel n) (contactLineCore Q D C.line) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  refine {
    toFun := fun X => ⟨fun z => C.line.contactFormComplex Q D z (X z), ?_⟩
    map_add' := ?_
    map_smul' := ?_ }
  · exact C.contactHolomorphic.comp X.contMDiff
  · intro X Y
    apply ContMDiffSection.ext
    intro z
    exact map_add (C.line.contactFormComplex Q D z) _ _
  · intro c X
    apply ContMDiffSection.ext
    intro z
    exact map_smul (C.line.contactFormComplex Q D z) c _

theorem contraction_equivariant (f : ContactAutomorphisms Q D B C.line) :
    letI := B.charts
    letI := B.complexManifold
    ∀ X : Fields (V := ComplexTwistorModel n) (Z := SphereBundleTotal Q),
      contraction Q D B C (pushForwardLinear f.1 X) =
        contactSectionEquiv Q D B C f (contraction Q D B C X) := by
  letI := B.charts
  letI := B.complexManifold
  intro X
  apply ContMDiffSection.ext
  intro y
  obtain ⟨z, rfl⟩ := f.1.surjective y
  change C.line.contactFormComplex Q D (f.1 z)
      (pushForwardLinear f.1 X (f.1 z)) =
    contactSectionEquiv Q D B C f (contraction Q D B C X) (f.1 z)
  rw [pushForwardLinear_apply_at_image, contactSectionEquiv_apply_at_image]
  exact (contactFiberEquiv_contactForm Q D B C.line f z (X z)).symm

theorem contraction_intertwines_representations
    (f : ContactAutomorphisms Q D B C.line) :
    letI := B.charts
    letI := B.complexManifold
    (contraction Q D B C).comp
        (GeneralHolomorphicDistributionVectorFields.representation
          (contactDistribution Q D B C.line) f) =
      (contactSectionRepresentation Q D B C f).comp (contraction Q D B C) := by
  letI := B.charts
  letI := B.complexManifold
  apply LinearMap.ext
  exact contraction_equivariant Q D B C f

end
end QuaternionicSymmetry.ManifoldTwistorContactContraction
