import QuaternionicSymmetry.HolomorphicLineCoreClassPowers
import QuaternionicSymmetry.ManifoldTwistorLineCoreClasses

/-! The registered complex-contact canonical formula in the actual
commutative group of represented holomorphic line classes. This is the
anticanonical relation, not a claim that the contact class generates the
full Picard group. -/

namespace QuaternionicSymmetry.ManifoldTwistorCanonicalClassGroup

open HolomorphicLineCoreClasses HolomorphicLineCoreClassPowers
open ManifoldTwistorLineCoreClasses ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore ManifoldQuaternionicMetric ManifoldQuaternionicConnection
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

theorem anticanonicalClass_eq_contactClass_pow_of_generalContact
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    {n : ℕ} {A : CompatibleComplexAtlas Q D n}
    (C : NondegenerateHolomorphicContactData Q D n A) :
    letI := A.charts
    anticanonicalClass Q D A = contactClass Q D C.contact.line ^ (n + 1) := by
  letI := A.charts
  rw [anticanonicalClass_eq_contactTensorIterate_of_generalContact Q D hGeneral C,
    tensorIterate_eq_pow]
  rfl

end
end QuaternionicSymmetry.ManifoldTwistorCanonicalClassGroup
