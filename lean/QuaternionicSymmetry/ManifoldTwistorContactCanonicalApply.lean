import QuaternionicSymmetry.GeneralComplexContactCanonicalFormula
import QuaternionicSymmetry.ManifoldTwistorGeneralContactInstantiation
import QuaternionicSymmetry.ManifoldTwistorContactCanonicalRelation

/-! Application of the general, twistor-independent complex-contact
canonical formula to the exact LeBrun contact data on the actual
quaternionic twistor sphere bundle. All hypotheses of the general
formula are discharged by previously checked geometry; the universal
formula remains the explicitly cited external source premise. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open QuaternionicSymmetry.GeneralComplexContactData
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

universe uE uM

variable {E : Type uE} {M : Type uM}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

/-- The complex-contact determinant formula specialized to the genuine
twistor tangent and contact-line cores. No Hilbert/index value is assumed. -/
theorem contactCanonicalIso_of_generalContact
    (hGeneral : GeneralContactCanonicalTheorem.{uE,uE,uM})
    {n : ℕ} {A : CompatibleComplexAtlas Q D n}
    (C : NondegenerateHolomorphicContactData Q D n A) :
    Nonempty (HolomorphicContactCanonicalIso Q D n A C.contact.line) := by
  let G := C.toGeneralContactGeometry Q D
  obtain ⟨e⟩ := hGeneral G
  exact ⟨{
    fiberEquiv := e.fiberEquiv
    holomorphicForward := e.holomorphicForward
    holomorphicBackward := e.holomorphicBackward
  }⟩

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
