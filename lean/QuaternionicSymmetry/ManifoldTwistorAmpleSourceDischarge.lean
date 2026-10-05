import QuaternionicSymmetry.ManifoldTwistorPositiveContactAmple
import QuaternionicSymmetry.ManifoldTwistorAmpleCoreReverseBridge
import QuaternionicSymmetry.ManifoldTwistorLeBrunAmpleSource

/-! The earlier composite `NormalizedAmpleContactExistence` literature
interface is now a theorem from strictly narrower, literal source
premises: positive-Ricci Kähler–Einstein twistor existence, the general
complex-contact canonical isomorphism, and general Hermitian Kodaira.
All metric gauge/root and projective-linear-system transfers are internal. -/

namespace QuaternionicSymmetry.ManifoldTwistorAmpleSourceDischarge

open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorPositiveRicciInput
open ManifoldTwistorPositiveContactAmple
open ManifoldTwistorAmpleCoreReverseBridge
open HolomorphicPositiveLineKodairaSource
open scoped Manifold ContDiff
noncomputable section

theorem normalizedAmpleContact_of_positiveRicci
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0}) :
    NormalizedAmpleContactExistence.{0,0} := by
  intro E M _ _ _ _ _ _ _ _ _ _ P n hn hDim hScalar
  obtain ⟨A,C,hAmple⟩ := exists_normalized_ample_contact_core
    hT1 hKodaira P n hn hDim hScalar
  exact ⟨A,C,ampleContactLine_of_ampleCore
    P.tangent P.connection C.contact.line hAmple⟩

end
end QuaternionicSymmetry.ManifoldTwistorAmpleSourceDischarge
