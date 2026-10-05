import QuaternionicSymmetry.ManifoldQuaternionicActualTwistorTangentContinuity
import QuaternionicSymmetry.ManifoldQuaternionicTwistorTangentContinuityTransfer
import QuaternionicSymmetry.CompactTorusEigenbasisSource

/-! Integral eigenvectors in the actual complete contact-line section space,
not a tensor power or an abstract representation. Joint continuity is proved
from BG-R3 through the actual tangent and line actions; only the registered
finiteness and compact-character theorems are additional source inputs. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicContactSectionsFromSources

open ManifoldQuaternionicTorusAction ManifoldQuaternionicTorusContactSections
open ManifoldQuaternionicContactFiniteSections
open ManifoldQuaternionicActualTwistorTangentContinuity
open ManifoldQuaternionicTwistorTangentContinuityTransfer
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open HolomorphicLineCorePullback CompactTorusEigenbasisSource TorusCharacterInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [CompactSpace M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
  (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
  (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
  {r : ℕ} (A : ContinuousTorusAction Q r)
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B)

include hR3 in
theorem continuous_contactTorusAction_from_sources :
    letI := B.charts
    letI := contactSectionsNormedAddCommGroup Q hFinite D B C
    Continuous (fun p : Torus r ×
      GlobalSections 𝓘(ℂ, ComplexTwistorModel n) (contactLineCore Q D C.line) =>
      contactTorusRepresentation Q A D B C p.1 p.2) :=
  continuous_contactTorusAction_of_existing_tangent Q hFinite A D B C
    (continuous_jointSphereTangentAction Q hR3)

include hR3 hFinite hEigen hCircle in
theorem exists_integral_contact_eigenbasis_from_sources :
    letI := B.charts
    ∃ b : Module.Basis
      (Fin (Module.finrank ℂ
        (GlobalSections 𝓘(ℂ, ComplexTwistorModel n) (contactLineCore Q D C.line))))
      ℂ (GlobalSections 𝓘(ℂ, ComplexTwistorModel n) (contactLineCore Q D C.line)),
      ∃ μ : Fin (Module.finrank ℂ
        (GlobalSections 𝓘(ℂ, ComplexTwistorModel n) (contactLineCore Q D C.line))) →
          Fin r → ℤ,
        ∀ t i, contactTorusRepresentation Q A D B C t (b i) =
          (weightCharacter (μ i) t : ℂ) • b i := by
  letI := B.charts
  letI := finiteDimensional_contactSections Q hFinite D B C
  letI := contactSectionsNormedAddCommGroup Q hFinite D B C
  letI := contactSectionsNormedSpace Q hFinite D B C
  exact exists_integral_eigenbasis hEigen hCircle
    (contactTorusRepresentation Q A D B C)
    (continuous_contactTorusAction_from_sources Q hR3 hFinite A D B C)

end
end QuaternionicSymmetry.ManifoldQuaternionicContactSectionsFromSources
