import QuaternionicSymmetry.ManifoldHodgePositiveScaling
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry
import QuaternionicSymmetry.ManifoldClosedTangentGenerators

/-!
The registered H1 intersection theorem in its scale-invariant form.

Amann, Partial Classification Results for Positive Quaternion Kähler
Manifolds, arXiv:0911.4587v1 (24 November 2009), Theorem 1.2, p. 6,
gives the signed intersection
inequality for every real class of even degree with the canonical `u=-c₂(H)`.
The user accepted this inspected preprint as the authoritative source text on
28 September 2026. The associated journal article is IJM 23 (2012), 1250038,
DOI 10.1142/S0129167X12500383; its final PDF has not been inspected.
In degree `4*m` the sign is positive. Semmelmann--Weingart,
arXiv:math/0208079v1, Section 2, printed p. 3, identifies `4*u` with a
positive scalar multiple of the Kraines form. Consequently the source
asserts existence of a positive multiple of the actual fundamental class
with the generalized square inequality. Only this weaker, normalization-free
consequence of the registered H1/I1 statements is requested here.

The source premise quantifies over all actual compact connected positive
quaternionic Kähler inputs and all cohomology classes in the permitted
degrees. It contains no certificate, recovered class, index or classification
conclusion. It is an explicit theorem argument, never a Lean axiom.
The internal positive-rescaling proof then transfers it to the analytic
quarter class using the already proved KSW curvature calculation. No claim
of topological characteristic-class or index identification is made.
-/

namespace QuaternionicSymmetry.ManifoldAmannIntersectionInput

open ManifoldHodgeSquareApplication ManifoldEvenCharacteristicAlgebra
  ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicFundamentalClass
  ManifoldQuaternionicKSWScalarInput ManifoldQuaternionicKSWEq38Input
  ManifoldTangentTraceRootCandidates ManifoldClosedTangentGenerators
  ManifoldEvenClosedClassMap ManifoldIntegratedRecoveredCertificates
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]

/-- Scale-invariant consequence of the registered H1 theorem and the
registered positive Kraines-form representative of its canonical class. -/
def AmannKrainesRayInput : Prop :=
  ∀ (S : QuaternionicStructure E)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M)),
    2 ≤ S.quaternionicDimension →
    ∀ (k : ℕ) (_hn : S.quaternionicDimension = k + 1)
      (hdim : 4 * (k + 1) = Module.finrank ℝ E),
      ∃ c : ℝ, 0 < c ∧ GeneralizedSquareNonnegative P.tangent k hdim
        (c • fundamentalClass P.tangent P.connection)

variable (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

theorem fundamental_square_nonnegative
    (hAmann : AmannKrainesRayInput (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) (k : ℕ)
    (hk : S.quaternionicDimension = k + 1)
    (hdim : 4 * (k + 1) = Module.finrank ℝ E) :
    GeneralizedSquareNonnegative P.tangent k hdim
      (fundamentalClass P.tangent P.connection) := by
  obtain ⟨c, hc, h⟩ := hAmann S P hn k hk hdim
  exact (generalizedSquareNonnegative_smul_iff P.tangent k hdim
    (fundamentalClass P.tangent P.connection) c hc).mp h

theorem quarter_square_nonnegative
    (hAmann : AmannKrainesRayInput (E := E) (M := M))
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) (k : ℕ)
    (hk : S.quaternionicDimension = k + 1)
    (hdim : 4 * (k + 1) = Module.finrank ℝ E) :
    GeneralizedSquareNonnegative P.tangent k hdim
      (quarterUClass P.tangent P.connection) := by
  obtain ⟨t, ht, hquarter, _⟩ := P.exists_common_parameter S hn hsp heq38
  have hclass : quarterUClass P.tangent P.connection =
      (t ^ 4 / Real.pi ^ 2) • fundamentalClass P.tangent P.connection := by
    rw [← quarterForm_class, hquarter, map_smul]
    rfl
  rw [hclass]
  exact generalizedSquareNonnegative_smul P.tangent k hdim
    (fundamentalClass P.tangent P.connection)
    (fundamental_square_nonnegative S P hAmann hn k hk hdim)
    _ (by positivity)

theorem amann_witness13_square_nonnegative
    (hAmann : AmannKrainesRayInput (E := E) (M := M))
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 13) (hdim : 52 = Module.finrank ℝ E) :
    0 ≤ sevenCandidateNumber P.tangent P.connection 13 12 hdim
      (H2WitnessThirteen.factor ^ 2 * DimensionThirteenFourteenDensity.u ^ 7) :=
  witness13_square_nonnegative P.tangent P.connection hdim
    (quarter_square_nonnegative S P hAmann hsp heq38 (by omega) 12 hn hdim)

theorem amann_witness14_square_nonnegative
    (hAmann : AmannKrainesRayInput (E := E) (M := M))
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 14) (hdim : 56 = Module.finrank ℝ E) :
    0 ≤ sevenCandidateNumber P.tangent P.connection 14 13 hdim
      (H2WitnessFourteen.factor ^ 2 * DimensionThirteenFourteenDensity.u ^ 8) :=
  witness14_square_nonnegative P.tangent P.connection hdim
    (quarter_square_nonnegative S P hAmann hsp heq38 (by omega) 13 hn hdim)

end
end QuaternionicSymmetry.ManifoldAmannIntersectionInput
