import QuaternionicSymmetry.ManifoldSWActualHilbertValues
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerAllVirtualBounds

/-! The actual SW cohomological Hilbert values and the actual pointwise
virtual-density positivity imply a lower bound for the genuine contact-line
section space. Salamon's section--Killing correspondence is a separate step. -/
namespace QuaternionicSymmetry.ManifoldSWSectionDimensionBound
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldSWActualHilbertValues ManifoldSWEquation22PQK
open ManifoldTangentCharacterNumber ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore ManifoldPositiveQuaternionicKahlerAllVirtualBounds
open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff
noncomputable section

universe w
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

variable [HasSheafify (Opens.grothendieckTopology
    (TopCat.of (SphereBundleTotal P.tangent))) (ModuleCat ℂ)]
  [HasExt.{w} (TopCat.Sheaf (ModuleCat ℂ)
    (TopCat.of (SphereBundleTotal P.tangent)))]

theorem contact_sections_dimension_lower_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hAmann : ManifoldAmannIntersectionInput.AmannKrainesRayInput (E := E) (M := M))
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (A : CompatibleComplexAtlas P.tangent P.connection S.quaternionicDimension)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection
      S.quaternionicDimension A)
    (hSW : SWEquation22OnPQK S P A C)
    (hn : 2 ≤ S.quaternionicDimension ∧ S.quaternionicDimension ≤ 14)
    (hCanonical : Nonempty (HolomorphicContactCanonicalIso
      P.tangent P.connection S.quaternionicDimension A C.contact.line))
    (x : SphereBundleTotal P.tangent)
    (hfinite : ∀ (r : ℤ) (s : ℕ), FiniteDimensional ℂ
      (holomorphicTwistComplexCohomology P.tangent P.connection C.contact.line r s))
    (hKodairaZero : ∀ s, 0 < s → s ≤ 2*S.quaternionicDimension+1 →
      Subsingleton (holomorphicTwistComplexCohomology P.tangent P.connection C.contact.line 0 s))
    (hKodairaOne : ∀ s, 0 < s → s ≤ 2*S.quaternionicDimension+1 →
      Subsingleton (holomorphicTwistComplexCohomology P.tangent P.connection C.contact.line 1 s))
    (hKodairaNegative : ∀ (r : ℤ), r < 0 → ∀ s, s ≤ 2*S.quaternionicDimension →
      Subsingleton (holomorphicTwistComplexCohomology P.tangent P.connection C.contact.line r s))
    (hSerre : ∀ (r : ℤ) (s : ℕ), s ≤ 2*S.quaternionicDimension+1 →
      Module.finrank ℂ (holomorphicTwistComplexCohomology P.tangent P.connection
        C.contact.line r s) =
      Module.finrank ℂ (holomorphicTwistComplexCohomology P.tangent P.connection
        C.contact.line (-r-(S.quaternionicDimension:ℤ)-1)
          (2*S.quaternionicDimension+1-s))) :
    QuaternionicSymmetry.delta S.quaternionicDimension + 1 ≤
      Module.finrank ℂ (HolomorphicTwistSections P.tangent P.connection
        C.contact.line 1) := by
  have hpositive := virtual_positive_two_fourteen S P hsource hAmann hsp heq38
    S.quaternionicDimension hn rfl
  have hvirtual := actual_virtual_eq_sections_sub_delta S P A C hSW hn hCanonical
    x hfinite hKodairaZero hKodairaOne hKodairaNegative hSerre
  rw [hvirtual] at hpositive
  have hnat : QuaternionicSymmetry.delta S.quaternionicDimension <
      Module.finrank ℂ (HolomorphicTwistSections P.tangent P.connection
        C.contact.line 1) := by
    exact_mod_cast (show (QuaternionicSymmetry.delta S.quaternionicDimension : ℝ) <
      (Module.finrank ℂ (HolomorphicTwistSections P.tangent P.connection
        C.contact.line 1) : ℝ) by linarith)
  omega

end
end QuaternionicSymmetry.ManifoldSWSectionDimensionBound
