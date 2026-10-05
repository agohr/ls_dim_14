import QuaternionicSymmetry.ManifoldSWSectionDimensionBound
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerQuantitativeBounds
import QuaternionicSymmetry.ManifoldKillingFieldsPaperVirtualBound
import QuaternionicSymmetry.ManifoldTwistorSWKillingComparison

/-! The full quantitative Killing-field bound `d ≥ c_n + v_n U` from
Four Killing fields suffice, for `2 ≤ n ≤ 14`. The volume term is the
canonical integral of the actual quarter-Pontryagin form. The existing
source premises and cohomological identifications are retained explicitly. -/
namespace QuaternionicSymmetry.ManifoldSWKillingVolumeBound
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldSWSectionDimensionBound ManifoldSWEquation22PQK
open ManifoldSWActualHilbertValues
open ManifoldPositiveQuaternionicKahlerQuantitativeBounds
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
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

section Cohomology
variable [HasSheafify (Opens.grothendieckTopology
    (TopCat.of (SphereBundleTotal P.tangent))) (ModuleCat ℂ)]
  [HasExt.{w} (TopCat.Sheaf (ModuleCat ℂ)
    (TopCat.of (SphereBundleTotal P.tangent)))]

theorem killing_dimension_volume_lower_bound
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
          (2*S.quaternionicDimension+1-s)))
    (hSalamon : HolomorphicTwistSections P.tangent P.connection C.contact.line 1 ≃ₗ[ℂ]
      ManifoldQuaternionicKillingFields.ComplexKillingFields P.tangent) :
    (delta S.quaternionicDimension : ℝ) +
      (scalarCoefficient S.quaternionicDimension : ℝ) * quaternionicVolume S P ≤
      (ManifoldQuaternionicKillingFields.killingDimension P.tangent : ℝ) := by
  have hbound := ManifoldKillingFieldsPaperVirtualBound.virtual_quarter_bound S P hsource hAmann hsp heq38
    S.quaternionicDimension hn rfl
  have hvirtual := actual_virtual_eq_sections_sub_delta S P A C hSW hn hCanonical
    x hfinite hKodairaZero hKodairaOne hKodairaNegative hSerre
  rw [hvirtual, hSalamon.finrank_eq,
    ManifoldQuaternionicKillingFields.complexKillingFields_finrank] at hbound
  change (scalarCoefficient S.quaternionicDimension : ℝ) * quaternionicVolume S P ≤
    (ManifoldQuaternionicKillingFields.killingDimension P.tangent : ℝ) -
      (delta S.quaternionicDimension : ℝ) at hbound
  linarith

end Cohomology

/-- The strict middle inequality in the paper's corollary. No integrality
of quaternionic volume is required. -/
theorem offset_lt_volume_lower_bound
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) :
    (delta S.quaternionicDimension : ℝ) <
      (delta S.quaternionicDimension : ℝ) +
        (scalarCoefficient S.quaternionicDimension : ℝ) * quaternionicVolume S P := by
  have hc : (0 : ℝ) < scalarCoefficient S.quaternionicDimension := by
    exact_mod_cast scalarCoefficient_pos (by omega : 0 < S.quaternionicDimension)
  exact lt_add_of_pos_right _ (mul_pos hc (quaternionicVolume_pos S P hsp heq38 hn))

end
end QuaternionicSymmetry.ManifoldSWKillingVolumeBound
