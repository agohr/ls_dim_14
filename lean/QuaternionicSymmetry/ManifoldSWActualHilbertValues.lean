import QuaternionicSymmetry.ManifoldSWEquation22PQK
import QuaternionicSymmetry.ManifoldTwistorSWCohomology
import QuaternionicSymmetry.IndexCharacterDeduction

/-! The cohomological SW inputs give the special values of the *actual*
characteristic functional. The Euler characteristic is used as a function
of integer twists, without postulating an additive extension from twists to
the Laurent character ring. -/
namespace QuaternionicSymmetry.ManifoldSWActualHilbertValues

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldSWEquation22PQK ManifoldTangentCharacterNumber
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

variable [HasSheafify (Opens.grothendieckTopology
    (TopCat.of (SphereBundleTotal P.tangent))) (ModuleCat ℂ)]
  [HasExt.{w} (TopCat.Sheaf (ModuleCat ℂ)
    (TopCat.of (SphereBundleTotal P.tangent)))]

private def actualHilbert
    (A : CompatibleComplexAtlas P.tangent P.connection S.quaternionicDimension)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection
    S.quaternionicDimension A)
    (hfinite : ∀ (r : ℤ) (s : ℕ), FiniteDimensional ℂ
      (holomorphicTwistComplexCohomology P.tangent P.connection C.contact.line r s))
    (r : ℤ) : ℝ :=
  ((holomorphicTwistComplexEulerCharacteristic P.tangent P.connection
    C.contact.line r (2*S.quaternionicDimension+1) (hfinite r) : ℤ) : ℝ)

/-- The source's Euler values and its individual Eq. (2.2) give the precise
Hilbert values required by the finite virtual-character calculation. -/
theorem actual_characteristic_hilbertValues
    (A : CompatibleComplexAtlas P.tangent P.connection S.quaternionicDimension)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection
      S.quaternionicDimension A)
    (hSW : SWEquation22OnPQK S P A C)
    (hn : 2 ≤ S.quaternionicDimension)
    (hCanonical : Nonempty (HolomorphicContactCanonicalIso
      P.tangent P.connection S.quaternionicDimension A C.contact.line))
    (x : SphereBundleTotal P.tangent)
    (hfinite : ∀ (r : ℤ) (s : ℕ), FiniteDimensional ℂ
      (holomorphicTwistComplexCohomology P.tangent P.connection C.contact.line r s))
    (hKodairaZero : ∀ s, 0 < s → s ≤ 2*S.quaternionicDimension+1 →
      Subsingleton (holomorphicTwistComplexCohomology P.tangent P.connection
        C.contact.line 0 s))
    (hKodairaOne : ∀ s, 0 < s → s ≤ 2*S.quaternionicDimension+1 →
      Subsingleton (holomorphicTwistComplexCohomology P.tangent P.connection
        C.contact.line 1 s))
    (hKodairaNegative : ∀ (r : ℤ), r < 0 → ∀ s, s ≤ 2*S.quaternionicDimension →
      Subsingleton (holomorphicTwistComplexCohomology P.tangent P.connection
        C.contact.line r s))
    (hSerre : ∀ (r : ℤ) (s : ℕ), s ≤ 2*S.quaternionicDimension+1 →
      Module.finrank ℂ (holomorphicTwistComplexCohomology P.tangent P.connection
        C.contact.line r s) =
      Module.finrank ℂ (holomorphicTwistComplexCohomology P.tangent P.connection
        C.contact.line (-r-(S.quaternionicDimension:ℤ)-1)
          (2*S.quaternionicDimension+1-s))) :
    IndexCharacterDeduction.HilbertValues S.quaternionicDimension
      (Module.finrank ℂ (HolomorphicTwistSections P.tangent P.connection
        C.contact.line 1) : ℝ)
      (actualHilbert S P A C hfinite)
      (characteristicFunctional P.tangent P.connection
        S.quaternionicDimension (S.quaternionicDimension-1)
        (show 4*((S.quaternionicDimension-1)+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold actualHilbert
    exact_mod_cast sw_hilbert_zero_eq_one P C hn S.real_finrank hCanonical x
      (hfinite 0) hKodairaZero
  · unfold actualHilbert
    exact_mod_cast sw_hilbert_nonnegative_eq_sections P C hn S.real_finrank
      hCanonical 1 (by omega) (hfinite 1) hKodairaOne
  · intro j hj hjn
    unfold actualHilbert
    exact_mod_cast sw_hilbert_negative_root P C hn S.real_finrank hCanonical
      (-(j:ℤ)) (by omega) (by omega) hfinite hKodairaNegative hSerre
  · intro r hr
    exact (sw_equation22_at_twist S P A C hSW hn r hr (hfinite r)).symm

theorem actual_characteristic_specialValues
    (A : CompatibleComplexAtlas P.tangent P.connection S.quaternionicDimension)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection
      S.quaternionicDimension A)
    (hSW : SWEquation22OnPQK S P A C)
    (hn : 2 ≤ S.quaternionicDimension)
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
    IndexCharacterDeduction.SpecialValues S.quaternionicDimension
      (Module.finrank ℂ (HolomorphicTwistSections P.tangent P.connection
        C.contact.line 1) : ℝ)
      (characteristicFunctional P.tangent P.connection
        S.quaternionicDimension (S.quaternionicDimension-1)
        (show 4*((S.quaternionicDimension-1)+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)) :=
  IndexCharacterDeduction.specialValues_of_hilbert
    (actual_characteristic_hilbertValues S P A C hSW hn hCanonical x hfinite
      hKodairaZero hKodairaOne hKodairaNegative hSerre)

/-- The finite character calculation now applies directly to the actual
integrated Chern--Weil functional; no virtual index formula is assumed in
the SW source premise. -/
theorem actual_virtual_eq_sections_sub_delta
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
    characteristicFunctional P.tangent P.connection
      S.quaternionicDimension (S.quaternionicDimension-1)
      (show 4*((S.quaternionicDimension-1)+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega)
      (Characters.virtual S.quaternionicDimension) =
      (Module.finrank ℂ (HolomorphicTwistSections P.tangent P.connection
        C.contact.line 1) : ℝ) -
      (QuaternionicSymmetry.delta S.quaternionicDimension : ℝ) := by
  exact IndexCharacterDeduction.virtual_index_of_hilbert hn.1 hn.2
    (Module.finrank ℂ (HolomorphicTwistSections P.tangent P.connection
      C.contact.line 1) : ℝ)
    (actualHilbert S P A C hfinite)
    (characteristicFunctional P.tangent P.connection
      S.quaternionicDimension (S.quaternionicDimension-1)
      (show 4*((S.quaternionicDimension-1)+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega))
    (actual_characteristic_hilbertValues S P A C hSW hn.1 hCanonical x hfinite
      hKodairaZero hKodairaOne hKodairaNegative hSerre)

end
end QuaternionicSymmetry.ManifoldSWActualHilbertValues
