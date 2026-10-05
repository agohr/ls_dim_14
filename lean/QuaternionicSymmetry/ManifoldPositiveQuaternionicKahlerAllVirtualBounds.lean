import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerLowerVirtualBounds
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerVirtualBounds
import QuaternionicSymmetry.ManifoldE14VirtualBounds

/-! Uniform positivity of the actual tangent virtual-character functional
in the finite quaternionic-dimensional ranges. The Euler-characteristic and
symmetry-dimension comparisons remain separate. -/
namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerAllVirtualBounds
open ManifoldTangentCharacterNumber ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveQuaternionicKahlerLowerVirtualBounds
open ManifoldPositiveQuaternionicKahlerVirtualBounds
open ManifoldE14VirtualBounds
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

theorem virtual_positive_two_ten
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n ∧ n ≤ 10) (hqdim : S.quaternionicDimension = n) :
    0 < characteristicFunctional P.tangent P.connection n (n-1)
      (show 4*((n-1)+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega) (Characters.virtual n) := by
  rcases hn with ⟨hn2, hn10⟩
  interval_cases n
  · exact virtual2_positive S P hsp heq38 hqdim
  · exact virtual3_positive S P hsp heq38 hqdim
  · exact virtual4_positive S P hsp heq38 hqdim
  · exact virtual5_positive S P hsp heq38 hqdim
  · exact virtual6_positive S P hsp heq38 hqdim
  · exact virtual7_positive S P hsp heq38 hqdim
  · exact virtual8_positive S P hsp heq38 hqdim
  · exact virtual9_positive S P hsp heq38 hqdim
  · exact virtual10_positive S P hsp heq38 hqdim

theorem virtual_positive_two_twelve
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n ∧ n ≤ 12) (hqdim : S.quaternionicDimension = n) :
    0 < characteristicFunctional P.tangent P.connection n (n-1)
      (show 4*((n-1)+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega) (Characters.virtual n) := by
  rcases hn with ⟨hn2, hn12⟩
  by_cases hn10 : n ≤ 10
  · exact virtual_positive_two_ten S P hsp heq38 n ⟨hn2, hn10⟩ hqdim
  · have hn11 : 11 ≤ n := by omega
    interval_cases n
    · exact virtual11_positive S P hsource hsp heq38 hqdim
    · exact virtual12_positive S P hsource hsp heq38 hqdim

theorem virtual_positive_two_fourteen
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hAmann : ManifoldAmannIntersectionInput.AmannKrainesRayInput (E := E) (M := M))
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n ∧ n ≤ 14) (hqdim : S.quaternionicDimension = n) :
    0 < characteristicFunctional P.tangent P.connection n (n-1)
      (show 4*((n-1)+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega) (Characters.virtual n) := by
  rcases hn with ⟨hn2, hn14⟩
  by_cases hn12 : n ≤ 12
  · exact virtual_positive_two_twelve S P hsource hsp heq38 n ⟨hn2, hn12⟩ hqdim
  · have hn13 : 13 ≤ n := by omega
    interval_cases n
    · exact virtual13_positive S P hsource hAmann hsp heq38 hqdim
    · exact virtual14_positive S P hsource hAmann hsp heq38 hqdim

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerAllVirtualBounds
