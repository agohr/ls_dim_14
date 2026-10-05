import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerAllVirtualBounds
import QuaternionicSymmetry.IndexCharacterDeduction
import QuaternionicSymmetry.FiniteVirtualCharacterSpan

/-! Arithmetic consequences of the actual tangent virtual-character positivity.
The equality of the holomorphic index functional with the characteristic
functional is an explicit index-theorem input, not proved by the density
calculation. Likewise, Hilbert values are supplied separately. -/
namespace QuaternionicSymmetry.ManifoldVirtualIndexConsequences
open ManifoldTangentCharacterNumber ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveQuaternionicKahlerAllVirtualBounds
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

/-- The I1 identification and the twistor Hilbert values turn a positive
actual virtual characteristic number into the strict real symmetry bound. -/
theorem index_dimension_gt_delta
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hAmann : ManifoldAmannIntersectionInput.AmannKrainesRayInput (E := E) (M := M))
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n ∧ n ≤ 14) (hqdim : S.quaternionicDimension = n)
    (d : ℝ) (hilbertPolynomial : ℤ → ℝ)
    (index : LaurentPolynomial ℚ →ₗ[ℚ] ℝ)
    (hHilbert : IndexCharacterDeduction.HilbertValues n d hilbertPolynomial index)
    (hI1 : ∀ q : ℕ, q ≤ n+2 → q % 2 = n % 2 →
      index (Characters.chi q) =
        characteristicFunctional P.tangent P.connection n (n-1)
          (show 4*((n-1)+1) = Module.finrank ℝ E by
            have h := S.real_finrank; omega) (Characters.chi q)) :
    (QuaternionicSymmetry.delta n : ℝ) < d := by
  have hpositive := virtual_positive_two_fourteen S P hsource hAmann hsp heq38
    n hn hqdim
  have hindex := IndexCharacterDeduction.virtual_index_of_hilbert hn.1 hn.2
    d hilbertPolynomial index hHilbert
  have hvirtual := FiniteVirtualCharacterSpan.maps_virtual_eq_of_chi
    n hn index
      (characteristicFunctional P.tangent P.connection n (n-1)
        (show 4*((n-1)+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)) hI1
  rw [hvirtual] at hindex
  linarith

/-- The integer form used by the finite symmetry-dimension induction. -/
theorem index_dimension_lower_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hAmann : ManifoldAmannIntersectionInput.AmannKrainesRayInput (E := E) (M := M))
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n ∧ n ≤ 14) (hqdim : S.quaternionicDimension = n)
    (d : ℕ) (hilbertPolynomial : ℤ → ℝ)
    (index : LaurentPolynomial ℚ →ₗ[ℚ] ℝ)
    (hHilbert : IndexCharacterDeduction.HilbertValues n (d : ℝ) hilbertPolynomial index)
    (hI1 : ∀ q : ℕ, q ≤ n+2 → q % 2 = n % 2 →
      index (Characters.chi q) =
        characteristicFunctional P.tangent P.connection n (n-1)
          (show 4*((n-1)+1) = Module.finrank ℝ E by
            have h := S.real_finrank; omega) (Characters.chi q)) :
    QuaternionicSymmetry.delta n + 1 ≤ d := by
  have hreal := index_dimension_gt_delta S P hsource hAmann hsp heq38
    n hn hqdim (d : ℝ) hilbertPolynomial index hHilbert hI1
  exact Nat.lt_iff_add_one_le.mp (by exact_mod_cast hreal)

end
end QuaternionicSymmetry.ManifoldVirtualIndexConsequences
