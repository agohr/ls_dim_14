import QuaternionicSymmetry.ManifoldTangentCharacterNumber

/-! The full actual characteristic integrand for a single symmetric-power
character. This is the finite Chern-root character expansion used in the I1
index comparison; no index or topological class identity is asserted. -/
namespace QuaternionicSymmetry.ManifoldSymmetricPowerCharacterExpansion
open LaurentPolynomial Characters TangentAhatCharacterDensity
open ManifoldTangentCharacterNumber ManifoldTangentTraceRootCandidates
open ManifoldEvenCharacteristicAlgebra ManifoldIntegratedRecoveredCertificates
  ManifoldIntegratedDensityCertificates
open scoped Manifold ContDiff
noncomputable section

/-- The coefficient of the formal degree-`2j` term in the torus character
of `Sym^q H`, with formal roots `±sqrt(u)`. -/
def symmetricPowerCoefficient (q j : ℕ) : ℚ :=
  ∑ a ∈ Finset.range (q+1),
    (((q : ℤ) - 2 * (a : ℤ) : ℤ) : ℚ)^(2*j) / (Nat.factorial (2*j) : ℚ)

theorem taylorCoefficient_chi (q j : ℕ) :
    taylorCoefficient j (chi q) = symmetricPowerCoefficient q j := by
  simp only [chi, map_sum, taylorCoefficient_T, symmetricPowerCoefficient]

variable {R : Type} [CommRing R] [Algebra ℚ R]

/-- Exact A-hat/Chern-character convolution for one nonnegative symmetric
power, retaining all tangent coefficients through the top degree. -/
theorem characterDensity_chi (n q : ℕ) (u : R) (t : ℕ → R) :
    characterDensity n u t (chi q) =
      ∑ j ∈ Finset.range (n+1),
        algebraMap ℚ R (symmetricPowerCoefficient q (n-j)) *
          u^(n-j) * tangentAhatCoefficient t j := by
  simp only [characterDensity, LinearMap.coe_mk, AddHom.coe_mk,
    taylorCoefficient_chi]

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
local instance : Algebra ℚ (Total (E := E) (M := M)) :=
  ManifoldTangentTraceRootCandidates.rationalAlgebra

theorem characteristicFunctional_chi (n q : ℕ)
    (hn : 1 ≤ n)
    (hdim : 4*n = Module.finrank ℝ E) :
    characteristicFunctional Q D n (n-1)
      (show 4*((n-1)+1) = Module.finrank ℝ E by omega) (chi q) =
      integrateGrade Q (n-1)
        (show 4*((n-1)+1) = Module.finrank ℝ E by omega)
        (DirectSum.component ℝ ℕ (Grade (E := E) (M := M)) (n-1+1)
          (∑ j ∈ Finset.range (n+1),
            algebraMap ℚ (Total (E := E) (M := M))
              (symmetricPowerCoefficient q (n-j)) *
              (quarterUTotal Q D)^(n-j) *
                tangentAhatCoefficient (normalizedTangentHalfTrace Q D n) j)) := by
  have hn : n-1+1 = n := by omega
  unfold characteristicFunctional
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  have hden :
      characterDensity (n-1+1) (quarterUTotal Q D)
        (normalizedTangentHalfTrace Q D n) (chi q) =
      ∑ j ∈ Finset.range (n+1),
        algebraMap ℚ (Total (E := E) (M := M))
          (symmetricPowerCoefficient q (n-j)) *
          (quarterUTotal Q D)^(n-j) *
            tangentAhatCoefficient (normalizedTangentHalfTrace Q D n) j := by
    simpa only [hn] using characterDensity_chi n q (quarterUTotal Q D)
      (normalizedTangentHalfTrace Q D n)
  rw [hden]

end
end QuaternionicSymmetry.ManifoldSymmetricPowerCharacterExpansion
