import QuaternionicSymmetry.FiniteTypeCSchurSix
import QuaternionicSymmetry.QuarticOrbitalTwelve

/-! The printed quartic orbitals are instances of the finite Schur family. -/

namespace QuaternionicSymmetry.QuarticOrbitalFiniteBridge

open MvPolynomial
noncomputable section

variable {R : Type*} [CommRing R] [Algebra ℚ R]

private def includeQuartic : QuarticOrbitalEleven.P →ₐ[ℚ] FiniteTypeCSchurSix.P :=
  aeval ![X 0, X 1, X 2, X 3]

private theorem schur_polynomial :
    FiniteTypeCSchurSix.schur [4] = includeQuartic QuarticOrbitalEleven.s₄ ∧
    FiniteTypeCSchurSix.schur [3, 1] = includeQuartic QuarticOrbitalEleven.s₃₁ ∧
    FiniteTypeCSchurSix.schur [2, 2] = includeQuartic QuarticOrbitalEleven.s₂₂ ∧
    FiniteTypeCSchurSix.schur [2, 1, 1] = includeQuartic QuarticOrbitalEleven.s₂₁₁ ∧
    FiniteTypeCSchurSix.schur [1, 1, 1, 1] = includeQuartic QuarticOrbitalEleven.s₁₁₁₁ := by
  repeat' constructor
  all_goals
    apply MvPolynomial.funext
    intro v
  all_goals
    norm_num [includeQuartic, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, FiniteTypeCSchurSix.schur, FiniteTypeCSchurSix.h4,
      FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h1,
      FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e3, FiniteTypeCSchurSix.e2,
      FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
      FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4,
      QuarticOrbitalEleven.s₄, QuarticOrbitalEleven.s₃₁, QuarticOrbitalEleven.s₂₂,
      QuarticOrbitalEleven.s₂₁₁, QuarticOrbitalEleven.s₁₁₁₁,
      QuarticOrbitalEleven.h₁, QuarticOrbitalEleven.h₂,
      QuarticOrbitalEleven.h₃, QuarticOrbitalEleven.h₄,
      QuarticOrbitalEleven.p₁, QuarticOrbitalEleven.p₂,
      QuarticOrbitalEleven.p₃, QuarticOrbitalEleven.p₄]
    ring

private theorem schur_eval (v : Fin 6 → R) :
    aeval v (FiniteTypeCSchurSix.schur [4]) =
        aeval ![v 0, v 1, v 2, v 3] QuarticOrbitalEleven.s₄ ∧
    aeval v (FiniteTypeCSchurSix.schur [3, 1]) =
        aeval ![v 0, v 1, v 2, v 3] QuarticOrbitalEleven.s₃₁ ∧
    aeval v (FiniteTypeCSchurSix.schur [2, 2]) =
        aeval ![v 0, v 1, v 2, v 3] QuarticOrbitalEleven.s₂₂ ∧
    aeval v (FiniteTypeCSchurSix.schur [2, 1, 1]) =
        aeval ![v 0, v 1, v 2, v 3] QuarticOrbitalEleven.s₂₁₁ ∧
    aeval v (FiniteTypeCSchurSix.schur [1, 1, 1, 1]) =
        aeval ![v 0, v 1, v 2, v 3] QuarticOrbitalEleven.s₁₁₁₁ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := schur_polynomial
  rw [h1, h2, h3, h4, h5]
  have he (p : QuarticOrbitalEleven.P) :
      aeval v (includeQuartic p) = aeval ![v 0, v 1, v 2, v 3] p := by
    have hv : (fun i : Fin 4 => aeval v ((![X 0, X 1, X 2, X 3] : Fin 4 → FiniteTypeCSchurSix.P) i)) =
        ![v 0, v 1, v 2, v 3] := by
      funext i
      fin_cases i <;> simp
    simpa only [includeQuartic, hv] using
      (MvPolynomial.comp_aeval_apply ![X 0, X 1, X 2, X 3] (aeval v) p)
  simp only [he, and_self]

private theorem schur_values (a : List ℕ) :
    FiniteTypeCSchurSix.schurValue a [4] = QuarticOrbitalEleven.schurValues a 0 ∧
    FiniteTypeCSchurSix.schurValue a [3, 1] = QuarticOrbitalEleven.schurValues a 1 ∧
    FiniteTypeCSchurSix.schurValue a [2, 2] = QuarticOrbitalEleven.schurValues a 2 ∧
    FiniteTypeCSchurSix.schurValue a [2, 1, 1] = QuarticOrbitalEleven.schurValues a 3 ∧
    FiniteTypeCSchurSix.schurValue a [1, 1, 1, 1] = QuarticOrbitalEleven.schurValues a 4 := by
  have hv : (fun i : Fin 4 => QuarticOrbitalEleven.powerSum a (i.val + 1)) =
      ![FiniteTypeCSchurSix.powerSum a 1, FiniteTypeCSchurSix.powerSum a 2,
        FiniteTypeCSchurSix.powerSum a 3, FiniteTypeCSchurSix.powerSum a 4] := by
    funext i
    fin_cases i <;> rfl
  simpa [FiniteTypeCSchurSix.schurValue, QuarticOrbitalEleven.schurValues,
    QuarticOrbitalEleven.evalSpectrum, hv] using
    schur_eval (fun i : Fin 6 => FiniteTypeCSchurSix.powerSum a (i.val + 1))

theorem orbital11_eval (a : List ℕ) (v : Fin 6 → R) :
    aeval v (FiniteTypeCSchurSix.orbital 11 4 a) =
      aeval ![v 0, v 1, v 2, v 3] (QuarticOrbitalEleven.orbital a) := by
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := schur_eval v
  obtain ⟨ha1, ha2, ha3, ha4, ha5⟩ := schur_values a
  obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := QuarticOrbitalEleven.rho_factorials
  norm_num [FiniteTypeCSchurSix.orbital, FiniteTypeCSchurSix.partitions,
    QuarticOrbitalEleven.orbital, hr1, hr2, hr3, hr4, hr5,
    ha1, ha2, ha3, ha4, ha5, hs1, hs2, hs3, hs4, hs5, map_ofNat]
  ring

theorem orbital12_eval (a : List ℕ) (v : Fin 6 → R) :
    aeval v (FiniteTypeCSchurSix.orbital 12 4 a) =
      aeval ![v 0, v 1, v 2, v 3] (QuarticOrbitalTwelve.orbital a) := by
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := schur_eval v
  obtain ⟨ha1, ha2, ha3, ha4, ha5⟩ := schur_values a
  obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := QuarticOrbitalTwelve.rho_factorials
  norm_num [FiniteTypeCSchurSix.orbital, FiniteTypeCSchurSix.partitions,
    QuarticOrbitalTwelve.orbital, hr1, hr2, hr3, hr4, hr5,
    ha1, ha2, ha3, ha4, ha5, hs1, hs2, hs3, hs4, hs5, map_ofNat]
  ring

end
end QuaternionicSymmetry.QuarticOrbitalFiniteBridge
