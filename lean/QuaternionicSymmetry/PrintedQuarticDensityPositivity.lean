import QuaternionicSymmetry.PrintedQuarticOrbitalPositivity
import QuaternionicSymmetry.QuarticOrbitalDensityBridge
import QuaternionicSymmetry.PrintedProjectionCubicPositivity

/-! Pointwise quartic orbital signs in the exact six-variable density ring. -/
namespace QuaternionicSymmetry.PrintedQuarticDensityPositivity

open MvPolynomial Module QuaternionicFundamental QuaternionicTracePositivity
  MatrixTracePolynomial PrintedProjectionCubicPositivity

set_option maxHeartbeats 800000

noncomputable section

private theorem eval_includeQuartic {R : Type*} [CommRing R] [Algebra ℚ R]
    (v : Fin 6 → R) (p : QuarticOrbitalEleven.P) :
    aeval v (QuarticOrbitalDensityBridge.includeQuartic p) =
      aeval ![v 1, v 2, v 3, v 4] p := by
  have hv : (fun i : Fin 4 => aeval v
      (![DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2,
        DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4] i)) =
      ![v 1, v 2, v 3, v 4] := by
    funext i
    fin_cases i <;> simp [DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2,
      DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4]
  simpa only [QuarticOrbitalDensityBridge.includeQuartic, hv] using
    MvPolynomial.comp_aeval_apply
      ![DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2,
        DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4] (aeval v) p

variable {ι β V : Type*} [Fintype ι] [Fintype β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
private theorem eval_includeQuartic_forms {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (η : β → E V) (p : QuarticOrbitalEleven.P) :
    aeval (densityValues Q c B η) (QuarticOrbitalDensityBridge.includeQuartic p) =
      embed (V := V) (aeval ![signedTracePower (complexifiedMatrix B η) 1,
        signedTracePower (complexifiedMatrix B η) 2,
        signedTracePower (complexifiedMatrix B η) 3,
        signedTracePower (complexifiedMatrix B η) 4] p) := by
  rw [eval_includeQuartic]
  have hm := MvPolynomial.comp_aeval_apply
    ![signedTracePower (complexifiedMatrix B η) 1,
      signedTracePower (complexifiedMatrix B η) 2,
      signedTracePower (complexifiedMatrix B η) 3,
      signedTracePower (complexifiedMatrix B η) 4]
    ((embed (V := V)).restrictScalars ℚ) p
  have hf : (fun i : Fin 4 => ((embed (V := V)).restrictScalars ℚ)
      (![signedTracePower (complexifiedMatrix B η) 1,
        signedTracePower (complexifiedMatrix B η) 2,
        signedTracePower (complexifiedMatrix B η) 3,
        signedTracePower (complexifiedMatrix B η) 4] i)) =
      ![densityValues Q c B η 1, densityValues Q c B η 2,
        densityValues Q c B η 3, densityValues Q c B η 4] := by
    funext i
    fin_cases i <;> rfl
  rw [hf] at hm
  exact hm.symm

theorem orbital11_density_mixed_in_positive_ray
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (a : List ℕ) (ha : a.length ≤ 11)
    (B : β → Matrix (Fin 11 ⊕ Fin 11) (Fin 11 ⊕ Fin 11) ℂ)
    (hB : ∀ b, QuaternionicMatrixModel.HermitianAntiSelfDual (B b))
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 4 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (aeval (densityValues Q c B η) (QuarticOrbitalDensityBridge.orbital11 a) *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 4)) := by
  obtain ⟨r, hr, he⟩ := PrintedQuarticOrbitalPositivity.orbital11_mem_positiveRay
    hsource a ha B hB Q c η hη hk
  refine ⟨r, hr, ?_⟩
  rw [QuarticOrbitalDensityBridge.orbital11, eval_includeQuartic_forms]
  have hm := congrArg (embed (V := V)) he
  rw [map_mul, map_pow] at hm
  exact hm.trans ((embed (V := V)).toLinearMap.map_smul r (topForm Q c))

theorem orbital12_density_mixed_in_positive_ray
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (a : List ℕ) (ha : a.length ≤ 12)
    (B : β → Matrix (Fin 12 ⊕ Fin 12) (Fin 12 ⊕ Fin 12) ℂ)
    (hB : ∀ b, QuaternionicMatrixModel.HermitianAntiSelfDual (B b))
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 4 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (aeval (densityValues Q c B η) (QuarticOrbitalDensityBridge.orbital12 a) *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 4)) := by
  obtain ⟨r, hr, he⟩ := PrintedQuarticOrbitalPositivity.orbital12_mem_positiveRay
    hsource a ha B hB Q c η hη hk
  refine ⟨r, hr, ?_⟩
  rw [QuarticOrbitalDensityBridge.orbital12, eval_includeQuartic_forms]
  have hm := congrArg (embed (V := V)) he
  rw [map_mul, map_pow] at hm
  exact hm.trans ((embed (V := V)).toLinearMap.map_smul r (topForm Q c))

end
end QuaternionicSymmetry.PrintedQuarticDensityPositivity
