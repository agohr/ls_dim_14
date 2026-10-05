import QuaternionicSymmetry.H2OrbitalPointwise

/-! The complete orbital portions of the printed dimension13/14 witnesses
have the required pointwise sign. Their Hodge-square portions remain separate. -/
namespace QuaternionicSymmetry.H2OrbitalDensityPointwise

open Module MvPolynomial QuaternionicFundamental MatrixTracePolynomial H2OrbitalPointwise
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

private theorem eval_embed {R : Type*} [CommRing R] [Algebra ℚ R]
    (u : R) (v : Fin 6 → R) (p : FiniteTypeCSchurSix.P) :
    aeval (Fin.cases u v) (H2WitnessThirteen.embed p) = aeval v p := by
  have he : (fun i : Fin 6 => aeval (Fin.cases u v)
      (![DimensionThirteenFourteenDensity.p1, DimensionThirteenFourteenDensity.p2,
        DimensionThirteenFourteenDensity.p3, DimensionThirteenFourteenDensity.p4,
        DimensionThirteenFourteenDensity.p5, DimensionThirteenFourteenDensity.p6] i)) = v := by
    ext i
    fin_cases i <;> simp [DimensionThirteenFourteenDensity.p1, DimensionThirteenFourteenDensity.p2,
      DimensionThirteenFourteenDensity.p3, DimensionThirteenFourteenDensity.p4,
      DimensionThirteenFourteenDensity.p5, DimensionThirteenFourteenDensity.p6]
    all_goals rfl
  simpa only [H2WitnessThirteen.embed, he] using MvPolynomial.comp_aeval_apply
    ![DimensionThirteenFourteenDensity.p1, DimensionThirteenFourteenDensity.p2,
      DimensionThirteenFourteenDensity.p3, DimensionThirteenFourteenDensity.p4,
      DimensionThirteenFourteenDensity.p5, DimensionThirteenFourteenDensity.p6]
    (aeval (Fin.cases u v)) p

private theorem eval_orbitalSum13 {R : Type*} [CommRing R] [Algebra ℚ R]
    (u : R) (v : Fin 6 → R) :
    aeval (Fin.cases u v) H2WitnessThirteen.orbitalSum =
      ∑ i : Fin 6, aeval v (groups13 i) * u ^ (13-(i.val+1)) := by
  simp only [H2WitnessThirteen.orbitalSum, map_add, map_mul, map_pow, eval_embed,
    DimensionThirteenFourteenDensity.u, aeval_X, Fin.cases_zero]
  simp [Fin.sum_univ_succ, groups13]
  ring

private theorem eval_orbitalSum14 {R : Type*} [CommRing R] [Algebra ℚ R]
    (u : R) (v : Fin 6 → R) :
    aeval (Fin.cases u v) H2WitnessFourteen.orbitalSum =
      ∑ i : Fin 6, aeval v (groups14 i) * u ^ (14-(i.val+1)) := by
  simp only [H2WitnessFourteen.orbitalSum, H2WitnessFourteen.embed,
    map_add, map_mul, map_pow, eval_embed,
    DimensionThirteenFourteenDensity.u, aeval_X, Fin.cases_zero]
  simp [Fin.sum_univ_succ, groups14]
  ring

variable {ι β V : Type*} [Fintype ι] [Fintype β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem orbitalSum13_mem_positiveRay
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (B : β → Matrix (Fin 13 ⊕ Fin 13) (Fin 13 ⊕ Fin 13) ℂ)
    (hB : ∀ b, QuaternionicMatrixModel.HermitianAntiSelfDual (B b))
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V) (hn : Q.quaternionicDimension = 13)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c) :
    PositiveRay.Contains (topForm Q c)
      (aeval (Fin.cases (form Q c)
        (fun i : Fin 6 => signedTracePower (complexifiedMatrix B η) (i.val+1)))
        H2WitnessThirteen.orbitalSum) := by
  rw [eval_orbitalSum13]
  apply PositiveRay.sum
  intro i
  simpa only [hn] using groups13_mem_positiveRay hsource B hB Q c η hη (by omega) i

theorem orbitalSum14_mem_positiveRay
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (B : β → Matrix (Fin 14 ⊕ Fin 14) (Fin 14 ⊕ Fin 14) ℂ)
    (hB : ∀ b, QuaternionicMatrixModel.HermitianAntiSelfDual (B b))
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V) (hn : Q.quaternionicDimension = 14)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c) :
    PositiveRay.Contains (topForm Q c)
      (aeval (Fin.cases (form Q c)
        (fun i : Fin 6 => signedTracePower (complexifiedMatrix B η) (i.val+1)))
        H2WitnessFourteen.orbitalSum) := by
  rw [eval_orbitalSum14]
  apply PositiveRay.sum
  intro i
  simpa only [hn] using groups14_mem_positiveRay hsource B hB Q c η hη (by omega) i

end
end QuaternionicSymmetry.H2OrbitalDensityPointwise
