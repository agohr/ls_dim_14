import QuaternionicSymmetry.OrbitalPointwisePolynomialSign
import QuaternionicSymmetry.QuaternionicTracePositivity
import QuaternionicSymmetry.H2WitnessThirteenChecks
import QuaternionicSymmetry.H2WitnessFourteenChecks

/-! The E14 orbital groups evaluated on genuine quaternionic two-forms.
Only the registered scalar orbital integral formula remains an input.
The Hodge-square term is intentionally absent from this pointwise statement. -/

namespace QuaternionicSymmetry.QuaternionicE14OrbitalPointwise

open Module MvPolynomial QuaternionicFundamental QuaternionicTracePositivity
  MatrixTracePolynomial OrbitalMatrixPolynomialBridge
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

theorem eval_embed13 {R : Type*} [CommRing R] [Algebra ℚ R]
    (v : Fin 7 → R) (p : FiniteTypeCSchurSix.P) :
    aeval v (H2WitnessThirteen.embed p) =
      aeval (fun i : Fin 6 => v i.succ) p := by
  rw [H2WitnessThirteen.embed, comp_aeval_apply]
  congr 2
  funext i
  fin_cases i <;> simp [DimensionThirteenFourteenDensity.p1,
    DimensionThirteenFourteenDensity.p2, DimensionThirteenFourteenDensity.p3,
    DimensionThirteenFourteenDensity.p4, DimensionThirteenFourteenDensity.p5,
    DimensionThirteenFourteenDensity.p6]

theorem eval_embed14 {R : Type*} [CommRing R] [Algebra ℚ R]
    (v : Fin 7 → R) (p : FiniteTypeCSchurSix.P) :
    aeval v (H2WitnessFourteen.embed p) =
      aeval (fun i : Fin 6 => v i.succ) p :=
  eval_embed13 v p

variable {ι β V : Type*} [Fintype ι] [Fintype β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The fundamental form and all six signed trace generators, before
the common positive curvature rescaling. -/
def sevenValues {n : ℕ} (Q : QuaternionicStructure V) (b : Basis ι ℝ V) (s : ℝ)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (η : β → E V) : Fin 7 → CE V :=
  Fin.cases (s • embed (V := V) (form Q b)) (fun i : Fin 6 =>
    embed (V := V) (signedTracePower (complexifiedMatrix A η) (i.val + 1)))

omit [FiniteDimensional ℝ V] in
theorem eval_embed_forms {n : ℕ} (Q : QuaternionicStructure V)
    (b : Basis ι ℝ V) (s : ℝ)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (η : β → E V) (p : FiniteTypeCSchurSix.P) :
    aeval (sevenValues Q b s A η) (H2WitnessThirteen.embed p) =
      embed (V := V) (aeval (fun i : Fin 6 =>
        signedTracePower (complexifiedMatrix A η) (i.val + 1)) p) := by
  rw [eval_embed13]
  exact (comp_aeval_apply _ ((embed (V := V)).restrictScalars ℚ) p).symm

theorem orbital_term_in_positive_ray
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (n k : ℕ) (hn : 11 ≤ n) (hk : k ≤ 6)
    (a : List ℕ) (ha : a.length ≤ n)
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V) (s : ℝ) (hs : 0 ≤ s)
    (hqdim : Q.quaternionicDimension = n)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hA : ∀ i, QuaternionicMatrixModel.HermitianAntiSelfDual (A i))
    (η : β → E V) (hη : ∀ i, η i ∈ HyperholomorphicExterior.formSpace Q b) :
    PositiveRay.Contains (embed (V := V) (topForm Q b))
      (aeval (sevenValues Q b s A η)
        (DimensionThirteenFourteenDensity.u ^ (n-k) *
          H2WitnessThirteen.embed (FiniteTypeCSchurSix.orbital n k a))) := by
  rw [map_mul, map_pow, DimensionThirteenFourteenDensity.u, aeval_X,
    eval_embed_forms]
  change PositiveRay.Contains _ ((s • embed (V := V) (form Q b)) ^ (n-k) * _)
  rw [smul_pow, smul_mul_assoc]
  apply PositiveRay.smul ?_ (pow_nonneg hs _)
  obtain ⟨r, hr, he⟩ := OrbitalPointwisePolynomialSign.orbital_mem_positiveRay
    hsource n k hn hk a ha A hA Q b η hη (by omega)
  refine ⟨r, hr, ?_⟩
  have hm := congrArg (embed (V := V)) he
  rw [map_mul, map_pow, hqdim] at hm
  rw [mul_comm]
  exact hm.trans ((embed (V := V)).toLinearMap.map_smul r (topForm Q b))

end
end QuaternionicSymmetry.QuaternionicE14OrbitalPointwise
