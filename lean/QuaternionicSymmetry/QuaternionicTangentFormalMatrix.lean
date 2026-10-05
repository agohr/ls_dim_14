import QuaternionicSymmetry.QuaternionicCurvatureFiniteExpansion
import QuaternionicSymmetry.RealifiedTracePolynomial
import QuaternionicSymmetry.CommutativeMatrixEvenBinomial
import QuaternionicSymmetry.ContinuousEndomorphismMatrixTrace
import QuaternionicSymmetry.QuaternionicTraceOrthogonality

/-! Universal polynomial matrices for a quaternion-linear symplectic block
and a scalar quaternionic block in a fixed real basis. -/
namespace QuaternionicSymmetry.QuaternionicTangentFormalMatrix
open Module QuaternionicCurvatureFiniteExpansion QuaternionicLieAlgebraProjection
  VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
  QuaternionicUniversalEvenTrace RealifiedTracePolynomial
  ContinuousEndomorphismMatrix LocalEndomorphismTrace
open scoped Quaternion
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
variable (S : QuaternionicStructure E)

abbrev SpIndex := QuaternionicCurvatureFiniteExpansion.Index S
abbrev Index := SpIndex S ⊕ Fin 3
abbrev MatrixIndex := Fin (Module.finrank ℝ E)

private def realBasis : Basis (MatrixIndex (E := E)) ℝ E := Module.finBasis ℝ E

def spOperator (a : SpIndex S) : E →L[ℝ] E := (operatorBasis S a).val

def scalarOperator (i : Fin 3) : E →L[ℝ] E :=
  synth S (Pi.single i 1)

def spMatrix (a : SpIndex S) : Matrix (MatrixIndex (E := E))
    (MatrixIndex (E := E)) ℝ :=
  LinearMap.toMatrix realBasis realBasis (spOperator S a).toLinearMap

def scalarMatrix (i : Fin 3) : Matrix (MatrixIndex (E := E))
    (MatrixIndex (E := E)) ℝ :=
  LinearMap.toMatrix realBasis realBasis (scalarOperator S i).toLinearMap

def spPolynomial : Matrix (MatrixIndex (E := E))
    (MatrixIndex (E := E)) (MvPolynomial (Index S) ℝ) :=
  combination (spMatrix S) (fun a => MvPolynomial.X (Sum.inl a))

def scalarPolynomial : Matrix (MatrixIndex (E := E))
    (MatrixIndex (E := E)) (MvPolynomial (Index S) ℝ) :=
  combination (scalarMatrix S) (fun i => MvPolynomial.X (Sum.inr i))

def fullPolynomial : Matrix (MatrixIndex (E := E))
    (MatrixIndex (E := E)) (MvPolynomial (Index S) ℝ) :=
  spPolynomial S + scalarPolynomial S

def spValue (x : Index S → ℝ) : E →L[ℝ] E :=
  ∑ a : SpIndex S, x (Sum.inl a) • spOperator S a

/-- Each finite basis operator is quaternion-linear and hence commutes
with every scalar quaternionic combination. -/
theorem spOperator_commutes_synth (a : SpIndex S) (b : Fin 3 → ℝ) :
    spOperator S a * synth S b = synth S b * spOperator S a := by
  have hmem := (operatorBasis S a).property
  have hI := ((S.mem_skewCentralizer_iff _).mp hmem).2.1
  have hJ := ((S.mem_skewCentralizer_iff _).mp hmem).2.2
  have hgen (i : Fin 3) :
      spOperator S a * quaternionicGenerator S i =
        quaternionicGenerator S i * spOperator S a := by
    fin_cases i
    · apply ContinuousLinearMap.ext
      intro v
      exact hI v
    · apply ContinuousLinearMap.ext
      intro v
      exact hJ v
    · apply ContinuousLinearMap.ext
      intro v
      change spOperator S a (S.I (S.J v)) =
        S.I (S.J (spOperator S a v))
      calc
        spOperator S a (S.I (S.J v)) = S.I (spOperator S a (S.J v)) := hI _
        _ = S.I (S.J (spOperator S a v)) := congrArg S.I (hJ _)
  rw [ManifoldQuaternionicRankThreeOrthogonal.synth_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun z => b i • z) (hgen i))

/-- Every real linear combination of the centralizer basis commutes with
all three scalar quaternionic generators. -/
theorem spValue_commutes_synth (x : Index S → ℝ) (b : Fin 3 → ℝ) :
    spValue S x * synth S b = synth S b * spValue S x := by
  unfold spValue
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  exact Finset.sum_congr rfl (fun a _ =>
    congrArg (fun z => x (Sum.inl a) • z) (spOperator_commutes_synth S a b))

def scalarValue (x : Index S → ℝ) : E →L[ℝ] E :=
  ∑ i : Fin 3, x (Sum.inr i) • scalarOperator S i

omit [FiniteDimensional ℝ E] in
theorem scalarValue_eq_synth (x : Index S → ℝ) :
    scalarValue S x = synth S (fun i => x (Sum.inr i)) := by
  have hcoord : (fun i : Fin 3 => x (Sum.inr i)) =
      ∑ i : Fin 3, x (Sum.inr i) • (Pi.single i (1 : ℝ) : Fin 3 → ℝ) := by
    funext j
    simp [Pi.single_apply]
  rw [hcoord, map_sum]
  simp [scalarValue, scalarOperator]

def scalarNormPolynomial : MvPolynomial (Index S) ℝ :=
  ∑ i : Fin 3, MvPolynomial.X (Sum.inr i) *
    MvPolynomial.X (Sum.inr i)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
@[simp] theorem eval_scalarNormPolynomial (x : Index S → ℝ) :
    MvPolynomial.eval x (scalarNormPolynomial S) =
      ∑ i : Fin 3, x (Sum.inr i) * x (Sum.inr i) := by
  simp [scalarNormPolynomial]

omit [FiniteDimensional ℝ E] in
private theorem scalarValue_square (x : Index S → ℝ) :
    (scalarValue S x) ^ 2 =
      (-(∑ i : Fin 3, x (Sum.inr i) * x (Sum.inr i))) •
        (1 : E →L[ℝ] E) := by
  rw [scalarValue_eq_synth]
  have h := QuaternionicScalarTrace.synth_anticommutator
    S (fun i => x (Sum.inr i)) (fun i => x (Sum.inr i))
  change synth S (fun i => x (Sum.inr i)) *
      synth S (fun i => x (Sum.inr i)) +
      synth S (fun i => x (Sum.inr i)) *
      synth S (fun i => x (Sum.inr i)) =
        (-(2 * ∑ i : Fin 3, x (Sum.inr i) * x (Sum.inr i))) •
          (1 : E →L[ℝ] E) at h
  rw [pow_two]
  calc
    synth S (fun i => x (Sum.inr i)) * synth S (fun i => x (Sum.inr i)) =
      (1 / 2 : ℝ) • (synth S (fun i => x (Sum.inr i)) *
        synth S (fun i => x (Sum.inr i)) +
        synth S (fun i => x (Sum.inr i)) * synth S (fun i => x (Sum.inr i))) := by module
    _ = (1 / 2 : ℝ) •
      ((-(2 * ∑ i : Fin 3, x (Sum.inr i) * x (Sum.inr i))) •
        (1 : E →L[ℝ] E)) := by rw [h]
    _ = _ := by module

private local instance : NormedRing (Matrix (MatrixIndex (E := E))
    (MatrixIndex (E := E)) ℝ) := Matrix.linftyOpNormedRing
private local instance : NormedAlgebra ℝ (Matrix (MatrixIndex (E := E))
    (MatrixIndex (E := E)) ℝ) := Matrix.linftyOpNormedAlgebra

omit [Nontrivial E] in
/-- Evaluation of the universal symplectic matrix recovers the concrete
operator expanded in the finite centralizer basis. -/
theorem eval_spPolynomial (x : Index S → ℝ) :
    (MvPolynomial.eval x).mapMatrix (spPolynomial S) =
      ContinuousEndomorphismMatrix.matrixCLM realBasis (spValue S x) := by
  ext i j
  simp [spPolynomial, combination, spMatrix, spValue,
    ContinuousEndomorphismMatrix.matrixCLM_apply,
    map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply,
    MvPolynomial.eval_X, MvPolynomial.eval_C]
  exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)

/-- Evaluation of the scalar matrix recovers the synthesized quaternionic
scalar operator. -/
theorem eval_scalarPolynomial (x : Index S → ℝ) :
    (MvPolynomial.eval x).mapMatrix (scalarPolynomial S) =
      ContinuousEndomorphismMatrix.matrixCLM realBasis (scalarValue S x) := by
  ext i j
  simp [scalarPolynomial, combination, scalarMatrix, scalarValue,
    ContinuousEndomorphismMatrix.matrixCLM_apply,
    map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply,
    MvPolynomial.eval_X, MvPolynomial.eval_C,
    scalarOperator]
  exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)

/-- The formal symplectic and scalar matrices commute as a polynomial
identity, obtained from concrete centralizer commutation at every real point. -/
theorem sp_scalarPolynomial_commute : Commute (spPolynomial S) (scalarPolynomial S) := by
  apply Matrix.ext
  intro i j
  apply MvPolynomial.funext
  intro x
  let b := realBasis (E := E)
  have hc : spValue S x * scalarValue S x =
      scalarValue S x * spValue S x := by
    rw [scalarValue_eq_synth]
    exact spValue_commutes_synth S x (fun i => x (Sum.inr i))
  have hm : (ContinuousEndomorphismMatrix.matrixCLM b (spValue S x)) *
      (ContinuousEndomorphismMatrix.matrixCLM b (scalarValue S x)) =
      (ContinuousEndomorphismMatrix.matrixCLM b (scalarValue S x)) *
      (ContinuousEndomorphismMatrix.matrixCLM b (spValue S x)) := by
    rw [← ContinuousEndomorphismMatrix.matrixCLM_mul,
      ← ContinuousEndomorphismMatrix.matrixCLM_mul, hc]
  change ((MvPolynomial.eval x).mapMatrix
      (spPolynomial S * scalarPolynomial S)) i j =
    ((MvPolynomial.eval x).mapMatrix
      (scalarPolynomial S * spPolynomial S)) i j
  rw [RingHom.mapMatrix_apply, Matrix.map_mul,
    RingHom.mapMatrix_apply, Matrix.map_mul]
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
    eval_spPolynomial S x, eval_scalarPolynomial S x]
  exact congrArg (fun A => A i j) hm

/-- The formal scalar quaternionic matrix has square equal to minus its
coordinate norm times the identity, as a polynomial matrix identity. -/
theorem scalarPolynomial_square :
    (scalarPolynomial S) ^ 2 =
      (-(scalarNormPolynomial S)) •
        (1 : Matrix (MatrixIndex (E := E)) (MatrixIndex (E := E))
          (MvPolynomial (Index S) ℝ)) := by
  apply Matrix.ext
  intro i j
  apply MvPolynomial.funext
  intro x
  let b := realBasis (E := E)
  have hs := scalarValue_square S x
  have hm : (ContinuousEndomorphismMatrix.matrixCLM b (scalarValue S x)) ^ 2 =
      (-(∑ i : Fin 3, x (Sum.inr i) * x (Sum.inr i))) •
        (1 : Matrix (MatrixIndex (E := E)) (MatrixIndex (E := E)) ℝ) := by
    rw [pow_two, ← ContinuousEndomorphismMatrix.matrixCLM_mul,
      ← pow_two, hs, map_smul]
    change (-(∑ i : Fin 3, x (Sum.inr i) * x (Sum.inr i))) •
      ContinuousEndomorphismMatrix.matrixCLM b (1 : E →L[ℝ] E) = _
    have hone : ContinuousEndomorphismMatrix.matrixCLM b (1 : E →L[ℝ] E) =
        (1 : Matrix (MatrixIndex (E := E)) (MatrixIndex (E := E)) ℝ) := by
      change LinearMap.toMatrix b b (1 : E →L[ℝ] E).toLinearMap = 1
      exact LinearMap.toMatrix_one b
    rw [hone]
  have heval : (MvPolynomial.eval x).mapMatrix ((scalarPolynomial S) ^ 2) =
      (MvPolynomial.eval x).mapMatrix
        ((-(scalarNormPolynomial S)) •
          (1 : Matrix (MatrixIndex (E := E)) (MatrixIndex (E := E))
            (MvPolynomial (Index S) ℝ))) := by
    rw [RingHom.mapMatrix_apply, Matrix.map_pow]
    rw [← RingHom.mapMatrix_apply, eval_scalarPolynomial S x]
    rw [hm]
    ext a c
    by_cases hac : a = c <;>
      simp [Matrix.map_apply, Matrix.smul_apply, hac,
        eval_scalarNormPolynomial]
  exact congrArg (fun M => M i j) heval

omit [Nontrivial E] in
private theorem matrixCLM_pow (T : E →L[ℝ] E) (m : ℕ) :
    ContinuousEndomorphismMatrix.matrixCLM realBasis (T ^ m) =
      (ContinuousEndomorphismMatrix.matrixCLM realBasis T) ^ m := by
  induction m with
  | zero =>
      change ContinuousEndomorphismMatrix.matrixCLM realBasis
        (1 : E →L[ℝ] E) = 1
      change LinearMap.toMatrix realBasis realBasis
        (1 : E →L[ℝ] E).toLinearMap = 1
      exact LinearMap.toMatrix_one realBasis
  | succ m ih =>
      rw [pow_succ, ContinuousEndomorphismMatrix.matrixCLM_mul,
        ih, pow_succ]

/-- Every formal odd mixed trace vanishes; the proof evaluates the
polynomial at all real assignments and uses actual quaternionic trace
orthogonality, so it remains valid after nilpotent specialization. -/
theorem odd_mixed_trace_zero (m : ℕ) :
    Matrix.trace ((spPolynomial S) ^ m * scalarPolynomial S) = 0 := by
  apply MvPolynomial.funext
  intro x
  let b := realBasis (E := E)
  have hcomm (a : Fin 3 → ℝ) :
      (spValue S x) ^ m * synth S a = synth S a * (spValue S x) ^ m :=
    (Commute.pow_left (spValue_commutes_synth S x a) m).eq
  have hn : LocalEndomorphismTrace.traceCLM
      ((spValue S x) ^ m * scalarValue S x) = 0 := by
    rw [scalarValue_eq_synth]
    exact QuaternionicTraceOrthogonality.trace_mul_synth S
      ((spValue S x) ^ m) hcomm (fun i => x (Sum.inr i))
  have hmat : Matrix.trace
      ((ContinuousEndomorphismMatrix.matrixCLM b (spValue S x)) ^ m *
        ContinuousEndomorphismMatrix.matrixCLM b (scalarValue S x)) = 0 := by
    rw [← matrixCLM_pow (spValue S x) m,
      ← ContinuousEndomorphismMatrix.matrixCLM_mul]
    change ExteriorMatrixTraceBridge.traceCLM
      (ContinuousEndomorphismMatrix.matrixCLM b
        ((spValue S x) ^ m * scalarValue S x)) = 0
    rw [← ContinuousEndomorphismMatrixTrace.trace_factor_apply]
    exact hn
  change MvPolynomial.eval x
    (Matrix.trace ((spPolynomial S) ^ m * scalarPolynomial S)) = 0
  rw [AddMonoidHom.map_trace]
  change Matrix.trace ((MvPolynomial.eval x).mapMatrix
    ((spPolynomial S) ^ m * scalarPolynomial S)) = 0
  rw [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_pow,
    ← RingHom.mapMatrix_apply, eval_spPolynomial S x,
    ← RingHom.mapMatrix_apply, eval_scalarPolynomial S x]
  exact hmat

/-- Universal tangent-versus-symplectic even trace identity over the real
polynomial ring. It was proved from actual real quaternionic operators at
all assignments, and therefore may be specialized to nilpotent algebras. -/
theorem tangent_even_trace_polynomial (j : ℕ) :
    Matrix.trace ((fullPolynomial S) ^ (2 * j)) =
      ∑ m ∈ Finset.range (2 * j + 1),
        (if Even (2 * j - m) then
          (-(scalarNormPolynomial S)) ^ ((2 * j - m) / 2) *
            Matrix.trace ((spPolynomial S) ^ m)
         else 0) *
          (Nat.choose (2 * j) m : MvPolynomial (Index S) ℝ) := by
  exact CommutativeMatrixEvenBinomial.trace_binomial_even
    (spPolynomial S) (scalarPolynomial S) (scalarNormPolynomial S)
    (sp_scalarPolynomial_commute S) (scalarPolynomial_square S)
    (odd_mixed_trace_zero S) j

end
end QuaternionicSymmetry.QuaternionicTangentFormalMatrix
