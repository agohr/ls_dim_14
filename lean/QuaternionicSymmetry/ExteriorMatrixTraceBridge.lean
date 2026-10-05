import QuaternionicSymmetry.ExteriorMatrixWedgeBridge

/-! Trace of a normalized matrix wedge power is the canonical pairing of
the homogeneous exterior trace of the corresponding matrix power. -/
namespace QuaternionicSymmetry.ExteriorMatrixTraceBridge
open ExteriorMatrixWedgeBridge ExteriorContinuousPairing
  QuaternionicExteriorEvenTrace EvenForms ContinuousMatrixWedgeEntries
noncomputable section
set_option maxHeartbeats 1000000

variable {V κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype κ] [DecidableEq κ]

private abbrev X := ExteriorAlgebra ℝ (Module.Dual ℝ V)

local instance : NormedRing (Matrix κ κ ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix κ κ ℝ) := Matrix.linftyOpNormedAlgebra

def traceCLM : Matrix κ κ ℝ →L[ℝ] ℝ :=
  (Matrix.traceLinearMap κ ℝ ℝ).toContinuousLinearMap

omit [DecidableEq κ] in
@[simp] theorem traceCLM_apply (A : Matrix κ κ ℝ) : traceCLM A = Matrix.trace A := rfl

def wedgeTrace (A : Matrix κ κ (EvenAlgebra V))
    (hA : ∀ i j, ((A i j : EvenAlgebra V) : X (V := V)) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V))
    (k : ℕ) : Power V (wedgeDegree k) :=
  ⟨(Matrix.trace (A ^ (k + 1)) : EvenAlgebra V), by
    rw [wedgeDegree_eq]
    exact EvenExteriorMatrixHomogeneity.matrix_trace_pow_mem 2 (k + 1) A hA⟩

/-- The precise all-degree trace bridge for actual normalized alternating
matrix-valued wedges. -/
theorem trace_matrixWedgePower (A : Matrix κ κ (EvenAlgebra V))
    (hA : ∀ i j, ((A i j : EvenAlgebra V) : X (V := V)) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V))
    (k : ℕ) :
    traceCLM.compContinuousAlternatingMap
      (matrixWedgePower (matrixTwoForm A hA) k) =
      toContinuous (wedgeDegree k) (wedgeTrace A hA k) := by
  ext v
  change traceCLM (matrixWedgePower (matrixTwoForm A hA) k v) = _
  rw [traceCLM_apply]
  rw [Matrix.trace]
  change (∑ i : κ, entry i i (matrixWedgePower (matrixTwoForm A hA) k) v) = _
  simp_rw [matrixWedgePower_entry A hA k]
  change (∑ i : κ, (toContinuousLinear (V := V) (wedgeDegree k))
    (wedgeEntry A hA k i i) v) = _
  have hsum :
      (∑ i : κ, (toContinuousLinear (V := V) (wedgeDegree k))
        (wedgeEntry A hA k i i) v) =
      toContinuous (wedgeDegree k) (∑ i : κ, wedgeEntry A hA k i i) v := by
    have h := map_sum (toContinuousLinear (V := V) (wedgeDegree k))
      (fun i : κ => wedgeEntry A hA k i i) Finset.univ
    simpa only [ContinuousAlternatingMap.sum_apply] using
      (congrArg (fun f : V [⋀^Fin (wedgeDegree k)]→L[ℝ] ℝ => f v) h).symm
  rw [hsum]
  have heq : (∑ i : κ, wedgeEntry A hA k i i) = wedgeTrace A hA k := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, wedgeEntry, wedgeTrace]
    change (∑ i : κ, (((A ^ (k + 1)) i i : EvenAlgebra V) : X (V := V))) =
      ((Matrix.trace (A ^ (k + 1)) : EvenAlgebra V) : X (V := V))
    simp [Matrix.trace]
  exact congrArg (fun z : Power V (wedgeDegree k) => toContinuous (wedgeDegree k) z v) heq

end
end QuaternionicSymmetry.ExteriorMatrixTraceBridge
