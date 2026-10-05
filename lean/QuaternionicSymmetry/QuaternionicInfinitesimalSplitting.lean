import QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrientation
import QuaternionicSymmetry.QuaternionicUnitScalarIsometries

/-! Explicit splitting of an infinitesimal quaternionic normalizer into
its quaternion-linear and scalar quaternionic parts. -/
namespace QuaternionicSymmetry.QuaternionicInfinitesimalSplitting

open Matrix VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
  ManifoldQuaternionicRankThreeOrientation ManifoldQuaternionicRankThreeOrthogonal
open scoped Matrix
noncomputable section

def scalarCoefficients (B : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ :=
  ![B 2 1 / 2, B 0 2 / 2, B 1 0 / 2]

theorem cross_scalarCoefficients (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : B.transpose = -B) (b : Fin 3 → ℝ) :
    (2 : ℝ) • crossProduct (scalarCoefficients B) b = B.mulVec b := by
  have hsk (i j : Fin 3) : B i j = -B j i := by
    have h := congrArg (fun C : Matrix (Fin 3) (Fin 3) ℝ => C j i) hB
    exact h
  have hd (i : Fin 3) : B i i = 0 := by linarith [hsk i i]
  ext i
  fin_cases i <;>
    simp [scalarCoefficients, crossProduct, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, hd, hsk 0 1, hsk 2 0, hsk 1 2] <;> ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E]

def scalarPart (S : QuaternionicStructure E) (B : Matrix (Fin 3) (Fin 3) ℝ) : E →L[ℝ] E :=
  synth S (scalarCoefficients B)

def symplecticPart (S : QuaternionicStructure E) (A : E →L[ℝ] E)
    (B : Matrix (Fin 3) (Fin 3) ℝ) : E →L[ℝ] E := A - scalarPart S B

theorem scalarPart_commutator (S : QuaternionicStructure E)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.transpose = -B) (b : Fin 3 → ℝ) :
    scalarPart S B * synth S b - synth S b * scalarPart S B = synth S (B.mulVec b) := by
  rw [scalarPart, synth_commutator_cross, ← map_smul, cross_scalarCoefficients B hB b]

theorem symplecticPart_commutes (S : QuaternionicStructure E)
    (A : E →L[ℝ] E) (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.transpose = -B)
    (hA : ∀ b : Fin 3 → ℝ, A * synth S b - synth S b * A = synth S (B.mulVec b))
    (b : Fin 3 → ℝ) :
    symplecticPart S A B * synth S b = synth S b * symplecticPart S A B := by
  have hc := scalarPart_commutator S B hB b
  unfold symplecticPart
  rw [sub_mul, mul_sub]
  have h := (hA b).trans hc.symm
  exact sub_eq_sub_iff_sub_eq_sub.mp h

theorem scalarPart_skew (S : QuaternionicStructure E)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (v w : E) :
    inner ℝ (scalarPart S B v) w + inner ℝ v (scalarPart S B w) = 0 := by
  simp only [scalarPart, synth_apply, Fin.sum_univ_three,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  simp [quaternionicGenerator, S.I_skew, S.J_skew, S.J_I_anti]
  ring

theorem symplecticPart_skew (S : QuaternionicStructure E)
    (A : E →L[ℝ] E) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ v w, inner ℝ (A v) w + inner ℝ v (A w) = 0) (v w : E) :
    inner ℝ (symplecticPart S A B v) w + inner ℝ v (symplecticPart S A B w) = 0 := by
  have hs := scalarPart_skew S B v w
  simp only [symplecticPart, ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  linarith [hA v w]

end
end QuaternionicSymmetry.QuaternionicInfinitesimalSplitting
