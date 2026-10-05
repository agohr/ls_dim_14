import QuaternionicSymmetry.QuaternionicMatrixCoordinates

/-! A fixed quaternionic basis sends real skew quaternion-linear operators
to the Hermitian anti-self-dual matrices used in the orbital identities. -/
namespace QuaternionicSymmetry.QuaternionicOperatorMatrix
open QuaternionicCanonicalModel QuaternionicMatrixModel QuaternionicMatrixCoordinates
open scoped Matrix
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (S : QuaternionicStructure E)

def modelEnd (A : E →ₗ[ℝ] E) :
    V S.quaternionicDimension →ₗ[ℝ] V S.quaternionicDimension :=
  (canonicalModel S).toLinearEquiv.conj A

theorem modelEnd_commutes_I (A : E →ₗ[ℝ] E)
    (hI : ∀ v, A (S.I v) = S.I (A v)) (v : V S.quaternionicDimension) :
    modelEnd S A (standardI S.quaternionicDimension v) =
      standardI S.quaternionicDimension (modelEnd S A v) := by
  let U := canonicalModel S
  have hu : U.symm (standardI S.quaternionicDimension v) = S.I (U.symm v) := by
    apply U.injective
    rw [U.apply_symm_apply, canonicalModel_I, U.apply_symm_apply]
  change U (A (U.symm (standardI S.quaternionicDimension v))) = _
  rw [hu, hI, canonicalModel_I]
  rfl

theorem modelEnd_commutes_J (A : E →ₗ[ℝ] E)
    (hJ : ∀ v, A (S.J v) = S.J (A v)) (v : V S.quaternionicDimension) :
    modelEnd S A (standardJ S.quaternionicDimension v) =
      standardJ S.quaternionicDimension (modelEnd S A v) := by
  let U := canonicalModel S
  have hu : U.symm (standardJ S.quaternionicDimension v) = S.J (U.symm v) := by
    apply U.injective
    rw [U.apply_symm_apply, canonicalModel_J, U.apply_symm_apply]
  change U (A (U.symm (standardJ S.quaternionicDimension v))) = _
  rw [hu, hJ, canonicalModel_J]
  rfl

theorem modelEnd_skew (A : E →ₗ[ℝ] E)
    (hskew : ∀ v w, inner ℝ (A v) w + inner ℝ v (A w) = 0)
    (v w : V S.quaternionicDimension) :
    inner ℝ (modelEnd S A v) w + inner ℝ v (modelEnd S A w) = 0 := by
  let U := canonicalModel S
  have h := hskew (U.symm v) (U.symm w)
  have h1 := U.inner_map_map (A (U.symm v)) (U.symm w)
  have h2 := U.inner_map_map (U.symm v) (A (U.symm w))
  rw [U.apply_symm_apply] at h1 h2
  change inner ℝ (U (A (U.symm v))) w + inner ℝ v (U (A (U.symm w))) = 0
  rw [h1, h2]
  exact h

def operatorMatrix (A : E →ₗ[ℝ] E) (hI : ∀ v, A (S.I v) = S.I (A v)) :
    Matrix (Fin S.quaternionicDimension ⊕ Fin S.quaternionicDimension)
      (Fin S.quaternionicDimension ⊕ Fin S.quaternionicDimension) ℂ :=
  matrixEnd (modelEnd S A) (modelEnd_commutes_I S A hI)

theorem operatorMatrix_action (A : E →ₗ[ℝ] E)
    (hI : ∀ v, A (S.I v) = S.I (A v)) (v : E) :
    realMatrixAction (operatorMatrix S A hI) (canonicalModel S v) =
      canonicalModel S (A v) := by
  rw [operatorMatrix, matrixEnd_action]
  change canonicalModel S (A ((canonicalModel S).symm (canonicalModel S v))) = _
  rw [(canonicalModel S).symm_apply_apply]

theorem operatorMatrix_hermitianAntiSelfDual (A : E →ₗ[ℝ] E)
    (hI : ∀ v, A (S.I v) = S.I (A v))
    (hJ : ∀ v, A (S.J v) = S.J (A v))
    (hskew : ∀ v w, inner ℝ (A v) w + inner ℝ v (A w) = 0) :
    HermitianAntiSelfDual (Complex.I • operatorMatrix S A hI) :=
  matrixEnd_hermitianAntiSelfDual (modelEnd S A)
    (modelEnd_commutes_I S A hI) (modelEnd_commutes_J S A hJ) (modelEnd_skew S A hskew)

end
end QuaternionicSymmetry.QuaternionicOperatorMatrix
