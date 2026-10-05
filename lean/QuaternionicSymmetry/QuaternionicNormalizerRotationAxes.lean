import QuaternionicSymmetry.QuaternionicUnitQuaternionPairTransport

/-! Extract the two quaternionic imaginary axes of an actual orthogonal
normalizer element. -/

namespace QuaternionicSymmetry.QuaternionicNormalizerRotationAxes

open scoped Quaternion
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
  ManifoldQuaternionicRankThreeOrthogonal
  QuaternionicIsometryNormalizer QuaternionicUnitScalarIsometries

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
variable (S : QuaternionicStructure E)

theorem rotation_eval (g : normalizer S) (a : Fin 3 → ℝ) (v : E) :
    synth S (rotationLinear S g a) (g.1 v) = g.1 (synth S a v) := by
  rw [synth_rotationLinear]
  simp only [conjugation_apply, g.1.symm_apply_apply]

/-- The adjoint action of every orthogonal normalizer preserves the
Euclidean dot product on quaternionic coefficients. -/
theorem rotation_dot (g : normalizer S) (a b : Fin 3 → ℝ) :
    (∑ t : Fin 3, (rotationLinear S g a) t * (rotationLinear S g b) t) =
      ∑ t : Fin 3, a t * b t := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  let w : E := (‖v‖⁻¹ : ℝ) • v
  have hw : ‖w‖ = 1 := norm_smul_inv_norm hv
  have hgw : ‖g.1 w‖ = 1 := by rw [g.1.norm_map, hw]
  calc
    _ = inner ℝ (synth S (rotationLinear S g a) (g.1 w))
          (synth S (rotationLinear S g b) (g.1 w)) := by
            exact (synth_eval_inner S _ _ _ hgw).symm
    _ = inner ℝ (g.1 (synth S a w)) (g.1 (synth S b w)) := by
          rw [rotation_eval S g a w, rotation_eval S g b w]
    _ = inner ℝ (synth S a w) (synth S b w) := g.1.inner_map_map _ _
    _ = _ := synth_eval_inner S a b w hw

def firstAxis (g : normalizer S) : ℍ :=
  pureScalar (rotationLinear S g (Pi.basisFun ℝ (Fin 3) 0))

def secondAxis (g : normalizer S) : ℍ :=
  pureScalar (rotationLinear S g (Pi.basisFun ℝ (Fin 3) 1))

@[simp] theorem firstAxis_re (g : normalizer S) : (firstAxis S g).re = 0 := rfl
@[simp] theorem secondAxis_re (g : normalizer S) : (secondAxis S g).re = 0 := rfl

theorem firstAxis_normSq (g : normalizer S) :
    Quaternion.normSq (firstAxis S g) = 1 := by
  have h := rotation_dot S g
    (Pi.basisFun ℝ (Fin 3) 0) (Pi.basisFun ℝ (Fin 3) 0)
  simpa [firstAxis, pureScalar, Quaternion.normSq_def',
    Fin.sum_univ_succ, Pi.basisFun_apply, pow_two, add_assoc] using h

theorem secondAxis_normSq (g : normalizer S) :
    Quaternion.normSq (secondAxis S g) = 1 := by
  have h := rotation_dot S g
    (Pi.basisFun ℝ (Fin 3) 1) (Pi.basisFun ℝ (Fin 3) 1)
  simpa [secondAxis, pureScalar, Quaternion.normSq_def',
    Fin.sum_univ_succ, Pi.basisFun_apply, pow_two, add_assoc] using h

theorem firstAxis_action (g : normalizer S) (v : E) :
    S.action (firstAxis S g) (g.1 v) = g.1 (S.I v) := by
  rw [firstAxis, action_pureScalar]
  rw [rotation_eval]
  rw [synth_basis]
  rfl

theorem secondAxis_action (g : normalizer S) (v : E) :
    S.action (secondAxis S g) (g.1 v) = g.1 (S.J v) := by
  rw [secondAxis, action_pureScalar]
  rw [rotation_eval]
  rw [synth_basis]
  rfl

theorem axes_anticommute (g : normalizer S) :
    firstAxis S g * secondAxis S g =
      -secondAxis S g * firstAxis S g := by
  apply action_injective S
  apply LinearMap.ext
  intro v
  let w := g.1.symm v
  have hv : g.1 w = v := g.1.apply_symm_apply v
  rw [map_mul, map_mul]
  rw [map_neg]
  change S.action (firstAxis S g)
      (S.action (secondAxis S g) v) =
    -S.action (secondAxis S g)
      (S.action (firstAxis S g) v)
  rw [← hv, secondAxis_action S g w, firstAxis_action S g w,
    firstAxis_action S g (S.J w), secondAxis_action S g (S.I w)]
  simp [S.I_J_anti]

end
end QuaternionicSymmetry.QuaternionicNormalizerRotationAxes
