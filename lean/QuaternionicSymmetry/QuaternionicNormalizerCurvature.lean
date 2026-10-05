import QuaternionicSymmetry.QuaternionicCurvatureScalarFromBianchi
import QuaternionicSymmetry.QuaternionicLieAlgebraProjection

/-! Extract the scalar coefficient forms from actual quaternionic-normalizer
curvature and apply the proved algebraic first-Bianchi calculation. -/
namespace QuaternionicSymmetry.QuaternionicNormalizerCurvature
open QuaternionicLieAlgebraProjection ManifoldQuaternionicAdjointConnection
open ManifoldQuaternionicRankThreeOrientation
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
open ManifoldQuaternionicRankThreeOrthogonal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] (S : QuaternionicStructure E)

def coefficientMap (i : Fin 3) : (E →L[ℝ] E) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (axialProjection.comp (adjointRepresentation S))

def coefficients (R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (i : Fin 3) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) ℝ (coefficientMap S i)).comp R

theorem scalarProjection_coefficients (A : E →L[ℝ] E) :
    scalarProjection S A = synth S (fun i => coefficientMap S i A) := rfl

theorem commutator_synth (A : E →L[ℝ] E)
    (hA : ∀ b, symplecticProjection S A * synth S b =
      synth S b * symplecticProjection S A) (b : Fin 3 → ℝ) :
    A * synth S b - synth S b * A =
      (2 : ℝ) • synth S (crossProduct (fun i => coefficientMap S i A) b) := by
  have he := hA b
  change (A - scalarProjection S A) * synth S b =
    synth S b * (A - scalarProjection S A) at he
  rw [sub_mul, mul_sub] at he
  have h' := sub_eq_sub_iff_sub_eq_sub.mp he
  rw [h', scalarProjection_coefficients, synth_commutator_cross]

theorem commutator_I (A : E →L[ℝ] E)
    (hA : ∀ b, symplecticProjection S A * synth S b =
      synth S b * symplecticProjection S A) (w : E) :
    A (S.I w) - S.I (A w) =
      (2 : ℝ) • (coefficientMap S 2 A • S.J w - coefficientMap S 1 A • S.K w) := by
  have he := congrArg (fun B : E →L[ℝ] E => B w)
    (commutator_synth S A hA (Pi.basisFun ℝ (Fin 3) 0))
  rw [synth_basis] at he
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.smul_apply] at he
  simpa [synth_apply, Fin.sum_univ_three, crossProduct, Pi.basisFun_apply,
    quaternionicGenerator, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    sub_eq_add_neg, add_comm] using he

theorem commutator_J (A : E →L[ℝ] E)
    (hA : ∀ b, symplecticProjection S A * synth S b =
      synth S b * symplecticProjection S A) (w : E) :
    A (S.J w) - S.J (A w) =
      (2 : ℝ) • (coefficientMap S 0 A • S.K w - coefficientMap S 2 A • S.I w) := by
  have he := congrArg (fun B : E →L[ℝ] E => B w)
    (commutator_synth S A hA (Pi.basisFun ℝ (Fin 3) 1))
  rw [synth_basis] at he
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.smul_apply] at he
  simpa [synth_apply, Fin.sum_univ_three, crossProduct, Pi.basisFun_apply,
    quaternionicGenerator, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    sub_eq_add_neg, add_comm] using he

theorem commutator_K (A : E →L[ℝ] E)
    (hA : ∀ b, symplecticProjection S A * synth S b =
      synth S b * symplecticProjection S A) (w : E) :
    A (S.K w) - S.K (A w) =
      (2 : ℝ) • (coefficientMap S 1 A • S.I w - coefficientMap S 0 A • S.J w) := by
  have he := congrArg (fun B : E →L[ℝ] E => B w)
    (commutator_synth S A hA (Pi.basisFun ℝ (Fin 3) 2))
  rw [synth_basis] at he
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.smul_apply] at he
  simpa [synth_apply, Fin.sum_univ_three, crossProduct, Pi.basisFun_apply,
    quaternionicGenerator, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    sub_eq_add_neg, add_comm] using he

theorem exists_scalar (R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (hn : 2 ≤ S.quaternionicDimension)
    (hfirst : ∀ u v, R u v = -R v u)
    (hlast : ∀ u v w z, inner ℝ (R u v w) z = -inner ℝ (R u v z) w)
    (hB : ∀ u v w, R u v w + R v w u + R w u v = 0)
    (hA : ∀ u v b, symplecticProjection S (R u v) * synth S b =
      synth S b * symplecticProjection S (R u v)) :
    ∃ c : ℝ, ∀ u v, scalarProjection S (R u v) =
      c • synth S (fun t => inner ℝ (quaternionicGenerator S t u) v) := by
  have hsk (t : Fin 3) (u v : E) :
      coefficients S R t u v = -coefficients S R t v u := by
    change coefficientMap S t (R u v) = -coefficientMap S t (R v u)
    rw [hfirst, map_neg]
  obtain ⟨c,hc⟩ := QuaternionicCurvatureScalarFromBianchi.exists_scalar S hn R
    (coefficients S R) hsk hfirst hlast hB
    (fun u v w => commutator_I S (R u v) (hA u v) w)
    (fun u v w => commutator_J S (R u v) (hA u v) w)
    (fun u v w => commutator_K S (R u v) (hA u v) w)
  refine ⟨c, ?_⟩
  intro u v
  rw [scalarProjection_coefficients, ← map_smul]
  congr 1
  funext t
  exact hc t u v

end
end QuaternionicSymmetry.QuaternionicNormalizerCurvature
