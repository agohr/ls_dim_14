import QuaternionicSymmetry.ComplexSubmanifoldInput
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Linear coordinates on an invariant real tangent range. -/
namespace QuaternionicSymmetry.ComplexSubmanifoldLinear
noncomputable section

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F]

theorem projection_of_invariant_range (D : E →L[ℝ] F)
    (hD : Function.Injective D)
    (hI : ∀ v, v ∈ LinearMap.range D.toLinearMap →
      Complex.I • v ∈ LinearMap.range D.toLinearMap) :
    ∃ (m : ℕ) (L : F →L[ℂ] EuclideanSpace ℂ (Fin m))
      (e : E ≃L[ℝ] EuclideanSpace ℂ (Fin m)),
      Module.finrank ℝ E = 2 * m ∧ ∀ v, L (D v) = e v := by
  let V : Submodule ℂ F :=
    { carrier := LinearMap.range D.toLinearMap
      zero_mem' := (LinearMap.range D.toLinearMap).zero_mem
      add_mem' := (LinearMap.range D.toLinearMap).add_mem
      smul_mem' := by
        intro c v hv
        rw [← Complex.re_add_im c]
        simp only [add_smul, mul_smul, Complex.coe_smul]
        exact (LinearMap.range D.toLinearMap).add_mem
          ((LinearMap.range D.toLinearMap).smul_mem c.re hv)
          ((LinearMap.range D.toLinearMap).smul_mem c.im (hI v hv)) }
  let d : E →ₗ[ℝ] V :=
    { toFun := fun v => ⟨D v, ⟨v,rfl⟩⟩
      map_add' := by intros; apply Subtype.ext; exact D.map_add _ _
      map_smul' := by intros; apply Subtype.ext; exact D.map_smul _ _ }
  have hd : Function.Bijective d := by
    constructor
    · intro u v h; exact hD (congrArg Subtype.val h)
    · rintro ⟨v,w,hw⟩
      exact ⟨w, Subtype.ext hw⟩
  let eD := (LinearEquiv.ofBijective d hd).toContinuousLinearEquiv
  let m := Module.finrank ℂ V
  let eV : V ≃L[ℂ] EuclideanSpace ℂ (Fin m) :=
    (ContinuousLinearEquiv.ofFinrankEq (by simp [m]))
  obtain ⟨P,hP⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (f := V.subtypeL) Subtype.val_injective
  refine ⟨m,eV.toContinuousLinearMap.comp P,
    eD.trans (eV.toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv,?_,?_⟩
  · have hdim := Module.finrank_mul_finrank ℝ ℂ V
    rw [Complex.finrank_real_complex] at hdim
    exact eD.toLinearEquiv.finrank_eq.trans hdim.symm
  · intro v
    change eV (P (V.subtypeL (d v))) = eV (d v)
    rw [hP]

end
end QuaternionicSymmetry.ComplexSubmanifoldLinear
