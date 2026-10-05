import Mathlib.Analysis.Calculus.VectorField

/-! Lie brackets of related vector fields are related by the actual
derivative, even when the derivative is not invertible. The hypotheses
are germs at the point, as needed for later manifold chart applications. -/

namespace QuaternionicSymmetry.VectorFieldRelatedBracket

open scoped Topology
noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : E → F} {V W : E → E} {V' W' : F → F} {x : E}

theorem fderiv_lieBracket_of_eventually_related {n : WithTop ℕ∞}
    (hf : ContDiffAt 𝕜 n f x) (hn : minSmoothness 𝕜 2 ≤ n)
    (hV : DifferentiableAt 𝕜 V x) (hW : DifferentiableAt 𝕜 W x)
    (hV' : DifferentiableAt 𝕜 V' (f x))
    (hW' : DifferentiableAt 𝕜 W' (f x))
    (hRelV : (fun y => fderiv 𝕜 f y (V y)) =ᶠ[𝓝 x] (fun y => V' (f y)))
    (hRelW : (fun y => fderiv 𝕜 f y (W y)) =ᶠ[𝓝 x] (fun y => W' (f y))) :
    fderiv 𝕜 f x (VectorField.lieBracket 𝕜 V W x) =
      VectorField.lieBracket 𝕜 V' W' (f x) := by
  have hdf : DifferentiableAt 𝕜 f x :=
    hf.differentiableAt (ne_of_gt (lt_of_lt_of_le (by simp) (le_minSmoothness.trans hn)))
  rw [VectorField.fderiv_apply_lieBracket hf hn hW hV,
    hRelW.fderiv_eq, hRelV.fderiv_eq]
  have hWcomp : fderiv 𝕜 (fun y => W' (f y)) x =
      (fderiv 𝕜 W' (f x)).comp (fderiv 𝕜 f x) :=
    fderiv_comp x hW' hdf
  have hVcomp : fderiv 𝕜 (fun y => V' (f y)) x =
      (fderiv 𝕜 V' (f x)).comp (fderiv 𝕜 f x) :=
    fderiv_comp x hV' hdf
  rw [hWcomp, hVcomp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, hRelV.eq_of_nhds, hRelW.eq_of_nhds]
  rfl

theorem fderiv_lieBracket_of_related {n : WithTop ℕ∞}
    (hf : ContDiffAt 𝕜 n f x) (hn : minSmoothness 𝕜 2 ≤ n)
    (hV : DifferentiableAt 𝕜 V x) (hW : DifferentiableAt 𝕜 W x)
    (hV' : DifferentiableAt 𝕜 V' (f x))
    (hW' : DifferentiableAt 𝕜 W' (f x))
    (hRelV : ∀ y, fderiv 𝕜 f y (V y) = V' (f y))
    (hRelW : ∀ y, fderiv 𝕜 f y (W y) = W' (f y)) :
    fderiv 𝕜 f x (VectorField.lieBracket 𝕜 V W x) =
      VectorField.lieBracket 𝕜 V' W' (f x) :=
  fderiv_lieBracket_of_eventually_related hf hn hV hW hV' hW'
    (Filter.Eventually.of_forall hRelV) (Filter.Eventually.of_forall hRelW)

end
end QuaternionicSymmetry.VectorFieldRelatedBracket
