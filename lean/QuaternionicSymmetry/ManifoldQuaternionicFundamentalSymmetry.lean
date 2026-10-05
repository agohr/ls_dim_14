import QuaternionicSymmetry.ManifoldQuaternionicFourFormGluing
import QuaternionicSymmetry.ManifoldDifferentialForms
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
Smooth symmetries of the actual quaternionic fundamental four-form. This is a
geometric first interface for the symmetry branch: the form is the one glued
from the tangent reduction, and pullback is by the manifold derivative.
Preserving this form alone is weaker than preserving the metric and the full
quaternionic reduction, especially in real dimension four.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicFundamentalSymmetry

open ManifoldDifferentialForms ManifoldQuaternionicFourFormGluing
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- A smooth diffeomorphism preserving the genuine fundamental four-form. -/
def PreservesFundamentalForm (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞) : Prop :=
  formPullback (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E))
    (f : M → M) (fundamentalFourForm Q) = fundamentalFourForm Q

theorem preserves_refl :
    PreservesFundamentalForm Q (Diffeomorph.refl 𝓘(ℝ,E) M ∞) := by
  exact formPullback_id (fundamentalFourForm Q)

theorem preserves_trans
    {f g : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞}
    (hf : PreservesFundamentalForm Q f)
    (hg : PreservesFundamentalForm Q g) :
    PreservesFundamentalForm Q (f.trans g) := by
  change formPullback (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E))
    ((g : M → M) ∘ (f : M → M)) (fundamentalFourForm Q) = fundamentalFourForm Q
  rw [formPullback_comp (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E))
    (I'' := 𝓘(ℝ,E))
    (hf := f.contMDiff.mdifferentiable (by simp))
    (hg := g.contMDiff.mdifferentiable (by simp)), hg, hf]

theorem preserves_symm
    {f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞}
    (hf : PreservesFundamentalForm Q f) :
    PreservesFundamentalForm Q f.symm := by
  -- Pull the preservation equation back along the inverse map.
  change formPullback (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E))
    (f.symm : M → M) (fundamentalFourForm Q) = fundamentalFourForm Q
  calc
    formPullback (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E))
        (f.symm : M → M) (fundamentalFourForm Q) =
      formPullback (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E))
        (f.symm : M → M)
        (formPullback (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E))
          (f : M → M) (fundamentalFourForm Q)) := by rw [hf]
    _ = formPullback (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E))
        ((f : M → M) ∘ (f.symm : M → M)) (fundamentalFourForm Q) := by
          rw [formPullback_comp (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E))
            (I'' := 𝓘(ℝ,E))
            (hf := f.symm.contMDiff.mdifferentiable (by simp))
            (hg := f.contMDiff.mdifferentiable (by simp))]
    _ = fundamentalFourForm Q := by
      have hid : ((f : M → M) ∘ (f.symm : M → M)) = id := by
        funext x
        exact f.apply_symm_apply x
      rw [hid, formPullback_id]

/-- Pointwise preservation of the tangent metric under the actual manifold
derivative. This is the differential-geometric isometry equation. -/
def PreservesMetric (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞) : Prop :=
  ∀ x (v w : TangentSpace 𝓘(ℝ,E) x),
    Q.tangentMetricForm (f x)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) x v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) x w) =
    Q.tangentMetricForm x v w

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem metric_refl :
    PreservesMetric Q (Diffeomorph.refl 𝓘(ℝ,E) M ∞) := by
  intro x v w
  simp [mfderiv_id]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem metric_trans
    {f g : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞}
    (hf : PreservesMetric Q f) (hg : PreservesMetric Q g) :
    PreservesMetric Q (f.trans g) := by
  intro x v w
  change Q.tangentMetricForm (g (f x))
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ((g : M → M) ∘ (f : M → M)) x v)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ((g : M → M) ∘ (f : M → M)) x w) =
      Q.tangentMetricForm x v w
  rw [mfderiv_comp x
    (g.contMDiff.mdifferentiable (by simp) (f x))
    (f.contMDiff.mdifferentiable (by simp) x)]
  change Q.tangentMetricForm (g (f x))
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (g : M → M) (f x)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) x v))
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (g : M → M) (f x)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) x w)) = _
  rw [hg, hf]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem metric_symm
    {f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞}
    (hf : PreservesMetric Q f) : PreservesMetric Q f.symm := by
  intro y v w
  have h := hf (f.symm y)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.symm : M → M) y v)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.symm : M → M) y w)
  have hid : ((f : M → M) ∘ (f.symm : M → M)) = id := by
    funext x
    exact f.apply_symm_apply x
  have hderiv :
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) (f.symm y)).comp
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.symm : M → M) y) =
          ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ,E) y) := by
    have hc := mfderiv_comp y
      (f.contMDiff.mdifferentiable (by simp) (f.symm y))
      (f.symm.contMDiff.mdifferentiable (by simp) y)
    rw [hid, mfderiv_id] at hc
    exact hc.symm
  have hcancel (u : TangentSpace 𝓘(ℝ,E) y) :
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) (f.symm y)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.symm : M → M) y u) = u := by
    calc
      _ = ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) (f.symm y)).comp
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.symm : M → M) y)) u := rfl
      _ = u := by rw [hderiv]; rfl
  have hfy : f (f.symm y) = y := f.apply_symm_apply y
  rw [hfy] at h
  exact h.symm.trans
    (congrArg₂ (fun a b => Q.tangentMetricForm y a b)
      (hcancel v) (hcancel w))

/-- Smooth metric isometries that preserve the glued quaternionic four-form.
For quaternionic dimension at least two this is the intended pointwise
stabilizer interface; the converse identification with the full reduction
remains a separate linear-algebra theorem. -/
def IsGeometricSymmetry (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞) : Prop :=
  PreservesMetric Q f ∧ PreservesFundamentalForm Q f

theorem geometric_refl :
    IsGeometricSymmetry Q (Diffeomorph.refl 𝓘(ℝ,E) M ∞) :=
  ⟨metric_refl Q, preserves_refl Q⟩

theorem geometric_trans
    {f g : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞}
    (hf : IsGeometricSymmetry Q f)
    (hg : IsGeometricSymmetry Q g) :
    IsGeometricSymmetry Q (f.trans g) :=
  ⟨metric_trans Q hf.1 hg.1, preserves_trans Q hf.2 hg.2⟩

theorem geometric_symm
    {f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞}
    (hf : IsGeometricSymmetry Q f) : IsGeometricSymmetry Q f.symm :=
  ⟨metric_symm Q hf.1, preserves_symm Q hf.2⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicFundamentalSymmetry
