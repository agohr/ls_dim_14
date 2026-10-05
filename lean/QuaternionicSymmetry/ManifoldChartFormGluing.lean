import QuaternionicSymmetry.ManifoldDifferentialForms
import QuaternionicSymmetry.ContinuousWedge

/-!
Gluing scalar differential forms from genuine manifold charts. The coordinate
law is a verifiable obligation on a proposed local curvature expression;
it includes the derivative of the actual chart transition on every tangent
argument. This file supplies the gluing construction and local-to-global
closedness, without asserting that PQK curvature satisfies the coordinate law.
-/

namespace QuaternionicSymmetry.ManifoldChartFormGluing

open Filter QuaternionicSymmetry.ManifoldDifferentialForms
open scoped Manifold Topology ContDiff

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}

private theorem wedge_compContinuousLinearMap {p q : ℕ}
    (L : E →L[ℝ] E)
    (a : E [⋀^Fin p]→L[ℝ] ℝ) (b : E [⋀^Fin q]→L[ℝ] ℝ) :
    ContinuousAlternatingMap.compContinuousLinearMap
      (ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ) a b) L =
      ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ)
        (a.compContinuousLinearMap L) (b.compContinuousLinearMap L) := by
  ext v
  simp only [ContinuousWedge.wedge_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1

/-- Smooth chart forms with the genuine tangent-coordinate transition law. -/
structure ChartFormData (n : ℕ) where
  localForm : M → E → E [⋀^Fin n]→L[ℝ] ℝ
  regular : ∀ p : M, ContDiffOn ℝ ∞ (localForm p)
    (extChartAt 𝓘(ℝ, E) p).target
  coordinateLaw : ∀ (p q : M) (y : E),
    y ∈ (extChartAt 𝓘(ℝ, E) p).target →
    (extChartAt 𝓘(ℝ, E) p).symm y ∈
      (extChartAt 𝓘(ℝ, E) q).source →
    localForm p y =
      ContinuousAlternatingMap.compContinuousLinearMap
        (localForm q
          ((extChartAt 𝓘(ℝ, E) q)
            ((extChartAt 𝓘(ℝ, E) p).symm y)))
        (fderiv ℝ
          ((extChartAt 𝓘(ℝ, E) q) ∘
            (extChartAt 𝓘(ℝ, E) p).symm) y)

namespace ChartFormData

variable (D : ChartFormData (E := E) (M := M) n)

/-- The normalized wedge of two compatible chart-form families. -/
noncomputable def wedge {m : ℕ} (A : ChartFormData (E := E) (M := M) m) :
    ChartFormData (E := E) (M := M) (m + n) where
  localForm p y :=
    ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ)
      (A.localForm p y) (D.localForm p y)
  regular p := by
    have hleft : ContDiffOn ℝ ∞
        (fun y => (ContinuousWedge.wedgeCLM
          (E := E) (p := m) (q := n) (ContinuousLinearMap.mul ℝ ℝ))
            (A.localForm p y))
        (extChartAt 𝓘(ℝ, E) p).target :=
      (A.regular p).continuousLinearMap_comp _
    simpa only [ContinuousWedge.wedgeCLM_apply] using
      hleft.clm_apply (D.regular p)
  coordinateLaw p q y hp hq := by
    rw [A.coordinateLaw p q y hp hq, D.coordinateLaw p q y hp hq]
    exact (wedge_compContinuousLinearMap
      (fderiv ℝ
        ((extChartAt 𝓘(ℝ, E) q) ∘
          (extChartAt 𝓘(ℝ, E) p).symm) y)
      (A.localForm q ((extChartAt 𝓘(ℝ, E) q)
        ((extChartAt 𝓘(ℝ, E) p).symm y)))
      (D.localForm q ((extChartAt 𝓘(ℝ, E) q)
        ((extChartAt 𝓘(ℝ, E) p).symm y)))).symm

/-- At a point, evaluate the corresponding chart form and transport its
arguments from the actual tangent fiber into that chart. -/
noncomputable def toForm : Form 𝓘(ℝ, E) M n :=
  fun x => (D.localForm x (extChartAt 𝓘(ℝ, E) x x))
    |>.compContinuousLinearMap
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x) x)

/-- The gluing construction recovers the local input at its chart center. -/
theorem inChartModel_toForm_at_center (x : M) :
    inChartModel x D.toForm (extChartAt 𝓘(ℝ, E) x x) =
      D.localForm x (extChartAt 𝓘(ℝ, E) x x) := by
  let C := extChartAt 𝓘(ℝ, E) x
  have hsource : x ∈ C.source := mem_extChartAt_source x
  have hcomp :
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C x) ∘L
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C.symm (C x)) =
          ContinuousLinearMap.id ℝ E := by
    simpa [C, mfderivWithin_univ] using
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
        (I := 𝓘(ℝ, E)) hsource)
  ext v
  rw [inChartModel_self_apply]
  rw [C.left_inv hsource]
  change D.localForm x (C x)
      (fun i => (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C x)
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C.symm (C x)) (v i))) = _
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    using congrArg (fun L : E →L[ℝ] E =>
      D.localForm x (C x) (fun i => L (v i))) hcomp

/-- The glued form has precisely the supplied expression in every chart. -/
theorem inChartModel_toForm (p : M) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    inChartModel p D.toForm y = D.localForm p y := by
  let x : M := (extChartAt 𝓘(ℝ, E) p).symm y
  have hx : x ∈ (extChartAt 𝓘(ℝ, E) x).source :=
    mem_extChartAt_source x
  have hc := inChartModel_change D.toForm p x y hy hx
  have hcenter := D.inChartModel_toForm_at_center x
  rw [hcenter] at hc
  have hlaw := D.coordinateLaw p x y hy hx
  exact hc.trans hlaw.symm

/-- Chartwise regularity becomes smoothness of the genuine manifold form. -/
theorem toForm_smooth : ChartSmooth D.toForm := by
  intro p
  exact (D.regular p).congr (fun y hy => (D.inChartModel_toForm p hy))

/-- Local closedness glues to closedness of the manifold exterior derivative. -/
theorem toForm_closed
    (hclosed : ∀ (p : M) (y : E),
      y ∈ (extChartAt 𝓘(ℝ, E) p).target →
        extDeriv (D.localForm p) y = 0) :
    exteriorDerivative D.toForm = 0 := by
  funext x
  let C := extChartAt 𝓘(ℝ, E) x
  have hy : C x ∈ C.target := mem_extChartAt_target x
  have hevent : inChartModel x D.toForm =ᶠ[𝓝 (C x)] D.localForm x := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hy] with y hy'
    exact D.inChartModel_toForm x hy'
  have hderiv := hevent.extDeriv_eq
  change (extDeriv (inChartModel x D.toForm) (C x)).compContinuousLinearMap _ = 0
  rw [hderiv, hclosed x (C x) hy]
  ext v
  rfl

/-- A chartwise primitive gives an actual global exact equality once its
coordinate law has been established. -/
theorem toForm_sub_eq_exteriorDerivative
    (A B : ChartFormData (E := E) (M := M) (n + 1))
    (hlocal : ∀ (p : M) (y : E),
      y ∈ (extChartAt 𝓘(ℝ, E) p).target →
        A.localForm p y - B.localForm p y =
          extDeriv (D.localForm p) y) :
    A.toForm - B.toForm = exteriorDerivative D.toForm := by
  funext x
  let C := extChartAt 𝓘(ℝ, E) x
  have hy : C x ∈ C.target := mem_extChartAt_target x
  have hevent : inChartModel x D.toForm =ᶠ[𝓝 (C x)] D.localForm x := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hy] with y hy'
    exact D.inChartModel_toForm x hy'
  have hderiv := hevent.extDeriv_eq
  change
    (A.localForm x (C x)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C x) -
      (B.localForm x (C x)).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C x) =
      (extDeriv (inChartModel x D.toForm) (C x)).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C x)
  rw [hderiv]
  ext v
  simp only [ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  exact congrArg (fun eta =>
    eta (fun i => (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C x) (v i)))
    (hlocal x (C x) hy)

end ChartFormData
end QuaternionicSymmetry.ManifoldChartFormGluing
