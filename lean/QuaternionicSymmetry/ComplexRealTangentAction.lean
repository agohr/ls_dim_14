import QuaternionicSymmetry.ComplexRealTangentTopology
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-! Joint tangent-action continuity transfers from real to complex scalars
in one compatible complex atlas. This compares actual derivatives and
actual tangent-bundle topologies, not just their underlying sets.
-/

namespace QuaternionicSymmetry.ComplexRealTangentAction

open Manifold ComplexRealTangentTopology
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ,E) 1 M] [IsManifold 𝓘(ℝ,E) 1 M]

/-- The genuine real derivative is the scalar restriction of the genuine
complex derivative when both are taken in the same complex atlas. -/
theorem mfderiv_real_complex {f : M → M} {x : M}
    (hR : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) f x)
    (hC : MDifferentiableAt 𝓘(ℂ,E) 𝓘(ℂ,E) f x) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f x =
      (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,E) f x).restrictScalars ℝ := by
  rw [hR.mfderiv, hC.mfderiv]
  simp only [modelWithCornersSelf_coe]
  rw [show writtenInExtChartAt 𝓘(ℝ,E) 𝓘(ℝ,E) x f =
    writtenInExtChartAt 𝓘(ℂ,E) 𝓘(ℂ,E) x f from rfl]
  simp only [Set.range_id, fderivWithin_univ]
  have hc : DifferentiableAt ℂ (writtenInExtChartAt 𝓘(ℂ,E) 𝓘(ℂ,E) x f)
      ((extChartAt 𝓘(ℂ,E) x) x) := by
    simpa only [modelWithCornersSelf_coe, Set.range_id,
      differentiableWithinAt_univ] using
      hC.differentiableWithinAt_writtenInExtChartAt
  exact hc.fderiv_restrictScalars ℝ

/-- Scalar restriction intertwines the actual total tangent maps. -/
theorem tangentMap_toComplex {f : M → M}
    (hR : MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,E) f)
    (hC : MDifferentiable 𝓘(ℂ,E) 𝓘(ℂ,E) f)
    (v : TangentBundle 𝓘(ℂ,E) M) :
    toComplex (tangentMap 𝓘(ℝ,E) 𝓘(ℝ,E) f (toReal v)) =
      tangentMap 𝓘(ℂ,E) 𝓘(ℂ,E) f v := by
  apply Bundle.TotalSpace.ext
  · rfl
  · apply heq_of_eq
    change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f v.1 v.2 =
      mfderiv 𝓘(ℂ,E) 𝓘(ℂ,E) f v.1 v.2
    rw [mfderiv_real_complex (hR v.1) (hC v.1)]
    rfl

/-- A parameter space needs only a topology: joint continuity of its real
tangent family and individual holomorphicity imply joint continuity of the
complex tangent family. -/
theorem continuous_tangentAction_complex [TopologicalSpace G]
    (F : G → M → M)
    (hR : ∀ g, MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,E) (F g))
    (hC : ∀ g, MDifferentiable 𝓘(ℂ,E) 𝓘(ℂ,E) (F g))
    (hJoint : Continuous (fun p : G × TangentBundle 𝓘(ℝ,E) M =>
      tangentMap 𝓘(ℝ,E) 𝓘(ℝ,E) (F p.1) p.2)) :
    Continuous (fun p : G × TangentBundle 𝓘(ℂ,E) M =>
      tangentMap 𝓘(ℂ,E) 𝓘(ℂ,E) (F p.1) p.2) := by
  have h := continuous_toComplex.comp (hJoint.comp
    (continuous_fst.prodMk (continuous_toReal.comp continuous_snd)))
  exact h.congr (fun p => tangentMap_toComplex (hR p.1) (hC p.1) p.2)

end
end QuaternionicSymmetry.ComplexRealTangentAction
