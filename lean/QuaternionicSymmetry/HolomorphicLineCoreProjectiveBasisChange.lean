import QuaternionicSymmetry.HolomorphicLineCoreAmpleness

/-! The genuine complete projective map changes by an invertible linear
coordinate map under an arbitrary change of basis of all global sections.
In particular, injectivity of a very ample complete map holds in an
integral eigenbasis as well. -/
namespace QuaternionicSymmetry.HolomorphicLineCoreProjectiveBasisChange

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreProjectiveEvaluation HolomorphicLineCoreAmpleFiniteMap
open ComplexProjectiveTopology
open scoped Manifold ContDiff LinearAlgebra.Projectivization
noncomputable section
universe u

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H) (L : LineCore.{u} (B := B) IB)

def basisCoordinateChange (d e : ℕ)
    (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections IB L))
    (c : Module.Basis (Fin (e + 1)) ℂ (GlobalSections IB L)) :
    Coord d ≃ₗ[ℂ] Coord e :=
  b.dualBasis.equivFun.symm.trans c.dualBasis.equivFun

theorem basisEvaluation_change (d e : ℕ)
    (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections IB L))
    (c : Module.Basis (Fin (e + 1)) ℂ (GlobalSections IB L)) (x : B) :
    basisCoordinateChange IB L d e b c (basisEvaluation IB L d b x) =
      basisEvaluation IB L e c x := by
  have hb : basisEvaluation IB L d b x = b.dualBasis.equivFun (evaluation IB L x) := by
    ext i
    exact (b.dualBasis_equivFun (evaluation IB L x) i).symm
  have hc : basisEvaluation IB L e c x = c.dualBasis.equivFun (evaluation IB L x) := by
    ext i
    exact (c.dualBasis_equivFun (evaluation IB L x) i).symm
  rw [hb,hc]
  simp [basisCoordinateChange]

theorem projectiveEvaluation_change (d e : ℕ)
    (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections IB L))
    (c : Module.Basis (Fin (e + 1)) ℂ (GlobalSections IB L))
    (hGen : GloballyGenerated IB L) (x : B) :
    projectiveEvaluationOfGenerated IB L e c hGen x =
      Projectivization.map (basisCoordinateChange IB L d e b c).toLinearMap
        (basisCoordinateChange IB L d e b c).injective
        (projectiveEvaluationOfGenerated IB L d b hGen x) := by
  unfold projectiveEvaluationOfGenerated projectiveEvaluation
  rw [Projectivization.map_mk]
  change Projectivization.mk ℂ (basisEvaluation IB L e c x) _ =
    Projectivization.mk ℂ
      (basisCoordinateChange IB L d e b c (basisEvaluation IB L d b x)) _
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨1, ?_⟩
  simpa only [one_smul] using (basisEvaluation_change IB L d e b c x)

theorem projectiveEvaluation_injective_of_basis (d e : ℕ)
    (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections IB L))
    (c : Module.Basis (Fin (e + 1)) ℂ (GlobalSections IB L))
    (hGen : GloballyGenerated IB L)
    (hc : Function.Injective (projectiveEvaluationOfGenerated IB L e c hGen)) :
    Function.Injective (projectiveEvaluationOfGenerated IB L d b hGen) := by
  intro x y h
  apply hc
  rw [projectiveEvaluation_change IB L d e b c hGen x,
    projectiveEvaluation_change IB L d e b c hGen y,h]

theorem veryAmple_projectiveEvaluation_injective [IsManifold IB ∞ B]
    (hVery : VeryAmpleCore IB L) (d : ℕ)
    (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections IB L))
    (hGen : GloballyGenerated IB L) :
    Function.Injective (projectiveEvaluationOfGenerated IB L d b hGen) := by
  obtain ⟨e,c,hGen',hEmb,hImm⟩ := hVery
  exact projectiveEvaluation_injective_of_basis IB L d e b c hGen hEmb.injective

end
end QuaternionicSymmetry.HolomorphicLineCoreProjectiveBasisChange
