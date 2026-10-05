import QuaternionicSymmetry.HolomorphicLineCoreRestrictedSubsystem
import Mathlib.Topology.Separation.Hausdorff

/-! The complete restricted linear system detects at least as many points
as the subsystem obtained by restricting ambient sections. Thus an embedded
ambient subsystem makes the complete restricted system point-injective; on
a compact complex submanifold this yields a topological embedding. The
immersion upgrade is a separate differential statement. -/

namespace QuaternionicSymmetry.HolomorphicLineCoreCompleteRestriction

open QuaternionicSymmetry.HolomorphicLineCorePullback
open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLineCoreProjectiveEvaluation
open QuaternionicSymmetry.HolomorphicLineCoreRestrictedSubsystem
open QuaternionicSymmetry.ComplexProjectiveTopology
open scoped Manifold ContDiff LinearAlgebra.Projectivization
noncomputable section
universe u

variable {B B' H H' F F' : Type*}
  [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace H]
  [TopologicalSpace H'] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F'] [NormedSpace ℂ F']
  [ChartedSpace H B] [ChartedSpace H' B']
  (IB : ModelWithCorners ℂ F H) (IB' : ModelWithCorners ℂ F' H')
  [IsManifold IB ∞ B] [IsManifold IB' ∞ B']
  (L : LineCore.{u} (B := B) IB)
  (f : B' → B) (hf : ContMDiff IB' IB ∞ f)
  (d : ℕ) (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections IB L))
  (h : GloballyGenerated IB L)

private def restrictedLine := pullbackLineCore IB IB' L f hf
private def restrictedGenerated : GloballyGenerated IB' (restrictedLine IB IB' L f hf) :=
  globallyGenerated_pullback IB IB' L f hf h

variable (e : ℕ)
  (c : Module.Basis (Fin (e + 1)) ℂ
    (GlobalSections IB' (restrictedLine IB IB' L f hf)))

/-- If the complete restricted projective evaluation identifies two
points, then every restricted ambient section has proportional values, so
the ambient-basis subsystem also identifies those points. -/
theorem subsystem_eq_of_complete_eq {x y : B'}
    (hxy : projectiveEvaluationOfGenerated IB'
      (restrictedLine IB IB' L f hf) e c
      (restrictedGenerated IB IB' L f hf h) x =
      projectiveEvaluationOfGenerated IB'
        (restrictedLine IB IB' L f hf) e c
        (restrictedGenerated IB IB' L f hf h) y) :
    restrictedSubsystemMap IB IB' L f hf d b h x =
      restrictedSubsystemMap IB IB' L f hf d b h y := by
  let R := restrictedLine IB IB' L f hf
  let hR := restrictedGenerated IB IB' L f hf h
  have hx : x ∉ baseLocus IB' R := by
    simpa [(globallyGenerated_iff_baseLocus_empty IB' R).1 hR]
  have hy : y ∉ baseLocus IB' R := by
    simpa [(globallyGenerated_iff_baseLocus_empty IB' R).1 hR]
  have hxy' : Projectivization.mk ℂ (basisEvaluation IB' R e c x)
      (basisEvaluation_ne_zero IB' R e c hx) =
      Projectivization.mk ℂ (basisEvaluation IB' R e c y)
        (basisEvaluation_ne_zero IB' R e c hy) := by
    exact hxy
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' ℂ
      (basisEvaluation IB' R e c x)
      (basisEvaluation IB' R e c y) _ _).1 hxy'
  have hlin : evaluation IB' R x = a • evaluation IB' R y := by
    apply c.ext
    intro k
    exact (congrFun ha k).symm
  have hsub : restrictedBasisEvaluation IB IB' L f hf d b x =
      a • restrictedBasisEvaluation IB IB' L f hf d b y := by
    funext k
    have hk := congrArg
      (fun q : Module.Dual ℂ (GlobalSections IB' R) =>
        q (restrictionLinear IB IB' L f hf (b k))) hlin
    simpa [evaluation, restrictedBasisEvaluation, restrictedLine] using hk
  have hsubx : restrictedBasisEvaluation IB IB' L f hf d b x ≠ 0 := by
    rw [restrictedBasisEvaluation_eq]
    exact basisEvaluation_ne_zero IB L d b
      (by simpa [(globallyGenerated_iff_baseLocus_empty IB L).1 h])
  have hsuby : restrictedBasisEvaluation IB IB' L f hf d b y ≠ 0 := by
    rw [restrictedBasisEvaluation_eq]
    exact basisEvaluation_ne_zero IB L d b
      (by simpa [(globallyGenerated_iff_baseLocus_empty IB L).1 h])
  change projectivize d (restrictedBasisEvaluation IB IB' L f hf d b x) =
    projectivize d (restrictedBasisEvaluation IB IB' L f hf d b y)
  rw [projectivize_of_ne_zero d _ hsubx,
    projectivize_of_ne_zero d _ hsuby]
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨a, hsub.symm⟩

/-- Point-injectivity of an ambient restricted subsystem transfers to the
complete linear system of *all* restricted holomorphic sections. -/
theorem completeRestrictedMap_injective_of_subsystem
    (hSub : Function.Injective
      (restrictedSubsystemMap IB IB' L f hf d b h)) :
    Function.Injective
      (projectiveEvaluationOfGenerated IB'
        (restrictedLine IB IB' L f hf) e c
        (restrictedGenerated IB IB' L f hf h)) := by
  intro x y hxy
  exact hSub (subsystem_eq_of_complete_eq IB IB' L f hf d b h e c hxy)

/-- Finite fibers also transfer from the restricted ambient subsystem to
the complete restricted linear system: every complete fiber lies inside
one subsystem fiber once a point in it is chosen. -/
theorem completeRestrictedMap_finiteFibers_of_subsystem
    (hSub : ∀ p : Space d,
      ((restrictedSubsystemMap IB IB' L f hf d b h) ⁻¹' {p}).Finite)
    (q : Space e) :
    ((projectiveEvaluationOfGenerated IB'
      (restrictedLine IB IB' L f hf) e c
      (restrictedGenerated IB IB' L f hf h)) ⁻¹' {q}).Finite := by
  let g := projectiveEvaluationOfGenerated IB'
    (restrictedLine IB IB' L f hf) e c
    (restrictedGenerated IB IB' L f hf h)
  let t := restrictedSubsystemMap IB IB' L f hf d b h
  by_cases hne : ∃ x : B', g x = q
  · obtain ⟨x, hx⟩ := hne
    apply (hSub (t x)).subset
    intro y hy
    have hgy : g y = g x := hy.trans hx.symm
    exact subsystem_eq_of_complete_eq IB IB' L f hf d b h e c hgy
  · have hempty : g ⁻¹' {q} = ∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim (hne ⟨x, hx⟩)
      · intro hx
        exact False.elim (by simpa using hx)
    change (g ⁻¹' {q}).Finite
    simpa [hempty]

/-- Restricting a finite-fiber ambient complete linear system along an
injective holomorphic map gives finite fibers for every complete restricted
system, even though ambient sections need not span all restricted sections. -/
theorem completeRestrictedMap_finiteFibers_of_ambient
    (hfInj : Function.Injective f)
    (hAmbient : ∀ p : Space d,
      ((projectiveEvaluationOfGenerated IB L d b h) ⁻¹' {p}).Finite)
    (q : Space e) :
    ((projectiveEvaluationOfGenerated IB'
      (restrictedLine IB IB' L f hf) e c
      (restrictedGenerated IB IB' L f hf h)) ⁻¹' {q}).Finite := by
  apply completeRestrictedMap_finiteFibers_of_subsystem IB IB' L f hf d b h e c
  intro p
  rw [restrictedSubsystemMap_eq_comp]
  change (f ⁻¹' ((projectiveEvaluationOfGenerated IB L d b h) ⁻¹' {p})).Finite
  exact (hAmbient p).preimage (fun _ _ _ _ hxy => hfInj hxy)

/-- On a compact complex submanifold the complete restricted system is
a topological embedding as soon as the ambient restricted subsystem is
point-injective. This is still short of proving an immersion. -/
theorem completeRestrictedMap_isEmbedding_of_subsystem
    [CompactSpace B'] [T2Space (Space e)]
    (hSub : Function.Injective
      (restrictedSubsystemMap IB IB' L f hf d b h)) :
    Topology.IsEmbedding
      (projectiveEvaluationOfGenerated IB'
        (restrictedLine IB IB' L f hf) e c
        (restrictedGenerated IB IB' L f hf h)) := by
  have hCont :=
    (projectiveEvaluationOfGenerated_contMDiff IB'
      (restrictedLine IB IB' L f hf) e c
      (restrictedGenerated IB IB' L f hf h)).continuous
  exact (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    hCont (completeRestrictedMap_injective_of_subsystem
      IB IB' L f hf d b h e c hSub) hCont.isClosedMap).isEmbedding

end
end QuaternionicSymmetry.HolomorphicLineCoreCompleteRestriction
