import QuaternionicSymmetry.ComplexProjectiveProjCutoutClosedPointEquiv
import Mathlib.Topology.Algebra.MvPolynomial

/-! The classical-point map is continuous from the genuine complex
projective topology to the Zariski topology of Proj. Only this direction
is asserted: the closed-point set equivalence is not a homeomorphism. -/

namespace QuaternionicSymmetry.ComplexProjectiveProjContinuous

open ComplexProjectiveTopology ComplexProjectiveLineProjPoint
open ComplexProjectiveLineProjLocus ComplexProjectiveLineProjInvariant
open ComplexProjectiveLineKernelHomogeneous
open ComplexProjectiveProjClosedPointEquiv
open scoped LinearAlgebra.Projectivization Polynomial
noncomputable section

variable {d : ℕ}

local instance (d : ℕ) : GradedAlgebra
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
  MvPolynomial.gradedAlgebra

theorem mem_linePrimeIdeal_iff (v : Coord d)
    (p : MvPolynomial (Fin (d + 1)) ℂ) :
    p ∈ linePrimeIdeal v ↔ ∀ c : ℂ, MvPolynomial.eval (c • v) p = 0 := by
  change lineEval v p = 0 ↔ _
  constructor
  · intro hp c
    have h := congrArg (Polynomial.eval c) hp
    simpa only [eval_lineEval, Polynomial.eval_zero] using h
  · intro hp
    apply Polynomial.funext
    intro c
    simpa only [eval_lineEval, Polynomial.eval_zero] using hp c

theorem projectivePointToProj_continuous :
    Continuous (projectivePointToProj (d := d)) := by
  change @Continuous (Space d) _
    (TopologicalSpace.coinduced (Projectivization.mk' ℂ) inferInstance) _ _
  apply continuous_coinduced_dom.mpr
  apply continuous_iff_isClosed.mpr
  intro Z hZ
  obtain ⟨S,rfl⟩ := (ProjectiveSpectrum.isClosed_iff_zeroLocus _ Z).mp hZ
  have hpre :
      (projectivePointToProj ∘ Projectivization.mk' ℂ) ⁻¹'
        ProjectiveSpectrum.zeroLocus
          (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) S =
      ⋂ p ∈ S, ⋂ c : ℂ,
        {v : {v : Coord d // v ≠ 0} | MvPolynomial.eval (c • v.1) p = 0} := by
    ext v
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_iInter,
      Set.mem_setOf_eq]
    change projectivePointToProj (Projectivization.mk ℂ v.1 v.2) ∈ _ ↔ _
    rw [projectivePointToProj_mk]
    change (∀ p ∈ S, p ∈ lineHomogeneousPrime v.1) ↔ _
    have hid := lineHomogeneousPrime_toIdeal v.1 v.2
    change (∀ p ∈ S, p ∈ (lineHomogeneousPrime v.1).toIdeal) ↔ _
    rw [hid]
    simp only [mem_linePrimeIdeal_iff]
  rw [hpre]
  apply isClosed_iInter
  intro p
  apply isClosed_iInter
  intro hp
  apply isClosed_iInter
  intro c
  exact isClosed_eq
    (p.continuous_eval.comp (continuous_const.smul continuous_subtype_val))
    continuous_const

theorem projectiveClosedPointEquiv_continuous :
    Continuous (projectiveClosedPointEquiv (d := d)) :=
  projectivePointToProj_continuous.subtype_mk _

end
end QuaternionicSymmetry.ComplexProjectiveProjContinuous
