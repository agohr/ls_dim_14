import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.Prod

/-! Derivatives of block-diagonal operator families, including transport by
a fixed continuous linear coordinate equivalence. -/
namespace QuaternionicSymmetry.OperatorBlockDerivative
noncomputable section
variable {X V W Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem fderiv_prodMap (f : X → V →L[ℝ] V) (g : X → W →L[ℝ] W)
    (x u : X) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun y => (f y).prodMap (g y)) x u =
      (fderiv ℝ f x u).prodMap (fderiv ℝ g x u) := by
  let L := ContinuousLinearMap.prodMapL ℝ V V W W
  have hd := L.hasFDerivAt.comp x (hf.hasFDerivAt.prodMk hg.hasFDerivAt)
  exact congrArg (fun T => T u) hd.fderiv

def blockOperator (c : Z ≃L[ℝ] V × W)
    (A : V →L[ℝ] V) (B : W →L[ℝ] W) : Z →L[ℝ] Z :=
  c.symm.toContinuousLinearMap.comp ((A.prodMap B).comp c.toContinuousLinearMap)

theorem fderiv_blockOperator (c : Z ≃L[ℝ] V × W)
    (f : X → V →L[ℝ] V) (g : X → W →L[ℝ] W)
    (x u : X) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun y => blockOperator c (f y) (g y)) x u =
      blockOperator c (fderiv ℝ f x u) (fderiv ℝ g x u) := by
  let P := ContinuousLinearMap.prodMapL ℝ V V W W
  let C := c.symm.conjContinuousAlgEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hd := (C.comp P).hasFDerivAt.comp x (hf.hasFDerivAt.prodMk hg.hasFDerivAt)
  exact congrArg (fun T => T u) hd.fderiv

end
end QuaternionicSymmetry.OperatorBlockDerivative
