import QuaternionicSymmetry.ContinuousAlgebraWedgePowers
import QuaternionicSymmetry.LocalEndomorphismTrace

/-! Trace of a normalized algebra-valued wedge power is additive across a
fixed orthogonal direct-sum block representation. -/
namespace QuaternionicSymmetry.ContinuousBlockTracePowers
open ContinuousAlgebraWedgePowers LocalChernWeilTracePowers
  LocalEndomorphismTrace
noncomputable section
set_option maxHeartbeats 1000000

variable {B V W : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

private abbrev Z := WithLp 2 (V × W)
private abbrev EV := V →L[ℝ] V
private abbrev EW := W →L[ℝ] W
private abbrev EZ := Z (V := V) (W := W) →L[ℝ] Z (V := V) (W := W)

private def blockLinear : (EV (V := V) × EW (W := W)) →ₗ[ℝ] EZ (V := V) (W := W) where
  toFun z :=
    let c := WithLp.prodContinuousLinearEquiv 2 ℝ V W
    c.symm.toContinuousLinearMap.comp
      ((z.1.prodMap z.2).comp c.toContinuousLinearMap)
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ V W).injective
    apply Prod.ext <;>
      simp [ContinuousLinearMap.prodMap, map_add]
  map_smul' r a := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ V W).injective
    apply Prod.ext <;>
      simp [ContinuousLinearMap.prodMap, map_smul]

def blockCLM : (EV (V := V) × EW (W := W)) →L[ℝ] EZ (V := V) (W := W) :=
  blockLinear.toContinuousLinearMap

@[simp] theorem blockCLM_apply (a : EV (V := V)) (b : EW (W := W))
    (x : Z (V := V) (W := W)) :
    (WithLp.prodContinuousLinearEquiv 2 ℝ V W) (blockCLM (a,b) x) =
      (a ((WithLp.prodContinuousLinearEquiv 2 ℝ V W) x).1,
       b ((WithLp.prodContinuousLinearEquiv 2 ℝ V W) x).2) := rfl

/-- Block embedding is multiplicative. -/
theorem blockCLM_mul (a b : EV (V := V) × EW (W := W)) :
    blockCLM (a * b) = blockCLM a * blockCLM b := by
  apply ContinuousLinearMap.ext
  intro x
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ V W).injective
  change
    ((a.1 * b.1) ((WithLp.prodContinuousLinearEquiv 2 ℝ V W x).1),
      (a.2 * b.2) ((WithLp.prodContinuousLinearEquiv 2 ℝ V W x).2)) =
    (a.1 (b.1 ((WithLp.prodContinuousLinearEquiv 2 ℝ V W x).1)),
      a.2 (b.2 ((WithLp.prodContinuousLinearEquiv 2 ℝ V W x).2)))
  simp [ContinuousLinearMap.mul_apply]

/-- Real trace of a block endomorphism is the sum of block traces. -/
theorem blockCLM_trace (a : EV (V := V)) (b : EW (W := W)) :
    traceCLM (blockCLM (a,b)) = traceCLM a + traceCLM b := by
  let c := WithLp.prodContinuousLinearEquiv 2 ℝ V W
  have hblock :
      c.toLinearEquiv.conj (blockCLM (a,b)).toLinearMap =
        a.toLinearMap.prodMap b.toLinearMap := by
    apply LinearMap.ext
    intro z
    apply Prod.ext <;> rfl
  have htrace := LinearMap.trace_conj'
    (blockCLM (a,b)).toLinearMap c.toLinearEquiv
  rw [hblock, LinearMap.trace_prodMap'] at htrace
  exact htrace.symm

local instance : NormedRing (EV (V := V)) := inferInstance
local instance : NormedAlgebra ℝ (EV (V := V)) := inferInstance
local instance : NormedRing (EW (W := W)) := inferInstance
local instance : NormedAlgebra ℝ (EW (W := W)) := inferInstance
local instance : NormedRing (EZ (V := V) (W := W)) := inferInstance
local instance : NormedAlgebra ℝ (EZ (V := V) (W := W)) := inferInstance
local instance : NormedRing (EV (V := V) × EW (W := W)) := inferInstance
local instance : NormedAlgebra ℝ (EV (V := V) × EW (W := W)) := inferInstance

/-- Exact all-degree splitting of normalized trace powers of a block-valued
two-form, before choosing any connection. -/
theorem trace_power_block (F : B [⋀^Fin 2]→L[ℝ] EV (V := V))
    (G : B [⋀^Fin 2]→L[ℝ] EW (W := W)) (k : ℕ) :
    traceCLM.compContinuousAlternatingMap
      (power (blockCLM.compContinuousAlternatingMap (F.prod G)) k) =
    traceCLM.compContinuousAlternatingMap (power F k) +
      traceCLM.compContinuousAlternatingMap (power G k) := by
  apply ContinuousAlternatingMap.ext
  intro w
  have hb := congrArg (fun H : B [⋀^Fin (powerDegree k)]→L[ℝ]
      EZ (V := V) (W := W) => H w)
    (map_power blockCLM blockCLM_mul (F.prod G) k)
  let fstCLM := ContinuousLinearMap.fst ℝ (EV (V := V)) (EW (W := W))
  let sndCLM := ContinuousLinearMap.snd ℝ (EV (V := V)) (EW (W := W))
  have hf := congrArg (fun H : B [⋀^Fin (powerDegree k)]→L[ℝ]
      EV (V := V) => H w)
    (map_power fstCLM (by intro a b; rfl) (F.prod G) k)
  have hg := congrArg (fun H : B [⋀^Fin (powerDegree k)]→L[ℝ]
      EW (W := W) => H w)
    (map_power sndCLM (by intro a b; rfl) (F.prod G) k)
  change traceCLM (power (blockCLM.compContinuousAlternatingMap (F.prod G)) k w) =
    traceCLM (power F k w) + traceCLM (power G k w)
  change blockCLM (power (F.prod G) k w) =
    power (blockCLM.compContinuousAlternatingMap (F.prod G)) k w at hb
  rw [← hb, blockCLM_trace]
  change (power (F.prod G) k w).1 = power F k w at hf
  change (power (F.prod G) k w).2 = power G k w at hg
  rw [hf, hg]

end
end QuaternionicSymmetry.ContinuousBlockTracePowers
