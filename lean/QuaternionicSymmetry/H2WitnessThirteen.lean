import QuaternionicSymmetry.DimensionThirteenFourteenDensity
import QuaternionicSymmetry.FiniteTypeCSchurSix

/-! A complete finite rational witness for the dimension-thirteen density.
The finite type-C orbital polynomials are algebraic; interpreting their
integrals and the restricted Hodge square remains separate. -/

namespace QuaternionicSymmetry.H2WitnessThirteen

open MvPolynomial
open FiniteTypeCSchurSix
noncomputable section
set_option maxHeartbeats 2000000

abbrev P := FiniteTypeCSchurSix.P

private theorem weight_one :
    C (68590932 / 2695 : ℚ) * orbital 13 1 [1] =
      C (45727288 / 315315 : ℚ) * p1 := by
  apply MvPolynomial.funext
  intro v
  norm_num [orbital, partitions, schurValue, schur, powerSum,
    QuarticOrbitalEleven.factorialRho, h1, p1, Nat.factorial]
  ring

def w1 : P :=
  C (68590932 / 2695 : ℚ) * orbital 13 1 [1]

def w2 : P :=
  C (10708383607513441749702953 / 143951500000000000000000 : ℚ) * orbital 13 2 [50, 1]
    + C (65602910510542820705739997 / 125756030400000000000000 : ℚ) * orbital 13 2 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def w3 : P :=
  C (2858719709007 / 1832600 : ℚ) * orbital 13 3 [1, 1]
    + C (4333550741029 / 8246700 : ℚ) * orbital 13 3 [1, 1, 1, 1]
    + C (45675202613 / 16493400 : ℚ) * orbital 13 3 [5, 5, 1, 1, 1, 1, 1, 1, 1, 1]

def w4 : P :=
  C (57797612703712424962645481998175417 / 20385594215910000000000000000 : ℚ) * orbital 13 4 [1, 1, 1]
    + C (1398103055863691053677063102212393 / 81542376863640000000000000000 : ℚ) * orbital 13 4 [5, 2, 2, 2]
    + C (3175237080089429103166917689513 / 8154237686364000000000000000 : ℚ) * orbital 13 4 [5, 4, 4, 2]
    + C (50206219320404685051859164229163 / 20385594215910000000000000000 : ℚ) * orbital 13 4 [10, 10, 1, 1, 1, 1, 1, 1]
    + C (10283164392804210004974670684643 / 3261695074545600000000000000 : ℚ) * orbital 13 4 [10, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def w5 : P :=
  C (529969484698848557981276116 / 57547966484403635625 : ℚ) * orbital 13 5 [1, 1, 1]
    + C (397752879455833518699970273 / 552460478250274902000 : ℚ) * orbital 13 5 [4, 1, 1, 1, 1]
    + C (241608744776390398951066 / 172643899453210906875 : ℚ) * orbital 13 5 [10, 10, 1, 1, 1]
    + C (447701333087150062092017 / 591921940982437395000 : ℚ) * orbital 13 5 [10, 1, 1, 1, 1, 1, 1, 1, 1]
    + C (82595807681135059652507 / 191826554948012118750 : ℚ) * orbital 13 5 [10, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    + C (159679884424337004559 / 8719388861273278125 : ℚ) * orbital 13 5 [20, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    + C (8834087592466133875613 / 61384497583363878000 : ℚ) * orbital 13 5 [20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def w6 : P :=
  C (27371957472941576136978915939311370873942497197111305918685467 / 737977779560740815938876408995155217630640000000000000000000 : ℚ) * orbital 13 6 [10, 3]
    + C (248645550369362999933210936446567436909753915018626160782705511 / 2213933338682222447816629226985465652891920000000000000000000 : ℚ) * orbital 13 6 [14, 5]
    + C (41331773200888048829080288220582102586760342552174507371249731 / 72456000175054552837635138337706148640099200000000000000 : ℚ) * orbital 13 6 [4, 1, 1]
    + C (106306912853123854523001574692173108871615317889249372678997 / 123980266966204457077731236711186076561947520000000000000 : ℚ) * orbital 13 6 [4, 4, 4, 1, 1]
    + C (12628437095926527878653929800597422194499412566410099270471161 / 111582240269584011369958113040067468905752768000000000000000 : ℚ) * orbital 13 6 [5, 5, 5, 3, 3]
    + C (3542745630049154836519186142180856788789684350471761236941 / 184494444890185203984719102248788804407660000000000000000 : ℚ) * orbital 13 6 [7, 7, 2, 1, 1, 1]
    + C (10008127111233974142475608949912417404193457100643361811185299 / 11069666693411112239083146134927328264459600000000000000000 : ℚ) * orbital 13 6 [11, 6, 1, 1, 1, 1]
    + C (2738418964244734630066945034757924255342335560116233481266033 / 2213933338682222447816629226985465652891920000000000000000 : ℚ) * orbital 13 6 [12, 2, 2, 1, 1, 1]
    + C (40829535099584609586615344166076582546648984758425570123451197 / 15940320038512001624279730434295352700821824000000000000000 : ℚ) * orbital 13 6 [12, 3, 3, 1, 1, 1]
    + C (186787855500731456547705433304885920491863917792483941 / 1073422224815623005002002049447498498371840000000000000 : ℚ) * orbital 13 6 [20, 20, 20, 1, 1, 1]
    + C (23343305979188311063452176259198708735207091218823038824303 / 3162761912403174925452327467122093789845600000000000000000 : ℚ) * orbital 13 6 [20, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def f1 : P := C (999999993 / 1000000000 : ℚ) * p1
def f3 : P := C (29552 / 1000000000 : ℚ) * p3
  + C (83790 / 1000000000 : ℚ) * p1 * p2
  + C (74653 / 1000000000 : ℚ) * p1 ^ 3

private theorem weight_two :
    w2 + C (18 : ℚ) * f1 ^ 2 =
      C (121006364 / 5457375 : ℚ) * p1 ^ 2 +
        C (1781548 / 716625 : ℚ) * p2 := by
  apply MvPolynomial.funext
  intro v
  norm_num [w2, f1, orbital, partitions, schurValue, schur, powerSum,
    QuarticOrbitalEleven.factorialRho, h1, h2, e1, e2,
    p1, p2, Nat.factorial]
  ring

private theorem weight_three :
    w3 = C (3397924 / 1913625 : ℚ) * p1 ^ 3 +
      C (36184556 / 49116375 : ℚ) * p1 * p2 +
      C (1323256 / 34827975 : ℚ) * p3 := by
  apply MvPolynomial.funext
  intro v
  norm_num [w3, orbital, partitions, schurValue, schur, powerSum,
    QuarticOrbitalEleven.factorialRho, h1, h2, h3, e1, e2, e3,
    p1, p2, p3, Nat.factorial]
  ring

private theorem weight_four :
    w4 + C (36 : ℚ) * f1 * f3 =
      C (9911 / 127575 : ℚ) * p1 ^ 4 +
        C (16042 / 212625 : ℚ) * p1 ^ 2 * p2 +
        C (26423 / 4465125 : ℚ) * p2 ^ 2 +
        C (284456 / 16372125 : ℚ) * p1 * p3 +
        C (8894 / 19348875 : ℚ) * p4 := by
  apply MvPolynomial.funext
  intro v
  norm_num [w4, f1, f3, orbital, partitions, schurValue, schur, powerSum,
    QuarticOrbitalEleven.factorialRho, h1, h2, h3, h4,
    e1, e2, e3, e4, p1, p2, p3, p4, Nat.factorial]
  ring

private theorem weight_five :
    w5 = C (19 / 10935 : ℚ) * p1 ^ 5 +
      C (1214 / 382725 : ℚ) * p1 ^ 3 * p2 +
      C (116 / 76545 : ℚ) * p1 ^ 2 * p3 +
      C (61 / 70875 : ℚ) * p1 * p2 ^ 2 +
      C (1154 / 2338875 : ℚ) * p1 * p4 +
      C (3596 / 13395375 : ℚ) * p2 * p3 +
      C (1168 / 19348875 : ℚ) * p5 := by
  apply MvPolynomial.funext
  intro v
  norm_num [w5, orbital, partitions, schurValue, schur, powerSum,
    QuarticOrbitalEleven.factorialRho, h1, h2, h3, h4, h5,
    e1, e2, e3, e4, e5, p1, p2, p3, p4, p5, Nat.factorial]
  ring

private theorem weight_six :
    w6 + C (18 : ℚ) * f3 ^ 2 =
      C (1 / 65610 : ℚ) * p1 ^ 6 +
        C (1 / 21870 : ℚ) * p1 ^ 4 * p2 +
        C (8 / 229635 : ℚ) * p1 ^ 3 * p3 +
        C (1 / 36450 : ℚ) * p1 ^ 2 * p2 ^ 2 +
        C (1 / 42525 : ℚ) * p1 ^ 2 * p4 +
        C (8 / 382725 : ℚ) * p1 * p2 * p3 +
        C (16 / 1403325 : ℚ) * p1 * p5 +
        C (1 / 546750 : ℚ) * p2 ^ 3 +
        C (1 / 212625 : ℚ) * p2 * p4 +
        C (16 / 8037225 : ℚ) * p3 ^ 2 +
        C (5528 / 1915538625 : ℚ) * p6 := by
  apply MvPolynomial.funext
  intro v
  norm_num [w6, f3, orbital, partitions, schurValue, schur, powerSum,
    QuarticOrbitalEleven.factorialRho, h1, h2, h3, h4, h5, h6,
    e1, e2, e3, e4, e5, e6, p1, p2, p3, p4, p5, p6, Nat.factorial]
  ring

/-- Embed reduced power sums into the full polynomial algebra, retaining
`u` as an independent variable. -/
def embed : P →ₐ[ℚ] DimensionThirteenFourteenDensity.P :=
  MvPolynomial.aeval ![DimensionThirteenFourteenDensity.p1,
    DimensionThirteenFourteenDensity.p2, DimensionThirteenFourteenDensity.p3,
    DimensionThirteenFourteenDensity.p4, DimensionThirteenFourteenDensity.p5,
    DimensionThirteenFourteenDensity.p6]

def factor : DimensionThirteenFourteenDensity.P :=
  DimensionThirteenFourteenDensity.u ^ 2 * embed f1 + embed f3

def orbitalSum : DimensionThirteenFourteenDensity.P :=
  DimensionThirteenFourteenDensity.u ^ 12 * embed w1 +
    DimensionThirteenFourteenDensity.u ^ 11 * embed w2 +
    DimensionThirteenFourteenDensity.u ^ 10 * embed w3 +
    DimensionThirteenFourteenDensity.u ^ 9 * embed w4 +
    DimensionThirteenFourteenDensity.u ^ 8 * embed w5 +
    DimensionThirteenFourteenDensity.u ^ 7 * embed w6

def witness : DimensionThirteenFourteenDensity.P :=
  C 392 * DimensionThirteenFourteenDensity.u ^ 13 + orbitalSum +
    C 18 * factor ^ 2 * DimensionThirteenFourteenDensity.u ^ 7

private theorem w1_value : w1 = C (45727288 / 315315 : ℚ) * p1 := by
  simpa only [w1] using weight_one

theorem density13_witness : DimensionThirteenFourteenDensity.density13 = witness := by
  rw [DimensionThirteenFourteenDensity.density13_printed]
  unfold witness orbitalSum factor
  rw [w1_value]
  have h2 := congrArg embed weight_two
  have h3 := congrArg embed weight_three
  have h4 := congrArg embed weight_four
  have h5 := congrArg embed weight_five
  have h6 := congrArg embed weight_six
  simp only [map_add, map_mul, map_pow] at h2 h3 h4 h5 h6
  simp only [DimensionThirteenFourteenDensity.printed13,
    DimensionThirteenFourteenDensity.q13]
  simp [embed, p1, p2, p3, p4, p5, p6,
    DimensionThirteenFourteenDensity.p1, DimensionThirteenFourteenDensity.p2,
    DimensionThirteenFourteenDensity.p3, DimensionThirteenFourteenDensity.p4,
    DimensionThirteenFourteenDensity.p5, DimensionThirteenFourteenDensity.p6] at h2 h3 h4 h5 h6 ⊢
  simp only [map_ofNat] at h2 h3 h4 h5 h6 ⊢
  linear_combination
    -(DimensionThirteenFourteenDensity.u ^ 11) * h2 -
    DimensionThirteenFourteenDensity.u ^ 10 * h3 -
    DimensionThirteenFourteenDensity.u ^ 9 * h4 -
    DimensionThirteenFourteenDensity.u ^ 8 * h5 -
    DimensionThirteenFourteenDensity.u ^ 7 * h6

end
end QuaternionicSymmetry.H2WitnessThirteen
