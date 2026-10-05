import QuaternionicSymmetry.KillingFieldsPaperCertificate
import QuaternionicSymmetry.Arithmetic
import QuaternionicSymmetry.ManifoldSevenVariableGradedEvaluation

/-! The paper's even certificates and adjacent averages, expressed as positive
linear combinations in a single rank. No pointwise sign of a product of
orbital moments is asserted: the mixed contribution stays one global square. -/
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
open ManifoldSevenVariableGradedEvaluation
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

/-- Coefficient, Weyl weight, and one of the twelve fixed spectra. -/
def terms : ℕ → List (ℚ × ℕ × Fin 12)
  | 2 => []
  | 3 => [(1624 / 15, 1, 0)]
  | 4 => [(3248 / 15, 1, 0)]
  | 5 => [(1624 / 15, 1, 0),
      (84448 / 225, 1, 0),
      (10034 / 33, 2, 0),
      (29522 / 4125, 2, 6)]
  | 6 => [(168896 / 225, 1, 0),
      (20068 / 33, 2, 0),
      (59044 / 4125, 2, 6)]
  | 7 => [(84448 / 225, 1, 0),
      (10034 / 33, 2, 0),
      (29522 / 4125, 2, 6),
      (186992 / 225, 1, 0),
      (1739449 / 2079, 2, 0),
      (7833103 / 259875, 2, 6),
      (1555997407 / 925530954, 3, 6),
      (69513876931 / 925530954, 3, 7),
      (8363273489 / 925530954, 3, 10)]
  | 8 => [(373984 / 225, 1, 0),
      (3478898 / 2079, 2, 0),
      (15666206 / 259875, 2, 6),
      (1555997407 / 462765477, 3, 6),
      (69513876931 / 462765477, 3, 7),
      (8363273489 / 462765477, 3, 10)]
  | 9 => [(186992 / 225, 1, 0),
      (1739449 / 2079, 2, 0),
      (7833103 / 259875, 2, 6),
      (1555997407 / 925530954, 3, 6),
      (69513876931 / 925530954, 3, 7),
      (8363273489 / 925530954, 3, 10),
      (1682464 / 1125, 1, 0),
      (5626348 / 4455, 2, 0),
      (43225312 / 556875, 2, 6),
      (218013654061 / 13882964310, 3, 6),
      (20876910519307 / 97180750170, 3, 7),
      (578272362323 / 13882964310, 3, 10),
      (76725377446472029 / 6840085454190, 4, 2),
      (6526042748888190253 / 492486152701680, 4, 5),
      (920100557319229 / 9120113938920, 4, 7),
      (245063979915392 / 10260128181285, 4, 10),
      (2710003708106171 / 492486152701680, 4, 11)]
  | 10 => [(3364928 / 1125, 1, 0),
      (11252696 / 4455, 2, 0),
      (86450624 / 556875, 2, 6),
      (218013654061 / 6941482155, 3, 6),
      (20876910519307 / 48590375085, 3, 7),
      (578272362323 / 6941482155, 3, 10),
      (76725377446472029 / 3420042727095, 4, 2),
      (6526042748888190253 / 246243076350840, 4, 5),
      (920100557319229 / 4560056969460, 4, 7),
      (490127959830784 / 10260128181285, 4, 10),
      (2710003708106171 / 246243076350840, 4, 11)]
  | 11 => [(1682464 / 1125, 1, 0),
      (5626348 / 4455, 2, 0),
      (43225312 / 556875, 2, 6),
      (218013654061 / 13882964310, 3, 6),
      (20876910519307 / 97180750170, 3, 7),
      (578272362323 / 13882964310, 3, 10),
      (76725377446472029 / 6840085454190, 4, 2),
      (6526042748888190253 / 492486152701680, 4, 5),
      (920100557319229 / 9120113938920, 4, 7),
      (245063979915392 / 10260128181285, 4, 10),
      (2710003708106171 / 492486152701680, 4, 11),
      (88472504 / 37125, 1, 0),
      (1135846567 / 1029105, 2, 0),
      (20298758713 / 128638125, 2, 6),
      (14675431142402 / 229068911115, 3, 6),
      (529697809179824 / 1603482377805, 3, 7),
      (4283136662894 / 45813782223, 3, 10),
      (1177945968325523269 / 225722819988270, 4, 2),
      (1578553797143219004613 / 16252043039155440, 4, 5),
      (34057685089397437 / 300963759984360, 4, 7),
      (57413318891409872 / 338584229982405, 4, 10),
      (315399374278428371 / 16252043039155440, 4, 11),
      (88894646316395317116326928068 / 1424114964987280699682475, 5, 0),
      (14905767856075301327320167776 / 284822992997456139936495, 5, 2),
      (21426537390738721689476 / 18988199533163742662433, 5, 4),
      (221215195239914960994909008563 / 1708937957984736839618970, 5, 5),
      (6247484631148399677275293 / 18988199533163742662433, 5, 7),
      (4090995445656709362495128 / 94940997665818713312165, 5, 8),
      (53261846158644562302798617 / 1708937957984736839618970, 5, 11)]
  | 12 => [(176945008 / 37125, 1, 0),
      (2271693134 / 1029105, 2, 0),
      (40597517426 / 128638125, 2, 6),
      (29350862284804 / 229068911115, 3, 6),
      (1059395618359648 / 1603482377805, 3, 7),
      (8566273325788 / 45813782223, 3, 10),
      (1177945968325523269 / 112861409994135, 4, 2),
      (1578553797143219004613 / 8126021519577720, 4, 5),
      (34057685089397437 / 150481879992180, 4, 7),
      (114826637782819744 / 338584229982405, 4, 10),
      (315399374278428371 / 8126021519577720, 4, 11),
      (177789292632790634232653856136 / 1424114964987280699682475, 5, 0),
      (29811535712150602654640335552 / 284822992997456139936495, 5, 2),
      (42853074781477443378952 / 18988199533163742662433, 5, 4),
      (221215195239914960994909008563 / 854468978992368419809485, 5, 5),
      (12494969262296799354550586 / 18988199533163742662433, 5, 7),
      (8181990891313418724990256 / 94940997665818713312165, 5, 8),
      (53261846158644562302798617 / 854468978992368419809485, 5, 11)]
  | 13 => [(88472504 / 37125, 1, 0),
      (1135846567 / 1029105, 2, 0),
      (20298758713 / 128638125, 2, 6),
      (14675431142402 / 229068911115, 3, 6),
      (529697809179824 / 1603482377805, 3, 7),
      (4283136662894 / 45813782223, 3, 10),
      (1177945968325523269 / 225722819988270, 4, 2),
      (1578553797143219004613 / 16252043039155440, 4, 5),
      (34057685089397437 / 300963759984360, 4, 7),
      (57413318891409872 / 338584229982405, 4, 10),
      (315399374278428371 / 16252043039155440, 4, 11),
      (88894646316395317116326928068 / 1424114964987280699682475, 5, 0),
      (14905767856075301327320167776 / 284822992997456139936495, 5, 2),
      (21426537390738721689476 / 18988199533163742662433, 5, 4),
      (221215195239914960994909008563 / 1708937957984736839618970, 5, 5),
      (6247484631148399677275293 / 18988199533163742662433, 5, 7),
      (4090995445656709362495128 / 94940997665818713312165, 5, 8),
      (53261846158644562302798617 / 1708937957984736839618970, 5, 11),
      (11840372416 / 3378375, 1, 0),
      (115718127170636 / 13579040475, 2, 0),
      (2551076356204 / 339476011875, 2, 6),
      (11247385162635668 / 62535812734395, 3, 6),
      (650601791843556892 / 2188753445703825, 3, 7),
      (38691103135930268 / 312679063671975, 3, 10),
      (1014038932884089708310268349 / 99368627623571044059750, 4, 3),
      (427744780900323760797628 / 115930065560832884736375, 4, 6),
      (14193516825066981495946786 / 23186013112166576947275, 4, 9),
      (62563465422821843446273 / 27823215734599892336730, 4, 10),
      (67016005016388156452909881 / 347790196682498654209125, 4, 11),
      (219279270899813636068459224395422 / 21383086199284019705732362125, 5, 0),
      (33051775363633280107835440257074 / 4276617239856803941146472425, 5, 2),
      (2828441591169237064340802398 / 285107815990453596076431495, 5, 4),
      (15128757886994191974115488762985531 / 12829851719570411823439417275, 5, 5),
      (6404565848887085558177065499 / 31678646221161510675159055, 5, 7),
      (439598531516221854574771731052 / 1425539079952267980382157475, 5, 8),
      (3292495033549157333827853528804 / 12829851719570411823439417275, 5, 11),
      (1072713099860856215658012944221351564853803 / 22582982138009977971166598338342823100, 6, 0),
      (200235994468922957393056999584909121102438448131 / 2529293999457117532770659013894396187200, 6, 1),
      (11242769265826533321210507111460347120647701 / 5735360542986661072042310689102939200, 6, 2),
      (39508359428371035238657634948304286691561 / 60221285701359941256444262235580861600, 6, 3),
      (5210091745017796631093004718311475432651121 / 14951491622406606105048230624006282880, 6, 5),
      (745812544172353353492195216519988624127 / 2709957856561197356539991800601138772000, 6, 6),
      (10775452588479621047849188090482837414331 / 8306384234670336725026794791114601600, 6, 7),
      (3649953617987630632603068892691073143591 / 421548999909519588795109835649066031200, 6, 8),
      (99594696754186270092778299457061134409 / 8603040814479991608063466033654408800, 6, 9),
      (422864623449995853268401257126800021169 / 6452280610859993706047599525240806600, 6, 10),
      (154938952549795997151949198682495339 / 12904561221719987412095199050481613200, 6, 11)]
  | 14 => [(23680744832 / 3378375, 1, 0),
      (231436254341272 / 13579040475, 2, 0),
      (5102152712408 / 339476011875, 2, 6),
      (22494770325271336 / 62535812734395, 3, 6),
      (1301203583687113784 / 2188753445703825, 3, 7),
      (77382206271860536 / 312679063671975, 3, 10),
      (1014038932884089708310268349 / 49684313811785522029875, 4, 3),
      (855489561800647521595256 / 115930065560832884736375, 4, 6),
      (28387033650133962991893572 / 23186013112166576947275, 4, 9),
      (62563465422821843446273 / 13911607867299946168365, 4, 10),
      (134032010032776312905819762 / 347790196682498654209125, 4, 11),
      (438558541799627272136918448790844 / 21383086199284019705732362125, 5, 0),
      (66103550727266560215670880514148 / 4276617239856803941146472425, 5, 2),
      (5656883182338474128681604796 / 285107815990453596076431495, 5, 4),
      (30257515773988383948230977525971062 / 12829851719570411823439417275, 5, 5),
      (12809131697774171116354130998 / 31678646221161510675159055, 5, 7),
      (879197063032443709149543462104 / 1425539079952267980382157475, 5, 8),
      (6584990067098314667655707057608 / 12829851719570411823439417275, 5, 11),
      (1072713099860856215658012944221351564853803 / 11291491069004988985583299169171411550, 6, 0),
      (200235994468922957393056999584909121102438448131 / 1264646999728558766385329506947198093600, 6, 1),
      (11242769265826533321210507111460347120647701 / 2867680271493330536021155344551469600, 6, 2),
      (39508359428371035238657634948304286691561 / 30110642850679970628222131117790430800, 6, 3),
      (5210091745017796631093004718311475432651121 / 7475745811203303052524115312003141440, 6, 5),
      (745812544172353353492195216519988624127 / 1354978928280598678269995900300569386000, 6, 6),
      (10775452588479621047849188090482837414331 / 4153192117335168362513397395557300800, 6, 7),
      (3649953617987630632603068892691073143591 / 210774499954759794397554917824533015600, 6, 8),
      (99594696754186270092778299457061134409 / 4301520407239995804031733016827204400, 6, 9),
      (422864623449995853268401257126800021169 / 3226140305429996853023799762620403300, 6, 10),
      (154938952549795997151949198682495339 / 6452280610859993706047599525240806600, 6, 11)]
  | _ => []

theorem terms_admissible (n : ℕ) (hn : 2 ≤ n ∧ n ≤ 14)
    (t : ℚ × ℕ × Fin 12) (ht : t ∈ terms n) :
    0 < t.1 ∧ 1 ≤ t.2.1 ∧ t.2.1 ≤ 6 ∧ t.2.1 ≤ n := by
  rcases hn with ⟨hlo, hhi⟩
  have hall : ∀ t ∈ terms n, 0 < t.1 ∧ 1 ≤ t.2.1 ∧ t.2.1 ≤ 6 ∧ t.2.1 ≤ n := by
    interval_cases n <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, terms]
  exact hall t ht

def remainder (n : ℕ) : P :=
  ((terms n).map fun t => C t.1 * (u ^ (n-t.2.1) * moment t.2.1 t.2.2)).sum

def squareCoefficient (n : ℕ) : ℚ := if n = 13 then 1/2 else if n = 14 then 1 else 0

def squareTerm (n : ℕ) : P := C (squareCoefficient n) * (eta ^ 2 * u ^ (n-6))

theorem full_certificate2 : density 2 =
    C (16 : ℚ) * u ^ 2 + squareTerm 2 + remainder 2 := by
  simp only [density, reduced, reduced2, remainder, terms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, squareTerm, squareCoefficient]
  norm_num only
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, ]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem full_certificate3 : density 3 =
    C (32 : ℚ) * u ^ 3 + squareTerm 3 + remainder 3 := by
  simp only [density, reduced, reduced3, remainder, terms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, squareTerm, squareCoefficient]
  norm_num only
  rw [moment1_0_eq]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, expanded1_0]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem full_certificate4 : density 4 =
    C (48 : ℚ) * u ^ 4 + squareTerm 4 + remainder 4 := by
  simp only [density, reduced, reduced4, remainder, terms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, squareTerm, squareCoefficient]
  norm_num only
  rw [moment1_0_eq]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, expanded1_0]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem full_certificate5 : density 5 =
    C (72 : ℚ) * u ^ 5 + squareTerm 5 + remainder 5 := by
  simp only [density, reduced, reduced5, remainder, terms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, squareTerm, squareCoefficient]
  norm_num only
  rw [moment1_0_eq, moment2_0_eq, moment2_6_eq]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, expanded1_0, expanded2_0, expanded2_6]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem full_certificate6 : density 6 =
    C (96 : ℚ) * u ^ 6 + squareTerm 6 + remainder 6 := by
  simp only [density, reduced, reduced6, remainder, terms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, squareTerm, squareCoefficient]
  norm_num only
  rw [moment1_0_eq, moment2_0_eq, moment2_6_eq]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, expanded1_0, expanded2_0, expanded2_6]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem full_certificate7 : density 7 =
    C (128 : ℚ) * u ^ 7 + squareTerm 7 + remainder 7 := by
  simp only [density, reduced, reduced7, remainder, terms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, squareTerm, squareCoefficient]
  norm_num only
  rw [moment1_0_eq, moment2_0_eq, moment2_6_eq, moment3_6_eq, moment3_7_eq, moment3_10_eq]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, expanded1_0, expanded2_0, expanded2_6, expanded3_6, expanded3_7, expanded3_10]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem full_certificate8 : density 8 =
    C (160 : ℚ) * u ^ 8 + squareTerm 8 + remainder 8 := by
  simp only [density, reduced, reduced8, remainder, terms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, squareTerm, squareCoefficient]
  norm_num only
  rw [moment1_0_eq, moment2_0_eq, moment2_6_eq, moment3_6_eq, moment3_7_eq, moment3_10_eq]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, expanded1_0, expanded2_0, expanded2_6, expanded3_6, expanded3_7, expanded3_10]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem full_certificate9 : density 9 =
    C (200 : ℚ) * u ^ 9 + squareTerm 9 + remainder 9 := by
  simp only [density, reduced, reduced9, remainder, terms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, squareTerm, squareCoefficient]
  norm_num only
  rw [moment1_0_eq, moment2_0_eq, moment2_6_eq, moment3_6_eq, moment3_7_eq, moment3_10_eq, moment4_2_eq, moment4_5_eq, moment4_7_eq, moment4_10_eq, moment4_11_eq]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, expanded1_0, expanded2_0, expanded2_6, expanded3_6, expanded3_7, expanded3_10, expanded4_2, expanded4_5, expanded4_7, expanded4_10, expanded4_11]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem full_certificate10 : density 10 =
    C (240 : ℚ) * u ^ 10 + squareTerm 10 + remainder 10 := by
  simp only [density, reduced, reduced10, remainder, terms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, squareTerm, squareCoefficient]
  norm_num only
  rw [moment1_0_eq, moment2_0_eq, moment2_6_eq, moment3_6_eq, moment3_7_eq, moment3_10_eq, moment4_2_eq, moment4_5_eq, moment4_7_eq, moment4_10_eq, moment4_11_eq]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, expanded1_0, expanded2_0, expanded2_6, expanded3_6, expanded3_7, expanded3_10, expanded4_2, expanded4_5, expanded4_7, expanded4_10, expanded4_11]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem full_certificate11 : density 11 =
    C (288 : ℚ) * u ^ 11 + squareTerm 11 + remainder 11 := by
  simp only [density, reduced, reduced11, remainder, terms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, squareTerm, squareCoefficient]
  norm_num only
  rw [moment1_0_eq, moment2_0_eq, moment2_6_eq, moment3_6_eq, moment3_7_eq, moment3_10_eq, moment4_2_eq, moment4_5_eq, moment4_7_eq, moment4_10_eq, moment4_11_eq, moment5_0_eq, moment5_2_eq, moment5_4_eq, moment5_5_eq, moment5_7_eq, moment5_8_eq, moment5_11_eq]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, expanded1_0, expanded2_0, expanded2_6, expanded3_6, expanded3_7, expanded3_10, expanded4_2, expanded4_5, expanded4_7, expanded4_10, expanded4_11, expanded5_0, expanded5_2, expanded5_4, expanded5_5, expanded5_7, expanded5_8, expanded5_11]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem full_certificate12 : density 12 =
    C (336 : ℚ) * u ^ 12 + squareTerm 12 + remainder 12 := by
  simp only [density, reduced, reduced12, remainder, terms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, squareTerm, squareCoefficient]
  norm_num only
  rw [moment1_0_eq, moment2_0_eq, moment2_6_eq, moment3_6_eq, moment3_7_eq, moment3_10_eq, moment4_2_eq, moment4_5_eq, moment4_7_eq, moment4_10_eq, moment4_11_eq, moment5_0_eq, moment5_2_eq, moment5_4_eq, moment5_5_eq, moment5_7_eq, moment5_8_eq, moment5_11_eq]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, expanded1_0, expanded2_0, expanded2_6, expanded3_6, expanded3_7, expanded3_10, expanded4_2, expanded4_5, expanded4_7, expanded4_10, expanded4_11, expanded5_0, expanded5_2, expanded5_4, expanded5_5, expanded5_7, expanded5_8, expanded5_11]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem full_certificate13 : density 13 =
    C (392 : ℚ) * u ^ 13 + squareTerm 13 + remainder 13 := by
  simp only [density, reduced, reduced13, remainder, terms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, squareTerm, squareCoefficient]
  norm_num only
  rw [moment1_0_eq, moment2_0_eq, moment2_6_eq, moment3_6_eq, moment3_7_eq, moment3_10_eq, moment4_2_eq, moment4_3_eq, moment4_5_eq, moment4_6_eq, moment4_7_eq, moment4_9_eq, moment4_10_eq, moment4_11_eq, moment5_0_eq, moment5_2_eq, moment5_4_eq, moment5_5_eq, moment5_7_eq, moment5_8_eq, moment5_11_eq, moment6_0_eq, moment6_1_eq, moment6_2_eq, moment6_3_eq, moment6_5_eq, moment6_6_eq, moment6_7_eq, moment6_8_eq, moment6_9_eq, moment6_10_eq, moment6_11_eq, eta_eq]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, expanded1_0, expanded2_0, expanded2_6, expanded3_6, expanded3_7, expanded3_10, expanded4_2, expanded4_3, expanded4_5, expanded4_6, expanded4_7, expanded4_9, expanded4_10, expanded4_11, expanded5_0, expanded5_2, expanded5_4, expanded5_5, expanded5_7, expanded5_8, expanded5_11, expanded6_0, expanded6_1, expanded6_2, expanded6_3, expanded6_5, expanded6_6, expanded6_7, expanded6_8, expanded6_9, expanded6_10, expanded6_11, expandedEta]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem full_certificate14 : density 14 =
    C (448 : ℚ) * u ^ 14 + squareTerm 14 + remainder 14 := by
  simp only [density, reduced, reduced14, remainder, terms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, squareTerm, squareCoefficient]
  norm_num only
  rw [moment1_0_eq, moment2_0_eq, moment2_6_eq, moment3_6_eq, moment3_7_eq, moment3_10_eq, moment4_3_eq, moment4_6_eq, moment4_9_eq, moment4_10_eq, moment4_11_eq, moment5_0_eq, moment5_2_eq, moment5_4_eq, moment5_5_eq, moment5_7_eq, moment5_8_eq, moment5_11_eq, moment6_0_eq, moment6_1_eq, moment6_2_eq, moment6_3_eq, moment6_5_eq, moment6_6_eq, moment6_7_eq, moment6_8_eq, moment6_9_eq, moment6_10_eq, moment6_11_eq, eta_eq]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, expanded1_0, expanded2_0, expanded2_6, expanded3_6, expanded3_7, expanded3_10, expanded4_3, expanded4_6, expanded4_9, expanded4_10, expanded4_11, expanded5_0, expanded5_2, expanded5_4, expanded5_5, expanded5_7, expanded5_8, expanded5_11, expanded6_0, expanded6_1, expanded6_2, expanded6_3, expanded6_5, expanded6_6, expanded6_7, expanded6_8, expanded6_9, expanded6_10, expanded6_11, expandedEta]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem full_certificate (n : ℕ) (hn : 2 ≤ n ∧ n ≤ 14) :
    density n = C (scalarCoefficient n : ℚ) * u ^ n + squareTerm n + remainder n := by
  rcases hn with ⟨hlo, hhi⟩
  interval_cases n
  · simpa only [scalarCoefficient, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      Nat.reducePow, if_pos, if_false, Nat.cast_ofNat] using full_certificate2
  · simpa only [scalarCoefficient, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      Nat.reducePow, if_pos, if_false, Nat.cast_ofNat] using full_certificate3
  · simpa only [scalarCoefficient, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      Nat.reducePow, if_pos, if_false, Nat.cast_ofNat] using full_certificate4
  · simpa only [scalarCoefficient, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      Nat.reducePow, if_pos, if_false, Nat.cast_ofNat] using full_certificate5
  · simpa only [scalarCoefficient, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      Nat.reducePow, if_pos, if_false, Nat.cast_ofNat] using full_certificate6
  · simpa only [scalarCoefficient, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      Nat.reducePow, if_pos, if_false, Nat.cast_ofNat] using full_certificate7
  · simpa only [scalarCoefficient, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      Nat.reducePow, if_pos, if_false, Nat.cast_ofNat] using full_certificate8
  · simpa only [scalarCoefficient, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      Nat.reducePow, if_pos, if_false, Nat.cast_ofNat] using full_certificate9
  · simpa only [scalarCoefficient, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      Nat.reducePow, if_pos, if_false, Nat.cast_ofNat] using full_certificate10
  · simpa only [scalarCoefficient, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      Nat.reducePow, if_pos, if_false, Nat.cast_ofNat] using full_certificate11
  · simpa only [scalarCoefficient, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      Nat.reducePow, if_pos, if_false, Nat.cast_ofNat] using full_certificate12
  · simpa only [scalarCoefficient, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      Nat.reducePow, if_pos, if_false, Nat.cast_ofNat] using full_certificate13
  · simpa only [scalarCoefficient, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      Nat.reducePow, if_pos, if_false, Nat.cast_ofNat] using full_certificate14

/-- Integration is used only linearly. Orbital signs and the global Hodge
square sign are distinct premises, so this cannot silently multiply
nonnegative characteristic forms. -/
theorem linear_lower_bound (n : ℕ) (hn : 2 ≤ n ∧ n ≤ 14) (L : P →ₗ[ℚ] ℝ)
    (hOrbital : ∀ t ∈ terms n, 0 ≤ L (u ^ (n-t.2.1) * moment t.2.1 t.2.2))
    (hSquare : 0 ≤ L (squareTerm n)) :
    (scalarCoefficient n : ℝ) * L (u ^ n) ≤ L (density n) := by
  have hr : 0 ≤ L (remainder n) := by
    unfold remainder
    rw [map_list_sum]
    apply List.sum_nonneg
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
    rw [← smul_eq_C_mul, map_smul, Rat.smul_def]
    exact mul_nonneg (by exact_mod_cast (terms_admissible n hn t ht).1.le) (hOrbital t ht)
  rw [full_certificate n hn, map_add, map_add, ← smul_eq_C_mul, map_smul,
    Rat.smul_def]
  norm_cast
  linarith

end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
