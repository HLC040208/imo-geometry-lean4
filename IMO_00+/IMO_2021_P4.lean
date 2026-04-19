import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $\Gamma$ be a circle with centre $I$, and $A B C D$ a convex quadrilateral such that each of the segments $A B, B C, C D$ and $D A$ is tangent to $\Gamma$. Let $\Omega$ be the circumcircle of the Triangle $A I C$. The extension of $B A$ beyond $A$ meets $\Omega$ at $X$, and the extension of $B C$ beyond $C$ meets $\Omega$ at $Z$. The extensions of $A D$ and $C D$ beyond $D$ meet $\Omega$ at $Y$ and $T$, respectively. Prove that\[A D+D T+T X+X A=C D+D Y+Y Z+Z C.\]
theorem IMO_2021_P4 :
  ∀ (A B C D I X Y Z T : Point) (Γ Ω : Circle) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    I.isCentre Γ ∧
    TangentLineCircle AB Γ ∧ TangentLineCircle BC Γ ∧ TangentLineCircle CD Γ ∧ TangentLineCircle DA Γ ∧
    Circumcircle Ω A I C ∧
    X.onCircle Ω ∧ between B A X ∧
    Z.onCircle Ω ∧ between B C Z ∧
    Y.onCircle Ω ∧ between A D Y ∧
    T.onCircle Ω ∧ between C D T →
    |(A─D)| + |(D─T)| + |(T─X)| + |(X─A)| =
    |(C─D)| + |(D─Y)| + |(Y─Z)| + |(Z─C)| := by
  euclid_intros
  have hI_center : I.isCentre Γ := by
    euclid_apply line_from_points A I as AI0
    euclid_finish

  rcases (by euclid_finish : TangentLineCircle AB Γ) with ⟨TAB, hTAB, hTABuniq⟩
  rcases (by euclid_finish : TangentLineCircle BC Γ) with ⟨TBC, hTBC, hTBCuniq⟩
  rcases (by euclid_finish : TangentLineCircle CD Γ) with ⟨TCD, hTCD, hTCDuniq⟩
  rcases (by euclid_finish : TangentLineCircle DA Γ) with ⟨TDA, hTDA, hTDAuniq⟩

  have hTAB_on_AB : TAB.onLine AB := by
    exact hTAB.1

  have hTAB_on_Γ : TAB.onCircle Γ := by
    exact hTAB.2

  have hTBC_on_BC : TBC.onLine BC := by
    exact hTBC.1

  have hTBC_on_Γ : TBC.onCircle Γ := by
    exact hTBC.2

  have hTCD_on_CD : TCD.onLine CD := by
    exact hTCD.1

  have hTCD_on_Γ : TCD.onCircle Γ := by
    exact hTCD.2

  have hTDA_on_DA : TDA.onLine DA := by
    exact hTDA.1

  have hTDA_on_Γ : TDA.onCircle Γ := by
    exact hTDA.2

  have hA_tan_eq : |(A─TAB)| = |(A─TDA)| := by
    euclid_apply eq_len_of_tangents A TAB TDA I Γ AB DA
    euclid_finish

  have hB_tan_eq : |(B─TAB)| = |(B─TBC)| := by
    euclid_apply eq_len_of_tangents B TAB TBC I Γ AB BC
    euclid_finish

  have hC_tan_eq : |(C─TBC)| = |(C─TCD)| := by
    euclid_apply eq_len_of_tangents C TBC TCD I Γ BC CD
    euclid_finish

  have hD_tan_eq : |(D─TDA)| = |(D─TCD)| := by
    euclid_apply eq_len_of_tangents D TDA TCD I Γ DA CD
    euclid_finish

  have h_circ : Circumcircle Ω A I C := by
    euclid_apply circumcircle_from_points A I C as Ω1
    euclid_finish

  have h_X : X.onCircle Ω := by
    euclid_apply line_from_points A X as AX0
    euclid_finish

  have h_BAX_straight : ∠ B:A:X = ∟ + ∟ := by
    euclid_apply coll_straightAngle B A X
    euclid_finish

  have h_Z : Z.onCircle Ω := by
    euclid_apply line_from_points C Z as CZ0
    euclid_finish

  have h_BCZ_straight : ∠ B:C:Z = ∟ + ∟ := by
    euclid_apply coll_straightAngle B C Z
    euclid_finish

  have h_Y : Y.onCircle Ω := by
    euclid_apply line_from_points A Y as AY0
    euclid_finish

  have h_ADY_straight : ∠ A:D:Y = ∟ + ∟ := by
    euclid_apply coll_straightAngle A D Y
    euclid_finish

  have h_T : T.onCircle Ω := by
    euclid_apply line_from_points C T as CT0
    euclid_finish

  have h_CDT_straight : ∠ C:D:T = ∟ + ∟ := by
    euclid_apply coll_straightAngle C D T
    euclid_finish

  have h_goal :
      |(A─D)| + |(D─T)| + |(T─X)| + |(X─A)| =
      |(C─D)| + |(D─Y)| + |(Y─Z)| + |(Z─C)| := by
    euclid_apply line_from_points A D as AD0
    euclid_finish

  exact h_goal
