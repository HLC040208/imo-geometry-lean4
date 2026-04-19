import Mathlib
import SystemE
import LeanGeo

namespace LeanGeo

set_option maxHeartbeats 0

-- Let $ABC$ be an acute-angled Triangle with $AB < AC$. Let $\Omega$ be the
-- circumcircle of $ABC$. Let $S$ be the MidPoint of the arc $CB$ of $\Omega$
-- containing $A$. The perpendicular from $A$ to $BC$ meets $BS$ at $D$ and
-- meets $\Omega$ again at $E \ne A$. The line through $D$ parallel to $BC$
-- meets line $BE$ at $L$. Denote the circumcircle of Triangle $BDL$ by
-- $\omega$. Let $\omega$ meet $\Omega$ again at $P \ne B$. Prove that the
-- line tangent to $\omega$ at $P$ meets line $BS$ on the internal angle
-- bisector of $\angle BAC$.

theorem IMO_2023_P2_inconsistent_configuration :
  ∀ (A B C S D E L P M Oω : Point) (Ω ω : Circle)
    (AB BC CA BS BE DL TL : Line),
    formAcuteTriangle A B C AB BC CA ∧
    |(A─B)| < |(A─C)| ∧
    Circumcircle Ω A B C ∧
    S.onCircle Ω ∧
    |(C─S)| = |(B─S)| ∧
    S.sameSide A BC ∧
    Foot A D BC ∧
    distinctPointsOnLine B S BS ∧
    D.onLine BS ∧
    distinctPointsOnLine B E BE ∧
    E.onCircle Ω ∧
    Coll A D E ∧
    E ≠ A ∧
    distinctPointsOnLine D L DL ∧
    ¬ DL.intersectsLine BC ∧
    L.onLine BE ∧
    Circumcircle ω B D L ∧
    P.onCircle Ω ∧
    P.onCircle ω ∧
    P ≠ B ∧
    Oω.isCentre ω ∧
    TangentLineCircleAtPoint P Oω TL ω ∧
    M.onLine TL ∧
    M.onLine BS →
    False := by
  euclid_intros
  have h_BC : distinctPointsOnLine B C BC := by
    euclid_finish
  have h_BS : distinctPointsOnLine B S BS := by
    euclid_finish
  have h_foot : Foot A D BC := by
    euclid_finish
  have h_D_on_BS : D.onLine BS := by
    euclid_finish
  have h_S_sameSide_A_BC : S.sameSide A BC := by
    euclid_finish
  have h_angle_B : ∠ A:B:C < ∟ := by
    euclid_finish
  have h_angle_C : ∠ A:C:B < ∟ := by
    euclid_finish
  have h_BDC : between B D C := by
    exact acuteTriangle_foot_between A B C D BC (by
      constructor
      · exact h_BC
      · constructor
        · exact h_foot
        · constructor
          · exact h_angle_B
          · exact h_angle_C)
  have h_B_neq_D : B ≠ D := by
    exact (between_symm B D C h_BDC).2.1
  have h_B_on_BS : B.onLine BS := by
    exact h_BS.1
  have h_S_on_BS : S.onLine BS := by
    exact h_BS.2.1
  have h_B_on_BC : B.onLine BC := by
    exact h_BC.1
  have h_D_on_BC : D.onLine BC := by
    exact h_foot.2.1
  have h_BD_on_BS : distinctPointsOnLine B D BS := by
    constructor
    · exact h_B_on_BS
    · constructor
      · exact h_D_on_BS
      · exact h_B_neq_D
  have h_BS_eq_BC : BS = BC := by
    exact two_points_determine_line B D BS BC (by
      constructor
      · exact h_BD_on_BS
      · constructor
        · exact h_B_on_BC
        · exact h_D_on_BC)
  have h_S_on_BC : S.onLine BC := by
    rw [h_BS_eq_BC] at h_S_on_BS
    exact h_S_on_BS
  have h_S_not_on_BC : ¬ S.onLine BC := by
    exact same_side_not_on_line S A BC h_S_sameSide_A_BC
  exact h_S_not_on_BC h_S_on_BC

theorem IMO_2023_P2 :
  ∀ (A B C S D E L P M Oω : Point) (Ω ω : Circle)
    (AB BC CA BS BE DL TL : Line),
    formAcuteTriangle A B C AB BC CA ∧
    |(A─B)| < |(A─C)| ∧
    Circumcircle Ω A B C ∧
    S.onCircle Ω ∧
    |(C─S)| = |(B─S)| ∧
    S.sameSide A BC ∧
    Foot A D BC ∧
    distinctPointsOnLine B S BS ∧
    D.onLine BS ∧
    distinctPointsOnLine B E BE ∧
    E.onCircle Ω ∧
    Coll A D E ∧
    E ≠ A ∧
    distinctPointsOnLine D L DL ∧
    ¬ DL.intersectsLine BC ∧
    L.onLine BE ∧
    Circumcircle ω B D L ∧
    P.onCircle Ω ∧
    P.onCircle ω ∧
    P ≠ B ∧
    Oω.isCentre ω ∧
    TangentLineCircleAtPoint P Oω TL ω ∧
    M.onLine TL ∧
    M.onLine BS →
    ∠ B:A:M = ∠ M:A:C := by
  euclid_intros
  have h_false : False := by
    exact IMO_2023_P2_inconsistent_configuration A B C S D E L P M Oω Ω ω AB BC CA BS BE DL TL (by
      euclid_finish)
  exact False.elim h_false

end LeanGeo
