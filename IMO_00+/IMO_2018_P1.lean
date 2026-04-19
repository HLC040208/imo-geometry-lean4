import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $\Gamma$ be the circumcircle of acute Triangle $ABC$. Points $D$ and $E$ are on segments $AB$ and $AC$ respectively such that $AD = AE$. The perpendicular bisectors of $BD$ and $CE$ intersect minor arcs $AB$ and $AC$ of $\Gamma$ at points $F$ and $G$ respectively. Prove that lines $DE$ and $FG$ are either parallel or they are the same line.
theorem IMO_2018_P1 :
  ∀ (A B C D E F G : Point)
    (AB BC CA L1 L2 DE FG : Line)
    (Γ : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    Circumcircle Γ A B C ∧
    between A D B ∧
    between A E C ∧
    |(A─D)| = |(A─E)| ∧
    PerpBisector B D L1 ∧
    F.onCircle Γ ∧
    F.onLine L1 ∧
    F.opposingSides C AB ∧
    PerpBisector C E L2 ∧
    G.onCircle Γ ∧
    G.onLine L2 ∧
    G.opposingSides B AC ∧
    distinctPointsOnLine D E DE ∧
    distinctPointsOnLine F G FG →
    ¬(DE.intersectsLine FG) := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points A B as AB_line
  euclid_apply line_from_points A C as AC_line
  euclid_apply line_from_points D E as DE_line
  euclid_apply line_from_points F G as FG_line

  have h_tri : formAcuteTriangle A B C AB BC CA := by
    euclid_apply line_from_points A B as AB0
    euclid_finish

  have hΓ : Circumcircle Γ A B C := by
    euclid_apply circumcircle_from_points A B C as Γ0
    euclid_finish

  have h_between_D : between A D B := by
    euclid_apply line_from_points A B as AB1
    euclid_finish

  have h_between_E : between A E C := by
    euclid_apply line_from_points A C as AC0
    euclid_finish

  have h_AD_eq_AE : |(A─D)| = |(A─E)| := by
    euclid_apply line_from_points A D as AD0
    euclid_finish

  have h_perp_BD : PerpBisector B D L1 := by
    euclid_apply line_from_points B D as BD0
    euclid_finish

  have h_perp_CE : PerpBisector C E L2 := by
    euclid_apply line_from_points C E as CE0
    euclid_finish

  have hF_on_Γ : F.onCircle Γ := by
    have hΓ' : Circumcircle Γ A B C := by
      exact hΓ
    euclid_finish

  have hG_on_Γ : G.onCircle Γ := by
    have hΓ' : Circumcircle Γ A B C := by
      exact hΓ
    euclid_finish

  have hF_on_L1 : F.onLine L1 := by
    euclid_apply line_from_points B D as BD1
    euclid_finish

  have hG_on_L2 : G.onLine L2 := by
    euclid_apply line_from_points C E as CE1
    euclid_finish

  have h_no_inter : ¬(DE.intersectsLine FG) := by
    euclid_apply line_from_points D E as DE0
    euclid_finish

  exact h_no_inter
