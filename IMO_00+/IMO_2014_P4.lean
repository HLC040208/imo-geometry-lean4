import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $P$ and $Q$ be on segment $BC$ of an acute Triangle $ABC$ such that $\angle PAB=\angle BCA$ and $\angle CAQ=\angle ABC$. Let $M$ and $N$ be the points on $AP$ and $AQ$, respectively, such that $P$ is the MidPoint of $AM$ and $Q$ is the MidPoint of $AN$. Prove that the intersection of $BM$ and $CN$ is on the circumference of Triangle $ABC$.
theorem IMO_2014_P4 :
  ∀ (A B C P Q M N X : Point) (AB BC CA BM CN : Line) (Ω : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    between B P C ∧ between B Q C ∧
    ∠ P:A:B = ∠ B:C:A ∧ ∠ C:A:Q = ∠ A:B:C ∧
    MidPoint A P M ∧ MidPoint A Q N ∧
    distinctPointsOnLine B M BM ∧ distinctPointsOnLine C N CN ∧
    TwoLinesIntersectAtPoint BM CN X ∧
    Circumcircle Ω A B C
    → X.onCircle Ω := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points A P as AP
  euclid_apply line_from_points A Q as AQ
  euclid_apply line_from_points B M as BM_line
  euclid_apply line_from_points C N as CN_line
  euclid_apply line_from_points B C as BC_line

  have h_tri : formAcuteTriangle A B C AB BC CA := by
    euclid_apply line_from_points A B as AB0
    euclid_finish

  have hP_between : between B P C := by
    euclid_apply line_from_points B C as BC0
    euclid_finish

  have hQ_between : between B Q C := by
    euclid_apply line_from_points B C as BC1
    euclid_finish

  have h_angle1 : ∠ P:A:B = ∠ B:C:A := by
    euclid_apply line_from_points A P as AP0
    euclid_finish

  have h_angle2 : ∠ C:A:Q = ∠ A:B:C := by
    euclid_apply line_from_points A Q as AQ0
    euclid_finish

  have h_midP : MidPoint A P M := by
    euclid_apply line_from_points A P as AP1
    euclid_finish

  have h_midQ : MidPoint A Q N := by
    euclid_apply line_from_points A Q as AQ1
    euclid_finish

  have hP_on_AP : P.onLine AP := by
    euclid_finish

  have hQ_on_AQ : Q.onLine AQ := by
    euclid_finish

  have hM_on_BM : M.onLine BM := by
    euclid_finish

  have hN_on_CN : N.onLine CN := by
    euclid_finish

  have hX_inter : TwoLinesIntersectAtPoint BM CN X := by
    euclid_apply line_from_points B M as BM0
    euclid_finish

  have hX_on_BM : X.onLine BM := by
    have h1 : TwoLinesIntersectAtPoint BM CN X := by
      exact hX_inter
    euclid_finish

  have hX_on_CN : X.onLine CN := by
    have h1 : TwoLinesIntersectAtPoint BM CN X := by
      exact hX_inter
    euclid_finish

  have hΩ : Circumcircle Ω A B C := by
    euclid_apply circumcircle_from_points A B C as Ω0
    euclid_finish

  have hX_on_Ω : X.onCircle Ω := by
    have hΩ' : Circumcircle Ω A B C := by
      exact hΩ
    have hX_on_BM' : X.onLine BM := by
      exact hX_on_BM
    have hX_on_CN' : X.onLine CN := by
      exact hX_on_CN
    euclid_finish

  exact hX_on_Ω
