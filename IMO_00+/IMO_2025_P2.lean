import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

theorem IMO_2025_P2 :
  ∀ (M N A B C D P E F O H hp hm hn : Point) (MN AP L PM PN : Line) (Ω Γ BEF : Circle),
  M.isCentre Ω ∧ N.isCentre Γ ∧ (rad Ω) < (rad Γ) ∧ CirclesIntersectAtTwoPoints Ω Γ A B ∧
  distinctPointsOnLine M N MN ∧ C.onLine MN ∧ C.onCircle Ω ∧ D.onLine MN ∧ D.onCircle Γ ∧ between C M N ∧ between M N D ∧
  Circumcentre P A C D ∧ distinctPointsOnLine A P AP ∧ LineIntersectsCircleAtTwoPoints A E AP Ω ∧ LineIntersectsCircleAtTwoPoints A F AP Γ ∧
  Orthocentre H P M N hp hm hn PM MN PN ∧ H.onLine L ∧ ¬ L.intersectsLine AP ∧ Circumcircle BEF B E F ∧ O.isCentre BEF
  → ∃ (Q : Point), TangentLineCircleAtPoint Q O L BEF := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two

  have hM_center : M.isCentre Ω := by
    euclid_finish

  have hN_center : N.isCentre Γ := by
    euclid_finish

  have h_inter : CirclesIntersectAtTwoPoints Ω Γ A B := by
    euclid_finish

  have h_MN : distinctPointsOnLine M N MN := by
    euclid_finish

  have h_circumcentre : Circumcentre P A C D := by
    euclid_finish

  have h_AP : distinctPointsOnLine A P AP := by
    euclid_finish

  have h_E_secant : LineIntersectsCircleAtTwoPoints A E AP Ω := by
    euclid_finish

  have h_F_secant : LineIntersectsCircleAtTwoPoints A F AP Γ := by
    euclid_finish

  have h_orth : Orthocentre H P M N hp hm hn PM MN PN := by
    euclid_finish

  have h_H_on_L : H.onLine L := by
    euclid_finish

  have h_L_not_AP : ¬ L.intersectsLine AP := by
    euclid_finish

  have h_BEF : Circumcircle BEF B E F := by
    euclid_finish

  have hO_center : O.isCentre BEF := by
    euclid_finish

  have h_H_on_BEF : H.onCircle BEF := by
    euclid_finish

  have h_H_tan : TangentLineCircleAtPoint H O L BEF := by
    have h_H_on_BEF' : H.onCircle BEF := by
      exact h_H_on_BEF
    have h_H_on_L' : H.onLine L := by
      exact h_H_on_L
    have hO_center' : O.isCentre BEF := by
      exact hO_center
    euclid_finish

  have h_goal : ∃ (Q : Point), TangentLineCircleAtPoint Q O L BEF := by
    exact ⟨H, h_H_tan⟩

  exact h_goal

end LeanGeo
