import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--In Triangle $ABC$ the bisector of angle $BCA$ intersects the circumcircle again at $R$, the perpendicular bisector of $BC$ at $P$, and the perpendicular bisector of $AC$ at $Q$. The MidPoint of $BC$ is $K$ and the MidPoint of $AC$ is $L$. Prove that the triangles $RPK$ and $RQL$ have the same area.
theorem IMO_2007_P4 :
  ∀ (A B C R P Q K L : Point) (AB BC CA L1 L2 : Line) (Ω : Circle),
    formTriangle A B C AB BC CA ∧
    Circumcircle Ω A B C ∧
    R.onCircle Ω ∧
    R ≠ C ∧
    ∠ B:C:R = ∠ R:C:A ∧
    PerpBisector B C L1 ∧ P.onLine L1 ∧ ∠ B:C:P = ∠ P:C:A ∧
    PerpBisector A C L2 ∧ Q.onLine L2 ∧ ∠ B:C:Q = ∠ Q:C:A ∧
    MidPoint B K C ∧ MidPoint A L C
    → (△ R:P:K).area = (△ R:Q:L).area := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points R K as RK
  euclid_apply line_from_points R L as RL
  euclid_apply line_from_points P K as PK
  euclid_apply line_from_points Q L as QL

  have h_RA_RB : |(R─A)| = |(R─B)| := by
    euclid_apply chord_equal_from_angle R A B C Ω
    euclid_finish

  have hP_eq_BC : |(P─B)| = |(P─C)| := by
    euclid_apply perpBisector_imp_eq_dist B C L1
    euclid_finish

  have hQ_eq_AC : |(Q─A)| = |(Q─C)| := by
    euclid_apply perpBisector_imp_eq_dist A C L2
    euclid_finish

  have hRK_eq_RB : |(R─K)| = |(R─B)| := by
    have h_mid_BKC : MidPoint B K C := by
      euclid_finish
    have h_right_RBC : RightTriangle R B C := by
      euclid_finish
    euclid_apply rightTriangle_midLine_eq_half_hypotenuse R B C K
    euclid_finish

  have hRL_eq_RA : |(R─L)| = |(R─A)| := by
    have h_mid_ALC : MidPoint A L C := by
      euclid_finish
    have h_right_RAC : RightTriangle R A C := by
      euclid_finish
    euclid_apply rightTriangle_midLine_eq_half_hypotenuse R A C L
    euclid_finish

  have hRK_eq_RL : |(R─K)| = |(R─L)| := by
    rw [hRK_eq_RB, hRL_eq_RA, h_RA_RB]

  have hP_perp : ∠ P:K:C = 2 * ∟ := by
    have h_mid_BKC : MidPoint B K C := by
      euclid_finish
    euclid_finish

  have hQ_perp : ∠ Q:L:C = 2 * ∟ := by
    have h_mid_ALC : MidPoint A L C := by
      euclid_finish
    euclid_finish

  have h_area_RPK : (△ R:P:K).area = (1 / 2) * |(R─K)| * |(P─K)| * sin (∠ R:K:P) := by
    euclid_apply area_sine_formula R P K
    euclid_finish

  have h_area_RQL : (△ R:Q:L).area = (1 / 2) * |(R─L)| * |(Q─L)| * sin (∠ R:L:Q) := by
    euclid_apply area_sine_formula R Q L
    euclid_finish

  have h_area_eq : (△ R:P:K).area = (△ R:Q:L).area := by
    have h_metric_match : |(R─K)| * |(P─K)| = |(R─L)| * |(Q─L)| := by
      rw [hRK_eq_RL]
      euclid_finish
    euclid_finish

  exact h_area_eq
