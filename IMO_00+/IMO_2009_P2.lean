import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--Let $ABC$ be a Triangle with circumcentre $O$. The points $P$ and $Q$ are interior points of the sides $CA$ and $AB$ respectively. Let $K,L$ and $M$ be the midpoints of the segments $BP,CQ$ and $PQ$. respectively, and let $\Gamma$ be the circle passing through $K,L$ and $M$. Suppose that the line $PQ$ is tangent to the circle $\Gamma$. Prove that $OP = OQ$.
theorem IMO_2009_P2 :
  ∀ (A B C O P Q K L M OΓ : Point) (AB BC CA PQ : Line) (Γ : Circle),
    formTriangle A B C AB BC CA ∧
    Circumcentre O A B C ∧ between C P A ∧ between A Q B ∧
    MidPoint B K P ∧
    MidPoint C L Q ∧
    MidPoint P M Q ∧
    Circumcircle Γ K L M ∧
    TangentLineCircleAtPoint M OΓ PQ Γ →
    |(O─P)| = |(O─Q)| := by
  euclid_intros
  euclid_apply line_from_points M K as MK
  euclid_apply line_from_points K L as KL
  euclid_apply line_from_points M L as ML
  euclid_apply circle_from_points O A as Ω
  euclid_apply line_from_points A Q as AQ
  euclid_apply line_from_points A P as AP
  euclid_apply line_from_points Q P as QP
  euclid_apply line_from_points B Q as BQ
  euclid_apply line_from_points C P as CP

  have h_tangent_ratio : |(A─Q)| * |(M─K)| = |(A─P)| * |(M─L)| := by
    have h_angle1 : ∠ K:M:Q = ∠ K:L:M := by
      euclid_apply AlternateSegmentTheorem M K L Q OΓ Γ MK KL ML PQ
      euclid_finish
    have h_angle2 : ∠ L:M:P = ∠ L:K:M := by
      euclid_apply AlternateSegmentTheorem M L K P OΓ Γ ML KL MK PQ
      euclid_finish
    have h_tri_KLM : Triangle K L M := by
      euclid_finish
    have h_tri_AQP : Triangle A Q P := by
      euclid_finish
    euclid_apply LawOfSines K L M
    euclid_apply LawOfSines A Q P
    euclid_finish

  have h_mid1 : |(B─Q)| = |(K─M)| * 2 := by
    have h_mid_BKP : MidPoint B K P := by
      euclid_finish
    have h_mid_PMQ : MidPoint P M Q := by
      euclid_finish
    have h_tri_PBQ : Triangle P B Q := by
      euclid_finish
    euclid_apply triangleMidsegment_half_len P B Q K M
    euclid_finish

  have h_mid2 : |(C─P)| = |(L─M)| * 2 := by
    have h_mid_CLQ : MidPoint C L Q := by
      euclid_finish
    have h_mid_PMQ : MidPoint P M Q := by
      euclid_finish
    have h_tri_QCP : Triangle Q C P := by
      euclid_finish
    euclid_apply triangleMidsegment_half_len Q C P L M
    euclid_finish

  have h_prod : |(A─Q)| * |(Q─B)| = |(A─P)| * |(P─C)| := by
    have hMK : |(M─K)| = |(K─M)| := by euclid_finish
    have hML : |(M─L)| = |(L─M)| := by euclid_finish
    have hBQ : |(B─Q)| = |(Q─B)| := by euclid_finish
    have hCP : |(C─P)| = |(P─C)| := by euclid_finish
    rw [hMK, hML] at h_tangent_ratio
    rw [hBQ, hCP]
    nlinarith

  have h_powP : |(P─C)| * |(P─A)| + |(P─O)| * |(P─O)| = |(O─C)| * |(O─C)| := by
    have hP_between : between C P A := by
      euclid_finish
    have hO_center : O.isCentre Ω := by
      euclid_finish
    have hC_on_Ω : C.onCircle Ω := by
      euclid_finish
    have hA_on_Ω : A.onCircle Ω := by
      euclid_finish
    euclid_apply pow_of_point_in_circle P O C A Ω
    euclid_finish

  have h_powQ : |(Q─A)| * |(Q─B)| + |(Q─O)| * |(Q─O)| = |(O─A)| * |(O─A)| := by
    have hQ_between : between A Q B := by
      euclid_finish
    have hO_center : O.isCentre Ω := by
      euclid_finish
    have hA_on_Ω : A.onCircle Ω := by
      euclid_finish
    have hB_on_Ω : B.onCircle Ω := by
      euclid_finish
    euclid_apply pow_of_point_in_circle Q O A B Ω
    euclid_finish

  have hOCA : |(O─C)| = |(O─A)| := by
    have h_circ : Circumcentre O A B C := by
      euclid_finish
    euclid_finish
  have hPA : |(P─A)| = |(A─P)| := by
    euclid_finish
  have hQA : |(Q─A)| = |(A─Q)| := by
    euclid_finish
  have hQO : |(Q─O)| = |(O─Q)| := by
    euclid_finish
  have hPO : |(P─O)| = |(O─P)| := by
    euclid_finish
  rw [hPA, hPO, hOCA] at h_powP
  rw [hQA, hQO] at h_powQ
  nlinarith
