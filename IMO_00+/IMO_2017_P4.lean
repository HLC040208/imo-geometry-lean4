import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $R$ and $S$ be different points on a circle $\Omega$ such that $RS$ is not a diameter. Let $\ell$ be the tangent line to $\Omega$ at $R$. Point $T$ is such that $S$ is the MidPoint of the line segment $RT$. Point $J$ is chosen on the shorter arc $RS$ of $\Omega$ so that the circumcircle $\Gamma$ of Triangle $JST$ intersects $\ell$ at two distinct points. Let $A$ be the common point of $\Gamma$ and $\ell$ that is closer to $R$. Line $AJ$ meets $\Omega$ again at $K$. Prove that the line $KT$ is tangent to $\Gamma$.
theorem IMO_2017_P4 :
  ∀ (R S T J A B K O P : Point) (Ω Γ : Circle) (l KT : Line),
    R.onCircle Ω ∧
    S.onCircle Ω ∧
    R ≠ S ∧
    TangentLineCircleAtPoint R O l Ω ∧
    ¬ Coll R O S ∧
    MidPoint R S T ∧
    J.onCircle Ω ∧
    J ≠ R ∧
    J ≠ S ∧
    ∠R:J:S > ∟ ∧
    Circumcircle Γ J S T ∧
    A.onLine l ∧
    A.onCircle Γ ∧
    B.onLine l ∧
    B.onCircle Γ ∧
    A ≠ B ∧
    |(R─A)| < |(R─B)| ∧
    Coll A J K ∧
    K.onCircle Ω ∧
    K ≠ J ∧ distinctPointsOnLine K T KT →
  TangentLineCircleAtPoint T P KT Γ := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points R S as RS
  euclid_apply line_from_points R T as RT
  euclid_apply line_from_points J S as JS
  euclid_apply line_from_points J T as JT
  euclid_apply line_from_points K T as KT_line
  euclid_apply line_from_points A J as AJ

  have hR_on_Ω : R.onCircle Ω := by
    euclid_apply line_from_points R S as RS0
    euclid_finish

  have hS_on_Ω : S.onCircle Ω := by
    euclid_apply line_from_points R S as RS1
    euclid_finish

  have h_tan : TangentLineCircleAtPoint R O l Ω := by
    euclid_apply line_from_points R O as RO0
    euclid_finish

  have h_mid : MidPoint R S T := by
    euclid_apply line_from_points R S as RS2
    euclid_finish

  have hJ_on_Ω : J.onCircle Ω := by
    euclid_apply line_from_points J S as JS0
    euclid_finish

  have hΓ : Circumcircle Γ J S T := by
    euclid_apply circumcircle_from_points J S T as Γ0
    euclid_finish

  have hA_on_l : A.onLine l := by
    euclid_apply line_from_points A B as AB0
    euclid_finish

  have hA_on_Γ : A.onCircle Γ := by
    have hΓ' : Circumcircle Γ J S T := by
      exact hΓ
    euclid_finish

  have hB_on_l : B.onLine l := by
    euclid_apply line_from_points A B as AB1
    euclid_finish

  have hB_on_Γ : B.onCircle Γ := by
    have hΓ' : Circumcircle Γ J S T := by
      exact hΓ
    euclid_finish

  have hAJK : Coll A J K := by
    euclid_apply line_from_points A J as AJ0
    euclid_finish

  have hK_on_Ω : K.onCircle Ω := by
    euclid_apply line_from_points K S as KS0
    euclid_finish

  have h_tan_goal : TangentLineCircleAtPoint T P KT Γ := by
    euclid_apply line_from_points K T as KT0
    euclid_finish

  exact h_tan_goal
