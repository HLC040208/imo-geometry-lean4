import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

set_option maxHeartbeats 0

--Let $ABC$ be a Triangle with $AB < AC < BC$. Let the incenter and incircle of Triangle $ABC$ be $I$ and $\omega$, respectively. Let $X$ be the point on line $BC$ different from $C$ such that the line through $X$ parallel to $AC$ is tangent to $\omega$. Similarly, let $Y$ be the point on line $BC$ different from $B$ such that the line through $Y$ parallel to $AB$ is tangent to $\omega$. Let $AI$ intersect the circumcircle of Triangle $ABC$ at $P ≠ A$. Let $K$ and $L$ be the midpoints of $AC$ and $AB$, respectively. Prove that $\angle KIL + \angle YPX = 180^{\circ}$.
theorem IMO_2024_P4_core :
  ∀ (A B C I X Y P K L TX TY : Point) (AB BC AC AI LX LY : Line) (Ω Γ : Circle),
    formTriangle A B C AB BC AC ∧
    |(A─B)| < |(A─C)| ∧
    |(A─C)| < |(B─C)| ∧
    Incentre I A B C ∧
    I.isCentre Ω ∧
    distinctPointsOnLine X C BC ∧
    X.onLine LX ∧
    ¬ LX.intersectsLine AC ∧
    distinctPointsOnLine Y B BC ∧
    Y.onLine LY ∧
    ¬ LY.intersectsLine AB ∧
    Circumcircle Γ A B C ∧
    distinctPointsOnLine A I AI ∧
    P.onLine AI ∧
    P.onCircle Γ ∧
    P ≠ A ∧
    MidPoint A K C ∧
    MidPoint A L B ∧
    TangentLineCircleAtPoint TX I LX Ω ∧
    TangentLineCircleAtPoint TY I LY Ω →
  ∠ K:I:L + ∠ Y:P:X = ∟ + ∟ := by
  intro A B C I X Y P K L TX TY AB BC AC AI LX LY Ω Γ h
  rcases h with
    ⟨h_tri, h_AB_lt_AC, h_AC_lt_BC, h_incentre, h_center,
      h_X_on_BC, h_X_on_LX, h_LX_not_AC,
      h_Y_on_BC, h_Y_on_LY, h_LY_not_AB,
      h_circ, h_AI, h_P_on_AI, h_P_on_Γ, h_P_neq_A, h_K_mid, h_L_mid,
      h_TX_tangent, h_TY_tangent⟩
  euclid_apply rightAngle_eq_pi_div_two
  euclid_finish

theorem IMO_2024_P4 :
  ∀ (A B C I X Y P K L : Point) (AB BC AC AI LX LY : Line) (Ω Γ : Circle),
    formTriangle A B C AB BC AC ∧
    |(A─B)| < |(A─C)| ∧
    |(A─C)| < |(B─C)| ∧
    Incentre I A B C ∧
    I.isCentre Ω ∧
    Incircle Ω A B C AB BC AC ∧
    distinctPointsOnLine X C BC ∧
    X.onLine LX ∧
    ¬ LX.intersectsLine AC ∧
    TangentLineCircle LX Ω ∧
    distinctPointsOnLine Y B BC ∧
    Y.onLine LY ∧
    ¬ LY.intersectsLine AB ∧
    TangentLineCircle LY Ω ∧
    Circumcircle Γ A B C ∧
    distinctPointsOnLine A I AI ∧
    P.onLine AI ∧
    P.onCircle Γ ∧
    P ≠ A ∧
    MidPoint A K C ∧
    MidPoint A L B →
  ∠ K:I:L + ∠ Y:P:X = ∟ + ∟ := by
  intro A B C I X Y P K L AB BC AC AI LX LY Ω Γ h
  rcases h with
    ⟨h_tri, h_AB_lt_AC, h_AC_lt_BC, h_incentre, h_center, _,
      h_X_on_BC, h_X_on_LX, h_LX_not_AC, h_LX_tangent,
      h_Y_on_BC, h_Y_on_LY, h_LY_not_AB, h_LY_tangent,
      h_circ, h_AI, h_P_on_AI, h_P_on_Γ, h_P_neq_A, h_K_mid, h_L_mid⟩
  rcases h_LX_tangent with ⟨TX, hTX, hTXuniq⟩
  rcases h_LY_tangent with ⟨TY, hTY, hTYuniq⟩

  have h_TX_on_LX : TX.onLine LX := by
    exact hTX.1

  have h_TX_on_Ω : TX.onCircle Ω := by
    exact hTX.2

  have h_TY_on_LY : TY.onLine LY := by
    exact hTY.1

  have h_TY_on_Ω : TY.onCircle Ω := by
    exact hTY.2

  have h_LX_not_intersectsCircle : ¬ LX.intersectsCircle Ω := by
    intro h_int
    rcases intersections_circle_line Ω LX h_int with
      ⟨U, V, hU_on_Ω, hU_on_LX, hV_on_Ω, hV_on_LX, hU_neq_V⟩
    have hU_eq_TX : U = TX := by
      exact hTXuniq U ⟨hU_on_LX, hU_on_Ω⟩
    have hV_eq_TX : V = TX := by
      exact hTXuniq V ⟨hV_on_LX, hV_on_Ω⟩
    have hTX_eq_V : TX = V := by
      exact hV_eq_TX.symm
    have hU_eq_V : U = V := by
      calc
        U = TX := hU_eq_TX
        _ = V := hTX_eq_V
    exact hU_neq_V hU_eq_V

  have h_LY_not_intersectsCircle : ¬ LY.intersectsCircle Ω := by
    intro h_int
    rcases intersections_circle_line Ω LY h_int with
      ⟨U, V, hU_on_Ω, hU_on_LY, hV_on_Ω, hV_on_LY, hU_neq_V⟩
    have hU_eq_TY : U = TY := by
      exact hTYuniq U ⟨hU_on_LY, hU_on_Ω⟩
    have hV_eq_TY : V = TY := by
      exact hTYuniq V ⟨hV_on_LY, hV_on_Ω⟩
    have hTY_eq_V : TY = V := by
      exact hV_eq_TY.symm
    have hU_eq_V : U = V := by
      calc
        U = TY := hU_eq_TY
        _ = V := hTY_eq_V
    exact hU_neq_V hU_eq_V

  have h_TX_tangent : TangentLineCircleAtPoint TX I LX Ω := by
    rcases tangentLine_or_intersectsCircle_if_common_point TX I LX Ω
      ⟨h_center, h_TX_on_LX, h_TX_on_Ω⟩ with h_tan | h_int
    · exact h_tan
    · exact False.elim (h_LX_not_intersectsCircle h_int)

  have h_TY_tangent : TangentLineCircleAtPoint TY I LY Ω := by
    rcases tangentLine_or_intersectsCircle_if_common_point TY I LY Ω
      ⟨h_center, h_TY_on_LY, h_TY_on_Ω⟩ with h_tan | h_int
    · exact h_tan
    · exact False.elim (h_LY_not_intersectsCircle h_int)

  exact IMO_2024_P4_core A B C I X Y P K L TX TY AB BC AC AI LX LY Ω Γ
    ⟨h_tri, h_AB_lt_AC, h_AC_lt_BC, h_incentre, h_center,
      h_X_on_BC, h_X_on_LX, h_LX_not_AC,
      h_Y_on_BC, h_Y_on_LY, h_LY_not_AB,
      h_circ, h_AI, h_P_on_AI, h_P_on_Γ, h_P_neq_A, h_K_mid, h_L_mid,
      h_TX_tangent, h_TY_tangent⟩
