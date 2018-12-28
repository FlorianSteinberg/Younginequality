Require Import Reals Qreals Psatz.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssrfun.
From Coquelicot Require Import Coquelicot.
Require Import Rstruct youngsinequality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.
Section Rabs_power_continuous.

    Lemma Rpower_cont q x: 0 < x -> continuous (Rpower^~ q) x.
    Proof.
      move => ineq.
      apply/(continuous_comp (fun x => q * ln x) exp).
      - apply/continuous_mult; first exact/continuous_const.
        apply/continuity_pt_filterlim/derivable_continuous_pt.
        exists (/x).
        exact/derivable_pt_lim_ln.
      exact/continuity_pt_filterlim/derivable_continuous_pt/derivable_pt_exp.
    Qed.

    Lemma Rapw_cont q x: 0 < q -> continuous (fun x => Rabs_power x q) x.
    Proof.
      move => gt.
      case: (total_order_T 0 x) => [[ineq | <-] | ineq].
      - + apply/continuity_pt_filterlim/(continuity_pt_ext_loc (fun x => Rpower x q)); last first.
          * exact/continuity_pt_filterlim/Rpower_cont.
          have pos: 0 < x /2 by lra.
          exists (mkposreal _ pos) => y /=.
          rewrite /ball/=/AbsRing_ball/=/abs/=/minus/=/plus/=/opp/=/Rabs_power => ineq'.
          have ->: eqr y 0 = false by apply/eqP; split_Rabs; lra.
          by rewrite Rabs_pos_eq//; split_Rabs;lra.
      - move => A [[eps ineq]].
        rewrite Rapw0 => bll.
        have pos: 0 < `|eps`|^(/q) by apply/Rapw_lt; lra.
        exists (mkposreal _ pos) => y bll'; apply/bll; move: bll'.
        rewrite /ball /=/AbsRing_ball/abs/=!minus_zero_r => bll'.
        rewrite Rabs_pos_eq; last exact/Rapw_pos.
        apply/Rlt_le_trans.
        + apply/Rapw_inc => //.
          rewrite -(Rabs_pos_eq (`|eps`|^/q)) in bll'; last exact/Rapw_pos.
          exact/bll'.
        rewrite Rapw_inv; try lra.
        by rewrite Rabs_pos_eq; try lra.
      apply/continuity_pt_filterlim.
      apply/(continuity_pt_ext_loc (fun x => Rpower (-x) q)).
      - have pos: 0 < (- x) /2 by lra.
        exists (mkposreal _ pos) => y /=.
        rewrite /ball/=/AbsRing_ball/=/abs/=/minus/=/plus/=/opp/=/Rabs_power => ineq'.
        have ->: eqr y 0 = false by apply/eqP; split_Rabs; lra.
        rewrite -{2}(Ropp_involutive y) Rabs_Ropp.
        by rewrite Rabs_pos_eq//; split_Rabs;lra.
      apply/continuity_pt_filterlim/(continuous_comp Ropp (fun x => Rpower x q)).
      - exact/continuous_opp.
      by apply/Rpower_cont; lra.
    Qed.
End Rabs_power_continuous.