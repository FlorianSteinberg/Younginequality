Require Import Reals Qreals Psatz.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssrfun.
Require Import Rstruct mean_value_theorem concave.
From Coquelicot Require Import Coquelicot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.
Local Open Scope mf_scope.
Section Rabs_power.
  Context (p: R).
  Definition Rabs_power r p := if eqr r 0 then 0 else Rpower (Rabs r) p.
  
  Notation "`| r `|^ p" := (Rabs_power r p) (format "'`|' r '`|^' p", at level 35).
  Lemma Rapw0 q: `|0`|^q = 0.
  Proof. by rewrite /Rabs_power; case: ifP => /eqP //. Qed.

  Lemma Rapw1 q: `|1`|^q = 1.
  Proof.
    rewrite /Rabs_power.
    have ->: eqr 1 0 = false by apply /eqP.
    rewrite /Rpower Rabs_pos_eq; try lra.
    by rewrite ln_1 Rmult_0_r exp_0.
  Qed.

  Lemma Rapw_p1 r: `|r`|^1 = Rabs r.
  Proof.
    rewrite /Rabs_power.
    case: ifP => [/eqP -> | /eqP neq]; first by rewrite Rabs_R0.
    by rewrite Rpower_1//; split_Rabs; lra.
  Qed.
  
  Lemma Rapw_p0 r: `|r`|^0 = INR (~~ eqr r 0).
  Proof.
    rewrite /Rabs_power; case: ifP => // /eqP neq.
    by rewrite Rpower_O //; split_Rabs; lra.
  Qed.
  
  Lemma Rapw_pos r q: 0 <= `|r`|^q.
  Proof.
    rewrite /Rabs_power; case: ifP => [eq | ineq]; first exact/Rle_refl.
    by rewrite/Rpower; apply/Rlt_le/exp_pos.
  Qed.

  Lemma Rapw_lt r q: r <> 0 -> 0 < `|r`|^q.
  Proof.
    rewrite /Rabs_power => ineq.
    have ->: eqr r 0 = false by apply/eqP.
    exact/exp_pos.
  Qed.

  Lemma Rapw_Rabs r: `|Rabs r`|^p = `|r`|^p.
  Proof.
    rewrite /Rabs_power.
    case: ifP => [/eqP eq | /eqP ineq]; first by have:= Rnorm0_eq0 eq; case: ifP => /eqP //.
    case: ifP => [/eqP  eq| /eqP neq]; first by exfalso; apply ineq; rewrite eq Rabs_R0.
    by rewrite Rabs_Rabsolu.
  Qed.

  Lemma RapwN r: `|-r`|^p = `|r`|^p.
  Proof. by rewrite -(Rapw_Rabs r) -Rabs_Ropp Rapw_Rabs. Qed.
  
  Lemma Rapw_eq0 r q: `|r`|^q = 0 ->  r = 0.
  Proof.
    rewrite /Rabs_power; case: ifP =>/eqP // _.
    by rewrite /Rpower; have := exp_pos (q * ln (Rabs r)); lra.
  Qed.

  Lemma Rapw_inj r r' q: q <> 0 -> `|r`|^q = `|r' `|^q -> Rabs r = Rabs r'.
  Proof.
    rewrite {2}/Rabs_power => ineq.
    case: ifP => [/eqP -> zr | neq]; first by rewrite (@Rapw_eq0 r q).
    rewrite {1}/Rabs_power; case: ifP => [/eqP -> zr| /eqP neq']; last move: neq => /eqP neq.
    - by rewrite (@Rapw_eq0 r' q) // /Rabs_power neq.
    rewrite /Rpower => /exp_inv/Rmult_eq_reg_l [] // /ln_inv -> //; split_Rabs; lra.
  Qed.

  Lemma Rapw_mult x y q: `|x * y`|^q = `|x`|^q * `|y`|^q.
  Proof.
    rewrite /Rabs_power Rabs_mult.
    case: ifP => [/eqP /Rmult_integral [] ->| /eqP /Rmult_neq_0_reg [ineq ineq']].
    + by case: ifP => /eqP //; rewrite Rmult_0_l.
    - case: ifP; first by rewrite Rmult_0_l.
      by case: ifP => /eqP //; rewrite Rmult_0_r.
    case: ifP => /eqP // _; case: ifP => /eqP //_.
    by rewrite -Rpower_mult_distr //; split_Rabs; lra.
  Qed.

  Lemma Rapw_inc x y q: 0 < q -> Rabs x < Rabs y ->  `|x`|^q < `|y`|^q.
  Proof.
    rewrite /Rabs_power => pg0 ineq; case: ifP => /eqP.
    - by case: ifP => [/eqP | /eqP _ _]; [move: ineq; split_Rabs; lra | exact/exp_pos].
    case: ifP => /eqP; first by move: ineq; split_Rabs; lra.
    rewrite /Rpower => neq neq'.
    rewrite !(Rmult_comm q); apply/exp_increasing/Rmult_lt_compat_r => //.
    by apply/ln_increasing; first by split_Rabs; lra.
  Qed.
  
  Lemma Rapw_inc_le x y: 0 <= p -> Rabs x <= Rabs y ->  `|x`|^p <= `|y`|^p.
  Proof.
    case => [pg0 | <-]; last first.
    - rewrite !Rapw_p0; case: (total_order_T y 0) => [[ineq | eq] | ineq].
      + have -> /=: eqr y 0 = false by apply/eqP; lra.
        by case: (eqr x 0) => /=; lra.
      + rewrite eq => ineq; have ->: x = 0 by move: ineq; split_Rabs; lra.
        by have -> /= : eqr 0 0 = true; [apply/eqP | apply/Rle_refl].
      + have ->/=: eqr y 0 = false by apply/eqP; lra.
        by case: (eqr x 0) => /=; lra.
    case => [ineq | eq]; first exact/Rlt_le/Rapw_inc.
    by rewrite -(Rapw_Rabs x) eq Rapw_Rabs; apply /Rle_refl.
  Qed.

  Lemma Rapw_lt_inv x y: 0 < p -> `|x`|^p < `|y`|^p -> Rabs x < Rabs y.
  Proof.
    rewrite /Rabs_power => pg0.
    case: ifP => [/eqP -> | /eqP neq].
    - by case: ifP => [/eqP -> | /eqP]; split_Rabs; lra.
    case: ifP => [ | /eqP neq' /exp_lt_inv ineq].
    - by rewrite /Rpower; first by have := exp_pos (p * ln (Rabs x)); lra.
    apply/ln_lt_inv; try by split_Rabs; lra.
    exact/Rmult_lt_reg_l/ineq.
  Qed.
                                         
  Lemma Rapw_le_inv x y: 0 < p -> `|x`|^p <= `|y`|^p -> Rabs x <= Rabs y.
  Proof.
    move => pg0 [ineq | eq]; first by apply/Rlt_le/Rapw_lt_inv.
    by rewrite (Rapw_inj _ eq); lra.
  Qed.

  Lemma Rapw_inv x q: q <> 0 -> `|`|x`|^(/q)`|^q = Rabs x.
  Proof.
    rewrite/Rabs_power => neg.
    case E: (eqr x 0); move: E => /eqP.
    - by case: ifP => [_ -> | /eqP] //; rewrite Rabs_R0.
    case: ifP => /eqP.
    - rewrite /Rpower => eq; suff : 0 < 0 by lra.
      by rewrite -{2}eq; apply/exp_pos => ineq'.
    rewrite /Rpower [X in q * ln (X)]Rabs_pos_eq; last exact/Rlt_le/exp_pos.
    rewrite ln_exp -Rmult_assoc Rinv_r//Rmult_1_l => ineq ineq'.
    by rewrite exp_ln; split_Rabs; lra.
  Qed.
  
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
    - apply/continuity_pt_filterlim/(continuity_pt_ext_loc (fun x => Rpower x q)); last first.
      + exact/continuity_pt_filterlim/Rpower_cont.
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
End Rabs_power.


Notation "`| r `|^ p" := (Rabs_power r p) (format "'`|' r '`|^' p", at level 35).

Section Young's_inequality.
  Lemma Young's_inequality (a b p q: R):
      1 <= p -> 1 <= q -> /p + /q = 1 -> a * b <= `|a`|^p / p + `|b`|^q/q.
  Proof.
    move => pg1 qg1 pq.
    have posa:= Rapw_pos a p; have posp: 0 < /p by apply/Rinv_0_lt_compat; lra.
    have posb:= Rapw_pos b q; have posq: 0 < /q by apply/Rinv_0_lt_compat; lra.
    case: (total_order_T (a * b) 0) => [[lt | ]| gt].
    - apply/Rle_trans/Rplus_le_compat/Rmult_le_compat_r/Rapw_pos; try lra; last first.
      + by apply/Rmult_le_compat_r/Rapw_pos; lra.
      lra.
    - rewrite/Rdiv => ->; rewrite -(Rplus_0_r 0).
      apply/Rplus_le_compat; first by apply/Rmult_le_pos; lra.
      by apply/Rmult_le_pos; lra.
    rewrite {1}/Rabs_power; case E: (eqr a 0).
    - move: E => /eqP ->; rewrite /Rdiv !Rmult_0_l Rplus_0_l.
      apply/Rmult_le_pos/Rlt_le/Rinv_0_lt_compat; last lra.
      exact/Rapw_pos.
    rewrite /Rabs_power; case E': (eqr b 0).
    - move: E' => /eqP ->; rewrite /Rdiv !Rmult_0_l Rmult_0_r Rplus_0_r.
      apply/Rmult_le_pos/Rlt_le/Rinv_0_lt_compat; last lra.
      exact/Rlt_le/exp_pos.
    rewrite -(Rabs_pos_eq (a * b)); try lra.
    apply/ln_le_inv; first by apply/Rabs_pos_lt; lra.
    - rewrite -(Rplus_0_r 0); apply/Rplus_lt_compat/Rmult_lt_0_compat/posq/exp_pos.
      exact/Rmult_lt_0_compat/posp/exp_pos.
    apply/Rle_trans; last first.
    - case: (total_order_T (Rpower (Rabs a) p) (Rpower (Rabs b) q)) => [[ineq | eq] | ineq].
      + have:
          /p * ln (Rpower (Rabs a) p) + (1 - /p) * ln (Rpower (Rabs b) q)
          <
          ln (/p * Rpower (Rabs a) p + (1 - /p) * Rpower (Rabs b) q).
        * apply/scnc_prp; try lra.
          apply/scnc_subs/ln_scnc => x /= [ineq' _].
          exact/Rlt_le_trans/ineq'/exp_pos.
        have ->: 1 - /p = /q by lra.
        by rewrite ![/ _ * _]Rmult_comm ![_*/p + _]Rplus_comm /Rdiv => ineq'; apply/Rlt_le/ineq'.
      + rewrite eq /Rdiv; have ->: /q = 1 - /p by lra.
        have ->: Rpower (Rabs b) q * /p + Rpower (Rabs b) q * (1 - /p) = Rpower (Rabs b) q by ring.
        have ->:
             ln (Rpower (Rabs b) q) * (1 - /p) + ln (Rpower (Rabs b) q) * /p
             =
             ln (Rpower (Rabs b) q) by ring.
        exact/Rle_refl.
      have:
        /q * ln (Rpower (Rabs b) q) + (1 - /q) * ln (Rpower (Rabs a) p)
        <
        ln (/q * Rpower (Rabs b) q + (1 - /q) * Rpower (Rabs a) p).
      + apply/scnc_prp; try lra.
        by apply/scnc_subs/ln_scnc => x /= [ineq' _]; first exact/Rlt_le_trans/ineq'/exp_pos.
      have ->: 1- /q = /p by lra.
      by rewrite ![/ _ * _]Rmult_comm /Rdiv ![_*/p + _]Rplus_comm  => ineq'; apply/Rlt_le/ineq'.
    have [n0 n0']: a <> 0 /\ b <> 0 by apply/Rmult_neq_0_reg; lra.
    rewrite Rabs_mult ln_mult; try by split_Rabs; lra.
    by rewrite !ln_exp ![_ * /_]Rmult_comm -!Rmult_assoc !Rinv_l; try lra.
  Qed.
End Young's_inequality.