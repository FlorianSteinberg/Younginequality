Require Import Reals Qreals Psatz.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssrfun.
Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.
Section Rabs_power.
  Context (p: R).
  Definition Rabs_power r p := if eqr r 0 then 0 else Rpower (Rabs r) p.
  
  Notation "`| r `|^ p" := (Rabs_power r p) (format "'`|' r '`|^' p", at level 35).
  Lemma Rapw0 q: `|0`|^q = 0.
  Proof. by rewrite /Rabs_power; case: ifP => /eqP //. Qed.
  
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

End Rabs_power.
Notation "`| r `|^ p" := (Rabs_power r p) (format "'`|' r '`|^' p", at level 35).

Section ln_strictly_concave.   
  Definition strictly_concave_on A f :=
    forall x y z, A x -> A y -> A z -> x < y < z ->
                    (f z - f y)/(z - y) < (f y - f x)/ (y - x).

  Lemma scnc_spec f a b: a < b -> strictly_concave_on (fun x => a <= x <= b) f ->
                         forall r, 0 < r < 1 -> r * f b + (1 - r) * f a < f (r * b + (1 - r) * a).
  Proof.
    move => alb conc r ineq.
    suff: (1 - r) * (f (r * b + (1 - r) * a) - f a) > r * (f b - f ( r * b + (1 - r) * a)) by lra.
    apply/Rlt_gt.
    apply/(Rmult_lt_reg_l (/(1-r))); first by apply/Rinv_0_lt_compat; lra.
    rewrite -!Rmult_assoc Rinv_l; try lra; rewrite Rmult_1_l.
    rewrite (Rmult_comm _ r).
    apply/(Rmult_lt_reg_l (/r)); first by apply/Rinv_0_lt_compat; lra.
    rewrite -!Rmult_assoc Rinv_l; try lra; rewrite Rmult_1_l.
    apply/(Rmult_lt_reg_r (/(b - a))); first by apply/Rinv_0_lt_compat; lra.
    have /=:= conc a (r * b + (1 - r) * a) b.
    have ->: b - ( r * b + (1 - r) * a) = (1 - r)* (b - a) by ring.
    have ->: r * b + (1 - r)* a - a = r * (b - a) by ring.
    rewrite !/Rdiv !Rinv_mult_distr; try lra.
    suff ineq': a < r * b + (1 - r) * a < b by lra.
    split; first by apply/Rle_lt_trans/Rplus_lt_le_compat/Rle_refl/Rmult_lt_compat_l/alb; lra.
    apply/Rlt_le_trans.
    - by apply/Rplus_le_lt_compat/Rmult_lt_compat_l/alb; try lra; apply/Rle_refl.
    lra.  
  Qed.

  Lemma ln_derivable_pt x: 0 < x -> derivable_pt ln x.
  Proof.
    rewrite /derivable_pt/derivable_pt_abs => ineq.
    by exists (/x); apply/derivable_pt_lim_ln.
  Qed.

  Lemma derivable_pt_lim_id x: derivable_pt_lim id x 1.
  Proof.
    move => eps eg0; exists (mkposreal _ eg0) => h neq /= ineq.
    have ->: (x + h - x) / h = 1 by field.
    by split_Rabs; lra.
  Qed.

  Lemma derive_pt_unique f x P Q: derive_pt f x P = derive_pt f x Q.
  Proof. by apply/derive_pt_eq; move: Q => [f'x lim]. Qed.

  Lemma ln_scnc: strictly_concave_on (fun x => 0 < x) ln.
  Proof.
    move => x y z /= xg0 yg0 zg0 [] ygx zgy.
    have diff1: forall z, x < z < y -> derivable_pt id z.
    - by move => c ineq; exists 1; apply derivable_pt_lim_id.
    have diff2: forall z, x < z < y -> derivable_pt ln z.
    - by move => c ineq; apply/ln_derivable_pt; lra.
    have [c ineq | c ineq | c [ineq /=]]:= MVT id ln x y diff1 diff2 ygx.
    - by apply/derivable_continuous_pt; exists 1; apply/derivable_pt_lim_id.
    - by apply/derivable_continuous_pt/ln_derivable_pt; lra.
    have ->: derive_pt id c (diff1 c ineq) = 1.
    - by rewrite -(derive_pt_id c); apply/derive_pt_unique.
    rewrite Rmult_1_r => ->.
    have ->: derive_pt ln c (diff2 c ineq) = /c.
    - by apply/derive_pt_eq/derivable_pt_lim_ln; lra.
    rewrite Rmult_comm /Rdiv Rmult_assoc Rinv_r; try lra; rewrite Rmult_1_r.
    have diff3: forall x, y < x < z -> derivable_pt id x.
    - by move => d ineq'; exists 1; apply derivable_pt_lim_id.
    have diff4: forall x, y < x < z -> derivable_pt ln x.
    - by move => d ineq'; apply/ln_derivable_pt; lra.
    have [d ineq' | d ineq' | d [ineq' /=]]:= MVT id ln y z diff3 diff4 zgy.
    - by apply/derivable_continuous_pt; exists 1; apply/derivable_pt_lim_id.
    - by apply/derivable_continuous_pt/ln_derivable_pt; lra.
    have ->: derive_pt id d (diff3 d ineq') = 1.
    - by rewrite -(derive_pt_id d); apply/derive_pt_unique.
    rewrite Rmult_1_r => ->.
    have ->: derive_pt ln d (diff4 d ineq') = /d.
    - apply/derive_pt_eq/derivable_pt_lim_ln; lra.
    rewrite Rmult_comm -Rmult_assoc Rinv_l; try lra; rewrite Rmult_1_l.
    apply/Rinv_lt_contravar; try lra.
    by apply/Rmult_lt_0_compat; lra.
  Qed.

  Lemma scnc_subs A B f: (forall x, A x -> B x) ->
                         strictly_concave_on B f -> strictly_concave_on A f.
  Proof. by move => subs conc x y z /subs bx /subs yb /subs zb; apply/conc. Qed.
  
  Lemma ln_le_inv x y: 0 < x -> 0 < y -> ln x <= ln y -> x <= y.
  Proof.
    move => x0 y0.
    case => [ineq | eq]; first exact/Rlt_le/ln_lt_inv.
    by rewrite (ln_inv x y) //; exact/Rle_refl.
  Qed.
End ln_strictly_concave.

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
          /q * ln (Rpower (Rabs b) q) + (1 - /q) * ln (Rpower (Rabs a) p)
          <
          ln (/q * Rpower (Rabs b) q + (1 - /q) * Rpower (Rabs a) p).
        * apply/scnc_spec; try lra.
          apply/scnc_subs/ln_scnc => x /= [ineq' _].
          exact/Rlt_le_trans/ineq'/exp_pos.
        have ->: 1 - /q = /p by lra.
        by rewrite ![/ _ * _]Rmult_comm ![_*/p + _]Rplus_comm /Rdiv => ineq'; apply/Rlt_le/ineq'.
      + rewrite eq /Rdiv; have ->: /q = 1 - /p by lra.
        have ->: Rpower (Rabs b) q * /p + Rpower (Rabs b) q * (1 - /p) = Rpower (Rabs b) q by ring.
        have ->:
             ln (Rpower (Rabs b) q) * (1 - /p) + ln (Rpower (Rabs b) q) * /p
             =
             ln (Rpower (Rabs b) q) by ring.
        exact/Rle_refl.
      have:
        /p * ln (Rpower (Rabs a) p) + (1 - /p) * ln (Rpower (Rabs b) q)
        <
        ln (/p * Rpower (Rabs a) p + (1 - /p) * Rpower (Rabs b) q).
      + apply/scnc_spec; try lra.
        by apply/scnc_subs/ln_scnc => x /= [ineq' _]; first exact/Rlt_le_trans/ineq'/exp_pos.
      have ->: 1- /p = /q by lra.
      by rewrite ![/ _ * _]Rmult_comm /Rdiv ![_*/p + _]Rplus_comm  => ineq'; apply/Rlt_le/ineq'.
    have [n0 n0']: a <> 0 /\ b <> 0 by apply/Rmult_neq_0_reg; lra.
    rewrite Rabs_mult ln_mult; try by split_Rabs; lra.
    by rewrite !ln_exp ![_ * /_]Rmult_comm -!Rmult_assoc !Rinv_l; try lra.
  Qed.
End Young's_inequality. 
