Require Import Reals.
Local Open Scope R_scope.

Theorem additive_equality : forall z x y, x + z = y + z -> x = y.
  proof.
    let z, x, y be such that
           (x + z         = y + z        ).
      then (x + z + - z   = y + z + - z  ).
      then (x + (z + - z) = y + (z + - z)) by Rplus_assoc.
      then (x + 0         = y + 0        ) by Rplus_opp_r.
      hence thesis                         by Rplus_0_r  .
  end proof.
Qed.

Theorem multiplicative_equality : forall z x y, x * z = y * z -> z <> 0 -> x = y.
  proof.
    let z, x, y be such that
         H:(x * z         = y * z        ) and NZ:(z <> 0).
      have (x * z * / z   = y * z * / z  ) by H.
      then (x * (z * / z) = y * (z * / z)) by Rmult_assoc  .
      then (x * 1         = y * 1        ) by (Rinv_r z NZ).
      hence thesis                         by Rmult_1_r    .
  end proof.
Qed.

Theorem divisive_equality : forall z x y, x / z = y / z -> z <> 0 -> x = y.
  proof.
    let z, x, y be such that H:(x / z = y / z) and NZ:(z <> 0).
      thus thesis by (multiplicative_equality (/ z) x y H (Rinv_neq_0_compat z NZ)).
  end proof.
Qed.

Theorem cross_multiply : forall x y a b, y <> 0 -> b <> 0 -> (x * b = a * y <-> x / y = a / b).
  proof.
    let x, y, a, b be such that 

Theorem cross_multiply_0 : forall x y a b, x * b = a * y -> y <> 0 -> b <> 0 -> x / y = a / b.
  intros.
  assert ((x * b) * / b = (a * y) * / b) by congruence.
  rewrite Rmult_assoc, Rinv_r, Rmult_1_r in H2 by assumption.
  assert (x * / y = a * y * / b * / y) by congruence.
  rewrite Rmult_assoc, (Rmult_comm (/ b)), Rmult_assoc in H3.
  rewrite <- (Rmult_assoc y) in H3.
  rewrite Rinv_r, Rmult_1_l in H3 by assumption.
  unfold Rdiv ; assumption.
  Show Tree.
Qed.

Theorem cross_multiply_1 : forall x y a b, x / y = a / b -> y <> 0 -> b <> 0 -> x * b = a * y.
  intros.
  apply cross_multiply_0 in H ; try (apply Rinv_neq_0_compat ; assumption).
  unfold Rdiv in H.
  rewrite ?Rinv_involutive in H ; assumption.
  Show Tree.
Qed.

Theorem p_0_0 : forall x, 4 * x = 16 -> x = 4.
  intros.
  replace 16 with (4 * 4) in H by Rcompute.
  rewrite Rmult_comm in H.
  apply multiplicative_equality in H ; [assumption | discrR].
  Show Tree.
Qed.

Theorem p_0_1 : forall x, 4 * x + 56 = 72 -> x = 4.
  intros.
  replace 72 with (16 + 56) in H by Rcompute.
  apply additive_equality in H.
  apply p_0_0 ; assumption.
  Show Tree.
Qed.

Theorem p_0_2 : forall x, (x + 14) / 24 = 3 / 4 -> x = 4.
  intros.
  apply cross_multiply_1 in H ; discrR.
  replace (3 * 24) with 72 in H by Rcompute.
  rewrite Rmult_plus_distr_r in H.
  rewrite Rmult_comm in H.
  replace (14 * 4) with 56 in H by Rcompute.
  apply p_0_1 ; assumption.
  Show Tree.
Qed.

Lemma div_id : forall x, x / 1 = x.
  intros.
  unfold Rdiv.
  rewrite Rinv_1.
  apply Rmult_1_r.
  Show Tree.
Qed.

Theorem p_0_3 : forall x, 10 - x <> 0 -> (x - - 14) / (10 - x) = 3 / 1 -> x = 4.
  intros x NZ H.
  apply cross_multiply_1 in H ; assumption || discrR.
  rewrite Rmult_1_r in H.
  unfold Rminus in H.
  rewrite Ropp_involutive in H.
  rewrite -> (Rmult_plus_distr_l 3) in H.
  replace (3 * 10) with 30 in H by Rcompute.
  rewrite Ropp_mult_distr_r_reverse in H. 
  assert (x + 14 + 3 * x = 30 + - (3 * x) + 3 * x) by congruence.
  replace (30 + - (3 * x) + 3 * x) with (30 + (- (3 * x) + 3 * x)) in H0 by (symmetry ; apply Rplus_assoc).
  rewrite Rplus_opp_l in H0.
  replace (30 + 0) with (16 + 14) in H0 by Rcompute.
  replace (x + 14 + 3 * x) with (x + (14 + 3 * x)) in H0 by (symmetry ; apply Rplus_assoc).
  replace (14 + 3 * x) with (3 * x + 14) in H0 by (apply Rplus_comm).
  rewrite <- Rplus_assoc in H0.
  apply (additive_equality 14) in H0.
  rewrite <- (Rmult_1_l x) in H0 at 1.
  rewrite <- Rmult_plus_distr_r in H0.
  replace 16 with (4 * (1 + 3)) in H0 by Rcompute.
  rewrite Rmult_comm in H0.
  apply multiplicative_equality in H0 ; discrR ; assumption.
  Show Tree.
Qed.

Theorem p_1_0 : forall x, 2 * (3 * x + 1) - 8 * x = - 2 * x + 2.
  intros.
  rewrite Rmult_plus_distr_l.
  rewrite <- Rmult_assoc.
  unfold Rminus.
  rewrite Rplus_assoc.
  rewrite (Rplus_comm (2 * 1)).
  rewrite <- Rplus_assoc.
  rewrite <- Ropp_mult_distr_l_reverse.
  rewrite <- Rmult_plus_distr_r.
  rewrite Rmult_1_r.
  replace (6 + -8) with (-2) by Rcompute.
  reflexivity.
  Show Tree.
Qed.

Theorem p_1_1 : forall x, 2 * (3 * x + 1) = 8 * x -> x = 1.
  intros.
  assert (2 * (3 * x + 1) - 8 * x = 8 * x - 8 * x) by congruence.
  rewrite p_1_0 in H0.
  unfold Rminus in H0.
  rewrite Rplus_opp_r in H0.
  replace 0 with (-2 + 2) in H0 by Rcompute.
  apply additive_equality in H0.
  rewrite Rmult_comm in H0.
  rewrite <- (Rmult_1_l (-2)) in H0 at 2.
  apply multiplicative_equality in H0 ; assumption || discrR.
  Show Tree.
Qed.

Theorem p_1_2 : forall a b c d, a = 2 * b -> a = 8 * d -> b = c + 1 -> c = 3 * d -> d = 1.
  intros.
  rewrite H1 in H ; rewrite H2 in H ; rewrite H in H0.
  apply p_1_1 in H0 ; assumption.
  Show Tree.
Qed.

Theorem p_2_0 : forall x, 1600 - (75 / 1000) * x < 100 <-> x > 20000.
  intros.
  replace (75 / 1000) with (3 / 40).
  assert ((40 * / 3) * (3 / 40) = 1) as id40_3.
  rewrite <- Rinv_Rdiv ; discrR.
  apply Rinv_r ; rewrite <- (div_id 0).
  pose 0 as temp ; contradict temp. apply cross_multiply_1 in temp ; discrR. contradict temp ; clear temp ; discrR.
  split ; intros.
  apply (Rplus_lt_compat_l (-1600)) in H.
  replace (-1600 + 100) with (-1500) in H by Rcompute.
  unfold Rminus in H.
  rewrite <- (Rplus_assoc (-1600)) in H.
  rewrite Rplus_opp_l in H.
  rewrite Rplus_0_l in H.
  apply Ropp_lt_gt_contravar in H.
  rewrite ?Ropp_involutive in H.
  apply (Rmult_lt_compat_l (40 * / 3)) in H.
  rewrite Rmult_assoc in H.
  replace (/ 3 * 1500) with 500 in H.
  replace (40 * 500) with 20000 in H by Rcompute.
  rewrite <- (Rmult_assoc (40 * / 3)) in H.
  rewrite id40_3 in H.
  rewrite Rmult_1_l in H.
  apply Rlt_gt ; assumption.
  replace (/ 3 * 1500) with (1500 / 3).
  rewrite <- (div_id 500) at 1.
  apply cross_multiply_0 ; discrR.
  Rcompute.
  unfold Rdiv.
  apply Rmult_comm.
  apply Fourier_util.Rlt_mult_inv_pos ; prove_sup.
  apply (Rplus_lt_reg_r (-1600)).
  replace (-1600 + 100) with (-1500) by Rcompute.
  unfold Rminus.
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  apply Ropp_gt_lt_contravar.
  apply (Rmult_lt_reg_l (40 * / 3)).
  apply Fourier_util.Rlt_mult_inv_pos ; prove_sup.
  rewrite <- (Rmult_assoc _ (3 / 40)).
  rewrite id40_3.
  rewrite Rmult_1_l.
  rewrite Rmult_comm.
  rewrite <- (Rmult_assoc 1500).
  replace (1500 * 40) with 60000 by Rcompute.
  replace (60000 * / 3) with 20000.
  apply Rgt_lt ; assumption.
  replace (60000 * / 3) with (60000 / 3) by (unfold Rdiv ; reflexivity).
  rewrite <- (div_id 20000).
  apply cross_multiply_0 ; discrR ; Rcompute.
  apply cross_multiply_0 ; discrR ; Rcompute.
  Show Tree.
Qed.

Theorem p_2_2 : forall net gross, net = gross - 400 -> (1600 - (75 / 1000) * gross < 100 <-> net > 19600).
  intros.
  unfold Rminus in H.
  rewrite H.
  split ; intros.
  apply p_2_0 in H0. 
  replace 19600 with (20000 + - 400) by Rcompute.
  apply Rplus_gt_compat_r ; assumption.
  replace 19600 with (20000 + - 400) in H0 by Rcompute.
  rewrite Rplus_comm, (Rplus_comm 20000) in H0.
  apply Rplus_gt_reg_l in H0.
  apply p_2_0 in H0 ; assumption.
  Show Tree.
Qed.

(*Theorem p_3_0 : forall x, (3 / 5) * x + 4 = 24 -> x = 100 / 3.
  intros.
  replace 24 with (20 + 4) in H by Rcompute.
  apply additive_equality in H.
  replace 20 with ((3 / 5) * (100 / 3)) in H.
  rewrite Rmult_comm, (Rmult_comm _ (100 / 3)) in H.
  apply multiplicative_equality in H ; try assumption.
  contradict H.*)
