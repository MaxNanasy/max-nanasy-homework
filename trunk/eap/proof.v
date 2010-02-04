Require Import Reals.
Local Open Scope R_scope.
SearchAbout ["assoc"].

Definition associative A f := forall x y z : A, f (f x y) z = f x (f y z).
Definition commutative A B (f : A -> A -> B) := forall x y, f x y = f y x.

Theorem comm_3 : forall A f, associative _ f -> commutative _ _ f -> forall x y z : A, f (f x y) z = f (f x z) y.
  proof.
    let A, f be such that ASSOC:(associative A f) and COMM:(commutative A A f).
    let  x:A, y:A, z:A.
      have  (f (f x y) z =  f (f x y) z)         .
                        ~= (f x (f y z)) by ASSOC.
                        ~= (f x (f z y)) by COMM .
      hence (f (f x y) z =  f (f x z) y) by ASSOC.
  end proof.
Qed.

Definition Rplus_comm_3 := comm_3 _ Rplus Rplus_assoc Rplus_comm.
Definition Rmult_comm_3 := comm_3 _ Rmult Rmult_assoc Rmult_comm.

Theorem Rplus_minus_eq : forall z x y, x = y + z -> x - z = y.
  proof.
    let z, x, y be such that
            (x       =  y + z        ).
      then  (x + - z =  y + z + - z  ).
                    ~= (y + (z + - z)) by Rplus_assoc.
                    ~= (y + 0        ) by Rplus_opp_r.
                    ~= (y            ) by Rplus_opp_r.
      hence (x - z   =  y            ).
  end proof.
Qed.

Theorem Rdiv_mult_eq : forall z x y, z <> 0 -> x = y / z -> x * z = y.
  proof.
    let z, x, y be such that NZ:(z <> 0) and
            (x     =  y / z        )                 .
      then  (x * z =  y / z * z    )                 .
                  ~= (y * (/ z * z)) by  Rmult_assoc .
                  ~= (y * 1        ) by (Rinv_l _ NZ).
      hence (x * z =  y            ) by  Rmult_1_r   .
  end proof.
Qed.

Theorem cross_multiply : forall x y a b, y <> 0 -> b <> 0 -> (x / b = a / y -> x * y = a * b).
  proof.
    let x:R, y, a:R, b be such that YNZ:(y <> 0) and BNZ:(b <> 0) and
            (x * / b        = a / y    )                                  .
      then  (x * / b * y    = a        ) by (Rdiv_mult_eq _ (x / b) a YNZ).
      =~    (x * y * / b  )              by Rmult_comm_3                  .
      then  (a              = x * y / b) by sym_eq                        .
      hence (x * y          = a * b    ) by (Rdiv_mult_eq _ a (x * y) BNZ).
  end proof.
Qed.

Lemma NZ4 : 4 <> 0.
  discrR.
Qed.

Theorem p_0_0 : forall x, 4 * x = 16 -> x = 4.
  proof.
    let x be such that
           (4 * x =    16   )                                   .
                 ~= H:(4 * 4) using field                       .
      thus (x     =    4    ) by    (Rmult_eq_reg_l _ _ _ H NZ4).
  end proof.
Qed.

Theorem p_0_1 : forall x, 4 * x + 56 = 72 -> x = 4.
  proof.
    let x be such that
            (4 * x + 56  =  72     )                    .
                        ~= (56 + 16) using field        .
      =~    (56 + 4 * x)             by   Rmult_comm    .
      then  (4 * x       =  16     ) by   Rplus_eq_reg_l.
      hence (x           =  4      ) by   p_0_0         .
  end proof.
Qed.

Lemma NZ24 : 24 <> 0.
  discrR.
Qed.

Theorem p_0_2 : forall x, (x + 14) / 24 = 3 / 4 -> x = 4.
  proof.
    let x be such that
            ((x + 14) / 24    = 3 / 4 )                                               .
      then  ((x + 14) * 4     = 3 * 24) by    (cross_multiply (x + 14) _ 3 _ NZ4 NZ24).
                             ~= 72      using field                                   .
      =~     (x * 4 + 14 * 4)           by    Rmult_plus_distr_r                      .
      =~     (x * 4 + 56    )           using field                                   .
      =~     (4 * x + 56    )           by    Rmult_comm                              .
      hence ( x               = 4     ) by p_0_1.
  end proof.
Qed.

Theorem p_0_3 : forall x, 10 - x <> 0 -> (x - - 14) / (10 - x) = 3 / 1 -> x = 4.
  proof.
    let x be such that NZ:(10 - x <> 0) and
           ((x - - 14) / (10 - x)    =  3 / 1           )                                                   .
     =~    ((x + - - 14) / (10 - x))                                                                        .
     =~    ((x + 14) / (10 - x)    )                      by    Ropp_involutive                             .
     then  ((x + 14) * 1             =  3 * (10 - x)    ) by    (cross_multiply (x + 14) _ 3 _ R1_neq_R0 NZ).
     =~     (x + 14)                                      by    Rmult_1_r                                   .
                                    ~= (3 * (10 + - x)  )                                                   .
                                    ~= (3 * 10 + 3 * - x) by    Rmult_plus_distr_l                          .
                                    ~= (30 + 3 * - x    ) using field                                       .
     then  ( x + 14 - 3 * - x        =  30              ) by    Rplus_minus_eq                              .
     =~    ( x + 14 + - (3 * - x)).
     =~    ( x + 14 + - - (3 * x))                        by    Ropp_mult_distr_r_reverse                   .
     =~    ( x + 14 + 3 * x      )                        by    Ropp_involutive                             .
     =~    ( x + 3 * x + 14      )                        by    Rplus_comm_3                                .
     =~    ( 1 * x + 3 * x + 14  )                        by    Rmult_1_l                                   .
     =~    ( (1 + 3) * x + 14    )                        by    Rmult_plus_distr_r                          .
     =~    ( 4 * x + 14          )                        using field                                       .
     then  ( 30 - 14                 = 4 * x            ) by    Rplus_minus_eq                              .
     then  ( 4 * x                   = 30 - 14          ) by    sym_eq                                      .
                                    ~= 16                 using field                                       .
     hence ( x                       = 4                ) by    p_0_0                                       .
  end proof.
Qed.

Theorem p_1_0 : forall x, 2 * (3 * x + 1) - 8 * x = - 2 * x + 2.
  proof.
    let x:R.
      have (2 * (3 * x + 1) - 8 * x =  2 * (3 * x + 1) - 8 * x).
                                   ~= (2 * (3 * x) + 2 * 1 - 8 * x) by Rmult_plus_distr_l.
                                   ~= (2 * 3 * x + 2 * 1 - 8 * x)   by Rmult_assoc.
                                   ~= (6 * x + 2 - 8 * x)           using field.
                                   ~= (
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
