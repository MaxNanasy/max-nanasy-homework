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
      have  (2 * (3 * x + 1) - 8 * x =  2 * (3 * x + 1) - 8 * x    ).
                                    ~= (2 * (3 * x) + 2 * 1 - 8 * x) by    Rmult_plus_distr_l       .
                                    ~= (2 * 3 * x + 2 * 1 - 8 * x  ) by    Rmult_assoc              .
                                    ~= (6 * x + 2 - 8 * x          ) using field                    .
                                    ~= (6 * x + 2 + - (8 * x)      )                                .
                                    ~= (6 * x + - (8 * x) + 2      ) by    Rplus_comm_3             .
                                    ~= (6 * x + - 8 * x + 2        ) by    Ropp_mult_distr_l_reverse.
                                    ~= ((6 + - 8) * x + 2          ) by    Rmult_plus_distr_r       .
      hence (2 * (3 * x + 1) - 8 * x =  - 2 * x + 2                ) using field                    .
  end proof.
Qed.
