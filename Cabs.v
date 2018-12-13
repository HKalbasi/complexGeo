Require Import Cbase.

Definition Cabs ( x : Complex ) := sqrt ( real_p x * real_p x + imag_p x * imag_p x )%R.

Local Open Scope R_scope.

Lemma Ra2b2pos : forall a b : R , 0<=a*a+b*b.
Proof.
  intros.
  assert ( 0 <= a * a ).
  replace ( a * a ) with (a^2) ; [idtac | ring ].
  apply pow2_ge_0 with ( x := a ).
  assert ( 0 <= b * b ).
  replace ( b * b ) with (b^2) ; [idtac | ring ].
  apply pow2_ge_0 with ( x := b ).
  replace 0 with (0+0); [ idtac | ring ].
  apply Rplus_le_compat.
  auto.
  auto.
Qed.

Lemma ineq_p2 : forall a b : R , a * a >= b * b -> a >= 0 -> a >= b.
Proof.
  intros.
  apply Rnot_lt_ge.
  unfold not.
  intros.
  assert ( b >= 0 ).
  apply Rge_trans with (r2 := a).
  apply Rle_ge.
  auto with real.
  auto with real.
  assert ( a * a <= a * b ).
  auto with real.
  assert ( a * b <= b * b ).
  auto with real.
  assert ( a * a <= b * b ).
  auto with real.
  case H5.
  intros.
  assert ( ~ a * a >= b * b ).
  apply Rlt_not_ge.
  auto.
  contradiction.
  intros.
  assert ( sqrt (a*a) = sqrt (b*b) ).
  rewrite H6.
  auto.
  rewrite sqrt_square in H7.
  rewrite sqrt_square in H7.
  assert ( a <> b ).
  auto with real.
  auto.
  auto with real.
  auto with real.
Qed.

Lemma Rhelp_sqrt2 : forall x y : R , 0 <= x -> 0 <= y -> (sqrt x + sqrt y)^2 = x + y + 2 * sqrt (x*y).
Proof.
  intros.
  replace ( (sqrt x + sqrt y) ^ 2 ) with ( sqrt (x*x) + sqrt (y*y) + 2*sqrt(x*y) ).
  rewrite ! sqrt_square.
  auto.
  auto with real.
  auto with real.
  rewrite ! sqrt_mult_alt.
  ring.
  auto.
  auto.
  auto.
Qed.

Lemma ineq_hesabi_help : forall x y : R , x*x + y*y >= 2*x*y .
Proof.
  intros.
  apply Rplus_ge_reg_l with ( r := -2*x*y ).
  replace ( -2 * x * y + 2 * x * y ) with 0; [ idtac | ring ].
  replace ( -2 * x * y + (x * x + y * y) ) with ((x-y)^2); [ idtac | ring ].
  apply Rle_ge.
  apply pow2_ge_0.
Qed.

Lemma ineq_hesabi_hendesi : forall x y : R , 0<=x -> 0<=y -> x + y >= 2*sqrt(x*y).
Proof.
  intros.
  assert ( 0<=x * y ).
  replace ( 0 ) with ( x * 0 ) ; [ idtac | ring ].
  apply Rmult_le_compat_l.
  auto.
  auto.
  apply ineq_p2.
  replace ( 2 * sqrt (x * y) * (2 * sqrt (x * y)) ) with ( 4*x*y ).
  replace ( (x + y) * (x + y) ) with ( x*x + y*y + 2*x*y ) ; [ idtac | ring ].
  replace ( 4 * x * y ) with ( 2 * x * y + 2 * x * y ) ; [ idtac | ring ].
  apply Rplus_ge_compat_r.
  apply ineq_hesabi_help.
  replace ( 4*x*y ) with ( 4* sqrt(x*y) * sqrt (x*y) ).
  ring.
  rewrite Rmult_assoc.
  replace ( sqrt (x * y) * sqrt (x * y) ) with (x*y).
  ring.
  rewrite <- sqrt_mult_alt.
  apply eq_sym.
  apply sqrt_square.
  auto.
  auto.
  apply Rle_ge.
  replace 0 with (0+0) ; [ idtac | ring ].
  apply Rplus_le_compat.
  auto.
  auto.
Qed.

Lemma Rhelp_tri_ineq : forall ar ai br bi : R ,
 sqrt ( ar * ar + ai * ai ) + sqrt ( br * br + bi * bi )  >= sqrt ( (ar+br)*(ar+br) + (ai+bi)*(ai+bi) ).
Proof.
  intros.
  apply ineq_p2.
  replace ( sqrt ((ar + br) * (ar + br) + (ai + bi) * (ai + bi)) *
sqrt ((ar + br) * (ar + br) + (ai + bi) * (ai + bi)) )
  with ( ((ar + br) * (ar + br) + (ai + bi) * (ai + bi)) ).
  replace ( (sqrt (ar * ar + ai * ai) + sqrt (br * br + bi * bi)) *
(sqrt (ar * ar + ai * ai) + sqrt (br * br + bi * bi)) ) with 
  ( (sqrt (ar * ar + ai * ai) + sqrt (br * br + bi * bi))^2  ).
  rewrite Rhelp_sqrt2.
  replace ((ar + br) * (ar + br) + (ai + bi) * (ai + bi)) with 
    ( ar*ar+ai*ai+(br*br+bi*bi)+(2*ar*br+2*ai*bi) ); [ idtac | ring ].
  apply Rplus_ge_compat_l.
  replace ( 2 * ar * br + 2 * ai * bi ) with ( 2 * ( ar*br+ai*bi ) ) ; [ idtac | ring ].
  apply Rmult_ge_compat_l.
  auto with real.
  apply ineq_p2.
  replace ( sqrt ((ar * ar + ai * ai) * (br * br + bi * bi)) *
sqrt ((ar * ar + ai * ai) * (br * br + bi * bi)) ) with ( (ar * ar + ai * ai) * (br * br + bi * bi)).
  replace ( (ar * ar + ai * ai) * (br * br + bi * bi) ) with
   ((ar*ar*br*br + ai*ai*bi*bi) + ((bi*ar)*(bi*ar) + (br*ai)*(br*ai)) ) ; [idtac|ring].
  replace ( (ar * br + ai * bi) * (ar * br + ai * bi) ) with 
  ( (ar*ar*br*br + ai*ai*bi*bi) + 2*(bi * ar) * (br * ai) ) ; [idtac|ring ].
  apply Rplus_ge_compat_l.
  apply ineq_hesabi_help.
  apply eq_sym.
  apply sqrt_sqrt.
  replace 0 with ( (ar * ar + ai * ai) * 0 ).
  apply Rmult_le_compat_l.
  apply Ra2b2pos.
  apply Ra2b2pos.
  ring.
  apply Rle_ge.
  apply sqrt_pos.
  apply Ra2b2pos.
  apply Ra2b2pos.
  ring.
  apply eq_sym.
  apply sqrt_def.
  apply Ra2b2pos.
  replace 0 with (0+0) ; [ idtac | ring ].
  apply Rplus_ge_compat.
  apply Rle_ge.
  apply sqrt_pos.
  apply Rle_ge.
  apply sqrt_pos.
Qed.

Local Close Scope R_scope.

Lemma r2pi2pos : forall x : Complex , (0 <= real_p x * real_p x + imag_p x * imag_p x)%R.
Proof.
  intros.
  apply Ra2b2pos.
Qed.

Lemma abs_mult : forall a b : Complex , ( Cabs a * Cabs b = Cabs (a*b)%C )%R.
Proof.
  intros.
  rewrite Cmult_decompose.
  unfold Cabs.
  simpl.
  replace ((sqrt (real_p a * real_p a + imag_p a * imag_p a) *
 sqrt (real_p b * real_p b + imag_p b * imag_p b))%R) with 
  (sqrt ((real_p a * real_p a + imag_p a * imag_p a) *
 (real_p b * real_p b + imag_p b * imag_p b))%R).
  assert ( (real_p a * real_p a + imag_p a * imag_p a) *
   (real_p b * real_p b + imag_p b * imag_p b) =

   (real_p a * real_p b - imag_p a * imag_p b) *
   (real_p a * real_p b - imag_p a * imag_p b) +
   (real_p a * imag_p b + imag_p a * real_p b) *
   (real_p a * imag_p b + imag_p a * real_p b))%R.
  ring.
  rewrite H.
  auto.
  apply sqrt_mult_alt.
  apply r2pi2pos.
Qed.

Hint Resolve abs_mult : complex.



Lemma abs_tri_ineq : forall a b : Complex , ( Cabs a + Cabs b >= Cabs (a+b)%C )%R.
Proof.
  intros.
  rewrite Cplus_decompose.
  unfold Cabs.
  simpl.
  apply Rhelp_tri_ineq.
Qed.

Hint Resolve abs_tri_ineq : complex.

 