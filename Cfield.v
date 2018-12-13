Require Import Cbase Cabs Carg Ccoj.

Local Open Scope R_scope.


Local Close Scope R_scope.

Definition argminus ( x : R ) ( y : R ) := x +^ -^ y.

Infix " -^ " := argminus ( at level 20 ).

Lemma argnegineq : forall x : R , (-PI < x <= PI)%R -> (-PI < ( -^ x ) <= PI)%R.
Proof.
  intros.
  unfold argneg.
  destruct ( Real_eq_dec x PI ).
  split.
  ring_simplify.
  replace PI with ( 1 * PI )%R ; [idtac|ring].
  rewrite Ropp_mult_distr_l.
  apply Rmult_lt_compat_r.
  apply PI_RGT_0.
  apply Rplus_lt_reg_r  with (r := (1)%R ).
  ring_simplify.
  auto with real.
  auto with real.
  destruct H.
  case H0.
  intros.
  split.
  auto with real.
  left.
  apply Ropp_lt_cancel.
  ring_simplify.
  auto.
  intros.
  contradiction.
Qed.

Lemma argminusineq : forall x y : R , (-PI < x <= PI)%R -> (-PI < y <= PI)%R -> (-PI < ( x -^ y ) <= PI)%R.
Proof.
  intros.
  unfold argminus.
  apply argplusineq.
  auto.
  apply argnegineq.
  auto.
Qed.

Lemma argnegcos : forall x : R , cos ( -^ x ) = cos ( - x )%R.
Proof.
  intros.
  unfold argneg.
  destruct ( Real_eq_dec x PI ).
  rewrite cos_neg.
  rewrite e.
  auto.
  auto.
Qed.

Lemma argnegsin : forall x : R , sin ( -^ x ) = sin ( - x )%R.
Proof.
  intros.
  unfold argneg.
  destruct ( Real_eq_dec x PI ).
  rewrite sin_neg.
  rewrite e.
  rewrite sin_PI.
  ring.
  auto.
Qed.

Lemma argminuscos : forall x y : R , cos ( x -^ y ) = cos ( x - y )%R.
Proof.
  intros.
  unfold argminus.
  rewrite argpluscos.
  rewrite cos_plus.
  rewrite argnegcos.
  rewrite argnegsin.
  unfold Rminus.
  rewrite cos_plus.
  ring.
Qed.

Lemma Ceq_side : forall a b : Complex , (a - b)%C = C0 -> a = b.
Proof.
  intros.
  unfold Cminus in H.
  unfold C0 in H.
  apply eq_sym in H.
  rewrite Cdecompose with ( z := b ) in H.
  unfold Copp in H.
  rewrite Cplus_decompose in H.
  simpl in H.
  apply injective_projections.
  apply eq_sym.
  apply Rminus_diag_uniq_sym.
  replace (fst a - fst b)%R with ( fst ((real_p a + - real_p b)%R, (imag_p a + - imag_p b)%R) ).
  rewrite <- H.
  auto.
  auto.
  apply eq_sym.
  apply Rminus_diag_uniq_sym.
  replace (snd a - snd b)%R with ( snd ((real_p a + - real_p b)%R, (imag_p a + - imag_p b)%R) ).
  rewrite <- H.
  auto.
  auto.
Qed.

Lemma Ceq_side2 : forall a b : Complex , a = b -> ( a - b )%C=C0.
Proof.
  intros.
  rewrite H.
  unfold C0.
  rewrite Cdecompose with ( z:=b).
  unfold Cminus.
  unfold Copp.
  rewrite Cplus_decompose.
  simpl.
  apply injective_projections.
  simpl.
  ring.
  simpl.
  ring.
Qed.

Check field_theory.

Lemma complexSFth : field_theory C0 C1 Cplus Cmult Cminus Copp Cdiv Cinv (@eq Complex).
Proof.
  constructor. exact complexSRth.
  exact C1_neq_C0.
  unfold Cdiv.
  auto.
  apply Cinv_l.
Qed.

Add Field complexf : complexSFth.

Lemma CinvnC0 : forall a : Complex , a <> C0 -> (/ a)%C <> C0.
Proof.
  intros.
  unfold not.
  intros.
  assert ( a / a = a * C0 )%C.
  unfold Cdiv.
  rewrite H0.
  auto.
  field_simplify in H1.
  replace (C1 / C1)%C with C1 in H1; [ idtac | field ].
  apply C1_neq_C0.
  rewrite H1.
  replace (R0,R0) with C0.
  field.
  apply C1_neq_C0.
  auto.
  apply C1_neq_C0.
  contradiction.
Qed.

Lemma Cabs2 : forall z : Complex , ((Cabs z)^2 = real_p z * real_p z + imag_p z * imag_p z )%R.
Proof.
  intros.
  unfold Cabs.
  simpl.
  rewrite <- Rmult_assoc.
  rewrite sqrt_def.
  ring.
  apply Ra2b2pos.
Qed.

Lemma Cosine_rule_intro : forall a b : Complex , ( ((real_p a + real_p b) * (real_p a + real_p b) +
   (imag_p a + imag_p b) * (imag_p a + imag_p b))%R = (real_p a * real_p a + imag_p a * imag_p a +
   (real_p b * real_p b + imag_p b * imag_p b) +
   2 * Cabs a * Cabs b *
   (cos (Carg a) * cos (Carg b) + sin (Carg a) * sin (Carg b)) ))%R.
Proof.
  intros.
  ring_simplify.
  replace ( 2 * Cabs a * Cabs b * cos (Carg a) * cos (Carg b) )%R 
  with ( 2 * (Cabs a * cos (Carg a)) * (Cabs b * cos (Carg b) ) )%R ; [ idtac | ring ].
  rewrite <- ! Creal_arg.
  replace ( 2 * Cabs a * Cabs b * sin (Carg a) * sin (Carg b) )%R with
  ( 2 * (Cabs a * sin (Carg a)) * (Cabs b * sin (Carg b)) )%R ; [ idtac | ring ].
  rewrite <- ! Cimag_arg.
  ring.
Qed.

Lemma Cosine_rule_pos : forall a c : Complex , (0%R <= Cabs a ^ 2 + Cabs c ^ 2 + 2 * Cabs a * Cabs c * cos (Carg a - Carg c))%R.
Proof.
  intros.
  rewrite ! Cabs2.
  rewrite cos_minus.
  rewrite <- Cosine_rule_intro.
  apply Ra2b2pos.
Qed.

Theorem Cosine_rule : forall a b : Complex , Cabs (a+b)%C = sqrt ( (Cabs a)^2 + (Cabs b)^2 + 2*(Cabs a)*(Cabs b)*cos(Carg a - Carg b) )%R. 
Proof.
  intros.
  rewrite ! Cabs2.
  rewrite Cplus_decompose.
  rewrite cos_minus.
  assert ( ((real_p a + real_p b) * (real_p a + real_p b) +
   (imag_p a + imag_p b) * (imag_p a + imag_p b))%R = (real_p a * real_p a + imag_p a * imag_p a +
   (real_p b * real_p b + imag_p b * imag_p b) +
   2 * Cabs a * Cabs b *
   (cos (Carg a) * cos (Carg b) + sin (Carg a) * sin (Carg b)) ))%R.
  apply Cosine_rule_intro.
  rewrite <- H.
  unfold Cabs.
  auto.
Qed.

Theorem Cabs_sum_eq : forall a b c d : Complex , a <> C0 -> c <> C0 -> Cabs a = Cabs b -> Cabs c = Cabs d -> Cabs (a+c)%C = Cabs (b+d)%C -> Rabs ( Carg a -^ Carg c )%R = Rabs ( Carg b -^ Carg d )%R.
Proof.
  intros a b c d an0 cn0.
  intros.
  rewrite Cosine_rule in H1.
  rewrite Cosine_rule in H1.
  apply sqrt_inj in H1.
  rewrite <- H in H1.
  rewrite <- H0 in H1.
  apply Rminus_diag_eq in H1.
  ring_simplify in H1.
  apply Rminus_diag_uniq_sym in H1.
  apply coseq.
  apply argminusineq.
  apply Carg_def.
  apply Carg_def.
  apply argminusineq.
  apply Carg_def.
  apply Carg_def.
  rewrite ! argminuscos.
  apply Rmult_eq_reg_l in H1.
  auto.
  unfold not.
  intros.
  Search ( _ * _ = 0 )%R.
  apply Rmult_integral in H2.
  case H2.
  intros.
  apply Rmult_integral in H3.
  case H3.
  intros.
  assert ( 2 <> 0 )%R.
  auto with real.
  contradiction.
  intros.
  apply Cabs0z0 in H4.
  contradiction.
  intros.
  apply Cabs0z0 in H3.
  contradiction.
  apply Cosine_rule_pos.
  apply Cosine_rule_pos.
Qed. 
