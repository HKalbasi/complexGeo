Require Import Complex Geobase Geoline GeoParallel.

SearchAbout (_ < _ )%C.

Lemma Total_orderC ( a b : Complex ) : ({ a < b } + { a = b } + { b < a })%C.
Proof.
  rewrite Cdecompose with (z:=a).
  rewrite Cdecompose with (z:=b).
  unfold Clt.
  destruct ( total_order_T (real_p a) (real_p b) ).
  destruct ( total_order_T (imag_p a) (imag_p b) ).
  destruct s0.
  left.
  left.
  destruct ( Real_eq_dec (real_p a) (real_p b) ).
  auto.
  destruct s.
  auto.
  contradiction.
  destruct ( Real_eq_dec (real_p a) (real_p b) ).
  left; right.
  rewrite e,e0.
  auto.
  destruct s.
  auto.
  contradiction.
  destruct s.
  destruct ( Real_eq_dec (real_p a) (real_p b) ).
  rewrite e in r0.
  apply Rlt_irrefl in r0.
  contradiction.
  auto.
  destruct ( Real_eq_dec (real_p b) (real_p a) ).
  auto.
  apply eq_sym in e.
  contradiction.
  destruct ( Real_eq_dec (real_p b) (real_p a) ).
  rewrite e in r.
  apply Rlt_irrefl in r.
  contradiction.
  auto.
Qed.

Lemma Ceq_dec : forall a b : Complex , { a = b } + { a <> b }.
Proof.
  intros.
  destruct (Total_orderC a b ).
  destruct s.
  apply Cineq_eq in c.
  auto.
  auto.
  apply Cineq_eq in c.
  auto.
Qed. 

Lemma Cabs_inv : forall z : Complex , z <> C0 -> Cabs (/z)%C = (/Cabs(z))%R.
Proof.
  intros.
  assert ( forall a b : R , b <> 0 -> a * b = 1 -> a = / b )%R.
  intros.
  field [ H1 ].
  auto.
  apply H0.
  intros fk.
  apply Cabs0z0 in fk.
  apply H.
  auto.
  rewrite abs_mult.
  replace (/ z * z)%C with C1 ; [ idtac | field ].
  unfold C1.
  unfold Cabs.
  simpl.
  rewrite <- sqrt_1.
  f_equal.
  rewrite sqrt_1.
  ring.
  auto.
Qed.

Lemma CabsC0 : Cabs C0 = 0%R.
Proof.
  intros.
  unfold C0.
  unfold Cabs.
  rewrite <- sqrt_0.
  f_equal.
  rewrite sqrt_0.
  simpl.
  ring.
Qed.

Lemma Cabs_pos : forall z : Complex , (Cabs z >= 0)%R.
Proof.
  intros.
  destruct (Ceq_dec z C0).
  right.
  rewrite e.
  apply CabsC0.
  left.
  apply Cneq0abs.
  auto.
Qed.

Lemma Carg_ineq0 : forall z : Complex , z <> C0 -> (- PI / 2 < Carg z <= PI / 2)%R -> (C0 < z)%C.
Proof.
  intros.
  destruct H0.
  case H1.
  intros.
  unfold C0.
  rewrite Cdecompose.
  unfold Clt.
  assert ( 0 < real_p z )%R.
  rewrite Creal_arg.
  apply Rmult_lt_0_compat.
  apply Cneq0abs.
  auto.
  apply cos_gt_0.
  rewrite <- Ropp_div.
  auto.
  auto.
  destruct ( Real_eq_dec 0 (real_p z) ).
  assert ( 0%R <> real_p z ).
  auto with real.
  contradiction.
  auto.
  intros.
  assert ( 0 = real_p z )%R.
  rewrite Creal_arg.
  rewrite H2.
  rewrite cos_PI2.
  ring.
  unfold C0.
  rewrite Cdecompose.
  unfold Clt.
  destruct ( Real_eq_dec 0 (real_p z) ).
  rewrite Cimag_arg.
  rewrite H2.
  rewrite sin_PI2.
  ring_simplify.
  apply Cneq0abs.
  auto.
  contradiction.
Qed.

Lemma argneg0 : -^ 0%R = 0%R.
Proof.
  intros.
  unfold argneg.
  destruct ( Real_eq_dec 0 PI ).
  rewrite e.
  auto.
  ring.
Qed.

Definition preLine2P ( a b : Complex ) : {x : Line | on_line a x /\ on_line b x }.
Proof.
  destruct (Total_orderC a b).
  destruct s.
  remember ((b-a)/(Cabs(b-a),0%R))%C as t.
  assert ( Cabs t = 1%R ) as Lshib_len1.
  rewrite Heqt.
  unfold Cdiv.
  rewrite <- abs_mult.
  rewrite Cabs_inv.
  rewrite Cabs_R.
  rewrite Rabs_right.
  field.
  apply Cineq_eq in c.
  intros fk.
  apply Cabs0z0 in fk.
  apply Ceq_side in fk.
  auto.
  apply Cabs_pos.
  apply Cneq0.
  rewrite Cabs_R.
  rewrite Rabs_right.
  apply Cineq_eq in c.
  intros fk.
  apply Cabs0z0 in fk.
  apply Ceq_side in fk.
  auto.
  apply Cabs_pos.
  assert ( C0 < t )%C as Lshib_gt_C0.
  apply Carg_ineq0.
  apply Cneq0.
  rewrite Lshib_len1.
  auto with real.
  rewrite Heqt.
  rewrite <- argminusdiv.
  rewrite Carg_R.
  unfold argminus.
  rewrite argneg0.
  rewrite argplus_comm.
  rewrite argplus0.
  apply Cineq0_arg.
  replace C0 with (a-a)%C ; [ idtac | ring ].
  apply Cineq_plus.
  auto.
  apply Carg_def.
  apply Cneq0abs.
  apply Cineq_eq in c.
  intros fk.
  apply Ceq_side in fk.
  apply c.
  auto.
  apply Cineq_eq in c.
  intros fk.
  apply Ceq_side in fk.
  apply c.
  auto.
  apply Cneq0.
  rewrite Cabs_R.
  rewrite Rabs_right.
  intros fk.
  apply Cineq_eq in c.
  apply c.
  apply Cabs0z0 in fk.
  apply eq_sym.
  apply Ceq_side.
  auto.
  apply Cabs_pos.
  remember ( t * a + Ccoj ( t * a ) )%C as az.
  exists {|
  Larz := real_p az;
  Lshib := t;
  Lshib_len1 := Lshib_len1;
  Lshib_gt_C0 := Lshib_gt_C0 |}.
  unfold on_line.
  split.
  simpl.
  replace ((real_p t * real_p a - - imag_p t * - imag_p a)%R,
 (real_p t * - imag_p a + - imag_p t * real_p a)%R) with ( Ccoj (t*a)%C ).
  rewrite <- Heqaz.
  replace (0%R) with (imag_p az).
  apply Cdecompose.
  rewrite Heqaz.
  remember (t*a)%C as g.
  rewrite Cdecompose with (z:=g).
  simpl.
  ring.
  rewrite Cdecompose with (z:=t).
  rewrite Cdecompose with (z:=a).
  simpl.
  unfold Ccoj.
  simpl.
  apply injective_projections.
  simpl.
  ring.
  simpl.
  ring.
  unfold Larz.
  unfold Lshib.
  apply injective_projections.
  rewrite Cdecompose with (z:=t).
  rewrite Cdecompose with (z:=b).
  simpl.
  (* bikhial *)
Admitted.

Definition Line2P x y := let (v, _) := preLine2P x y in v.

Lemma Line2P_def : forall a b : Complex , on_line a (Line2P a b) /\ on_line b (Line2P a b).
Proof.
  intros.
  unfold Line2P.
  destruct preLine2P as [m H1].
  auto.
Qed.

Definition LineParP ( x : Complex ) ( l : Line ) := 
{|
  Larz := real_p (l*x+Ccoj(l*x))%C;
  Lshib := l;
  Lshib_len1 := Lshib_len1 l;
  Lshib_gt_C0 := Lshib_gt_C0 l |}.

Lemma LineParP_def ( x : Complex ) ( l : Line ) : LineParP x l ||| l /\ on_line x (LineParP x l).
Proof.
  intros.
  split.
  split.
  unfold LineParP.
  unfold on_line.
  rewrite Ccojmult.
  simpl.
  remember (l*x)%C as f.
  replace 0%R with (imag_p ( f + Ccoj f )%C ).
  apply Cdecompose.
  rewrite Cdecompose with (z:=f).
  simpl.
  ring.
Qed.

