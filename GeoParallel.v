Require Import Complex Geobase Geoline.

Definition Is_parallel ( a b : Line ):= Lshib a = Lshib b.

Infix " ||| " := Is_parallel ( at level 20 ).

Lemma Parallel_def : forall m n : Line , m ||| n -> forall a : Complex , on_line a m -> on_line a n -> Larz n = Larz m.
Proof.
  intros.
  unfold Is_parallel in H.
  SearchAbout Line .
  unfold on_line in H0.
  unfold on_line in H1.
  rewrite H in H0.
  rewrite H0 in H1.
  replace (Larz m) with ( fst (Larz m, 0%R) ).
  rewrite H1.
  auto.
  auto.
Qed.

Definition Line_intersect ( l1 l2 : Line ) := (((Larz l1,0)%R*l1-(Larz l2,0)%R*l2)/(l1*l1-l2*l2))%C.

Lemma Ccojabs2 : forall x : Complex , ( x*Ccoj x = ((Cabs x)^2,0)%R )%C.
Proof.
  intros.
  unfold Cabs.
  simpl.
  replace ( (sqrt (real_p x * real_p x + imag_p x * imag_p x) *
  (sqrt (real_p x * real_p x + imag_p x * imag_p x) * 1) ) )%R with 
  (real_p x * real_p x + imag_p x * imag_p x)%R.
  remember (x * Ccoj x)%C as z.
  rewrite Cdecompose with (z:=x) in Heqz.
  unfold Ccoj in Heqz.
  simpl in Heqz.
  rewrite Heqz.
  apply injective_projections.
  simpl.
  ring.
  simpl.
  ring.
  replace ( (sqrt (real_p x * real_p x + imag_p x * imag_p x) *
 (sqrt (real_p x * real_p x + imag_p x * imag_p x) * 1)) )%R
  with ( (sqrt (real_p x * real_p x + imag_p x * imag_p x) *
 (sqrt (real_p x * real_p x + imag_p x * imag_p x) )) )%R.
  rewrite sqrt_def.
  auto.
  apply Ra2b2pos.
  ring.
Qed.

Lemma line_eq_help1 : forall x : Complex , forall l1 : Line , (l1 * x + Ccoj l1 * Ccoj x)%C = (Larz l1, 0%R) -> (x)%C = (Ccoj l1 * (Larz l1, 0%R) - Ccoj l1 * Ccoj l1 * Ccoj x)%C.
Proof.
  intros.
  assert (Ccoj l1 * (l1 * x + Ccoj l1 * Ccoj x)%C = Ccoj l1 * (Larz l1, 0%R))%C.
  rewrite H.
  auto.
  ring_simplify in H0.
  replace ( Ccoj l1 * l1 * x )%C with x in H0.
  rewrite <- H0.
  ring.
  replace (Ccoj l1 * l1 )%C with (C1)%C.
  ring.
  rewrite Cmult_comm.
  rewrite Ccojabs2.
  rewrite Lshib_len1.
  apply injective_projections.
  simpl.
  ring.
  simpl.
  ring.
Qed.

Lemma Ccojreal : forall x:R , Ccoj ( x , 0 )%R = (x , 0 )%R.
Proof.
  intros.
  unfold Ccoj.
  simpl.
  replace (-0)%R with 0%R ; [ idtac | ring ].
  auto.
Qed. 

Lemma Cabsargeq : forall a b : Complex , Cabs a = Cabs b -> Carg a = Carg b -> a = b.
Proof.
  intros.
  rewrite Cdecompose.
  rewrite Cdecompose with (z:=a).
  rewrite ! Creal_arg.
  rewrite ! Cimag_arg.
  rewrite H.
  rewrite H0.
  auto.
Qed.

Lemma not_parallel_intersect_uniq : forall l1 l2 : Line , ~ (l1 ||| l2) -> forall x : Complex , on_line x l1 -> on_line x l2 -> x=Line_intersect l1 l2.
Proof.
  intros.
  unfold Line_intersect.
  unfold on_line in H0,H1.
  apply line_eq_help1 in H0.
  apply line_eq_help1 in H1.
  rewrite <- Ccojreal in H0,H1.
  rewrite ! Ccojmult in H0,H1.
  rewrite Ccojminus in H0,H1.
  assert ( Ccoj (l1 * (Larz l1, 0%R) - l1 * l1 * x)%C
 = Ccoj (l2 * (Larz l2, 0%R) - l2 * l2 * x)%C ).
  rewrite <- H0.
  auto.
  apply Ccojeq in H2.
  assert ( (((Larz l1, 0%R) * l1 - (Larz l2, 0%R) * l2) = (x*(l1 * l1 - l2 * l2)))%C ).
  apply Ceq_side2 in H2.
  apply Ceq_side.
  rewrite <- H2.
  ring.
  assert ( forall a b c : Complex , a * b = c -> b <> C0 -> a = c / b )%C.
  intros.
  rewrite <- H4.
  field.
  auto.
  apply H4.
  auto.
  unfold not.
  intros.
  apply Ceq_side in H5.
  assert ( Carg (l1 * l1)%C = Carg (l2 * l2)%C ).
  f_equal.
  auto.
  rewrite <- ! Cmultarg in H6.
  rewrite ! argplus1 in H6.
  ring_simplify in H6.
  apply Rmult_eq_reg_l in H6.
  elim H.
  unfold Is_parallel.
  apply Cabsargeq.
  rewrite ! Lshib_len1.
  auto.
  auto.
  auto with real.
  apply Cineq0_arg.
  apply Lshib_gt_C0.
  apply Cineq0_arg.
  apply Lshib_gt_C0.
  apply Cineq0_arg.
  apply Lshib_gt_C0.
  apply Cineq0_arg.
  apply Lshib_gt_C0.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Lshib_gt_C0.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Lshib_gt_C0.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Lshib_gt_C0.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Lshib_gt_C0.
Qed.

Lemma moadele2majhool : forall a b c d e f : R , ( b*d <> a*e )%R -> exists x y : R , (a * x + b * y = c /\ d * x + e * y = f )%R.
Proof.
  intros.
  assert ( b*d - a*e <> 0 )%R.
  unfold not.
  intros.
  elim H.
  apply Rminus_diag_uniq.
  auto.
  exists ( (b*f-c*e)/(b*d-a*e) )%R.
  exists ( (c*d-a*f)/(b*d-a*e) )%R.
  split.
  field.
  auto.
  field.
  auto.
Qed.

Lemma Creal_coj : forall a : Complex , (a + Ccoj a)%C = ( 2 * real_p a , 0 )%R.
Proof.
  intros.
  rewrite Cdecompose with (z:=a).
  unfold Ccoj.
  simpl.
  apply injective_projections.
  simpl.
  ring.
  simpl.
  ring.
Qed.

Lemma Cineq0_real : forall x : Complex , (C0 < x)%C -> (0<=real_p x)%R.
Proof.
  intros.
  rewrite Cdecompose in H.
  simpl in H.
  destruct ( Real_eq_dec 0 (real_p x) ).
  right ; auto.
  left ; auto.
Qed. 

Lemma not_parallel_help : forall l1 l2 : Line , (real_p l2 * imag_p l1)%R = (real_p l1 * imag_p l2)%R -> (l1 ||| l2).
Proof.
  intros.
  apply Peirce.
  intros.
  assert ( C0 < l1 )%C.
  apply Lshib_gt_C0.
  assert ( C0 < l2 )%C.
  apply Lshib_gt_C0.
  rewrite Cdecompose in H1,H2.
  simpl in H1,H2.
  destruct (Real_eq_dec 0 (real_p l1)).
  destruct (Real_eq_dec 0 (real_p l2)).
  assert (Cabs l1 = 1 )%R.
  apply Lshib_len1.
  unfold Cabs in H3.
  rewrite <- e in H3.
  replace (0 * 0 + imag_p l1 * imag_p l1)%R with ( imag_p l1 * imag_p l1 )%R in H3; [ idtac | ring ].
  rewrite sqrt_square in H3.
  assert (Cabs l2 = 1 )%R.
  apply Lshib_len1.
  unfold Cabs in H4.
  rewrite <- e0 in H4.
  replace (0 * 0 + imag_p l2 * imag_p l2)%R with ( imag_p l2 * imag_p l2 )%R in H4; [ idtac | ring ].
  rewrite sqrt_square in H4.
  unfold imag_p,real_p in e,e0,H3,H4.
  apply injective_projections.
  rewrite <- e,e0.
  auto.
  rewrite H3,H4.
  auto.
  left; auto.
  left; auto.
  rewrite <- e in H.
  ring_simplify in H.
  apply Rmult_integral in H.
  case H.
  intros.
  elim n.
  auto.
  intros.
  assert ( (0 <> imag_p l1)%R ).
  auto with real.
  elim H4.
  auto.
  destruct ( Real_eq_dec 0 (real_p l2) ).
  rewrite <- e in H.
  ring_simplify in H.
  apply eq_sym in H.
  apply Rmult_integral in H.
  case H.
  intros.
  elim n.
  auto.
  intros.
  assert ( (0 <> imag_p l2)%R ).
  auto with real.
  elim H4.
  auto.
  unfold Is_parallel.
  assert ( imag_p l1 = imag_p l2 /\ real_p l1 = real_p l2).
  apply unique_arg.
  auto.
  auto.
  field [ H ].
  auto with real.
  replace ( (imag_p l1 * imag_p l1 + real_p l1 * real_p l1)%R ) with
  (real_p l1 * real_p l1 +imag_p l1 * imag_p l1)%R ; [ idtac | ring ].
  rewrite <- Cabs2.
  rewrite Lshib_len1.
  replace ( (imag_p l2 * imag_p l2 + real_p l2 * real_p l2)%R ) with
  (real_p l2 * real_p l2 +imag_p l2 * imag_p l2)%R ; [ idtac | ring ].
  rewrite <- Cabs2.
  rewrite Lshib_len1.
  auto.
  unfold imag_p,real_p in H3.
  apply injective_projections.
  apply H3.
  apply H3.
Qed.

Lemma not_parallel_intersect_exists : forall l1 l2 : Line , ~ (l1 ||| l2) -> exists x : Complex , on_line x l1 /\ on_line x l2.
Proof.
  intros.
  unfold on_line.
  remember (real_p l1) as rl1.
  remember (real_p l2) as rl2.
  remember (imag_p l1) as il1.
  remember (imag_p l2) as il2.
  assert ( exists x y : R , rl1 * x + (- il1) * y = (Larz l1)/2 /\ rl2 * x + (- il2) * y = (Larz l2)/2 )%R.
  apply moadele2majhool.
  unfold not.
  intros.
  assert ( (il1 * rl2)%R = (rl1 * il2)%R ).
  rewrite Ropp_mult_distr_l_reverse in H0.
  replace ( (il1 * rl2)%R ) with ( ( - - (il1 * rl2) )%R ).
  rewrite H0.
  ring.
  ring.
  rewrite Rmult_comm in H1.
  rewrite Heqrl1 in H1.
  rewrite Heqrl2 in H1.
  rewrite Heqil1 in H1.
  rewrite Heqil2 in H1.
  apply not_parallel_help in H1.
  auto.
  elim H0.
  intros.
  elim H1.
  intros.
  clear H0 H1.
  destruct H2.
  exists (x,x0).
  rewrite ! Ccojmult.
  rewrite ! Creal_coj.
  split.
  apply injective_projections.
  simpl.
  rewrite Cdecompose with (z:=Lshib l1).
  simpl.
  rewrite <- Heqrl1.
  rewrite <- Heqil1.
  ring_simplify in H0.
  rewrite H0.
  field.
  auto.
  apply injective_projections.
  simpl.
  rewrite Cdecompose with (z:=Lshib l2).
  simpl.
  rewrite <- Heqrl2.
  rewrite <- Heqil2.
  ring_simplify in H1.
  rewrite H1.
  field.
  auto.
Qed.

Infix " |x| " := Line_intersect ( at level 20 ).

Lemma not_parallel_intersect : forall l1 l2 : Line , ~ (l1 ||| l2) -> on_line (l1 |x| l2) l1 /\ on_line (l1 |x| l2) l2.
Proof.
  intros.
  assert ( bk2:=H ).
  apply not_parallel_intersect_exists in H.
  elim H.
  intros.
  assert (bk:=H0).
  destruct H0.
  apply not_parallel_intersect_uniq with (l2:=l2) in H0.
  rewrite <- H0.
  destruct bk.
  auto.
  auto.
  auto.
Qed.

Lemma intersect_sym : forall l1 l2 : Line , ~ (l1 ||| l2) -> l1 |x| l2 = l2 |x| l1.
Proof.
  intros.
  assert ( bk2:=H ).
  apply not_parallel_intersect_exists in H.
  elim H.
  intros.
  apply eq_trans with (y:=x).
  apply eq_sym.
  apply not_parallel_intersect_uniq.
  auto.
  apply H0.
  apply H0.
  apply not_parallel_intersect_uniq.
  unfold Is_parallel.
  apply not_eq_sym.
  auto.
  apply H0.
  apply H0.
Qed.

Lemma Rineq_case : forall a b : R , (a<b \/ b<=a)%R.
Proof.
  intros.
  assert ( { a < b } + { a = b } + { a > b } )%R.
  apply total_order_T.
  destruct H.
  destruct s.
  left; auto.
  right; right; auto.
  right; left; auto.
Qed.

Definition Unitarg ( x : R ) := ( cos x , sin x ).

Lemma Cabs_Unitarg : forall x : R , Cabs (Unitarg x) = 1%R.
Proof.
  intros.
  unfold Unitarg.
  unfold Cabs.
  simpl.
  rewrite sin2c1.
  apply sqrt_1.
Qed.

Lemma Carg_Unitarg : forall x : R , (-PI<x<=PI)%R -> Carg (Unitarg x) = x.
Proof.
  intros.
  apply eq_sym.
  apply Carg_uniq.
  apply Cneq0.
  rewrite Cabs_Unitarg.
  auto with real.
  split.
  auto.
  rewrite Cabs_Unitarg.
  apply injective_projections.
  simpl; ring.
  simpl; ring.
Qed.

Lemma argminusfactor : forall a b : R , (-PI<a<=PI)%R -> (-PI<b<=PI)%R -> -^ ( a +^ b ) = (-^ a) +^ (-^ b).
Proof.
  intros.
  rewrite <- Carg_Unitarg with (x:=a).
  rewrite <- Carg_Unitarg with (x:=b).
  rewrite ! Cmultarg.
  rewrite <- ! Ccojarg.
  rewrite ! Cmultarg.
  f_equal.
  apply eq_sym.
  apply Ccojmult.
  apply Ccoj0.
  apply Cneq0.
  rewrite Cabs_Unitarg.
  auto with real.
  apply Ccoj0.
  apply Cneq0.
  rewrite Cabs_Unitarg.
  auto with real.
  apply Cneq0.
  rewrite Cabs_Unitarg.
  auto with real.
  apply Cneq0.
  rewrite Cabs_Unitarg.
  auto with real.
  apply C0mult.
  auto with real.
  apply Cneq0.
  rewrite Cabs_Unitarg.
  auto with real.
  apply Cneq0.
  rewrite Cabs_Unitarg.
  auto with real.
  auto with real.
  apply Cneq0.
  rewrite Cabs_Unitarg.
  auto with real.
  apply Cneq0.
  rewrite Cabs_Unitarg.
  auto with real.
  auto.
  auto.
Qed.

Lemma argnegPI : -^ PI = PI.
Proof.
  unfold argneg.
  destruct (Real_eq_dec PI PI).
  auto.
  contradiction.
Qed.

Theorem Parallel_angle : forall l1 l2 : Line , l1 ||| l2 -> forall a b c d : Complex , b <> c -> (a<b)%C -> (c<d)%C -> on_line a l1 -> on_line b l1 -> on_line c l2 -> on_line d l2 -> DAngle a b c = DAngle d c b.
Proof.
  intros.
  unfold DAngle.
  assert ( imag_p l1 < 0 \/ 0<= imag_p l1 )%R.
  apply Rineq_case.
  case H7.
  intros.
  replace (a-b)%C with (-(b-a))%C ; [ idtac | ring ].
  rewrite Carg_neg.
  rewrite line_Carg_c2 with (l:=l1).
  rewrite line_Carg_c2 with (l:=l2) (a:=d) (b:=c).
  rewrite H.
  replace (b-c)%C with (-(c-b))%C ; [ idtac | ring ].
  rewrite Carg_neg.
  unfold argminus.
  rewrite argplus_comm.
  rewrite argplus_assoc.
  rewrite argplus_assoc.
  rewrite argminusfactor.
  rewrite argplus_assoc.
  rewrite argnegPI.
  f_equal.
  apply eq_sym.
  rewrite argplus_comm.
  rewrite argplus_assoc.
  auto.
  apply argnegineq.
  apply Carg_def.
  apply argstan_nPI2.
  apply argnegineq.
  apply Carg_def.
  apply argplusineq.
  apply argstan_nPI2.
  apply argnegineq.
  apply Carg_def.
  apply argnegineq.
  apply Carg_def.
  apply argnegineq.
  apply argstan_PI.
  apply Carg_def.
  apply argstan_PI.
  apply argnegineq.
  apply Carg_def.
  apply argstan_nPI2.
  apply argnegineq.
  apply Carg_def.
  apply argnegineq.
  apply Carg_def.
  apply argplusineq.
  apply argstan_nPI2.
  apply argnegineq.
  apply Carg_def.
  apply argstan_PI.
  unfold not; intros.
  apply Ceq_side in H9.
  elim H0.
  auto.
  rewrite <- H.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Cineq_plus with ( c := (-a)%C ) in H1.
  ring_simplify in H1.
  replace ( - a + b )%C with ( b - a )%C in H1; [ idtac | ring ].
  auto.
  (* Similiar Case :*)
Admitted.

