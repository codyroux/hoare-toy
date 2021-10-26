Require Import String ZArith Lia.
Require Export lang.

Definition pred := env -> Prop.

Open Scope lang_scope.

(* Extraordinalriy awkward because of higher-order unification...
   I think this is mostly solved by defining a WP.
 *)
Inductive hoare : pred -> insn -> pred -> Prop :=
| H_Skip : forall P,
    hoare P Skip P
| H_Assign : forall P x e,
    hoare (fun f => P (f [x --> eval_expr f e])) (x :== e) P
| H_Seq : forall P Q R i j,
    hoare P i Q ->
    hoare Q j R ->
    hoare P (i;j) R
| H_Ite : forall P Q e i j,
    hoare (fun f => eval_expr f e <> 0 /\ P f) i Q ->
    hoare (fun f => eval_expr f e = 0 /\ P f) j Q ->
    hoare P (If e Then i Else j) Q
| H_While : forall (P Q I : pred) e i,
    hoare (fun f => eval_expr f e <> 0 /\ I f) i I ->
    (forall f, I f -> eval_expr f e = 0 -> Q f) ->
    (forall f, P f -> I f) ->
    hoare P (While e Do i Done) Q
| H_Weak : forall (P P' Q Q' : pred) i,
    (forall f, P' f -> P f) ->
    (forall f, Q f -> Q' f) ->
    hoare P i Q ->
    hoare P' i Q'
.

Hint Constructors hoare.

Example test : hoare (fun f => True) ("foo" :== 42) (fun f => f "foo" = 42).
Proof.
  eapply H_Weak.
  - intros.
    assert (H' : f ["foo" --> eval_expr f 42] "foo" = 42) by reflexivity.
    exact H'.
  - intros.
    exact H.
  - apply H_Assign with (P := fun f => f "foo" = 42).
Qed.

Example test' : hoare (fun f => True) (If 0 Then Skip Else "foo" :== 42) (fun f => f "foo" = 42).
Proof.
  apply H_Ite.
  - simpl.
    apply H_Weak with (P := fun f => f "foo" = 42)(Q := fun f => f "foo" = 42); intros; firstorder.
  - eapply H_Weak with (P := fun f => f ["foo" --> eval_expr f 42] "foo" = 42)
                       (Q := fun f => f "foo" = 42).
    + simpl; now auto.
    + now auto.
    + apply H_Assign with (P := fun f => f "foo" = 42).
Qed.

Lemma while_inv : forall (I Q : pred) i body f g e,
    (forall f' g', I f' -> eval_expr f' e <> 0 -> big_step f' body g' -> I g') ->
    (forall f', I f' -> eval_expr f' e = 0 -> Q f') ->
    I f ->
    big_step f i g ->
    (i = While e Do body Done) ->
    Q g.
Proof.
  intros I Q i body f g e inv_body inv_break init big.
  induction big; intro eq; try inversion eq; subst; auto.
  apply IHbig2; [| now auto].
  eapply inv_body; [| apply H | apply big1].
  apply init.
Qed.

Theorem hoare_sound : forall f g P Q i,
    hoare P i Q -> big_step f i g -> P f -> Q g.
Proof.
  intros f g P Q i h.
  revert f g.
  induction h; intros f g step; inversion step; subst; eauto.
  (* 1 subgoal! *)
  intro hf.
  eapply while_inv; intros.
  - apply IHh with (f := f'); now eauto.
  - apply H; now auto.
  - simpl; apply H0; now eauto.
  - exact step.
  - reflexivity.
Qed.

(* This should be the strongest postcondition for [While e Do body
  Done], given P as a precondition. *)

Inductive invariant : forall (P : pred) (e : expr) (i : insn) (f : env), Prop :=
| inv_0 : forall (P : pred) e i f, P f -> invariant P e i f
| inv_s : forall (P : pred) e i f g,
    eval_expr f e <> 0 ->
    big_step f i g ->
    invariant P e i f ->
    invariant P e i g.

Hint Constructors invariant.

Lemma while_SP_1 : forall body e (P : pred) f,
    P f -> invariant P e body f.
Proof.
  intros; econstructor; now eauto.
Qed.

Lemma while_SP_2_gen : forall body e (P Q : pred),
    (forall f g, P f -> big_step f (While e Do body Done) g -> Q g) ->
    forall g h, invariant P e body g -> big_step g (While e Do body Done) h -> Q h.
Proof.
  intros until h; intros inv; induction inv.
  - intros; eapply H; now eauto.
  - intros; apply IHinv; auto.
    econstructor; now eauto.
Qed.


Lemma while_SP_2 : forall body e (P Q : pred),
    (forall f g, P f -> big_step f (While e Do body Done) g -> Q g) ->
    forall g, invariant P e body g -> eval_expr g e = 0 -> Q g.
Proof.
  intros; eapply while_SP_2_gen; now eauto.
Qed.


Theorem hoare_complete : forall i (P Q : pred),
    (forall f g, P f -> big_step f i g -> Q g) -> hoare P i Q.
Proof.
  induction i; intros P Q prop.
  - apply H_Weak with (P := P)(Q := P); auto.
    intros.
    eapply prop; try apply H; now auto.
  (* eauto works! *)
  - apply H_Weak with (P := (fun f => Q (f [s --> eval_expr f e])))(Q := Q); eauto.
  - apply H_Seq with (Q := fun f => forall g, big_step f i2 g -> Q g).
    + apply IHi1.
      intros; eauto.
    + apply IHi2; intros; eauto.
  - apply H_Ite.
    + apply IHi1; intros.
      eapply prop; destruct H; eauto.
    + apply IHi2; intros.
      eapply prop; destruct H; eauto.
  - eapply H_While with (I := invariant P e i); intros.
    + apply IHi.
      intros f g [neq H] bs. now eauto.
    + eapply while_SP_2; now eauto.
    + eapply while_SP_1; now eauto.
Qed.


(* Inductive is_fix : forall (F : (env -> env) -> env -> env) (f : env -> env), Prop := *)
(*   | is_fix_unfold : forall F f, is_fix F f -> is_fix F (F f). *)

Definition is_fix (F : (env -> env) -> env -> env) (f : env -> env) :=
  forall ctx, f ctx = F f ctx.

Definition fix_of_while (e : expr) (body : env -> env)
           (F : env -> env) :=
  fun ctx =>
    if eval_expr ctx e =? 0
    then ctx
    else
      let ctx' := body ctx in
      F ctx'.

Check fix_of_while.

Definition evals_to body body_sem :=
  forall f, big_step f body (body_sem f).

Check evals_to.
Print pred.

Print env.

Check hoare_complete.

Lemma ext_eval : forall f g e, f ≃ g -> eval_expr f e = eval_expr g e.
Proof.
  intros until e; induction e; simpl; intros; auto.
  rewrite IHe1; auto; rewrite IHe2; auto.
Qed.

(* this should really be in the logic area. *)
Lemma simeq_sym : forall f g, f ≃ g -> g ≃ f.
Proof. intros; intro; auto. Qed.

Hint Resolve simeq_sym.

Lemma fix_to_while_big : forall body e body_sem f ctx,
    evals_to body body_sem ->
    let specF := fix_of_while e body_sem in
    is_fix specF f ->
    big_step ctx (While e Do body Done) (f ctx).
Proof.
  intros body e body_sem f ctx h_body_sem specF h_is_fix.
  Search ({ _ = _} + {_ <> _}).
  case (Z.eq_dec (eval_expr ctx e) 0); intro eq_e.
  - subst specF.
    unfold fix_of_while, is_fix in *.
    assert (eval_zero : eval_expr ctx e =? 0 = true) by (apply Z.eqb_eq; auto).
    assert (h_is_fix' := h_is_fix ctx).
    rewrite eval_zero in *.
    rewrite h_is_fix'.
    apply BS_While_halt; now auto.
  - subst specF.
    unfold fix_of_while, is_fix in *.
    assert (eval_nz : eval_expr ctx e =? 0 = false) by (apply Z.eqb_neq; auto).
    eapply BS_While_continue; eauto.
    assert (h_is_fix' := h_is_fix ctx).
    rewrite eval_nz in *; rewrite h_is_fix'.
    (* Uh oh *)
Admitted.


Theorem fix_to_while : forall body e body_sem f,
    evals_to body body_sem ->
    let specF := fix_of_while e body_sem in
    is_fix specF f ->
    forall ctx,
      hoare (fun k => k ≃ ctx) (While e Do body Done) (fun k => k ≃ (f ctx)).
Proof.
  intros.
  eapply hoare_complete; intros.
  eapply big_step_ext; [eauto | | apply H1 | reflexivity].
  eapply fix_to_while_big; now eauto.
Qed.

