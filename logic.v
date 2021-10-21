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
