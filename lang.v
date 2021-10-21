Require Import String ZArith Lia.



Open Scope string_scope.
Open Scope Z_scope.

Section Lang.

  Declare Scope lang_scope.

  Inductive binop := Add | Sub | Leq.

  Inductive expr : Type :=
  | Var : string -> expr
  | Const : Z -> expr
  | Binop : binop -> expr -> expr -> expr.

  Inductive insn : Type :=
  | Skip : insn
  | Assign : string -> expr -> insn
  | Seq : insn -> insn -> insn
  | Ite : expr -> insn -> insn -> insn
  | While : expr -> insn -> insn.

  Coercion Var : string >-> expr.
  Coercion Const : Z >-> expr.

  Infix "+" := (Binop Add) : lang_scope.
  Infix "-" := (Binop Sub) : lang_scope.
  Infix "<=" := (Binop Leq)(at level 70) : lang_scope.

  Open Scope lang_scope.
  Check "foo" + 3.

  Notation "x :== e" := (Assign x e) (at level 80) : lang_scope.
  Infix ";" := Seq (at level 90, right associativity) : lang_scope.
  Notation "'If' e 'Then' i 'Else' j" := (Ite e i j)(at level 95) : lang_scope.

  Check (If 3 Then Skip Else Skip).

  Notation "'While' e 'Do' i 'Done'" := (While e i)(at level 100) : lang_scope.

  Check (While "x" <= 10 Do "x" :== "x" + 1; "y" :== "y" - 1; Skip Done).

  Definition env := string -> Z.

  Definition equiv_env (f g : env) : Prop := forall s, f s = g s.
 
  Notation "f ≃ g" := (equiv_env f g)(at level 50).

  Search (Z -> Z -> bool).
  
  Definition eval_op (o : binop) : Z -> Z -> Z :=
    match o with
    | Add => Z.add
    | Sub => Z.sub
    | Leq => (fun x y => if Z.leb x y then 1 else 0)
    end.
  
  Fixpoint eval_expr (f : env) (e : expr) : Z :=
    match e with
    | Var v => f v
    | Const c => c
    | Binop o e1 e2 => eval_op o (eval_expr f e1) (eval_expr f e2)
    end.

  Eval compute in (eval_expr (fun _ => 0) ("x" + "y" + 2 - 1)).

  Search (string -> string -> bool).

  Check String.eqb.
  Search (eqb).

  Definition by_cases (f : env) (x : string) (v : Z) : env :=
    fun y => if String.eqb x y then v else f y.

  Hint Unfold by_cases.

  Notation "f [ x --> v ]" := (by_cases f x v)(at level 70).
  
  Inductive big_step : env -> insn -> env -> Prop :=
  | BS_Skip : forall f,
      big_step f Skip f
  | BS_Assign : forall f x e v,
      eval_expr f e = v ->
      big_step f (x :== e) (f[x --> v])
  | BS_Seq : forall f g h i j,
      big_step f i g ->
      big_step g j h ->
      big_step f (i;j) h
  | BS_Ite_true : forall f g e i j,
      big_step f i g ->
      eval_expr f e <> 0 ->
      big_step f (If e Then i Else j) g
  | BS_Ite_false : forall f g e i j,
      big_step f j g ->
      eval_expr f e = 0 ->
      big_step f (If e Then i Else j) g
  | BS_While_halt : forall f e i,
      eval_expr f e = 0 ->
      big_step f (While e Do i Done) f
  | BS_While_continue : forall f g h e i,
      eval_expr f e <> 0 ->
      big_step f i g ->
      big_step g (While e Do i Done) h ->
      big_step f (While e Do i Done) h.

  Locate "≃".

  Hint Constructors big_step.

  Lemma eval_ext : forall e (f f' : env),
      f ≃ f' -> eval_expr f e = eval_expr f' e.
  Proof.
    unfold equiv_env; intros; induction e; simpl; auto.
    erewrite IHe1; erewrite IHe2; now auto.
  Qed.

  Hint Rewrite eval_ext.

  (* It's nice to know evaluation is deterministic... *)
  Theorem big_step_ext : forall (i : insn) (f g : env),
      big_step f i g ->
      forall i' f' g', big_step f' i' g' -> f ≃ f' -> i = i' -> g ≃ g'.
  Proof.
    intros i f g h1; induction h1; intros i' f' g' h2; induction h2; try (intros _ eq; now inversion eq); auto.
    - unfold by_cases; intros f_eq i_eq; inversion i_eq; subst
      ; intro y; try destruct (x0 =? y)%string; simpl; auto.
      erewrite eval_ext; now auto.
    - intros f_eq i_eq; eapply IHh1_2; eauto; [eapply IHh1_1; eauto; congruence| congruence].
    - intros f_eq i_eq; eapply IHh1; eauto; congruence.
    - intros f_eq i_eq; exfalso; apply H; erewrite eval_ext; eauto; congruence.
    - intros f_eq i_eq; exfalso; apply H0; inversion i_eq; subst; erewrite eval_ext; eauto; intro; now auto.
    - intros f_eq i_eq; eapply IHh1; eauto; congruence.
    - intros f_eq i_eq; exfalso; apply H0; inversion i_eq; subst; erewrite eval_ext; eauto; intro; now auto.
    - intros f_eq i_eq; exfalso; apply H; erewrite eval_ext; eauto; congruence.
    - intros f_eq i_eq.
      eapply IHh1_2; [ now eauto| | now eauto].
      eapply IHh1_1; eauto; congruence.
  Qed.

  Definition pred := env -> Prop.

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

  Lemma while_inv : forall (I G : pred) i body f g e,
      (forall f' g', I f' -> eval_expr f' e <> 0 -> big_step f' body g' -> I g') ->
      (forall f', I f' -> eval_expr f' e = 0 -> G f') ->
      I f ->
      big_step f i g ->
      (i = While e Do body Done) ->
      G g.
  Proof.
    intros I G i body f g e inv_body inv_break init big.
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
