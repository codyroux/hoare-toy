Require Import String ZArith Lia.



Open Scope string_scope.
Open Scope Z_scope.

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

